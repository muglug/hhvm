// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: the tests of `client_isolation_move`.

use super::output::Outcome;
use super::*;

fn root(suffix: &str) -> relative_path::T {
    relative_path::from_root(suffix)
}

#[test]
fn paths_are_renamed_under_the_target() {
    relative_path::set_prefixes_for_tests();
    let source = root("a/pkg");
    let target = root("b/pkg");
    assert_eq!(
        paths::original_path(&source, &target, &root("b/pkg/x/y.php")),
        root("a/pkg/x/y.php")
    );
    assert_eq!(
        paths::original_path(&source, &target, &root("c/z.php")),
        root("c/z.php")
    );
    assert_eq!(paths::target_name("b", "a/pkg"), "b/pkg");
    assert_eq!(paths::target_under(&root("b/c"), &source), root("b/c/pkg"));
    assert_eq!(
        paths::relative_to_root("/data/www/a/b.php"),
        root("a/b.php")
    );
    assert_eq!(
        relative_path::prefix(&paths::relative_to_root("/elsewhere/b.php")),
        relative_path::Prefix::Dummy
    );
}

#[test]
fn rename_path_only_replaces_whole_names() {
    use move_error::rename_path;
    assert_eq!(rename_path("see a/b/c", "a/b", "x/y"), "see x/y/c");
    assert_eq!(rename_path("see a/b_c", "a/b", "x/y"), "see a/b_c");
    assert_eq!(rename_path("a/b and za/b", "a/b", "x"), "x and za/b");
    assert_eq!(rename_path("a/b", "a/b", "x"), "x");
}

#[test]
fn introduced_errors_are_those_not_in_the_baseline() {
    relative_path::set_prefixes_for_tests();
    let error = |file: &str, message: &str| move_error::T {
        code: 4110,
        file: root(file),
        line: 3,
        message: message.to_string(),
    };
    let source = root("a/pkg");
    let target = root("b/pkg");
    let baseline = vec![error("a/pkg/f.php", "in a/pkg/f.php")];
    // Named as before the move, the first is the baseline's.
    let introduced = move_error::introduced(
        &source,
        &target,
        &baseline,
        vec![
            error("b/pkg/f.php", "in b/pkg/f.php"),
            error("b/pkg/g.php", "new"),
        ],
    );
    assert_eq!(introduced, vec![error("a/pkg/g.php", "new")]);
    assert!(move_error::same(&baseline, &baseline));
    assert!(!move_error::same(&baseline, &introduced));
}

fn text(outcome: &Outcome, json: bool) -> String {
    let mut out = vec![];
    output::print_outcome(&mut out, "a/pkg", "b/pkg", json, outcome).unwrap();
    String::from_utf8(out).unwrap()
}

#[test]
fn outcomes_as_text_and_json() {
    relative_path::set_prefixes_for_tests();
    let moved = Outcome::Moved { files: 2 };
    assert_eq!(
        text(&moved, false),
        "Moved: 2 files from a/pkg to b/pkg, with no new errors.\n"
    );
    assert_eq!(
        text(&moved, true),
        "{\"source\":\"a/pkg\",\"target\":\"b/pkg\",\"moved\":true,\"files\":2,\"refused\":null,\"blockers\":null,\"blocked_by\":null,\"new_errors\":null,\"baseline_restored\":null}\n"
    );
    assert!(matches!(
        output::exit_status(&moved),
        exit_status::T::NoError
    ));
    let refused = Outcome::Refused("why".to_string());
    assert_eq!(text(&refused, false), "Did not run: why\n");
    assert!(matches!(
        output::exit_status(&refused),
        exit_status::T::InputError
    ));
    let blocked = Outcome::Blocked(vec![server_isolation_types::Blocker {
        file: "x.php".to_string(),
        references: vec!["a/pkg/f.php".to_string()],
    }]);
    assert_eq!(
        text(&blocked, false),
        "Not moved: referenced from 1 file outside.\n  x.php\n"
    );
    assert_eq!(
        text(&blocked, true),
        "{\"source\":\"a/pkg\",\"target\":\"b/pkg\",\"moved\":false,\"files\":null,\"refused\":null,\"blockers\":[\"x.php\"],\"blocked_by\":[{\"file\":\"x.php\",\"references\":[\"a/pkg/f.php\"]}],\"new_errors\":null,\"baseline_restored\":null}\n"
    );
    assert!(matches!(
        output::exit_status(&blocked),
        exit_status::T::TypeError
    ));
    let errors: Vec<move_error::T> = (0..11)
        .map(|i| move_error::T {
            code: 4000 + i,
            file: root("a/pkg/f.php"),
            line: i,
            message: "first\nsecond".to_string(),
        })
        .collect();
    let not_moved = Outcome::NotMoved {
        errors: errors[..1].to_vec(),
        baseline_restored: true,
    };
    assert_eq!(
        text(&not_moved, false),
        "Not moved: the move introduced 1 error, and it was undone.\n  4000 a/pkg/f.php:0: first\n"
    );
    assert_eq!(
        text(&not_moved, true),
        "{\"source\":\"a/pkg\",\"target\":\"b/pkg\",\"moved\":false,\"files\":null,\"refused\":null,\"blockers\":null,\"blocked_by\":null,\"new_errors\":[{\"code\":4000,\"file\":\"a/pkg/f.php\",\"line\":0,\"message\":\"first\\nsecond\"}],\"baseline_restored\":true}\n"
    );
    let not_moved = Outcome::NotMoved {
        errors,
        baseline_restored: true,
    };
    assert!(text(&not_moved, false).ends_with("  4009 a/pkg/f.php:9: first\n  and 1 more\n"));
}

/// A fresh temporary directory.
fn temp_dir(name: &str) -> String {
    let dir =
        std::env::temp_dir().join(format!("hh_isolation_move_{}_{}", name, std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::canonicalize(&dir)
        .unwrap()
        .to_str()
        .unwrap()
        .to_string()
}

#[test]
fn a_move_makes_the_parents_and_is_undone() {
    let dir = temp_dir("move");
    let source = format!("{}/src/pkg", dir);
    std::fs::create_dir_all(&source).unwrap();
    std::fs::write(format!("{}/f.php", source), "<?hh").unwrap();
    let target = format!("{}/x/y/pkg", dir);
    assert_eq!(
        dir_move::missing_parents(&target),
        vec![format!("{}/x", dir), format!("{}/x/y", dir)]
    );
    let journal = dir_move::move_(&source, &target).unwrap();
    assert_eq!(
        journal,
        vec![
            dir_move::Step::Renamed {
                from: source.clone(),
                into: target.clone()
            },
            dir_move::Step::MadeDir(format!("{}/x/y", dir)),
            dir_move::Step::MadeDir(format!("{}/x", dir)),
        ]
    );
    assert!(std::path::Path::new(&format!("{}/f.php", target)).exists());
    dir_move::undo(&journal).unwrap();
    assert!(std::path::Path::new(&format!("{}/f.php", source)).exists());
    assert!(!std::path::Path::new(&format!("{}/x", dir)).exists());
    // Undoing again skips what is already undone.
    dir_move::undo(&journal).unwrap();
    // A failed move undoes the directories it made.
    let missing = format!("{}/nope", dir);
    let reason = dir_move::move_(&missing, &format!("{}/z/w", dir)).unwrap_err();
    assert_eq!(
        reason,
        format!(
            "(\"Unix.Unix_error(Unix.ENOENT, \\\"rename\\\", \\\"{}\\\")\")",
            missing
        )
    );
    assert!(!std::path::Path::new(&format!("{}/z", dir)).exists());
    let _ = std::fs::remove_dir_all(&dir);
}
