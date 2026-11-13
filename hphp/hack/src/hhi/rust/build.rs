use std::path::Path;
use std::path::PathBuf;

fn main() {
    const ROOT_PATH: &str = "../../../../..";

    let root_path = Path::new(ROOT_PATH);
    let hhi_lib = root_path.join("hphp/hack/hhi");
    let hsl = root_path.join("hphp/hsl/src");

    let out_dir = std::env::var("OUT_DIR").unwrap();
    let out_dir = Path::new(&out_dir);

    let mut contents: Vec<(PathBuf, String)> = Vec::new();

    // The handwritten hhi files, named relative to the hhi directory.
    //
    // Symlinked directories are followed, as dune did for the OCaml build:
    // extensions kept outside this tree link their hhi directory in here at
    // configure time (hphp/runtime/ext/slack's config.cmake creates
    // `hhi/slack`), and their declarations must be built in like the rest.
    for entry in walkdir::WalkDir::new(&hhi_lib)
        .follow_links(true)
        .sort_by_file_name()
    {
        let entry = entry.unwrap();
        let path = entry.path();
        // Watch the directories too, so that a file or a link that appears
        // later (the extension link is made at configure time) is picked up.
        if entry.file_type().is_dir() {
            rerun_if_changed(path);
        }
        if !entry.file_type().is_file() || path.extension() != Some(std::ffi::OsStr::new("hhi")) {
            continue;
        }
        rerun_if_changed(path);
        let name = path.strip_prefix(&hhi_lib).unwrap().to_path_buf();
        contents.push((name, std::fs::read_to_string(path).unwrap()));
    }

    // The interface of the Hack Standard Library, generated from its sources
    // as `hsl_generated/<path>.hhi`.
    for entry in walkdir::WalkDir::new(&hsl).sort_by_file_name() {
        let entry = entry.unwrap();
        if !entry.file_type().is_file() {
            continue;
        }
        let path = entry.path();
        let ext = path.extension().unwrap_or(std::ffi::OsStr::new(""));
        if ext != "php" && ext != "hack" {
            continue;
        }
        let source_path = path.strip_prefix(root_path).ok().and_then(Path::to_str);
        let mut out: Vec<u8> = Vec::new();
        if generate_hhi_lib::run(&mut out, path, source_path).is_ok() {
            rerun_if_changed(path);
            let name = Path::new("hsl_generated")
                .join(path.strip_prefix(&hsl).unwrap())
                .with_extension("hhi");
            contents.push((name, String::from_utf8(out).unwrap()));
        }
    }

    gen_hhi_contents_lib::write_hhi_contents_file(&out_dir.join("hhi_contents.rs"), &contents)
        .unwrap();

    rerun_if_changed("build.rs");
    rerun_if_changed("gen_hhi_contents.rs");
}

fn rerun_if_changed<P: AsRef<Path>>(f: P) {
    println!("cargo:rerun-if-changed={}", f.as_ref().to_str().unwrap());
}
