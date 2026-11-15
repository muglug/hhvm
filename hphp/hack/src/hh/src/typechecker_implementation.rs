// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: the program installed as `hh_client` and
//! `hh_server` when both typecheckers are, which runs the OCaml one
//! (`hh_client_ocaml`, `hh_server_ocaml`) or the Rust one (`hh_client_rust`,
//! `hh_server_rust`), whichever the root asks for. It plays the part of the
//! wrapper that `utils/repo_root.rs` mentions (`find_hh.sh`).
//!
//! The implementation is, the first that is set of:
//!
//! 1. `--typechecker-implementation=ocaml|rust` (or `... ocaml|rust`) on the
//!    command line, which is removed before the arguments are passed on;
//! 2. `$HH_TYPECHECKER_IMPLEMENTATION`;
//! 3. `typechecker_implementation = ocaml|rust` in the `.hhconfig` of the
//!    root;
//! 4. `ocaml`, or `rust` when the OCaml binary is not installed.
//!
//! The chosen binary is exec'd from the directory of this one, with the
//! same `argv[0]` (so usage messages still say `hh_client`) and with
//! `$HH_TYPECHECKER_IMPLEMENTATION` set to the choice, so that the programs
//! it starts make the same one: the OCaml `hh_client` starts the `hh_server`
//! next to it, which is this program again (the Rust one starts
//! `hh_server_rust` directly, [`crate::rt::exe_suffix`]).
//!
//! The root is found without parsing the command line in full (that can
//! read stdin, or exit): it is the last argument that is a directory under
//! a `.hhconfig`, else the current directory, and then the nearest ancestor
//! with a `.hhconfig`, as `Wwwroot.interpret_command_line_root_parameter`
//! looks for it. Where the program does not take its root from its
//! arguments (`hh_client lint FILE...`, which uses the current directory),
//! a directory among them could pick another root's setting.

use std::ffi::OsString;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::process::CommandExt;
use std::path::Path;
use std::path::PathBuf;

use crate::config_file_common;
use crate::config_keys;
use crate::exit_status;

/// The command line option.
pub const OPTION: &str = "--typechecker-implementation";

/// The environment variable.
pub const ENV_VAR: &str = "HH_TYPECHECKER_IMPLEMENTATION";

/// The programs this one can be installed as.
pub const PROGRAMS: &[&str] = &["hh_client", "hh_server"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Implementation {
    OCaml,
    Rust,
}

impl Implementation {
    pub fn of_string(s: &str) -> Option<Self> {
        match s.trim() {
            "ocaml" => Some(Implementation::OCaml),
            "rust" => Some(Implementation::Rust),
            _ => None,
        }
    }

    pub fn to_str(self) -> &'static str {
        match self {
            Implementation::OCaml => "ocaml",
            Implementation::Rust => "rust",
        }
    }

    /// The installed name of `program` (`hh_client`) in this implementation.
    pub fn binary_name(self, program: &str) -> String {
        format!("{}_{}", program, self.to_str())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// A bad value of the option (exits `Input_error`).
    BadOption(String),
    /// A bad value of the environment variable or of `.hhconfig` (exits
    /// `Config_error`).
    BadConfig(String),
}

/// The arguments without the option, and the option's last value.
pub fn take_option(args: Vec<OsString>) -> Result<(Vec<OsString>, Option<Implementation>), Error> {
    let parse = |value: &[u8]| {
        Implementation::of_string(&String::from_utf8_lossy(value)).ok_or_else(|| {
            Error::BadOption(format!(
                "{} must be ocaml or rust, not '{}'",
                OPTION,
                String::from_utf8_lossy(value)
            ))
        })
    };
    let mut rest = Vec::with_capacity(args.len());
    let mut choice = None;
    let mut args = args.into_iter();
    while let Some(arg) = args.next() {
        let bytes = arg.as_bytes();
        if bytes == OPTION.as_bytes() {
            match args.next() {
                Some(value) => choice = Some(parse(value.as_bytes())?),
                None => return Err(Error::BadOption(format!("{} needs a value", OPTION))),
            }
        } else if let Some(value) = bytes
            .strip_prefix(OPTION.as_bytes())
            .and_then(|v| v.strip_prefix(b"="))
        {
            choice = Some(parse(value)?);
        } else {
            rest.push(arg);
        }
    }
    Ok((rest, choice))
}

/// The root the arguments are about: the last that is a directory under a
/// `.hhconfig`, else the current directory's.
pub fn guess_root(args: &[OsString], cwd: &Path) -> Option<PathBuf> {
    args.iter()
        .rev()
        .filter(|arg| !arg.as_bytes().starts_with(b"-"))
        .map(|arg| cwd.join(arg))
        .filter(|path| path.is_dir())
        .find_map(|path| repo_root::guess_root_from(&path).ok())
        .or_else(|| repo_root::guess_root_from(cwd).ok())
}

/// The setting in the `.hhconfig` of `root`, if any.
pub fn of_hhconfig(root: &Path) -> Result<Option<Implementation>, Error> {
    let hhconfig = root.join(".hhconfig");
    let contents = match std::fs::read(&hhconfig) {
        Ok(contents) => contents,
        Err(_) => return Ok(None),
    };
    let config = config_file_common::parse_contents(&contents);
    match config_file_common::getters::string_opt(
        config_keys::hhconfig::TYPECHECKER_IMPLEMENTATION,
        &config,
    ) {
        None => Ok(None),
        Some(value) => Implementation::of_string(&value).map(Some).ok_or_else(|| {
            Error::BadConfig(format!(
                "{} in {} must be ocaml or rust, not '{}'",
                config_keys::hhconfig::TYPECHECKER_IMPLEMENTATION,
                hhconfig.display(),
                value
            ))
        }),
    }
}

/// The value of the environment variable, if set and not empty.
pub fn of_env(value: Option<OsString>) -> Result<Option<Implementation>, Error> {
    match value {
        None => Ok(None),
        Some(value) if value.is_empty() => Ok(None),
        Some(value) => Implementation::of_string(&value.to_string_lossy())
            .map(Some)
            .ok_or_else(|| {
                Error::BadConfig(format!(
                    "${} must be ocaml or rust, not '{}'",
                    ENV_VAR,
                    value.to_string_lossy()
                ))
            }),
    }
}

/// The implementation to run.
pub fn choose(
    option: Option<Implementation>,
    env: Option<Implementation>,
    hhconfig: impl FnOnce() -> Result<Option<Implementation>, Error>,
    ocaml_installed: bool,
) -> Result<Implementation, Error> {
    if let Some(i) = option.or(env) {
        return Ok(i);
    }
    Ok(match hhconfig()? {
        Some(i) => i,
        None if ocaml_installed => Implementation::OCaml,
        None => Implementation::Rust,
    })
}

fn die(program: &str, message: &str, exit_status: exit_status::T) -> ! {
    eprintln!("{}: {}", program, message);
    std::process::exit(exit_status::exit_code(&exit_status) as i32)
}

/// The `main` of the program.
pub fn main() -> ! {
    let mut args = std::env::args_os();
    let arg0 = args.next().unwrap_or_else(|| OsString::from("hh_client"));
    let program = Path::new(&arg0)
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default();
    if !PROGRAMS.contains(&program.as_str()) {
        die(
            &program,
            &format!("must be run as one of {}", PROGRAMS.join(", ")),
            exit_status::T::InputError,
        )
    }
    let dir = match std::env::current_exe() {
        Ok(exe) => exe.parent().map(Path::to_path_buf).unwrap_or_default(),
        Err(e) => die(
            &program,
            &format!("cannot find itself: {}", e),
            exit_status::T::InputError,
        ),
    };
    let binary = |i: Implementation| dir.join(i.binary_name(&program));
    let result = take_option(args.collect()).and_then(|(rest, option)| {
        let env = of_env(std::env::var_os(ENV_VAR))?;
        let hhconfig = || {
            let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
            match guess_root(&rest, &cwd) {
                Some(root) => of_hhconfig(&root),
                None => Ok(None),
            }
        };
        let ocaml_installed = binary(Implementation::OCaml).exists();
        choose(option, env, hhconfig, ocaml_installed).map(|choice| (rest, choice))
    });
    let (rest, implementation) = match result {
        Ok(x) => x,
        Err(Error::BadOption(message)) => die(&program, &message, exit_status::T::InputError),
        Err(Error::BadConfig(message)) => die(&program, &message, exit_status::T::ConfigError),
    };
    let binary = binary(implementation);
    let error = std::process::Command::new(&binary)
        .arg0(&arg0)
        .args(rest)
        .env(ENV_VAR, implementation.to_str())
        .exec();
    eprintln!(
        "{}: cannot run the {} typechecker ({}): {}",
        program,
        implementation.to_str(),
        binary.display(),
        error
    );
    // The shell's "command not found".
    std::process::exit(127)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn os(args: &[&str]) -> Vec<OsString> {
        args.iter().map(OsString::from).collect()
    }

    #[test]
    fn option() {
        assert_eq!(
            take_option(os(&["check", "--typechecker-implementation=rust", "."])),
            Ok((os(&["check", "."]), Some(Implementation::Rust)))
        );
        assert_eq!(
            take_option(os(&["--typechecker-implementation", "ocaml", "start"])),
            Ok((os(&["start"]), Some(Implementation::OCaml)))
        );
        // The last wins.
        assert_eq!(
            take_option(os(&[
                "--typechecker-implementation=ocaml",
                "--typechecker-implementation=rust"
            ])),
            Ok((vec![], Some(Implementation::Rust)))
        );
        assert_eq!(
            take_option(os(&["--json", "."])),
            Ok((os(&["--json", "."]), None))
        );
        assert!(matches!(
            take_option(os(&["--typechecker-implementation=java"])),
            Err(Error::BadOption(_))
        ));
        assert!(matches!(
            take_option(os(&["--typechecker-implementation"])),
            Err(Error::BadOption(_))
        ));
    }

    #[test]
    fn precedence() {
        use Implementation::*;
        let config = |i: Option<Implementation>| move || Ok(i);
        assert_eq!(
            choose(Some(Rust), Some(OCaml), config(Some(OCaml)), true),
            Ok(Rust)
        );
        assert_eq!(
            choose(None, Some(Rust), config(Some(OCaml)), true),
            Ok(Rust)
        );
        assert_eq!(choose(None, None, config(Some(Rust)), true), Ok(Rust));
        assert_eq!(choose(None, None, config(None), true), Ok(OCaml));
        assert_eq!(choose(None, None, config(None), false), Ok(Rust));
        // .hhconfig is not read when the choice is made already.
        let unread = || -> Result<Option<Implementation>, Error> { panic!("read") };
        assert_eq!(choose(Some(OCaml), None, unread, true), Ok(OCaml));
    }

    #[test]
    fn env() {
        assert_eq!(of_env(None), Ok(None));
        assert_eq!(of_env(Some("".into())), Ok(None));
        assert_eq!(of_env(Some("rust".into())), Ok(Some(Implementation::Rust)));
        assert!(matches!(
            of_env(Some("Rust".into())),
            Err(Error::BadConfig(_))
        ));
    }

    fn temp_dir(name: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("hh_impl_{}_{}", name, std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        d.canonicalize().unwrap()
    }

    #[test]
    fn roots_and_hhconfig() {
        let d = temp_dir("roots");
        let a = d.join("a");
        let b = d.join("b");
        std::fs::create_dir_all(a.join("sub")).unwrap();
        std::fs::create_dir_all(&b).unwrap();
        std::fs::create_dir_all(d.join("elsewhere")).unwrap();
        std::fs::write(
            a.join(".hhconfig"),
            "# c\ntypechecker_implementation = rust\n",
        )
        .unwrap();
        std::fs::write(b.join(".hhconfig"), "version = 1\n").unwrap();
        // The root argument, relative to the current directory.
        assert_eq!(guess_root(&os(&["check", "a/sub"]), &d), Some(a.clone()));
        // No argument: the current directory's.
        assert_eq!(guess_root(&os(&["start"]), &a.join("sub")), Some(a.clone()));
        // The last directory under a .hhconfig wins; options and others are
        // skipped.
        assert_eq!(
            guess_root(
                &os(&["--from", "vim", "elsewhere", &b.to_string_lossy(), "a"]),
                &d
            ),
            Some(a.clone())
        );
        assert_eq!(guess_root(&os(&["elsewhere"]), &b), Some(b.clone()));
        assert_eq!(of_hhconfig(&a), Ok(Some(Implementation::Rust)));
        assert_eq!(of_hhconfig(&b), Ok(None));
        assert_eq!(of_hhconfig(&d), Ok(None));
        std::fs::write(b.join(".hhconfig"), "typechecker_implementation = go\n").unwrap();
        assert!(matches!(of_hhconfig(&b), Err(Error::BadConfig(_))));
        std::fs::remove_dir_all(&d).unwrap();
    }
}
