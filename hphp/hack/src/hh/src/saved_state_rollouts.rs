// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `options/saved_state_rollouts.ml`. See `hh/PORTING.md`.
//!
//! The types are those of `oxidized::saved_state_rollouts`, re-exported. The
//! OCaml reached the rollout logic through three externals of
//! `options/options_ffi.rs` (`make_saved_state_rollouts`,
//! `get_current_rollout_flag`, `default_saved_state_rollouts`), which called
//! the methods of `oxidized`'s `SavedStateRollouts` and `Flag`: here those
//! methods are called directly, in the same way.

pub use oxidized::saved_state_rollouts::Flag;
pub use oxidized::saved_state_rollouts::FlagName;
pub use oxidized::saved_state_rollouts::SavedStateRollouts;

use crate::yojson::safe as yojson;

/// `Saved_state_rollouts.t`
pub type T = SavedStateRollouts;

/// `show_flag` (`[@@deriving show { with_path = false }]`): the name of the
/// constructor.
pub fn show_flag(flag: Flag) -> String {
    match flag {
        Flag::OptimizedMemberFanout => "Optimized_member_fanout",
        Flag::NewNamingTable => "New_naming_table",
    }
    .to_string()
}

pub fn flag_name(flag: Flag) -> FlagName {
    show_flag(flag).to_lowercase()
}

/// The `int` that the externals took is a `usize` on the Rust side:
/// `ocaml_ffi!` converted it with `usize::from_ocaml(..).unwrap()`, whose
/// panic on a negative one became the `Failure` raised to OCaml, with this
/// message.
fn rollout_flag_idx_to_usize(current_rolled_out_flag_idx: isize) -> usize {
    match usize::try_from(current_rolled_out_flag_idx) {
        Ok(idx) => idx,
        Err(e) => panic!(
            "called `Result::unwrap()` on an `Err` value: IntOutOfRange({:?})",
            e
        ),
    }
}

/// `external make_rust : int -> bool -> string option -> bool -> t`
fn make_rust(
    current_rolled_out_flag_idx: isize,
    deactivate_saved_state_rollout: bool,
    force_flag_value: Option<&str>,
    default: bool,
) -> T {
    let current_rolled_out_flag_idx = rollout_flag_idx_to_usize(current_rolled_out_flag_idx);
    let get_default = move |_flag_name: &str| Ok(default);
    SavedStateRollouts::make(
        current_rolled_out_flag_idx.try_into().unwrap(),
        deactivate_saved_state_rollout,
        force_flag_value,
        get_default,
    )
    .unwrap()
}

/// `external get_current_rollout_flag : int -> string option`
fn get_current_rollout_flag(current_rolled_out_flag_idx: isize) -> Option<String> {
    let current_rolled_out_flag_idx = rollout_flag_idx_to_usize(current_rolled_out_flag_idx);
    Flag::get_current_rollout_flag(current_rolled_out_flag_idx as isize)
        .map(|f| f.flag_name().to_owned())
}

/// `get_default` is typically an external config reading, e.g. from JK.
pub fn make(
    current_rolled_out_flag_idx: isize,
    deactivate_saved_state_rollout: bool,
    get_default: impl Fn(&str) -> bool,
    force_flag_value: Option<&str>,
) -> T {
    let default = match get_current_rollout_flag(current_rolled_out_flag_idx) {
        Some(flag_name) => get_default(&flag_name),
        None => false,
    };
    make_rust(
        current_rolled_out_flag_idx,
        deactivate_saved_state_rollout,
        force_flag_value,
        default,
    )
}

/// `let default : t = default_saved_state_rollouts ()`
pub fn default() -> T {
    SavedStateRollouts::default()
}

/// Prints `<flag> = <bool>` on stderr for each flag.
pub fn output(t: &T) {
    let print_flag = |flag: Flag, value: bool| eprint!("{} = {}\n", flag_name(flag), value);
    let SavedStateRollouts {
        optimized_member_fanout,
        new_naming_table,
    } = t;
    print_flag(Flag::OptimizedMemberFanout, *optimized_member_fanout);
    print_flag(Flag::NewNamingTable, *new_naming_table);
}

pub fn to_bit_array_string(t: &T) -> String {
    let s = |b: bool| match b {
        true => "1",
        false => "0",
    };
    let SavedStateRollouts {
        optimized_member_fanout,
        new_naming_table,
    } = t;
    s(*optimized_member_fanout).to_string() + s(*new_naming_table)
}

pub fn to_yojson(t: &T) -> yojson::T {
    let SavedStateRollouts {
        optimized_member_fanout,
        new_naming_table,
    } = t;
    yojson::T::Assoc(vec![
        (
            "optimized_member_fanout".to_string(),
            yojson::T::Bool(*optimized_member_fanout),
        ),
        (
            "new_naming_table".to_string(),
            yojson::T::Bool(*new_naming_table),
        ),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flag_names() {
        assert_eq!(
            flag_name(Flag::OptimizedMemberFanout),
            "optimized_member_fanout"
        );
        assert_eq!(flag_name(Flag::NewNamingTable), "new_naming_table");
    }

    #[test]
    fn make_follows_the_rollout_order() {
        // No flag is being rolled out at index 0: every flag is to come.
        let t = make(0, false, |_| true, None);
        assert_eq!(t, default());
        assert_eq!(to_bit_array_string(&t), "00");
        // Index 7 is `new_naming_table`, whose value is the default; the
        // flags of lower order are rolled out.
        let asked = std::cell::RefCell::new(vec![]);
        let t = make(
            7,
            false,
            |name| {
                asked.borrow_mut().push(name.to_string());
                true
            },
            None,
        );
        assert_eq!(asked.into_inner(), vec!["new_naming_table".to_string()]);
        assert_eq!(to_bit_array_string(&t), "11");
        assert_eq!(to_bit_array_string(&make(7, true, |_| true, None)), "10");
        assert_eq!(
            to_bit_array_string(&make(7, false, |_| true, Some("prod"))),
            "10"
        );
        assert_eq!(
            to_bit_array_string(&make(0, false, |_| false, Some("candidate"))),
            "00"
        );
        assert_eq!(
            yojson::to_string(&to_yojson(&t)),
            r#"{"optimized_member_fanout":true,"new_naming_table":true}"#
        );
    }

    #[test]
    #[should_panic(expected = "ForceFlagError(\"bogus\")")]
    fn make_with_a_bad_ss_force() {
        make(0, false, |_| false, Some("bogus"));
    }

    #[test]
    #[should_panic(
        expected = "called `Result::unwrap()` on an `Err` value: IntOutOfRange(TryFromIntError(()))"
    )]
    fn make_with_a_negative_index() {
        make(-1, false, |_| false, None);
    }
}
