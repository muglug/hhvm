// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `hh_version.ml`. See `hh/PORTING.md`.

use std::sync::LazyLock;

use crate::build_banner;
use crate::build_id;
use crate::yojson::safe as yojson;

/// Monotonically increasing identifier that can be used when we introduce
/// backward incompatible changes in hh_client commands, and to signal
/// new capabilities to clients.
/// v1 (hvvm 3.15, 11 May 2016) - persistent connection introduced
/// v4 (hvvm 3.18, 7 Nov 2016) - persistent connection stable
/// v5 (hvvm 3.23, 17 Nov 2017) - 'hh_client lsp' stable
#[allow(non_upper_case_globals)]
pub const api_version: isize = 5;

static VERSION: LazyLock<String> = LazyLock::new(|| match build_banner::banner() {
    Some(banner) => banner,
    None => build_id::build_revision() + " " + &build_id::build_commit_time_string(),
});

static VERSION_JSON: LazyLock<yojson::T> = LazyLock::new(|| {
    yojson::T::Assoc(vec![
        (
            "commit".to_string(),
            yojson::T::String(build_id::build_revision()),
        ),
        (
            "commit_time".to_string(),
            yojson::T::Int(build_id::build_commit_time()),
        ),
        (
            "build_mode".to_string(),
            yojson::T::String(build_id::build_mode()),
        ),
        ("api_version".to_string(), yojson::T::Int(api_version)),
    ])
});

pub fn version() -> String {
    VERSION.clone()
}

pub fn version_json() -> yojson::T {
    VERSION_JSON.clone()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn version_json_keys_in_order() {
        let json = yojson::to_string(&version_json());
        let expected = format!(
            r#"{{"commit":"{}","commit_time":{},"build_mode":"","api_version":5}}"#,
            build_id::build_revision(),
            build_id::build_commit_time()
        );
        assert_eq!(json, expected);
    }

    #[test]
    fn version_is_banner_or_revision_and_time() {
        match build_banner::banner() {
            Some(banner) => {
                assert_eq!(version(), banner);
                // `hackc-<sha1>-<hhvm version>`
                assert!(banner.starts_with("hackc-"), "{banner}");
            }
            None => assert_eq!(
                version(),
                format!(
                    "{} {}",
                    build_id::build_revision(),
                    build_id::build_commit_time_string()
                )
            ),
        }
    }
}
