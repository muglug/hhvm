// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `simplihack_check.ml`. See `hh/PORTING.md`.

use md5::Digest;
use naming_special_names_rust as sn;

use crate::simplihack_interpreter;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_error;
use crate::typing_error::primary::simplihack;

/// Helper function to compute digest of a string
/// (`Md5.digest_string str |> Md5.to_hex`)
pub fn compute_digest(str: impl AsRef<[u8]>) -> String {
    let digest = md5::Md5::digest(str.as_ref());
    digest.iter().map(|b| format!("{:02x}", b)).collect()
}

pub fn report_error(env: &Env, err: simplihack::T) {
    tast_env::add_typing_error(&typing_error::simplihack(err), env)
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_user_attribute(&mut self, env: &Env, ua: &'a tast::UserAttribute) {
        let tast::UserAttribute {
            name: ua_name,
            params: ua_params,
        } = ua;
        if ua_name.1 == sn::user_attributes::SIMPLIHACK {
            match ua_params.as_slice() {
                [prompt] => {
                    // We evaluate the prompt in order to record dependencies, though we do not include
                    // the hash of the prompt in the error message.
                    let prompt_value = simplihack_interpreter::eval(env, prompt);
                    let err = match prompt_value {
                        Ok(_) => {
                            // Report a SimpliHackRunPrompt error. This error should point to the position of the prompt expression
                            // and tell the user to run an AI Code Action by clicking on that position in the file.
                            let pos = tast::get_position(prompt).clone();
                            simplihack::T::Run_prompt { pos }
                        }
                        Err(err) => err,
                    };
                    report_error(env, err)
                }
                [prompt, hash] => {
                    // Evalute prompt and hash using Simplihack_interpreter.eval. If both evaluate to a string then do the following.
                    // Hash is a Digest encoded as a string.
                    // Prompt is a string, convert it to a digest.
                    //
                    // Compare the two Digest, if they are different report a SimpliHackRerunPrompt error. The error message should contain
                    // the two digests and suggest to re-run the AI Code Action
                    let prompt_pos = tast::get_position(prompt).clone();

                    // Evaluate prompt and hash expressions
                    let prompt_value = simplihack_interpreter::eval(env, prompt);
                    let hash_value = simplihack_interpreter::eval(env, hash);
                    match (prompt_value, hash_value) {
                        (Ok(prompt_str), Ok(expected_digest)) => {
                            // Compute digest of prompt string
                            let prompt_digest = compute_digest(&prompt_str);

                            // Compare digests
                            if prompt_digest.as_bytes() != expected_digest.as_slice() {
                                report_error(
                                    env,
                                    simplihack::T::Rerun_prompt {
                                        pos: prompt_pos,
                                        prompt_digest,
                                        expected_digest: expected_digest.to_string(),
                                    },
                                )
                            }
                        }
                        (err1, err2) => {
                            if let Err(err) = err1 {
                                report_error(env, err)
                            }
                            if let Err(err) = err2 {
                                report_error(env, err)
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digest() {
        assert_eq!(compute_digest(""), "d41d8cd98f00b204e9800998ecf8427e");
        assert_eq!(compute_digest("abc"), "900150983cd24fb0d6963f7d28e17f72");
    }
}
