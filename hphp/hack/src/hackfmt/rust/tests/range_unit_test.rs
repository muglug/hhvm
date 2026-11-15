// Copyright (c) 2017, Facebook, Inc.
// All rights reserved.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of hphp/hack/test/hackfmt/hackfmt_range_unit_test.ml.

const SUM: &str = "<?hh
function sum($a, $b) {
  return $a + $b;
}";

fn format_range(src: &str, range: (isize, isize)) -> String {
    // Like the OCaml test, parse without checking for syntax errors.
    let tree = hackfmt::parse(src.as_bytes(), "<format_range>", false, true);
    String::from_utf8(hackfmt::format_range(None, range, &tree)).unwrap()
}

fn assert_range_formats_to(src: &str, rng: ((isize, isize), &str), exp: &str) {
    let (range, expected_substring) = rng;
    // As a sanity check, and a convenience to the reader, require tests to
    // provide the text of the range they are formatting.
    assert_eq!(
        expected_substring,
        &src[range.0 as usize..range.1 as usize],
        "Provided range ({},{}) doesn't match source text substring",
        range.0,
        range.1
    );
    // Perform the actual test.
    assert_eq!(exp, format_range(src, range));
}

fn fs(n: usize) -> String {
    "f".repeat(n)
}

#[test]
fn first_token_on_line() {
    assert_range_formats_to(SUM, ((30, 36), "return"), "  return");
}

#[test]
fn token_with_leading_indentation() {
    assert_range_formats_to(SUM, ((28, 36), "  return"), "  return");
}

#[test]
fn trailing_newline() {
    assert_range_formats_to(SUM, ((26, 28), "{\n"), "{\n");
}

#[test]
fn trailing_newline_omitted() {
    assert_range_formats_to(SUM, ((26, 27), "{"), "{\n");
}

#[test]
fn trailing_newline_character() {
    assert_range_formats_to(SUM, ((27, 28), "\n"), "");
}

#[test]
fn leading_whitespace() {
    assert_range_formats_to(SUM, ((28, 30), "  "), "");
}

#[test]
fn inline_whitespace() {
    assert_range_formats_to(SUM, ((36, 37), " "), "");
}

#[test]
fn end_of_file() {
    assert_range_formats_to(SUM, ((46, 47), "}"), "}\n");
}

#[test]
fn operator_surrounding_whitespace() {
    assert_range_formats_to("$a + $b", ((2, 5), " + "), "+");
}

#[test]
fn operator_without_whitespace() {
    assert_range_formats_to("$a + $b", ((3, 4), "+"), "+");
}

#[test]
fn up_to_blank_line() {
    assert_range_formats_to("a;\n\nb;", ((0, 3), "a;\n"), "a;\n");
}

#[test]
fn blank_line_at_end() {
    assert_range_formats_to("a;\n\nb;", ((0, 4), "a;\n\n"), "a;\n\n");
}

#[test]
fn blank_line_at_start() {
    assert_range_formats_to("a;\n\nb;", ((3, 6), "\nb;"), "\nb;\n");
}

#[test]
fn comma_at_start_of_range() {
    assert_range_formats_to("f($x, $y)", ((4, 8), ", $y"), ", $y");
}

// When the formatter inserts a trailing comma, ensure that it is printed only
// if the atom preceding it is printed.
#[test]
fn trailing_comma_inserted_at_start_of_range() {
    let src = format!("<?hh\n{}($x,$y)", fs(95));
    assert_range_formats_to(&src, ((106, 107), ")"), ")\n");
}

#[test]
fn trailing_comma_inserted_at_end_of_range() {
    let src = format!("<?hh\n{}($x,$y)", fs(95));
    assert_range_formats_to(&src, ((104, 106), "$y"), "  $y,\n");
}

// If a trailing comma was already present outside the range, don't include it
// in the formatted output.
#[test]
fn trailing_comma_existed_at_start_of_range() {
    let src = format!("<?hh\n{}($x,$y,)", fs(95));
    assert_range_formats_to(&src, ((107, 108), ")"), ")\n");
}

#[test]
fn trailing_comma_existed_at_end_of_range() {
    let src = format!("<?hh\n{}($x,$y,)", fs(95));
    assert_range_formats_to(&src, ((104, 106), "$y"), "  $y");
}

#[test]
fn trailing_comma_included_at_start_of_range() {
    let src = format!("<?hh\n{}($x,$y,)", fs(95));
    assert_range_formats_to(&src, ((106, 108), ",)"), ",\n)\n");
}

#[test]
fn trailing_comma_included_at_end_of_range() {
    let src = format!("<?hh\n{}($x,$y,)", fs(95));
    assert_range_formats_to(&src, ((104, 107), "$y,"), "  $y,\n");
}

#[test]
fn trailing_comma_is_entire_range() {
    let src = format!("<?hh\n{}($x,$y,)", fs(95));
    assert_range_formats_to(&src, ((106, 107), ","), ",\n");
}

#[test]
fn deleted_trailing_comma_is_entire_range() {
    assert_range_formats_to("f($x,$y,)", ((7, 8), ","), "");
}
