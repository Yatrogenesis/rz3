// SPDX-License-Identifier: MIT
//! Fail-closed regression battery for strings and regular expressions (QF_S / QF_SLIA).
//!
//! Each case carries the verdict Z3 gives (recorded 2026-10-08). RZ3 may answer
//! `unknown` or return an explicit parse/unsupported error, but it must NEVER answer
//! `sat` where Z3 says `unsat` or vice versa, and must never accept a script by
//! silently dropping string constructs.

use rz3::driver::check_script;
use rz3::SolverResult;

/// (name, script, z3 verdict: "sat" | "unsat" | "unknown" | "error"). When Z3 itself
/// answers unknown or errors, any definite RZ3 verdict would be unverified and is rejected.
const CASES: &[(&str, &str, &str)] = &[
    (
        "s1",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= x "abc"))(assert (= (str.len x) 3))(check-sat)"##,
        "sat",
    ),
    (
        "s10",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.replace x "a" "b") "bb"))(assert (= x "ab"))(check-sat)"##,
        "sat",
    ),
    (
        "s11",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.replace "aaa" "a" "b") x))(check-sat)"##,
        "sat",
    ),
    (
        "s12",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.replace "aaa" "a" "b") "baa"))(check-sat)"##,
        "sat",
    ),
    (
        "s13",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.replace_all "aaa" "a" "b") x))(assert (= x "bbb"))(check-sat)"##,
        "sat",
    ),
    (
        "s14",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.to_int x) 12))(assert (= (str.len x) 3))(check-sat)"##,
        "sat",
    ),
    (
        "s15",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.to_int x) 12))(assert (= (str.len x) 2))(check-sat)"##,
        "sat",
    ),
    (
        "s16",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.from_int i) "007"))(check-sat)"##,
        "unsat",
    ),
    (
        "s17",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.from_int i) "7"))(check-sat)"##,
        "sat",
    ),
    (
        "s18",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (int.to.str i) "42"))(check-sat)"##,
        "sat",
    ),
    (
        "s19",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.to.int x) (- 5)))(check-sat)"##,
        "unsat",
    ),
    (
        "s2",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= x "abc"))(assert (= (str.len x) 4))(check-sat)"##,
        "unsat",
    ),
    (
        "s20",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.to_int x) (- 1)))(assert (= x "12"))(check-sat)"##,
        "unsat",
    ),
    (
        "s21",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.contains x "ab"))(assert (= (str.len x) 1))(check-sat)"##,
        "unsat",
    ),
    (
        "s22",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.contains x "ab"))(assert (not (str.contains x "a")))(check-sat)"##,
        "unsat",
    ),
    (
        "s23",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.indexof x "a" 0) 2))(assert (= (str.len x) 2))(check-sat)"##,
        "unsat",
    ),
    (
        "s24",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.indexof "abca" "a" 1) 3))(check-sat)"##,
        "sat",
    ),
    (
        "s25",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.indexof "abca" "a" 1) 0))(check-sat)"##,
        "unsat",
    ),
    (
        "s26",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.substr "hello" 1 3) x))(assert (not (= x "ell")))(check-sat)"##,
        "unsat",
    ),
    (
        "s27",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.substr x 0 2) "ab"))(assert (= (str.len x) 1))(check-sat)"##,
        "unsat",
    ),
    (
        "s28",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.< x y))(assert (str.< y x))(check-sat)"##,
        "unsat",
    ),
    (
        "s29",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.<= x y))(assert (str.<= y x))(assert (not (= x y)))(check-sat)"##,
        "unsat",
    ),
    (
        "s3",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.++ x y) "ab"))(assert (= (str.len x) 3))(check-sat)"##,
        "unsat",
    ),
    (
        "s30",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= x "\u{41}"))(assert (= (str.len x) 1))(check-sat)"##,
        "sat",
    ),
    (
        "s31",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= x "\x41"))(assert (= (str.len x) 1))(check-sat)"##,
        "unsat",
    ),
    (
        "s32",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x (re.range "a" "c")))(assert (= x "d"))(check-sat)"##,
        "unsat",
    ),
    (
        "s33",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x (re.union (str.to_re "a") (str.to_re "b"))))(assert (= x "c"))(check-sat)"##,
        "unsat",
    ),
    (
        "s34",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x (re.inter (re.* (str.to_re "a")) (re.+ (str.to_re "b")))))(check-sat)"##,
        "unsat",
    ),
    (
        "s35",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x (re.comp (str.to_re "a"))))(assert (= x "a"))(check-sat)"##,
        "unsat",
    ),
    (
        "s36",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x ((_ re.loop 2 3) (str.to_re "a"))))(assert (= (str.len x) 4))(check-sat)"##,
        "unsat",
    ),
    (
        "s37",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x ((_ re.^ 2) (str.to_re "a"))))(assert (= x "aa"))(check-sat)"##,
        "sat",
    ),
    (
        "s38",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x (re.opt (str.to_re "a"))))(assert (> (str.len x) 1))(check-sat)"##,
        "unsat",
    ),
    (
        "s39",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x re.allchar))(assert (= (str.len x) 2))(check-sat)"##,
        "unsat",
    ),
    (
        "s4",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x (re.+ (str.to_re "a"))))(assert (= (str.len x) 0))(check-sat)"##,
        "unsat",
    ),
    (
        "s40",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x re.none))(check-sat)"##,
        "unsat",
    ),
    (
        "s41",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x (re.diff re.all (str.to_re "a"))))(assert (= x "a"))(check-sat)"##,
        "unsat",
    ),
    (
        "s42",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.is_digit x))(assert (= x "a"))(check-sat)"##,
        "unsat",
    ),
    (
        "s43",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.to_code x) 97))(check-sat)"##,
        "sat",
    ),
    (
        "s44",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.from_code 98) x))(assert (= x "a"))(check-sat)"##,
        "unsat",
    ),
    (
        "s45",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.rev x) "ab"))(check-sat)"##,
        "error",
    ),
    (
        "s46",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re (str.++ x y) (re.+ (str.to_re "a"))))(assert (= y "b"))(check-sat)"##,
        "unsat",
    ),
    (
        "s47",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.++ x "b") (str.++ "a" y)))(assert (not (= x "a")))(assert (< (str.len x) 1))(check-sat)"##,
        "unsat",
    ),
    (
        "s48",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.len x) (- 1)))(check-sat)"##,
        "unsat",
    ),
    (
        "s49",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.len x) i))(assert (< i 0))(check-sat)"##,
        "unsat",
    ),
    (
        "s5",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x (re.* (str.to_re "ab"))))(assert (= (str.len x) 3))(check-sat)"##,
        "unsat",
    ),
    (
        "s50",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.replace_re x (re.+ (str.to_re "a")) "c") "c"))(check-sat)"##,
        "unknown",
    ),
    (
        "s51",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.replace_re_all x (str.to_re "a") "c") "cc"))(assert (= (str.len x) 2))(check-sat)"##,
        "unknown",
    ),
    (
        "s52",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (distinct x y))(assert (= (str.len x) 0))(assert (= (str.len y) 0))(check-sat)"##,
        "unsat",
    ),
    (
        "s53",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.in_re x (re.* (re.union (str.to_re "ab") (str.to_re "c")))))(assert (str.prefixof "cc" x))(assert (= (str.len x) 3))(check-sat)"##,
        "sat",
    ),
    (
        "s54",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (foo.bar x))(check-sat)"##,
        "error",
    ),
    (
        "s55",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.frobnicate x) "a"))(check-sat)"##,
        "error",
    ),
    (
        "s56",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= x (str.++ x "a")))(check-sat)"##,
        "unsat",
    ),
    (
        "s6",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.prefixof "ab" x))(assert (str.prefixof "ba" x))(check-sat)"##,
        "unsat",
    ),
    (
        "s7",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (str.prefixof "ab" x))(assert (str.suffixof "ba" x))(assert (= (str.len x) 3))(check-sat)"##,
        "sat",
    ),
    (
        "s8",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.at x 0) "a"))(assert (= (str.at x 0) "b"))(check-sat)"##,
        "unsat",
    ),
    (
        "s9",
        r##"(set-logic QF_SLIA)(declare-const x String)(declare-const y String)(declare-const i Int)(assert (= (str.at x 1) "z"))(assert (= (str.len x) 2))(check-sat)"##,
        "sat",
    ),
    (
        "g1",
        r##"(set-logic QF_SLIA)(assert (= (str.len "abc") 3))(check-sat)"##,
        "sat",
    ),
    (
        "g2",
        r##"(set-logic QF_SLIA)(assert (= (str.len "abc") 4))(check-sat)"##,
        "unsat",
    ),
    (
        "g3",
        r##"(set-logic QF_SLIA)(assert (= (str.++ "a" "b") "ab"))(check-sat)"##,
        "sat",
    ),
    (
        "g4",
        r##"(set-logic QF_SLIA)(assert (= (str.++ "a" "b") "ba"))(check-sat)"##,
        "unsat",
    ),
    (
        "g5",
        r##"(set-logic QF_SLIA)(assert (str.prefixof "ab" "abc"))(check-sat)"##,
        "sat",
    ),
    (
        "g6",
        r##"(set-logic QF_SLIA)(assert (str.prefixof "bc" "abc"))(check-sat)"##,
        "unsat",
    ),
    (
        "g7",
        r##"(set-logic QF_SLIA)(assert (str.suffixof "bc" "abc"))(check-sat)"##,
        "sat",
    ),
    (
        "g8",
        r##"(set-logic QF_SLIA)(assert (str.contains "abc" "bd"))(check-sat)"##,
        "unsat",
    ),
    (
        "g9",
        r##"(set-logic QF_SLIA)(assert (= (str.at "abc" 1) "b"))(check-sat)"##,
        "sat",
    ),
    (
        "g10",
        r##"(set-logic QF_SLIA)(assert (= (str.at "abc" 5) ""))(check-sat)"##,
        "sat",
    ),
    (
        "g11",
        r##"(set-logic QF_SLIA)(assert (= (str.replace "aaa" "a" "b") "baa"))(check-sat)"##,
        "sat",
    ),
    (
        "g12",
        r##"(set-logic QF_SLIA)(assert (= (str.replace "aaa" "a" "b") "bbb"))(check-sat)"##,
        "unsat",
    ),
    (
        "g13",
        r##"(set-logic QF_SLIA)(assert (= (str.replace_all "aaa" "a" "b") "bbb"))(check-sat)"##,
        "sat",
    ),
    (
        "g14",
        r##"(set-logic QF_SLIA)(assert (= (str.to_int "12") 12))(check-sat)"##,
        "sat",
    ),
    (
        "g15",
        r##"(set-logic QF_SLIA)(assert (= (str.to_int "1x") (- 1)))(check-sat)"##,
        "sat",
    ),
    (
        "g16",
        r##"(set-logic QF_SLIA)(assert (= (str.from_int 7) "7"))(check-sat)"##,
        "sat",
    ),
    (
        "g17",
        r##"(set-logic QF_SLIA)(assert (= (str.from_int (- 3)) ""))(check-sat)"##,
        "sat",
    ),
    (
        "g18",
        r##"(set-logic QF_SLIA)(assert (= (int.to.str 42) "42"))(check-sat)"##,
        "sat",
    ),
    (
        "g19",
        r##"(set-logic QF_SLIA)(assert (= (str.to.int "42") 42))(check-sat)"##,
        "sat",
    ),
    (
        "g20",
        r##"(set-logic QF_SLIA)(assert (= (str.indexof "abca" "a" 1) 3))(check-sat)"##,
        "sat",
    ),
    (
        "g21",
        r##"(set-logic QF_SLIA)(assert (= (str.indexof "abca" "a" 1) 0))(check-sat)"##,
        "unsat",
    ),
    (
        "g22",
        r##"(set-logic QF_SLIA)(assert (= (str.indexof "abc" "" 4) (- 1)))(check-sat)"##,
        "sat",
    ),
    (
        "g23",
        r##"(set-logic QF_SLIA)(assert (= (str.substr "hello" 1 3) "ell"))(check-sat)"##,
        "sat",
    ),
    (
        "g24",
        r##"(set-logic QF_SLIA)(assert (= (str.substr "hello" 3 10) "lo"))(check-sat)"##,
        "sat",
    ),
    (
        "g25",
        r##"(set-logic QF_SLIA)(assert (= (str.substr "hello" (- 1) 2) ""))(check-sat)"##,
        "sat",
    ),
    (
        "g26",
        r##"(set-logic QF_SLIA)(assert (str.< "a" "b"))(check-sat)"##,
        "sat",
    ),
    (
        "g27",
        r##"(set-logic QF_SLIA)(assert (str.< "b" "a"))(check-sat)"##,
        "unsat",
    ),
    (
        "g28",
        r##"(set-logic QF_SLIA)(assert (str.<= "a" "a"))(check-sat)"##,
        "sat",
    ),
    (
        "g29",
        r##"(set-logic QF_SLIA)(assert (= "\u{41}" "A"))(check-sat)"##,
        "sat",
    ),
    (
        "g30",
        r##"(set-logic QF_SLIA)(assert (= "\x41" "A"))(check-sat)"##,
        "unsat",
    ),
    (
        "g31",
        r##"(set-logic QF_SLIA)(assert (= (str.len "\u{1F600}") 1))(check-sat)"##,
        "sat",
    ),
    (
        "g32",
        r##"(set-logic QF_SLIA)(assert (= (str.len "a""b") 3))(check-sat)"##,
        "sat",
    ),
    (
        "g33",
        r##"(set-logic QF_SLIA)(assert (str.in_re "aab" (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))(check-sat)"##,
        "sat",
    ),
    (
        "g34",
        r##"(set-logic QF_SLIA)(assert (str.in_re "ab" (re.+ (str.to_re "a"))))(check-sat)"##,
        "unsat",
    ),
    (
        "g35",
        r##"(set-logic QF_SLIA)(assert (str.in_re "b" (re.range "a" "c")))(check-sat)"##,
        "sat",
    ),
    (
        "g36",
        r##"(set-logic QF_SLIA)(assert (str.in_re "d" (re.range "a" "c")))(check-sat)"##,
        "unsat",
    ),
    (
        "g37",
        r##"(set-logic QF_SLIA)(assert (str.in_re "a" (re.comp (str.to_re "a"))))(check-sat)"##,
        "unsat",
    ),
    (
        "g38",
        r##"(set-logic QF_SLIA)(assert (str.in_re "aaa" ((_ re.loop 2 3) (str.to_re "a"))))(check-sat)"##,
        "sat",
    ),
    (
        "g39",
        r##"(set-logic QF_SLIA)(assert (str.in_re "aaaa" ((_ re.loop 2 3) (str.to_re "a"))))(check-sat)"##,
        "unsat",
    ),
    (
        "g40",
        r##"(set-logic QF_SLIA)(assert (str.in_re "aa" ((_ re.^ 2) (str.to_re "a"))))(check-sat)"##,
        "sat",
    ),
    (
        "g41",
        r##"(set-logic QF_SLIA)(assert (str.in_re "" (re.opt (str.to_re "a"))))(check-sat)"##,
        "sat",
    ),
    (
        "g42",
        r##"(set-logic QF_SLIA)(assert (str.in_re "ab" re.allchar))(check-sat)"##,
        "unsat",
    ),
    (
        "g43",
        r##"(set-logic QF_SLIA)(assert (str.in_re "" re.none))(check-sat)"##,
        "unsat",
    ),
    (
        "g44",
        r##"(set-logic QF_SLIA)(assert (str.in_re "ab" re.all))(check-sat)"##,
        "sat",
    ),
    (
        "g45",
        r##"(set-logic QF_SLIA)(assert (str.in_re "a" (re.inter (re.* (str.to_re "a")) (re.+ (str.to_re "b")))))(check-sat)"##,
        "unsat",
    ),
    (
        "g46",
        r##"(set-logic QF_SLIA)(assert (str.in_re "a" (re.diff re.all (str.to_re "a"))))(check-sat)"##,
        "unsat",
    ),
    (
        "g47",
        r##"(set-logic QF_SLIA)(assert (str.is_digit "5"))(check-sat)"##,
        "sat",
    ),
    (
        "g48",
        r##"(set-logic QF_SLIA)(assert (str.is_digit "a"))(check-sat)"##,
        "unsat",
    ),
    (
        "g49",
        r##"(set-logic QF_SLIA)(assert (= (str.to_code "a") 97))(check-sat)"##,
        "sat",
    ),
    (
        "g50",
        r##"(set-logic QF_SLIA)(assert (= (str.from_code 98) "b"))(check-sat)"##,
        "sat",
    ),
    (
        "g51",
        r##"(set-logic QF_SLIA)(assert (= (str.rev "ab") "ba"))(check-sat)"##,
        "error",
    ),
    (
        "g52",
        r##"(set-logic QF_SLIA)(assert (= (str.replace_re "baab" (re.+ (str.to_re "a")) "c") "bcb"))(check-sat)"##,
        "unknown",
    ),
    (
        "g53",
        r##"(set-logic QF_SLIA)(assert (= (str.replace_re_all "aa" (str.to_re "a") "c") "cc"))(check-sat)"##,
        "unknown",
    ),
    (
        "g54",
        r##"(set-logic QF_SLIA)(assert (str.in_re "ab" (re.union (str.to_re "a") (str.to_re "ab"))))(check-sat)"##,
        "sat",
    ),
    (
        "g55",
        r##"(set-logic QF_SLIA)(assert (str.in_re "ab" (str.to_re "a")))(check-sat)"##,
        "unsat",
    ),
    (
        "g56",
        r##"(set-logic QF_SLIA)(assert (distinct "a" "b"))(check-sat)"##,
        "sat",
    ),
    (
        "g57",
        r##"(set-logic QF_SLIA)(assert (= (str.frobnicate "a") "a"))(check-sat)"##,
        "error",
    ),
    (
        "h1",
        r##"(set-logic ALL)(declare-fun f (String) Int)(assert (= (f "a") 1))(assert (= (f "a") 2))(check-sat)"##,
        "unsat",
    ),
    (
        "h2",
        r##"(set-logic ALL)(declare-fun f (Int) String)(assert (= (f 1) (f 2)))(assert (not (= (f 1) (f 2))))(check-sat)"##,
        "unsat",
    ),
    (
        "h3",
        r##"(set-logic ALL)(define-sort S () String)(declare-const x S)(assert (= x "a"))(assert (= x "b"))(check-sat)"##,
        "unsat",
    ),
    (
        "h4",
        r##"(set-logic ALL)(define-sort S () String)(declare-const x S)(assert (not (= x x)))(check-sat)"##,
        "unsat",
    ),
    (
        "h5",
        r##"(set-logic ALL)(declare-const x String)(assert (not (= x x)))(check-sat)"##,
        "unsat",
    ),
    (
        "h6",
        r##"(set-logic ALL)(define-fun s () String "a")(assert (= s "b"))(check-sat)"##,
        "unsat",
    ),
    (
        "h7",
        r##"(set-logic ALL)(define-fun s ((n Int)) String "a")(assert (not (= (s 1) (s 1))))(check-sat)"##,
        "unsat",
    ),
    (
        "h8",
        r##"(set-logic ALL)(assert (forall ((s String)) (= (str.len s) 0)))(check-sat)"##,
        "unsat",
    ),
    (
        "h9",
        r##"(set-logic ALL)(assert (exists ((s String)) (< (str.len s) 0)))(check-sat)"##,
        "unsat",
    ),
    (
        "h10",
        r##"(set-logic ALL)(assert (let ((s "a")) (= (str.len s) 2)))(check-sat)"##,
        "unsat",
    ),
    (
        "h11",
        r##"(set-logic ALL)(declare-const r RegLan)(assert (not (= r r)))(check-sat)"##,
        "unsat",
    ),
    (
        "h12",
        r##"(set-logic ALL)(declare-const r (RegEx String))(assert (not (= r r)))(check-sat)"##,
        "unsat",
    ),
    (
        "h13",
        r##"(set-logic ALL)(assert (not (str.in_re "a" re.all)))(check-sat)"##,
        "unsat",
    ),
    (
        "h14",
        r##"(set-logic ALL)(assert (not (= re.all re.all)))(check-sat)"##,
        "unsat",
    ),
    (
        "h15",
        r##"(set-logic ALL)(declare-const a (Array Int String))(assert (not (= (select a 0) (select a 0))))(check-sat)"##,
        "unsat",
    ),
    (
        "h16",
        r##"(set-logic ALL)(declare-const a (Array String Int))(assert (not (= (select a "x") (select a "x"))))(check-sat)"##,
        "unsat",
    ),
    (
        "h17",
        r##"(set-logic ALL)(declare-datatypes ((D 0)) (((mk (s String)))))(declare-const d D)(assert (not (= (s d) (s d))))(check-sat)"##,
        "unsat",
    ),
    (
        "h18",
        r##"(set-logic ALL)(declare-const x Int)(assert (= x (str.len "abc")))(assert (> x 5))(check-sat)"##,
        "unsat",
    ),
    (
        "h19",
        r##"(set-logic ALL)(declare-const x Int)(assert (str.is_digit x))(check-sat)"##,
        "error",
    ),
    (
        "h20",
        r##"(set-logic ALL)(declare-const x Int)(assert (= (str.to_int x) 3))(check-sat)"##,
        "error",
    ),
    (
        "h21",
        r##"(set-logic ALL)(declare-const x Int)(assert (= (str.len x) 3))(check-sat)"##,
        "error",
    ),
    (
        "h22",
        r##"(set-logic ALL)(declare-const x Int)(assert (and (> x 0) (< x 0)))(assert (= (str.len "a") 1))(check-sat)"##,
        "unsat",
    ),
    (
        "h23",
        r##"(set-logic ALL)(declare-const x Int)(assert (> x 0))(assert (< x 0))(declare-const s String)(check-sat)"##,
        "unsat",
    ),
    (
        "h24",
        r##"(set-logic ALL)(declare-const x Int)(assert (> x 0))(assert (< x 0))(assert (str.in_re "a" (re.* re.allchar)))(check-sat)"##,
        "unsat",
    ),
    (
        "h25",
        r##"(set-logic ALL)(declare-const x Int)(assert (> x 0))(assert (< x 0))(assert (! (= (str.len "a") 1) :named n))(check-sat)"##,
        "unsat",
    ),
    (
        "h26",
        r##"(set-logic ALL)(declare-const x Int)(assert (> x 0))(push 1)(assert (= "a" "b"))(pop 1)(check-sat)"##,
        "sat",
    ),
    (
        "h27",
        r##"(set-logic ALL)(declare-const x Int)(assert (> x 0))(assert (= (re.range "a" "b") re.none))(check-sat)"##,
        "unsat",
    ),
    (
        "h30",
        r##"(set-logic ALL)(declare-const x Int)(assert (> x 0))(assert (< x 0))(check-sat-assuming ((= "a" "b")))(check-sat)"##,
        "unsat",
    ),
    (
        "h31",
        r##"(set-logic ALL)(declare-const b Bool)(declare-const x Int)(assert (> x 0))(assert (< x 0))(define-fun-rec g ((s String)) Int 0)(check-sat)"##,
        "unsat",
    ),
    (
        "h32",
        r##"(set-logic ALL)(declare-const x Int)(assert (> x 0))(assert (< x 0))(declare-fun h (Int) (Seq Int))(check-sat)"##,
        "unsat",
    ),
    (
        "h33",
        r##"(set-logic ALL)(declare-const x Int)(assert (> x 0))(assert (< x 0))(declare-const u (Seq Int))(assert (= (seq.len u) 1))(check-sat)"##,
        "unsat",
    ),
    (
        "h34",
        r##"(set-logic ALL)(declare-const x Int)(assert (> x 0))(assert (< x 0))(assert (= (str.len (as seq.empty String)) 0))(check-sat)"##,
        "unsat",
    ),
];

#[test]
fn strings_never_contradict_z3() {
    let mut bad = Vec::new();
    for (name, script, z3) in CASES {
        let got = std::panic::catch_unwind(|| check_script(script));
        let got = match got {
            Ok(g) => g,
            Err(_) => {
                bad.push(format!("{name}: panic"));
                continue;
            }
        };
        match got {
            // Explicit error is always fail-closed.
            Err(_) => {}
            Ok(v) => match v.first() {
                Some(SolverResult::Sat) if *z3 != "sat" => {
                    bad.push(format!("{name}: rz3 sat, z3 {z3}"))
                }
                Some(SolverResult::Unsat) if *z3 != "unsat" => {
                    bad.push(format!("{name}: rz3 unsat, z3 {z3}"))
                }
                _ => {}
            },
        }
    }
    assert!(bad.is_empty(), "fail-closed violations: {bad:#?}");
}
