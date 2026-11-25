#!/usr/bin/env bash
# Tests for AxiomCheck.lean: compiles small core-Lean modules (no Mathlib) and checks each verdict.
# usage: scripts/worker/test_axiom_check.sh   (needs `lean` on PATH, the repository's toolchain)
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0

mod() { # name, expected exit code (0 clean, 1 reported), expected output line (regex), source
  printf '%s\n' "$4" > "$T/$1.lean"
  if ! (cd "$T" && LEAN_PATH="$T" lean -o "$1.olean" -i "$1.ilean" "$1.lean" > "$1.build" 2>&1); then
    if ! grep -q "declaration uses 'sorry'" "$T/$1.build"; then echo "FAIL $1: did not compile"; cat "$T/$1.build"; fail=1; return; fi
  fi
  out=$(LEAN_PATH="$T" lean --run "$HERE/AxiomCheck.lean" "$1" 2>&1); rc=$?
  # The exit code alone is not enough: a script that fails to compile also exits 1.
  if [ "$rc" = "$2" ] && printf '%s\n' "$out" | grep -Eq "$3"; then echo "ok   $1 (exit $rc): $(printf '%s' "$out" | head -1)"
  else echo "FAIL $1: exit $rc (expected $2), output:"; echo "$out"; fail=1; fi
}

mod Clean 0 'no escape hatches' 'theorem two : 1 + 1 = 2 := rfl'
mod CommentOnly 0 'no escape hatches' '-- an old note said: sorry, admit, axiom, native_decide
/-- The proof used to be `sorry`. -/
theorem two : 1 + 1 = 2 := rfl
def s : String := "sorry"'
mod DirectSorry 1 '^DirectSorry: t uses sorryAx' 'theorem t : 2 + 2 = 5 := by sorry'
mod Admit 1 '^Admit: t uses sorryAx' 'theorem t : 2 + 2 = 5 := by admit'
mod SorryInHave 1 '^SorryInHave: t uses sorryAx' 'theorem t : True := by
  have h : 2 + 2 = 5 := sorry
  trivial'
mod SorryInHelper 1 '^SorryInHelper: helper uses sorryAx' 'theorem helper : 2 + 2 = 5 := sorry
theorem main : 2 + 2 = 5 := helper'
mod CommentSwap 1 '^CommentSwap: t uses sorryAx' '-- this was sorry before, now it is fine
theorem t : 2 + 2 = 5 := by sorry'
mod NativeDecide 1 'declares an axiom \(from native_decide\)' 'theorem t : 10 * 10 = 100 := by native_decide'
mod NewAxiom 1 '^NewAxiom: cheat declares an axiom$' 'axiom cheat : 2 + 2 = 5
theorem t : 2 + 2 = 5 := cheat'
mod SorryDef 1 '^SorryDef: f uses sorryAx' 'def f : Nat := sorry'
# Importing a module with a sorry is not reported for the importer (only direct uses count).
mod ImportsSorry 0 'no escape hatches' 'import SorryDef
theorem g : 1 = 1 := rfl'
# Several modules at once: the clean one is not blamed for the other.
out=$(LEAN_PATH="$T" lean --run "$HERE/AxiomCheck.lean" Clean DirectSorry 2>&1); rc=$?
if [ "$rc" = 1 ] && printf '%s\n' "$out" | grep -q '^DirectSorry: t uses sorryAx' && ! printf '%s\n' "$out" | grep -q '^Clean:'; then
  echo "ok   (multi) Clean + DirectSorry: only DirectSorry reported"
else echo "FAIL (multi): exit $rc"; echo "$out"; fail=1; fi

[ $fail = 0 ] && echo "all passed" || { echo "FAILED"; exit 1; }
