/-
Copyright (c) 2026 Kevin Rajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Rajan
-/
import Lean

/-!

# Escape-hatch check for the PhyslibAlpha worker

Run as `lake env lean --run scripts/worker/AxiomCheck.lean <Module> ...` after `lake build`.

For every declaration defined in the given modules, including the auxiliary declarations Lean
generates for them (`_proof_`, `_nativeDecide_` and so on), this reports a declaration whose
type or value refers directly to

- `sorryAx` (`sorry`, `admit`, and an elaboration error that Lean replaced with `sorry`),
- `Lean.ofReduceBool`, `Lean.ofReduceNat` or `Lean.trustCompiler` (`native_decide` and
  `decide +kernel`-style shortcuts that trust the compiler instead of the kernel), or

and every `axiom` declared in these modules. It exits with code 1 if anything is reported.

Unlike searching the source text, this is not fooled by comments, strings, or a `sorry` moved
into a helper lemma or a `have`, because it reads the compiled declarations. Only direct uses
inside the given modules are reported, so existing escape hatches elsewhere in the library do
not make every importing module fail.

-/

open Lean

/-- Constants whose direct use bypasses the kernel or leaves a proof unfinished. The last three
are written as plain names because recent Lean versions no longer define them (`native_decide`
now adds its own auxiliary axiom, which the `axiom` rule below reports). -/
def escapeHatches : List Name :=
  [``sorryAx, `Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler]

/-- The reasons `ci` is reported, if any. -/
def problems (ci : ConstantInfo) : List String :=
  let used := ci.getUsedConstantsAsSet
  let hatches := escapeHatches.filter used.contains |>.map (s!"uses {·}")
  match ci with
  | .axiomInfo _ =>
    (if (`native_decide).isSuffixOf ci.name.getPrefix || ci.name.toString.contains "native_decide" then
      "declares an axiom (from native_decide)" else "declares an axiom") :: hatches
  | _ => hatches

/-- Check the declarations of the modules named on the command line. -/
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lean --run AxiomCheck.lean <Module> ..."
    return 2
  let mods := args.map String.toName
  if let some bad := args.find? fun a => a.toName.isAnonymous || a.any Char.isWhitespace then
    IO.eprintln s!"not a module name: {repr bad} (pass one module per argument)"
    return 2
  initSearchPath (← findSysroot)
  -- Only declarations are read, so environment extensions (and their initializers) are not loaded.
  let env ← importModules (mods.toArray.map fun m => { module := m }) {}
  let mut found := 0
  for (name, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless mods.contains mod do continue
    for p in problems ci do
      IO.println s!"{mod}: {name} {p}"
      found := found + 1
  if found == 0 then
    IO.println s!"no escape hatches in {mods.length} module(s)"
    return 0
  return 1
