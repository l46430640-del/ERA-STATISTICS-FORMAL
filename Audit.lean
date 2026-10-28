import BianchiIX
import Lean

/-! Check every project declaration, including dependencies of private lemmas. -/

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    if (`BianchiIX).isPrefixOf (privateToUserName name) then
      declarations := declarations + 1
      if info.isTheorem then
        theorems := theorems + 1
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
  if theorems == 0 then
    throwError "No BianchiIX theorems were audited"
  logInfo m!"Axiom audit passed: {theorems} theorem declarations (including generated ones), {declarations} total declarations."

#check BianchiIX.Literature.BirkhoffErgodicInput
#check BianchiIX.Literature.BrehmIXAttractorInput
#check BianchiIX.exists_full_measure_era_statistics
#print axioms BianchiIX.exists_full_measure_era_statistics
