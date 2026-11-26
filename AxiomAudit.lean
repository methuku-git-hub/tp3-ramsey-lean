module

public import TP3
import Lean.Util.CollectAxioms

/-! Audit the transitive axiom dependencies of every exported TP3 declaration,
including the unconditional main theorem. Challenge is not imported. The
independent statement comparison is performed separately by Comparator. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`TP3).isPrefixOf name then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      count := count + 1
  logInfo m!"Audited {count} exported TP3 declarations: only the three permitted axioms."
  if env.contains `TP3.ramsey_bound then
    logInfo "The main declaration is present; run Comparator to check its exact statement."
  else
    logInfo "MAIN THEOREM ABSENT: supporting lemmas only; not ready for registration."
