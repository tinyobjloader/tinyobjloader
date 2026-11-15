import Tess
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Audit compiled dependencies, including imported dependencies of every
public Tess declaration. Incomplete proofs and nonstandard axioms are errors. -/
run_cmd do
  let environment ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in environment.constants.toList do
    if (`Tess).isPrefixOf name then
      count := count+1
      let dependencies ← Lean.collectAxioms name
      for axiomName in dependencies do
        unless allowed.contains axiomName do
          throwError "Tess axiom audit rejected {name}: {axiomName}"
  logInfo m!"Tess axiom audit passed: {count} declarations; standard allowlist only"
