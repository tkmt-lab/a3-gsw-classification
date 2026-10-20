import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Build-time dependency inspection. This command creates no theorem and is not
used as a proof rule. It rejects every transitive axiom outside the three listed
standard axioms, including compiler trust and sorryAx. -/
open Lean Elab Command

elab "standard_axioms " ids:ident+ : command => do
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let dependencies ← Lean.collectAxioms name
    for dependency in dependencies do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name}: forbidden axiom {dependency}"
    logInfo m!"standard-axiom gate PASS: {name} ({dependencies.toList})"
