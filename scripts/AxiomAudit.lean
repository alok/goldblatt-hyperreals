import Goldblatt
/-!
Axiom audit: walks every declaration of the `Goldblatt` library and reports the union of
the axioms they depend on, plus the declarations that mention `sorryAx` directly.
Run with `lake env lean scripts/AxiomAudit.lean`.
-/
open Lean

partial def auditVisit (env : Environment) (n : Name) : StateM (NameSet × NameSet) Unit := do
  let (seen, _) ← get
  if seen.contains n then return
  modify fun (s, a) => (s.insert n, a)
  match env.find? n with
  | some ci =>
    if let .axiomInfo _ := ci then modify fun (s, a) => (s, a.insert n)
    for d in ci.getUsedConstantsAsSet do auditVisit env d
  | none => pure ()

run_cmd do
  let env ← getEnv
  let mut st : NameSet × NameSet := ({}, {})
  let mut count : Nat := 0
  let mut direct : Array Name := #[]
  for (n, ci) in env.constants.map₁ do
    if let some idx := env.getModuleIdxFor? n then
      if (env.header.moduleNames[idx.toNat]!).getRoot == `Goldblatt then
        count := count + 1
        st := ((auditVisit env n).run st).2
        if ci.getUsedConstantsAsSet.contains ``sorryAx then direct := direct.push n
  logInfo m!"{count} declarations; axioms used: {st.2.toList}; declarations using sorry directly ({direct.size}): {direct}"
