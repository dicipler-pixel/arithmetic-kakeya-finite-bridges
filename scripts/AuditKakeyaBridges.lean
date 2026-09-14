import OperatorFirst.KakeyaDenominators
import OperatorFirst.KakeyaCutCompletion
import OperatorFirst.KakeyaForcingBridge
import OperatorFirst.KakeyaAuditControls
import OperatorFirst.KakeyaCutAssumptionControl
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Inventory by defining module, not namespace. Include definitions, generated
declarations, theorem types and transitive axiom dependencies. The accompanying
human definition audit is still required: a clean axiom list alone cannot
establish that a theorem's hypotheses match its advertised mathematical scope.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`OperatorFirst.KakeyaDenominators,
    `OperatorFirst.KakeyaCutCompletion, `OperatorFirst.KakeyaForcingBridge,
    `OperatorFirst.KakeyaAuditControls, `OperatorFirst.KakeyaCutAssumptionControl]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx]!
    unless modules.contains mod do continue
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "unapproved axiom {ax} in {name}"
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive"
    if kind == "axiom" then
      throwError "new axiom declaration {name}"
    let typeText ← liftTermElabM do
      withOptions (fun opts => opts.setBool `pp.fullNames true |>.setBool `pp.universes true) do
        return (← Meta.ppExpr info.type).pretty
    let bodyText ← liftTermElabM do
      match info with
      | .defnInfo value => return (← Meta.ppExpr value.value).pretty
      | .opaqueInfo value => return (← Meta.ppExpr value.value).pretty
      | _ => return ""
    let row := Json.mkObj [
      ("module", toJson mod.toString), ("name", toJson name.toString),
      ("kind", toJson kind), ("type", toJson typeText),
      ("definition_body", toJson bodyText),
      ("axioms", toJson (axioms.map Name.toString))]
    logInfo m!"AUDIT_JSON {row.compress}"
    count := count + 1
  if count == 0 then throwError "empty module inventory"
  logInfo m!"AUDIT_TOTAL {count}"
