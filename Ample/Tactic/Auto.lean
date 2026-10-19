import Ample.Tactic.Normalize
import Ample.Tactic.Unfold
import Ample.Tactic.Injection
import Ample.Tactic.Ext
import Ample.Tactic.Indisc
import Ample.Tactic.Wlog
import Ample.Tactic.Transform
import Ample.Tactic.Congr
import Lean.Elab.Tactic.BuiltinTactic
import Lean.Elab.Tactic.Classical

/-!
`open scoped Course.Auto` normalizes expressions before and after each step in ordinary `by` proofs.
Native sequencing and proof-state information are preserved.
-/

open Lean Elab Tactic

namespace Course.Automation

syntax (name := autoByCases) "course_auto_by_cases " ident " : " term : tactic

@[tactic autoByCases]
def evalAutoByCases : Tactic := fun stx => do
  match stx with
  | `(tactic| course_auto_by_cases $h:ident : $p:term) =>
    let untouched := (← getGoals).drop 1
    classical <| evalTactic (← `(tactic| refine if $h:ident : $p then ?pos else ?neg))
    unless course.autoNormalize.get (← getOptions) do return
    let mut next := []
    for goal in ← getUnsolvedGoals do
      let marked ← if untouched.contains goal then pure goal else markClassicalGoal goal
      next := next ++ [marked]
    setGoals next
  | _ => throwUnsupportedSyntax

syntax (name := autoStep) "course_auto_step " tactic : tactic

private partial def updateStepInfo (stx : Syntax) (mctx : MetavarContext)
    (goals : List MVarId) : InfoTree → InfoTree
  | .context context tree => .context context (updateStepInfo stx mctx goals tree)
  | .node info children =>
    let info := match info with
      | .ofTacticInfo tacticInfo =>
        if tacticInfo.stx == stx then
          .ofTacticInfo { tacticInfo with mctxAfter := mctx, goalsAfter := goals }
        else info
      | _ => info
    .node info (children.map (updateStepInfo stx mctx goals))
  | .hole id => .hole id

@[tactic autoStep]
def evalAutoStep : Tactic := fun stx => do
  normalizeGoals
  withOptions (course.inAutoStep.set · true) <| evalTactic stx[1]
  normalizeGoals
  let mctx ← getMCtx
  let goals ← getUnsolvedGoals
  -- The cursor at the end of a tactic must see the same state as the following line.
  modifyInfoState fun state => { state with
    trees := state.trees.map (updateStepInfo stx[1] mctx goals)
    assignment := state.assignment.map (updateStepInfo stx[1] mctx goals)
  }

private def instrumentSequence (stx : Syntax) (bodyIndex : Nat) : Syntax := Id.run do
  let body := stx[bodyIndex]
  let args := body.getArgs.mapIdx fun i tac =>
    if i % 2 == 0 then
      Syntax.node tac.getHeadInfo ``autoStep #[Syntax.atom .none "course_auto_step ", tac]
    else tac
  return stx.setArg bodyIndex (body.setArgs args)

end Course.Automation

namespace Course.Auto

scoped macro_rules
  | `(tactic| by_cases $h:ident : $p:term) => do
    `(tactic| course_auto_by_cases $h : $p)
  | `(tactic| by_cases $p:term) => do
    `(tactic| course_auto_by_cases $(mkIdent `h):ident : $p)

@[scoped tactic Lean.Parser.Tactic.seq1, no_fallback]
def evalAutoSeq : Tactic := fun stx => do
  if course.autoNormalize.get (← getOptions) then
    evalSeq1 (Automation.instrumentSequence stx 0)
  else
    evalSeq1 stx

@[scoped tactic Lean.Parser.Tactic.tacticSeq1Indented, no_fallback]
def evalAutoIndented : Tactic := fun stx => do
  if course.autoNormalize.get (← getOptions) then
    evalTacticSeq1Indented (Automation.instrumentSequence stx 0)
  else
    evalTacticSeq1Indented stx

@[scoped tactic Lean.Parser.Tactic.tacticSeqBracketed, no_fallback]
def evalAutoBracketed : Tactic := fun stx => do
  if course.autoNormalize.get (← getOptions) then
    evalTacticSeqBracketed (Automation.instrumentSequence stx 1)
  else
    evalTacticSeqBracketed stx

end Course.Auto
