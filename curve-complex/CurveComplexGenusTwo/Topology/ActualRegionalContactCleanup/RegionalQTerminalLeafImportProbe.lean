import CurveComplexGenusTwo.Topology.ActualQTerminalSurgery
import Lean

open Lean Elab Term in
elab "regionalOriginalQTerminalLeaf" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualQTerminalSurgery 0).append
    `CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.actual_original_essential_terminal_surgery_branches_cannot_both_be_parallel_isolated
  discard <| getConstInfo n
  return mkConst n

#check regionalOriginalQTerminalLeaf
