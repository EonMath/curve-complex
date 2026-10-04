import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualNonloopNeighborhoodAnnulus
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- Two actual arcs in the literal two-mark disk produce endpoint-relative
path homotopy while avoiding all FOUR other original branch points. No marked
isotopy, same-class assertion or homotopy certificate is assumed. -/
theorem actual_two_mark_disk_oriented_arc_path_homotopy
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (h0 : b.val.map 0 = a.val.map 0) (h1 : b.val.map 1 = a.val.map 1) :
    ∃ hu : a.val.map 0 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ,
    ∃ hv : a.val.map 1 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ,
    ∃ α β : Path (⟨a.val.map 0,hu⟩ : ↑((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ)
      ⟨a.val.map 1,hv⟩,
      (∀ t : Interval, (α t : S) = a.val.map t) ∧
      (∀ t : Interval, (β t : S) = b.val.map t) ∧ α.Homotopic β := by
  classical
  have hzero : (0 : Interval) = ⟨0,by norm_num⟩ := by apply Subtype.ext; norm_num
  have hone : (1 : Interval) = ⟨1,by norm_num⟩ := by apply Subtype.ext; norm_num
  letI : ContractibleSpace (Metric.closedBall (0 : Plane) 1) :=
    (convex_closedBall (0 : Plane) 1).contractibleSpace ⟨0,by simp⟩
  letI : ContractibleSpace N.closedSet := N.disk.symm.contractibleSpace
  let u : N.closedSet := ⟨a.val.map 0,interior_subset (N.arc_inside (mem_range_self 0))⟩
  let v : N.closedSet := ⟨a.val.map 1,interior_subset (N.arc_inside (mem_range_self 1))⟩
  let f : Path u v := {
    toFun := fun t => ⟨a.val.map t,interior_subset (N.arc_inside (mem_range_self t))⟩
    continuous_toFun := a.val.continuous.subtype_mk _
    source' := rfl
    target' := rfl }
  let g : Path u v := {
    toFun := fun t => ⟨b.val.map t,interior_subset (hb (mem_range_self t))⟩
    continuous_toFun := b.val.continuous.subtype_mk _
    source' := Subtype.ext h0
    target' := Subtype.ext h1 }
  let X := ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ
  have havoid (x : N.closedSet) : x.val ∈ X := by
    rintro ⟨hxm,hxn⟩
    have hh : x.val ∈ (M.cover.branch : Set S) ∩ N.closedSet := ⟨hxm,x.property⟩
    have hh' := N.marked_inside ▸ hh
    exact hxn (by simpa only [← hzero,← hone] using hh')
  let j : C(N.closedSet,X) := ⟨fun x => ⟨x.val,havoid x⟩,continuous_subtype_val.subtype_mk _⟩
  let α := f.map j.continuous
  let β := g.map j.continuous
  have hh : α.Homotopic β := (SimplyConnectedSpace.paths_homotopic f g).map j
  exact ⟨havoid u,havoid v,α,β,fun _ => rfl,fun _ => rfl,hh⟩
end CurveComplex.HyperellipticModel
