import CurveComplexGenusTwo.Dictionary.Circle24.BranchCenterExtension
import Mathlib.Topology.Homotopy.Lifting
open Set Topology
namespace CurveComplex.BranchedDoubleCover
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
set_option maxHeartbeats 3000000

/-- Lift the full radial strip of a one-mark cell, including its branch-center
face. The covering is used only at positive radius; the unique branch fiber
supplies the continuous extension at radius zero. -/
theorem radial_strip_lift_exists [CompactSpace E] [T2Space S]
    (q : BranchedDoubleCover E S)
    (H : C(Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,S)) (b : S) (hb : b ∈ q.branch)
    (hcenter : ∀ z, z.val.1 = 0 → H z = b)
    (havoid : ∀ z, 0 < z.val.1 → H z ∉ q.branch) :
    ∃ Γ : C(Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,E),
      (∀ z, q.projection (Γ z) = H z) ∧
      (∀ z z', z.val.1 = 0 → z'.val.1 = 0 → Γ z = Γ z') := by
  classical
  let R : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1
  let P : Set (ℝ × ℝ) := Ioc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1
  have hsub : P ⊆ R := by
    rintro z ⟨hzr,hzt⟩
    exact ⟨⟨hzr.1.le,hzr.2⟩,hzt⟩
  let p : P := ⟨(1,0),by simp [P]⟩
  let : ContractibleSpace P := ((convex_Ioc (0:ℝ) 1).prod
    (convex_Icc (0:ℝ) 1)).contractibleSpace ⟨p.val,p.property⟩
  let : LocallyPathConnectedSpace P := ((convex_Ioc (0:ℝ) 1).prod
    (convex_Icc (0:ℝ) 1)).locallyPathConnectedSpace
  let H' : C(P,S) := H.comp ⟨Set.inclusion hsub,continuous_inclusion hsub⟩
  obtain ⟨e,he⟩ := q.projection_surjective (H' p)
  obtain ⟨L,hL,_⟩ := q.unbranched_cover.existsUnique_continuousMap_lifts H' he
    (fun z => havoid ⟨z.val,hsub z.property⟩ z.property.1.1)
  have hLπ (z : P) : q.projection (L z) = H' z := congrFun hL.2 z
  obtain ⟨w,hw,hunique⟩ := q.branch_fiber_unique hb
  let g : R → E := fun z => if h : 0 < z.val.1 then
    L ⟨z.val,⟨⟨h,z.property.1.2⟩,z.property.2⟩⟩ else w
  have hgπ (z : R) : q.projection (g z) = H z := by
    by_cases h : 0 < z.val.1
    · simpa only [g,dite_eq_left h,H',ContinuousMap.comp_apply,ContinuousMap.coe_mk,Set.inclusion] using
        hLπ ⟨z.val,⟨⟨h,z.property.1.2⟩,z.property.2⟩⟩
    · have hz0 : z.val.1 = 0 := le_antisymm (le_of_not_gt h) z.property.1.1
      simpa only [g,dite_eq_right h] using hw.trans (hcenter z hz0).symm
  let O : Set R := {z | 0 < z.val.1}
  have hO : IsOpen O := isOpen_lt continuous_const
    (continuous_fst.comp continuous_subtype_val)
  have hgO : ContinuousOn g O := by
    rw [continuousOn_iff_continuous_domRestrict]
    let j : O → P := fun z =>
      ⟨z.val.val,⟨⟨z.property,z.val.property.1.2⟩,z.val.property.2⟩⟩
    have hj : Continuous j :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    convert L.continuous.comp hj using 1
    funext z
    exact dite_eq_left z.property
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : 0 < z.val.1
    · exact hgO.continuousAt (hO.mem_nhds hz)
    · apply q.continuousAt_of_branch_projection g z
      · rw [hgπ,hcenter z (le_antisymm (le_of_not_gt hz) z.property.1.1)]
        exact hb
      · have heq : q.projection ∘ g = H := funext hgπ
        rw [heq]
        exact H.continuous.continuousAt
  refine ⟨⟨g,hgcont⟩,hgπ,?_⟩
  intro z z' hz hz'
  change g z = g z'
  have h : ¬ 0 < z.val.1 := by rw [hz]; exact lt_irrefl _
  have h' : ¬ 0 < z'.val.1 := by rw [hz']; exact lt_irrefl _
  rw [show g z = w from dite_eq_right h,show g z' = w from dite_eq_right h']

/-- The radial filling can be anchored at a specified upstairs boundary point,
so its eventual attaching arcs use the same sheet as the corridor. -/
theorem radial_strip_lift_exists_at [CompactSpace E] [T2Space S]
    (q : BranchedDoubleCover E S)
    (H : C(Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,S)) (b : S) (hb : b ∈ q.branch)
    (hcenter : ∀ z, z.val.1 = 0 → H z = b)
    (havoid : ∀ z, 0 < z.val.1 → H z ∉ q.branch)
    (p : Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) (e : E)
    (he : q.projection e = H p) :
    ∃ Γ : C(Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,E), Γ p = e ∧
      (∀ z, q.projection (Γ z) = H z) ∧
      (∀ z z', z.val.1 = 0 → z'.val.1 = 0 → Γ z = Γ z') := by
  obtain ⟨Γ,hΓ,hzero⟩ := q.radial_strip_lift_exists H b hb hcenter havoid
  rcases (q.fiber_pair (Γ p) e).mp ((hΓ p).trans he.symm) with h | h
  · exact ⟨Γ,h.symm,hΓ,hzero⟩
  · let Δ : C(Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,E) :=
      ⟨fun z => q.deck (Γ z),q.deck.continuous.comp Γ.continuous⟩
    refine ⟨Δ,h.symm,?_,?_⟩
    · intro z
      exact (q.projection_deck (Γ z)).trans (hΓ z)
    · intro z z' hz hz'
      exact congrArg q.deck (hzero z z' hz hz')

end CurveComplex.BranchedDoubleCover
#print axioms CurveComplex.BranchedDoubleCover.radial_strip_lift_exists

#print axioms CurveComplex.BranchedDoubleCover.radial_strip_lift_exists_at
