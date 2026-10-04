import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.Topology.IntersectionParity.ArcInterior

open Set Topology

namespace CurveComplex.LocalSurgery

/-- An embedded circle cannot be a proper embedded subcircle of another.
This identifies the complete essential curve if a crosscut joins both old
corners along the same original side. -/
theorem curve_image_eq_of_subset
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (a c : Curve S) (hc : c.image ⊆ a.image) : c.image = a.image := by
  classical
  let T : Set a.image := {x | (x : S) ∈ c.image}
  have hTclosed : IsClosed T :=
    (isCompact_range c.embedded.continuous).isClosed.preimage continuous_subtype_val
  have hTopen : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨z, hz⟩ := hx
    let f : C(Interval, S) :=
      ⟨fun t => c.map (z * Circle.exp (Real.pi * (t.val - 1 / 2))), c.embedded.continuous.comp (by fun_prop)⟩
    have hfInj : Function.Injective f := by
      intro u v heq
      have heq' := c.embedded.injective heq
      change z * Circle.exp (Real.pi * (u.val - 1 / 2)) =
        z * Circle.exp (Real.pi * (v.val - 1 / 2)) at heq'
      have hu : Real.pi * (u.val - 1 / 2) ∈ Set.Ico (-Real.pi) Real.pi := by
        constructor <;> nlinarith [u.property.1, u.property.2, Real.pi_pos]
      have hv : Real.pi * (v.val - 1 / 2) ∈ Set.Ico (-Real.pi) Real.pi := by
        constructor <;> nlinarith [v.property.1, v.property.2, Real.pi_pos]
      have hang := Circle.exp_injOn_Ico (by linarith : Real.pi - (-Real.pi) ≤ 2 * Real.pi)
        hu hv (mul_left_cancel heq')
      apply Subtype.ext
      nlinarith [Real.pi_pos]
    have hf : IsEmbedding f := (f.continuous.isClosedEmbedding hfInj).isEmbedding
    have hfc : Set.range f ⊆ c.image := by rintro y ⟨t, rfl⟩; exact ⟨_, rfl⟩
    have hfa := hfc.trans hc
    let F : Set a.image := {y | (y : S) ∈ f '' Set.Ioo (0 : Interval) 1}
    have hFopen : IsOpen F := embedded_curve_subarc_interior_isOpen a f hf hfa
    have hxF : x ∈ F := by
      refine ⟨⟨1 / 2, by constructor <;> norm_num⟩, ?_, ?_⟩
      · constructor
        · change (0 : ℝ) < 1 / 2; norm_num
        · change (1 / 2 : ℝ) < 1; norm_num
      · simpa [f] using hz
    have hFT : F ⊆ T := by
      rintro y ⟨t, ht, heq⟩
      exact hfc ⟨t, heq⟩
    exact Filter.mem_of_superset (hFopen.mem_nhds hxF) hFT
  haveI : ConnectedSpace a.image := Subtype.connectedSpace (isConnected_range a.embedded.continuous)
  have hTne : T.Nonempty := ⟨⟨c.map 1, hc ⟨1, rfl⟩⟩, ⟨1, rfl⟩⟩
  have hTall : T = Set.univ := (show IsClopen T from ⟨hTclosed, hTopen⟩).eq_univ hTne
  apply Set.Subset.antisymm hc
  intro x hx
  have hmem : (⟨x, hx⟩ : a.image) ∈ T := hTall.symm ▸ Set.mem_univ _
  exact hmem

end CurveComplex.LocalSurgery
