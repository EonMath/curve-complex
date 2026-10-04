import CurveComplexGenusTwo.Filtration.Geometry.ActualClosedObstacleRadialEnlargement
import CurveComplexGenusTwo.Filtration.Geometry.ActualSupportCrosscutAlignment
import Schoenflies.BoundaryContinuity2

noncomputable section
open Set Topology Schoenflies CurveComplex Metric

namespace CurveComplex

def actualSupPlaneProductHomeomorph : Plane ≃ₜ (ℝ × ℝ) := {
  toEquiv := {
    toFun := fun z => (z 0, z 1)
    invFun := fun z => Plane.mk z.1 z.2
    left_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk]
    right_inv := by intro z; exact Prod.ext (by simp [Plane.mk]) (by simp [Plane.mk]) }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop }

theorem actualSupPlaneProductHomeomorph_norm (z : Plane) :
    ‖actualSupPlaneProductHomeomorph z‖ = Plane.supNorm z := by
  simp [actualSupPlaneProductHomeomorph, Prod.norm_def, Real.norm_eq_abs, Plane.supNorm]

/-- PRODUCE an enlarged repair square for the actual pair of boundary arcs.
The closed obstacle may meet both original arcs at the common endpoints.
Those endpoints remain literal, and the entire enlarged OPEN square avoids
the obstacle. Neither a collar nor a relative ambient isotopy is assumed. -/
theorem actual_endpoint_preserving_bigon_enlargement
    (A B : Set Plane) (p q : Plane)
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hwhole : A ∪ B = modelCurve)
    (F : Set Plane) (hF : IsClosed F) (hpF : p ∈ F) (hqF : q ∈ F)
    (hboundary : ∀ z ∈ F, z ∈ modelCurve → z = p ∨ z = q)
    (hinside : Disjoint (Plane.openSquare 0 1) F) :
    ∃ φ : Plane ≃ₜ Plane,
      φ p = p ∧ φ q = q ∧
      IsArcBetween (φ.symm '' A) p q ∧ IsArcBetween (φ.symm '' B) p q ∧
      (φ.symm '' A) \ {p, q} ⊆ Plane.openSquare 0 1 ∧
      (φ.symm '' B) \ {p, q} ⊆ Plane.openSquare 0 1 ∧
      ∀ z ∈ Plane.openSquare 0 1, φ z ∉ F := by
  let P := actualSupPlaneProductHomeomorph
  have hPF : IsClosed (P '' F) := P.isClosedMap _ hF
  have hPFne : (P '' F).Nonempty := ⟨P p, Set.mem_image_of_mem P hpF⟩
  have hPinside : Disjoint {z : ℝ × ℝ | ‖z‖ < 1} (P '' F) := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨x, hx, rfl⟩
    have hxs : x ∈ Plane.openSquare 0 1 :=
      mem_openSquare_zero_one.mpr ((actualSupPlaneProductHomeomorph_norm x).symm ▸ hz)
    exact Set.disjoint_left.mp hinside hxs hx
  obtain ⟨H, hfix, hpush, hfree⟩ :=
    actual_closed_obstacle_radial_enlargement (P '' F) hPF hPFne hPinside
  obtain ⟨g, hg⟩ := H.homeomorphism_at (1 : Interval)
  let φ : Plane ≃ₜ Plane := (P.trans g).trans P.symm
  have hφcoord (z : Plane) : P (φ z) = H.finalMap (P z) := by
    change P (P.symm (g (P z))) = H.finalMap (P z)
    rw [P.apply_symm_apply]
    exact hg _
  have hφfix (z : Plane) (hz : z ∈ F) : φ z = z := by
    apply P.injective
    rw [hφcoord]
    exact hfix 1 (P z) (Set.mem_image_of_mem P hz)
  have hφp : φ p = p := hφfix p hpF
  have hφq : φ q = q := hφfix q hqF
  have hφip : φ.symm p = p := by
    apply φ.injective
    rw [φ.apply_symm_apply, hφp]
  have hφiq : φ.symm q = q := by
    apply φ.injective
    rw [φ.apply_symm_apply, hφq]
  have hpre (x : Plane) (hx : x ∈ modelCurve) (hxn : x ∉ F) :
      φ.symm x ∈ Plane.openSquare 0 1 := by
    have hPx : ‖P x‖ = 1 := by
      rw [actualSupPlaneProductHomeomorph_norm]
      exact hx
    have hPxn : P x ∉ P '' F := by
      rintro ⟨y, hy, he⟩
      exact hxn (P.injective he ▸ hy)
    obtain ⟨w, hw, hwx⟩ := hpush ⟨hPx, hPxn⟩
    have he : φ (P.symm w) = x := by
      apply P.injective
      rw [hφcoord, P.apply_symm_apply]
      exact hwx
    have hi : φ.symm x = P.symm w := by
      apply φ.injective
      rw [φ.apply_symm_apply, he]
    rw [hi]
    apply mem_openSquare_zero_one.mpr
    rw [← actualSupPlaneProductHomeomorph_norm, P.apply_symm_apply]
    exact hw
  have hproper (C : Set Plane) (hC : C ⊆ modelCurve) :
      (φ.symm '' C) \ {p, q} ⊆ Plane.openSquare 0 1 := by
    rintro x ⟨⟨z, hz, rfl⟩, hn⟩
    apply hpre z (hC hz)
    intro hzF
    rcases hboundary z hzF (hC hz) with he | he
    · apply hn
      rw [he, hφip]
      exact Set.mem_insert p {q}
    · apply hn
      rw [he, hφiq]
      exact Set.mem_insert_of_mem p (Set.mem_singleton q)
  have hA' : IsArcBetween (φ.symm '' A) p q := by
    simpa only [hφip, hφiq] using hA.image_of_injOn (Set.subset_univ _)
      φ.symm.continuous.continuousOn φ.symm.injective.injOn
  have hB' : IsArcBetween (φ.symm '' B) p q := by
    simpa only [hφip, hφiq] using hB.image_of_injOn (Set.subset_univ _)
      φ.symm.continuous.continuousOn φ.symm.injective.injOn
  refine ⟨φ, hφp, hφq, hA', hB',
    hproper A (hwhole ▸ Set.subset_union_left),
    hproper B (hwhole ▸ Set.subset_union_right), ?_⟩
  intro z hz hφz
  apply Set.disjoint_left.mp hfree
  · refine ⟨P z, ?_, (hφcoord z).symm⟩
    change ‖P z‖ < 1
    rw [actualSupPlaneProductHomeomorph_norm]
    exact mem_openSquare_zero_one.mp hz
  · exact Set.mem_image_of_mem P hφz

#print axioms actualSupPlaneProductHomeomorph_norm
#print axioms actual_endpoint_preserving_bigon_enlargement

end CurveComplex
