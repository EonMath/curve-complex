import CurveComplexGenusTwo.Hyperbolic.OriginalG2.G2UnitDiskCutPair
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.G1ArbitraryCrosscutAlternationPROVED
import Mathlib

namespace CurveComplex.Hyperbolic

open Set Topology Schoenflies CurveComplex.LocalSurgery

theorem g2_disk_arc_opposite_semicircle_path_intersects
    (f : C(unitInterval,ℂ)) (hf : IsEmbedding f)
    (hf0 : f 0 = -1) (hf1 : f 1 = 1)
    (hfIn : ∀ s : unitInterval, ‖f s‖ ≤ 1)
    (hfBoundary : ∀ s : unitInterval, ‖f s‖ = 1 → f s = -1 ∨ f s = 1)
    (γ : C(ℝ,ℂ)) (hγ : ∀ t : ℝ, ‖γ t‖ < 1)
    (w₁ w₂ : ℂ) (hn₁ : ‖w₁‖ = 1) (hn₂ : ‖w₂‖ = 1)
    (hsign : w₁.im * w₂.im < 0)
    (hw₁ : actualComplexSchoenflies w₁ ∈
      closure (Set.range (fun t : ℝ => actualComplexSchoenflies (γ t))))
    (hw₂ : actualComplexSchoenflies w₂ ∈
      closure (Set.range (fun t : ℝ => actualComplexSchoenflies (γ t)))) :
    (Set.range γ ∩ Set.range f).Nonempty := by
  let C : Set Plane := Metric.sphere (0:Plane) 1
  let P : Set Plane := actualComplexSchoenflies '' Set.range f
  let Q : Set Plane := Set.range (fun t : ℝ => actualComplexSchoenflies (γ t))
  let a : Plane := actualComplexSchoenflies (-1:ℂ)
  let b : Plane := actualComplexSchoenflies (1:ℂ)
  let A₁ : Set Plane := actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ 0 ≤ z.im}
  let A₂ : Set Plane := actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ z.im ≤ 0}
  have hP : IsArcBetween P a b := by
    simpa only [P,a,b,hf0,hf1] using g2_embedded_interval_isArc f hf
  have hPC : P ∩ C = {a,b} := by
    ext z
    constructor
    · rintro ⟨⟨v,⟨s,rfl⟩,rfl⟩,hz⟩
      have hn : ‖f s‖=1 := by
        simpa only [C,Metric.mem_sphere,dist_zero_right,actualComplexSchoenflies_norm] using hz
      rcases hfBoundary s hn with h | h
      · exact Or.inl (by simp [a,h])
      · exact Or.inr (by simp [b,h])
    · rintro (rfl | rfl)
      · exact ⟨⟨-1,⟨0,hf0⟩,rfl⟩,by simp [C,a,Metric.mem_sphere,dist_zero_right,
          actualComplexSchoenflies_norm]⟩
      · exact ⟨⟨1,⟨1,hf1⟩,rfl⟩,by simp [C,b,Metric.mem_sphere,dist_zero_right,
          actualComplexSchoenflies_norm]⟩
  have hPD : P \ {a,b} ⊆ inside C := by
    rw [show inside C = Metric.ball (0:Plane) 1 from
      g2_unit_disk_inside]
    rintro z ⟨⟨v,⟨s,rfl⟩,rfl⟩,hoff⟩
    have hle : ‖f s‖ ≤ 1 := hfIn s
    have hne : ‖f s‖ ≠ 1 := by
      intro hn
      rcases hfBoundary s hn with he | he
      · exact hoff (by simp [a,he])
      · exact hoff (by simp [b,he])
    have hlt : ‖f s‖ < 1 := lt_of_le_of_ne hle hne
    simpa only [Metric.mem_ball,dist_zero_right,actualComplexSchoenflies_norm] using hlt
  have hQ : IsPreconnected Q :=
    isPreconnected_range (actualComplexSchoenflies.continuous.comp γ.continuous)
  have hQD : Q ⊆ inside C := by
    rw [show inside C = Metric.ball (0:Plane) 1 from
      g2_unit_disk_inside]
    rintro z ⟨t,rfl⟩
    simpa only [Metric.mem_ball,dist_zero_right,actualComplexSchoenflies_norm] using hγ t
  have hcut : IsCutPair C a b A₁ A₂ := g2_unit_circle_cut_pair
  have hmeet : (Q ∩ P).Nonempty := by
    rcases mul_neg_iff.mp hsign with hcase | hcase
    · have hw₁A : actualComplexSchoenflies w₁ ∈ A₁ :=
        ⟨w₁,⟨hn₁,hcase.1.le⟩,rfl⟩
      have hw₁B : actualComplexSchoenflies w₁ ∉ A₂ := by
        rintro ⟨v,hv,he⟩
        have := actualComplexSchoenflies.injective he
        subst v
        exact (not_le_of_gt hcase.1) hv.2
      have hw₂B : actualComplexSchoenflies w₂ ∈ A₂ :=
        ⟨w₂,⟨hn₂,hcase.2.le⟩,rfl⟩
      have hw₂A : actualComplexSchoenflies w₂ ∉ A₁ := by
        rintro ⟨v,hv,he⟩
        have := actualComplexSchoenflies.injective he
        subst v
        exact (not_le_of_gt hcase.2) hv.2
      exact arbitrary_jordan_crosscut_alternating_inter_nonempty
        g2_unit_circle_jordan hP hcut hPC hPD
        hQ hQD hw₁ hw₂ hw₁A hw₁B hw₂B hw₂A
    · have hw₁A : actualComplexSchoenflies w₂ ∈ A₁ :=
        ⟨w₂,⟨hn₂,hcase.2.le⟩,rfl⟩
      have hw₁B : actualComplexSchoenflies w₂ ∉ A₂ := by
        rintro ⟨v,hv,he⟩
        have := actualComplexSchoenflies.injective he
        subst v
        exact (not_le_of_gt hcase.2) hv.2
      have hw₂B : actualComplexSchoenflies w₁ ∈ A₂ :=
        ⟨w₁,⟨hn₁,hcase.1.le⟩,rfl⟩
      have hw₂A : actualComplexSchoenflies w₁ ∉ A₁ := by
        rintro ⟨v,hv,he⟩
        have := actualComplexSchoenflies.injective he
        subst v
        exact (not_le_of_gt hcase.1) hv.2
      exact arbitrary_jordan_crosscut_alternating_inter_nonempty
        g2_unit_circle_jordan hP hcut hPC hPD
        hQ hQD hw₂ hw₁ hw₁A hw₁B hw₂B hw₂A
  obtain ⟨z,⟨t,rfl⟩,⟨v,⟨s,hs⟩,hv⟩⟩ := hmeet
  refine ⟨γ t,⟨t,rfl⟩,⟨s,?_⟩⟩
  apply actualComplexSchoenflies.injective
  rw [hs]
  exact hv

#print axioms g2_disk_arc_opposite_semicircle_path_intersects

end CurveComplex.Hyperbolic
