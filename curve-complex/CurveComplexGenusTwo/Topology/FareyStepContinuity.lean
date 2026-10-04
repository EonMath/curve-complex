import CurveComplexGenusTwo.Topology.FareyStageHomotopy

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- The support-based stage move agrees with the continuous face-affine map. -/
theorem fareyStageStep_eq_faceAffine
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (x : FiniteSimplex σ.1) (t : ConeTime) :
    fareyStageStep n hn (fareyStageCoverMap n ⟨σ, x⟩) t =
      fareyStageFaceAffine n hn σ t x := by
  classical
  let z : fareyStage n := fareyStageCoverMap n ⟨σ, x⟩
  have hz : z.1 = faceInclusion fareyComplex σ.1 σ.2.1 x := rfl
  change fareyStageStep n hn z t = fareyStageFaceAffine n hn σ t x
  by_cases hpositive : ∃ p : ℚ, p.den = n ∧ z.1.weight (some p) ≠ 0
  · obtain ⟨p, hpn, hpweight⟩ := hpositive
    have hpσ : some p ∈ σ.1 := by
      by_contra hnot
      exact hpweight (by rw [hz]; exact
        faceInclusion_weight_of_not_mem fareyComplex σ.1 σ.2.1 x (some p) hnot)
    have hpsupport : some p ∈ supportFinset fareyComplex z.1 :=
      (mem_supportFinset_iff fareyComplex z.1 (some p)).2 hpweight
    have hpgt : 1 < p.den := by omega
    have hS : supportFinset fareyComplex z.1 ⊆ fareyParentTriangle p hpgt :=
      fareyStage_support_subset_parentTriangle n hn z p hpsupport hpn
    rw [fareyStageStep_eq_parentTriangleMove n hn z p hpsupport hpn hpgt hS t,
      fareyStageFaceAffine_of_top n hn σ p hpσ hpn]
    apply RealizationPoint.ext
    funext w
    rw [fareyParentTriangleMove_weight, fareyTopFaceAffine_weight, hz]
  · have hzero : ∀ p : ℚ, p.den = n → z.1.weight (some p) = 0 := by
      intro p hpn
      by_contra hpweight
      exact hpositive ⟨p, hpn, hpweight⟩
    have hnot : ¬ ∃ p : ℚ,
        some p ∈ supportFinset fareyComplex z.1 ∧ p.den = n := by
      rintro ⟨p, hp, hpn⟩
      exact (mem_supportFinset_iff fareyComplex z.1 (some p)).1 hp (hzero p hpn)
    have hface : fareyStageFaceAffine n hn σ t x = z.1 := by
      rw [fareyStageFaceAffine_fixed_of_no_top_mass n hn σ t x]
      · exact hz.symm
      · intro p hpn
        rw [← hz]
        exact hzero p hpn
    simp only [fareyStageStep, hnot]
    exact hface.symm

theorem fareyStageStep_continuous
    (n : ℕ) (hn : 1 < n) :
    Continuous (fun q : fareyStage n × ConeTime =>
      fareyStageStep n hn q.1 q.2) := by
  have hEq : (fun q : fareyStage n × ConeTime =>
      fareyStageStep n hn q.1 q.2) = fareyStageAffineAmbient n hn := by
    funext q
    classical
    obtain ⟨⟨σ, x⟩, hx⟩ := (fareyStageCoverMap_isQuotientMap n).surjective q.1
    have h := fareyStageStep_eq_faceAffine n hn σ x q.2
    change fareyStageStep n hn q.1 q.2 =
      fareyStageAffineAmbient n hn (q.1, q.2)
    rw [← hx]
    exact h.trans (fareyStageAffineAmbient_face n hn σ q.2 x).symm
  rw [hEq]
  exact fareyStageAffineAmbient_continuous n hn

end CurveComplexGenusTwo.Topology
