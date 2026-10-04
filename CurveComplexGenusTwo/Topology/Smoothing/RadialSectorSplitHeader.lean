import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
open Set Metric Schoenflies

-- Inserting the new radius really partitions a convex sector. A supporting
-- functional excludes the negative half of its line, including the initial
-- half-disk case. Both common loop incidences remain distinct source arms.
theorem radial_sector_determinant_split (Q : Set Plane) (hc : Convex ℝ Q) (R : ℝ) (hR : 0 < R)
    (hQ : Q ⊆ closedBall (0:Plane) R) (hzero : (0:Plane) ∈ Q)
    (e : Plane) (he : e ∈ Q) (heR : ‖e‖ = R)
    (L : Plane →L[ℝ] ℝ) (hL : ∀ x ∈ Q, 0 ≤ L x) (heL : 0 < L e) :
    let Q₁ := Q ∩ {x | 0 ≤ Plane.det e x}
    let Q₂ := Q ∩ {x | Plane.det e x ≤ 0}
    Q₁ ∪ Q₂ = Q ∧ Q₁ ∩ Q₂ = segment ℝ (0:Plane) e ∧
      Convex ℝ Q₁ ∧ Convex ℝ Q₂ := by
  intro Q₁ Q₂
  have hen : e ≠ 0 := by
    intro he0
    simp [he0] at heL
  constructor
  · ext x
    constructor
    · rintro (hx|hx) <;> exact hx.1
    · intro hx
      rcases le_total 0 (Plane.det e x) with hp|hn
      · exact Or.inl ⟨hx,hp⟩
      · exact Or.inr ⟨hx,hn⟩
  constructor
  · ext x
    constructor
    · rintro ⟨⟨hx,hp⟩,⟨_,hn⟩⟩
      have hd : Plane.det e x = 0 := le_antisymm hn hp
      obtain ⟨r,hr⟩ := (Plane.det_eq_zero_iff_smul e x hen).mp hd
      have hrpos : 0 ≤ r := by
        have hxL := hL x hx
        rw [hr,map_smul,smul_eq_mul] at hxL
        exact nonneg_of_mul_nonneg_left hxL heL
      have hnorm : ‖x‖ ≤ R := by
        simpa only [mem_closedBall,dist_zero_right] using hQ hx
      have hr1 : r ≤ 1 := by
        rw [hr,norm_smul,Real.norm_eq_abs,abs_of_nonneg hrpos,heR] at hnorm
        nlinarith
      rw [hr]
      exact ⟨1-r,r,sub_nonneg.mpr hr1,hrpos,by ring,by simp⟩
    · intro hx
      have hxQ : x ∈ Q := hc.segment_subset hzero he hx
      have hd : Plane.det e x = 0 := by
        obtain ⟨a,b,ha,hb,hab,hxab⟩ := hx
        rw [← hxab]
        simp
      exact ⟨⟨hxQ,hd.ge⟩,⟨hxQ,hd.le⟩⟩
  constructor
  · apply hc.inter
    intro x hx y hy a b ha hb hab
    change 0 ≤ Plane.det e (a • x + b • y)
    rw [Plane.det_add_right,Plane.det_smul_right,Plane.det_smul_right]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  · apply hc.inter
    intro x hx y hy a b ha hb hab
    change Plane.det e (a • x + b • y) ≤ 0
    rw [Plane.det_add_right,Plane.det_smul_right,Plane.det_smul_right]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
      (mul_nonpos_of_nonneg_of_nonpos hb hy)

#print axioms radial_sector_determinant_split
