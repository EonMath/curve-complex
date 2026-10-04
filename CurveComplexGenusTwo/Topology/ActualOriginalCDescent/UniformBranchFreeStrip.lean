import CurveComplexGenusTwo.Dictionary.ActualCircle24Components

namespace CurveComplex.HyperellipticModel
open Set Topology

theorem uniform_branch_free_strip
    {S : Type} [TopologicalSpace S] [T2Space S]
    (B : Set S) (hBclosed : IsClosed B)
    (g : C(Circle × Set.Icc (-2:ℝ) 3,S))
    (hcentral : ∀ (z : Circle) (t : Set.Icc (-2:ℝ) 3),
      0 ≤ (t:ℝ) → (t:ℝ) ≤ 1 → g (z,t) ∉ B) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (z : Circle) (t : Set.Icc (-2:ℝ) 3),
        -δ ≤ (t:ℝ) → (t:ℝ) ≤ 1+δ → g (z,t) ∉ B := by
  let X := Set.Icc (-2:ℝ) 3
  let Bad : Set X :=
    Prod.snd '' (g ⁻¹' B)
  have hBadCompact : IsCompact Bad :=
    (hBclosed.preimage g.continuous).isCompact.image continuous_snd
  have hBadClosed : IsClosed Bad := hBadCompact.isClosed
  have h0 : (⟨0,by norm_num [X]⟩ : X) ∉ Bad := by
    rintro ⟨⟨z,t⟩,ht,hEq⟩
    have ht0 : (t:ℝ)=0 := congrArg Subtype.val hEq
    exact hcentral z t (by rw [ht0]) (by rw [ht0]; norm_num) ht
  have h1 : (⟨1,by norm_num [X]⟩ : X) ∉ Bad := by
    rintro ⟨⟨z,t⟩,ht,hEq⟩
    have ht1 : (t:ℝ)=1 := congrArg Subtype.val hEq
    exact hcentral z t (by rw [ht1]; norm_num) (by rw [ht1]) ht
  obtain ⟨ε0,hε0,hball0⟩ := Metric.isOpen_iff.mp hBadClosed.isOpen_compl
    (⟨0,by norm_num [X]⟩ : X) h0
  obtain ⟨ε1,hε1,hball1⟩ := Metric.isOpen_iff.mp hBadClosed.isOpen_compl
    (⟨1,by norm_num [X]⟩ : X) h1
  let δ : ℝ := min 1 (min ε0 ε1) / 2
  refine ⟨δ,by dsimp [δ]; positivity,by dsimp [δ]; linarith [min_le_left 1 (min ε0 ε1)],?_⟩
  intro z t htL htR
  by_cases ht0 : 0 ≤ (t:ℝ)
  · by_cases ht1 : (t:ℝ) ≤ 1
    · exact hcentral z t ht0 ht1
    · have hdist : dist t (⟨1,by norm_num [X]⟩ : X) < ε1 := by
        change dist (t:ℝ) (1:ℝ) < ε1
        rw [Real.dist_eq]
        rw [abs_of_nonneg (by linarith)]
        dsimp [δ] at htR
        linarith [min_le_right ε0 ε1,min_le_right 1 (min ε0 ε1)]
      have htBad : t ∉ Bad := hball1 hdist
      exact fun h => htBad ⟨(z,t),h,rfl⟩
  · have hdist : dist t (⟨0,by norm_num [X]⟩ : X) < ε0 := by
      change dist (t:ℝ) (0:ℝ) < ε0
      rw [Real.dist_eq]
      rw [abs_of_nonpos (by linarith)]
      dsimp [δ] at htL
      linarith [min_le_left ε0 ε1,min_le_right 1 (min ε0 ε1)]
    have htBad : t ∉ Bad := hball0 hdist
    exact fun h => htBad ⟨(z,t),h,rfl⟩

end CurveComplex.HyperellipticModel
