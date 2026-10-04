import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexQuarterClosure

namespace CurveComplex.Hyperbolic
open Set Topology

theorem open_set_contains_point_off_vertex_axes (U : Set H2)
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, z.re ≠ 0 ∧ z.re ^ 2 + z.im ^ 2 ≠ 1 := by
  obtain ⟨y, hy⟩ := hne
  let f : ℝ → H2 := fun t => t +ᵥ y
  have hf : Continuous f := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun t : ℝ => (t : ℂ) + (y : ℂ))
    exact Complex.continuous_ofReal.add continuous_const
  have hopen : IsOpen (f ⁻¹' U) := hU.preimage hf
  have h0 : (0 : ℝ) ∈ f ⁻¹' U := by simpa [f] using hy
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
  let t : ℝ := if 0 ≤ y.re then δ / 4 else -(δ / 4)
  have ht : t ≠ 0 := by
    dsimp [t]
    split <;> linarith
  have hmem (k : ℝ) (hk : k ∈ Set.Icc 1 3) : f (k * t) ∈ U := by
    rcases hk with ⟨hk1, hk3⟩
    apply hball
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_mul]
    rw [abs_of_pos (by linarith : 0 < k)]
    dsimp [t]
    split <;> (try simp only [abs_neg]) <;>
      rw [show |δ / 4| = δ / 4 by rw [abs_of_pos (by linarith)]] <;> nlinarith
  have hre (k : ℝ) (hk : k ∈ Set.Icc 1 3) : (f (k * t)).re ≠ 0 := by
    rcases hk with ⟨hk1, hk3⟩
    simp only [f, UpperHalfPlane.vadd_re]
    dsimp [t]
    split
    · have hprod : 0 < k * (δ / 4) := mul_pos (by linarith) (by linarith)
      linarith
    · have hprod : 0 < k * (δ / 4) := mul_pos (by linarith) (by linarith)
      linarith
  by_contra h
  have hbad (k : ℝ) (hk : k ∈ Set.Icc 1 3) :
      (f (k * t)).re ^ 2 + (f (k * t)).im ^ 2 = 1 := by
    by_contra hne'
    exact h ⟨f (k * t), hmem k hk, hre k hk, hne'⟩
  have h1 := hbad 1 (by norm_num)
  have h2 := hbad 2 (by norm_num)
  have h3 := hbad 3 (by norm_num)
  simp only [f, UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_im, one_mul] at h1 h2 h3
  nlinarith [sq_pos_of_ne_zero ht]

end CurveComplex.Hyperbolic
