import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformZeroGermSmallness
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The logarithmic affine redraw is uniformly small near the actual zero
endpoint, even though its logarithm need not extend to that endpoint. -/
theorem actual_logarithmic_germ_redraw_bound
    (g : C(unitInterval × unitInterval,ℂ)) (hg : ∀ τ, g (τ,0)=0)
    (Λ : C(unitInterval × Ioc (0:ℝ) 1,ℂ))
    (hΛ : ∀ z, Complex.exp (Λ z)=g
      (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩))
    (ρ : ℝ) (hρ : 0<ρ) :
    ∃ δ : ℝ, 0<δ ∧ δ<1/2 ∧
      ∀ (τ : unitInterval) (t : Ioc (0:ℝ) 1), t.val≤δ →
        ‖Complex.exp ((1-(τ:ℝ)) • Λ (0,t)+(τ:ℝ) • Λ (1,t))‖<ρ := by
  obtain ⟨δ,hδ,hhalf,hbound⟩ := actual_uniform_zero_germ_smallness g hg ρ hρ
  refine ⟨δ,hδ,hhalf,?_⟩
  intro τ t ht
  apply (actual_complex_log_affine_norm_le (Λ (0,t)) (Λ (1,t)) τ).trans_lt
  apply max_lt_iff.mpr
  rw [hΛ,hΛ]
  exact ⟨hbound 0 _ ht,hbound 1 _ ht⟩
end CurveComplex.HyperellipticModel
