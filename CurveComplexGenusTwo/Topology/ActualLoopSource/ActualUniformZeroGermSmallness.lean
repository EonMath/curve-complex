import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualComplexLogAffineNorm
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Compactness of the actual time axis constructs one uniform small germ
window. The bound is a conclusion, not an assumed endpoint certificate. -/
theorem actual_uniform_zero_germ_smallness
    (g : C(unitInterval × unitInterval,ℂ))
    (hg : ∀ τ, g (τ,0)=0) (ρ : ℝ) (hρ : 0<ρ) :
    ∃ δ : ℝ, 0<δ ∧ δ<1/2 ∧
      ∀ τ t : unitInterval, (t:ℝ)≤δ → ‖g (τ,t)‖<ρ := by
  have hN : IsOpen {z : unitInterval × unitInterval | ‖g z‖<ρ} :=
    isOpen_lt g.continuous.norm continuous_const
  have hline : (univ : Set unitInterval) ×ˢ {(0:unitInterval)} ⊆
      {z : unitInterval × unitInterval | ‖g z‖<ρ} := by
    rintro ⟨τ,t⟩ ⟨_,ht⟩
    rw [mem_singleton_iff] at ht
    change t=0 at ht
    subst t
    simpa [hg] using hρ
  obtain ⟨A,B,_,hB,hA,hzeroB,hAB⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hN hline
  obtain ⟨η,hη,hball⟩ := Metric.mem_nhds_iff.mp
    (hB.mem_nhds (hzeroB (mem_singleton (0:unitInterval))))
  let δ : ℝ := min η (1/2) /2
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδη : δ<η := by have hh := min_le_left η (1/2); dsimp [δ]; linarith
  have hδhalf : δ<1/2 := by have hh := min_le_right η (1/2); dsimp [δ]; linarith
  refine ⟨δ,hδ,hδhalf,?_⟩
  intro τ t ht
  apply hAB ⟨hA (mem_univ τ),hball ?_⟩
  change dist t (0:unitInterval)<η
  rw [Subtype.dist_eq,Real.dist_eq]
  change |(t:ℝ)-0|<η
  rw [sub_zero,abs_of_nonneg t.property.1]
  exact ht.trans_lt hδη
end CurveComplex.HyperellipticModel
