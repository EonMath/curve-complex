import CurveComplexGenusTwo.Hyperbolic.LocalMeasureDomination

namespace CurveComplex.Hyperbolic

open MeasureTheory Function
open scoped ENNReal

theorem measure_le_smul_of_local_measurable_le
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (ρ ν : Measure X) (c : ℝ≥0∞)
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ s : Set X, MeasurableSet s → s ⊆ U → ρ s ≤ c * ν s) :
    ρ ≤ c • ν := by
  classical
  choose U hUopen hxU hlocal using h
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨f, hfcover⟩ :=
    isLindelof_univ.indexed_countable_subcover U hUopen hcover
  let V : ℕ → Set X := fun n => U (f n)
  refine Measure.le_iff.mpr fun s hs => ?_
  have hVU : (⋃ n, V n) = (Set.univ : Set X) := Set.eq_univ_iff_forall.mpr
    (fun x => hfcover (Set.mem_univ x))
  have hPunion : (⋃ n, s ∩ disjointed V n) = s := by
    rw [← Set.inter_iUnion, iUnion_disjointed, hVU, Set.inter_univ]
  have hPmeas (n : ℕ) : MeasurableSet (s ∩ disjointed V n) :=
    hs.inter (MeasurableSet.disjointed (fun i => (hUopen (f i)).measurableSet) n)
  have hPdisj : Pairwise (Disjoint on fun n => s ∩ disjointed V n) :=
    (disjoint_disjointed V).mono fun i j => Disjoint.mono Set.inter_subset_right
      Set.inter_subset_right
  have hPle (n : ℕ) : ρ (s ∩ disjointed V n) ≤ c * ν (s ∩ disjointed V n) :=
    hlocal (f n) _ (hPmeas n)
      (Set.inter_subset_right.trans (disjointed_subset V n))
  calc
    ρ s = ∑' n, ρ (s ∩ disjointed V n) := by
      calc
        ρ s = ρ (⋃ n, s ∩ disjointed V n) := congrArg ρ hPunion.symm
        _ = ∑' n, ρ (s ∩ disjointed V n) := measure_iUnion hPdisj hPmeas
    _ ≤ ∑' n, c * ν (s ∩ disjointed V n) := ENNReal.tsum_le_tsum hPle
    _ = c * ν s := by
      rw [ENNReal.tsum_mul_left, ← measure_iUnion hPdisj hPmeas, hPunion]

theorem withDensity_set_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞)
    {s : Set X} (hs : MeasurableSet s) (a b : ℝ≥0∞)
    (ha : ∀ x ∈ s, a ≤ f x) (hb : ∀ x ∈ s, f x ≤ b) :
    a * μ s ≤ μ.withDensity f s ∧ μ.withDensity f s ≤ b * μ s := by
  rw [withDensity_apply f hs]
  constructor
  · calc
      a * μ s = ∫⁻ _ in s, a ∂μ := (setLIntegral_const s a).symm
      _ ≤ ∫⁻ x in s, f x ∂μ := setLIntegral_mono' hs ha
  · calc
      ∫⁻ x in s, f x ∂μ ≤ ∫⁻ _ in s, b ∂μ := setLIntegral_mono' hs hb
      _ = b * μ s := setLIntegral_const s b

end CurveComplex.Hyperbolic
