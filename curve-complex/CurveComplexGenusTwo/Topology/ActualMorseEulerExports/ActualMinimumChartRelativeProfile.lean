import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualPartialChartNormalSublevelTransport
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualContractibleEmptyRelativeProfile
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Convex.Contractible

open Set CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

theorem actual_minimum_coordinate_upper_eq_closedBall
    (ρ b : ℝ) (hb : 0 ≤ b) :
    {z : ℂ | ‖z‖ ≤ ρ ∧ ‖z‖ ^ 2 ≤ b} =
      Metric.closedBall (0 : ℂ) (min ρ (Real.sqrt b)) := by
  ext z
  simp only [Metric.mem_closedBall, dist_zero_right, le_min_iff]
  exact and_congr_right (fun _ => (Real.le_sqrt (norm_nonneg z) hb).symm)

theorem actual_minimum_coordinate_upper_contractible
    (ρ b : ℝ) (hρ : 0 ≤ ρ) (hb : 0 ≤ b) :
    ContractibleSpace {z : ℂ | ‖z‖ ≤ ρ ∧ ‖z‖ ^ 2 ≤ b} := by
  letI : ContractibleSpace (Metric.closedBall (0 : ℂ) (min ρ (Real.sqrt b))) :=
    Metric.contractibleSpace_closedBall (le_min hρ (Real.sqrt_nonneg b))
  exact (Homeomorph.setCongr (actual_minimum_coordinate_upper_eq_closedBall ρ b hb)).contractibleSpace

theorem actual_minimum_coordinate_pair_relative_profile
    (ρ a b : ℝ) (hρ : 0 ≤ ρ) (ha : a < 0) (hb : 0 ≤ b) :
    let R := {z : ℂ | ‖z‖ ≤ ρ ∧ ‖z‖ ^ 2 ≤ b};
    let A : Set R := {z | ‖z.1‖ ^ 2 ≤ a};
    Nonempty (relativeHomology R A 0 ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ n : ℕ, 0 < n → IsZero (relativeHomology R A n) := by
  dsimp only
  let R := {z : ℂ | ‖z‖ ≤ ρ ∧ ‖z‖ ^ 2 ≤ b}
  let A : Set R := {z | ‖z.1‖ ^ 2 ≤ a}
  letI : ContractibleSpace R := actual_minimum_coordinate_upper_contractible ρ b hρ hb
  letI : IsEmpty A := ⟨fun z => by
    have hz : ‖z.1.1‖ ^ 2 ≤ a := z.2
    have hn := sq_nonneg ‖z.1.1‖
    linarith⟩
  exact actual_contractible_empty_pair_relative_profile R A

/-- The actual bounded local minimum pair, in a supplied proved normal chart,
has one integral generator in degree zero and vanishes in every other degree.
The ORIGINAL function F is retained by the literal chart comparison map. -/
theorem actual_minimum_normal_chart_relative_profile
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (F : E → ℝ) (p : E) (ρ a b : ℝ)
    (hρ : 0 ≤ ρ) (ha : a < 0) (hb : 0 ≤ b)
    (hball : Metric.closedBall (0 : ℂ) ρ ⊆ c.target)
    (hnormal : ∀ x ∈ c.source, F x = F p + ‖c x‖ ^ 2) :
    let R := {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + b};
    let A : Set R := {x | F x.1 ≤ F p + a};
    Nonempty (relativeHomology R A 0 ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ n : ℕ, 0 < n → IsZero (relativeHomology R A n) := by
  dsimp only
  let R := {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + b}
  let A : Set R := {x | F x.1 ≤ F p + a}
  let Q := {z : ℂ | ‖z‖ ≤ ρ ∧ ‖z‖ ^ 2 ≤ b}
  let B : Set Q := {z | ‖z.1‖ ^ 2 ≤ a}
  let e := actual_partial_chart_normal_sublevel_homeomorph c F p
    (fun z => ‖z‖ ^ 2) ρ b hball hnormal
  let f : C(R, Q) := ⟨e, e.continuous⟩
  have hf : ∀ x ∈ A, f x ∈ B := fun x hx =>
    (actual_partial_chart_normal_sublevel_lower_membership c F p
      (fun z => ‖z‖ ^ 2) ρ b a hball hnormal x).mp hx
  have hi (n : ℕ) : IsIso (pairRelativeHomologyMap A B f hf n) :=
    actual_partial_chart_normal_sublevel_pair_relativeHomology_isIso c F p
      (fun z => ‖z‖ ^ 2) ρ b a hball hnormal n
  obtain ⟨⟨e0⟩, hzero⟩ := actual_minimum_coordinate_pair_relative_profile ρ a b hρ ha hb
  letI := hi 0
  refine ⟨⟨asIso (pairRelativeHomologyMap A B f hf 0) ≪≫ e0⟩, ?_⟩
  intro n hn
  letI := hi n
  exact (hzero n hn).of_iso (asIso (pairRelativeHomologyMap A B f hf n))

