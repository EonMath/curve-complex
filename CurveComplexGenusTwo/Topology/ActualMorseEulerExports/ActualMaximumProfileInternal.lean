import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualPartialChartNormalSublevelTransport
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualContractibleCircleRelativeProfile
import CurveComplexGenusTwo.Topology.ActualClosedRadialAnnulus.Coordinates
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Convex.Contractible

open Set CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

/-! Internal derivations; source-facing exported leaf is separately awaiting
review in ActualMaximumNormalChartProfileScaffold.lean. -/

private theorem maximum_upper_eq_closedBall (ρ b : ℝ) (hb : 0 ≤ b) :
    {z : ℂ | ‖z‖ ≤ ρ ∧ -(‖z‖ ^ 2) ≤ b} = Metric.closedBall (0 : ℂ) ρ := by
  ext z
  simp only [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  exact and_iff_left (by nlinarith [sq_nonneg ‖z‖])

private theorem maximum_lower_radius_iff (z : ℂ) (a : ℝ) :
    -(‖z‖ ^ 2) ≤ a ↔ Real.sqrt (-a) ≤ ‖z‖ := by
  rw [Real.sqrt_le_left (norm_nonneg z)]
  constructor <;> intro h <;> linarith

private def maximum_lower_annulus_homeomorph
    (ρ a b : ℝ) (hb : 0 ≤ b) :
    let R := {z : ℂ | ‖z‖ ≤ ρ ∧ -(‖z‖ ^ 2) ≤ b};
    let A : Set R := {z | -(‖z.1‖ ^ 2) ≤ a};
    A ≃ₜ ActualClosedRadialAnnulus (Real.sqrt (-a)) ρ := by
  dsimp only
  exact
    { toFun := fun x => ⟨x.1.1, (maximum_lower_radius_iff _ _).mp x.2, x.1.2.1⟩
      invFun := fun x => ⟨⟨x.1, x.2.2, by nlinarith [sq_nonneg ‖x.1‖]⟩,
        (maximum_lower_radius_iff _ _).mpr x.2.1⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

private theorem maximum_coordinate_profile
    (ρ a b : ℝ) (hρ : 0 < ρ) (hminus : -(ρ ^ 2) ≤ a)
    (ha : a < 0) (hb : 0 ≤ b) :
    let R := {z : ℂ | ‖z‖ ≤ ρ ∧ -(‖z‖ ^ 2) ≤ b};
    let A : Set R := {z | -(‖z.1‖ ^ 2) ≤ a};
    IsZero (relativeHomology R A 0) ∧
      IsZero (relativeHomology R A 1) ∧
      Nonempty (relativeHomology R A 2 ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology R A n)) ∧
      ∀ n : ℕ, Module.Finite ℤ (relativeHomology R A n) := by
  dsimp only
  let R := {z : ℂ | ‖z‖ ≤ ρ ∧ -(‖z‖ ^ 2) ≤ b}
  let A : Set R := {z | -(‖z.1‖ ^ 2) ≤ a}
  letI : ContractibleSpace (Metric.closedBall (0 : ℂ) ρ) :=
    Metric.contractibleSpace_closedBall hρ.le
  letI : ContractibleSpace R :=
    (Homeomorph.setCongr (maximum_upper_eq_closedBall ρ b hb)).contractibleSpace
  have hr : 0 < Real.sqrt (-a) := Real.sqrt_pos.mpr (by linarith)
  have hR : Real.sqrt (-a) ≤ ρ := (Real.sqrt_le_left hρ.le).mpr (by linarith)
  let e := maximum_lower_annulus_homeomorph ρ a b hb
  letI := actual_closed_radial_annulus_pathConnectedSpace hr hR
  letI : PathConnectedSpace A := e.symm.pathConnectedSpace
  let he : ContinuousMap.HomotopyEquiv A Circle := e.toHomotopyEquiv.trans
    (actualClosedRadialAnnulusCircleHomotopyEquiv hr hR)
  obtain ⟨h0, h1, ⟨e2⟩, hh⟩ := actual_contractible_circle_pair_relative_profile R A he
  refine ⟨h0, h1, ⟨e2⟩, hh, ?_⟩
  intro n
  rcases n with _ | n
  · letI := ModuleCat.subsingleton_of_isZero h0
    infer_instance
  rcases n with _ | n
  · letI := ModuleCat.subsingleton_of_isZero h1
    infer_instance
  rcases n with _ | n
  · exact Module.Finite.equiv e2.toLinearEquiv.symm
  · letI := ModuleCat.subsingleton_of_isZero (hh (n + 3) (by omega))
    infer_instance

private theorem maximum_normal_chart_profile
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (F : E → ℝ) (p : E) (ρ a b : ℝ)
    (hρ : 0 < ρ) (hminus : -(ρ ^ 2) ≤ a) (ha : a < 0) (hb : 0 ≤ b)
    (hball : Metric.closedBall (0 : ℂ) ρ ⊆ c.target)
    (hnormal : ∀ x ∈ c.source, F x = F p - ‖c x‖ ^ 2) :
    let R := {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + b};
    let A : Set R := {x | F x.1 ≤ F p + a};
    IsZero (relativeHomology R A 0) ∧
      IsZero (relativeHomology R A 1) ∧
      Nonempty (relativeHomology R A 2 ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ n : ℕ, 3 ≤ n → IsZero (relativeHomology R A n)) ∧
      ∀ n : ℕ, Module.Finite ℤ (relativeHomology R A n) := by
  dsimp only
  let R := {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + b}
  let A : Set R := {x | F x.1 ≤ F p + a}
  let Q := {z : ℂ | ‖z‖ ≤ ρ ∧ -(‖z‖ ^ 2) ≤ b}
  let B : Set Q := {z | -(‖z.1‖ ^ 2) ≤ a}
  have hn : ∀ x ∈ c.source, F x = F p + -(‖c x‖ ^ 2) := by
    simpa only [sub_eq_add_neg] using hnormal
  let e := actual_partial_chart_normal_sublevel_homeomorph c F p
    (fun z => -(‖z‖ ^ 2)) ρ b hball hn
  let f : C(R, Q) := ⟨e, e.continuous⟩
  have hf : ∀ x ∈ A, f x ∈ B := fun x hx =>
    (actual_partial_chart_normal_sublevel_lower_membership c F p
      (fun z => -(‖z‖ ^ 2)) ρ b a hball hn x).mp hx
  have hi (n : ℕ) : IsIso (pairRelativeHomologyMap A B f hf n) :=
    actual_partial_chart_normal_sublevel_pair_relativeHomology_isIso c F p
      (fun z => -(‖z‖ ^ 2)) ρ b a hball hn n
  have iso (n : ℕ) : relativeHomology R A n ≅ relativeHomology Q B n := by
    letI := hi n
    exact asIso (pairRelativeHomologyMap A B f hf n)
  obtain ⟨h0, h1, ⟨e2⟩, hh, hfin⟩ := maximum_coordinate_profile ρ a b hρ hminus ha hb
  refine ⟨h0.of_iso (iso 0), h1.of_iso (iso 1), ⟨iso 2 ≪≫ e2⟩,
    fun n hn => (hh n hn).of_iso (iso n), ?_⟩
  intro n
  letI := hfin n
  exact Module.Finite.equiv (iso n).toLinearEquiv.symm

