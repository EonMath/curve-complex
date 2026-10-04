import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualPublicSaddleCoordinateProfile
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRelativeHomologyFiniteness
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualPartialChartNormalSublevelTransport

open Set CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

theorem actual_saddle_coordinate_pair_relative_finite
    (ρ a b : ℝ) (hρ : 0 < ρ) (hminus : -(ρ ^ 2) ≤ a)
    (ha : a < 0) (hb : 0 ≤ b) :
    let R := {z : ℂ | ‖z‖ ≤ ρ ∧ z.re ^ 2 - z.im ^ 2 ≤ b};
    let A : Set R := {z | z.1.re ^ 2 - z.1.im ^ 2 ≤ a};
    ∀ n : ℕ, Module.Finite ℤ (relativeHomology R A n) := by
  dsimp only
  let R := {z : ℂ | ‖z‖ ≤ ρ ∧ z.re ^ 2 - z.im ^ 2 ≤ b}
  let A : Set R := {z | z.1.re ^ 2 - z.1.im ^ 2 ≤ a}
  let L := {z : ℂ | ‖z‖ ≤ ρ ∧ z.re ^ 2 - z.im ^ 2 ≤ a}
  let e : A ≃ₜ L :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1, x.2.2.trans (ha.le.trans hb)⟩, x.2.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  letI : Module.Finite ℤ (H L 0) := actual_saddle_coordinate_lower_h0_finite ρ a hρ hminus ha
  letI : Module.Finite ℤ (H A 0) := Module.Finite.equiv
    (CircleHomologyComputation.homotopyHomologyIso e.toHomotopyEquiv 0).toLinearEquiv.symm
  letI : ContractibleSpace R := actual_saddle_coordinate_upper_contractible ρ b hρ.le hb
  letI : Subsingleton (H R 1) := ModuleCat.subsingleton_of_isZero
    (CircleHomologyComputation.contractible_positive_homology R 1 (by omega))
  have hp := actual_saddle_coordinate_pair_relative_profile ρ a b hρ hminus ha hb
  intro n
  cases n with
  | zero =>
      letI := ModuleCat.subsingleton_of_isZero hp.1
      infer_instance
  | succ n =>
      cases n with
      | zero => exact actual_relativeHomology_positive_finite_of_absolute_and_subspace_finite R A 0
      | succ n =>
          letI := ModuleCat.subsingleton_of_isZero (hp.2.2 n)
          infer_instance

/-- Transport the checked coordinate saddle through a literal supplied normal
chart. This retains the original F and gives its ACTUAL bounded local pair's
integral profile and finite generation in EVERY degree. -/
theorem actual_saddle_normal_chart_relative_profile
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (F : E → ℝ) (p : E) (ρ a b : ℝ)
    (hρ : 0 < ρ) (hminus : -(ρ ^ 2) ≤ a) (ha : a < 0) (hb : 0 ≤ b)
    (hball : Metric.closedBall (0 : ℂ) ρ ⊆ c.target)
    (hnormal : ∀ x ∈ c.source, F x = F p + ((c x).re ^ 2 - (c x).im ^ 2)) :
    let R := {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + b};
    let A : Set R := {x | F x.1 ≤ F p + a};
    IsZero (relativeHomology R A 0) ∧
      Module.finrank ℤ (relativeHomology R A 1) = 1 ∧
      (∀ n : ℕ, IsZero (relativeHomology R A (n + 2))) ∧
      ∀ n : ℕ, Module.Finite ℤ (relativeHomology R A n) := by
  dsimp only
  let R := {x : E | x ∈ c.source ∧ ‖c x‖ ≤ ρ ∧ F x ≤ F p + b}
  let A : Set R := {x | F x.1 ≤ F p + a}
  let Q := {z : ℂ | ‖z‖ ≤ ρ ∧ z.re ^ 2 - z.im ^ 2 ≤ b}
  let B : Set Q := {z | z.1.re ^ 2 - z.1.im ^ 2 ≤ a}
  let e := actual_partial_chart_normal_sublevel_homeomorph c F p
    (fun z => z.re ^ 2 - z.im ^ 2) ρ b hball hnormal
  let f : C(R, Q) := ⟨e, e.continuous⟩
  have hf : ∀ x ∈ A, f x ∈ B := fun x hx =>
    (actual_partial_chart_normal_sublevel_lower_membership c F p
      (fun z => z.re ^ 2 - z.im ^ 2) ρ b a hball hnormal x).mp hx
  have hi (n : ℕ) : IsIso (pairRelativeHomologyMap A B f hf n) :=
    actual_partial_chart_normal_sublevel_pair_relativeHomology_isIso c F p
      (fun z => z.re ^ 2 - z.im ^ 2) ρ b a hball hnormal n
  have iso (n : ℕ) : relativeHomology R A n ≅ relativeHomology Q B n := by
    letI := hi n
    exact asIso (pairRelativeHomologyMap A B f hf n)
  have hp := actual_saddle_coordinate_pair_relative_profile ρ a b hρ hminus ha hb
  have hfin := actual_saddle_coordinate_pair_relative_finite ρ a b hρ hminus ha hb
  refine ⟨hp.1.of_iso (iso 0), ?_, fun n => (hp.2.2 n).of_iso (iso (n + 2)), ?_⟩
  · rw [(iso 1).toLinearEquiv.finrank_eq]
    exact hp.2.1
  · intro n
    letI := hfin n
    exact Module.Finite.equiv (iso n).toLinearEquiv.symm

