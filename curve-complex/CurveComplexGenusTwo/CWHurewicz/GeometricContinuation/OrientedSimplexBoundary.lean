import Lean
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
import Mathlib.Algebra.BigOperators.Fin
import CurveComplexGenusTwo.CWHurewicz.SingularRealization.BoundaryHeaders
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.SuccPred

open Lean Elab Tactic
-- Scratch tooling: audit anonymous proof expressions without adding public theorem names.
syntax "audit_proof" tacticSeq : tactic
elab_rules : tactic
  | `(tactic| audit_proof $ts:tacticSeq) => do
    let initial ← getGoals
    evalTactic ts
    unless (← getGoals).isEmpty do
      throwError "anonymous audit requires a completed proof"
    let mut found : Array Name := #[]
    for g in initial do
      let p ← instantiateMVars (mkMVar g)
      for c in p.getUsedConstants do
        for a in (← collectAxioms c) do
          if !found.contains a then found := found.push a
    logInfo m!"ANONYMOUS_PROOF_AXIOMS: {found.qsort Name.lt}"
    for a in found do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "anonymous proof uses unapproved axiom {a}"

open Convexity Topology
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
theorem simplex_half_reparam (n : ℕ) :
    ∃ r : C({u : StdSimplex ℝ (Fin (n + 2)) // u.weights 1 ≤ u.weights 0},
      StdSimplex ℝ (Fin (n + 2))),
      (∀ u, (r u).weights 0 = u.val.weights 0 - u.val.weights 1) ∧
      (∀ u, (r u).weights 1 = 2 * u.val.weights 1) ∧
      ∀ u (j : Fin n), (r u).weights j.succ.succ = u.val.weights j.succ.succ := by
  let D := {u : StdSimplex ℝ (Fin (n + 2)) // u.weights 1 ≤ u.weights 0}
  let w (u : D) : Fin (n + 2) → ℝ := Fin.cases
    (u.val.weights 0 - u.val.weights 1)
    (Fin.cases (2 * u.val.weights 1) (fun j => u.val.weights j.succ.succ))
  let r (u : D) : StdSimplex ℝ (Fin (n + 2)) := {
    weights := Finsupp.equivFunOnFinite.symm (w u)
    nonneg := by
      intro i
      change 0 ≤ w u i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr u.property
      · refine Fin.cases ?_ (fun j => ?_) j
        · exact mul_nonneg (by norm_num) (StdSimplex.weights_nonneg _)
        · exact StdSimplex.weights_nonneg _
    total := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      change ∑ i : Fin (n + 2), w u i = 1
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [w, Fin.cases_zero, Fin.cases_succ]
      have hu : ∑ i : Fin (n + 2), u.val.weights i = 1 := by
        have ht := u.val.total
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at ht
        exact ht
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hu
      change u.val.weights 0 + (u.val.weights 1 + ∑ j : Fin n, u.val.weights j.succ.succ) = 1 at hu
      linarith }
  have hr : Continuous r := by
    apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff.mpr
    apply continuous_pi
    intro i
    change Continuous (fun u : D => w u i)
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ((StdSimplex.continuous_weights_apply ℝ 0).comp continuous_subtype_val).sub
        ((StdSimplex.continuous_weights_apply ℝ 1).comp continuous_subtype_val)
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact continuous_const.mul ((StdSimplex.continuous_weights_apply ℝ 1).comp continuous_subtype_val)
      · exact (StdSimplex.continuous_weights_apply ℝ j.succ.succ).comp continuous_subtype_val
  refine ⟨⟨r, hr⟩, ?_, ?_, ?_⟩ <;> intros <;> rfl
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier

open Convexity Topology
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
theorem simplex_facet_fold (n : ℕ) : ∃ R : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (n + 2))),
    (∀ u, (R u).weights 0 = max (u.weights 0 - u.weights 1) 0) ∧
    (∀ u, (R u).weights 1 = u.weights 0 + u.weights 1 - max (u.weights 0 - u.weights 1) 0) ∧
    (∀ u (j : Fin n), (R u).weights j.succ.succ = u.weights j.succ.succ) ∧
    ∀ u i, u.weights i = 0 → (R u).weights i = 0 := by
  let S := StdSimplex ℝ (Fin (n + 2))
  have hs : (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) := by apply Fin.ext; rfl
  let w (u : S) : Fin (n + 2) → ℝ := Fin.cases
    (max (u.weights 0 - u.weights 1) 0)
    (Fin.cases (u.weights 0 + u.weights 1 - max (u.weights 0 - u.weights 1) 0)
      (fun j => u.weights j.succ.succ))
  let R (u : S) : S := {
    weights := Finsupp.equivFunOnFinite.symm (w u)
    nonneg := by
      intro i
      change 0 ≤ w u i
      refine Fin.cases (le_max_right _ _) (fun j => ?_) i
      refine Fin.cases ?_ (fun j => StdSimplex.weights_nonneg _) j
      change 0 ≤ u.weights 0 + u.weights 1 - max (u.weights 0 - u.weights 1) 0
      by_cases h : u.weights 1 ≤ u.weights 0
      · rw [max_eq_left (sub_nonneg.mpr h)]
        linarith [StdSimplex.weights_nonneg (w := u) 1]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_lt (lt_of_not_ge h)))]
        linarith [StdSimplex.weights_nonneg (w := u) 0, StdSimplex.weights_nonneg (w := u) 1]
    total := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      change ∑ i : Fin (n + 2), w u i = 1
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [w, Fin.cases_zero, Fin.cases_succ]
      have hu := u.total
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ, Fin.sum_univ_succ, hs] at hu
      linarith }
  have hR : Continuous R := by
    apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff.mpr
    apply continuous_pi
    intro i
    change Continuous (fun u : S => w u i)
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ((StdSimplex.continuous_weights_apply ℝ 0).sub (StdSimplex.continuous_weights_apply ℝ 1)).max continuous_const
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact ((StdSimplex.continuous_weights_apply ℝ 0).add (StdSimplex.continuous_weights_apply ℝ 1)).sub
          (((StdSimplex.continuous_weights_apply ℝ 0).sub (StdSimplex.continuous_weights_apply ℝ 1)).max continuous_const)
      · exact StdSimplex.continuous_weights_apply ℝ j.succ.succ
  refine ⟨⟨R, hR⟩, (fun _ => rfl), (fun _ => rfl), (fun _ _ => rfl), ?_⟩
  intro u i
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hz
    change max (u.weights 0 - u.weights 1) 0 = 0
    rw [hz]
    exact max_eq_right (by linarith [StdSimplex.weights_nonneg (w := u) 1])
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro hz
      rw [hs] at hz
      change u.weights 0 + u.weights 1 - max (u.weights 0 - u.weights 1) 0 = 0
      rw [hz]
      have hh : u.weights 0 - 0 = u.weights 0 := sub_zero _
      rw [hh, max_eq_left (StdSimplex.weights_nonneg _)]
      ring
    · intro hz
      exact hz
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier

open Convexity Topology
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
theorem simplex_half_homeomorph (n : ℕ) : ∃ e :
    {u : StdSimplex ℝ (Fin (n + 2)) // u.weights 1 ≤ u.weights 0} ≃ₜ
      StdSimplex ℝ (Fin (n + 2)),
    (∀ u, (e u).weights 0 = u.val.weights 0 - u.val.weights 1) ∧
    (∀ u, (e u).weights 1 = 2 * u.val.weights 1) ∧
    ∀ u (j : Fin n), (e u).weights j.succ.succ = u.val.weights j.succ.succ := by
  have hs : (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  obtain ⟨r, hr₀, hr₁, hrt⟩ := simplex_half_reparam n
  let S := StdSimplex ℝ (Fin (n + 2))
  let D := {u : S // u.weights 1 ≤ u.weights 0}
  let w (u : S) : Fin (n + 2) → ℝ := Fin.cases
    (u.weights 0 + u.weights 1 / 2)
    (Fin.cases (u.weights 1 / 2) (fun j => u.weights j.succ.succ))
  let v (u : S) : S := {
    weights := Finsupp.equivFunOnFinite.symm (w u)
    nonneg := by
      intro i
      change 0 ≤ w u i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact add_nonneg (StdSimplex.weights_nonneg _) (div_nonneg (StdSimplex.weights_nonneg _) (by norm_num))
      · refine Fin.cases ?_ (fun j => ?_) j
        · exact div_nonneg (StdSimplex.weights_nonneg _) (by norm_num)
        · exact StdSimplex.weights_nonneg _
    total := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      change ∑ i : Fin (n + 2), w u i = 1
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [w, Fin.cases_zero, Fin.cases_succ]
      have hu := u.total
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ, Fin.sum_univ_succ] at hu
      rw [hs] at hu
      linarith }
  have hv (u : S) : (v u).weights 1 ≤ (v u).weights 0 := by
    change u.weights 1 / 2 ≤ u.weights 0 + u.weights 1 / 2
    linarith [StdSimplex.weights_nonneg (w := u) 0]
  let b (u : S) : D := ⟨v u, hv u⟩
  have hb : Continuous b := by
    have hc : Continuous v := by
      apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff.mpr
      apply continuous_pi
      intro i
      change Continuous (fun u : S => w u i)
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (StdSimplex.continuous_weights_apply ℝ 0).add
          ((StdSimplex.continuous_weights_apply ℝ 1).div_const 2)
      · refine Fin.cases ?_ (fun j => ?_) j
        · exact (StdSimplex.continuous_weights_apply ℝ 1).div_const 2
        · exact StdSimplex.continuous_weights_apply ℝ j.succ.succ
    exact hc.subtype_mk hv
  have hbr (u : D) : b (r u) = u := by
    apply Subtype.ext
    apply StdSimplex.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (r u).weights 0 + (r u).weights 1 / 2 = u.val.weights 0
      rw [hr₀, hr₁]
      ring
    · refine Fin.cases ?_ (fun j => ?_) j
      · change (r u).weights 1 / 2 = u.val.weights 1
        rw [hr₁]
        ring
      · change (r u).weights j.succ.succ = u.val.weights j.succ.succ
        exact hrt u j
  have hrb (u : S) : r (b u) = u := by
    apply StdSimplex.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hr₀]
      change (u.weights 0 + u.weights 1 / 2) - u.weights 1 / 2 = u.weights 0
      ring
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [hs, hr₁]
        change 2 * (u.weights 1 / 2) = u.weights 1
        ring
      · rw [hrt]
        rfl
  let e : D ≃ₜ S := {
    toFun := r
    invFun := b
    left_inv := hbr
    right_inv := hrb
    continuous_toFun := r.continuous
    continuous_invFun := hb }
  exact ⟨e, hr₀, hr₁, hrt⟩
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier


open CategoryTheory Convexity Topology CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
open scoped Simplicial unitInterval
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
-- Exact original binary merge statement, with actual arbitrary-chart geometry.
private theorem recoveredBinaryMerge {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (smap : C(StdSimplex ℝ (Fin (k + 4)), X))
    (hlow : ∀ t (i j : Fin (k + 4)), i ≠ j → t.weights i = 0 → t.weights j = 0 → smap t = x)
    (q : C(StdSimplex ℝ (Fin (k + 3)), StdSimplex ℝ (Fin (k + 4))))
    (hq₀ : ∀ u, (q u).weights 0 = max (u.weights 1 - u.weights 0) 0)
    (hq₁ : ∀ u, (q u).weights 1 = max (u.weights 0 - u.weights 1) 0)
    (hq₂ : ∀ u, (q u).weights 2 = 2 * min (u.weights 0) (u.weights 1))
    (hqt : ∀ u (j : Fin (k + 1)), (q u).weights j.succ.succ.succ = u.weights j.succ.succ)
    (f₀ f₁ m : GenLoop (Fin (k + 2)) X x)
    (hf₀ : ∀ a, f₀ a = smap ((e a).map (SimplexCategory.δ (0 : Fin (k + 4)))))
    (hf₁ : ∀ a, f₁ a = smap ((e a).map (SimplexCategory.δ (1 : Fin (k + 4)))))
    (hm : ∀ a, m a = smap (q (e a))) :
    (⟦m⟧ : HomotopyGroup.Pi (k + 2) X x) =
      ((· * ·) : HomotopyGroup.Pi (k + 2) X x → HomotopyGroup.Pi (k + 2) X x →
        HomotopyGroup.Pi (k + 2) X x) ⟦f₀⟧
        ((fun a : HomotopyGroup.Pi (k + 2) X x => a ^ (-1 : ℤ)) ⟦f₁⟧) := by
  audit_proof
    classical
    have cut_multiplication {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (p r m : GenLoop (Fin (k + 2)) X x)
    (hp : ∀ a, (e a).weights 0 ≤ (e a).weights 1 → p a = x)
    (hr : ∀ a, (e a).weights 1 ≤ (e a).weights 0 → r a = x)
    (hml : ∀ a, (e a).weights 1 ≤ (e a).weights 0 → m a = p a)
    (hmr : ∀ a, (e a).weights 0 ≤ (e a).weights 1 → m a = r a) :
    GenLoop.Homotopic m (GenLoop.transAt (0 : Fin (k + 2)) r p) := by
      audit_proof
        classical
        have localize_half {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
        (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
        (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
        (p : GenLoop (Fin (k + 2)) X x)
        (hp : ∀ a, (e a).weights 0 ≤ (e a).weights 1 → p a = x) :
        ∃ β : Fin (k + 2) → unitInterval,
          (e β).weights 1 < (e β).weights 0 ∧ β ∉ Cube.boundary (Fin (k + 2)) ∧
          ∀ U : Set (Fin (k + 2) → unitInterval), IsOpen U → β ∈ U →
            ∃ q : GenLoop (Fin (k + 2)) X x, GenLoop.Homotopic p q ∧
              (∀ a, a ∉ U → q a = x) ∧
              (∀ a, (e a).weights 0 ≤ (e a).weights 1 → q a = x) ∧
              ∃ K : p.val.HomotopyRel q.val (Cube.boundary (Fin (k + 2))),
                ∀ t a, (e a).weights 0 ≤ (e a).weights 1 → K (t, a) = x := by
          audit_proof
            classical
            have half_chart (k : ℕ)
            (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
            (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i) :
            ∃ d : (Fin (k + 2) → unitInterval) ≃ₜ
                {u : StdSimplex ℝ (Fin (k + 3)) // u.weights 1 ≤ u.weights 0},
              (∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔
                (d a).val.weights 0 = (d a).val.weights 1 ∨ ¬ ∀ i, 0 < (d a).val.weights i) ∧
              (let c : Fin (k + 2) → unitInterval := fun _ => ⟨1 / 2, by constructor <;> norm_num⟩
               (d c).val.weights 1 < (d c).val.weights 0 ∧ ∀ i, 0 < (d c).val.weights i) := by
              audit_proof
                obtain ⟨L, hL₀, hL₁, hLt⟩ := simplex_half_homeomorph (k + 1)
                let d := e.trans L.symm
                have hd (a : Fin (k + 2) → unitInterval) : L (d a) = e a := by simp [d]
                have hw₀ (a : Fin (k + 2) → unitInterval) :
                    (e a).weights 0 = (d a).val.weights 0 - (d a).val.weights 1 := by
                  rw [← hd, hL₀]
                have hw₁ (a : Fin (k + 2) → unitInterval) :
                    (e a).weights 1 = 2 * (d a).val.weights 1 := by
                  rw [← hd, hL₁]
                have hwt (a : Fin (k + 2) → unitInterval) (j : Fin (k + 1)) :
                    (e a).weights j.succ.succ = (d a).val.weights j.succ.succ := by
                  rw [← hd, hLt]
                have hs : (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) := by apply Fin.ext; rfl
                refine ⟨d, ?_, ?_⟩
                · intro a
                  rw [he]
                  constructor
                  · intro ha
                    obtain ⟨i, hi⟩ := not_forall.mp ha
                    revert hi
                    refine Fin.cases ?_ (fun j => ?_) i
                    · intro hi
                      left
                      have hh := (d a).property
                      rw [hw₀] at hi
                      linarith
                    · refine Fin.cases ?_ (fun j => ?_) j
                      · intro hi
                        right
                        intro hp
                        rw [hs, hw₁] at hi
                        linarith [hp 1]
                      · intro hi
                        right
                        intro hp
                        rw [hwt] at hi
                        exact hi (hp j.succ.succ)
                  · rintro (hseam | hbd)
                    · intro hp
                      have hh := hp 0
                      rw [hw₀, hseam, sub_self] at hh
                      exact lt_irrefl _ hh
                    · obtain ⟨i, hi⟩ := not_forall.mp hbd
                      have hz : (d a).val.weights i = 0 :=
                        le_antisymm (le_of_not_gt hi) (StdSimplex.weights_nonneg _)
                      intro hp
                      revert hz
                      refine Fin.cases ?_ (fun j => ?_) i
                      · intro hz
                        have hz₁ : (d a).val.weights 1 = 0 := by
                          have hh := (d a).property
                          rw [hz] at hh
                          exact le_antisymm hh (StdSimplex.weights_nonneg _)
                        have hh := hp 1
                        rw [hw₁, hz₁, mul_zero] at hh
                        exact lt_irrefl _ hh
                      · refine Fin.cases ?_ (fun j => ?_) j
                        · intro hz
                          rw [hs] at hz
                          have hh := hp 1
                          rw [hw₁, hz, mul_zero] at hh
                          exact lt_irrefl _ hh
                        · intro hz
                          have hh := hp j.succ.succ
                          rw [hwt, hz] at hh
                          exact lt_irrefl _ hh
                · let c : Fin (k + 2) → unitInterval := fun _ => ⟨1 / 2, by constructor <;> norm_num⟩
                  have hc : c ∉ Cube.boundary (Fin (k + 2)) := by
                    rintro ⟨i, hi | hi⟩
                    · have hh := congrArg Subtype.val hi
                      change (1 / 2 : ℝ) = 0 at hh
                      norm_num at hh
                    · have hh := congrArg Subtype.val hi
                      change (1 / 2 : ℝ) = 1 at hh
                      norm_num at hh
                  have hpos : ∀ i, 0 < (e c).weights i := by
                    by_contra hh
                    exact hc ((he c).mpr hh)
                  change (d c).val.weights 1 < (d c).val.weights 0 ∧ ∀ i, 0 < (d c).val.weights i
                  have hstrict : (d c).val.weights 1 < (d c).val.weights 0 := by
                    have hh := hpos 0
                    rw [hw₀] at hh
                    linarith
                  refine ⟨hstrict, ?_⟩
                  intro i
                  refine Fin.cases ?_ (fun j => ?_) i
                  · linarith [StdSimplex.weights_nonneg (w := (d c).val) 1]
                  · refine Fin.cases ?_ (fun j => ?_) j
                    · rw [hs]
                      have hh := hpos 1
                      rw [hw₁] at hh
                      linarith
                    · rw [← hwt]
                      exact hpos _
            have localize {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
            (f : GenLoop (Fin (k + 2)) X x)
            (U : Set (Fin (k + 2) → unitInterval)) (hU : IsOpen U)
            (hc : (fun _ : Fin (k + 2) => (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval)) ∈ U) :
            ∃ g : GenLoop (Fin (k + 2)) X x,
              GenLoop.Homotopic f g ∧ ∀ a, a ∉ U → g a = x := by
              audit_proof
                have compress (b : ℝ) (hb₀ : 0 ≤ b) (hb₁ : b < 1 / 2) :
                    ∃ g : GenLoop (Fin (k + 2)) X x,
                      GenLoop.Homotopic f g ∧ ∀ a, (∃ i, (a i).val ≤ b ∨ 1 - b ≤ (a i).val) → g a = x := by
                  audit_proof
                    let r : unitInterval × (Fin (k + 2) → unitInterval) → Fin (k + 2) → unitInterval :=
                      fun z i => Set.projIcc 0 1 zero_le_one (((z.2 i).val - z.1.val * b) / (1 - 2 * z.1.val * b))
                    have hd (t : unitInterval) : 0 < 1 - 2 * t.val * b := by nlinarith [t.property.2]
                    have hr : Continuous r := by
                      apply continuous_pi
                      intro i
                      apply continuous_projIcc.comp
                      exact ((continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)).sub
                        ((continuous_subtype_val.comp continuous_fst).mul_const b)).div
                        (continuous_const.sub ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).mul_const b))
                        (fun z => ne_of_gt (hd z.1))
                    have hb (t : unitInterval) (a : Fin (k + 2) → unitInterval)
                        (ha : a ∈ Cube.boundary (Fin (k + 2))) : r (t, a) ∈ Cube.boundary (Fin (k + 2)) := by
                      obtain ⟨i, hi | hi⟩ := ha
                      · refine ⟨i, Or.inl ?_⟩
                        change Set.projIcc 0 1 zero_le_one (((a i).val - t.val * b) / (1 - 2 * t.val * b)) = 0
                        apply Set.projIcc_of_le_left zero_le_one
                        rw [hi]
                        exact div_nonpos_of_nonpos_of_nonneg (by simpa using neg_nonpos.mpr (mul_nonneg t.property.1 hb₀)) (le_of_lt (hd t))
                      · refine ⟨i, Or.inr ?_⟩
                        change Set.projIcc 0 1 zero_le_one (((a i).val - t.val * b) / (1 - 2 * t.val * b)) = 1
                        apply Set.projIcc_of_right_le zero_le_one
                        rw [hi]
                        apply (le_div_iff₀ (hd t)).mpr
                        change 1 * (1 - 2 * t.val * b) ≤ 1 - t.val * b
                        nlinarith [t.property.1]
                    have hzero (a : Fin (k + 2) → unitInterval) : r (0, a) = a := by
                      funext i
                      change Set.projIcc 0 1 zero_le_one (((a i).val - (0 : unitInterval).val * b) /
                        (1 - 2 * (0 : unitInterval).val * b)) = a i
                      simp only [show (0 : unitInterval).val = (0 : ℝ) from rfl, zero_mul, mul_zero, sub_zero, div_one, Set.projIcc_val]
                    let g : GenLoop (Fin (k + 2)) X x :=
                      ⟨f.val.comp ⟨fun a => r (1, a), hr.comp (continuous_const.prodMk continuous_id)⟩,
                        fun a ha => GenLoop.boundary f _ (hb 1 a ha)⟩
                    refine ⟨g, ⟨{
                      toHomotopy := {
                        toContinuousMap := f.val.comp ⟨r, hr⟩
                        map_zero_left := ?_
                        map_one_left := fun _ => rfl }
                      prop' := ?_ }⟩, ?_⟩
                    · intro a
                      change f (r (0, a)) = f a
                      rw [hzero]
                    · intro t a ha
                      change f (r (t, a)) = f a
                      exact (GenLoop.boundary f _ (hb t a ha)).trans (GenLoop.boundary f a ha).symm
                    · intro a ha
                      change f (r (1, a)) = x
                      apply GenLoop.boundary f
                      obtain ⟨i, hi | hi⟩ := ha
                      · refine ⟨i, Or.inl ?_⟩
                        change Set.projIcc 0 1 zero_le_one (((a i).val - (1 : unitInterval).val * b) /
                          (1 - 2 * (1 : unitInterval).val * b)) = 0
                        apply Set.projIcc_of_le_left zero_le_one
                        exact div_nonpos_of_nonpos_of_nonneg (by simpa using sub_nonpos.mpr hi) (le_of_lt (hd 1))
                      · refine ⟨i, Or.inr ?_⟩
                        change Set.projIcc 0 1 zero_le_one (((a i).val - (1 : unitInterval).val * b) /
                          (1 - 2 * (1 : unitInterval).val * b)) = 1
                        apply Set.projIcc_of_right_le zero_le_one
                        apply (le_div_iff₀ (hd 1)).mpr
                        change 1 * (1 - 2 * (1 : ℝ) * b) ≤ (a i).val - (1 : ℝ) * b
                        linarith
                let c : Fin (k + 2) → unitInterval := fun _ => ⟨1 / 2, by constructor <;> norm_num⟩
                obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc
                let δ : ℝ := min ε (1 / 4)
                have hδ : 0 < δ := lt_min hε (by norm_num)
                have hδε : δ ≤ ε := min_le_left _ _
                have hδsmall : δ ≤ 1 / 4 := min_le_right _ _
                let b : ℝ := 1 / 2 - δ
                have hb₀ : 0 ≤ b := by dsimp [b]; linarith
                have hb₁ : b < 1 / 2 := by dsimp [b]; linarith
                obtain ⟨g, hfg, hg⟩ := compress b hb₀ hb₁
                refine ⟨g, hfg, ?_⟩
                intro a ha
                by_contra hne
                have hcoord (i : Fin (k + 2)) : b < (a i).val ∧ (a i).val < 1 - b := by
                  have hn : ¬ ((a i).val ≤ b ∨ 1 - b ≤ (a i).val) := by
                    intro hh
                    exact hne (hg a ⟨i, hh⟩)
                  simpa only [not_or, not_le] using hn
                have hdac : dist a c < δ := by
                  apply (dist_pi_lt_iff hδ).mpr
                  intro i
                  change dist (a i).val (1 / 2 : ℝ) < δ
                  rw [Real.dist_eq]
                  apply abs_lt.mpr
                  have hi := hcoord i
                  dsimp [b] at hi
                  constructor <;> linarith [hi.1, hi.2]
                exact ha (hball (lt_of_lt_of_le hdac hδε))
            have glue {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
            (L R : Set A) (hL : IsClosed L) (hR : IsClosed R)
            (hcover : ∀ a, a ∈ L ∨ a ∈ R)
            (HL : C(unitInterval × L, X)) (HR : C(unitInterval × R, X))
            (hagree : ∀ t a (hl : a ∈ L) (hr : a ∈ R), HL (t, ⟨a, hl⟩) = HR (t, ⟨a, hr⟩)) :
            ∃ H : C(unitInterval × A, X),
              (∀ t a (hl : a ∈ L), H (t, a) = HL (t, ⟨a, hl⟩)) ∧
              ∀ t a (hr : a ∈ R), H (t, a) = HR (t, ⟨a, hr⟩) := by
              audit_proof
                classical
                let S : Bool → Set (unitInterval × A) := fun b => if b then {z | z.2 ∈ R} else {z | z.2 ∈ L}
                let φ : ∀ b, C(S b, X) := fun b => by
                  cases b
                  · exact HL.comp ⟨fun z => (z.val.1, ⟨z.val.2, z.property⟩),
                      (continuous_fst.comp continuous_subtype_val).prodMk
                        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z => z.property))⟩
                  · exact HR.comp ⟨fun z => (z.val.1, ⟨z.val.2, z.property⟩),
                      (continuous_fst.comp continuous_subtype_val).prodMk
                        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z => z.property))⟩
                have hφ : ∀ i j z (hi : z ∈ S i) (hj : z ∈ S j), φ i ⟨z, hi⟩ = φ j ⟨z, hj⟩ := by
                  intro i j z hi hj
                  cases i <;> cases j
                  · rfl
                  · exact hagree z.1 z.2 hi hj
                  · exact (hagree z.1 z.2 hj hi).symm
                  · rfl
                have hScover : (⋃ b, S b) = Set.univ := by
                  apply Set.eq_univ_of_forall
                  intro z
                  rcases hcover z.2 with hl | hr
                  · exact Set.mem_iUnion.mpr ⟨false, hl⟩
                  · exact Set.mem_iUnion.mpr ⟨true, hr⟩
                let h : unitInterval × A → X := Set.liftCover S (fun b => φ b) hφ hScover
                have hclosed : ∀ b, IsClosed (S b) := by
                  intro b
                  cases b
                  · exact hL.preimage continuous_snd
                  · exact hR.preimage continuous_snd
                have hcont : ∀ b, ContinuousOn h (S b) := by
                  intro b
                  rw [continuousOn_iff_continuous_domRestrict]
                  change Continuous (fun z : S b => h z.val)
                  have heq : (fun z : S b => h z.val) = φ b := by
                    funext z
                    exact Set.liftCover_coe z
                  rw [heq]
                  exact (φ b).continuous
                let H : C(unitInterval × A, X) := ⟨h, (locallyFinite_of_finite S).continuous hScover hclosed hcont⟩
                refine ⟨H, ?_, ?_⟩
                · intro t a ha
                  change h (t, a) = _
                  dsimp only [h]
                  rw [Set.liftCover_of_mem (i := false) (hx := (show (t, a) ∈ S false from ha))]
                  rfl
                · intro t a ha
                  change h (t, a) = _
                  dsimp only [h]
                  rw [Set.liftCover_of_mem (i := true) (hx := (show (t, a) ∈ S true from ha))]
                  rfl
            obtain ⟨d, hdb, hdc⟩ := half_chart k e he
            let c : Fin (k + 2) → unitInterval := fun _ => ⟨1 / 2, by constructor <;> norm_num⟩
            let A : C((Fin (k + 2) → unitInterval), Fin (k + 2) → unitInterval) :=
              ⟨fun a => e.symm (d a).val, e.symm.continuous.comp (continuous_subtype_val.comp d.continuous)⟩
            have heA (a : Fin (k + 2) → unitInterval) : e (A a) = (d a).val := by
              change e (e.symm (d a).val) = _
              exact e.apply_symm_apply _
            let β := A c
            have hβstrict : (e β).weights 1 < (e β).weights 0 := by
              rw [heA]
              exact hdc.1
            have hβint : β ∉ Cube.boundary (Fin (k + 2)) := by
              intro hb
              have hh := (he β).mp hb
              rw [heA] at hh
              exact hh hdc.2
            refine ⟨β, hβstrict, hβint, ?_⟩
            intro U hU hβ
            let P : GenLoop (Fin (k + 2)) X x := ⟨p.val.comp A, by
              intro a ha
              rcases (hdb a).mp ha with hseam | hb
              · apply hp
                rw [heA, hseam]
              · apply GenLoop.boundary p
                apply (he _).mpr
                rwa [heA]⟩
            let U' : Set (Fin (k + 2) → unitInterval) := A ⁻¹' U
            obtain ⟨Q, ⟨H⟩, hQoutside⟩ := localize k x P U' (hU.preimage A.continuous) hβ
            let S := StdSimplex ℝ (Fin (k + 3))
            let L : Set S := {u | u.weights 1 ≤ u.weights 0}
            let R : Set S := {u | u.weights 0 ≤ u.weights 1}
            have hR_of_not_L (u : S) (hl : u ∉ L) : u ∈ R := by
              change ¬ u.weights 1 ≤ u.weights 0 at hl
              change u.weights 0 ≤ u.weights 1
              exact le_of_lt (lt_of_not_ge hl)
            have hdseam (u : L) (hu : u.val.weights 0 = u.val.weights 1 ∨ ¬ ∀ i, 0 < u.val.weights i) :
                d.symm u ∈ Cube.boundary (Fin (k + 2)) := by
              apply (hdb _).mpr
              rwa [d.apply_symm_apply]
            let HL : C(unitInterval × L, X) := H.toContinuousMap.comp
              ⟨fun z => (z.1, d.symm z.2), continuous_fst.prodMk (d.symm.continuous.comp continuous_snd)⟩
            let HR : C(unitInterval × R, X) := ContinuousMap.const _ x
            obtain ⟨G, hGL, hGR⟩ := glue L R
              (isClosed_le (StdSimplex.continuous_weights_apply ℝ 1) (StdSimplex.continuous_weights_apply ℝ 0))
              (isClosed_le (StdSimplex.continuous_weights_apply ℝ 0) (StdSimplex.continuous_weights_apply ℝ 1))
              (fun u => le_total (u.weights 1) (u.weights 0)) HL HR (by
                intro t u hl hr
                change H (t, d.symm ⟨u, hl⟩) = x
                have hb := hdseam ⟨u, hl⟩ (Or.inl (le_antisymm hr hl))
                rw [H.eq_fst t hb]
                exact GenLoop.boundary P _ hb)
            have hGzero (u : S) : G (0, u) = p (e.symm u) := by
              by_cases hl : u ∈ L
              · rw [hGL 0 u hl]
                change H (0, d.symm ⟨u, hl⟩) = p (e.symm u)
                rw [H.apply_zero]
                change p (e.symm (d (d.symm ⟨u, hl⟩)).val) = _
                rw [d.apply_symm_apply]
              · have hr : u ∈ R := hR_of_not_L u hl
                rw [hGR 0 u hr]
                change x = p (e.symm u)
                symm
                apply hp
                rwa [e.apply_symm_apply]
            have hGb (t : unitInterval) (u : S) (hu : ¬ ∀ i, 0 < u.weights i) : G (t, u) = x := by
              by_cases hl : u ∈ L
              · rw [hGL t u hl]
                change H (t, d.symm ⟨u, hl⟩) = x
                have hb := hdseam ⟨u, hl⟩ (Or.inr hu)
                rw [H.eq_fst t hb]
                exact GenLoop.boundary P _ hb
              · exact hGR t u (hR_of_not_L u hl)
            let q : GenLoop (Fin (k + 2)) X x :=
              ⟨G.comp ⟨fun a => (1, e a), continuous_const.prodMk e.continuous⟩,
                fun a ha => hGb 1 (e a) ((he a).mp ha)⟩
            let K : p.val.HomotopyRel q.val (Cube.boundary (Fin (k + 2))) := {
              toHomotopy := {
                toContinuousMap := G.comp ⟨fun z => (z.1, e z.2),
                  continuous_fst.prodMk (e.continuous.comp continuous_snd)⟩
                map_zero_left := by
                  intro a
                  change G (0, e a) = p a
                  rw [hGzero, e.symm_apply_apply]
                map_one_left := fun _ => rfl }
              prop' := by
                intro t a ha
                change G (t, e a) = p a
                rw [hGb t (e a) ((he a).mp ha), GenLoop.boundary p a ha] }
            refine ⟨q, ⟨K⟩, ?_, ?_, ⟨K, ?_⟩⟩
            · intro a ha
              change G (1, e a) = x
              by_cases hl : e a ∈ L
              · rw [hGL 1 (e a) hl]
                change H (1, d.symm ⟨e a, hl⟩) = x
                rw [H.apply_one]
                apply hQoutside
                intro hh
                apply ha
                change A (d.symm ⟨e a, hl⟩) ∈ U at hh
                have hA : A (d.symm ⟨e a, hl⟩) = a := by
                  change e.symm (d (d.symm ⟨e a, hl⟩)).val = a
                  rw [d.apply_symm_apply, e.symm_apply_apply]
                rwa [hA] at hh
              · exact hGR 1 (e a) (hR_of_not_L (e a) hl)
            · intro a ha
              exact hGR 1 (e a) ha
            · intro t a ha
              exact hGR t (e a) ha
        have swap_chart (k : ℕ)
        (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
        (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i) :
        ∃ e' : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)),
          (∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e' a).weights i) ∧
          (∀ a, (e' a).weights 0 = (e a).weights 1) ∧
          (∀ a, (e' a).weights 1 = (e a).weights 0) ∧
          ∀ a (j : Fin (k + 1)), (e' a).weights j.succ.succ = (e a).weights j.succ.succ := by
          audit_proof
            let τ : Equiv.Perm (Fin (k + 3)) := Equiv.swap 0 1
            have hTT (u : StdSimplex ℝ (Fin (k + 3))) : (u.map τ).map τ = u := by
              rw [← StdSimplex.map_comp]
              have hττ : (τ : Fin (k + 3) → Fin (k + 3)) ∘ τ = id := by
                funext i
                simp [τ]
              rw [hττ, StdSimplex.map_id]
            let T : StdSimplex ℝ (Fin (k + 3)) ≃ₜ StdSimplex ℝ (Fin (k + 3)) := {
              toFun := StdSimplex.map τ
              invFun := StdSimplex.map τ
              left_inv := hTT
              right_inv := hTT
              continuous_toFun := by fun_prop
              continuous_invFun := by fun_prop }
            have hT (u : StdSimplex ℝ (Fin (k + 3))) (i : Fin (k + 3)) :
                (T u).weights (τ i) = u.weights i := by
              change (u.map τ).weights (τ i) = u.weights i
              rw [StdSimplex.weights_map]
              exact Finsupp.mapDomain_apply_of_injective τ.injective _ _
            have hpos (u : StdSimplex ℝ (Fin (k + 3))) :
                (∀ i, 0 < (T u).weights i) ↔ ∀ i, 0 < u.weights i := by
              constructor
              · intro h i
                simpa [hT] using h (τ i)
              · intro h i
                have hh := hT u (τ i)
                have hτi : τ (τ i) = i := by simp [τ]
                rw [hτi] at hh
                rw [hh]
                exact h _
            let e' := e.trans T
            refine ⟨e', ?_, ?_, ?_, ?_⟩
            · intro a
              change a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (T (e a)).weights i
              rw [hpos]
              exact he a
            · intro a
              simpa [e', τ] using hT (e a) 1
            · intro a
              simpa [e', τ] using hT (e a) 0
            · intro a j
              have hτj : τ j.succ.succ = j.succ.succ :=
                Equiv.swap_apply_of_ne_of_ne (by apply Fin.ne_of_val_ne; simp)
                  (by apply Fin.ne_of_val_ne; simp)
              simpa [e', hτj] using hT (e a) j.succ.succ
        have glue {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
        (L R : Set A) (hL : IsClosed L) (hR : IsClosed R)
        (hcover : ∀ a, a ∈ L ∨ a ∈ R)
        (HL : C(unitInterval × L, X)) (HR : C(unitInterval × R, X))
        (hagree : ∀ t a (hl : a ∈ L) (hr : a ∈ R), HL (t, ⟨a, hl⟩) = HR (t, ⟨a, hr⟩)) :
        ∃ H : C(unitInterval × A, X),
          (∀ t a (hl : a ∈ L), H (t, a) = HL (t, ⟨a, hl⟩)) ∧
          ∀ t a (hr : a ∈ R), H (t, a) = HR (t, ⟨a, hr⟩) := by
          audit_proof
            classical
            let S : Bool → Set (unitInterval × A) := fun b => if b then {z | z.2 ∈ R} else {z | z.2 ∈ L}
            let φ : ∀ b, C(S b, X) := fun b => by
              cases b
              · exact HL.comp ⟨fun z => (z.val.1, ⟨z.val.2, z.property⟩),
                  (continuous_fst.comp continuous_subtype_val).prodMk
                    ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z => z.property))⟩
              · exact HR.comp ⟨fun z => (z.val.1, ⟨z.val.2, z.property⟩),
                  (continuous_fst.comp continuous_subtype_val).prodMk
                    ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z => z.property))⟩
            have hφ : ∀ i j z (hi : z ∈ S i) (hj : z ∈ S j), φ i ⟨z, hi⟩ = φ j ⟨z, hj⟩ := by
              intro i j z hi hj
              cases i <;> cases j
              · rfl
              · exact hagree z.1 z.2 hi hj
              · exact (hagree z.1 z.2 hj hi).symm
              · rfl
            have hScover : (⋃ b, S b) = Set.univ := by
              apply Set.eq_univ_of_forall
              intro z
              rcases hcover z.2 with hl | hr
              · exact Set.mem_iUnion.mpr ⟨false, hl⟩
              · exact Set.mem_iUnion.mpr ⟨true, hr⟩
            let h : unitInterval × A → X := Set.liftCover S (fun b => φ b) hφ hScover
            have hclosed : ∀ b, IsClosed (S b) := by
              intro b
              cases b
              · exact hL.preimage continuous_snd
              · exact hR.preimage continuous_snd
            have hcont : ∀ b, ContinuousOn h (S b) := by
              intro b
              rw [continuousOn_iff_continuous_domRestrict]
              change Continuous (fun z : S b => h z.val)
              have heq : (fun z : S b => h z.val) = φ b := by
                funext z
                exact Set.liftCover_coe z
              rw [heq]
              exact (φ b).continuous
            let H : C(unitInterval × A, X) := ⟨h, (locallyFinite_of_finite S).continuous hScover hclosed hcont⟩
            refine ⟨H, ?_, ?_⟩
            · intro t a ha
              change h (t, a) = _
              dsimp only [h]
              rw [Set.liftCover_of_mem (i := false) (hx := (show (t, a) ∈ S false from ha))]
              rfl
            · intro t a ha
              change h (t, a) = _
              dsimp only [h]
              rw [Set.liftCover_of_mem (i := true) (hx := (show (t, a) ∈ S true from ha))]
              rfl
        have axis_cut {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
        (i : Fin (k + 2)) (cut : ℝ) (hcut₀ : 0 < cut) (hcut₁ : cut < 1)
        (p r m : GenLoop (Fin (k + 2)) X x)
        (hp : ∀ a, cut ≤ (a i).val → p a = x)
        (hr : ∀ a, (a i).val ≤ cut → r a = x)
        (hml : ∀ a, (a i).val ≤ cut → m a = p a)
        (hmr : ∀ a, cut ≤ (a i).val → m a = r a) :
        GenLoop.Homotopic m (GenLoop.transAt i r p) := by
          audit_proof
            have midpoint_cut {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
            (i : Fin (k + 2)) (p r m : GenLoop (Fin (k + 2)) X x)
            (hp : ∀ a, 1 / 2 ≤ (a i).val → p a = x)
            (hr : ∀ a, (a i).val ≤ 1 / 2 → r a = x)
            (hml : ∀ a, (a i).val ≤ 1 / 2 → m a = p a)
            (hmr : ∀ a, 1 / 2 ≤ (a i).val → m a = r a) :
            GenLoop.Homotopic m (GenLoop.transAt i r p) := by
              audit_proof
                have split_loop {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
                (f : GenLoop (Fin (k + 2)) X x) (i : Fin (k + 2))
                (hmiddle : ∀ a : Fin (k + 2) → unitInterval, (a i).val = 1 / 2 → f a = x) :
                ∃ p q : GenLoop (Fin (k + 2)) X x,
                  (∀ a, p a = f (Function.update a i ⟨(a i).val / 2, by
                    constructor <;> linarith [(a i).property.1, (a i).property.2]⟩)) ∧
                  (∀ a, q a = f (Function.update a i ⟨((a i).val + 1) / 2, by
                    constructor <;> linarith [(a i).property.1, (a i).property.2]⟩)) ∧
                  f = GenLoop.transAt i p q ∧
                  (⟦f⟧ : HomotopyGroup.Pi (k + 2) X x) =
                    ((· * ·) : HomotopyGroup.Pi (k + 2) X x → HomotopyGroup.Pi (k + 2) X x →
                      HomotopyGroup.Pi (k + 2) X x) ⟦q⟧ ⟦p⟧ := by
                  let L : C(unitInterval, unitInterval) := ⟨fun t => ⟨t.val / 2, by
                    constructor <;> linarith [t.property.1, t.property.2]⟩,
                    (continuous_subtype_val.div_const 2).subtype_mk (fun t => by
                      constructor <;> linarith [t.property.1, t.property.2])⟩
                  let R : C(unitInterval, unitInterval) := ⟨fun t => ⟨(t.val + 1) / 2, by
                    constructor <;> linarith [t.property.1, t.property.2]⟩,
                    (continuous_subtype_val.add_const 1 |>.div_const 2).subtype_mk (fun t => by
                      constructor <;> linarith [t.property.1, t.property.2])⟩
                  let l : C((Fin (k + 2) → unitInterval), Fin (k + 2) → unitInterval) :=
                    ⟨fun a => Function.update a i (L (a i)), continuous_id.update i (L.continuous.comp (continuous_apply i))⟩
                  let r : C((Fin (k + 2) → unitInterval), Fin (k + 2) → unitInterval) :=
                    ⟨fun a => Function.update a i (R (a i)), continuous_id.update i (R.continuous.comp (continuous_apply i))⟩
                  have hl (a : Fin (k + 2) → unitInterval) (ha : a ∈ Cube.boundary (Fin (k + 2))) : f (l a) = x := by
                    obtain ⟨j, hj⟩ := ha
                    by_cases hji : j = i
                    · subst j
                      rcases hj with hj | hj
                      · apply GenLoop.boundary f
                        refine ⟨i, Or.inl ?_⟩
                        apply Subtype.ext
                        simp [l, L, hj]
                      · apply hmiddle
                        simp [l, L, hj]
                    · apply GenLoop.boundary f
                      exact ⟨j, by simpa [l, Function.update_of_ne hji] using hj⟩
                  have hr (a : Fin (k + 2) → unitInterval) (ha : a ∈ Cube.boundary (Fin (k + 2))) : f (r a) = x := by
                    obtain ⟨j, hj⟩ := ha
                    by_cases hji : j = i
                    · subst j
                      rcases hj with hj | hj
                      · apply hmiddle
                        simp [r, R, hj]
                      · apply GenLoop.boundary f
                        refine ⟨i, Or.inr ?_⟩
                        apply Subtype.ext
                        simp [r, R, hj]
                    · apply GenLoop.boundary f
                      exact ⟨j, by simpa [r, Function.update_of_ne hji] using hj⟩
                  let p : GenLoop (Fin (k + 2)) X x := ⟨f.val.comp l, hl⟩
                  let q : GenLoop (Fin (k + 2)) X x := ⟨f.val.comp r, hr⟩
                  have heq : f = GenLoop.transAt i p q := by
                    apply GenLoop.ext
                    intro a
                    simp only [GenLoop.transAt, GenLoop.coe_copy]
                    change f a = if (a i).val ≤ 1 / 2 then
                      p (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * (a i).val)))
                      else q (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * (a i).val - 1)))
                    split_ifs with h
                    · change f a = f (l (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * (a i).val))))
                      apply congrArg f
                      symm
                      apply funext
                      intro j
                      by_cases hji : j = i
                      · subst j
                        apply Subtype.ext
                        have hclip : (Set.projIcc 0 1 zero_le_one (2 * (a i).val)).val = 2 * (a i).val := by
                          exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one (by
                            constructor <;> linarith [(a i).property.1]))
                        change (l (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * (a i).val))) i).val = (a i).val
                        dsimp only [l, ContinuousMap.coe_mk]
                        rw [Function.update_self, Function.update_self]
                        change (Set.projIcc 0 1 zero_le_one (2 * (a i).val)).val / 2 = (a i).val
                        rw [hclip]
                        ring
                      · simp [l, Function.update_of_ne hji]
                    · change f a = f (r (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * (a i).val - 1))))
                      apply congrArg f
                      symm
                      apply funext
                      intro j
                      by_cases hji : j = i
                      · subst j
                        apply Subtype.ext
                        have hclip : (Set.projIcc 0 1 zero_le_one (2 * (a i).val - 1)).val = 2 * (a i).val - 1 := by
                          exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one (by
                            constructor <;> linarith [(a i).property.2]))
                        change (r (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * (a i).val - 1))) i).val = (a i).val
                        dsimp only [r, ContinuousMap.coe_mk]
                        rw [Function.update_self, Function.update_self]
                        change ((Set.projIcc 0 1 zero_le_one (2 * (a i).val - 1)).val + 1) / 2 = (a i).val
                        rw [hclip]
                        ring
                      · simp [r, Function.update_of_ne hji]
                  refine ⟨p, q, (fun _ => rfl), (fun _ => rfl), heq, ?_⟩
                  rw [heq]
                  exact (HomotopyGroup.mul_spec (i := i) (p := q) (q := p)).symm
                have hmiddle (a : Fin (k + 2) → unitInterval) (ha : (a i).val = 1 / 2) : m a = x := by
                  rw [hml a (le_of_eq ha), hp a (le_of_eq ha.symm)]
                obtain ⟨P, R, hP, hR, heqm, hprod⟩ := split_loop k x m i hmiddle
                have hleft (a : Fin (k + 2) → unitInterval) : P a = p (Function.update a i
                    ⟨(a i).val / 2, by constructor <;> linarith [(a i).property.1, (a i).property.2]⟩) := by
                  rw [hP]
                  apply hml
                  simp only [Function.update_self]
                  linarith [(a i).property.2]
                have hright (a : Fin (k + 2) → unitInterval) : R a = r (Function.update a i
                    ⟨((a i).val + 1) / 2, by constructor <;> linarith [(a i).property.1, (a i).property.2]⟩) := by
                  rw [hR]
                  apply hmr
                  simp only [Function.update_self]
                  linarith [(a i).property.1]
                let l (z : unitInterval × (Fin (k + 2) → unitInterval)) : Fin (k + 2) → unitInterval :=
                  Function.update z.2 i ⟨(1 - z.1.val / 2) * (z.2 i).val, by
                    constructor <;> nlinarith [z.1.property.1, z.1.property.2, (z.2 i).property.1, (z.2 i).property.2]⟩
                have hl : Continuous l := by
                  apply continuous_id.snd.update
                  exact (((continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)).mul
                    (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))).subtype_mk _)
                have hpP : GenLoop.Homotopic p P := by
                  refine ⟨{
                    toHomotopy := {
                      toContinuousMap := p.val.comp ⟨l, hl⟩
                      map_zero_left := ?_
                      map_one_left := ?_ }
                    prop' := ?_ }⟩
                  · intro a
                    change p (l (0, a)) = p a
                    have heq : l (0, a) = a := by
                      funext j
                      by_cases hji : j = i
                      · subst j
                        apply Subtype.ext
                        simp [l]
                      · simp [l, Function.update_of_ne hji]
                    rw [heq]
                  · intro a
                    change p (l (1, a)) = P a
                    rw [hleft]
                    congr 1
                    apply congrArg (Function.update a i)
                    apply Subtype.ext
                    dsimp [l]
                    ring
                  · intro t a ha
                    change p (l (t, a)) = p a
                    rw [GenLoop.boundary p a ha]
                    obtain ⟨j, hj⟩ := ha
                    by_cases hji : j = i
                    · subst j
                      rcases hj with hj | hj
                      · apply GenLoop.boundary p
                        refine ⟨i, Or.inl ?_⟩
                        apply Subtype.ext
                        simp [l, hj]
                      · apply hp
                        simp only [l, Function.update_self]
                        rw [hj]
                        change 1 / 2 ≤ (1 - t.val / 2) * 1
                        linarith [t.property.2]
                    · apply GenLoop.boundary p
                      exact ⟨j, by simpa [l, Function.update_of_ne hji] using hj⟩
                let rr (z : unitInterval × (Fin (k + 2) → unitInterval)) : Fin (k + 2) → unitInterval :=
                  Function.update z.2 i ⟨(1 - z.1.val / 2) * (z.2 i).val + z.1.val / 2, by
                    constructor <;> nlinarith [z.1.property.1, z.1.property.2, (z.2 i).property.1, (z.2 i).property.2]⟩
                have hrr : Continuous rr := by
                  apply continuous_id.snd.update
                  exact ((((continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)).mul
                    (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))).add
                      ((continuous_subtype_val.comp continuous_fst).div_const 2)).subtype_mk _)
                have hrR : GenLoop.Homotopic r R := by
                  refine ⟨{
                    toHomotopy := {
                      toContinuousMap := r.val.comp ⟨rr, hrr⟩
                      map_zero_left := ?_
                      map_one_left := ?_ }
                    prop' := ?_ }⟩
                  · intro a
                    change r (rr (0, a)) = r a
                    have heq : rr (0, a) = a := by
                      funext j
                      by_cases hji : j = i
                      · subst j
                        apply Subtype.ext
                        simp [rr]
                      · simp [rr, Function.update_of_ne hji]
                    rw [heq]
                  · intro a
                    change r (rr (1, a)) = R a
                    rw [hright]
                    congr 1
                    apply congrArg (Function.update a i)
                    apply Subtype.ext
                    dsimp [rr]
                    ring
                  · intro t a ha
                    change r (rr (t, a)) = r a
                    rw [GenLoop.boundary r a ha]
                    obtain ⟨j, hj⟩ := ha
                    by_cases hji : j = i
                    · subst j
                      rcases hj with hj | hj
                      · apply hr
                        simp only [rr, Function.update_self]
                        rw [hj]
                        change (1 - t.val / 2) * 0 + t.val / 2 ≤ 1 / 2
                        linarith [t.property.2]
                      · apply GenLoop.boundary r
                        refine ⟨i, Or.inr ?_⟩
                        apply Subtype.ext
                        simp [rr, hj]
                    · apply GenLoop.boundary r
                      exact ⟨j, by simpa [rr, Function.update_of_ne hji] using hj⟩
                apply @Quotient.exact (GenLoop (Fin (k + 2)) X x)
                  (GenLoop.Homotopic.setoid (Fin (k + 2)) x) m (GenLoop.transAt i r p)
                rw [hprod, ← HomotopyGroup.mul_spec (i := i)]
                have hpclass : (⟦P⟧ : HomotopyGroup.Pi (k + 2) X x) = ⟦p⟧ := Quotient.sound hpP.symm
                have hrclass : (⟦R⟧ : HomotopyGroup.Pi (k + 2) X x) = ⟦r⟧ := Quotient.sound hrR.symm
                rw [hpclass, hrclass]
                exact @mul_comm (HomotopyGroup.Pi (k + 2) X x) inferInstance ⟦r⟧ ⟦p⟧
            have precompose {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
            (i : Fin (k + 2)) (f : GenLoop (Fin (k + 2)) X x)
            (h : C(unitInterval, unitInterval)) (h₀ : h 0 = 0) (h₁ : h 1 = 1) :
            ∃ q : GenLoop (Fin (k + 2)) X x,
              (∀ a, q a = f (Function.update a i (h (a i)))) ∧ GenLoop.Homotopic f q := by
              audit_proof
                let r (z : unitInterval × (Fin (k + 2) → unitInterval)) : Fin (k + 2) → unitInterval :=
                  Function.update z.2 i ⟨(1 - z.1.val) * (z.2 i).val + z.1.val * (h (z.2 i)).val, by
                    constructor <;> nlinarith [z.1.property.1, z.1.property.2,
                      (z.2 i).property.1, (z.2 i).property.2, (h (z.2 i)).property.1, (h (z.2 i)).property.2]⟩
                have hr : Continuous r := by
                  apply continuous_snd.update
                  exact ((((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
                    (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))).add
                      ((continuous_subtype_val.comp continuous_fst).mul
                        (continuous_subtype_val.comp (h.continuous.comp ((continuous_apply i).comp continuous_snd))))).subtype_mk _)
                have hb (t : unitInterval) (a : Fin (k + 2) → unitInterval)
                    (ha : a ∈ Cube.boundary (Fin (k + 2))) : r (t, a) ∈ Cube.boundary (Fin (k + 2)) := by
                  obtain ⟨j, hj⟩ := ha
                  by_cases hji : j = i
                  · subst j
                    rcases hj with hj | hj
                    · refine ⟨i, Or.inl ?_⟩
                      apply Subtype.ext
                      simp [r, hj, h₀]
                    · refine ⟨i, Or.inr ?_⟩
                      apply Subtype.ext
                      simp [r, hj, h₁]
                  · exact ⟨j, by simpa [r, Function.update_of_ne hji] using hj⟩
                let q : GenLoop (Fin (k + 2)) X x :=
                  ⟨f.val.comp ⟨fun a => r (1, a), hr.comp (continuous_const.prodMk continuous_id)⟩,
                    fun a ha => GenLoop.boundary f _ (hb 1 a ha)⟩
                have hone (a : Fin (k + 2) → unitInterval) : r (1, a) = Function.update a i (h (a i)) := by
                  apply congrArg (Function.update a i)
                  apply Subtype.ext
                  simp
                refine ⟨q, ?_, ?_⟩
                · intro a
                  change f (r (1, a)) = _
                  rw [hone]
                · refine ⟨{
                    toHomotopy := {
                      toContinuousMap := f.val.comp ⟨r, hr⟩
                      map_zero_left := ?_
                      map_one_left := fun _ => rfl }
                    prop' := ?_ }⟩
                  · intro a
                    change f (r (0, a)) = f a
                    have hz : r (0, a) = a := by
                      funext j
                      by_cases hji : j = i
                      · subst j
                        apply Subtype.ext
                        simp [r]
                      · simp [r, Function.update_of_ne hji]
                    rw [hz]
                  · intro t a ha
                    change f (r (t, a)) = f a
                    exact (GenLoop.boundary f _ (hb t a ha)).trans (GenLoop.boundary f a ha).symm
            let w (t : unitInterval) : ℝ :=
              2 * cut * min t.val (1 / 2) + 2 * (1 - cut) * max (t.val - 1 / 2) 0
            have hw (t : unitInterval) : w t ∈ Set.Icc (0 : ℝ) 1 := by
              dsimp [w]
              by_cases ht : t.val ≤ 1 / 2
              · rw [min_eq_left ht, max_eq_right (sub_nonpos.mpr ht)]
                constructor <;> nlinarith [t.property.1, t.property.2]
              · have ht' : 1 / 2 ≤ t.val := le_of_lt (lt_of_not_ge ht)
                rw [min_eq_right ht', max_eq_left (sub_nonneg.mpr ht')]
                constructor <;> nlinarith [t.property.1, t.property.2]
            let h : C(unitInterval, unitInterval) := ⟨fun t => ⟨w t, hw t⟩,
              (((continuous_const.mul (continuous_subtype_val.min continuous_const)).add
                (continuous_const.mul ((continuous_subtype_val.sub continuous_const).max continuous_const))).subtype_mk hw)⟩
            have hh₀ : h 0 = 0 := by apply Subtype.ext; norm_num [h, w]
            have hh₁ : h 1 = 1 := by apply Subtype.ext; norm_num [h, w]; ring
            have hleft (t : unitInterval) (ht : t.val ≤ 1 / 2) : (h t).val ≤ cut := by
              change w t ≤ cut
              dsimp [w]
              rw [min_eq_left ht, max_eq_right (sub_nonpos.mpr ht)]
              nlinarith [t.property.1]
            have hright (t : unitInterval) (ht : 1 / 2 ≤ t.val) : cut ≤ (h t).val := by
              change cut ≤ w t
              dsimp [w]
              rw [min_eq_right ht, max_eq_left (sub_nonneg.mpr ht)]
              nlinarith
            obtain ⟨P, hP, hpP⟩ := precompose k x i p h hh₀ hh₁
            obtain ⟨R, hR, hrR⟩ := precompose k x i r h hh₀ hh₁
            obtain ⟨M, hM, hmM⟩ := precompose k x i m h hh₀ hh₁
            have hmid : GenLoop.Homotopic M (GenLoop.transAt i R P) :=
              midpoint_cut k x i P R M (by
                intro a ha
                rw [hP]
                apply hp
                simpa only [Function.update_self] using hright (a i) ha) (by
                intro a ha
                rw [hR]
                apply hr
                simpa only [Function.update_self] using hleft (a i) ha) (by
                intro a ha
                rw [hM, hP]
                apply hml
                simpa only [Function.update_self] using hleft (a i) ha) (by
                intro a ha
                rw [hM, hR]
                apply hmr
                simpa only [Function.update_self] using hright (a i) ha)
            apply @Quotient.exact (GenLoop (Fin (k + 2)) X x)
              (GenLoop.Homotopic.setoid (Fin (k + 2)) x) m (GenLoop.transAt i r p)
            have hpclass : (⟦P⟧ : HomotopyGroup.Pi (k + 2) X x) = ⟦p⟧ := Quotient.sound hpP.symm
            have hrclass : (⟦R⟧ : HomotopyGroup.Pi (k + 2) X x) = ⟦r⟧ := Quotient.sound hrR.symm
            have hmclass : (⟦m⟧ : HomotopyGroup.Pi (k + 2) X x) = ⟦M⟧ := Quotient.sound hmM
            have hmidclass : (⟦M⟧ : HomotopyGroup.Pi (k + 2) X x) = ⟦GenLoop.transAt i R P⟧ := Quotient.sound hmid
            rw [hmclass, hmidclass, ← HomotopyGroup.mul_spec (i := i),
              ← HomotopyGroup.mul_spec (i := i), hpclass, hrclass]
        obtain ⟨β, hβside, hβbd, hlocalP⟩ := localize_half k x e he p hp
        obtain ⟨e', he', hs₀, hs₁, hst⟩ := swap_chart k e he
        have hr' (a : Fin (k + 2) → unitInterval) (ha : (e' a).weights 0 ≤ (e' a).weights 1) : r a = x := by
          rw [hs₀, hs₁] at ha
          exact hr a ha
        obtain ⟨γ, hγside', hγbd, hlocalR⟩ := localize_half k x e' he' r hr'
        have hγside : (e γ).weights 0 < (e γ).weights 1 := by
          rwa [hs₁, hs₀] at hγside'
        have hβγ : β ≠ γ := by
          intro heq
          rw [heq] at hβside
          linarith
        obtain ⟨i, hβγi⟩ : ∃ i : Fin (k + 2), β i ≠ γ i := by
          by_contra hh
          push Not at hh
          exact hβγ (funext hh)
        have hint (a : Fin (k + 2) → unitInterval) (ha : a ∉ Cube.boundary (Fin (k + 2))) :
            0 < (a i).val ∧ (a i).val < 1 := by
          constructor
          · by_contra hh
            have hz : a i = 0 := Subtype.ext (le_antisymm (le_of_not_gt hh) (a i).property.1)
            exact ha ⟨i, Or.inl hz⟩
          · by_contra hh
            have ho : a i = 1 := Subtype.ext (le_antisymm (a i).property.2 (le_of_not_gt hh))
            exact ha ⟨i, Or.inr ho⟩
        have hβi := hint β hβbd
        have hγi := hint γ hγbd
        have hneq : (β i).val ≠ (γ i).val := by
          intro hh
          exact hβγi (Subtype.ext hh)
        let cut : ℝ := ((β i).val + (γ i).val) / 2
        have hcut₀ : 0 < cut := by dsimp [cut]; linarith [hβi.1, hγi.1]
        have hcut₁ : cut < 1 := by dsimp [cut]; linarith [hβi.2, hγi.2]
        let U : Set (Fin (k + 2) → unitInterval) :=
          if (β i).val < (γ i).val then {a | (a i).val < cut} else {a | cut < (a i).val}
        let V : Set (Fin (k + 2) → unitInterval) :=
          if (β i).val < (γ i).val then {a | cut < (a i).val} else {a | (a i).val < cut}
        have hU : IsOpen U := by
          dsimp [U]
          split_ifs
          · exact isOpen_lt (continuous_subtype_val.comp (continuous_apply i)) continuous_const
          · exact isOpen_lt continuous_const (continuous_subtype_val.comp (continuous_apply i))
        have hV : IsOpen V := by
          dsimp [V]
          split_ifs
          · exact isOpen_lt continuous_const (continuous_subtype_val.comp (continuous_apply i))
          · exact isOpen_lt (continuous_subtype_val.comp (continuous_apply i)) continuous_const
        have hUβ : β ∈ U := by
          dsimp [U]
          split_ifs with ho
          · change (β i).val < cut
            dsimp [cut]
            linarith
          · change cut < (β i).val
            dsimp [cut]
            have hrorder : (γ i).val < (β i).val := lt_of_le_of_ne (le_of_not_gt ho) (Ne.symm hneq)
            linarith
        have hVγ : γ ∈ V := by
          dsimp [V]
          split_ifs with ho
          · change cut < (γ i).val
            dsimp [cut]
            linarith
          · change (γ i).val < cut
            dsimp [cut]
            have hrorder : (γ i).val < (β i).val := lt_of_le_of_ne (le_of_not_gt ho) (Ne.symm hneq)
            linarith
        obtain ⟨P, hpP, hPout, hPhalf, ⟨Kp, hKp⟩⟩ := hlocalP U hU hUβ
        obtain ⟨R, hrR, hRout, hRhalf', ⟨Kr, hKr'⟩⟩ := hlocalR V hV hVγ
        have hRhalf (a : Fin (k + 2) → unitInterval) (ha : (e a).weights 1 ≤ (e a).weights 0) : R a = x := by
          apply hRhalf'
          rwa [hs₀, hs₁]
        have hKr (t : unitInterval) (a : Fin (k + 2) → unitInterval)
            (ha : (e a).weights 1 ≤ (e a).weights 0) : Kr (t, a) = x := by
          apply hKr'
          rwa [hs₀, hs₁]
        let L : Set (Fin (k + 2) → unitInterval) := {a | (e a).weights 1 ≤ (e a).weights 0}
        let Q : Set (Fin (k + 2) → unitInterval) := {a | (e a).weights 0 ≤ (e a).weights 1}
        let GL : C(unitInterval × L, X) := Kp.toContinuousMap.comp
          ⟨fun z => (z.1, z.2.val), continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩
        let GR : C(unitInterval × Q, X) := Kr.toContinuousMap.comp
          ⟨fun z => (z.1, z.2.val), continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩
        obtain ⟨G, hGL, hGR⟩ := glue L Q
          (isClosed_le ((StdSimplex.continuous_weights_apply ℝ 1).comp e.continuous)
            ((StdSimplex.continuous_weights_apply ℝ 0).comp e.continuous))
          (isClosed_le ((StdSimplex.continuous_weights_apply ℝ 0).comp e.continuous)
            ((StdSimplex.continuous_weights_apply ℝ 1).comp e.continuous))
          (fun a => le_total ((e a).weights 1) ((e a).weights 0)) GL GR (by
            intro t a hl hq
            change Kp (t, a) = Kr (t, a)
            rw [hKp t a hq, hKr t a hl])
        have hGzero (a : Fin (k + 2) → unitInterval) : G (0, a) = m a := by
          rcases le_total ((e a).weights 1) ((e a).weights 0) with hl | hq
          · rw [hGL 0 a hl]
            change Kp (0, a) = m a
            rw [Kp.apply_zero]
            exact (hml a hl).symm
          · rw [hGR 0 a hq]
            change Kr (0, a) = m a
            rw [Kr.apply_zero]
            exact (hmr a hq).symm
        have hGb (t : unitInterval) (a : Fin (k + 2) → unitInterval)
            (ha : a ∈ Cube.boundary (Fin (k + 2))) : G (t, a) = x := by
          rcases le_total ((e a).weights 1) ((e a).weights 0) with hl | hq
          · rw [hGL t a hl]
            change Kp (t, a) = x
            rw [Kp.eq_fst t ha]
            exact GenLoop.boundary p a ha
          · rw [hGR t a hq]
            change Kr (t, a) = x
            rw [Kr.eq_fst t ha]
            exact GenLoop.boundary r a ha
        let M : GenLoop (Fin (k + 2)) X x :=
          ⟨G.comp ⟨fun a => (1, a), continuous_const.prodMk continuous_id⟩, fun a ha => hGb 1 a ha⟩
        have hmM : GenLoop.Homotopic m M := by
          refine ⟨{
            toHomotopy := {
              toContinuousMap := G
              map_zero_left := hGzero
              map_one_left := fun _ => rfl }
            prop' := ?_ }⟩
          intro t a ha
          change G (t, a) = m a
          rw [hGb t a ha, GenLoop.boundary m a ha]
        have hMleft (a : Fin (k + 2) → unitInterval) (ha : (e a).weights 1 ≤ (e a).weights 0) : M a = P a := by
          change G (1, a) = P a
          rw [hGL 1 a ha]
          exact Kp.apply_one a
        have hMright (a : Fin (k + 2) → unitInterval) (ha : (e a).weights 0 ≤ (e a).weights 1) : M a = R a := by
          change G (1, a) = R a
          rw [hGR 1 a ha]
          exact Kr.apply_one a
        have hMeqP (a : Fin (k + 2) → unitInterval) (hz : R a = x) : M a = P a := by
          rcases le_total ((e a).weights 1) ((e a).weights 0) with hl | hq
          · exact hMleft a hl
          · rw [hMright a hq, hz, hPhalf a hq]
        have hMeqR (a : Fin (k + 2) → unitInterval) (hz : P a = x) : M a = R a := by
          rcases le_total ((e a).weights 1) ((e a).weights 0) with hl | hq
          · rw [hMleft a hl, hz, hRhalf a hl]
          · exact hMright a hq
        have hclass : (⟦M⟧ : HomotopyGroup.Pi (k + 2) X x) =
            ((· * ·) : HomotopyGroup.Pi (k + 2) X x → _ → _) ⟦P⟧ ⟦R⟧ := by
          by_cases ho : (β i).val < (γ i).val
          · have hPl (a : Fin (k + 2) → unitInterval) (ha : cut ≤ (a i).val) : P a = x := by
              apply hPout
              simpa only [U, ite_eq_left ho, Set.mem_ofPred_eq, not_lt] using ha
            have hRr (a : Fin (k + 2) → unitInterval) (ha : (a i).val ≤ cut) : R a = x := by
              apply hRout
              simpa only [V, ite_eq_left ho, Set.mem_ofPred_eq, not_lt] using ha
            have hH := axis_cut k x i cut hcut₀ hcut₁ P R M hPl hRr
              (fun a ha => hMeqP a (hRr a ha)) (fun a ha => hMeqR a (hPl a ha))
            exact (Quotient.sound hH).trans (HomotopyGroup.mul_spec (i := i)).symm
          · have hPr (a : Fin (k + 2) → unitInterval) (ha : (a i).val ≤ cut) : P a = x := by
              apply hPout
              simpa only [U, ite_eq_right ho, Set.mem_ofPred_eq, not_lt] using ha
            have hRl (a : Fin (k + 2) → unitInterval) (ha : cut ≤ (a i).val) : R a = x := by
              apply hRout
              simpa only [V, ite_eq_right ho, Set.mem_ofPred_eq, not_lt] using ha
            have hH := axis_cut k x i cut hcut₀ hcut₁ R P M hRl hPr
              (fun a ha => hMeqR a (hPr a ha)) (fun a ha => hMeqP a (hRl a ha))
            have hh : (⟦M⟧ : HomotopyGroup.Pi (k + 2) X x) =
                ((· * ·) : HomotopyGroup.Pi (k + 2) X x → _ → _) ⟦R⟧ ⟦P⟧ :=
              (Quotient.sound hH).trans (HomotopyGroup.mul_spec (i := i)).symm
            exact hh.trans (@mul_comm (HomotopyGroup.Pi (k + 2) X x) inferInstance ⟦R⟧ ⟦P⟧)
        apply @Quotient.exact (GenLoop (Fin (k + 2)) X x)
          (GenLoop.Homotopic.setoid (Fin (k + 2)) x) m (GenLoop.transAt (0 : Fin (k + 2)) r p)
        have hmclass : (⟦m⟧ : HomotopyGroup.Pi (k + 2) X x) = ⟦M⟧ := Quotient.sound hmM
        have hpclass : (⟦P⟧ : HomotopyGroup.Pi (k + 2) X x) = ⟦p⟧ := Quotient.sound hpP.symm
        have hrclass : (⟦R⟧ : HomotopyGroup.Pi (k + 2) X x) = ⟦r⟧ := Quotient.sound hrR.symm
        rw [hmclass, hclass, hpclass, hrclass]
        exact HomotopyGroup.mul_spec (i := (0 : Fin (k + 2)))
    have split_packet {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (e : (Fin (n + 1) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (n + 2)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (n + 1)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (smap : C(StdSimplex ℝ (Fin (n + 3)), X))
    (hlow : ∀ t (i j : Fin (n + 3)), i ≠ j → t.weights i = 0 → t.weights j = 0 → smap t = x)
    (q : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (n + 3))))
    (hq₀ : ∀ u, (q u).weights 0 = max (u.weights 1 - u.weights 0) 0)
    (hq₁ : ∀ u, (q u).weights 1 = max (u.weights 0 - u.weights 1) 0)
    (hq₂ : ∀ u, (q u).weights 2 = 2 * min (u.weights 0) (u.weights 1))
    (hqt : ∀ u (j : Fin n), (q u).weights j.succ.succ.succ = u.weights j.succ.succ)
    (f₀ f₁ m : GenLoop (Fin (n + 1)) X x)
    (hf₀ : ∀ a, f₀ a = smap ((e a).map (SimplexCategory.δ (0 : Fin (n + 3)))))
    (hf₁ : ∀ a, f₁ a = smap ((e a).map (SimplexCategory.δ (1 : Fin (n + 3)))))
    (hm : ∀ a, m a = smap (q (e a))) :
    ∃ (R T : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (n + 2))))
      (ρ : C((Fin (n + 1) → unitInterval), Fin (n + 1) → unitInterval))
      (p₀ p₁ r s : GenLoop (Fin (n + 1)) X x),
      (∀ u, (R u).weights 0 = max (u.weights 0 - u.weights 1) 0) ∧
      (∀ u, (R u).weights 1 = u.weights 0 + u.weights 1 - max (u.weights 0 - u.weights 1) 0) ∧
      (∀ u (j : Fin n), (R u).weights j.succ.succ = u.weights j.succ.succ) ∧
      (∀ u, (T u).weights 0 = u.weights 1) ∧
      (∀ u, (T u).weights 1 = u.weights 0) ∧
      (∀ u (j : Fin n), (T u).weights j.succ.succ = u.weights j.succ.succ) ∧
      (∀ a, ρ a = e.symm (T (e a))) ∧
      (∀ a, p₁ a = smap ((R (e a)).map (SimplexCategory.δ (1 : Fin (n + 3))))) ∧
      (∀ a, ρ (ρ a) = a) ∧
      (∀ a, a ∈ Cube.boundary (Fin (n + 1)) → ρ a ∈ Cube.boundary (Fin (n + 1))) ∧
      GenLoop.Homotopic f₀ p₀ ∧ GenLoop.Homotopic f₁ p₁ ∧
      (∀ a, r a = p₁ (ρ a)) ∧
      (∀ a, s a = f₁ (ρ a)) ∧ GenLoop.Homotopic s r ∧
      (∀ a, (e a).weights 1 ≤ (e a).weights 0 → m a = p₀ a) ∧
      (∀ a, (e a).weights 0 ≤ (e a).weights 1 → m a = r a) ∧
      (∀ a, (e a).weights 0 ≤ (e a).weights 1 → p₀ a = x) ∧
      (∀ a, (e a).weights 1 ≤ (e a).weights 0 → r a = x) ∧
      (∀ a, (e a).weights 0 = (e a).weights 1 → m a = x) := by
      audit_proof
        classical
        have zero_preserving {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
        (e : (Fin n → unitInterval) ≃ₜ StdSimplex ℝ (Fin (n + 1)))
        (he : ∀ a, a ∈ Cube.boundary (Fin n) ↔ ¬ ∀ i, 0 < (e a).weights i)
        (g : C(StdSimplex ℝ (Fin (n + 1)), X))
        (hg : ∀ u, (¬ ∀ i, 0 < u.weights i) → g u = x)
        (R : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 1))))
        (hR : ∀ u i, u.weights i = 0 → (R u).weights i = 0)
        (p q : GenLoop (Fin n) X x)
        (hp : ∀ a, p a = g (e a)) (hq : ∀ a, q a = g (R (e a))) :
        GenLoop.Homotopic p q := by
          classical
          let r : unitInterval × (Fin n → unitInterval) → StdSimplex ℝ (Fin (n + 1)) :=
            fun z => convexCombPair (R := ℝ) (1 - z.1.val) z.1.val
              (sub_nonneg.mpr z.1.property.2) z.1.property.1 (by ring) (e z.2) (R (e z.2))
          have hr : Continuous r := by
            apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff.mpr
            apply continuous_pi
            intro i
            change Continuous (fun z : unitInterval × (Fin n → unitInterval) => (r z).weights i)
            simp only [r, StdSimplex.weights_convexCombPair, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
            exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
              ((StdSimplex.continuous_weights_apply ℝ i).comp (e.continuous.comp continuous_snd))).add
              ((continuous_subtype_val.comp continuous_fst).mul
                ((StdSimplex.continuous_weights_apply ℝ i).comp (R.continuous.comp (e.continuous.comp continuous_snd))))
          refine ⟨{
            toHomotopy := {
              toContinuousMap := g.comp ⟨r, hr⟩
              map_zero_left := ?_
              map_one_left := ?_ }
            prop' := ?_ }⟩
          · intro a
            change g (r (0, a)) = p a
            have hz : r (0, a) = e a := by
              apply StdSimplex.ext
              ext i
              simp [r]
            rw [hz, hp]
          · intro a
            change g (r (1, a)) = q a
            have ho : r (1, a) = R (e a) := by
              apply StdSimplex.ext
              ext i
              simp [r]
            rw [ho, hq]
          · intro t a ha
            change g (r (t, a)) = p a
            rw [GenLoop.boundary p a ha]
            apply hg
            obtain ⟨i, hi⟩ := not_forall.mp ((he a).mp ha)
            have hz : (e a).weights i = 0 := le_antisymm (le_of_not_gt hi) (StdSimplex.weights_nonneg _)
            intro h
            have hpos := h i
            change 0 < (convexCombPair (R := ℝ) (1 - t.val) t.val _ _ _ (e a) (R (e a))).weights i at hpos
            rw [StdSimplex.weights_convexCombPair] at hpos
            simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hz, hR _ _ hz, mul_zero, add_zero] at hpos
            exact lt_irrefl _ hpos
        have geometry :
            ∃ R T : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (n + 2))),
              (∀ u i, u.weights i = 0 → (R u).weights i = 0) ∧
              (∀ u, (R u).weights 0 = max (u.weights 0 - u.weights 1) 0) ∧
              (∀ u, (R u).weights 1 = u.weights 0 + u.weights 1 - max (u.weights 0 - u.weights 1) 0) ∧
              (∀ u (j : Fin n), (R u).weights j.succ.succ = u.weights j.succ.succ) ∧
              (∀ u, (T u).weights 0 = u.weights 1) ∧
              (∀ u, (T u).weights 1 = u.weights 0) ∧
              (∀ u (j : Fin n), (T u).weights j.succ.succ = u.weights j.succ.succ) ∧
              (∀ u, T (T u) = u) ∧
              (∀ u, u.weights 1 ≤ u.weights 0 → q u = (R u).map (SimplexCategory.δ (0 : Fin (n + 3)))) ∧
              (∀ u, u.weights 0 ≤ u.weights 1 → q u = (R (T u)).map (SimplexCategory.δ (1 : Fin (n + 3)))) ∧
              (∀ u, u.weights 0 ≤ u.weights 1 → smap ((R u).map (SimplexCategory.δ (0 : Fin (n + 3)))) = x) ∧
              (∀ u, u.weights 1 ≤ u.weights 0 → smap ((R (T u)).map (SimplexCategory.δ (1 : Fin (n + 3)))) = x) ∧
              (∀ u, u.weights 0 = u.weights 1 → smap (q u) = x) := by
          audit_proof
           classical
           obtain ⟨R, hR₀, hR₁, hRt, hRzero⟩ := FiniteSingularCarrier.simplex_facet_fold n
           let τ : Equiv.Perm (Fin (n + 2)) := Equiv.swap 0 1
           let T : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (n + 2))) :=
             ⟨StdSimplex.map τ, by fun_prop⟩
           have hT (u : StdSimplex ℝ (Fin (n + 2))) (i : Fin (n + 2)) :
               (T u).weights (τ i) = u.weights i := by
             change (u.map τ).weights (τ i) = u.weights i
             rw [StdSimplex.weights_map]
             exact Finsupp.mapDomain_apply_of_injective τ.injective _ _
           have hT₀ (u : StdSimplex ℝ (Fin (n + 2))) : (T u).weights 0 = u.weights 1 := by
             simpa [τ] using hT u 1
           have hT₁ (u : StdSimplex ℝ (Fin (n + 2))) : (T u).weights 1 = u.weights 0 := by
             simpa [τ] using hT u 0
           have hTt (u : StdSimplex ℝ (Fin (n + 2))) (j : Fin n) :
               (T u).weights j.succ.succ = u.weights j.succ.succ := by
             simpa [τ, Equiv.swap_apply_of_ne_of_ne (by apply Fin.ne_of_val_ne; simp : j.succ.succ ≠ (0 : Fin (n + 2)))
               (by apply Fin.ne_of_val_ne; simp : j.succ.succ ≠ (1 : Fin (n + 2)))] using hT u j.succ.succ
           have hmap (i : Fin (n + 3)) (v : StdSimplex ℝ (Fin (n + 2))) (j : Fin (n + 2)) :
               (v.map (SimplexCategory.δ i)).weights (i.succAbove j) = v.weights j := by
             rw [StdSimplex.weights_map]
             exact Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective _ _
           have hmiss (i : Fin (n + 3)) (v : StdSimplex ℝ (Fin (n + 2))) :
               (v.map (SimplexCategory.δ i)).weights i = 0 := by
             rw [StdSimplex.weights_map]
             exact Finsupp.mapDomain_of_notMem_range _ _ (by
               rintro ⟨j, hj⟩
               exact Fin.succAbove_ne i j hj)
           have hs : (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) := by apply Fin.ext; rfl
           have hs₁ : (0 : Fin (n + 2)).succ = (1 : Fin (n + 3)) := by apply Fin.ext; rfl
           have hs₂ : (0 : Fin (n + 1)).succ.succ = (2 : Fin (n + 3)) := by apply Fin.ext; rfl
           have hδ₀ (j : Fin (n + 2)) : (0 : Fin (n + 3)).succAbove j = j.succ := by simp
           have hδ₁₀ : (1 : Fin (n + 3)).succAbove 0 = 0 := by simp
           have hδ₁t (j : Fin (n + 1)) : (1 : Fin (n + 3)).succAbove j.succ = j.succ.succ := by
             apply Fin.succAbove_of_le_castSucc
             change 1 ≤ j.val + 1
             omega
           refine ⟨R, T, hRzero, hR₀, hR₁, hRt, hT₀, hT₁, hTt, ?_, ?_, ?_, ?_, ?_, ?_⟩
           · intro u
             apply StdSimplex.ext
             ext i
             refine Fin.cases ?_ (fun j => ?_) i
             · rw [hT₀, hT₁]
             · refine Fin.cases ?_ (fun j => ?_) j
               · rw [hs, hT₁, hT₀]
               · rw [hTt, hTt]
           · intro u hu
             apply StdSimplex.ext
             ext i
             refine Fin.cases ?_ (fun j => ?_) i
             · rw [hq₀, hmiss, max_eq_right (sub_nonpos.mpr hu)]
             · rw [← hδ₀ j, hmap]
               refine Fin.cases ?_ (fun j => ?_) j
               · rw [hδ₀, hs₁, hq₁, hR₀]
               · refine Fin.cases ?_ (fun j => ?_) j
                 · rw [hδ₀, hs₂, hq₂, hs, hR₁, min_eq_right hu,
                     max_eq_left (sub_nonneg.mpr hu)]
                   ring
                 · rw [hδ₀, hqt, hRt]
           · intro u hu
             apply StdSimplex.ext
             ext i
             refine Fin.cases ?_ (fun j => ?_) i
             · rw [← hδ₁₀, hmap, hδ₁₀, hq₀, hR₀, hT₀, hT₁]
             · refine Fin.cases ?_ (fun j => ?_) j
               · rw [hs₁, hq₁, hmiss, max_eq_right (sub_nonpos.mpr hu)]
               · rw [← hδ₁t j, hmap]
                 refine Fin.cases ?_ (fun j => ?_) j
                 · rw [hδ₁t, hs₂, hq₂, hs, hR₁, hT₀, hT₁, min_eq_left hu,
                     max_eq_left (sub_nonneg.mpr hu)]
                   ring
                 · rw [hδ₁t, hqt, hRt, hTt]
           · intro u hu
             apply hlow _ 0 1 (by apply Fin.ne_of_val_ne; simp) (hmiss 0 _)
             rw [← hs₁, ← hδ₀ 0, hmap, hR₀, max_eq_right (sub_nonpos.mpr hu)]
           · intro u hu
             apply hlow _ 1 0 (by apply Fin.ne_of_val_ne; simp) (hmiss 1 _)
             rw [← hδ₁₀, hmap, hR₀, hT₀, hT₁, max_eq_right (sub_nonpos.mpr hu)]
           · intro u hu
             apply hlow _ 0 1 (by apply Fin.ne_of_val_ne; simp)
             · rw [hq₀, ← hu, sub_self, max_self]
             · rw [hq₁, hu, sub_self, max_self]
        obtain ⟨R, T, hRzero, hR₀, hR₁, hRt, hT₀, hT₁, hTt, hTT, hqleft, hqright, hpleft, hpright, hseam⟩ := geometry
        have hTboundary (u : StdSimplex ℝ (Fin (n + 2)))
            (hu : ¬ ∀ i, 0 < u.weights i) : ¬ ∀ i, 0 < (T u).weights i := by
          obtain ⟨i, hi⟩ := not_forall.mp hu
          intro h
          revert hi
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa [hT₁ u] using h 1
          · refine Fin.cases ?_ (fun j => ?_) j
            · have hs : (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) := by apply Fin.ext; rfl
              simpa [hs, hT₀ u] using h 0
            · simpa [hTt u j] using h j.succ.succ
        let ρ : C((Fin (n + 1) → unitInterval), Fin (n + 1) → unitInterval) :=
          ⟨fun a => e.symm (T (e a)), e.symm.continuous.comp (T.continuous.comp e.continuous)⟩
        have hρboundary (a : Fin (n + 1) → unitInterval)
            (ha : a ∈ Cube.boundary (Fin (n + 1))) : ρ a ∈ Cube.boundary (Fin (n + 1)) := by
          apply (he _).mpr
          change ¬ ∀ i, 0 < (e (e.symm (T (e a)))).weights i
          rw [e.apply_symm_apply]
          exact hTboundary _ ((he a).mp ha)
        let g₀ : C(StdSimplex ℝ (Fin (n + 2)), X) :=
          smap.comp ⟨StdSimplex.map (SimplexCategory.δ (0 : Fin (n + 3))), by fun_prop⟩
        let g₁ : C(StdSimplex ℝ (Fin (n + 2)), X) :=
          smap.comp ⟨StdSimplex.map (SimplexCategory.δ (1 : Fin (n + 3))), by fun_prop⟩
        have hg₀ (u : StdSimplex ℝ (Fin (n + 2))) (hu : ¬ ∀ i, 0 < u.weights i) : g₀ u = x := by
          have ha : e.symm u ∈ Cube.boundary (Fin (n + 1)) := (he _).mpr (by simpa using hu)
          have ht := hf₀ (e.symm u)
          rw [e.apply_symm_apply] at ht
          exact ht.symm.trans (GenLoop.boundary f₀ _ ha)
        have hg₁ (u : StdSimplex ℝ (Fin (n + 2))) (hu : ¬ ∀ i, 0 < u.weights i) : g₁ u = x := by
          have ha : e.symm u ∈ Cube.boundary (Fin (n + 1)) := (he _).mpr (by simpa using hu)
          have ht := hf₁ (e.symm u)
          rw [e.apply_symm_apply] at ht
          exact ht.symm.trans (GenLoop.boundary f₁ _ ha)
        have hRboundary (u : StdSimplex ℝ (Fin (n + 2))) (hu : ¬ ∀ i, 0 < u.weights i) :
            ¬ ∀ i, 0 < (R u).weights i := by
          obtain ⟨i, hi⟩ := not_forall.mp hu
          have hz : u.weights i = 0 := le_antisymm (le_of_not_gt hi) (StdSimplex.weights_nonneg _)
          intro h
          have hh := h i
          rw [hRzero u i hz] at hh
          exact lt_irrefl _ hh
        let p₀ : GenLoop (Fin (n + 1)) X x :=
          ⟨g₀.comp (R.comp ⟨e, e.continuous⟩), fun a ha => hg₀ _ (hRboundary _ ((he a).mp ha))⟩
        let p₁ : GenLoop (Fin (n + 1)) X x :=
          ⟨g₁.comp (R.comp ⟨e, e.continuous⟩), fun a ha => hg₁ _ (hRboundary _ ((he a).mp ha))⟩
        let r : GenLoop (Fin (n + 1)) X x :=
          ⟨p₁.val.comp ρ, fun a ha => GenLoop.boundary p₁ _ (hρboundary a ha)⟩
        let s : GenLoop (Fin (n + 1)) X x :=
          ⟨f₁.val.comp ρ, fun a ha => GenLoop.boundary f₁ _ (hρboundary a ha)⟩
        have hhp₁ : GenLoop.Homotopic f₁ p₁ :=
          zero_preserving
            (n + 1) x e he g₁ hg₁ R hRzero f₁ p₁ hf₁ (fun _ => rfl)
        refine ⟨R, T, ρ, p₀, p₁, r, s, hR₀, hR₁, hRt, hT₀, hT₁, hTt,
          (fun _ => rfl), (fun _ => rfl), ?_, hρboundary, ?_, hhp₁,
          (fun _ => rfl), (fun _ => rfl), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro a
          change e.symm (T (e (e.symm (T (e a))))) = a
          rw [e.apply_symm_apply, hTT, e.symm_apply_apply]
        · exact zero_preserving
            (n + 1) x e he g₀ hg₀ R hRzero f₀ p₀ hf₀ (fun _ => rfl)
        · obtain ⟨H⟩ := hhp₁
          refine ⟨{
            toHomotopy := H.toHomotopy.compContinuousMap ρ
            prop' := ?_ }⟩
          intro t a ha
          change H (t, ρ a) = f₁ (ρ a)
          exact H.eq_fst t (hρboundary a ha)
        · intro a ha
          rw [hm, hqleft _ ha]
          rfl
        · intro a ha
          rw [hm, hqright _ ha]
          change smap ((R (T (e a))).map (SimplexCategory.δ (1 : Fin (n + 3)))) =
            smap ((R (e (e.symm (T (e a))))).map (SimplexCategory.δ (1 : Fin (n + 3))))
          rw [e.apply_symm_apply]
        · exact fun a ha => hpleft (e a) ha
        · intro a ha
          change smap ((R (e (e.symm (T (e a))))).map (SimplexCategory.δ (1 : Fin (n + 3)))) = x
          rw [e.apply_symm_apply]
          exact hpright (e a) ha
        · intro a ha
          rw [hm]
          exact hseam (e a) ha
    have null_packet {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (e : (Fin (n + 1) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (n + 2)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (n + 1)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (g : C(StdSimplex ℝ (Fin (n + 2)), X))
    (hg : ∀ u, (¬ ∀ i, 0 < u.weights i) → g u = x)
    (R T : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (n + 2))))
    (hR₀ : ∀ u, (R u).weights 0 = max (u.weights 0 - u.weights 1) 0)
    (hR₁ : ∀ u, (R u).weights 1 = u.weights 0 + u.weights 1 - max (u.weights 0 - u.weights 1) 0)
    (hRt : ∀ u (j : Fin n), (R u).weights j.succ.succ = u.weights j.succ.succ)
    (hT₀ : ∀ u, (T u).weights 0 = u.weights 1)
    (hT₁ : ∀ u, (T u).weights 1 = u.weights 0)
    (hTt : ∀ u (j : Fin n), (T u).weights j.succ.succ = u.weights j.succ.succ) :
    ∃ v : GenLoop (Fin (n + 1)) X x,
      (∀ a, (e a).weights 1 ≤ (e a).weights 0 → v a = g (R (e a))) ∧
      (∀ a, (e a).weights 0 ≤ (e a).weights 1 → v a = g (R (T (e a)))) ∧
      (∀ a, (e a).weights 0 = (e a).weights 1 → v a = x) ∧
      GenLoop.Homotopic v GenLoop.const := by
      audit_proof
        have cancellation :
            ∃ V : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (n + 2))),
              (∀ u, (V u).weights 0 = |u.weights 0 - u.weights 1|) ∧
              (∀ u, (V u).weights 1 = 2 * min (u.weights 0) (u.weights 1)) ∧
              (∀ u (j : Fin n), (V u).weights j.succ.succ = u.weights j.succ.succ) ∧
              (∀ u, (¬ ∀ i, 0 < u.weights i) → ¬ ∀ i, 0 < (V u).weights i) ∧
              ContinuousMap.HomotopicRel (g.comp V) (ContinuousMap.const _ x)
                {u | ¬ ∀ i, 0 < u.weights i} := by
          audit_proof
            let S := StdSimplex ℝ (Fin (n + 2))
            have hs : (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) := by apply Fin.ext; rfl
            let w (u : S) : Fin (n + 2) → ℝ := Fin.cases
              |u.weights 0 - u.weights 1|
              (Fin.cases (u.weights 0 + u.weights 1 - |u.weights 0 - u.weights 1|)
                (fun j => u.weights j.succ.succ))
            let V (u : S) : S := {
              weights := Finsupp.equivFunOnFinite.symm (w u)
              nonneg := by
                intro i
                change 0 ≤ w u i
                refine Fin.cases (abs_nonneg _) (fun j => ?_) i
                refine Fin.cases ?_ (fun j => StdSimplex.weights_nonneg _) j
                change 0 ≤ u.weights 0 + u.weights 1 - |u.weights 0 - u.weights 1|
                by_cases h : u.weights 1 ≤ u.weights 0
                · rw [abs_of_nonneg (sub_nonneg.mpr h)]
                  linarith [StdSimplex.weights_nonneg (w := u) 1]
                · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt (lt_of_not_ge h)))]
                  linarith [StdSimplex.weights_nonneg (w := u) 0]
              total := by
                rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
                change ∑ i : Fin (n + 2), w u i = 1
                rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
                simp only [w, Fin.cases_zero, Fin.cases_succ]
                have hu := u.total
                rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ, Fin.sum_univ_succ, hs] at hu
                linarith }
            have hV : Continuous V := by
              apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff.mpr
              apply continuous_pi
              intro i
              change Continuous (fun u : S => w u i)
              refine Fin.cases ?_ (fun j => ?_) i
              · exact ((StdSimplex.continuous_weights_apply ℝ 0).sub (StdSimplex.continuous_weights_apply ℝ 1)).abs
              · refine Fin.cases ?_ (fun j => ?_) j
                · exact ((StdSimplex.continuous_weights_apply ℝ 0).add (StdSimplex.continuous_weights_apply ℝ 1)).sub
                    (((StdSimplex.continuous_weights_apply ℝ 0).sub (StdSimplex.continuous_weights_apply ℝ 1)).abs)
                · exact StdSimplex.continuous_weights_apply ℝ j.succ.succ
            have hV₀ (u : S) : (V u).weights 0 = |u.weights 0 - u.weights 1| := rfl
            have hV₁ (u : S) : (V u).weights 1 = 2 * min (u.weights 0) (u.weights 1) := by
              change u.weights 0 + u.weights 1 - |u.weights 0 - u.weights 1| = _
              by_cases h : u.weights 1 ≤ u.weights 0
              · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
                ring
              · have h' := le_of_lt (lt_of_not_ge h)
                rw [min_eq_left h', abs_of_nonpos (sub_nonpos.mpr h')]
                ring
            have hVt (u : S) (j : Fin n) : (V u).weights j.succ.succ = u.weights j.succ.succ := rfl
            have hzero (u : S) (hu : ¬ ∀ i, 0 < u.weights i) :
                ∃ i : Fin (n + 2), i ≠ 0 ∧ (V u).weights i = 0 := by
              obtain ⟨i, hi⟩ := not_forall.mp hu
              have hz : u.weights i = 0 := le_antisymm (le_of_not_gt hi) (StdSimplex.weights_nonneg _)
              revert hz
              refine Fin.cases ?_ (fun j => ?_) i
              · intro hz
                refine ⟨1, by apply Fin.ne_of_val_ne; simp, ?_⟩
                rw [hV₁, hz, min_eq_left (StdSimplex.weights_nonneg _), mul_zero]
              · refine Fin.cases ?_ (fun j => ?_) j
                · intro hz
                  rw [hs] at hz
                  refine ⟨1, by apply Fin.ne_of_val_ne; simp, ?_⟩
                  rw [hV₁, hz, min_eq_right (StdSimplex.weights_nonneg _), mul_zero]
                · intro hz
                  exact ⟨j.succ.succ, by apply Fin.ne_of_val_ne; simp, (hVt u j).trans hz⟩
            let v : S := StdSimplex.single 0
            have hv (i : Fin (n + 2)) (hi : i ≠ 0) : v.weights i = 0 := by
              simp [v, StdSimplex.weights_single, hi]
            let H (z : unitInterval × S) : S :=
              convexCombPair (R := ℝ) (1 - z.1.val) z.1.val
                (sub_nonneg.mpr z.1.property.2) z.1.property.1 (by ring) (V z.2) v
            have hH : Continuous H := by
              apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff.mpr
              apply continuous_pi
              intro i
              change Continuous (fun z : unitInterval × S => (H z).weights i)
              simp only [H, S, StdSimplex.weights_convexCombPair, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
              exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
                ((StdSimplex.continuous_weights_apply ℝ i).comp (hV.comp continuous_snd))).add
                ((continuous_subtype_val.comp continuous_fst).mul continuous_const)
            have hHb (t : unitInterval) (u : S) (hu : ¬ ∀ i, 0 < u.weights i) :
                ¬ ∀ i, 0 < (H (t, u)).weights i := by
              obtain ⟨i, hi, hzi⟩ := hzero u hu
              intro hp
              have hh := hp i
              change 0 < (convexCombPair (R := ℝ) (1 - t.val) t.val _ _ _ (V u) v).weights i at hh
              rw [StdSimplex.weights_convexCombPair] at hh
              simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hzi, hv i hi, mul_zero, add_zero] at hh
              exact lt_irrefl _ hh
            refine ⟨⟨V, hV⟩, hV₀, hV₁, hVt, ?_, ?_⟩
            · intro u hu
              obtain ⟨i, _, hzi⟩ := hzero u hu
              intro hp
              have hh := hp i
              change 0 < (V u).weights i at hh
              rw [hzi] at hh
              exact lt_irrefl _ hh
            · refine ⟨{
                toHomotopy := {
                  toContinuousMap := g.comp ⟨H, hH⟩
                  map_zero_left := ?_
                  map_one_left := ?_ }
                prop' := ?_ }⟩
              · intro u
                change g (H (0, u)) = g (V u)
                have heq : H (0, u) = V u := by
                  apply StdSimplex.ext
                  ext i
                  simp [H]
                rw [heq]
              · intro u
                change g (H (1, u)) = x
                have heq : H (1, u) = v := by
                  apply StdSimplex.ext
                  ext i
                  simp [H]
                rw [heq]
                apply hg
                intro hp
                have hh := hp 1
                rw [hv 1 (by apply Fin.ne_of_val_ne; simp)] at hh
                exact lt_irrefl _ hh
              · intro t u hu
                change g (H (t, u)) = g (V u)
                have hz : g (V u) = x := hg _ (by
                  obtain ⟨i, _, hzi⟩ := hzero u hu
                  intro hp
                  have hh := hp i
                  rw [hzi] at hh
                  exact lt_irrefl _ hh)
                rw [hz]
                exact hg _ (hHb t u hu)
        obtain ⟨V, hV₀, hV₁, hVt, hVboundary, ⟨H⟩⟩ := cancellation
        have hs : (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) := by apply Fin.ext; rfl
        have hleft (u : StdSimplex ℝ (Fin (n + 2))) (hu : u.weights 1 ≤ u.weights 0) : V u = R u := by
          apply StdSimplex.ext
          ext i
          refine Fin.cases ?_ (fun j => ?_) i
          · rw [hV₀, hR₀, abs_of_nonneg (sub_nonneg.mpr hu), max_eq_left (sub_nonneg.mpr hu)]
          · refine Fin.cases ?_ (fun j => ?_) j
            · rw [hs, hV₁, hR₁, min_eq_right hu, max_eq_left (sub_nonneg.mpr hu)]
              ring
            · rw [hVt, hRt]
        have hright (u : StdSimplex ℝ (Fin (n + 2))) (hu : u.weights 0 ≤ u.weights 1) : V u = R (T u) := by
          apply StdSimplex.ext
          ext i
          refine Fin.cases ?_ (fun j => ?_) i
          · rw [hV₀, hR₀, hT₀, hT₁, abs_of_nonpos (sub_nonpos.mpr hu), max_eq_left (sub_nonneg.mpr hu)]
            ring
          · refine Fin.cases ?_ (fun j => ?_) j
            · rw [hs, hV₁, hR₁, hT₀, hT₁, min_eq_left hu, max_eq_left (sub_nonneg.mpr hu)]
              ring
            · rw [hVt, hRt, hTt]
        let v : GenLoop (Fin (n + 1)) X x :=
          ⟨g.comp (V.comp ⟨e, e.continuous⟩), fun a ha => hg _ (hVboundary _ ((he a).mp ha))⟩
        refine ⟨v, ?_, ?_, ?_, ?_⟩
        · intro a ha
          change g (V (e a)) = g (R (e a))
          rw [hleft _ ha]
        · intro a ha
          change g (V (e a)) = g (R (T (e a)))
          rw [hright _ ha]
        · intro a ha
          change g (V (e a)) = x
          apply hg
          intro hp
          have hh := hp 0
          rw [hV₀, ha, sub_self, abs_zero] at hh
          exact lt_irrefl _ hh
        · refine ⟨{
            toHomotopy := H.toHomotopy.compContinuousMap ⟨e, e.continuous⟩
            prop' := ?_ }⟩
          intro t a ha
          change H (t, e a) = g (V (e a))
          exact H.eq_fst t ((he a).mp ha)
    obtain ⟨R, T, ρ, p₀, p₁, r, s, hR₀, hR₁, hRt, hT₀, hT₁, hTt,
      hρ, hp₁eval, _, _, hp₀, hp₁, hrEval, _, _, hmleft, hmright,
      hp₀inactive, hrinactive, _⟩ :=
      split_packet (k + 1) x e he smap hlow q hq₀ hq₁ hq₂ hqt f₀ f₁ m hf₀ hf₁ hm
    let g : C(StdSimplex ℝ (Fin (k + 3)), X) :=
      smap.comp ⟨StdSimplex.map (SimplexCategory.δ (1 : Fin (k + 4))), by fun_prop⟩
    have hg (u : StdSimplex ℝ (Fin (k + 3))) (hu : ¬ ∀ i, 0 < u.weights i) : g u = x := by
      have ha : e.symm u ∈ Cube.boundary (Fin (k + 2)) := (he _).mpr (by simpa using hu)
      have ht := hf₁ (e.symm u)
      rw [e.apply_symm_apply] at ht
      exact ht.symm.trans (GenLoop.boundary f₁ _ ha)
    obtain ⟨v, hvleft, hvright, _, hvnull⟩ := null_packet (k + 1) x e he g hg R T hR₀ hR₁ hRt hT₀ hT₁ hTt
    have hp₁inactive (a : Fin (k + 2) → unitInterval)
        (ha : (e a).weights 0 ≤ (e a).weights 1) : p₁ a = x := by
      rw [hp₁eval]
      apply hg
      intro hpos
      have hh := hpos 0
      rw [hR₀, max_eq_right (sub_nonpos.mpr ha)] at hh
      exact lt_irrefl _ hh
    have hvleft' (a : Fin (k + 2) → unitInterval)
        (ha : (e a).weights 1 ≤ (e a).weights 0) : v a = p₁ a := by
      rw [hvleft a ha, hp₁eval]
      rfl
    have hvright' (a : Fin (k + 2) → unitInterval)
        (ha : (e a).weights 0 ≤ (e a).weights 1) : v a = r a := by
      rw [hvright a ha, hrEval, hp₁eval, hρ, e.apply_symm_apply]
      rfl
    have hcancel := cut_multiplication k x e he p₁ r v hp₁inactive hrinactive hvleft' hvright'
    have hmerged := cut_multiplication k x e he p₀ r m hp₀inactive hrinactive hmleft hmright
    let a : HomotopyGroup.Pi (k + 2) X x := ⟦p₁⟧
    let b : HomotopyGroup.Pi (k + 2) X x := ⟦r⟧
    let c₀ : HomotopyGroup.Pi (k + 2) X x := ⟦f₀⟧
    let c₁ : HomotopyGroup.Pi (k + 2) X x := ⟦f₁⟧
    have hvone : (⟦v⟧ : HomotopyGroup.Pi (k + 2) X x) =
        (1 : HomotopyGroup.Pi (k + 2) X x) :=
      (Quotient.sound hvnull).trans HomotopyGroup.one_def.symm
    have hpair : a * b = 1 := by
      have hmul : a * b = (⟦GenLoop.transAt (0 : Fin (k + 2)) r p₁⟧ : HomotopyGroup.Pi (k + 2) X x) :=
        HomotopyGroup.mul_spec (i := (0 : Fin (k + 2)))
      exact hmul.trans ((Quotient.sound hcancel).symm.trans hvone)
    have hb : b = a⁻¹ := by
      calc
        b = (a⁻¹ * a) * b := by rw [inv_mul_cancel, one_mul]
        _ = a⁻¹ * (a * b) := mul_assoc _ _ _
        _ = a⁻¹ := by rw [hpair, mul_one]
    have hzero : (⟦p₀⟧ : HomotopyGroup.Pi (k + 2) X x) = c₀ := Quotient.sound hp₀.symm
    have hone : a = c₁ := Quotient.sound hp₁.symm
    have hmerge : (⟦m⟧ : HomotopyGroup.Pi (k + 2) X x) =
        ((· * ·) : HomotopyGroup.Pi (k + 2) X x → _ → _) ⟦p₀⟧ b :=
      (Quotient.sound hmerged).trans (HomotopyGroup.mul_spec (i := (0 : Fin (k + 2)))).symm
    change (⟦m⟧ : HomotopyGroup.Pi (k + 2) X x) = c₀ * c₁ ^ (-1 : ℤ)
    rw [zpow_neg_one, hmerge, hzero, hb, hone]
end CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
open CategoryTheory Convexity Topology
open scoped Simplicial
open scoped unitInterval
noncomputable section
set_option linter.unusedSimpArgs false
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
-- Internal construction for the protected full oriented boundary obligation.
private theorem boundaryMergeDeformation (n : ℕ) :
    ∃ H : C(unitInterval × StdSimplex ℝ (Fin (n + 3)), StdSimplex ℝ (Fin (n + 3))),
      (∀ u, H (0, u) = u) ∧
      (∀ t u, (H (t,u)).weights 0 = u.weights 0 + max (t.val * u.weights 2 - u.weights 1) 0) ∧
      (∀ t u, (H (t,u)).weights 1 = max (u.weights 1 - t.val * u.weights 2) 0) ∧
      (∀ t u, (H (t,u)).weights 2 = u.weights 1 + u.weights 2 -
        max (t.val * u.weights 2 - u.weights 1) 0 - max (u.weights 1 - t.val * u.weights 2) 0) ∧
      (∀ t u (j : Fin n), (H (t,u)).weights j.succ.succ.succ = u.weights j.succ.succ.succ) ∧
      (∀ t u, u.weights 0 = 0 → (H (t,u)).weights 0 = 0 ∨ (H (t,u)).weights 1 = 0) ∧
      (∀ t u, u.weights 1 = 0 → (H (t,u)).weights 1 = 0) ∧
      (∀ t u, u.weights 2 = 0 → (H (t,u)).weights 2 = 0) ∧
      (∀ u, u.weights 1 = 0 → (H (1,u)).weights 2 = 0) := by
  audit_proof
    let S := StdSimplex ℝ (Fin (n + 3))
    let w (z : unitInterval × S) : Fin (n + 3) → ℝ := Fin.cases
      (z.2.weights 0 + max (z.1.val * z.2.weights 2 - z.2.weights 1) 0)
      (Fin.cases (max (z.2.weights 1 - z.1.val * z.2.weights 2) 0)
        (Fin.cases (z.2.weights 1 + z.2.weights 2 -
          max (z.1.val * z.2.weights 2 - z.2.weights 1) 0 -
          max (z.2.weights 1 - z.1.val * z.2.weights 2) 0)
          (fun j => z.2.weights j.succ.succ.succ)))
    let H (z : unitInterval × S) : S := {
      weights := Finsupp.equivFunOnFinite.symm (w z)
      nonneg := by
        intro i
        change 0 ≤ w z i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact add_nonneg (z.2.weights_nonneg 0) (le_max_right _ _)
        · refine Fin.cases (le_max_right _ _) (fun j => ?_) j
          refine Fin.cases ?_ (fun j => z.2.weights_nonneg _) j
          change 0 ≤ z.2.weights 1 + z.2.weights 2 -
            max (z.1.val * z.2.weights 2 - z.2.weights 1) 0 -
            max (z.2.weights 1 - z.1.val * z.2.weights 2) 0
          have ht0 := z.1.property.1
          have ht1 := z.1.property.2
          have hb := z.2.weights_nonneg 1
          have hc := z.2.weights_nonneg 2
          by_cases hh : z.2.weights 1 ≤ z.1.val * z.2.weights 2
          · rw [max_eq_left (sub_nonneg.mpr hh), max_eq_right (sub_nonpos.mpr hh)]
            nlinarith
          · have hh' := le_of_lt (lt_of_not_ge hh)
            rw [max_eq_right (sub_nonpos.mpr hh'), max_eq_left (sub_nonneg.mpr hh')]
            nlinarith
      total := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        change ∑ i : Fin (n + 3), w z i = 1
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp only [w, Fin.cases_zero, Fin.cases_succ]
        have hu := z.2.total
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ,
          Fin.sum_univ_succ, Fin.sum_univ_succ] at hu
        change z.2.weights 0 + (z.2.weights 1 + (z.2.weights 2 +
          ∑ j : Fin n, z.2.weights j.succ.succ.succ)) = 1 at hu
        linarith }
    have hH : Continuous H := by
      apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 3))).continuous_iff.mpr
      apply continuous_pi
      intro i
      change Continuous (fun z : unitInterval × S => w z i)
      have ht : Continuous (fun z : unitInterval × S => z.1.val) :=
        continuous_subtype_val.comp continuous_fst
      have hw (j : Fin (n + 3)) : Continuous (fun z : unitInterval × S => z.2.weights j) :=
        (StdSimplex.continuous_weights_apply ℝ j).comp continuous_snd
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (hw 0).add (((ht.mul (hw 2)).sub (hw 1)).max continuous_const)
      · refine Fin.cases ?_ (fun j => ?_) j
        · exact ((hw 1).sub (ht.mul (hw 2))).max continuous_const
        · refine Fin.cases ?_ (fun j => hw _) j
          exact (((hw 1).add (hw 2)).sub
            (((ht.mul (hw 2)).sub (hw 1)).max continuous_const)).sub
            (((hw 1).sub (ht.mul (hw 2))).max continuous_const)
    refine ⟨⟨H,hH⟩, ?_, (fun _ _ => rfl), (fun _ _ => rfl),
      (fun _ _ => rfl), (fun _ _ _ => rfl), ?_, ?_, ?_, ?_⟩
    · intro u
      apply StdSimplex.ext
      apply Finsupp.ext
      intro i
      change w (0,u) i = u.weights i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [w, max_eq_right (neg_nonpos.mpr (u.weights_nonneg 1))]
      · refine Fin.cases ?_ (fun j => ?_) j
        · change max ((u.weights 1) - (0 : unitInterval).val * u.weights 2) 0 = u.weights 1
          simp [max_eq_left (u.weights_nonneg 1)]
        · refine Fin.cases ?_ (fun j => rfl) j
          change u.weights 1 + u.weights 2 - max ((0 : unitInterval).val * u.weights 2 - u.weights 1) 0 -
            max (u.weights 1 - (0 : unitInterval).val * u.weights 2) 0 = u.weights 2
          simp [max_eq_right (neg_nonpos.mpr (u.weights_nonneg 1)),
            max_eq_left (u.weights_nonneg 1)]
    · intro t u hz
      by_cases hh : t.val * u.weights 2 ≤ u.weights 1
      · left
        change u.weights 0 + max (t.val * u.weights 2 - u.weights 1) 0 = 0
        rw [hz,max_eq_right (sub_nonpos.mpr hh),add_zero]
      · right
        change max (u.weights 1 - t.val * u.weights 2) 0 = 0
        exact max_eq_right (sub_nonpos.mpr (le_of_lt (lt_of_not_ge hh)))
    · intro t u hz
      change max (u.weights 1 - t.val * u.weights 2) 0 = 0
      rw [hz]
      exact max_eq_right (by nlinarith [t.property.1, u.weights_nonneg 2])
    · intro t u hz
      change u.weights 1 + u.weights 2 - max (t.val * u.weights 2 - u.weights 1) 0 -
        max (u.weights 1 - t.val * u.weights 2) 0 = 0
      simp [hz, max_eq_right (neg_nonpos.mpr (u.weights_nonneg 1)),
        max_eq_left (u.weights_nonneg 1)]
    · intro u hz
      change u.weights 1 + u.weights 2 - max ((1 : unitInterval).val * u.weights 2 - u.weights 1) 0 -
        max (u.weights 1 - (1 : unitInterval).val * u.weights 2) 0 = 0
      simp [hz, max_eq_left (u.weights_nonneg 2),
        max_eq_right (neg_nonpos.mpr (u.weights_nonneg 2))]

-- The endpoint preserves the exact two-zero condition and really kills face 1.
private theorem oneFaceCollapseWithCarrier {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smap : C(StdSimplex ℝ (Fin (n + 3)), X))
    (hlow : ∀ u (i j : Fin (n + 3)), i ≠ j → u.weights i = 0 →
      u.weights j = 0 → smap u = x) :
    ∃ g : C(StdSimplex ℝ (Fin (n + 3)), X),
      (∀ u (i j : Fin (n + 3)), i ≠ j → u.weights i = 0 →
        u.weights j = 0 → g u = x) ∧
      (∀ u, u.weights 1 = 0 → g u = x) ∧
      (∀ j : Fin (n + 3), 2 ≤ j.val → ContinuousMap.HomotopicRel
        (smap.comp ⟨StdSimplex.map (SimplexCategory.δ j), by fun_prop⟩)
        (g.comp ⟨StdSimplex.map (SimplexCategory.δ j), by fun_prop⟩)
        {u | ¬ ∀ i, 0 < u.weights i}) ∧
      (∀ j : Fin (n + 3), 2 ≤ j.val →
        (∀ u, u.weights j = 0 → smap u = x) →
        ∀ u, u.weights j = 0 → g u = x) ∧
      ∃ q : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (n + 3))),
        (∀ u, (q u).weights 0 = max (u.weights 1 - u.weights 0) 0) ∧
        (∀ u, (q u).weights 1 = max (u.weights 0 - u.weights 1) 0) ∧
        (∀ u, (q u).weights 2 = 2 * min (u.weights 0) (u.weights 1)) ∧
        (∀ u (j : Fin n), (q u).weights j.succ.succ.succ = u.weights j.succ.succ) ∧
        (∀ u, g (u.map (SimplexCategory.δ (0 : Fin (n + 3)))) = smap (q u)) := by
  audit_proof
    obtain ⟨H,hstart,h0,h1,h2,htail,hunion,hkeep1,hkeep2,hkill⟩ := boundaryMergeDeformation n
    have hkeep (t : unitInterval) (u : StdSimplex ℝ (Fin (n + 3)))
        (i : Fin (n + 3)) (hi : i ≠ 0) (hz : u.weights i = 0) :
        (H (t,u)).weights i = 0 := by
      revert hi hz
      refine Fin.cases ?_ (fun r => ?_) i
      · intro hi hz; exact (hi rfl).elim
      · refine Fin.cases ?_ (fun r => ?_) r
        · intro hi hz; exact hkeep1 t u hz
        · refine Fin.cases ?_ (fun r => ?_) r
          · intro hi hz; exact hkeep2 t u hz
          · intro hi hz; exact (htail t u r).trans hz
    let g : C(StdSimplex ℝ (Fin (n + 3)), X) :=
      smap.comp ⟨fun u => H (1,u), H.continuous.comp (continuous_const.prodMk continuous_id)⟩
    have hg1 (u : StdSimplex ℝ (Fin (n + 3))) (hz : u.weights 1 = 0) : g u = x := by
      apply hlow (H (1,u)) 1 2 (by intro h; have hv := congrArg Fin.val h; change 1 = 2 at hv; omega)
      · exact hkeep1 1 u hz
      · exact hkill u hz
    refine ⟨g, ?_, hg1, ?_, ?_, ?_⟩
    · intro u i j hij hi hj
      by_cases hi0 : i = 0
      · subst i
        by_cases hj1 : j = 1
        · exact hg1 u (hj1 ▸ hj)
        · have hj0 : j ≠ 0 := Ne.symm hij
          have hkj := hkeep 1 u j hj0 hj
          rcases hunion 1 u hi with h | h
          · exact hlow (H (1,u)) 0 j hij h hkj
          · exact hlow (H (1,u)) 1 j (Ne.symm hj1) h hkj
      · by_cases hj0 : j = 0
        · subst j
          by_cases hi1 : i = 1
          · exact hg1 u (hi1 ▸ hi)
          · have hki := hkeep 1 u i hi0 hi
            rcases hunion 1 u hj with h | h
            · exact hlow (H (1,u)) i 0 hij hki h
            · exact hlow (H (1,u)) i 1 hi1 hki h
        · exact hlow (H (1,u)) i j hij (hkeep 1 u i hi0 hi) (hkeep 1 u j hj0 hj)
    · intro j hj
      let face : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (n + 3))) :=
        ⟨StdSimplex.map (SimplexCategory.δ j), by fun_prop⟩
      have hzj (u : StdSimplex ℝ (Fin (n + 2))) : (face u).weights j = 0 := by
        change (u.map (SimplexCategory.δ j)).weights j = 0
        rw [StdSimplex.weights_map]
        exact Finsupp.mapDomain_of_notMem_range _ _ (by
          rintro ⟨i,hi⟩
          exact Fin.succAbove_ne j i hi)
      have hj0 : j ≠ 0 := by intro h; subst j; simp at hj
      have hj1 : j ≠ 1 := by intro h; subst j; simp at hj
      refine ⟨{
        toHomotopy := {
        toContinuousMap := smap.comp (H.comp
          ⟨fun z : unitInterval × StdSimplex ℝ (Fin (n + 2)) => (z.1,face z.2),
            continuous_fst.prodMk (face.continuous.comp continuous_snd)⟩)
        map_zero_left := ?_
        map_one_left := ?_ }
        prop' := ?_ }⟩
      · intro u
        change smap (H (0,face u)) = smap (face u)
        rw [hstart]
      · intro u
        rfl
      · intro t u hu
        have hz : smap (H (t,face u)) = x := by
          push Not at hu
          obtain ⟨r,hr⟩ := hu
          have hr0 : u.weights r = 0 := le_antisymm hr (u.weights_nonneg r)
          have hzi : (face u).weights (j.succAbove r) = 0 := by
            change (u.map (SimplexCategory.δ j)).weights (j.succAbove r) = 0
            rw [StdSimplex.weights_map]
            exact (Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective _ _).trans hr0
          have hkj := hkeep t (face u) j hj0 (hzj u)
          have hij : j.succAbove r ≠ j := Fin.succAbove_ne j r
          by_cases hi0 : j.succAbove r = 0
          · rw [hi0] at hzi
            rcases hunion t (face u) hzi with h | h
            · exact hlow (H (t,face u)) 0 j (Ne.symm hj0) h hkj
            · exact hlow (H (t,face u)) 1 j (Ne.symm hj1) h hkj
          · exact hlow (H (t,face u)) (j.succAbove r) j hij
              (hkeep t (face u) (j.succAbove r) hi0 hzi) hkj
        have hz0 : smap (face u) = x := by
          push Not at hu
          obtain ⟨r,hr⟩ := hu
          have hr0 : u.weights r = 0 := le_antisymm hr (u.weights_nonneg r)
          have hzi : (face u).weights (j.succAbove r) = 0 := by
            change (u.map (SimplexCategory.δ j)).weights (j.succAbove r) = 0
            rw [StdSimplex.weights_map]
            exact (Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective _ _).trans hr0
          exact hlow (face u) (j.succAbove r) j (Fin.succAbove_ne j r) hzi (hzj u)
        exact hz.trans hz0.symm
    · intro j hj hc u hz
      apply hc (H (1,u))
      exact hkeep 1 u j (by intro h; subst j; simp at hj) hz
    · let face : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (n + 3))) :=
        ⟨StdSimplex.map (SimplexCategory.δ (0 : Fin (n + 3))), by fun_prop⟩
      let q : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (n + 3))) :=
        ⟨fun u => H (1,face u), H.continuous.comp (continuous_const.prodMk face.continuous)⟩
      have hf0 (u : StdSimplex ℝ (Fin (n + 2))) : (face u).weights 0 = 0 := by
        change (u.map (SimplexCategory.δ (0 : Fin (n + 3)))).weights 0 = 0
        rw [StdSimplex.weights_map]
        exact Finsupp.mapDomain_of_notMem_range _ _ (by
          rintro ⟨i,hi⟩; exact Fin.succAbove_ne 0 i hi)
      have hf (u : StdSimplex ℝ (Fin (n + 2))) (i : Fin (n + 2)) :
          (face u).weights i.succ = u.weights i := by
        change (u.map (SimplexCategory.δ (0 : Fin (n + 3)))).weights ((0 : Fin (n + 3)).succAbove i) = u.weights i
        rw [StdSimplex.weights_map]
        exact Finsupp.mapDomain_apply_of_injective (f := (0 : Fin (n + 3)).succAbove)
          Fin.succAbove_right_injective u.weights i
      have hf1 (u : StdSimplex ℝ (Fin (n + 2))) : (face u).weights 1 = u.weights 0 := by
        simpa only [Fin.succ_zero_eq_one] using hf u 0
      have hf2 (u : StdSimplex ℝ (Fin (n + 2))) : (face u).weights 2 = u.weights 1 := by
        simpa only [Fin.succ_one_eq_two] using hf u 1
      refine ⟨q, ?_, ?_, ?_, ?_, (fun _ => rfl)⟩
      · intro u
        change (H (1,face u)).weights 0 = _
        rw [h0,hf0,hf1,hf2]
        simp
      · intro u
        change (H (1,face u)).weights 1 = _
        rw [h1,hf1,hf2]
        simp
      · intro u
        change (H (1,face u)).weights 2 = _
        rw [h2,hf1,hf2]
        simp only [show (1 : unitInterval).val = 1 from rfl,one_mul]
        by_cases h : u.weights 0 ≤ u.weights 1
        · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h),min_eq_left h]
          ring
        · have h' := le_of_lt (lt_of_not_ge h)
          rw [max_eq_right (sub_nonpos.mpr h'),max_eq_left (sub_nonneg.mpr h'),min_eq_right h']
          ring
      · intro u j
        exact (htail 1 (face u) j).trans (hf u j.succ.succ)
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
noncomputable section
set_option linter.unusedSimpArgs false
-- A single domain permutation transports BOTH adjacent oriented faces.
private theorem adjacentFacePermutation (n : ℕ) (a : Fin (n + 2))
    (perm : Equiv.Perm (Fin (n + 3)))
    (ha : perm a.castSucc = 0) (hb : perm a.succ = 1) :
    ∃ ρ : Equiv.Perm (Fin (n + 2)),
      (∀ r, perm (a.castSucc.succAbove r) = (0 : Fin (n + 3)).succAbove (ρ r)) ∧
      (∀ r, perm (a.succ.succAbove r) = (1 : Fin (n + 3)).succAbove (ρ r)) := by
  audit_proof
    let θ : {i : Fin (n + 3) // i ≠ a.castSucc} ≃ {i : Fin (n + 3) // i ≠ 0} :=
      perm.subtypeEquiv (fun i => by
        constructor
        · intro hi hz
          apply hi
          exact perm.injective (hz.trans ha.symm)
        · intro hi hz
          apply hi
          exact hz ▸ ha)
    let ρ : Equiv.Perm (Fin (n + 2)) :=
      (finSuccAboveEquiv a.castSucc).trans (θ.trans (finSuccAboveEquiv 0).symm)
    have hρ (r : Fin (n + 2)) :
        perm (a.castSucc.succAbove r) = (0 : Fin (n + 3)).succAbove (ρ r) := by
      have h : (finSuccAboveEquiv (0 : Fin (n + 3))) (ρ r) =
          θ ((finSuccAboveEquiv a.castSucc) r) := by
        simp [ρ]
      exact (congrArg Subtype.val h).symm
    refine ⟨ρ,hρ,?_⟩
    intro r
    by_cases hra : r = a
    · subst r
      have hleft : a.castSucc.succAbove a = a.succ := by
        simp [Fin.succAbove]
      have hright : a.succ.succAbove a = a.castSucc := by
        simp [Fin.succAbove, Fin.castSucc_lt_succ]
      have hρ0 : ρ a = 0 := by
        have hh := hρ a
        rw [hleft,hb] at hh
        have hs : (0 : Fin (n + 3)).succAbove (ρ a) = (ρ a).succ :=
          Fin.succAbove_zero_apply _
        rw [hs] at hh
        have hv := congrArg Fin.val hh
        change 1 = (ρ a).val + 1 at hv
        apply Fin.ext
        change (ρ a).val = 0
        omega
      rw [hright,ha,hρ0]
      simp [Fin.succAbove]
    · have hsame : a.castSucc.succAbove r = a.succ.succAbove r := by
        apply Fin.ext
        simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> have hne : r.val ≠ a.val := fun h => hra (Fin.ext h)
        all_goals omega
      have hrne : ρ r ≠ 0 := by
        intro hz
        have hh := hρ r
        rw [hz] at hh
        have hperm : perm (a.castSucc.succAbove r) = perm a.succ := by
          simpa [hb] using hh
        have hinj := perm.injective hperm
        have har : a.castSucc.succAbove a = a.succ := by simp [Fin.succAbove]
        rw [← har] at hinj
        exact hra (Fin.succAbove_right_injective hinj)
      have hzeroone : (0 : Fin (n + 3)).succAbove (ρ r) =
          (1 : Fin (n + 3)).succAbove (ρ r) := by
        apply Fin.ext
        have hrpos : 0 < (ρ r).val := Fin.pos_iff_ne_zero.mpr hrne
        simp only [Fin.succAbove, Fin.lt_def, Fin.val_zero, Fin.val_one,
          Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> omega
      exact (congrArg perm hsame).symm.trans ((hρ r).trans hzeroone)

private theorem pairToFirstTwo (n : ℕ) (a : Fin (n + 3)) (b : Fin (n + 3)) (hab : a ≠ b) :
    ∃ perm : Equiv.Perm (Fin (n + 3)), perm a = 0 ∧ perm b = 1 := by
  audit_proof
    classical
    let τ : Equiv.Perm (Fin (n + 3)) := Equiv.swap 0 a
    have hτa : τ a = 0 := by simp [τ]
    have hτb : τ b ≠ 0 := by
      intro h
      exact hab (τ.injective (hτa.trans h.symm))
    let υ : Equiv.Perm (Fin (n + 3)) := Equiv.swap 1 (τ b)
    refine ⟨τ.trans υ, ?_, ?_⟩
    · change υ (τ a) = 0
      rw [hτa]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h; have hv := congrArg Fin.val h; change 0 = 1 at hv; omega
      · exact Ne.symm hτb
    · change υ (τ b) = 1
      simp [υ]
open CategoryTheory Convexity Topology
open scoped Simplicial unitInterval
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
private def simplexPerm (m : ℕ) (perm : Equiv.Perm (Fin m)) :
    StdSimplex ℝ (Fin m) ≃ₜ StdSimplex ℝ (Fin m) := {
  toFun := StdSimplex.map perm
  invFun := StdSimplex.map perm.symm
  left_inv := by
    intro u
    rw [← StdSimplex.map_comp]
    have h : (perm.symm : Fin m → Fin m) ∘ perm = id := by funext i; exact perm.symm_apply_apply i
    rw [h,StdSimplex.map_id]
  right_inv := by
    intro u
    rw [← StdSimplex.map_comp]
    have h : (perm : Fin m → Fin m) ∘ perm.symm = id := by funext i; exact perm.apply_symm_apply i
    rw [h,StdSimplex.map_id]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop }
private theorem simplexPerm_weights (m : ℕ) (perm : Equiv.Perm (Fin m))
    (u : StdSimplex ℝ (Fin m)) (i : Fin m) :
    (simplexPerm m perm u).weights (perm i) = u.weights i := by
  change (u.map perm).weights (perm i) = u.weights i
  rw [StdSimplex.weights_map]
  exact Finsupp.mapDomain_apply_of_injective perm.injective _ _
private theorem simplexPerm_pos (m : ℕ) (perm : Equiv.Perm (Fin m))
    (u : StdSimplex ℝ (Fin m)) :
    (∀ i, 0 < (simplexPerm m perm u).weights i) ↔ ∀ i, 0 < u.weights i := by
  constructor
  · intro h i; simpa [simplexPerm_weights] using h (perm i)
  · intro h i
    have hw := simplexPerm_weights m perm u (perm.symm i)
    rw [perm.apply_symm_apply] at hw
    rw [hw]
    exact h _
private theorem simplex_face_zero (m : ℕ) (i : Fin (m + 2))
    (u : StdSimplex ℝ (Fin (m + 1))) :
    (u.map (SimplexCategory.δ i)).weights i = 0 := by
  rw [StdSimplex.weights_map]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by
    rintro ⟨j,hj⟩; exact Fin.succAbove_ne i j hj)
private theorem simplex_face_weights (m : ℕ) (i : Fin (m + 2))
    (u : StdSimplex ℝ (Fin (m + 1))) (j : Fin (m + 1)) :
    (u.map (SimplexCategory.δ i)).weights (i.succAbove j) = u.weights j := by
  rw [StdSimplex.weights_map]
  exact Finsupp.mapDomain_apply_of_injective (f := i.succAbove)
    Fin.succAbove_right_injective u.weights j
private def literalFaceLoop {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (smap : C(StdSimplex ℝ (Fin (k + 4)), X))
    (hlow : ∀ t (i j : Fin (k + 4)), i ≠ j → t.weights i = 0 →
      t.weights j = 0 → smap t = x)
    (i : Fin (k + 4)) : GenLoop (Fin (k + 2)) X x :=
  ⟨smap.comp ⟨fun a => (e a).map (SimplexCategory.δ i), by fun_prop⟩, by
    intro a ha
    change smap ((e a).map (SimplexCategory.δ i)) = x
    have hb := (he a).mp ha
    push Not at hb
    obtain ⟨j,hj⟩ := hb
    have hz : (e a).weights j = 0 := le_antisymm hj ((e a).weights_nonneg j)
    exact hlow _ i (i.succAbove j) (Ne.symm (Fin.succAbove_ne i j))
      (simplex_face_zero _ i (e a)) ((simplex_face_weights _ i (e a) j).trans hz)⟩
end CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
open CategoryTheory Convexity Topology
open scoped Simplicial unitInterval
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
private theorem adjacent_simplex_face_homotopy {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (f : C(StdSimplex ℝ (Fin (n + 3)), X))
    (hfaces : ∀ t (i : Fin (n + 3)), 2 ≤ i.val → t.weights i = 0 → f t = x)
    (hshared : ∀ t, t.weights 0 = 0 → t.weights 1 = 0 → f t = x) :
    ContinuousMap.HomotopicRel
      (f.comp ⟨StdSimplex.map (SimplexCategory.δ (0 : Fin (n + 3))), by fun_prop⟩)
      (f.comp ⟨StdSimplex.map (SimplexCategory.δ (1 : Fin (n + 3))), by fun_prop⟩)
      {t | ¬ ∀ i, 0 < t.weights i} := by
  let p (z : unitInterval × StdSimplex ℝ (Fin (n + 2))) :=
    convexCombPair (R := ℝ) (1 - z.1.val) z.1.val
      (sub_nonneg.mpr z.1.property.2) z.1.property.1 (by ring)
      (z.2.map (SimplexCategory.δ (0 : Fin (n + 3))))
      (z.2.map (SimplexCategory.δ (1 : Fin (n + 3))))
  have hp : Continuous p := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 3))).continuous_iff]
    change Continuous (fun z : unitInterval × StdSimplex ℝ (Fin (n + 2)) => (p z).weights.toFun)
    apply continuous_pi
    intro i
    change Continuous (fun z : unitInterval × StdSimplex ℝ (Fin (n + 2)) => (p z).weights i)
    simp only [p, StdSimplex.weights_convexCombPair, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul]
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((StdSimplex.continuous_weights_apply ℝ i).comp
        ((StdSimplex.continuous_map (R := ℝ) (SimplexCategory.δ (0 : Fin (n + 3)))).comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((StdSimplex.continuous_weights_apply ℝ i).comp
          ((StdSimplex.continuous_map (R := ℝ) (SimplexCategory.δ (1 : Fin (n + 3)))).comp continuous_snd)))
  have hmap (i : Fin (n + 3)) (j : Fin (n + 2)) (a : StdSimplex ℝ (Fin (n + 2))) :
      (a.map (SimplexCategory.δ i)).weights (i.succAbove j) = a.weights j := by
    rw [StdSimplex.weights_map]
    exact Finsupp.mapDomain_apply_of_injective (Fin.succAbove_right_injective) _ _
  refine ⟨{
    toHomotopy := {
      toContinuousMap := f.comp ⟨p, hp⟩
      map_zero_left := ?_
      map_one_left := ?_ }
    prop' := ?_ }⟩
  · intro a
    change f (p (0, a)) = f (a.map (SimplexCategory.δ (0 : Fin (n + 3))))
    congr 1
    simp [p]
  · intro a
    change f (p (1, a)) = f (a.map (SimplexCategory.δ (1 : Fin (n + 3))))
    congr 1
    simp [p]
  · intro t a ha
    push Not at ha
    obtain ⟨j, hj⟩ := ha
    have hz : a.weights j = 0 := le_antisymm hj (a.weights_nonneg j)
    have hzero : f (p (t, a)) = x := by
      by_cases hj0 : j = 0
      · subst j
        apply hshared
        · simp only [p, StdSimplex.weights_convexCombPair, Finsupp.add_apply,
            Finsupp.smul_apply, smul_eq_mul]
          have h0 : (a.map (SimplexCategory.δ (0 : Fin (n + 3)))).weights 0 = 0 := by
            rw [StdSimplex.weights_map]
            exact Finsupp.mapDomain_of_notMem_range _ _ (by
              rintro ⟨j, hj⟩
              change (0 : Fin (n + 3)).succAbove j = 0 at hj
              exact Fin.succAbove_ne _ _ hj)
          have h1 : (a.map (SimplexCategory.δ (1 : Fin (n + 3)))).weights 0 = 0 := by
            have h := hmap (1 : Fin (n + 3)) 0 a
            simpa using h.trans hz
          rw [h0, h1]
          simp
        · simp only [p, StdSimplex.weights_convexCombPair, Finsupp.add_apply,
            Finsupp.smul_apply, smul_eq_mul]
          have h0 : (a.map (SimplexCategory.δ (0 : Fin (n + 3)))).weights 1 = 0 := by
            have h := hmap (0 : Fin (n + 3)) 0 a
            simpa using h.trans hz
          have h1 : (a.map (SimplexCategory.δ (1 : Fin (n + 3)))).weights 1 = 0 := by
            rw [StdSimplex.weights_map]
            exact Finsupp.mapDomain_of_notMem_range _ _ (by
              rintro ⟨j, hj⟩
              change (1 : Fin (n + 3)).succAbove j = 1 at hj
              exact Fin.succAbove_ne _ _ hj)
          rw [h0, h1]
          simp
      · apply hfaces (p (t, a)) j.succ (by
          change 2 ≤ j.val + 1
          have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj0
          omega)
        simp only [p, StdSimplex.weights_convexCombPair, Finsupp.add_apply,
          Finsupp.smul_apply, smul_eq_mul]
        have h0 : (0 : Fin (n + 3)).succAbove j = j.succ :=
          Fin.succAbove_of_le_castSucc _ _ (Fin.zero_le _)
        have h1 : (1 : Fin (n + 3)).succAbove j = j.succ :=
          Fin.succAbove_of_le_castSucc _ _ (by
            change 1 ≤ j.val
            have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj0
            omega)
        rw [← h0, hmap, h0, ← h1, hmap, hz]
        simp
    have hstart : f (a.map (SimplexCategory.δ (0 : Fin (n + 3)))) = x := by
      by_cases hj0 : j = 0
      · subst j
        apply hshared
        · rw [StdSimplex.weights_map]
          exact Finsupp.mapDomain_of_notMem_range _ _ (by
            rintro ⟨j, hj⟩
            change (0 : Fin (n + 3)).succAbove j = 0 at hj
            exact Fin.succAbove_ne _ _ hj)
        · have h := hmap (0 : Fin (n + 3)) 0 a
          simpa using h.trans hz
      · apply hfaces _ j.succ (by
          change 2 ≤ j.val + 1
          have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj0
          omega)
        have h0 : (0 : Fin (n + 3)).succAbove j = j.succ :=
          Fin.succAbove_of_le_castSucc _ _ (Fin.zero_le _)
        rw [← h0, hmap, hz]
    exact hzero.trans hstart.symm
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
open Convexity Topology
open scoped unitInterval
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
private theorem simplex_relative_homotopy_pullback {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (f g : C(StdSimplex ℝ (Fin (n + 1)), X))
    (H : f.HomotopyRel g {t | ¬ ∀ i, 0 < t.weights i})
    (u : C((Fin n → unitInterval), StdSimplex ℝ (Fin (n + 1))))
    (hu : ∀ a, a ∈ Cube.boundary (Fin n) → ¬ ∀ i, 0 < (u a).weights i)
    (p q : GenLoop (Fin n) X x) (hp : p.val = f.comp u) (hq : q.val = g.comp u) :
    GenLoop.Homotopic p q := by
  refine ⟨{
    toHomotopy := (H.toHomotopy.compContinuousMap u).cast hp.symm hq.symm
    prop' := ?_ }⟩
  intro t a ha
  change H (t, u a) = p a
  rw [H.eq_fst t (hu a ha)]
  exact congrArg (fun h : C((Fin n → unitInterval), X) => h a) hp.symm
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
open CategoryTheory Convexity Topology
open scoped Simplicial unitInterval
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
private theorem adjacent_face_pi_relation {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (smap : C(StdSimplex ℝ (Fin (k + 4)), X))
    (hfaces : ∀ t (i : Fin (k + 4)), 2 ≤ i.val → t.weights i = 0 → smap t = x)
    (hshared : ∀ t, t.weights 0 = 0 → t.weights 1 = 0 → smap t = x)
    (f₀ f₁ : GenLoop (Fin (k + 2)) X x)
    (hf₀ : ∀ a, f₀ a = smap ((e a).map (SimplexCategory.δ (0 : Fin (k + 4)))))
    (hf₁ : ∀ a, f₁ a = smap ((e a).map (SimplexCategory.δ (1 : Fin (k + 4))))) :
    GenLoop.Homotopic f₀ f₁ ∧
      ((· * ·) : HomotopyGroup.Pi (k + 2) X x → HomotopyGroup.Pi (k + 2) X x →
        HomotopyGroup.Pi (k + 2) X x) ⟦f₀⟧
        ((fun a : HomotopyGroup.Pi (k + 2) X x => a ^ (-1 : ℤ)) ⟦f₁⟧) = 1 := by
  obtain ⟨H⟩ := FiniteSingularCarrier.adjacent_simplex_face_homotopy
    (k + 1) x smap hfaces hshared
  have h : GenLoop.Homotopic f₀ f₁ :=
    FiniteSingularCarrier.simplex_relative_homotopy_pullback (k + 2) x _ _ H
      ⟨e, e.continuous⟩ (fun a ha => (he a).mp ha) f₀ f₁
      (by ext a; exact hf₀ a) (by ext a; exact hf₁ a)
  refine ⟨h, ?_⟩
  have hclass : (⟦f₀⟧ : HomotopyGroup.Pi (k + 2) X x) = ⟦f₁⟧ := Quotient.sound h
  let a : HomotopyGroup.Pi (k + 2) X x := ⟦f₁⟧
  rw [hclass]
  change a * a ^ (-1 : ℤ) = 1
  simp
end CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
open CategoryTheory Convexity Topology
open scoped Simplicial unitInterval
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
private theorem two_active_facet_product {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (smap : C(StdSimplex ℝ (Fin (k + 4)), X))
    (hfaces : ∀ t (i : Fin (k + 4)), 2 ≤ i.val → t.weights i = 0 → smap t = x)
    (hshared : ∀ t, t.weights 0 = 0 → t.weights 1 = 0 → smap t = x)
    (f : Fin (k + 4) → GenLoop (Fin (k + 2)) X x)
    (hf : ∀ i a, f i a = smap ((e a).map (SimplexCategory.δ i))) :
    ∏ i : Fin (k + 4), (fun a : HomotopyGroup.Pi (k + 2) X x =>
      a ^ ((-1 : ℤ) ^ i.val)) ⟦f i⟧ = 1 := by
  classical
  let c (i : Fin (k + 4)) : HomotopyGroup.Pi (k + 2) X x := ⟦f i⟧
  have hconst (i : Fin (k + 4)) (hi : 2 ≤ i.val) : c i = 1 := by
    have hfi : f i = GenLoop.const := by
      apply GenLoop.ext
      intro a
      rw [hf]
      apply hfaces _ i hi
      rw [StdSimplex.weights_map]
      exact Finsupp.mapDomain_of_notMem_range _ _ (by
        rintro ⟨j, hj⟩
        change i.succAbove j = i at hj
        exact Fin.succAbove_ne i j hj)
    let ofLoop : GenLoop (Fin (k + 2)) X x → HomotopyGroup.Pi (k + 2) X x := fun p => ⟦p⟧
    change ofLoop (f i) = 1
    rw [hfi]
    exact HomotopyGroup.one_def.symm
  have hrel := (adjacent_face_pi_relation k x e he smap hfaces hshared
    (f 0) (f 1) (hf 0) (hf 1)).2
  change ∏ i : Fin (k + 4), c i ^ ((-1 : ℤ) ^ i.val) = 1
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  have htail : (∏ i : Fin (k + 2), c i.succ.succ ^ ((-1 : ℤ) ^ i.succ.succ.val)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    rw [hconst i.succ.succ (by simp)]
    exact one_zpow _
  rw [htail]
  change c 0 * c 1 ^ (-1 : ℤ) = 1 at hrel
  have hs : (0 : Fin (k + 3)).succ = (1 : Fin (k + 4)) := by
    apply Fin.ext
    rfl
  simpa only [hs, Fin.val_one, Nat.cast_one, Fin.val_zero, Fin.val_succ, zero_add, pow_zero, pow_one, zpow_one, mul_one] using hrel
end CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
namespace CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
private theorem complementPerm (n : ℕ) (perm : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2)) :
    ∃ eta : Equiv.Perm (Fin (n + 1)),
      ∀ r, perm (j.succAbove r) = (perm j).succAbove (eta r) := by
  let E : {i : Fin (n + 2) // i ≠ j} ≃ {i : Fin (n + 2) // i ≠ perm j} :=
    perm.subtypeEquiv (fun i => perm.injective.ne_iff.symm)
  let eta := (finSuccAboveEquiv j).trans (E.trans (finSuccAboveEquiv (perm j)).symm)
  refine ⟨eta,?_⟩
  intro r
  have h : finSuccAboveEquiv (perm j) (eta r) = E (finSuccAboveEquiv j r) := by simp [eta]
  exact (congrArg Subtype.val h).symm
private theorem perm_face (n : ℕ) (perm : Equiv.Perm (Fin (n + 2)))
    (eta : Equiv.Perm (Fin (n + 1))) (j l : Fin (n + 2))
    (h : ∀ r, perm (j.succAbove r) = l.succAbove (eta r))
    (u : StdSimplex ℝ (Fin (n + 1))) :
    simplexPerm (n + 2) perm (u.map (SimplexCategory.δ j)) =
      (simplexPerm (n + 1) eta u).map (SimplexCategory.δ l) := by
  change (u.map (SimplexCategory.δ j)).map perm =
    (u.map eta).map (SimplexCategory.δ l)
  rw [← StdSimplex.map_comp,← StdSimplex.map_comp]
  congr 1
  funext r
  exact h r
private theorem genericAdjacentMerge {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
    (he : ∀ u, u ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e u).weights i)
    (smap : C(StdSimplex ℝ (Fin (k + 4)), X))
    (hlow : ∀ u (i j : Fin (k + 4)), i ≠ j → u.weights i = 0 → u.weights j = 0 → smap u = x)
    (f : Fin (k + 4) → GenLoop (Fin (k + 2)) X x)
    (hf : ∀ i u, f i u = smap ((e u).map (SimplexCategory.δ i)))
    (a : Fin (k + 3)) :
    ∃ (g : C(StdSimplex ℝ (Fin (k + 4)), X))
      (hg : ∀ u (i j : Fin (k + 4)), i ≠ j → u.weights i = 0 → u.weights j = 0 → g u = x)
      (ff : Fin (k + 4) → GenLoop (Fin (k + 2)) X x),
      (∀ i u, ff i u = g ((e u).map (SimplexCategory.δ i))) ∧
      (∀ u, u.weights a.succ = 0 → g u = x) ∧
      ((⟦ff a.castSucc⟧ : HomotopyGroup.Pi (k + 2) X x) = ((· * ·) : HomotopyGroup.Pi (k + 2) X x → _ → _) ⟦f a.castSucc⟧
        ((Inv.inv : HomotopyGroup.Pi (k + 2) X x → _) ⟦f a.succ⟧)) ∧
      (∀ j, j ≠ a.castSucc → j ≠ a.succ →
        (⟦ff j⟧ : HomotopyGroup.Pi (k + 2) X x) = ⟦f j⟧) ∧
      (∀ j, j ≠ a.castSucc → j ≠ a.succ →
        (∀ u, u.weights j = 0 → smap u = x) → ∀ u, u.weights j = 0 → g u = x) := by
  obtain ⟨perm,hpa,hpb⟩ := pairToFirstTwo (k + 1) a.castSucc a.succ (by
    intro h; have hv := congrArg Fin.val h; simp only [Fin.val_castSucc,Fin.val_succ] at hv; omega)
  obtain ⟨rho,hra,hrb⟩ := adjacentFacePermutation (k + 1) a perm hpa hpb
  let P := simplexPerm (k + 4) perm
  let Q := simplexPerm (k + 3) rho
  let e' := e.trans Q
  have he' : ∀ u, u ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e' u).weights i := by
    intro u
    change _ ↔ ¬ ∀ i, 0 < (simplexPerm (k + 3) rho (e u)).weights i
    rw [simplexPerm_pos]
    exact he u
  let s : C(StdSimplex ℝ (Fin (k + 4)), X) := smap.comp ⟨P.symm,P.symm.continuous⟩
  have hs : ∀ u (i j : Fin (k + 4)), i ≠ j → u.weights i = 0 → u.weights j = 0 → s u = x := by
    intro u i j hij hi hj
    apply hlow (P.symm u) (perm.symm i) (perm.symm j) (perm.symm.injective.ne hij)
    · have h := simplexPerm_weights (k + 4) perm (P.symm u) (perm.symm i)
      change (P (P.symm u)).weights (perm (perm.symm i)) = (P.symm u).weights (perm.symm i) at h
      rw [P.apply_symm_apply,perm.apply_symm_apply] at h
      exact h.symm.trans hi
    · have h := simplexPerm_weights (k + 4) perm (P.symm u) (perm.symm j)
      change (P (P.symm u)).weights (perm (perm.symm j)) = (P.symm u).weights (perm.symm j) at h
      rw [P.apply_symm_apply,perm.apply_symm_apply] at h
      exact h.symm.trans hj
  obtain ⟨gt,hgt,hgt1,hrel,hretain,q,hq0,hq1,hq2,hqtail,hq⟩ :=
    FiniteSingularCarrier.oneFaceCollapseWithCarrier (k + 1) x s hs
  let g : C(StdSimplex ℝ (Fin (k + 4)), X) := gt.comp ⟨P,P.continuous⟩
  have hg : ∀ u (i j : Fin (k + 4)), i ≠ j → u.weights i = 0 → u.weights j = 0 → g u = x := by
    intro u i j hij hi hj
    exact hgt (P u) (perm i) (perm j) (perm.injective.ne hij)
      ((simplexPerm_weights _ perm u i).trans hi) ((simplexPerm_weights _ perm u j).trans hj)
  let ff := literalFaceLoop k x e he g hg
  have hff : ∀ i u, ff i u = g ((e u).map (SimplexCategory.δ i)) := fun _ _ => rfl
  have hmova (u : StdSimplex ℝ (Fin (k + 3))) :
      P (u.map (SimplexCategory.δ a.castSucc)) = (Q u).map (SimplexCategory.δ (0 : Fin (k + 4))) :=
    perm_face (k + 2) perm rho a.castSucc 0 hra u
  have hmovb (u : StdSimplex ℝ (Fin (k + 3))) :
      P (u.map (SimplexCategory.δ a.succ)) = (Q u).map (SimplexCategory.δ (1 : Fin (k + 4))) :=
    perm_face (k + 2) perm rho a.succ 1 hrb u
  have hfa (u) : f a.castSucc u = s ((e' u).map (SimplexCategory.δ (0 : Fin (k + 4)))) := by
    rw [hf]
    change smap ((e u).map (SimplexCategory.δ a.castSucc)) =
      smap (P.symm ((Q (e u)).map (SimplexCategory.δ (0 : Fin (k + 4)))))
    rw [← hmova,P.symm_apply_apply]
  have hfb (u) : f a.succ u = s ((e' u).map (SimplexCategory.δ (1 : Fin (k + 4)))) := by
    rw [hf]
    change smap ((e u).map (SimplexCategory.δ a.succ)) =
      smap (P.symm ((Q (e u)).map (SimplexCategory.δ (1 : Fin (k + 4)))))
    rw [← hmovb,P.symm_apply_apply]
  have hmerged (u) : ff a.castSucc u = s (q (e' u)) := by
    rw [hff]
    change gt (P ((e u).map (SimplexCategory.δ a.castSucc))) = s (q (e' u))
    rw [hmova]
    exact hq (e' u)
  have hclass := recoveredBinaryMerge k x e' he' s hs q hq0 hq1 hq2 hqtail
    (f a.castSucc) (f a.succ) (ff a.castSucc) hfa hfb hmerged
  have hother (j : Fin (k + 4)) (hja : j ≠ a.castSucc) (hjb : j ≠ a.succ) : 2 ≤ (perm j).val := by
    have h0 : perm j ≠ 0 := by intro h; exact hja (perm.injective (h.trans hpa.symm))
    have h1 : perm j ≠ 1 := by intro h; exact hjb (perm.injective (h.trans hpb.symm))
    have h0v : (perm j).val ≠ 0 := fun h => h0 (Fin.ext h)
    have h1v : (perm j).val ≠ 1 := fun h => h1 (Fin.ext h)
    omega
  refine ⟨g,hg,ff,hff,?_,?_,?_,?_⟩
  · intro u hu
    apply hgt1 (P u)
    have hw := simplexPerm_weights _ perm u a.succ
    rw [hpb] at hw
    exact hw.trans hu
  · exact hclass.trans (congrArg
      (fun z : HomotopyGroup.Pi (k + 2) X x =>
        ((· * ·) : HomotopyGroup.Pi (k + 2) X x → _ → _) ⟦f a.castSucc⟧ z)
      (zpow_neg_one (G := HomotopyGroup.Pi (k + 2) X x) ⟦f a.succ⟧))
  · intro j hja hjb
    obtain ⟨eta,heta⟩ := complementPerm (k + 2) perm j
    let E := simplexPerm (k + 3) eta
    obtain ⟨K⟩ := hrel (perm j) (hother j hja hjb)
    have hmove (u : StdSimplex ℝ (Fin (k + 3))) :
        P (u.map (SimplexCategory.δ j)) = (E u).map (SimplexCategory.δ (perm j)) :=
      perm_face (k + 2) perm eta j (perm j) heta u
    have hn (u) : u ∈ Cube.boundary (Fin (k + 2)) → ¬ ∀ i, 0 < (E (e u)).weights i := by
      intro hu
      rw [simplexPerm_pos]
      exact (he u).mp hu
    have hp : (f j).val =
        (s.comp ⟨StdSimplex.map (SimplexCategory.δ (perm j)),by fun_prop⟩).comp
          ⟨fun u => E (e u),by fun_prop⟩ := by
      ext u
      change f j u = s ((E (e u)).map (SimplexCategory.δ (perm j)))
      rw [hf]
      change smap ((e u).map (SimplexCategory.δ j)) = smap (P.symm _)
      rw [← hmove,P.symm_apply_apply]
    have hp' : (ff j).val =
        (gt.comp ⟨StdSimplex.map (SimplexCategory.δ (perm j)),by fun_prop⟩).comp
          ⟨fun u => E (e u),by fun_prop⟩ := by
      ext u
      change g ((e u).map (SimplexCategory.δ j)) = gt ((E (e u)).map (SimplexCategory.δ (perm j)))
      change gt (P ((e u).map (SimplexCategory.δ j))) = _
      rw [hmove]
    exact (Quotient.sound (FiniteSingularCarrier.simplex_relative_homotopy_pullback
      (k + 2) x _ _ K ⟨fun u => E (e u),by fun_prop⟩ hn (f j) (ff j) hp hp')).symm
  · intro j hja hjb hc u hu
    apply hretain (perm j) (hother j hja hjb)
    · intro v hv
      apply hc (P.symm v)
      have hw := simplexPerm_weights _ perm (P.symm v) j
      have hP : P (P.symm v) = v := P.apply_symm_apply v
      change (P (P.symm v)).weights (perm j) = (P.symm v).weights j at hw
      rw [hP] at hw
      exact hw.symm.trans hv
    · exact (simplexPerm_weights _ perm u j).trans hu
end CurveComplexGenusTwo.CWHurewicz.CWGeometricChains

open scoped BigOperators
private theorem alternatingMergeProduct {G : Type*} [CommGroup G] (n : ℕ)
    (a : Fin (n + 1)) (c d : Fin (n + 2) → G)
    (hA : d a.castSucc = c a.castSucc * (c a.succ)⁻¹)
    (hB : d a.succ = 1)
    (hRest : ∀ j, j ≠ a.castSucc → j ≠ a.succ → d j = c j) :
    (∏ i : Fin (n + 2), d i ^ ((-1 : ℤ) ^ i.val)) =
      ∏ i : Fin (n + 2), c i ^ ((-1 : ℤ) ^ i.val) := by
  audit_proof
    classical
    let A : Fin (n + 2) := a.castSucc
    let B : Fin (n + 2) := a.succ
    have hab : A ≠ B := by
      intro h; have hv := congrArg Fin.val h
      change a.val = a.val + 1 at hv
      omega
    let s : Finset (Fin (n + 2)) := (Finset.univ.erase A).erase B
    have hbin : B ∈ Finset.univ.erase A := Finset.mem_erase.mpr ⟨Ne.symm hab,Finset.mem_univ _⟩
    have hsplit (F : Fin (n + 2) → G) :
        (∏ i, F i) = (F A * F B) * ∏ i ∈ s, F i := by
      rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ A),
        ← Finset.mul_prod_erase (Finset.univ.erase A) F hbin]
      exact (mul_assoc _ _ _).symm
    have hexp : (-1 : ℤ) ^ B.val = -((-1 : ℤ) ^ A.val) := by
      change (-1 : ℤ) ^ (a.val + 1) = -((-1 : ℤ) ^ a.val)
      simp [pow_succ]
    rw [hsplit,hsplit]
    have hpair : d A ^ ((-1 : ℤ) ^ A.val) * d B ^ ((-1 : ℤ) ^ B.val) =
        c A ^ ((-1 : ℤ) ^ A.val) * c B ^ ((-1 : ℤ) ^ B.val) := by
      rw [hA,hB,one_zpow,mul_one,mul_zpow,inv_zpow,hexp,zpow_neg]
    rw [hpair]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hjB : j ≠ B := (Finset.mem_erase.mp hj).1
    have hjA : j ≠ A := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    rw [hRest j hjA hjB]
namespace CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
private theorem boundedOrientedProduct {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
    (he : ∀ u, u ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e u).weights i) :
    ∀ (r : ℕ), r ≤ k + 4 →
    ∀ (smap : C(StdSimplex ℝ (Fin (k + 4)), X))
      (hlow : ∀ u (i j : Fin (k + 4)), i ≠ j → u.weights i = 0 → u.weights j = 0 → smap u = x)
      (hconst : ∀ u (i : Fin (k + 4)), r ≤ i.val → u.weights i = 0 → smap u = x)
      (f : Fin (k + 4) → GenLoop (Fin (k + 2)) X x)
      (hf : ∀ i u, f i u = smap ((e u).map (SimplexCategory.δ i))),
      ∏ i : Fin (k + 4), (fun a : HomotopyGroup.Pi (k + 2) X x =>
        a ^ ((-1 : ℤ) ^ i.val)) ⟦f i⟧ = 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr smap hlow hconst f hf
    by_cases hsmall : r ≤ 2
    · exact two_active_facet_product k x e he smap
        (fun u i hi hz => hconst u i (by omega) hz)
        (fun u h0 h1 => hlow u 0 1 (by
          intro h; have hv := congrArg Fin.val h; change 0 = 1 at hv; omega) h0 h1) f hf
    · let a : Fin (k + 3) := ⟨r - 2, by omega⟩
      obtain ⟨g,hg,ff,hff,hkill,hmerge,hrest,hkeep⟩ := genericAdjacentMerge k x e he smap hlow f hf a
      have hconst' (u : StdSimplex ℝ (Fin (k + 4))) (j : Fin (k + 4))
          (hj : r - 1 ≤ j.val) (hz : u.weights j = 0) : g u = x := by
        by_cases hjs : j = a.succ
        · subst j; exact hkill u hz
        · have hja : j ≠ a.castSucc := by
            intro h; have hv := congrArg Fin.val h
            change j.val = r - 2 at hv
            omega
          have hjr : r ≤ j.val := by
            have hneq : j.val ≠ r - 1 := by
              intro h; apply hjs; apply Fin.ext
              change j.val = (r - 2) + 1
              omega
            omega
          exact hkeep j hja hjs (fun v hv => hconst v j hjr hv) u hz
      have hb : (⟦ff a.succ⟧ : HomotopyGroup.Pi (k + 2) X x) = (1 : HomotopyGroup.Pi (k + 2) X x) := by
        have hloop : ff a.succ = GenLoop.const := by
          apply GenLoop.ext
          intro u
          rw [hff]
          exact hkill _ (simplex_face_zero (k + 2) a.succ (e u))
        change (Quotient.mk _ (ff a.succ) : HomotopyGroup.Pi (k + 2) X x) = (1 : HomotopyGroup.Pi (k + 2) X x)
        rw [hloop]
        exact HomotopyGroup.one_def.symm
      have hinv := alternatingMergeProduct (G := HomotopyGroup.Pi (k + 2) X x) (k + 2) a
        (fun i => (⟦f i⟧ : HomotopyGroup.Pi (k + 2) X x))
        (fun i => (⟦ff i⟧ : HomotopyGroup.Pi (k + 2) X x)) hmerge hb hrest
      have hfinal := ih (r - 1) (by omega) (by omega) g hg hconst' ff hff
      exact hinv.symm.trans hfinal

theorem oriented_simplex_face_classes_product_eq_one {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (smap : C(StdSimplex ℝ (Fin (k + 4)), X))
    (hlow : ∀ t (i j : Fin (k + 4)), i ≠ j → t.weights i = 0 →
      t.weights j = 0 → smap t = x)
    (f : Fin (k + 4) → GenLoop (Fin (k + 2)) X x)
    (hf : ∀ i a, f i a = smap ((e a).map (SimplexCategory.δ i))) :
    ∏ i : Fin (k + 4), (fun a : HomotopyGroup.Pi (k + 2) X x =>
      a ^ ((-1 : ℤ) ^ i.val)) ⟦f i⟧ = 1 := by
  audit_proof
    exact boundedOrientedProduct k x e he (k + 4) le_rfl smap hlow
      (fun u i hi hz => (by have := i.isLt; omega)) f hf
end CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
