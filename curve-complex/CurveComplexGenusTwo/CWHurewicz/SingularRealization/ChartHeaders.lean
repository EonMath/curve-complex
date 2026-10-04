import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.CWComplex.Classical.Basic
open Convexity Topology
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.SingularApproximation
/-- Closed unit disk chart for the genuine topological simplex, matching open-ball interior
with strict positivity of every barycentric coordinate. -/
theorem standardSimplex_diskChart (n : ℕ) :
    ∃ h : (Metric.closedBall (0 : Fin n → ℝ) 1) ≃ₜ StdSimplex ℝ (Fin (n + 1)),
      ∀ x, (∀ i, 0 < (h x).weights i) ↔ x.val ∈ Metric.ball 0 1 := by
  have hInterior : interior {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} =
      {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
    cases n with
    | zero => simp
    | succ n =>
      let L : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
      have hL : Function.Surjective L := by
        intro r
        refine ⟨Pi.single 0 r, ?_⟩
        simp [L, Pi.single_apply]
      have ho : IsOpenMap (fun x : Fin (n + 1) → ℝ => ∑ i, x i) :=
        by
          have he : (fun x : Fin (n+1) → ℝ => ∑ i, x i) = L := by
            funext x
            simp [L]
          rw [he]
          exact LinearMap.isOpenMap_of_finiteDimensional L hL
      have hcoord (i : Fin (n+1)) :
          interior {x : Fin (n+1) → ℝ | 0 ≤ x i} = {x | 0 < x i} := by
        change interior ((fun x : Fin (n+1) → ℝ => x i) ⁻¹' Set.Ici 0) = _
        rw [← (isOpenMap_eval i).preimage_interior_eq_interior_preimage (continuous_apply i),
          interior_Ici]
        rfl
      have hsum : interior {x : Fin (n+1) → ℝ | ∑ i, x i ≤ 1} =
          {x | ∑ i, x i < 1} := by
        change interior ((fun x : Fin (n+1) → ℝ => ∑ i, x i) ⁻¹' Set.Iic 1) = _
        rw [← ho.preimage_interior_eq_interior_preimage (by fun_prop), interior_Iic]
        rfl
      have he : {x : Fin (n+1) → ℝ | ∀ i, 0 ≤ x i} =
          ⋂ i, {x : Fin (n+1) → ℝ | 0 ≤ x i} := by ext; simp
      change interior ({x : Fin (n+1) → ℝ | ∀ i, 0 ≤ x i} ∩
        {x | ∑ i, x i ≤ 1}) = _
      rw [interior_inter, he, interior_iInter_of_finite, hsum]
      simp only [hcoord]
      ext
      simp
  have hGeometry : Convex ℝ {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} ∧
    IsClosed {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} ∧
    Bornology.IsBounded {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy a b ha hb hab
      constructor
      · intro i
        exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        calc
          a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
              (mul_le_mul_of_nonneg_left hy.2 hb)
          _ = 1 := by simpa using hab
    · have he : {x : Fin n → ℝ | ∀ i, 0 ≤ x i} =
          ⋂ i, {x : Fin n → ℝ | 0 ≤ x i} := by ext; simp
      change IsClosed ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ 1})
      refine IsClosed.inter ?_ (isClosed_le (by fun_prop) continuous_const)
      rw [he]
      exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
    · apply (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 i)]
      exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2
  have hPositive : {x : Fin n → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}.Nonempty := by
    refine ⟨fun _ => 1 / (n + 1 : ℝ), ?_, ?_⟩
    · intro i
      positivity
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      rw [div_eq_mul_inv, ← mul_assoc, ← div_eq_mul_inv]
      apply (div_lt_one (by positivity : 0 < (n + 1 : ℝ))).mpr
      linarith
  have hCoordinates : ∃ h : {x : Fin n → ℝ // (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} ≃ₜ
      StdSimplex ℝ (Fin (n+1)),
      ∀ x, (∀ i, 0 < (h x).weights i) ↔ (∀ i, 0 < x.val i) ∧ ∑ i, x.val i < 1 := by
    let C := {x : Fin n → ℝ // (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}
    let f : C → StdSimplex ℝ (Fin (n + 1)) := fun x =>
      { weights := Finsupp.equivFunOnFinite.symm (Fin.lastCases (1 - ∑ i, x.val i) x.val)
        nonneg := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using sub_nonneg.mpr x.property.2
          · simpa using x.property.1 j
        total := by
          simp [Finsupp.sum_fintype, Fin.sum_univ_castSucc] }
    let g : StdSimplex ℝ (Fin (n + 1)) → C := fun t =>
      ⟨fun i => t.weights i.castSucc, (fun i => t.nonneg _), by
        have ht := t.total_of_fintype
        rw [Fin.sum_univ_castSucc] at ht
        have hn : 0 ≤ t.weights (Fin.last n) := t.nonneg (Fin.last n)
        linarith⟩
    let h : C ≃ₜ StdSimplex ℝ (Fin (n+1)) := by
      refine { toFun := f
               invFun := g
               left_inv := ?_
               right_inv := ?_
               continuous_toFun := ?_
               continuous_invFun := ?_ }
      · intro x
        apply Subtype.ext
        funext i
        simp [f, g]
      · intro t
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · have ht := t.total_of_fintype
          rw [Fin.sum_univ_castSucc] at ht
          simp [f, g]
          linarith
        · simp [f, g]
      · rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
        apply continuous_pi
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Function.comp_apply, f]
          simpa using (show Continuous (fun x : C => 1 - ∑ j, x.val j) by
            dsimp [C]
            fun_prop)
        · simp only [Function.comp_apply, f]
          simpa using (show Continuous (fun x : C => x.val j) by
            exact (continuous_apply j).comp continuous_subtype_val)
      · apply Continuous.subtype_mk
        apply continuous_pi
        intro i
        exact StdSimplex.continuous_weights_apply ℝ _
    refine ⟨h, ?_⟩
    intro x
    change (∀ i, 0 < (f x).weights i) ↔ _
    simp only [f, Finsupp.coe_equivFunOnFinite_symm]
    constructor
    · intro hx
      refine ⟨fun i => ?_, ?_⟩
      · simpa using hx i.castSucc
      · have hl := hx (Fin.last n)
        simp only [Fin.lastCases_last] at hl
        linarith
    · rintro ⟨hx, hs⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.lastCases_last]
        linarith
      · simpa using hx j
  let C : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}
  obtain ⟨hc, hclosed, hb⟩ := hGeometry
  have hne : (interior C).Nonempty := by simpa [C, hInterior] using hPositive
  obtain ⟨H, hball, hdisk, _⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hb
  rw [hclosed.closure_eq] at hdisk
  obtain ⟨K, hK⟩ := hCoordinates
  let J : C ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 :=
    (H.image C).trans (Homeomorph.setCongr hdisk)
  refine ⟨J.symm.trans K, ?_⟩
  intro x
  rw [Homeomorph.trans_apply, hK]
  change ((∀ i, 0 < (J.symm x).val i) ∧ ∑ i, (J.symm x).val i < 1) ↔ _
  change (J.symm x).val ∈ {y : Fin n → ℝ | (∀ i, 0 < y i) ∧ ∑ i, y i < 1} ↔ _
  rw [← hInterior]
  have he : x.val = H (J.symm x).val := by
    have hj := congrArg Subtype.val (J.apply_symm_apply x)
    exact hj.symm
  rw [he, ← hball]
  exact H.injective.mem_set_image.symm
end CurveComplexGenusTwo.CWHurewicz.SingularApproximation
