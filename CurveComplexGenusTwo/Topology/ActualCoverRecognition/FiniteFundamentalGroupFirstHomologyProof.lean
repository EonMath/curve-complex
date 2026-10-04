import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import Mathlib.Topology.Homotopy.Path
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

open CategoryTheory CategoryTheory.Limits Convexity
open CurveComplexGenusTwo.CWHurewicz
open scoped Simplicial

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CurveComplex.LocalSurgery

/-- Degree-one integral Hurewicz consequence: the abelianization of a finite
based fundamental group is finite. This asserts actual singular integral H1,
not a supplied homology-surjectivity or cycle-generation certificate. -/
theorem finite_integral_first_homology_of_finite_fundamental_group
    (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) [Finite (FundamentalGroup X x)] :
    Finite (CurveComplex.integralHomology X 1) := by
  classical
  let T := TopCat.of X
  let Sing (n : ℕ) := (TopCat.toSSet.obj T) _⦋n⦌
  let C := mvAmbientComplex T
  let π : (Sing 1 →₀ ℤ) →ₗ[ℤ] C.opcycles 1 := (C.pOpcycles 1).hom
  let coord : C(StdSimplex ℝ (Fin 2), unitInterval) :=
    ⟨fun z => ⟨z.weights 1, z.weights_nonneg 1, z.weights_apply_le_one 1⟩,
      (StdSimplex.continuous_weights_apply ℝ 1).subtype_mk _⟩
  let pathSing {a b : X} (p : Path a b) : Sing 1 :=
    (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).symm (p.toContinuousMap.comp coord)
  let value {a b : X} (p : Path a b) : C.opcycles 1 := π (Finsupp.single (pathSing p) 1)
  have hboundary (c : Sing 2 →₀ ℤ) : π (singularBoundaryFinsupp T 1 c) = 0 := by
    have hh := congrArg (fun f => f c) (C.d_pOpcycles 2 1)
    exact hh
  have hconcat {a b c : X} (p : Path a b) (q : Path b c) :
      value (p.trans q) = value p + value q := by
    let k : C(StdSimplex ℝ (Fin 3), unitInterval) :=
      ⟨fun z => ⟨z.weights 1 / 2 + z.weights 2, by
          constructor
          · exact add_nonneg (div_nonneg (z.weights_nonneg 1) (by norm_num))
              (z.weights_nonneg 2)
          · have hs := z.total
            rw [Finsupp.sum_fintype] at hs <;> try simp
            simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
            change z.weights 0 + (z.weights 1 + z.weights 2) = 1 at hs
            linarith [z.weights_nonneg 0, z.weights_nonneg 1]⟩, by fun_prop⟩
    let τ : Sing 2 := (TopCat.toSSetObjEquiv T (.op ⦋2⦌)).symm
      ((p.trans q).toContinuousMap.comp k)
    have hk0 (z : StdSimplex ℝ (Fin 2)) :
        (k (z.map (0 : Fin 3).succAbove) : ℝ) = (1 + (coord z : ℝ)) / 2 := by
      change (z.map (0 : Fin 3).succAbove).weights 1 / 2 +
        (z.map (0 : Fin 3).succAbove).weights 2 = (1 + z.weights 1) / 2
      simp only [StdSimplex.weights_map]
      change (Finsupp.mapDomain (0 : Fin 3).succAbove z.weights)
          ((0 : Fin 3).succAbove 0) / 2 +
        (Finsupp.mapDomain (0 : Fin 3).succAbove z.weights)
          ((0 : Fin 3).succAbove 1) = (1 + z.weights 1) / 2
      rw [Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective,
        Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective]
      have hs := z.total
      rw [Finsupp.sum_fintype] at hs <;> try simp
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
      change z.weights 0 + z.weights 1 = 1 at hs
      linarith
    have hk1 (z : StdSimplex ℝ (Fin 2)) :
        k (z.map (1 : Fin 3).succAbove) = coord z := by
      apply Subtype.ext
      simp [k, coord, StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
        Fin.sum_univ_succ, Fin.succAbove]
    have hk2 (z : StdSimplex ℝ (Fin 2)) :
        (k (z.map (2 : Fin 3).succAbove) : ℝ) = (coord z : ℝ) / 2 := by
      simp [k, coord, StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
        Fin.sum_univ_succ, Fin.succAbove]
    have hface0 : (TopCat.toSSet.obj T).δ 0 τ = pathSing q := by
      apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
      apply ContinuousMap.ext
      intro z
      change (p.trans q) (k (z.map (0 : Fin 3).succAbove)) = q (coord z)
      rw [Path.trans_apply]
      split_ifs with ht
      · have hzero : coord z = 0 := by
          apply Subtype.ext
          have := (coord z).property.1
          rw [hk0] at ht
          change (coord z : ℝ) = 0
          linarith
        have hcalc : 2 * (k (z.map (0 : Fin 3).succAbove) : ℝ) = 1 := by
          rw [hk0, hzero]
          norm_num
        have hone : (⟨2 * (k (z.map (0 : Fin 3).succAbove) : ℝ), by
            rw [hcalc]; exact ⟨by norm_num, le_rfl⟩⟩ : unitInterval) = 1 :=
          Subtype.ext hcalc
        rw [hone, p.target, hzero, q.source]
      · congr 1
        apply Subtype.ext
        change 2 * (k (z.map (0 : Fin 3).succAbove) : ℝ) - 1 = (coord z : ℝ)
        rw [hk0]
        ring
    have hface1 : (TopCat.toSSet.obj T).δ 1 τ = pathSing (p.trans q) := by
      apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
      apply ContinuousMap.ext
      intro z
      change (p.trans q) (k (z.map (1 : Fin 3).succAbove)) = (p.trans q) (coord z)
      rw [hk1]
    have hface2 : (TopCat.toSSet.obj T).δ 2 τ = pathSing p := by
      apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
      apply ContinuousMap.ext
      intro z
      change (p.trans q) (k (z.map (2 : Fin 3).succAbove)) = p (coord z)
      rw [Path.trans_apply]
      split_ifs with ht
      · congr 1
        apply Subtype.ext
        change 2 * (k (z.map (2 : Fin 3).succAbove) : ℝ) = (coord z : ℝ)
        rw [hk2]
        ring
      · exfalso
        apply ht
        rw [hk2]
        linarith [(coord z).property.2]
    have hb : singularBoundaryFinsupp T 1 (Finsupp.single τ 1) =
        Finsupp.single (pathSing q) 1 - Finsupp.single (pathSing (p.trans q)) 1 +
          Finsupp.single (pathSing p) 1 := by
      rw [singularBoundaryFinsupp_single]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      norm_num only [Fin.val_zero, Fin.val_succ, pow_zero, pow_one, pow_two]
      simp only [one_smul]
      change Finsupp.single ((TopCat.toSSet.obj T).δ 0 τ) (1 : ℤ) +
        ((-1 : ℤ) • Finsupp.single ((TopCat.toSSet.obj T).δ 1 τ) (1 : ℤ) +
          Finsupp.single ((TopCat.toSSet.obj T).δ 2 τ) (1 : ℤ)) = _
      rw [hface0, hface1, hface2]
      simp only [neg_one_smul, one_smul]
      abel
    have hh := hboundary (Finsupp.single τ 1)
    rw [hb, map_add, map_sub] at hh
    change value q - value (p.trans q) + value p = 0 at hh
    apply sub_eq_zero.mp
    calc value (p.trans q) - (value p + value q) =
        -(value q - value (p.trans q) + value p) := by abel
      _ = 0 := by rw [hh]; simp
  have hweights (z : StdSimplex ℝ (Fin 2)) (i j : Fin 3) :
      (z.map i.succAbove).weights j =
        match i.val, j.val with
        | 0, 0 => 0
        | 0, 1 => z.weights 0
        | 0, 2 => z.weights 1
        | 1, 0 => z.weights 0
        | 1, 1 => 0
        | 1, 2 => z.weights 1
        | 2, 0 => z.weights 0
        | 2, 1 => z.weights 1
        | 2, 2 => 0
        | _, _ => 0 := by
    fin_cases i <;> fin_cases j <;>
      simp [StdSimplex.weights_map, Finsupp.mapDomain_apply, Finsupp.sum_fintype,
        Fin.sum_univ_succ, Fin.succAbove]
  have hsum (z : StdSimplex ℝ (Fin 2)) : z.weights 0 + z.weights 1 = 1 := by
    have hs := z.total
    rw [Finsupp.sum_fintype] at hs <;> try simp
    try simpa [Fin.sum_univ_succ] using hs
  have hconst (a : X) : value (Path.refl a) = 0 := by
    let τ : Sing 2 := (TopCat.toSSetObjEquiv T (.op ⦋2⦌)).symm
      (ContinuousMap.const _ a)
    have hfaces (i : Fin 3) : (TopCat.toSSet.obj T).δ i τ = pathSing (Path.refl a) := by
      apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
      apply ContinuousMap.ext
      intro z
      rfl
    have hh := hboundary (Finsupp.single τ 1)
    rw [singularBoundaryFinsupp_single] at hh
    have hb : (∑ i : Fin 3, (-1 : ℤ) ^ i.val •
        Finsupp.single ((TopCat.toSSet.obj T).δ i τ) (1 : ℤ)) =
        Finsupp.single (pathSing (Path.refl a)) 1 := by
      simp_rw [hfaces]
      norm_num [Fin.sum_univ_succ, neg_one_smul, one_smul]
    rw [hb] at hh
    exact hh
  have hhomotopic {a : X} (p q : Path a a) (h : p.Homotopic q) : value p = value q := by
    obtain ⟨F⟩ := h
    let A : C(StdSimplex ℝ (Fin 3), unitInterval × unitInterval) :=
      ⟨fun z => (⟨z.weights 1 + z.weights 2, by
          constructor
          · exact add_nonneg (z.weights_nonneg 1) (z.weights_nonneg 2)
          · have hs := z.total
            rw [Finsupp.sum_fintype] at hs <;> try simp
            simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
            change z.weights 0 + (z.weights 1 + z.weights 2) = 1 at hs
            linarith [z.weights_nonneg 0]⟩,
        ⟨z.weights 2, z.weights_nonneg 2, z.weights_apply_le_one 2⟩), by fun_prop⟩
    let B : C(StdSimplex ℝ (Fin 3), unitInterval × unitInterval) :=
      ⟨fun z => (⟨z.weights 2, z.weights_nonneg 2, z.weights_apply_le_one 2⟩,
        ⟨z.weights 1 + z.weights 2, by
          constructor
          · exact add_nonneg (z.weights_nonneg 1) (z.weights_nonneg 2)
          · have hs := z.total
            rw [Finsupp.sum_fintype] at hs <;> try simp
            simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
            change z.weights 0 + (z.weights 1 + z.weights 2) = 1 at hs
            linarith [z.weights_nonneg 0]⟩), by fun_prop⟩
    have hA0 (z : StdSimplex ℝ (Fin 2)) : A (z.map (0 : Fin 3).succAbove) = (1, coord z) := by
      apply Prod.ext <;> apply Subtype.ext
      · change (z.map (0 : Fin 3).succAbove).weights 1 + (z.map (0 : Fin 3).succAbove).weights 2 = 1
        rw [hweights, hweights]
        exact hsum z
      · change (z.map (0 : Fin 3).succAbove).weights 2 = z.weights 1
        rw [hweights]; rfl
    have hA1 (z : StdSimplex ℝ (Fin 2)) : A (z.map (1 : Fin 3).succAbove) = (coord z, coord z) := by
      apply Prod.ext <;> apply Subtype.ext
      · change (z.map (1 : Fin 3).succAbove).weights 1 + (z.map (1 : Fin 3).succAbove).weights 2 = z.weights 1
        rw [hweights, hweights]; simp
      · change (z.map (1 : Fin 3).succAbove).weights 2 = z.weights 1
        rw [hweights]; rfl
    have hA2 (z : StdSimplex ℝ (Fin 2)) : A (z.map (2 : Fin 3).succAbove) = (coord z, 0) := by
      apply Prod.ext <;> apply Subtype.ext
      · change (z.map (2 : Fin 3).succAbove).weights 1 + (z.map (2 : Fin 3).succAbove).weights 2 = z.weights 1
        rw [hweights, hweights]; simp
      · change (z.map (2 : Fin 3).succAbove).weights 2 = 0
        rw [hweights]; rfl
    have hB0 (z : StdSimplex ℝ (Fin 2)) : B (z.map (0 : Fin 3).succAbove) = (coord z, 1) := by
      apply Prod.ext <;> apply Subtype.ext
      · change (z.map (0 : Fin 3).succAbove).weights 2 = z.weights 1
        rw [hweights]; rfl
      · change (z.map (0 : Fin 3).succAbove).weights 1 + (z.map (0 : Fin 3).succAbove).weights 2 = 1
        rw [hweights, hweights]; exact hsum z
    have hB1 (z : StdSimplex ℝ (Fin 2)) : B (z.map (1 : Fin 3).succAbove) = (coord z, coord z) := by
      apply Prod.ext <;> apply Subtype.ext
      · change (z.map (1 : Fin 3).succAbove).weights 2 = z.weights 1
        rw [hweights]; rfl
      · change (z.map (1 : Fin 3).succAbove).weights 1 + (z.map (1 : Fin 3).succAbove).weights 2 = z.weights 1
        rw [hweights, hweights]; simp
    have hB2 (z : StdSimplex ℝ (Fin 2)) : B (z.map (2 : Fin 3).succAbove) = (0, coord z) := by
      apply Prod.ext <;> apply Subtype.ext
      · change (z.map (2 : Fin 3).succAbove).weights 2 = 0
        rw [hweights]; rfl
      · change (z.map (2 : Fin 3).succAbove).weights 1 + (z.map (2 : Fin 3).succAbove).weights 2 = z.weights 1
        rw [hweights, hweights]; simp
    let τA : Sing 2 := (TopCat.toSSetObjEquiv T (.op ⦋2⦌)).symm
      (F.toHomotopy.toContinuousMap.comp A)
    let τB : Sing 2 := (TopCat.toSSetObjEquiv T (.op ⦋2⦌)).symm
      (F.toHomotopy.toContinuousMap.comp B)
    let diag : Sing 1 := (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).symm
      ⟨fun z => F (coord z, coord z), F.continuous.comp (coord.continuous.prodMk coord.continuous)⟩
    have hfA (i : Fin 3) : (TopCat.toSSet.obj T).δ i τA =
        if i = 0 then pathSing q else if i = 1 then diag else pathSing (Path.refl a) := by
      fin_cases i
      all_goals apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
      all_goals apply ContinuousMap.ext
      all_goals intro z
      · change F (A (z.map (0 : Fin 3).succAbove)) = q (coord z)
        rw [hA0]
        exact F.toHomotopy.apply_one (coord z)
      · change F (A (z.map (1 : Fin 3).succAbove)) = F (coord z, coord z)
        rw [hA1]
      · change F (A (z.map (2 : Fin 3).succAbove)) = a
        rw [hA2, Path.Homotopy.source]
    have hfB (i : Fin 3) : (TopCat.toSSet.obj T).δ i τB =
        if i = 0 then pathSing (Path.refl a) else if i = 1 then diag else pathSing p := by
      fin_cases i
      all_goals apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
      all_goals apply ContinuousMap.ext
      all_goals intro z
      · change F (B (z.map (0 : Fin 3).succAbove)) = a
        rw [hB0, Path.Homotopy.target]
      · change F (B (z.map (1 : Fin 3).succAbove)) = F (coord z, coord z)
        rw [hB1]
      · change F (B (z.map (2 : Fin 3).succAbove)) = p (coord z)
        rw [hB2]
        exact F.toHomotopy.apply_zero (coord z)
    have hA := hboundary (Finsupp.single τA 1)
    have hB := hboundary (Finsupp.single τB 1)
    rw [singularBoundaryFinsupp_single] at hA hB
    simp_rw [hfA] at hA
    simp_rw [hfB] at hB
    norm_num [Fin.sum_univ_succ] at hA hB
    have hh := sub_eq_zero.mpr (hA.trans hB.symm)
    have he : value q - value p = 0 := by
      calc value q - value p =
          (π (Finsupp.single (pathSing q) 1) +
            (-π (Finsupp.single diag 1) + π (Finsupp.single (pathSing (Path.refl a)) 1))) -
          (π (Finsupp.single (pathSing (Path.refl a)) 1) +
            (-π (Finsupp.single diag 1) + π (Finsupp.single (pathSing p) 1))) := by
              dsimp [value]
              abel
        _ = 0 := hh
    exact (sub_eq_zero.mp he).symm

  have hsymm {a b : X} (p : Path a b) : value p.symm = -value p := by
    have hh := hhomotopic (p.trans p.symm) (Path.refl a) (Path.Homotopic.trans_symm p)
    rw [hconcat, hconst] at hh
    rw [add_comm] at hh
    exact eq_neg_of_add_eq_zero_left hh
  let φ : FundamentalGroup X x → C.opcycles 1 :=
    _root_.Quotient.lift (fun p : Path x x => value p) (fun p q h => hhomotopic p q h)
  have hφ (p : Path x x) : φ (Path.Homotopic.Quotient.mk p) = value p := rfl
  let G : AddSubgroup (C.opcycles 1) := {
    carrier := Set.range φ
    zero_mem' := ⟨Path.Homotopic.Quotient.mk (Path.refl x), hconst x⟩
    add_mem' := by
      rintro y z ⟨p, rfl⟩ ⟨q, rfl⟩
      induction p using Path.Homotopic.Quotient.ind with | mk p =>
      induction q using Path.Homotopic.Quotient.ind with | mk q =>
      exact ⟨Path.Homotopic.Quotient.mk (p.trans q), hconcat p q⟩
    neg_mem' := by
      rintro y ⟨p, rfl⟩
      induction p using Path.Homotopic.Quotient.ind with | mk p =>
      exact ⟨Path.Homotopic.Quotient.mk p.symm, hsymm p⟩ }
  have hGfinite : Finite G := by
    apply Finite.of_surjective (fun p : FundamentalGroup X x => (⟨φ p, ⟨p, rfl⟩⟩ : G))
    rintro ⟨y, p, hp⟩
    exact ⟨p, Subtype.ext hp⟩
  let basePath (a : X) : Path x a := PathConnectedSpace.somePath x a

  let vertex (σ : Sing 0) : X :=
    (TopCat.toSSetObjEquiv T (.op ⦋0⦌) σ) (.single 0)
  let edge (σ : Sing 1) : Path
      ((TopCat.toSSetObjEquiv T (.op ⦋1⦌) σ) (.single 0))
      ((TopCat.toSSetObjEquiv T (.op ⦋1⦌) σ) (.single 1)) := {
    toContinuousMap := (TopCat.toSSetObjEquiv T (.op ⦋1⦌) σ).comp
      ⟨StdSimplex.homeomorphI.symm, StdSimplex.homeomorphI.symm.continuous⟩
    source' := by simp
    target' := by simp }
  have hedge (σ : Sing 1) : pathSing (edge σ) = σ := by
    apply (TopCat.toSSetObjEquiv T (.op ⦋1⦌)).injective
    apply ContinuousMap.ext
    intro z
    change (TopCat.toSSetObjEquiv T (.op ⦋1⦌) σ)
      (StdSimplex.homeomorphI.symm (coord z)) = _
    have hc : coord z = StdSimplex.homeomorphI z := Subtype.ext rfl
    rw [hc, Homeomorph.symm_apply_apply]
  let loop (σ : Sing 1) : Path x x :=
    ((basePath _).trans (edge σ)).trans (basePath _).symm
  let ψ : (Sing 0 →₀ ℤ) →ₗ[ℤ] C.opcycles 1 :=
    Finsupp.linearCombination ℤ (fun σ => value (basePath (vertex σ)))
  let Λ : (Sing 1 →₀ ℤ) →ₗ[ℤ] C.opcycles 1 :=
    Finsupp.linearCombination ℤ (fun σ => value (loop σ))
  have hvertex0 (σ : Sing 1) : vertex ((TopCat.toSSet.obj T).δ 0 σ) =
      (TopCat.toSSetObjEquiv T (.op ⦋1⦌) σ) (.single 1) := by
    change (TopCat.toSSetObjEquiv T (.op ⦋1⦌) σ)
      ((StdSimplex.single (0 : Fin 1)).map (0 : Fin 2).succAbove) = _
    congr 1
    simp [StdSimplex.map_single, Fin.succAbove]
  have hvertex1 (σ : Sing 1) : vertex ((TopCat.toSSet.obj T).δ 1 σ) =
      (TopCat.toSSetObjEquiv T (.op ⦋1⦌) σ) (.single 0) := by
    change (TopCat.toSSetObjEquiv T (.op ⦋1⦌) σ)
      ((StdSimplex.single (0 : Fin 1)).map (1 : Fin 2).succAbove) = _
    congr 1
    simp [StdSimplex.map_single, Fin.succAbove]
  have hΛsingle (σ : Sing 1) : Λ (Finsupp.single σ (1 : ℤ)) = value (loop σ) := by
    simp only [Λ, Finsupp.linearCombination_single]
    exact (C.opcycles 1).isModule.one_smul (value (loop σ))
  have hψsingle (σ : Sing 0) : ψ (Finsupp.single σ (1 : ℤ)) = value (basePath (vertex σ)) := by
    simp only [ψ, Finsupp.linearCombination_single]
    exact (C.opcycles 1).isModule.one_smul (value (basePath (vertex σ)))
  have hSourceValue (σ : Sing 1) : value (basePath (vertex ((TopCat.toSSet.obj T).δ 0 σ))) =
      value (basePath ((TopCat.toSSetObjEquiv T (.op ⦋1⦌) σ) (.single 1))) :=
    congrArg (fun z : X => value (basePath z)) (hvertex0 σ)
  have hTargetValue (σ : Sing 1) : value (basePath (vertex ((TopCat.toSSet.obj T).δ 1 σ))) =
      value (basePath ((TopCat.toSSetObjEquiv T (.op ⦋1⦌) σ) (.single 0))) :=
    congrArg (fun z : X => value (basePath z)) (hvertex1 σ)
  have hΛ : Λ = π - ψ.comp (singularBoundaryFinsupp T 0) := by
    apply Finsupp.lhom_ext
    intro σ n
    have hone : Λ (Finsupp.single σ (1 : ℤ)) =
        π (Finsupp.single σ 1) - ψ (singularBoundaryFinsupp T 0 (Finsupp.single σ 1)) := by
      rw [hΛsingle]
      dsimp [loop]
      rw [hconcat, hconcat, hsymm]
      have he : value (edge σ) = π (Finsupp.single σ 1) := by
        dsimp [value]
        rw [hedge]
      rw [he]
      have hb : singularBoundaryFinsupp T 0 (Finsupp.single σ (1 : ℤ)) =
          Finsupp.single ((TopCat.toSSet.obj T).δ 0 σ) 1 -
          Finsupp.single ((TopCat.toSSet.obj T).δ 1 σ) 1 := by
        rw [singularBoundaryFinsupp_single]
        norm_num [Fin.sum_univ_succ, neg_one_smul, one_smul]
        abel
      rw [hb, map_sub, hψsingle, hψsingle, hSourceValue, hTargetValue]
      abel
    have hn : Finsupp.single σ n = n • Finsupp.single σ (1 : ℤ) := by simp
    rw [hn]
    change Λ (n • Finsupp.single σ 1) = π (n • Finsupp.single σ 1) -
      ψ (singularBoundaryFinsupp T 0 (n • Finsupp.single σ 1))
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, hone]
    exact smul_sub _ _ _
  have hΛmem (c : Sing 1 →₀ ℤ) : Λ c ∈ G := by
    change Finsupp.linearCombination ℤ (fun σ => value (loop σ)) c ∈ G
    rw [Finsupp.linearCombination_apply]
    apply G.sum_mem
    intro σ hσ
    have hm : value (loop σ) ∈ G := ⟨Path.Homotopic.Quotient.mk (loop σ), rfl⟩
    convert G.zsmul_mem hm (c σ) using 1
    exact int_smul_eq_zsmul (C.opcycles 1).isModule (c σ) (value (loop σ))
  have hcyclemem (c : C.cycles 1) : π ((C.iCycles 1) c) ∈ G := by
    have hz : singularBoundaryFinsupp T 0 ((C.iCycles 1) c) = 0 :=
      congrArg (fun f => f c) (C.iCycles_d 1 0)
    let cc : Sing 1 →₀ ℤ := (C.iCycles 1) c
    have hh : Λ cc = π cc := by
      have he := LinearMap.congr_fun hΛ cc
      change Λ cc = π cc - ψ (singularBoundaryFinsupp T 0 cc) at he
      rw [show singularBoundaryFinsupp T 0 cc = 0 from hz, map_zero, sub_zero] at he
      exact he
    exact hh ▸ hΛmem cc
  have hhommem (h : C.homology 1) : (C.homologyι 1) h ∈ G := by
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ 1)).mp inferInstance h
    have hh := congrArg (fun f => f c) (C.homology_π_ι 1)
    change (C.homologyι 1) ((C.homologyπ 1) c) = π ((C.iCycles 1) c) at hh
    exact hh.symm ▸ hcyclemem c
  letI : Finite G := hGfinite
  letI : Finite (C.homology 1) :=
    Finite.of_injective (fun h => (⟨(C.homologyι 1) h, hhommem h⟩ : G)) (by
      intro h k he
      apply (ModuleCat.mono_iff_injective (C.homologyι 1)).mp inferInstance
      exact congrArg Subtype.val he)
  let e := singularHomologyRepresentation T 1
  exact Finite.of_surjective e.hom (fun h => ⟨e.inv h, by
    have hh := congrArg (fun f => f h) e.inv_hom_id
    exact hh⟩)


end CurveComplex.LocalSurgery
