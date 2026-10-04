import CurveComplexGenusTwo.Octagon.GraphMV.GraphCoverBasic
import Mathlib.Analysis.Convex.Contractible
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers

noncomputable section
open CategoryTheory CategoryTheory.Limits ContinuousMap CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.Octagon.AttachingMap.GraphMV

private abbrev Overlap := vertexStar ∩ edgeMiddles
private abbrev OverlapParams := graphEdgeMap ⁻¹' Overlap
private abbrev ShortInterval := Set.Ioo (1/4 : ℝ) (3/8 : ℝ)

private def lowParams : Set OverlapParams :=
  {p | (p.1.2 : ℝ) < 3/8}

private theorem lowParams_open : IsOpen lowParams := by
  let f : OverlapParams → ℝ := fun p => p.1.2
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val
  change IsOpen (f ⁻¹' Set.Iio (3/8 : ℝ))
  exact isOpen_Iio.preimage hf

private theorem lowParams_compl_open : IsOpen lowParamsᶜ := by
  let f : OverlapParams → ℝ := fun p => p.1.2
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val
  have heq : lowParamsᶜ = f ⁻¹' Set.Ioi (5/8 : ℝ) := by
    ext p
    have hh : (p.1.2 : ℝ) < 3/8 ∨ 5/8 < (p.1.2 : ℝ) :=
      (Set.ext_iff.mp vertexStar_preimage p.1).mp p.2.1
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Ioi,
      lowParams, Set.mem_ofPred_eq]
    constructor
    · intro hn
      rcases hh with hl | hr
      · exact False.elim (hn hl)
      · exact hr
    · intro hr hl
      linarith
  rw [heq]
  exact isOpen_Ioi.preimage hf

private def splitClopen {X : Type*} [TopologicalSpace X]
    (s : Set X) (hs : IsOpen s) (hc : IsOpen sᶜ) : X ≃ₜ ↥s ⊕ ↥sᶜ := by
  classical
  let e := Equiv.Set.sumCompl s
  exact (e.toHomeomorphOfContinuousOpen
    (continuous_subtype_val.sumElim continuous_subtype_val)
    (isOpenMap_sumElim.mpr
      ⟨hs.isOpenMap_subtype_val, hc.isOpenMap_subtype_val⟩)).symm

private def lowParamsChart : lowParams ≃ₜ (Fin 4 × ShortInterval) where
  toFun p := (p.1.1.1, ⟨p.1.1.2.1, by
    constructor
    · exact ((Set.ext_iff.mp edgeMiddles_preimage p.1.1).mp p.1.2.2).1
    · exact p.2⟩)
  invFun q :=
    ⟨⟨(q.1, ⟨q.2.1, by
      constructor <;> linarith [q.2.2.1, q.2.2.2]⟩), by
      constructor
      · exact ⟨q.1, ⟨q.2.1, by
          constructor <;> linarith [q.2.2.1, q.2.2.2]⟩,
          rfl, Or.inl q.2.2.2⟩
      · exact ⟨q.1, ⟨q.2.1, by
          constructor <;> linarith [q.2.2.1, q.2.2.2]⟩,
          rfl, q.2.2.1, by linarith [q.2.2.2]⟩⟩,
      q.2.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  right_inv q := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def highParamsChart : ↥(lowParamsᶜ) ≃ₜ (Fin 4 × ShortInterval) where
  toFun p := (p.1.1.1, ⟨1 - p.1.1.2.1, by
    have hh : 5/8 < (p.1.1.2 : ℝ) := by
      have hx := (Set.ext_iff.mp vertexStar_preimage p.1.1).mp p.1.2.1
      rcases hx with hlo | hhi
      · exact False.elim (p.2 hlo)
      · exact hhi
    have hm := (Set.ext_iff.mp edgeMiddles_preimage p.1.1).mp p.1.2.2
    constructor <;> dsimp <;> linarith [hh, hm.2]⟩)
  invFun q :=
    ⟨⟨(q.1, ⟨1 - q.2.1, by
      constructor <;> linarith [q.2.2.1, q.2.2.2]⟩), by
      constructor
      · exact ⟨q.1, ⟨1 - q.2.1, by
          constructor <;> linarith [q.2.2.1, q.2.2.2]⟩,
          rfl, Or.inr (by linarith [q.2.2.2])⟩
      · exact ⟨q.1, ⟨1 - q.2.1, by
          constructor <;> linarith [q.2.2.1, q.2.2.2]⟩,
          rfl, by linarith [q.2.2.2], by linarith [q.2.2.1]⟩⟩,
      by change ¬ (1 - (q.2.1 : ℝ)) < 3/8
         linarith [q.2.2.2]⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp
      ring
  right_inv q := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp
      ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def splitIndexEquiv : (Fin 4 ⊕ Fin 4) ≃ (Fin 4 × Bool) where
  toFun := fun x => match x with
    | .inl i => (i, false)
    | .inr i => (i, true)
  invFun := fun p => if p.2 then .inr p.1 else .inl p.1
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    rintro ⟨i,b⟩
    cases b <;> rfl

private def splitToProduct :
    ((Fin 4 × ShortInterval) ⊕ (Fin 4 × ShortInterval)) ≃ₜ
      (Fin 4 × Bool × ShortInterval) :=
  ((Homeomorph.sumProdDistrib.symm).trans
    (splitIndexEquiv.toHomeomorphOfDiscrete.prodCongr
      (Homeomorph.refl ShortInterval))).trans
        (Homeomorph.prodAssoc (Fin 4) Bool ShortInterval)

def overlapIntervalChart :
    Overlap ≃ₜ (Fin 4 × Bool × ShortInterval) :=
  overlapQuotientChart.symm |>.trans
    ((splitClopen lowParams lowParams_open lowParams_compl_open).trans
      ((Homeomorph.sumCongr lowParamsChart highParamsChart).trans splitToProduct))

def overlapHomotopyFinBool : Overlap ≃ₕ (Fin 4 × Bool) := by
  have hc : Convex ℝ (Set.Ioo (1/4 : ℝ) (3/8 : ℝ)) := convex_Ioo _ _
  have hne : (Set.Ioo (1/4 : ℝ) (3/8 : ℝ)).Nonempty :=
    ⟨5/16, by constructor <;> norm_num⟩
  haveI : ContractibleSpace ShortInterval := hc.contractibleSpace hne
  exact overlapIntervalChart.toHomotopyEquiv |>.trans
    ((Homeomorph.prodAssoc (Fin 4) Bool ShortInterval).symm.toHomotopyEquiv.trans
      (((ContinuousMap.HomotopyEquiv.refl (Fin 4 × Bool)).prodCongr
        (ContractibleSpace.hequiv_unit ShortInterval).some).trans
          (Homeomorph.prodUnique (Fin 4 × Bool) Unit).toHomotopyEquiv))

theorem overlap_positive_homology (n : ℕ) (hn : 0 < n) :
    IsZero (H Overlap n) := by
  exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (Fin 4 × Bool)) (by omega)).of_iso
      (homotopyHomologyIso overlapHomotopyFinBool n)

theorem overlap_chart_index_public (x : ↥(vertexStar ∩ edgeMiddles)) :
    (overlapIntervalChart x).1 = (overlapQuotientChart.symm x).1.1 := by
  classical
  let y := overlapQuotientChart.symm x
  change (overlapIntervalChart x).1 = y.1.1
  change (splitToProduct
    ((Homeomorph.sumCongr lowParamsChart highParamsChart)
      ((splitClopen lowParams lowParams_open lowParams_compl_open) y))).1 = y.1.1
  by_cases h : y ∈ lowParams
  · have hs : (splitClopen lowParams lowParams_open lowParams_compl_open) y =
        Sum.inl ⟨y, h⟩ := by
      change (Equiv.Set.sumCompl lowParams).symm y = _
      exact Equiv.Set.sumCompl_symm_apply_of_mem h
    rw [hs]
    rfl

  · have hs : (splitClopen lowParams lowParams_open lowParams_compl_open) y =
        Sum.inr ⟨y, h⟩ := by
      change (Equiv.Set.sumCompl lowParams).symm y = _
      exact Equiv.Set.sumCompl_symm_apply_of_notMem h
    rw [hs]
    rfl

#print axioms overlap_positive_homology
#print axioms overlap_chart_index_public

end CurveComplex.Octagon.AttachingMap.GraphMV
