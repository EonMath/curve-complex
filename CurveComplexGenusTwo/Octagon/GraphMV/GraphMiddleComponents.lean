import CurveComplexGenusTwo.Octagon.GraphMV.GraphCoverBasic
import Mathlib.Analysis.Convex.Contractible
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers

noncomputable section
namespace CurveComplex.Octagon.AttachingMap.GraphMV
open CategoryTheory CategoryTheory.Limits ContinuousMap CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz

private abbrev MiddleParams := graphEdgeMap ⁻¹' edgeMiddles
private abbrev MiddleInterval := Set.Ioo (1/4 : ℝ) (3/4 : ℝ)

/-- Four interval coordinates on the literal middle-edge parameter domain. -/
def middleParameterChart : MiddleParams ≃ₜ (Fin 4 × MiddleInterval) where
  toFun a := (a.1.1, ⟨a.1.2.1, (Set.ext_iff.mp edgeMiddles_preimage a.1).mp a.2⟩)
  invFun p := ⟨(p.1, ⟨p.2.1, by constructor <;> linarith [p.2.2.1, p.2.2.2]⟩),
    (Set.ext_iff.mp edgeMiddles_preimage _).mpr p.2.2⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Explicit four-component homeomorphism of the actual middle set. -/
def edgeMiddlesIntervalChart : edgeMiddles ≃ₜ (Fin 4 × MiddleInterval) :=
  edgeMiddlesQuotientChart.symm.trans middleParameterChart

def edgeComponent (i : Fin 4) : Set edgeMiddles :=
  {x | (edgeMiddlesIntervalChart x).1 = i}

def edgeComponentIntervalChart (i : Fin 4) : edgeComponent i ≃ₜ MiddleInterval where
  toFun x := (edgeMiddlesIntervalChart x.1).2
  invFun t := ⟨edgeMiddlesIntervalChart.symm (i, t), by simp [edgeComponent]⟩
  left_inv x := by
    apply Subtype.ext
    apply edgeMiddlesIntervalChart.injective
    change edgeMiddlesIntervalChart
      (edgeMiddlesIntervalChart.symm (i, (edgeMiddlesIntervalChart x.1).2)) =
        edgeMiddlesIntervalChart x.1
    rw [edgeMiddlesIntervalChart.apply_symm_apply]
    exact Prod.ext x.2.symm rfl
  right_inv t := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem edge_component_contractible (i : Fin 4) :
    ContractibleSpace (edgeComponent i) := by
  have hc : Convex ℝ (Set.Ioo (1/4 : ℝ) (3/4 : ℝ)) := convex_Ioo _ _
  have hne : (Set.Ioo (1/4 : ℝ) (3/4 : ℝ)).Nonempty :=
    ⟨1/2, by constructor <;> norm_num⟩
  haveI : ContractibleSpace MiddleInterval := hc.contractibleSpace hne
  exact (edgeComponentIntervalChart i).contractibleSpace

def edgeMiddlesHomotopyFin : edgeMiddles ≃ₕ Fin 4 := by
  have hc : Convex ℝ (Set.Ioo (1/4 : ℝ) (3/4 : ℝ)) := convex_Ioo _ _
  have hne : (Set.Ioo (1/4 : ℝ) (3/4 : ℝ)).Nonempty :=
    ⟨1/2, by constructor <;> norm_num⟩
  haveI : ContractibleSpace MiddleInterval := hc.contractibleSpace hne
  exact edgeMiddlesIntervalChart.toHomotopyEquiv |>.trans
    (((ContinuousMap.HomotopyEquiv.refl (Fin 4)).prodCongr
      (ContractibleSpace.hequiv_unit MiddleInterval).some).trans
        (Homeomorph.prodUnique (Fin 4) Unit).toHomotopyEquiv)

theorem edgeMiddles_positive_homology (n : ℕ) (hn : 0 < n) :
    IsZero (H edgeMiddles n) := by
  exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (Fin 4)) (by omega)).of_iso
      (homotopyHomologyIso edgeMiddlesHomotopyFin n)

end CurveComplex.Octagon.AttachingMap.GraphMV

#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.edge_component_contractible
#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.edgeMiddles_positive_homology
