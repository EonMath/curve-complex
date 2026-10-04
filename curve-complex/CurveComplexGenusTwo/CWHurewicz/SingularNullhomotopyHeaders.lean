import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

namespace CurveComplex.WeightedFlowScratch

open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem singularHomologyMap_zero_of_nullhomotopy {X Y : TopCat} (f : X ⟶ Y)
    (y : Y) (H : TopCat.Homotopy f (TopCat.ofHom (ContinuousMap.const X y)))
    (n : ℕ) (hn : 0 < n) :
    HomologicalComplex.homologyMap (singularFinsuppMap f) n = 0 := by
  let q : X ⟶ TopCat.of PUnit := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let p : TopCat.of PUnit ⟶ Y := TopCat.ofHom (ContinuousMap.const PUnit y)
  have hfactor : TopCat.ofHom (ContinuousMap.const X y) = q ≫ p := by
    ext x
    rfl
  have hpoint : IsZero ((actualSingularFunctor.obj (TopCat.of PUnit)).homology n) := by
    exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) (by omega)
  have hq : HomologicalComplex.homologyMap (actualSingularFunctor.map q) n = 0 :=
    hpoint.eq_of_tgt _ _
  have hzero : HomologicalComplex.homologyMap (actualSingularFunctor.map f) n = 0 := by
    rw [H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) n]
    rw [hfactor, actualSingularFunctor.map_comp, HomologicalComplex.homologyMap_comp, hq]
    exact zero_comp
  apply (cancel_mono (singularHomologyRepresentation Y n).hom).mp
  rw [singularHomologyRepresentation_naturality]
  change (singularHomologyRepresentation X n).hom ≫
    HomologicalComplex.homologyMap (actualSingularFunctor.map f) n = _
  rw [hzero]
  simp

theorem chainMap_cycle_fills_of_homologyMap_zero
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ L)
    (n : ℕ) (z : K.X n) (hz : (K.sc n).g z = 0)
    (hf : HomologicalComplex.homologyMap f n = 0) :
    ∃ b : L.X (n + 1), L.d (n + 1) n b = f.f n z := by
  let S := K.sc n
  let T := L.sc n
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map f
  let cz : LinearMap.ker S.g.hom := ⟨z, hz⟩
  have hzi : S.iCycles (S.moduleCatCyclesIso.inv cz) = z := by
    exact congrArg (fun g : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => g cz)
      S.moduleCatCyclesIso_inv_iCycles
  have h := congrArg
    (fun g : S.cycles ⟶ T.opcycles => g (S.moduleCatCyclesIso.inv cz))
    (ShortComplex.π_homologyMap_ι φ)
  have hf' : S.homologyMap φ = 0 := hf
  simp only [hf', comp_zero, zero_comp, ConcreteCategory.comp_apply] at h
  change (0 : T.opcycles) = T.pOpcycles (f.f n (S.iCycles (S.moduleCatCyclesIso.inv cz))) at h
  rw [hzi] at h
  have hb : f.f n z ∈ LinearMap.range T.f.hom :=
    (T.moduleCat_pOpcycles_eq_zero_iff _).mp h.symm
  obtain ⟨b, hb⟩ := hb
  have hb' : ∃ b : L.X ((ComplexShape.down ℕ).prev n),
      L.d ((ComplexShape.down ℕ).prev n) n b = f.f n z := ⟨b, hb⟩
  rw [ChainComplex.prev ℕ n] at hb'
  exact hb'

theorem singularFinsupp_cycle_fills_of_nullhomotopy {X Y : TopCat} (f : X ⟶ Y)
    (y : Y) (H : TopCat.Homotopy f (TopCat.ofHom (ContinuousMap.const X y)))
    (n : ℕ) (hn : 0 < n)
    (z : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ)
    (hz : z ∈ absoluteSingularCycles X n) :
    ∃ b : (TopCat.toSSet.obj Y) _⦋n + 1⦌ →₀ ℤ,
      singularBoundaryFinsupp Y n b = singularFinsuppPush f n z := by
  have hzsc : ((mvAmbientComplex X).sc n).g z = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    change (mvAmbientComplex X).d (k + 1) ((ComplexShape.down ℕ).next (k + 1)) z = 0
    rw [ChainComplex.next_nat_succ]
    simp only [mvAmbientComplex, ChainComplex.of_d]
    change singularBoundaryFinsupp X k z = 0
    exact LinearMap.mem_ker.mp hz
  obtain ⟨b, hb⟩ := chainMap_cycle_fills_of_homologyMap_zero (singularFinsuppMap f) n z hzsc
    (singularHomologyMap_zero_of_nullhomotopy f y H n hn)
  refine ⟨b, ?_⟩
  simp only [mvAmbientComplex, ChainComplex.of_d, singularFinsuppMap_f] at hb
  change singularBoundaryFinsupp Y n b = singularFinsuppPush f n z at hb
  exact hb

end CurveComplex.WeightedFlowScratch
