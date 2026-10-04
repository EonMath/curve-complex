import CurveComplexGenusTwo.Topology.WeightedSurgery.SupportedEndpointRotation
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
/-- Actual nonzero punctured movie coordinates construct a continuous
logarithm on the WHOLE positive germ rectangle. No logarithm or lift is
supplied. The fixed marked endpoint itself is excluded from the domain. -/
theorem actual_punctured_plane_germ_logarithm
    (g : C(unitInterval × unitInterval,Plane))
    (hnonzero : ∀ τ t, 0<t → g (τ,t)≠0) :
    ∃ L : C(unitInterval × Ioc (0:ℝ) 1,ℂ),
      ∀ z, Complex.exp (L z)=ArcFinitePosition.planeComplexLinearEquiv
        (g (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩)) := by
  let : ContractibleSpace (Ioc (0:ℝ) 1) :=
    (convex_Ioc (𝕜:=ℝ) (0:ℝ) 1).contractibleSpace ⟨1,by norm_num⟩
  let : LocallyPathConnectedSpace (Ioc (0:ℝ) 1) :=
    (convex_Ioc (𝕜:=ℝ) (0:ℝ) 1).locallyPathConnectedSpace
  let : ContractibleSpace unitInterval :=
    (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
  let : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).locallyPathConnectedSpace
  let param : C(Ioc (0:ℝ) 1,unitInterval) :=
    ⟨fun t => ⟨t.val,t.property.1.le,t.property.2⟩,by fun_prop⟩
  let c : C(unitInterval × Ioc (0:ℝ) 1,ℂ) :=
    ⟨fun z => ArcFinitePosition.planeComplexLinearEquiv (g (z.1,param z.2)),
      ArcFinitePosition.planeComplexLinearEquiv.continuous.comp
        (g.continuous.comp (continuous_fst.prodMk (param.continuous.comp continuous_snd)))⟩
  have hc (z : unitInterval × Ioc (0:ℝ) 1) : c z≠0 := by
    intro he
    apply hnonzero z.1 (param z.2) z.2.property.1
    exact ArcFinitePosition.planeComplexLinearEquiv.injective
      (he.trans ArcFinitePosition.planeComplexLinearEquiv.map_zero.symm)
  let cNZ : C(unitInterval × Ioc (0:ℝ) 1,{z : ℂ // z≠0}) :=
    ⟨fun z => ⟨c z,hc z⟩,c.continuous.subtype_mk hc⟩
  let base : unitInterval × Ioc (0:ℝ) 1 := (0,⟨1,by norm_num⟩)
  have hb : (⟨Complex.exp (Complex.log (c base)),Complex.exp_ne_zero _⟩ : {z : ℂ // z≠0})=cNZ base :=
    Subtype.ext (Complex.exp_log (hc base))
  obtain ⟨L,⟨_,hL⟩,_⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
    cNZ base (Complex.log (c base)) hb
  exact ⟨L,fun z => congrArg Subtype.val (congrFun hL z)⟩
end CurveComplex.HyperellipticModel
