import CurveComplexGenusTwo.Octagon.GraphMV.GraphCoverBasic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Piecewise

noncomputable section
set_option maxHeartbeats 800000
namespace CurveComplex.Octagon.AttachingMap.GraphMV

private abbrev StarParams := graphEdgeMap ⁻¹' vertexStar

private def lowStarParams : Set StarParams :=
  {p | (p.1.2 : ℝ) < 3/8}

private theorem lowStarParams_clopen : IsClopen lowStarParams := by
  have hf : Continuous (fun p : StarParams => (p.1.2 : ℝ)) := by fun_prop
  constructor
  · apply isOpen_compl_iff.mp
    have h : lowStarParamsᶜ = {p : StarParams | 5/8 < (p.1.2 : ℝ)} := by
      ext p
      have hp := (Set.ext_iff.mp vertexStar_preimage p.1).mp p.2
      change ¬((p.1.2 : ℝ) < 3/8) ↔ 5/8 < (p.1.2 : ℝ)
      rcases hp with hp | hp <;> constructor <;> intro h <;> linarith
    rw [h]
    exact isOpen_Ioi.preimage hf
  · exact isOpen_Iio.preimage hf

private def starParam (s : unitInterval) (p : StarParams) : unitInterval :=
  if (p.1.2 : ℝ) < 3/8 then unitInterval.symm s * p.1.2
  else unitInterval.symm (unitInterval.symm s * unitInterval.symm p.1.2)

private theorem starParam_zero (p : StarParams) : starParam 0 p = p.1.2 := by
  unfold starParam
  split_ifs <;> simp

private theorem starParam_one (p : StarParams) :
    starParam 1 p = (if (p.1.2 : ℝ) < 3/8 then 0 else 1) := by
  unfold starParam
  split_ifs <;> simp

private theorem starParam_continuous :
    Continuous (fun z : StarParams × unitInterval => starParam z.2 z.1) := by
  let s : Set (StarParams × unitInterval) :=
    {z | (z.1.1.2 : ℝ) < 3/8}
  have hs : IsClopen s := lowStarParams_clopen.preimage continuous_fst
  have h₁ : Continuous (fun z : StarParams × unitInterval =>
      unitInterval.symm z.2 * z.1.1.2) := by fun_prop
  have h₂ : Continuous (fun z : StarParams × unitInterval =>
      unitInterval.symm (unitInterval.symm z.2 * unitInterval.symm z.1.1.2)) := by
    fun_prop
  have h := continuous_if (p := fun z : StarParams × unitInterval => z ∈ s)
    (f := fun z => unitInterval.symm z.2 * z.1.1.2)
    (g := fun z => unitInterval.symm (unitInterval.symm z.2 * unitInterval.symm z.1.1.2))
    (by simp [hs.frontier_eq]) h₁.continuousOn h₂.continuousOn
  simpa [starParam, s] using h

private theorem starParam_mem (s : unitInterval) (p : StarParams) :
    graphEdgeMap (p.1.1, starParam s p) ∈ vertexStar := by
  have hp := (Set.ext_iff.mp vertexStar_preimage p.1).mp p.2
  by_cases hlo : (p.1.2 : ℝ) < 3/8
  · have hval : ((starParam s p : unitInterval) : ℝ) =
        (1 - (s : ℝ)) * (p.1.2 : ℝ) := by
      simp [starParam, hlo, unitInterval.coe_symm_eq]
    refine ⟨p.1.1, starParam s p, rfl, Or.inl ?_⟩
    rw [hval]
    have hs := s.2.1
    have ht := p.1.2.2.1
    nlinarith [mul_nonneg hs ht]
  · have hhi : 5/8 < (p.1.2 : ℝ) := hp.resolve_left hlo
    have hval : ((starParam s p : unitInterval) : ℝ) =
        1 - (1 - (s : ℝ)) * (1 - (p.1.2 : ℝ)) := by
      simp [starParam, hlo, unitInterval.coe_symm_eq]
    refine ⟨p.1.1, starParam s p, rfl, Or.inr ?_⟩
    rw [hval]
    have hs := s.2.1
    have ht := p.1.2.2.2
    nlinarith [mul_nonneg hs (sub_nonneg.mpr ht)]

private theorem starParam_endpoint (s : unitInterval) (p : StarParams)
    (hp : p.1.2 = 0 ∨ p.1.2 = 1) :
    starParam s p = 0 ∨ starParam s p = 1 := by
  rcases hp with hp | hp
  · left
    simp [starParam, hp]
  · right
    norm_num [starParam, hp]

private def starQ : StarParams → vertexStar :=
  vertexStar.restrictPreimage graphEdgeMap

private theorem starQ_quotient : Topology.IsQuotientMap starQ :=
  graphEdgeMap_isQuotientMap.restrictPreimage_isOpen vertexStar_open

private theorem starParam_fiber (s : unitInterval) (p q : StarParams)
    (h : starQ p = starQ q) :
    graphEdgeMap (p.1.1, starParam s p) =
      graphEdgeMap (q.1.1, starParam s q) := by
  have h' : graphEdgeMap p.1 = graphEdgeMap q.1 := congrArg Subtype.val h
  rcases (graphEdgeMap_fiber p.1.1 q.1.1 p.1.2 q.1.2).mp h' with
    ⟨hidx, ht⟩ | ⟨hp, hq⟩
  · have heq : p = q := Subtype.ext (Prod.ext hidx ht)
    rw [heq]
  · apply (graphEdgeMap_fiber p.1.1 q.1.1 (starParam s p) (starParam s q)).mpr
    exact Or.inr ⟨starParam_endpoint s p hp, starParam_endpoint s q hq⟩

private def starParameterHomotopy : C(StarParams × unitInterval, vertexStar) where
  toFun z := ⟨graphEdgeMap (z.1.1.1, starParam z.2 z.1), starParam_mem z.2 z.1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply graphEdgeMap.continuous.comp
    apply Continuous.prodMk
    · fun_prop
    · exact starParam_continuous

private noncomputable def starHomotopyFun (z : vertexStar × unitInterval) : vertexStar :=
  starParameterHomotopy (Function.surjInv starQ_quotient.surjective z.1, z.2)

private theorem starHomotopyFun_factor (p : StarParams) (s : unitInterval) :
    starHomotopyFun (starQ p, s) = starParameterHomotopy (p, s) := by
  apply Subtype.ext
  change graphEdgeMap
    ((Function.surjInv starQ_quotient.surjective (starQ p)).1.1,
      starParam s (Function.surjInv starQ_quotient.surjective (starQ p))) =
      graphEdgeMap (p.1.1, starParam s p)
  apply starParam_fiber s
  exact Function.rightInverse_surjInv starQ_quotient.surjective (starQ p)

private theorem starHomotopyFun_continuous : Continuous starHomotopyFun := by
  apply starQ_quotient.continuous_lift_prod_left
  have h : (fun z : StarParams × unitInterval =>
      starHomotopyFun (starQ z.1, z.2)) = starParameterHomotopy := by
    funext z
    exact starHomotopyFun_factor z.1 z.2
  rw [h]
  exact starParameterHomotopy.continuous

private theorem graphEdgeMap_endpoint (i : Fin 4) (t : unitInterval)
    (ht : t = 0 ∨ t = 1) : graphEdgeMap (i, t) = base := by
  rcases ht with ht | ht
  · subst t
    exact (sideLoop (graphEdgeIndex i)).source
  · subst t
    exact (sideLoop (graphEdgeIndex i)).target

private theorem starHomotopyFun_zero (x : vertexStar) :
    starHomotopyFun (x, 0) = x := by
  let p := Function.surjInv starQ_quotient.surjective x
  have hp : starQ p = x := Function.rightInverse_surjInv starQ_quotient.surjective x
  apply Subtype.ext
  change graphEdgeMap (p.1.1, starParam 0 p) = x.1
  rw [starParam_zero]
  exact congrArg Subtype.val hp

private theorem starHomotopyFun_one (x : vertexStar) :
    starHomotopyFun (x, 1) = ⟨base, base_mem_vertexStar⟩ := by
  let p := Function.surjInv starQ_quotient.surjective x
  apply Subtype.ext
  change graphEdgeMap (p.1.1, starParam 1 p) = base
  apply graphEdgeMap_endpoint
  rw [starParam_one]
  split_ifs <;> simp

def vertexStarContraction :
    ContinuousMap.Homotopy (ContinuousMap.id vertexStar)
      (ContinuousMap.const vertexStar ⟨base, base_mem_vertexStar⟩) where
  toFun z := starHomotopyFun (z.2, z.1)
  continuous_toFun := starHomotopyFun_continuous.comp continuous_swap
  map_zero_left x := starHomotopyFun_zero x
  map_one_left x := starHomotopyFun_one x

theorem vertexStar_contractible : ContractibleSpace vertexStar := by
  exact (contractible_iff_id_nullhomotopic vertexStar).mpr
    ⟨⟨base, base_mem_vertexStar⟩, ⟨vertexStarContraction⟩⟩

end CurveComplex.Octagon.AttachingMap.GraphMV

#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.vertexStar_contractible
