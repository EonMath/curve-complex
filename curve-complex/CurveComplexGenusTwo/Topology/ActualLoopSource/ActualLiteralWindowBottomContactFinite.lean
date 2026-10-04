import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMarkedArcCompactContactCore
import Mathlib.Data.Set.Finite.Basic
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- A literal original-b interior window is embedded and has finite actual
old-a contacts, using the source collision property and original crossings. -/
theorem actual_literal_window_bottom_contact_finite
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (K G : C(Interval × Interval,S))
    (hzero : ∀ t,K (0,t)=b.val.map t)
    (hcollision : ∀ s t,K (0,s)=K (0,t) → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (φ : C(Interval,Interval)) (hφ : IsEmbedding φ)
    (hφbounds : ∀ t,0<(φ t:ℝ) ∧ (φ t:ℝ)<1)
    (hbottom : ∀ t,G (0,t)=b.val.map (φ t))
    (hmarks : ∀ t,G (0,t) ∉ (M.cover.branch : Set S))
    (hfinite : (ArcSurgery.crossings M a b).Finite) :
    IsEmbedding (fun t => G (0,t)) ∧ {t : Interval | G (0,t) ∈ a.val.image}.Finite := by
  let : T2Space S := M.sphere.symm.t2Space
  have hinj : Function.Injective (fun t => G (0,t)) := by
    intro s t he
    have hK : K (0,φ s)=K (0,φ t) := by rw [hzero,hzero,← hbottom,← hbottom]; exact he
    rcases hcollision (φ s) (φ t) hK with he | he | he
    · exact hφ.injective he
    · have hh := congrArg Subtype.val he.1
      change (φ s:ℝ)=0 at hh
      exact False.elim ((hφbounds s).1.ne' hh)
    · have hh := congrArg Subtype.val he.1
      change (φ s:ℝ)=1 at hh
      exact False.elim ((hφbounds s).2.ne hh)
  have hpre : ((fun t => G (0,t)) ⁻¹' ArcSurgery.crossings M a b).Finite :=
    Set.Finite.preimage (fun s _ t _ he => hinj he) hfinite
  refine ⟨((G.continuous.comp (continuous_const.prodMk continuous_id)).isClosedEmbedding hinj).isEmbedding,?_⟩
  apply hpre.subset
  intro t ht
  have hm := hmarks t
  change G (0,t) ∈ ArcSurgery.crossings M a b
  refine ⟨⟨ht,hm⟩,?_,hm⟩
  rw [hbottom]
  exact mem_range_self (φ t)
end CurveComplex.HyperellipticModel
