import CurveComplexGenusTwo.Filtration.ActualFiltrationEndpointProgress
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualRawSimultaneousCompatibleMinimum
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualSimplexInsertHeaders
import CurveComplexGenusTwo.Topology.ArcCounts.ActualFullACard12

namespace CurveComplex.HyperellipticModel
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance originalActualXSubcomplexDecidableEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

theorem actualX_subcomplex_actualA (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (hσ : σ ∈ actualX M) :
    σ ∈ actualA M := by
  classical
  by_cases hempty : σ.Nonempty
  · obtain ⟨v,hv⟩ := hempty
    obtain ⟨anchor,hanchor⟩ := Quotient.exists_rep v
    obtain ⟨r,hr,hf,ht,hd,hmin⟩ :=
      ArcSurgery.actual_raw_simultaneous_compatible_minimum_family M anchor σ
    change IsArcSimplex M σ
    refine ⟨r,hr,?_⟩
    intro v w hvw
    apply hd v w hvw
    have hvwval : v.val ≠ w.val := fun he => hvw (Subtype.ext he)
    obtain ⟨_,_,_,_,a,b,ha,hb,hab⟩ := hσ.2 v.val v.property w.val w.property hvwval
    let rb : {z // z ∈ ({w.val} : Finset (EssentialArcClass M))} → EssentialMarkedArc M :=
      fun _ => b
    have hrb : ∀ z, Quotient.mk (essentialArcSetoid M) (rb z) = z.val := by
      intro z
      exact hb.trans (Finset.mem_singleton.mp z.property).symm
    have hdb : ∀ z u, z ≠ u → Disjoint (arcInterior M (rb z)) (arcInterior M (rb u)) := by
      intro z u hzu
      exact False.elim (hzu (Subtype.ext ((Finset.mem_singleton.mp z.property).trans
        (Finset.mem_singleton.mp u.property).symm)))
    have hp := actual_simplex_insert_disjoint_representative M {w.val} rb hrb hdb a
      (fun _ => hab)
    rwa [ha] at hp
  · have he : σ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    subst σ
    exact empty_mem_actualA M

end CurveComplex.HyperellipticModel
