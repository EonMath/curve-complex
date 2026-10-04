import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homeomorph.Defs
namespace CurveComplex.LocalSurgery
open Set Topology
open scoped unitInterval

theorem actualEmbeddedUnitIntervalRange (κ : C(unitInterval,unitInterval))
    (hκ : Function.Injective κ) : Set.range κ=Set.uIcc (κ 0) (κ 1) := by
  have hI : Set.Icc (0 : unitInterval) 1=Set.univ := by
    ext t
    simp only [Set.mem_Icc,Set.mem_univ,iff_true]
    exact ⟨t.property.1,t.property.2⟩
  rcases κ.continuous.strictMono_of_inj_boundedOrder' hκ with hm | hm
  · have hImage := κ.continuous.continuousOn.image_Icc_of_monotoneOn
      (show (0 : unitInterval)≤1 by exact zero_le_one) (hm.monotone.monotoneOn _)
    have hle : κ 0≤κ 1 := hm.monotone (show (0 : unitInterval)≤1 by exact zero_le_one)
    simpa only [hI,Set.image_univ,Set.uIcc_of_le hle] using hImage
  · have hImage := κ.continuous.continuousOn.image_Icc_of_antitoneOn
      (show (0 : unitInterval)≤1 by exact zero_le_one) (hm.antitone.antitoneOn _)
    have hle : κ 1≤κ 0 := hm.antitone (show (0 : unitInterval)≤1 by exact zero_le_one)
    simpa only [hI,Set.image_univ,Set.uIcc_of_ge hle] using hImage

/-- Transfer actual original-boundary interior avoidance to any embedded
original subpath with those same two endpoints. -/
theorem actualOriginalBoundarySubarcInteriorAvoidance
    {X : Type*} [TopologicalSpace X] (b g : C(unitInterval,X)) (A : Set X)
    (hb : IsEmbedding b) (hg : IsEmbedding g) (hgRange : Set.range g⊆Set.range b)
    (η : C(unitInterval,unitInterval)) (hη : Function.Injective η)
    (hg0 : g 0=b (η 0)) (hg1 : g 1=b (η 1))
    (hAvoid : ∀ t∈Set.Ioo (0 : unitInterval) 1,b (η t)∉A) :
    ∀ s∈Set.Ioo (0 : unitInterval) 1,g s∉A := by
  let E := hb.toHomeomorph
  let ξ : C(unitInterval,unitInterval) :=
    ⟨fun s => E.symm ⟨g s,hgRange ⟨s,rfl⟩⟩,
      E.symm.continuous.comp (g.continuous.subtype_mk _)⟩
  have hpoint (s : unitInterval) : b (ξ s)=g s :=
    congrArg Subtype.val (E.apply_symm_apply ⟨g s,hgRange ⟨s,rfl⟩⟩)
  have hξ : Function.Injective ξ := by
    intro s t he
    apply hg.injective
    exact (hpoint s).symm.trans ((congrArg b he).trans (hpoint t))
  have hξ0 : ξ 0=η 0 := hb.injective ((hpoint 0).trans hg0)
  have hξ1 : ξ 1=η 1 := hb.injective ((hpoint 1).trans hg1)
  have hrange : Set.range ξ=Set.range η := by
    rw [actualEmbeddedUnitIntervalRange ξ hξ,actualEmbeddedUnitIntervalRange η hη,hξ0,hξ1]
  intro s hs hgs
  obtain ⟨t,ht⟩ := (show ξ s∈Set.range η from hrange ▸ ⟨s,rfl⟩)
  have hvalue : b (η t)=g s := (congrArg b ht).trans (hpoint s)
  have ht0 : t≠0 := by
    intro he
    subst t
    have htime : s=0 := hg.injective (hvalue.symm.trans hg0.symm)
    exact (ne_of_gt hs.1) htime
  have ht1 : t≠1 := by
    intro he
    subst t
    have htime : s=1 := hg.injective (hvalue.symm.trans hg1.symm)
    exact (ne_of_lt hs.2) htime
  exact hAvoid t ⟨lt_of_le_of_ne t.property.1 ht0.symm,lt_of_le_of_ne t.property.2 ht1⟩ (hvalue.symm ▸ hgs)
end CurveComplex.LocalSurgery
