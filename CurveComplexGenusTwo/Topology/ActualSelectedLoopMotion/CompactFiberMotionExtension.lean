import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib

namespace CurveComplex
open Set Topology

/-- A compact parameter-space motion descends through the actual fibers of B.
The descended motion is extended by the identity outside its open support. -/
theorem compact_fiber_motion_extension
    {Y X : Type} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (B : C(Y,X)) (U : Set X) (hU : IsOpen U)
    (hUA : U ⊆ Set.range B) (K : AmbientIsotopy Y)
    (hfiber : ∀ t y z, B (K.map (t,y)) = B (K.map (t,z)) ↔ B y = B z)
    (hfix : ∀ t y, B y ∉ U → B (K.map (t,y)) = B y) :
    ∃ H : AmbientIsotopy X,
      (∀ t y, H.map (t,B y) = B (K.map (t,y))) ∧
      (∀ t x, x ∉ U → H.map (t,x) = x) := by
  classical
  let A := Set.range B
  let select : A → Y := fun x => Classical.choose x.property
  have hselect (x : A) : B (select x) = x.val :=
    Classical.choose_spec x.property
  let f : Interval × X → X := fun tx =>
    if hx : tx.2 ∈ A then B (K.map (tx.1,select ⟨tx.2,hx⟩)) else tx.2
  have hfB (t : Interval) (y : Y) : f (t,B y) = B (K.map (t,y)) := by
    dsimp only [f]
    rw [dite_eq_left (show B y ∈ A from Set.mem_range_self y)]
    exact (hfiber t _ y).mpr (hselect ⟨B y,Set.mem_range_self y⟩)
  have hfid (t : Interval) (x : X) (hx : x ∉ U) : f (t,x) = x := by
    dsimp only [f]
    split_ifs with hxA
    · exact (hfix t _ (by rwa [hselect])).trans (hselect ⟨x,hxA⟩)
    · rfl
  have hA : IsClosed A := (isCompact_range B.continuous).isClosed
  let q : Interval × Y → Interval × A := fun ty =>
    (ty.1,⟨B ty.2,Set.mem_range_self ty.2⟩)
  have hqcont : Continuous q := continuous_fst.prodMk
    ((B.continuous.comp continuous_snd).subtype_mk _)
  have hqsurj : Function.Surjective q := by
    rintro ⟨t,x⟩
    obtain ⟨y,hy⟩ := x.property
    exact ⟨(t,y),Prod.ext rfl (Subtype.ext hy)⟩
  have hq : IsQuotientMap q := hqcont.isClosedMap.isQuotientMap hqcont hqsurj
  have hfcontA : Continuous (fun tx : Interval × A => f (tx.1,tx.2.val)) := by
    apply hq.continuous_iff.mpr
    have hc := B.continuous.comp K.map.continuous
    exact hc.congr (fun ty => (hfB ty.1 ty.2).symm)
  have hunion : ((Prod.snd ⁻¹' A : Set (Interval × X)) ∪
      Prod.snd ⁻¹' Uᶜ) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro tx
    by_cases hx : tx.2 ∈ U
    · exact Or.inl (hUA hx)
    · exact Or.inr hx
  have hfcont : Continuous f := by
    have hfirst : ContinuousOn f (Prod.snd ⁻¹' A) := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      let lift : (Prod.snd ⁻¹' A : Set (Interval × X)) → Interval × A :=
        fun z => (z.val.1,⟨z.val.2,z.property⟩)
      have hlift : Continuous lift := continuous_subtype_val.fst.prodMk
        (continuous_subtype_val.snd.subtype_mk _)
      exact hfcontA.comp hlift
    have hsecond : ContinuousOn f (Prod.snd ⁻¹' Uᶜ) := by
      apply continuous_snd.continuousOn.congr
      intro tx hx
      exact hfid tx.1 tx.2 hx
    rw [← continuousOn_univ,← hunion]
    exact hfirst.union_of_isClosed hsecond (hA.preimage continuous_snd)
      (hU.isClosed_compl.preimage continuous_snd)
  have hfbij (t : Interval) : Function.Bijective (fun x => f (t,x)) := by
    constructor
    · intro x z he
      change f (t,x) = f (t,z) at he
      by_cases hx : x ∈ A
      · obtain ⟨y,hy⟩ := hx
        by_cases hz : z ∈ A
        · obtain ⟨w,hw⟩ := hz
          rw [←hy,←hw,hfB,hfB] at he
          exact hy.symm.trans (((hfiber t y w).mp he).trans hw)
        · rw [←hy,hfB,hfid t z (fun h => hz (hUA h))] at he
          exact False.elim (hz ⟨K.map (t,y),he⟩)
      · by_cases hz : z ∈ A
        · obtain ⟨w,hw⟩ := hz
          rw [←hw,hfid t x (fun h => hx (hUA h)),hfB] at he
          exact False.elim (hx ⟨K.map (t,w),he.symm⟩)
        · rw [hfid t x (fun h => hx (hUA h)),hfid t z (fun h => hz (hUA h))] at he
          exact he
    · intro x
      by_cases hx : x ∈ A
      · obtain ⟨y,hy⟩ := hx
        obtain ⟨k,hk⟩ := K.homeomorphism_at t
        refine ⟨B (k.symm y),?_⟩
        change f (t,B (k.symm y)) = x
        rw [hfB,←hk,k.apply_symm_apply,hy]
      · exact ⟨x,hfid t x (fun h => hx (hUA h))⟩
  let H : AmbientIsotopy X := {
    map := ⟨f,hfcont⟩
    homeomorphism_at := by
      intro t
      have hc : Continuous (fun x => f (t,x)) :=
        hfcont.comp (continuous_const.prodMk continuous_id)
      let h := (Equiv.ofBijective (fun x => f (t,x)) (hfbij t)).toHomeomorphOfContinuousClosed
        hc hc.isClosedMap
      exact ⟨h,fun x => rfl⟩
    at_zero := by
      intro x
      change f (0,x) = x
      by_cases hx : x ∈ A
      · obtain ⟨y,rfl⟩ := hx
        exact (hfB 0 y).trans (congrArg B (K.at_zero y))
      · exact hfid 0 x (fun h => hx (hUA h)) }
  exact ⟨H,hfB,hfid⟩

end CurveComplex
