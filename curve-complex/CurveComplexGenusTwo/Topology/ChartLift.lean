import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.ModelCurve

namespace CurveComplex
open Schoenflies

private theorem position_isotopy_restrict {X : Type*} [TopologicalSpace X]
    (H : AmbientIsotopy X) (U : Set X)
    (hfix : ∀ t x, x ∉ U → H.map (t, x) = x) :
    ∃ K : AmbientIsotopy U,
      ∀ t x, (K.map (t, x) : X) = H.map (t, (x : X)) := by
  have hinv (t : Interval) (x : X) : x ∈ U ↔ H.map (t, x) ∈ U := by
    obtain ⟨e, he⟩ := H.homeomorphism_at t
    constructor
    · intro hx
      by_contra hn
      have heq : H.map (t, H.map (t, x)) = H.map (t, x) := hfix t _ hn
      have eqx : H.map (t, x) = x := e.injective (by simpa only [he] using heq)
      exact hn (eqx.symm ▸ hx)
    · intro hx
      by_contra hn
      exact hn ((hfix t x hn) ▸ hx)
  refine ⟨{ map := ⟨fun z => ⟨H.map (z.1, z.2.val), (hinv z.1 z.2.val).mp z.2.property⟩,
      (H.map.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩,
            homeomorphism_at := ?_, at_zero := ?_ }, fun t x => rfl⟩
  · intro t
    obtain ⟨e, he⟩ := H.homeomorphism_at t
    refine ⟨e.subtype (fun x => by simpa only [he] using hinv t x), ?_⟩
    intro x
    exact Subtype.ext (he x.val)
  · intro x
    exact Subtype.ext (H.at_zero x.val)

private theorem position_isotopy_conjugate {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (H : AmbientIsotopy Y) :
    ∃ K : AmbientIsotopy X,
      ∀ t x, K.map (t, x) = e.symm (H.map (t, e x)) := by
  refine ⟨{ map := ⟨fun z => e.symm (H.map (z.1, e z.2)),
      e.symm.continuous.comp (H.map.continuous.comp
        (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩,
            homeomorphism_at := ?_, at_zero := ?_ }, fun t x => rfl⟩
  · intro t
    obtain ⟨h, hh⟩ := H.homeomorphism_at t
    exact ⟨(e.trans h).trans e.symm, fun x => congrArg e.symm (hh (e x))⟩
  · intro x
    change e.symm (H.map (⟨0, by norm_num⟩, e x)) = x
    rw [H.at_zero, e.symm_apply_apply]

private theorem position_isotopy_extend {S : Type*} [TopologicalSpace S]
    [T2Space S] [CompactSpace S]
    (U K : Set S) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (H : AmbientIsotopy U)
    (hfix : ∀ t (x : U), x.val ∉ K → (H.map (t, x) : S) = x.val) :
    ∃ G : AmbientIsotopy S,
      (∀ t (x : U), G.map (t, x.val) = (H.map (t, x) : S)) ∧
      (∀ t x, x ∉ K → G.map (t, x) = x) := by
  classical
  let F : Interval × S → S := fun z =>
    if hx : z.2 ∈ U then (H.map (z.1, ⟨z.2, hx⟩) : S) else z.2
  have hFU (t : Interval) (x : U) : F (t, x.val) = (H.map (t, x) : S) := by
    simp only [F, dif_pos x.property]
  have hFK (t : Interval) (x : S) (hx : x ∉ K) : F (t, x) = x := by
    dsimp [F]
    split_ifs with h
    · exact hfix t ⟨x, h⟩ hx
    · rfl
  have hcontU : ContinuousOn F {z | z.2 ∈ U} := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hh : Continuous (fun z : {z : Interval × S | z.2 ∈ U} =>
        (H.map (z.val.1, ⟨z.val.2, z.property⟩) : S)) :=
      continuous_subtype_val.comp (H.map.continuous.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _)))
    have hsame : ({z : Interval × S | z.2 ∈ U}.domRestrict F) =
        (fun z : {z : Interval × S | z.2 ∈ U} =>
          (H.map (z.val.1, ⟨z.val.2, z.property⟩) : S)) := by
      funext z
      exact hFU z.val.1 ⟨z.val.2, z.property⟩
    rw [hsame]
    exact hh
  have hcontK : ContinuousOn F {z | z.2 ∉ K} := by
    apply continuous_snd.continuousOn.congr
    intro z hz
    exact hFK z.1 z.2 hz
  have hcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z.2 ∈ U
    · exact hcontU.continuousAt ((hU.preimage continuous_snd).mem_nhds hz)
    · exact hcontK.continuousAt
        ((hK.isOpen_compl.preimage continuous_snd).mem_nhds (fun hk => hz (hKU hk)))
  have hmem (t : Interval) (x : S) : F (t, x) ∈ U ↔ x ∈ U := by
    by_cases hx : x ∈ U
    · rw [hFU t ⟨x, hx⟩]
      exact iff_of_true (H.map (t, ⟨x, hx⟩)).property hx
    · simp only [F, dif_neg hx, hx]
  refine ⟨{ map := ⟨F, hcont⟩, homeomorphism_at := ?_, at_zero := ?_ }, hFU, hFK⟩
  · intro t
    obtain ⟨e, he⟩ := H.homeomorphism_at t
    have hinj : Function.Injective (fun x => F (t, x)) := by
      intro x y hxy
      change F (t, x) = F (t, y) at hxy
      by_cases hx : x ∈ U
      · have hy : y ∈ U := (hmem t y).mp (hxy ▸ (hmem t x).mpr hx)
        have heq : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
          apply Subtype.ext
          simpa only [he, hFU t ⟨x, hx⟩, hFU t ⟨y, hy⟩] using hxy
        exact congrArg Subtype.val (e.injective heq)
      · have hy : y ∉ U := by
          intro hy
          exact hx ((hmem t x).mp (hxy.symm ▸ (hmem t y).mpr hy))
        simpa only [F, dif_neg hx, dif_neg hy] using hxy
    have hsurj : Function.Surjective (fun x => F (t, x)) := by
      intro y
      by_cases hy : y ∈ U
      · refine ⟨(e.symm ⟨y, hy⟩).val, ?_⟩
        change F (t, (e.symm ⟨y, hy⟩).val) = y
        rw [hFU]
        have hh := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
        simpa only [he] using hh
      · exact ⟨y, by simp only [F, dif_neg hy]⟩
    have hh : IsHomeomorph (fun x => F (t, x)) :=
      (isHomeomorph_iff_continuous_bijective).mpr
        ⟨hcont.comp (continuous_const.prodMk continuous_id), hinj, hsurj⟩
    obtain ⟨e, he⟩ := isHomeomorph_iff_exists_homeomorph.mp hh
    exact ⟨e, fun x => congrFun he x⟩
  · intro x
    dsimp [F]
    split_ifs with hx
    · exact congrArg Subtype.val (H.at_zero ⟨x, hx⟩)
    · rfl

theorem position_surface_chart_lift
    (S : Type*) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (U : Set S) (V : Set Plane) (hU : IsOpen U)
    (e : U ≃ₜ V) (C : Set Plane) (hC : IsCompact C) (hCV : C ⊆ V)
    (H : AmbientIsotopy Plane)
    (hfix : ∀ t x, x ∉ C → H.map (t, x) = x) :
    ∃ K : AmbientIsotopy U, ∃ G : AmbientIsotopy S,
      (∀ t (x : U), (e (K.map (t, x)) : Plane) = H.map (t, (e x : Plane))) ∧
      (∀ t (x : U), G.map (t, x.val) = (K.map (t, x) : S)) ∧
      ∀ t x, x ∉ U → G.map (t, x) = x := by
  have hfixV : ∀ t x, x ∉ V → H.map (t, x) = x := by
    intro t x hx
    apply hfix
    exact fun hxc => hx (hCV hxc)
  obtain ⟨HV, hHV⟩ := position_isotopy_restrict H V hfixV
  obtain ⟨K, hK⟩ := position_isotopy_conjugate e HV
  have heimage (t : Interval) (x : U) :
      (e (K.map (t, x)) : Plane) = H.map (t, (e x : Plane)) := by
    rw [hK, e.apply_symm_apply]
    exact hHV t (e x)
  let j : C → S := fun x => (e.symm ⟨x.val, hCV x.property⟩).val
  have hj : Continuous j := continuous_subtype_val.comp
    (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hjU : Set.range j ⊆ U := by
    rintro x ⟨y, rfl⟩
    exact (e.symm ⟨y.val, hCV y.property⟩).property
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hjclosed : IsClosed (Set.range j) := (isCompact_range hj).isClosed
  have hfixK : ∀ t (x : U), x.val ∉ Set.range j → (K.map (t, x) : S) = x.val := by
    intro t x hx
    have hout : (e x : Plane) ∉ C := by
      intro hn
      apply hx
      refine ⟨⟨(e x : Plane), hn⟩, ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply x)
    have hEq : HV.map (t, e x) = e x :=
      Subtype.ext ((hHV t (e x)).trans (hfix t (e x) hout))
    rw [hK, hEq, e.symm_apply_apply]
  obtain ⟨G, hGU, hGfix⟩ :=
    position_isotopy_extend U (Set.range j) hU hjclosed hjU K hfixK
  exact ⟨K, G, heimage, hGU, fun t x hx => hGfix t x (fun h => hx (hjU h))⟩

#print axioms position_surface_chart_lift

end CurveComplex
