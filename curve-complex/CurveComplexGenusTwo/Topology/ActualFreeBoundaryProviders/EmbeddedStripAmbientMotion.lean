import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FiniteBoundaryClock
import CurveComplexGenusTwo.Topology.ChartLift

open Set Topology CurveComplex

namespace CoherentEndpointMotion

/-- Extend a motion on a compact embedded cell by identity. The cell interior
is relative to the ambient space, so it may include ambient boundary points. -/
theorem embedded_cell_isotopy_extend
    {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y]
    (E : C(Y, X)) (hE : IsEmbedding E)
    (V : Set Y) (hU : IsOpen (E '' V))
    (K : AmbientIsotopy Y)
    (hfix : ∀ t y, y ∉ V → K.map (t,y) = y) :
    ∃ H : AmbientIsotopy X,
      (∀ t y, H.map (t,E y) = E (K.map (t,y))) ∧
      (∀ t x, x ∉ E '' V → H.map (t,x) = x) := by
  classical
  let C : Set X := Set.range E
  let U : Set X := E '' V
  have hC : IsClosed C := (isCompact_range E.continuous).isClosed
  let e : Y ≃ₜ C := hE.toHomeomorph
  let F : Interval × X → X := fun p =>
    if h : p.2 ∈ C then E (K.map (p.1,e.symm ⟨p.2,h⟩)) else p.2
  have hFE (t : Interval) (y : Y) : F (t,E y) = E (K.map (t,y)) := by
    have hEy : E y ∈ C := Set.mem_range_self y
    simp only [F,dif_pos hEy]
    have he : e.symm ⟨E y,hEy⟩ = y := by
      apply e.injective
      exact e.apply_symm_apply ⟨E y,hEy⟩
    rw [he]
  have hFU (t : Interval) (x : X) (hx : x ∉ U) : F (t,x) = x := by
    dsimp only [F]
    split_ifs with h
    · let y := e.symm ⟨x,h⟩
      have hey : E y = x := congrArg Subtype.val (e.apply_symm_apply ⟨x,h⟩)
      have hy : y ∉ V := by
        intro hy
        exact hx ⟨y,hy,hey⟩
      rw [hfix t y hy]
      exact hey
    · rfl
  have hcontC : ContinuousOn F (Prod.snd ⁻¹' C) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let j : (Prod.snd ⁻¹' C : Set (Interval × X)) → Interval × Y := fun p =>
      (p.val.1,e.symm ⟨p.val.2,p.property⟩)
    have hj : Continuous j :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        (e.symm.continuous.comp
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
    have hf : (Prod.snd ⁻¹' C : Set (Interval × X)).domRestrict F =
        E ∘ K.map ∘ j := by
      funext p
      change F (p.val.1,p.val.2) =
        E (K.map (p.val.1,e.symm ⟨p.val.2,p.property⟩))
      exact dite_eq_left p.property
    rw [hf]
    exact E.continuous.comp (K.map.continuous.comp hj)
  have hcontU : ContinuousOn F (Prod.snd ⁻¹' Uᶜ) := by
    apply continuous_snd.continuousOn.congr
    intro p hp
    exact hFU p.1 p.2 hp
  have hcont : Continuous F := by
    apply continuousOn_univ.mp
    have hcover : (Prod.snd ⁻¹' C : Set (Interval × X)) ∪ Prod.snd ⁻¹' Uᶜ = univ := by
      ext p
      simp only [Set.mem_union,Set.mem_preimage,Set.mem_compl_iff,Set.mem_univ,iff_true]
      by_cases hp : p.2 ∈ C
      · exact Or.inl hp
      · exact Or.inr (fun hu => hp (Set.image_subset_range E V hu))
    rw [← hcover]
    exact hcontC.union_of_isClosed hcontU (hC.preimage continuous_snd)
      (hU.isClosed_compl.preimage continuous_snd)
  have hmem (t : Interval) (x : X) : F (t,x) ∈ C ↔ x ∈ C := by
    by_cases hx : x ∈ C
    · dsimp only [F]
      rw [dif_pos hx]
      exact iff_of_true (Set.mem_range_self _) hx
    · simp only [F,dif_neg hx,hx]
  have hhomeo (t : Interval) : ∃ f : X ≃ₜ X, ∀ x, f x = F (t,x) := by
    obtain ⟨k,hk⟩ := K.homeomorphism_at t
    let G : X → X := fun x =>
      if h : x ∈ C then E (k.symm (e.symm ⟨x,h⟩)) else x
    have hGE (y : Y) : G (E y) = E (k.symm y) := by
      have hEy : E y ∈ C := Set.mem_range_self y
      simp only [G,dif_pos hEy]
      have he : e.symm ⟨E y,hEy⟩ = y := by
        apply e.injective
        exact e.apply_symm_apply ⟨E y,hEy⟩
      rw [he]
    have hGU (x : X) (hx : x ∉ U) : G x = x := by
      dsimp only [G]
      split_ifs with h
      · let y := e.symm ⟨x,h⟩
        have hey : E y = x := congrArg Subtype.val (e.apply_symm_apply ⟨x,h⟩)
        have hy : y ∉ V := fun hy => hx ⟨y,hy,hey⟩
        have hky : k y = y := (hk y).trans (hfix t y hy)
        have hki : k.symm y = y := by
          apply k.injective
          rw [k.apply_symm_apply,hky]
        rw [hki]
        exact hey
      · rfl
    have hGc : Continuous G := by
      apply continuousOn_univ.mp
      have hcover : C ∪ Uᶜ = univ := by
        ext x
        simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_univ,iff_true]
        exact em (x ∈ C) |>.imp_right (fun h hu => h (Set.image_subset_range E V hu))
      rw [← hcover]
      apply ContinuousOn.union_of_isClosed ?_ ?_ hC hU.isClosed_compl
      · apply continuousOn_iff_continuous_domRestrict.mpr
        have heq : C.domRestrict G = E ∘ k.symm ∘ e.symm := by
          funext x
          simp only [G,Set.domRestrict,dif_pos x.property,Function.comp_apply]
        rw [heq]
        exact E.continuous.comp (k.symm.continuous.comp e.symm.continuous)
      · exact continuous_id.continuousOn.congr hGU
    have hleft (x : X) : G (F (t,x)) = x := by
      by_cases hx : x ∈ C
      · obtain ⟨y,rfl⟩ := hx
        rw [hFE,hGE,← hk,k.symm_apply_apply]
      · simp only [F,dif_neg hx,G]
    have hright (x : X) : F (t,G x) = x := by
      by_cases hx : x ∈ C
      · obtain ⟨y,rfl⟩ := hx
        rw [hGE,hFE,← hk,k.apply_symm_apply]
      · simp only [G,dif_neg hx,F]
    let f : X ≃ₜ X := {
      toFun := fun x => F (t,x)
      invFun := G
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hcont.comp (continuous_const.prodMk continuous_id)
      continuous_invFun := hGc }
    exact ⟨f,fun _ => rfl⟩
  refine ⟨{ map := ⟨F,hcont⟩,homeomorphism_at := hhomeo,at_zero := ?_ },hFE,hFU⟩
  intro x
  by_cases hx : x ∈ C
  · obtain ⟨y,rfl⟩ := hx
    change F (0,E y) = E y
    exact (hFE 0 y).trans (congrArg E (K.at_zero y))
  · exact hFU 0 x (fun hu => hx (Set.image_subset_range E V hu))

#print axioms embedded_cell_isotopy_extend

/-- A two-ended interval clock moves one interior point while fixing both ends. -/
theorem interval_point_isotopy (p q : Interval)
    (hp : p ∈ Ioo (0 : Interval) 1) (hq : q ∈ Ioo (0 : Interval) 1) :
    ∃ K : AmbientIsotopy Interval,
      (∀ t, K.map (t,0) = 0 ∧ K.map (t,1) = 1) ∧
      K.finalMap p = q ∧ (∀ t, StrictMono (fun x => K.map (t,x))) := by
  have hmono (v : Interval) : StrictMono (fun _ : Fin 1 => (v : ℝ)) := by
    intro i j hij
    have he : i = j := Subsingleton.elim _ _
    exact False.elim (by simpa [he] using hij)
  obtain ⟨W,hWc,hWm,hW0,hW1,hWpq⟩ := finite_ordered_interval_clock 1
    (fun _ => (p : ℝ)) (fun _ => (q : ℝ)) (hmono p) (hmono q)
    (fun _ => hp) (fun _ => hq)
  let f : Interval × ℝ → ℝ := fun z => (1 - (z.1 : ℝ)) * z.2 + (z.1 : ℝ) * W z.2
  have hfc : Continuous f := by dsimp [f]; fun_prop
  have hf0 (t : Interval) : f (t,0) = 0 := by simp [f,hW0]
  have hf1 (t : Interval) : f (t,1) = 1 := by simp [f,hW1]
  have hfm (t : Interval) : StrictMono (fun x => f (t,x)) := by
    intro x y hxy
    by_cases ht : (t : ℝ) = 0
    · simpa [f,ht] using hxy
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      have h0 : 0 ≤ (1 - (t : ℝ)) * (y - x) :=
        mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hxy.le)
      have h1 : 0 < (t : ℝ) * (W y - W x) := mul_pos htpos (sub_pos.mpr (hWm hxy))
      dsimp [f]
      nlinarith
  have hfI (t x : Interval) : f (t,(x : ℝ)) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hf0 t] using (hfm t).monotone x.property.1
    · simpa only [hf1 t] using (hfm t).monotone x.property.2
  let F : Interval × Interval → Interval := fun z => ⟨f (z.1,z.2),hfI z.1 z.2⟩
  have hFc : Continuous F :=
    (hfc.comp (continuous_fst.prodMk continuous_snd.subtype_val)).subtype_mk _
  have hh (t : Interval) : ∃ k : Interval ≃ₜ Interval, ∀ x, k x = F (t,x) := by
    have hi : Function.Injective (fun x => F (t,x)) := by
      intro x y h
      exact Subtype.ext ((hfm t).injective (congrArg Subtype.val h))
    have hs : Function.Surjective (fun x => F (t,x)) := by
      intro y
      have hy : (y : ℝ) ∈ Icc (f (t,0)) (f (t,1)) := by
        simpa only [hf0 t,hf1 t] using y.property
      obtain ⟨x,hx,hxy⟩ := intermediate_value_Icc zero_le_one
        ((hfc.comp (continuous_const.prodMk continuous_id)).continuousOn) hy
      exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
    let k := (hFc.comp (continuous_const.prodMk continuous_id)).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective (fun x => F (t,x)) ⟨hi,hs⟩)
    exact ⟨k,fun _ => rfl⟩
  let K : AmbientIsotopy Interval := {
    map := ⟨F,hFc⟩
    homeomorphism_at := hh
    at_zero := by intro x; apply Subtype.ext; simp [F,f] }
  refine ⟨K,?_,?_,?_⟩
  · intro t
    constructor <;> apply Subtype.ext
    · exact hf0 t
    · exact hf1 t
  · apply Subtype.ext
    change f (1,(p : ℝ)) = (q : ℝ)
    simpa [f] using hWpq (0 : Fin 1)
  · intro t x y hxy
    change f (t,(x:ℝ)) < f (t,(y:ℝ))
    exact hfm t hxy

#print axioms interval_point_isotopy

/-- Interior rails in a relatively open compact strip are related by an actual
ambient isotopy. Both end edges, and hence the distinguished boundary, stay setwise fixed. -/
theorem embedded_strip_rail_ambient_motion
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (B : Set X) (E : C(Interval × Interval, X)) (hE : IsEmbedding E)
    (hopen : IsOpen (E '' {z | z.2 ∈ Ioo (0 : Interval) 1}))
    (hB : ∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (p q : Interval) (hp : p ∈ Ioo (0 : Interval) 1) (hq : q ∈ Ioo (0 : Interval) 1) :
    ∃ H : AmbientIsotopy X,
      (∀ t, (fun x => H.map (t,x)) '' B = B) ∧
      (∀ s, H.finalMap (E (s,p)) = E (s,q)) ∧
      (∀ t x, x ∉ E '' {z | z.2 ∈ Ioo (0 : Interval) 1} → H.map (t,x) = x) := by
  obtain ⟨L,hLends,hLpq,hLmono⟩ := interval_point_isotopy p q hp hq
  let K : AmbientIsotopy (Interval × Interval) := {
    map := ⟨fun z => (z.2.1,L.map (z.1,z.2.2)),
      continuous_snd.fst.prodMk (L.map.continuous.comp
        (continuous_fst.prodMk continuous_snd.snd))⟩
    homeomorphism_at := by
      intro t
      obtain ⟨k,hk⟩ := L.homeomorphism_at t
      exact ⟨(Homeomorph.refl Interval).prodCongr k,fun _ => Prod.ext rfl (hk _)⟩
    at_zero := by intro z; exact Prod.ext rfl (L.at_zero _) }
  have hKfix (t : Interval) (z : Interval × Interval)
      (hz : z ∉ {z | z.2 ∈ Ioo (0 : Interval) 1}) : K.map (t,z) = z := by
    change (z.1,L.map (t,z.2)) = z
    refine Prod.ext rfl ?_
    by_cases h0 : z.2 = 0
    · simpa only [h0] using (hLends t).1
    · have h1 : z.2 = 1 := by
        apply le_antisymm le_top
        exact le_of_not_gt (fun h => hz ⟨bot_lt_iff_ne_bot.mpr h0,h⟩)
      simpa only [h1] using (hLends t).2
  obtain ⟨H,hHE,hHfix⟩ := embedded_cell_isotopy_extend E hE
    {z | z.2 ∈ Ioo (0 : Interval) 1} hopen K hKfix
  refine ⟨H,?_,?_,hHfix⟩
  · intro t
    have hmem (x : X) : H.map (t,x) ∈ B ↔ x ∈ B := by
      by_cases hx : x ∈ Set.range E
      · obtain ⟨z,rfl⟩ := hx
        rw [hHE,hB,hB]
        rfl
      · rw [hHfix t x (fun hxU => hx (Set.image_subset_range E _ hxU))]
    apply Set.Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact (hmem x).mpr hx
    · intro y hy
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      refine ⟨e.symm y,?_,?_⟩
      · apply (hmem _).mp
        rw [← he,e.apply_symm_apply]
        exact hy
      · change H.map (t,e.symm y) = y
        rw [← he,e.apply_symm_apply]
  · intro s
    change H.map (1,E (s,p)) = E (s,q)
    rw [hHE]
    change E (s,L.finalMap p) = E (s,q)
    rw [hLpq]

#print axioms embedded_strip_rail_ambient_motion

end CoherentEndpointMotion
