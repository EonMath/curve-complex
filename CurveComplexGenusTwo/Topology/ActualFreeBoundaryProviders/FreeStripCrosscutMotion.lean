import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.StripCrosscutMotion
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.StripEndEdgeMotion

open Set Topology CurveComplex

namespace CoherentEndpointMotion

private def composeMotion {X : Type*} [TopologicalSpace X]
    (K L : AmbientIsotopy X) : AmbientIsotopy X := {
  map := ⟨fun z => L.map (z.1,K.map (z.1,z.2)),
    L.map.continuous.comp (continuous_fst.prodMk K.map.continuous)⟩
  homeomorphism_at := by
    intro t
    obtain ⟨k,hk⟩ := K.homeomorphism_at t
    obtain ⟨l,hl⟩ := L.homeomorphism_at t
    exact ⟨k.trans l,fun z => (hl (k z)).trans (congrArg (fun w => L.map (t,w)) (hk z))⟩
  at_zero := by
    intro z
    change L.map (⟨0,by norm_num⟩,K.map (⟨0,by norm_num⟩,z)) = z
    rw [K.at_zero,L.at_zero] }

/-- A crosscut from one end of a rectangle to the other can be reached from
any interior rail, with arbitrary interior endpoint positions. Side edges are
fixed and each end edge stays in itself throughout the ambient motion. -/
theorem rectangle_free_crosscut_motion
    (a : C(Interval, Interval × Interval)) (ha : IsEmbedding a)
    (ha0 : (a 0).1 = 0) (ha1 : (a 1).1 = 1)
    (ha0width : (a 0).2 ∈ Ioo (0 : Interval) 1)
    (ha1width : (a 1).2 ∈ Ioo (0 : Interval) 1)
    (hai : ∀ t ∈ Ioo (0 : Interval) 1,
      (a t).1 ∈ Ioo (0 : Interval) 1 ∧ (a t).2 ∈ Ioo (0 : Interval) 1)
    (p : Interval) (hp : p ∈ Ioo (0 : Interval) 1) :
    ∃ K : AmbientIsotopy (Interval × Interval),
      K.finalMap '' Set.range (fun s : Interval => (s,p)) = Set.range a ∧
      (∀ t z, z.2 = 0 ∨ z.2 = 1 → K.map (t,z) = z) ∧
      (∀ t z, (K.map (t,z)).1 = 0 ↔ z.1 = 0) ∧
      (∀ t z, (K.map (t,z)).1 = 1 ↔ z.1 = 1) := by
  obtain ⟨L,hLfirst,hLfix,hLinterior,hL0,hL1⟩ :=
    rectangle_end_edge_motion p (a 0).2 (a 1).2 hp ha0width ha1width
  let c : C(Interval, Interval × Interval) :=
    ⟨fun s => L.finalMap (s,p),L.map.continuous.comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))⟩
  have hc : IsEmbedding c := by
    obtain ⟨l,hl⟩ := L.homeomorphism_at 1
    apply (c.continuous.isClosedEmbedding ?_).isEmbedding
    intro s t he
    change L.map (1,(s,p)) = L.map (1,(t,p)) at he
    exact congrArg Prod.fst (l.injective (by simpa only [hl] using he))
  have hc0 : c 0 = a 0 := hL0.trans (Prod.ext ha0.symm rfl)
  have hc1 : c 1 = a 1 := hL1.trans (Prod.ext ha1.symm rfl)
  have hcfirst (s : Interval) : (c s).1 = s := hLfirst 1 (s,p)
  have hci (s : Interval) (hs : s ∈ Ioo (0 : Interval) 1) :
      (c s).1 ∈ Ioo (0 : Interval) 1 ∧ (c s).2 ∈ Ioo (0 : Interval) 1 :=
    ⟨by rw [hcfirst]; exact hs,(hLinterior 1 (s,p)).mpr hp⟩
  obtain ⟨M,hMa,hMfix⟩ := rectangle_crosscuts_fixed_endpoints_motion c a hc ha
    hc0.symm hc1.symm (by rw [hc0]; exact ha0) (by rw [hc1]; exact ha1) hci hai
  have hMend (t : Interval) (z : Interval × Interval) (v : Interval)
      (hv : v = 0 ∨ v = 1) : (M.map (t,z)).1 = v ↔ z.1 = v := by
    constructor
    · intro he
      have hfix : M.map (t,M.map (t,z)) = M.map (t,z) := by
        apply hMfix
        rcases hv with hv | hv
        · exact Or.inl (he.trans hv)
        · exact Or.inr (Or.inl (he.trans hv))
      obtain ⟨m,hm⟩ := M.homeomorphism_at t
      have heq : M.map (t,z) = z := m.injective (by simpa only [hm] using hfix)
      exact heq ▸ he
    · intro he
      rw [hMfix t z (by
        rcases hv with hv | hv
        · exact Or.inl (he.trans hv)
        · exact Or.inr (Or.inl (he.trans hv)))]
      exact he
  let K := composeMotion L M
  refine ⟨K,?_,?_,?_,?_⟩
  · change (M.finalMap ∘ L.finalMap) '' Set.range (fun s : Interval => (s,p)) = _
    rw [Set.image_comp]
    have he : L.finalMap '' Set.range (fun s : Interval => (s,p)) = Set.range c := by
      rw [← Set.range_comp]
      rfl
    rw [he]
    exact hMa
  · intro t z hz
    change M.map (t,L.map (t,z)) = z
    rw [hLfix t z hz]
    apply hMfix
    rcases hz with hz | hz
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr hz))
  · intro t z
    change (M.map (t,L.map (t,z))).1 = 0 ↔ z.1 = 0
    rw [hMend t _ 0 (Or.inl rfl),hLfirst]
  · intro t z
    change (M.map (t,L.map (t,z))).1 = 1 ↔ z.1 = 1
    rw [hMend t _ 1 (Or.inr rfl),hLfirst]

#print axioms rectangle_free_crosscut_motion

/-- An arbitrary crosscut in a relatively open strip lies in the original
boundary-preserving ambient class of its center rail, with free end positions. -/
theorem embedded_strip_free_crosscut_ambient_motion
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (B : Set X) (E : C(Interval × Interval, X)) (hE : IsEmbedding E)
    (hopen : IsOpen (E '' {z | z.2 ∈ Ioo (0 : Interval) 1}))
    (hB : ∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (a : C(Interval, Interval × Interval)) (ha : IsEmbedding a)
    (ha0 : (a 0).1 = 0) (ha1 : (a 1).1 = 1)
    (ha0width : (a 0).2 ∈ Ioo (0 : Interval) 1)
    (ha1width : (a 1).2 ∈ Ioo (0 : Interval) 1)
    (hai : ∀ t ∈ Ioo (0 : Interval) 1,
      (a t).1 ∈ Ioo (0 : Interval) 1 ∧ (a t).2 ∈ Ioo (0 : Interval) 1)
    (p : Interval) (hp : p ∈ Ioo (0 : Interval) 1) :
    ∃ H : AmbientIsotopy X,
      (∀ t, (fun x => H.map (t,x)) '' B = B) ∧
      H.finalMap '' Set.range (fun s : Interval => E (s,p)) = Set.range (E.comp a) ∧
      (∀ t x, x ∉ E '' {z | z.2 ∈ Ioo (0 : Interval) 1} → H.map (t,x) = x) := by
  obtain ⟨K,hKa,hKfix,hK0,hK1⟩ :=
    rectangle_free_crosscut_motion a ha ha0 ha1 ha0width ha1width hai p hp
  have hfix (t : Interval) (z : Interval × Interval)
      (hz : z ∉ {z | z.2 ∈ Ioo (0 : Interval) 1}) : K.map (t,z) = z := by
    apply hKfix
    by_cases h0 : z.2 = 0
    · exact Or.inl h0
    · exact Or.inr (le_antisymm le_top (le_of_not_gt
        (fun h => hz ⟨bot_lt_iff_ne_bot.mpr h0,h⟩)))
  obtain ⟨H,hHE,hHfix⟩ := embedded_cell_isotopy_extend E hE
    {z | z.2 ∈ Ioo (0 : Interval) 1} hopen K hfix
  refine ⟨H,?_,?_,hHfix⟩
  · intro t
    have hmem (x : X) : H.map (t,x) ∈ B ↔ x ∈ B := by
      by_cases hx : x ∈ Set.range E
      · obtain ⟨z,rfl⟩ := hx
        rw [hHE,hB,hB,hK0,hK1]
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
  · have hcomm : H.finalMap ∘ E = E ∘ K.finalMap := by
      funext z
      exact hHE 1 z
    change H.finalMap '' Set.range (E ∘ fun s : Interval => (s,p)) = Set.range (E ∘ a)
    rw [Set.range_comp,Set.range_comp,← Set.image_comp,hcomm,Set.image_comp,hKa]

#print axioms embedded_strip_free_crosscut_ambient_motion

end CoherentEndpointMotion
