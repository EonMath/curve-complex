import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeStripCrosscutMotion

open Set Topology CurveComplex

namespace CoherentEndpointMotion

/-- Proper crosscuts with one common far endpoint admit a motion fixing the far
and side edges pointwise and preserving the other end edge setwise. -/
theorem rectangle_one_free_end_crosscuts_motion
    (old new : C(Interval, Interval × Interval))
    (hOld : IsEmbedding old) (hNew : IsEmbedding new)
    (hOldZero : (old 0).1 = 0) (hNewZero : (new 0).1 = 0)
    (hFar : old 1 = new 1)
    (hOldOne : (old 1).1 = 1)
    (hOldZeroWidth : (old 0).2 ∈ Ioo (0 : Interval) 1)
    (hNewZeroWidth : (new 0).2 ∈ Ioo (0 : Interval) 1)
    (hFarWidth : (old 1).2 ∈ Ioo (0 : Interval) 1)
    (hOldInterior : ∀ t ∈ Ioo (0 : Interval) 1,
      (old t).1 ∈ Ioo (0 : Interval) 1 ∧ (old t).2 ∈ Ioo (0 : Interval) 1)
    (hNewInterior : ∀ t ∈ Ioo (0 : Interval) 1,
      (new t).1 ∈ Ioo (0 : Interval) 1 ∧ (new t).2 ∈ Ioo (0 : Interval) 1) :
    ∃ L : AmbientIsotopy (Interval × Interval),
      L.finalMap '' Set.range old = Set.range new ∧
      (∀ r z, z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1 → L.map (r,z) = z) ∧
      (∀ r z, (L.map (r,z)).1 = 0 ↔ z.1 = 0) := by
  obtain ⟨J,hJends,hJmove,hJmono⟩ :=
    interval_point_isotopy (old 0).2 (new 0).2 hOldZeroWidth hNewZeroWidth
  let clock : Interval × Interval → Interval := fun z =>
    ⟨(z.1 : ℝ) * (1 - (z.2 : ℝ)),
      ⟨mul_nonneg z.1.property.1 (sub_nonneg.mpr z.2.property.2), by
        have h := mul_le_mul_of_nonneg_left
          (show 1 - (z.2 : ℝ) ≤ 1 by linarith [z.2.property.1]) z.1.property.1
        nlinarith [z.1.property.2]⟩⟩
  have hClock : Continuous clock := by
    apply Continuous.subtype_mk
    fun_prop
  have hClockZero (x : Interval) : clock (0,x) = 0 := by
    apply Subtype.ext
    simp [clock]
  have hClockFar (r : Interval) : clock (r,1) = 0 := by
    apply Subtype.ext
    simp [clock]
  have hClockLeft : clock (1,0) = 1 := by
    apply Subtype.ext
    simp [clock]
  let F : Interval × (Interval × Interval) → Interval × Interval :=
    fun z => (z.2.1,J.map (clock (z.1,z.2.1),z.2.2))
  have hF : Continuous F := continuous_snd.fst.prodMk
    (J.map.continuous.comp
      ((hClock.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
        continuous_snd.snd))
  let K : AmbientIsotopy (Interval × Interval) := {
    map := ⟨F,hF⟩
    homeomorphism_at := by
      intro r
      have hi : Function.Injective (fun z => F (r,z)) := by
        intro z w he
        have hx := congrArg Prod.fst he
        change z.1 = w.1 at hx
        have hy : J.map (clock (r,z.1),z.2) = J.map (clock (r,w.1),w.2) :=
          congrArg Prod.snd he
        rw [← hx] at hy
        obtain ⟨j,hj⟩ := J.homeomorphism_at (clock (r,z.1))
        exact Prod.ext hx (j.injective (by simpa only [hj] using hy))
      have hs : Function.Surjective (fun z => F (r,z)) := by
        intro z
        obtain ⟨j,hj⟩ := J.homeomorphism_at (clock (r,z.1))
        refine ⟨(z.1,j.symm z.2),Prod.ext rfl ?_⟩
        change J.map (clock (r,z.1),j.symm z.2) = z.2
        rw [← hj,j.apply_symm_apply]
      let k := (hF.comp (continuous_const.prodMk continuous_id)).homeoOfEquivCompactToT2
        (f := Equiv.ofBijective (fun z => F (r,z)) ⟨hi,hs⟩)
      exact ⟨k,fun _ => rfl⟩
    at_zero := by
      intro z
      change (z.1,J.map (clock (0,z.1),z.2)) = z
      rw [hClockZero]
      have he : J.map ((0 : Interval),z.2) = z.2 := J.at_zero z.2
      rw [he] }
  have hKfirst (r : Interval) (z : Interval × Interval) : (K.map (r,z)).1 = z.1 := rfl
  have hKfix (r : Interval) (z : Interval × Interval)
      (hz : z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1) : K.map (r,z) = z := by
    refine Prod.ext (hKfirst r z) ?_
    change J.map (clock (r,z.1),z.2) = z.2
    rcases hz with hz | hz | hz
    · rw [hz,hClockFar]
      exact J.at_zero z.2
    · rw [hz,(hJends _).1]
    · rw [hz,(hJends _).2]
  let c : C(Interval, Interval × Interval) :=
    ⟨fun s => K.finalMap (old s),K.map.continuous.comp
      (continuous_const.prodMk old.continuous)⟩
  have hc : IsEmbedding c := by
    obtain ⟨k,hk⟩ := K.homeomorphism_at 1
    apply (c.continuous.isClosedEmbedding ?_).isEmbedding
    intro s t he
    change K.map (1,old s) = K.map (1,old t) at he
    exact hOld.injective (k.injective (by simpa only [hk] using he))
  have hc0 : c 0 = new 0 := by
    apply Prod.ext
    · exact hOldZero.trans hNewZero.symm
    · change J.map (clock (1,(old 0).1),(old 0).2) = (new 0).2
      rw [hOldZero,hClockLeft]
      exact hJmove
  have hc1 : c 1 = new 1 := (hKfix 1 (old 1) (Or.inl hOldOne)).trans hFar
  have hcfirst (s : Interval) : (c s).1 = (old s).1 := rfl
  have hci (s : Interval) (hs : s ∈ Ioo (0 : Interval) 1) :
      (c s).1 ∈ Ioo (0 : Interval) 1 ∧ (c s).2 ∈ Ioo (0 : Interval) 1 := by
    refine ⟨(hOldInterior s hs).1,?_,?_⟩
    · change 0 < J.map (clock (1,(old s).1),(old s).2)
      simpa only [(hJends _).1] using hJmono (clock (1,(old s).1)) (hOldInterior s hs).2.1
    · change J.map (clock (1,(old s).1),(old s).2) < 1
      simpa only [(hJends _).2] using hJmono (clock (1,(old s).1)) (hOldInterior s hs).2.2
  obtain ⟨M,hMimage,hMfix⟩ := rectangle_crosscuts_fixed_endpoints_motion c new hc hNew
    hc0.symm hc1.symm (by rw [hcfirst]; exact hOldZero)
    (by rw [hcfirst]; exact hOldOne) hci hNewInterior
  have hMleft (r : Interval) (z : Interval × Interval) :
      (M.map (r,z)).1 = 0 ↔ z.1 = 0 := by
    constructor
    · intro hz
      obtain ⟨m,hm⟩ := M.homeomorphism_at r
      have hfix : M.map (r,M.map (r,z)) = M.map (r,z) := hMfix r _ (Or.inl hz)
      have heq : M.map (r,z) = z := m.injective (by simpa only [hm] using hfix)
      exact heq ▸ hz
    · intro hz
      rw [hMfix r z (Or.inl hz)]
      exact hz
  let L : AmbientIsotopy (Interval × Interval) := {
    map := ⟨fun z => M.map (z.1,K.map (z.1,z.2)),
      M.map.continuous.comp (continuous_fst.prodMk K.map.continuous)⟩
    homeomorphism_at := by
      intro r
      obtain ⟨k,hk⟩ := K.homeomorphism_at r
      obtain ⟨m,hm⟩ := M.homeomorphism_at r
      exact ⟨k.trans m,fun z => (hm (k z)).trans
        (congrArg (fun w => M.map (r,w)) (hk z))⟩
    at_zero := by
      intro z
      change M.map (⟨0,by norm_num⟩,K.map (⟨0,by norm_num⟩,z)) = z
      rw [K.at_zero,M.at_zero] }
  refine ⟨L,?_,?_,?_⟩
  · change (M.finalMap ∘ K.finalMap) '' Set.range old = _
    rw [Set.image_comp]
    have hKimage : K.finalMap '' Set.range old = Set.range c := by
      rw [← Set.range_comp]
      rfl
    rw [hKimage]
    exact hMimage
  · intro r z hz
    change M.map (r,K.map (r,z)) = z
    rw [hKfix r z hz]
    exact hMfix r z (Or.inr hz)
  · intro r z
    change (M.map (r,K.map (r,z))).1 = 0 ↔ z.1 = 0
    rw [hMleft,hKfirst]

end CoherentEndpointMotion
