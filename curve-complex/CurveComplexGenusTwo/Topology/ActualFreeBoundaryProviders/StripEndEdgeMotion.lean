import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.EmbeddedStripAmbientMotion

open Set Topology CurveComplex

namespace CoherentEndpointMotion

/-- Independent endpoint slides on the two end edges extend across the whole
rectangle, preserving its longitudinal coordinate and fixing its side edges. -/
theorem rectangle_end_edge_motion (p q₀ q₁ : Interval)
    (hp : p ∈ Ioo (0 : Interval) 1)
    (hq₀ : q₀ ∈ Ioo (0 : Interval) 1) (hq₁ : q₁ ∈ Ioo (0 : Interval) 1) :
    ∃ K : AmbientIsotopy (Interval × Interval),
      (∀ t z, (K.map (t,z)).1 = z.1) ∧
      (∀ t z, z.2 = 0 ∨ z.2 = 1 → K.map (t,z) = z) ∧
      (∀ t z, (K.map (t,z)).2 ∈ Ioo (0 : Interval) 1 ↔
        z.2 ∈ Ioo (0 : Interval) 1) ∧
      K.finalMap (0,p) = (0,q₀) ∧ K.finalMap (1,p) = (1,q₁) := by
  obtain ⟨L₀,hL₀ends,hL₀p,hL₀mono⟩ := interval_point_isotopy p q₀ hp hq₀
  obtain ⟨L₁,hL₁ends,hL₁p,hL₁mono⟩ := interval_point_isotopy p q₁ hp hq₁
  let f : Interval × (Interval × Interval) → ℝ := fun z =>
    (1 - (z.2.1 : ℝ)) * (L₀.map (z.1,z.2.2) : ℝ) +
      (z.2.1 : ℝ) * (L₁.map (z.1,z.2.2) : ℝ)
  have hfc : Continuous f := by
    dsimp [f]
    fun_prop
  have hf0 (t u : Interval) : f (t,(u,0)) = 0 := by
    simp [f,(hL₀ends t).1,(hL₁ends t).1]
  have hf1 (t u : Interval) : f (t,(u,1)) = 1 := by
    simp [f,(hL₀ends t).2,(hL₁ends t).2]
  have hfm (t u : Interval) : StrictMono (fun w : Interval => f (t,(u,w))) := by
    intro v w hvw
    have h0 : (L₀.map (t,v) : ℝ) < (L₀.map (t,w) : ℝ) := hL₀mono t hvw
    have h1 : (L₁.map (t,v) : ℝ) < (L₁.map (t,w) : ℝ) := hL₁mono t hvw
    by_cases hu : (u : ℝ) = 0
    · simpa [f,hu] using h0
    · have hupos : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm hu)
      have hleft : 0 ≤ (1 - (u : ℝ)) *
          ((L₀.map (t,w) : ℝ) - (L₀.map (t,v) : ℝ)) :=
        mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr h0.le)
      have hright : 0 < (u : ℝ) *
          ((L₁.map (t,w) : ℝ) - (L₁.map (t,v) : ℝ)) :=
        mul_pos hupos (sub_pos.mpr h1)
      dsimp [f]
      nlinarith
  have hfI (t u w : Interval) : f (t,(u,w)) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hf0] using (hfm t u).monotone (show (0 : Interval) ≤ w from bot_le)
    · simpa only [hf1] using (hfm t u).monotone (show w ≤ (1 : Interval) from le_top)
  let F : Interval × (Interval × Interval) → Interval × Interval :=
    fun z => (z.2.1,⟨f z,hfI z.1 z.2.1 z.2.2⟩)
  have hFc : Continuous F := continuous_snd.fst.prodMk (hfc.subtype_mk _)
  have hhomeo (t : Interval) : ∃ k : (Interval × Interval) ≃ₜ (Interval × Interval),
      ∀ z, k z = F (t,z) := by
    have hi : Function.Injective (fun z => F (t,z)) := by
      intro z w h
      have hfst := congrArg (fun p : Interval × Interval => p.1) h
      change z.1 = w.1 at hfst
      have hsnd : f (t,(z.1,z.2)) = f (t,(w.1,w.2)) :=
        congrArg (fun p : Interval × Interval => (p.2 : ℝ)) h
      rw [← hfst] at hsnd
      exact Prod.ext hfst ((hfm t z.1).injective hsnd)
    have hs : Function.Surjective (fun z => F (t,z)) := by
      intro z
      have hy : (z.2 : ℝ) ∈ Icc (f (t,(z.1,0))) (f (t,(z.1,1))) := by
        simpa only [hf0,hf1] using z.2.property
      have hc : Continuous (fun w : Interval => f (t,(z.1,w))) := by fun_prop
      obtain ⟨w,hw,he⟩ := intermediate_value_Icc (show (0 : Interval) ≤ 1 from bot_le)
        hc.continuousOn hy
      exact ⟨(z.1,w),Prod.ext rfl (Subtype.ext he)⟩
    let k := (hFc.comp (continuous_const.prodMk continuous_id)).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective (fun z => F (t,z)) ⟨hi,hs⟩)
    exact ⟨k,fun _ => rfl⟩
  let K : AmbientIsotopy (Interval × Interval) := {
    map := ⟨F,hFc⟩
    homeomorphism_at := hhomeo
    at_zero := by
      intro z
      change F (⟨0,by norm_num⟩,z) = z
      refine Prod.ext rfl ?_
      apply Subtype.ext
      change f (⟨0,by norm_num⟩,z) = (z.2 : ℝ)
      simp only [f,L₀.at_zero,L₁.at_zero]
      ring }
  have hK0 (t u : Interval) : K.map (t,(u,0)) = (u,0) :=
    Prod.ext rfl (Subtype.ext (hf0 t u))
  have hK1 (t u : Interval) : K.map (t,(u,1)) = (u,1) :=
    Prod.ext rfl (Subtype.ext (hf1 t u))
  refine ⟨K,fun _ _ => rfl,?_,?_,?_,?_⟩
  · intro t z hz
    rcases hz with hz | hz
    · have he : z = (z.1,0) := Prod.ext rfl hz
      rw [he]
      exact hK0 t z.1
    · have he : z = (z.1,1) := Prod.ext rfl hz
      rw [he]
      exact hK1 t z.1
  · intro t z
    constructor
    · intro hz
      by_contra hn
      have hz0 : z.2 = 0 ∨ z.2 = 1 := by
        by_cases h0 : z.2 = 0
        · exact Or.inl h0
        · exact Or.inr (le_antisymm le_top (le_of_not_gt
            (fun h => hn ⟨bot_lt_iff_ne_bot.mpr h0,h⟩)))
      rcases hz0 with hz0 | hz1
      · have h := congrArg Prod.snd (hK0 t z.1)
        have h' : (K.map (t,z)).2 = 0 := by simpa only [← hz0] using h
        exact (ne_of_gt hz.1) h'
      · have h := congrArg Prod.snd (hK1 t z.1)
        have h' : (K.map (t,z)).2 = 1 := by simpa only [← hz1] using h
        exact (ne_of_lt hz.2) h'
    · intro hz
      change 0 < f (t,z) ∧ f (t,z) < 1
      exact ⟨by simpa only [hf0] using hfm t z.1 hz.1,
        by simpa only [hf1] using hfm t z.1 hz.2⟩
  · change F (1,(0,p)) = (0,q₀)
    refine Prod.ext rfl ?_
    apply Subtype.ext
    change f (1,(0,p)) = (q₀ : ℝ)
    simpa [f,AmbientIsotopy.finalMap] using congrArg Subtype.val hL₀p
  · change F (1,(1,p)) = (1,q₁)
    refine Prod.ext rfl ?_
    apply Subtype.ext
    change f (1,(1,p)) = (q₁ : ℝ)
    simpa [f,AmbientIsotopy.finalMap] using congrArg Subtype.val hL₁p

#print axioms rectangle_end_edge_motion

end CoherentEndpointMotion
