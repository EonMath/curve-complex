import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.EmbeddedStripAmbientMotion
import CurveComplexGenusTwo.Topology.CrosscutIsotopy
import CurveComplexGenusTwo.Topology.TorusStrip.ArcInterval

open Set Topology CurveComplex Schoenflies

namespace CoherentEndpointMotion

noncomputable def rectanglePoint (z : Interval × Interval) : Plane :=
  Plane.mk (2*(z.1:ℝ)-1) (2*(z.2:ℝ)-1)

theorem rectanglePoint_continuous : Continuous rectanglePoint := by
  change Continuous (fun z : Interval × Interval =>
    Plane.mk (2*(z.1:ℝ)-1) (2*(z.2:ℝ)-1))
  fun_prop

theorem rectanglePoint_injective : Function.Injective rectanglePoint := by
  intro z w h
  have h0 := congrArg (fun p : Plane => p 0) h
  have h1 := congrArg (fun p : Plane => p 1) h
  apply Prod.ext <;> apply Subtype.ext
  · dsimp [rectanglePoint,Plane.mk] at h0
    linarith
  · dsimp [rectanglePoint,Plane.mk] at h1
    linarith

theorem rectanglePoint_mem_closed (z : Interval × Interval) :
    rectanglePoint z ∈ Plane.closedSquare 0 1 := by
  apply mem_closedSquare_zero_one.mpr
  change max |2*(z.1:ℝ)-1| |2*(z.2:ℝ)-1| ≤ 1
  rw [max_le_iff,abs_le,abs_le]
  constructor <;> constructor <;> linarith [z.1.property.1,z.1.property.2,
    z.2.property.1,z.2.property.2]

theorem rectanglePoint_mem_open_iff (z : Interval × Interval) :
    rectanglePoint z ∈ Plane.openSquare 0 1 ↔
      z.1 ∈ Ioo (0 : Interval) 1 ∧ z.2 ∈ Ioo (0 : Interval) 1 := by
  rw [mem_openSquare_zero_one]
  change max |2*(z.1:ℝ)-1| |2*(z.2:ℝ)-1| < 1 ↔
    (0 < (z.1:ℝ) ∧ (z.1:ℝ) < 1) ∧ (0 < (z.2:ℝ) ∧ (z.2:ℝ) < 1)
  rw [max_lt_iff,abs_lt,abs_lt]
  constructor
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem rectanglePoint_end_mem_model (z : Interval × Interval)
    (hz : z.1 = 0 ∨ z.1 = 1) : rectanglePoint z ∈ modelCurve := by
  have hw : |2*(z.2:ℝ)-1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [z.2.property.1,z.2.property.2]
  rcases hz with hz | hz
  · change max |2*(z.1:ℝ)-1| |2*(z.2:ℝ)-1| = 1
    have hval : (z.1:ℝ) = 0 := congrArg Subtype.val hz
    rw [hval]
    norm_num
    exact hw
  · change max |2*(z.1:ℝ)-1| |2*(z.2:ℝ)-1| = 1
    have hval : (z.1:ℝ) = 1 := congrArg Subtype.val hz
    rw [hval]
    norm_num
    exact hw

theorem rectanglePoint_homeomorph :
    ∃ e : (Interval × Interval) ≃ₜ Plane.closedSquare 0 1,
      ∀ z, (e z).val = rectanglePoint z := by
  let f : Interval × Interval → Plane.closedSquare 0 1 :=
    fun z => ⟨rectanglePoint z,rectanglePoint_mem_closed z⟩
  have hfc : Continuous f := rectanglePoint_continuous.subtype_mk _
  have hi : Function.Injective f := fun _ _ h =>
    rectanglePoint_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro p
    have hp := mem_closedSquare_zero_one.mp p.property
    change max |p.val 0| |p.val 1| ≤ 1 at hp
    have hx := abs_le.mp ((le_max_left _ _).trans hp)
    have hy := abs_le.mp ((le_max_right _ _).trans hp)
    let s : Interval := ⟨(p.val 0 + 1)/2,by constructor <;> linarith⟩
    let t : Interval := ⟨(p.val 1 + 1)/2,by constructor <;> linarith⟩
    refine ⟨(s,t),Subtype.ext ?_⟩
    ext i
    fin_cases i <;> dsimp [f,rectanglePoint,Plane.mk,s,t] <;> ring
  let e := hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hi,hs⟩)
  exact ⟨e,fun _ => rfl⟩

-- The canonical regional disk lift proves this same parametrization fact, but
-- its olean is not in the pinned cache. This private adapter uses the identical
-- clamped parameter construction, without importing that producer's obligations.
private theorem path_range_isArcBetween (f : C(Interval, Plane)) (hf : IsEmbedding f) :
    IsArcBetween (Set.range f) (f 0) (f 1) := by
  let fc : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
  have hfc : Continuous fc := f.continuous.comp continuous_projIcc
  have he (t : Interval) : fc t = f t := by
    simp [fc,Set.projIcc_of_mem zero_le_one t.property]
  refine ⟨fc,hfc.continuousOn,?_,?_,he 0,he 1⟩
  · intro t ht u hu h
    exact congrArg Subtype.val (hf.injective (by
      simpa only [← he] using h : f ⟨t,ht⟩ = f ⟨u,hu⟩))
  · ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,(he ⟨t,ht⟩).symm⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t,t.property,he t⟩

/-- Fixed-endpoint curved crosscuts in a closed strip are related by an
ambient motion of the strip fixing its entire boundary. -/
theorem rectangle_crosscuts_fixed_endpoints_motion
    (a b : C(Interval, Interval × Interval)) (ha : IsEmbedding a) (hb : IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (ha0 : (a 0).1 = 0) (ha1 : (a 1).1 = 1)
    (hai : ∀ t ∈ Ioo (0 : Interval) 1,
      (a t).1 ∈ Ioo (0 : Interval) 1 ∧ (a t).2 ∈ Ioo (0 : Interval) 1)
    (hbi : ∀ t ∈ Ioo (0 : Interval) 1,
      (b t).1 ∈ Ioo (0 : Interval) 1 ∧ (b t).2 ∈ Ioo (0 : Interval) 1) :
    ∃ K : AmbientIsotopy (Interval × Interval),
      K.finalMap '' Set.range a = Set.range b ∧
      (∀ t z, z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1 → K.map (t,z) = z) := by
  obtain ⟨e,he⟩ := rectanglePoint_homeomorph
  let A : C(Interval, Plane) := ⟨rectanglePoint ∘ a,
    rectanglePoint_continuous.comp a.continuous⟩
  let B : C(Interval, Plane) := ⟨rectanglePoint ∘ b,
    rectanglePoint_continuous.comp b.continuous⟩
  have hA : IsEmbedding A := (A.continuous.isClosedEmbedding
    (rectanglePoint_injective.comp ha.injective)).isEmbedding
  have hB : IsEmbedding B := (B.continuous.isClosedEmbedding
    (rectanglePoint_injective.comp hb.injective)).isEmbedding
  have hBA0 : B 0 = A 0 := congrArg rectanglePoint h0
  have hBA1 : B 1 = A 1 := congrArg rectanglePoint h1
  have hAi : Set.range A \ {A 0,A 1} ⊆ Plane.openSquare 0 1 := by
    rintro x ⟨⟨t,rfl⟩,ht⟩
    apply (rectanglePoint_mem_open_iff (a t)).mpr
    apply hai
    constructor
    · exact bot_lt_iff_ne_bot.mpr (fun h => ht (Or.inl (congrArg A h)))
    · exact lt_top_iff_ne_top.mpr (fun h => ht (Or.inr (congrArg A h)))
  have hBi : Set.range B \ {A 0,A 1} ⊆ Plane.openSquare 0 1 := by
    rintro x ⟨⟨t,rfl⟩,ht⟩
    apply (rectanglePoint_mem_open_iff (b t)).mpr
    apply hbi
    constructor
    · exact bot_lt_iff_ne_bot.mpr (fun h => ht (Or.inl ((congrArg B h).trans hBA0)))
    · exact lt_top_iff_ne_top.mpr (fun h => ht (Or.inr ((congrArg B h).trans hBA1)))
  obtain ⟨R,H,hR,hmove,hfar,hfix⟩ := position_crosscut_supported_isotopy
    (Set.range A) (Set.range B) (A 0) (A 1)
    (path_range_isArcBetween A hA)
    (by simpa only [hBA0,hBA1] using
      path_range_isArcBetween B hB)
    (rectanglePoint_end_mem_model (a 0) (Or.inl ha0))
    (rectanglePoint_end_mem_model (a 1) (Or.inr ha1)) hAi hBi
  have hstay (t : Interval) (z : Plane) :
      H.map (t,z) ∈ Plane.closedSquare 0 1 ↔ z ∈ Plane.closedSquare 0 1 := by
    by_cases hz : z ∈ Plane.openSquare 0 1
    · have hHz : H.map (t,z) ∈ Plane.openSquare 0 1 := by
        by_contra hn
        obtain ⟨k,hk⟩ := H.homeomorphism_at t
        have heq : H.map (t,z) = z := k.injective (by
          rw [hk,hk]
          exact hfix t _ hn)
        exact hn (heq.symm ▸ hz)
      exact iff_of_true (Plane.openSquare_subset_closedSquare 0 1 hHz)
        (Plane.openSquare_subset_closedSquare 0 1 hz)
    · rw [hfix t z hz]
  let L : AmbientIsotopy (Plane.closedSquare 0 1) := {
    map := ⟨fun z => ⟨H.map (z.1,z.2.val),(hstay z.1 z.2.val).mpr z.2.property⟩,
      (H.map.continuous.comp (continuous_fst.prodMk continuous_snd.subtype_val)).subtype_mk _⟩
    homeomorphism_at := by
      intro t
      obtain ⟨k,hk⟩ := H.homeomorphism_at t
      exact ⟨k.subtype (fun x => by simpa only [hk] using (hstay t x).symm),
        fun _ => Subtype.ext (hk _)⟩
    at_zero := by intro z; exact Subtype.ext (H.at_zero z.val) }
  let K : AmbientIsotopy (Interval × Interval) := {
    map := ⟨fun z => e.symm (L.map (z.1,e z.2)),
      e.symm.continuous.comp (L.map.continuous.comp
        (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩
    homeomorphism_at := by
      intro t
      obtain ⟨k,hk⟩ := L.homeomorphism_at t
      exact ⟨(e.trans k).trans e.symm,fun z => congrArg e.symm (hk (e z))⟩
    at_zero := by
      intro z
      change e.symm (L.map (⟨0,by norm_num⟩,e z)) = z
      rw [L.at_zero,e.symm_apply_apply] }
  have hcoord (t : Interval) (z : Interval × Interval) :
      rectanglePoint (K.map (t,z)) = H.map (t,rectanglePoint z) := by
    rw [← he]
    change (e (e.symm (L.map (t,e z)))).val = H.map (t,rectanglePoint z)
    rw [e.apply_symm_apply]
    change H.map (t,(e z).val) = _
    rw [he]
  refine ⟨K,?_,?_⟩
  · ext z
    constructor
    · rintro ⟨w,⟨s,rfl⟩,h⟩
      have hp : rectanglePoint z ∈ H.finalMap '' Set.range A := by
        refine ⟨A s,Set.mem_range_self s,?_⟩
        exact (hcoord 1 (a s)).symm.trans (congrArg rectanglePoint h)
      rw [hmove] at hp
      obtain ⟨t,ht⟩ := hp
      exact ⟨t,rectanglePoint_injective ht⟩
    · rintro ⟨s,rfl⟩
      have hp : rectanglePoint (b s) ∈ H.finalMap '' Set.range A := by
        rw [hmove]
        exact Set.mem_range_self s
      obtain ⟨x,⟨t,rfl⟩,hx⟩ := hp
      refine ⟨a t,Set.mem_range_self t,rectanglePoint_injective ?_⟩
      exact (hcoord 1 (a t)).trans hx
  · intro t z hz
    apply rectanglePoint_injective
    rw [hcoord]
    apply hfix
    rw [rectanglePoint_mem_open_iff]
    rintro ⟨h0,h1⟩
    rcases hz with hz | hz | hz | hz
    · exact (ne_of_gt h0.1) hz
    · exact (ne_of_lt h0.2) hz
    · exact (ne_of_gt h1.1) hz
    · exact (ne_of_lt h1.2) hz

#print axioms rectangle_crosscuts_fixed_endpoints_motion

end CoherentEndpointMotion
