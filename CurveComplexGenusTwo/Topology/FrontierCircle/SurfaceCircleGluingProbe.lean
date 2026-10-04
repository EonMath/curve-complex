import Mathlib

open Set Topology unitInterval
namespace CurveComplex

theorem exists_embedded_circle_of_injective_loop_probe
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {f : ℝ → S} (hf : ContinuousOn f I) (hclose : f 0 = f 1)
    (hi : InjOn f (Ico 0 1)) :
    ∃ r : C(Circle,S), IsEmbedding r ∧ Set.range r = f '' I := by
  have himage : f '' I = f '' I := rfl
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  let g : AddCircle (1 : ℝ) → S := AddCircle.liftIco 1 0 f
  have hgc : Continuous g := AddCircle.liftIco_zero_continuous hclose hf
  have hgi : Function.Injective g := by
    intro a b he
    obtain ⟨x,hx,rfl⟩ := AddCircle.eq_coe_Ico a
    obtain ⟨y,hy,rfl⟩ := AddCircle.eq_coe_Ico b
    have hxy : f x = f y := by
      simpa only [g,AddCircle.liftIco_zero_coe_apply hx,
        AddCircle.liftIco_zero_coe_apply hy] using he
    exact congrArg (fun t : ℝ => (t : AddCircle (1 : ℝ))) (hi hx hy hxy)
  let r : C(Circle,S) := ⟨g ∘ e.symm,hgc.comp e.symm.continuous⟩
  refine ⟨r,(r.continuous.isClosedEmbedding (hgi.comp e.symm.injective)).isEmbedding,?_⟩
  apply Set.Subset.antisymm
  · rintro z ⟨a,rfl⟩
    obtain ⟨t,ht,he⟩ := AddCircle.eq_coe_Ico (e.symm a)
    rw [← himage]
    refine ⟨t,⟨ht.1,ht.2.le⟩,?_⟩
    change f t = g (e.symm a)
    rw [← he]
    exact (AddCircle.liftIco_zero_coe_apply ht).symm
  · intro z hz
    rw [← himage] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    by_cases h1 : t = 1
    · subst t
      refine ⟨e (0 : AddCircle (1 : ℝ)),?_⟩
      change g (e.symm (e 0)) = f 1
      rw [e.symm_apply_apply]
      have h0 : (0:ℝ) ∈ Ico (0:ℝ) 1 := by simp
      exact (AddCircle.liftIco_zero_coe_apply h0).trans hclose
    · refine ⟨e (t : AddCircle (1 : ℝ)),?_⟩
      change g (e.symm (e (t : AddCircle (1 : ℝ)))) = f t
      rw [e.symm_apply_apply]
      exact AddCircle.liftIco_zero_coe_apply ⟨ht.1,lt_of_le_of_ne ht.2 h1⟩

/-- Two actual embedded paths with exactly the two common endpoints produce
an actual embedded circle in an arbitrary Hausdorff ambient space. -/
theorem exists_embedded_circle_of_two_paths_probe
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {a b : S} (p : Path a b) (q : Path b a)
    (hp : IsEmbedding p) (hq : IsEmbedding q)
    (hinter : Set.range p ∩ Set.range q = {a,b}) :
    ∃ r : C(Circle,S), IsEmbedding r ∧ Set.range r = Set.range p ∪ Set.range q := by
  let f := (p.trans q).extend
  have hf : Continuous f := (p.trans q).continuous_extend
  have hclose : f 0 = f 1 := by simp [f]
  have hinj : InjOn f (Ico 0 1) := by
    intro t ht u hu he
    have he' : (p.trans q) ⟨t,⟨ht.1,ht.2.le⟩⟩ =
        (p.trans q) ⟨u,⟨hu.1,hu.2.le⟩⟩ := by
      simpa only [f,(p.trans q).extend_apply ⟨ht.1,ht.2.le⟩,
        (p.trans q).extend_apply ⟨hu.1,hu.2.le⟩] using he
    rw [Path.trans_apply,Path.trans_apply] at he'
    split_ifs at he' with htHalf huHalf huHalf
    · have hh := congrArg Subtype.val (hp.injective he')
      dsimp at hh
      linarith
    · have hm : p ⟨2*t,(mul_pos_mem_iff zero_lt_two).2 ⟨ht.1,htHalf⟩⟩ ∈
          Set.range p ∩ Set.range q := ⟨Set.mem_range_self _,⟨_,he'.symm⟩⟩
      rw [hinter] at hm
      rcases hm with ha | hb
      · have hh := congrArg Subtype.val (hq.injective (he'.symm.trans (ha.trans q.target.symm)))
        dsimp at hh
        linarith [hu.2]
      · have hh := congrArg Subtype.val (hq.injective (he'.symm.trans (hb.trans q.source.symm)))
        dsimp at hh
        linarith
    · have hm : p ⟨2*u,(mul_pos_mem_iff zero_lt_two).2 ⟨hu.1,huHalf⟩⟩ ∈
          Set.range p ∩ Set.range q := ⟨Set.mem_range_self _,⟨_,he'⟩⟩
      rw [hinter] at hm
      rcases hm with ha | hb
      · have hh := congrArg Subtype.val (hq.injective (he'.trans (ha.trans q.target.symm)))
        dsimp at hh
        linarith [ht.2]
      · have hh := congrArg Subtype.val (hq.injective (he'.trans (hb.trans q.source.symm)))
        dsimp at hh
        linarith
    · have hh := congrArg Subtype.val (hq.injective he')
      dsimp at hh
      linarith
  obtain ⟨r,hr,hrange⟩ := exists_embedded_circle_of_injective_loop_probe
    hf.continuousOn hclose hinj
  refine ⟨r,hr,?_⟩
  rw [hrange]
  exact ((p.trans q).image_extend_of_subset (Set.Subset.refl I)).trans (p.trans_range q)

#print axioms exists_embedded_circle_of_two_paths_probe
#print axioms exists_embedded_circle_of_injective_loop_probe
end CurveComplex
