import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.EssentialStripClassExclusion

open Set Topology CurveComplex Schoenflies

namespace CoherentEndpointMotion

private theorem signed_width_homeomorph :
    ∃ k : Interval ≃ₜ Icc (-1 : ℝ) 1, ∀ t, (k t).val = 2*(t:ℝ)-1 := by
  let f : Interval → Icc (-1 : ℝ) 1 :=
    fun t => ⟨2*(t:ℝ)-1,by constructor <;> linarith [t.property.1,t.property.2]⟩
  have hfc : Continuous f := by dsimp [f]; fun_prop
  have hi : Function.Injective f := by
    intro s t he
    apply Subtype.ext
    have he := congrArg Subtype.val he
    dsimp [f] at he
    linarith
  have hs : Function.Surjective f := by
    intro w
    refine ⟨⟨(w.val+1)/2,by constructor <;> linarith [w.property.1,w.property.2]⟩,
      Subtype.ext ?_⟩
    dsimp [f]
    ring
  let k := hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hi,hs⟩)
  exact ⟨k,fun _ => rfl⟩

/-- The terminal-strip clearance lemma consumes the literal signed-width
proper-strip data supplied by the original proper-arc collar construction. -/
theorem proper_signed_strip_distinct_class_clearance
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B : Set X) (b a : C(Interval,X))
    (E : C(Interval × Icc (-1 : ℝ) 1,X)) (hE : IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = b t)
    (hend : ∀ w, E (0,w) ∈ B ∧ E (1,w) ∈ B)
    (hint : ∀ t ∈ Ioo (0 : Interval) 1, ∀ w, E (t,w) ∉ B)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (ha : IsEmbedding a) (haends : a 0 ∈ B ∧ a 1 ∈ B)
    (haInterior : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (hessential : ¬ ∃ c : C(Interval,X), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : Plane) 1,X), IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = Set.range a ∪ Set.range c)
    (hdistinct : ¬ ∃ H : AmbientIsotopy X,
      (∀ t, (fun x => H.map (t,x)) '' B = B) ∧ H.finalMap '' Set.range b = Set.range a)
    (hside0 : Disjoint (Set.range a)
      (Set.range (fun s : Interval => E (s,⟨-1,by norm_num⟩))))
    (hside1 : Disjoint (Set.range a)
      (Set.range (fun s : Interval => E (s,⟨1,by norm_num⟩)))) :
    Disjoint (Set.range a) (Set.range E) := by
  obtain ⟨k,hk⟩ := signed_width_homeomorph
  let r := (Homeomorph.refl Interval).prodCongr k
  let D : C(Interval × Interval,X) := ⟨E ∘ r,E.continuous.comp r.continuous⟩
  have hD : IsEmbedding D := hE.comp r.isEmbedding
  have hwidth (t : Interval) : (k t).val ∈ Ioo (-1 : ℝ) 1 ↔
      t ∈ Ioo (0 : Interval) 1 := by
    rw [hk]
    change (-1 < 2*(t:ℝ)-1 ∧ 2*(t:ℝ)-1 < 1) ↔ (0 < (t:ℝ) ∧ (t:ℝ) < 1)
    constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith
  have himage : D '' {z | z.2 ∈ Ioo (0 : Interval) 1} =
      E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨r z,(hwidth z.2).mpr hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      refine ⟨r.symm z,?_,?_⟩
      · apply (hwidth _).mp
        change (k (k.symm z.2)).val ∈ Ioo (-1 : ℝ) 1
        rw [k.apply_symm_apply]
        exact hz
      · change E (r (r.symm z)) = E z
        rw [r.apply_symm_apply]
  have hDB (z : Interval × Interval) : D z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
    change E (z.1,k z.2) ∈ B ↔ _
    constructor
    · intro hz
      by_cases h0 : z.1 = 0
      · exact Or.inl h0
      · have h1 : z.1 = 1 := by
          apply le_antisymm le_top
          apply le_of_not_gt
          intro h1
          exact hint z.1 ⟨bot_lt_iff_ne_bot.mpr h0,h1⟩ _ hz
        exact Or.inr h1
    · intro hz
      rcases hz with hz | hz
      · simpa only [hz] using (hend (k z.2)).1
      · simpa only [hz] using (hend (k z.2)).2
  let p : Interval := ⟨1/2,by constructor <;> norm_num⟩
  have hp : p ∈ Ioo (0 : Interval) 1 := by
    change (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1
    norm_num
  have hk0 : k 0 = ⟨-1,by norm_num⟩ := Subtype.ext (by rw [hk]; norm_num)
  have hk1 : k 1 = ⟨1,by norm_num⟩ := Subtype.ext (by rw [hk]; norm_num)
  have hkp : k p = ⟨0,by norm_num⟩ := Subtype.ext (by rw [hk]; norm_num [p])
  have hDp : Set.range (fun s : Interval => D (s,p)) = Set.range b := by
    have heq : (fun s : Interval => D (s,p)) = b := by
      funext s
      change E (s,k p) = b s
      rw [hkp]
      exact hcenter s
    rw [heq]
  have hD0 : Set.range (fun s : Interval => D (s,0)) =
      Set.range (fun s : Interval => E (s,⟨-1,by norm_num⟩)) := by
    congr 1
    funext s
    change E (s,k 0) = _
    rw [hk0]
  have hD1 : Set.range (fun s : Interval => D (s,1)) =
      Set.range (fun s : Interval => E (s,⟨1,by norm_num⟩)) := by
    congr 1
    funext s
    change E (s,k 1) = _
    rw [hk1]
  have hDE : Set.range D = Set.range E := r.surjective.range_comp E
  rw [← hDE]
  apply distinct_class_essential_arc_clears_strip_carrier B D hD (himage ▸ hopen) hDB
    a ha haends haInterior hessential p hp
  · simpa only [hDp] using hdistinct
  · simpa only [hD0] using hside0
  · simpa only [hD1] using hside1

#print axioms proper_signed_strip_distinct_class_clearance

end CoherentEndpointMotion
