import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceSurgeryInput

namespace CurveComplex

/-- The two complementary compact arcs of an actual embedded curve are
produced with the same endpoint orientation. -/
theorem source_curve_complementary_arcs
    {S : Type} [TopologicalSpace S] [T2Space S]
    (c : Curve S) (x y : S) (hx : x ∈ c.image) (hy : y ∈ c.image) (hxy : x ≠ y) :
    ∃ p q : C(Interval,S),
      Topology.IsEmbedding p ∧ Topology.IsEmbedding q ∧
      p 0 = x ∧ q 0 = x ∧ p 1 = y ∧ q 1 = y ∧
      Set.range p ∪ Set.range q = c.image ∧
      Set.range p ∩ Set.range q = {x,y} := by
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  have hst : s ≠ t := by intro he; exact hxy (hs.symm.trans ((congrArg c.map he).trans ht))
  let p : C(Interval,S) := ⟨c.map ∘ Circle.path s t,
    c.embedded.continuous.comp (Circle.path s t).continuous⟩
  let q : C(Interval,S) := ⟨c.map ∘ (Circle.path t s).symm,
    c.embedded.continuous.comp (Circle.path t s).symm.continuous⟩
  have hp : Function.Injective p :=
    c.embedded.injective.comp (Circle.path_injective_of_ne hst)
  have hq : Function.Injective q :=
    c.embedded.injective.comp
      ((Circle.path_injective_of_ne hst.symm).comp unitInterval.symm_involutive.injective)
  have hrp : Set.range p = c.map '' Set.range (Circle.path s t) := by
    change Set.range (c.map ∘ Circle.path s t) = _
    rw [Set.range_comp]
  have hrq : Set.range q = c.map '' Set.range (Circle.path t s) := by
    change Set.range (c.map ∘ (Circle.path t s).symm) = _
    rw [Set.range_comp, Path.symm_range]
  refine ⟨p,q,(p.continuous.isClosedEmbedding hp).isEmbedding,
    (q.continuous.isClosedEmbedding hq).isEmbedding,?_,?_,?_,?_,?_,?_⟩
  · exact (congrArg c.map (Circle.path s t).source).trans hs
  · exact (congrArg c.map (Circle.path t s).symm.source).trans hs
  · exact (congrArg c.map (Circle.path s t).target).trans ht
  · exact (congrArg c.map (Circle.path t s).symm.target).trans ht
  · rw [hrp,hrq,← Set.image_union,Circle.range_path_union_range_path hst]
    exact Set.image_univ
  · rw [hrp,hrq,← Set.image_inter c.embedded.injective,
      Circle.range_path_inter_range_path hst]
    simp [hs,ht]

/-- Both raw embedded surgery branches share the produced first-return arc.
Their complementary closing arcs cover the original current curve. -/
structure SourceTwoSurgeryBranches
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : SourceFirstReturnBoundary a b) where
  closing : Bool → C(Interval,S)
  closing_embedded : ∀ i, Topology.IsEmbedding (closing i)
  closing_zero : ∀ i, closing i 0 = D.start
  closing_one : ∀ i, closing i 1 = D.finish
  closing_cover : Set.range (closing false) ∪ Set.range (closing true) = b.image
  closing_inter : Set.range (closing false) ∩ Set.range (closing true) = {D.start,D.finish}
  boundary : Bool → Curve S
  boundary_image : ∀ i, (boundary i).image = Set.range D.first ∪ Set.range (closing i)

/-- Both actual raw surgery curves are constructed. The output contains
embedded maps and exact images, not hypothetical curve classes or a
nonseparating-retention assumption. -/
theorem source_first_return_two_surgery_branches
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b) :
    Nonempty (SourceTwoSurgeryBranches D) := by
  classical
  obtain ⟨p,q,hp,hq,hp0,hq0,hp1,hq1,hcover,hinter⟩ :=
    source_curve_complementary_arcs b D.start D.finish D.start_mem.2 D.finish_mem.2 D.distinct
  let closing : Bool → C(Interval,S) := fun i => if i then q else p
  have hclosing_emb (i : Bool) : Topology.IsEmbedding (closing i) := by cases i <;> assumption
  have hclosing_zero (i : Bool) : closing i 0 = D.start := by cases i <;> assumption
  have hclosing_one (i : Bool) : closing i 1 = D.finish := by cases i <;> assumption
  have hclosing_sub (i : Bool) : Set.range (closing i) ⊆ b.image := by
    intro z hz
    rw [← hcover]
    cases i
    · exact Or.inl hz
    · exact Or.inr hz
  have hcoll (i : Bool) (s t : Interval) (he : D.first s = closing i t) :
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    by_cases hs0 : s = 0
    · left
      refine ⟨hs0,?_⟩
      apply (hclosing_emb i).injective
      rw [← he,hs0,D.first_zero,hclosing_zero]
    · have hs1 : s = 1 := by
        by_contra hn
        exact D.first_interior_avoids s hs0 hn (he ▸ hclosing_sub i ⟨t,rfl⟩)
      right
      refine ⟨hs1,?_⟩
      apply (hclosing_emb i).injective
      rw [← he,hs1,D.first_one,hclosing_one]
  have hcurves (i : Bool) : ∃ c : Curve S,
      c.image = Set.range D.first ∪ Set.range (closing i) :=
    exists_curve_of_two_arcs D.first (closing i) D.first_embedded.injective
      (hclosing_emb i).injective
      (D.first_zero.trans (hclosing_zero i).symm)
      (D.first_one.trans (hclosing_one i).symm) (hcoll i)
  choose c hc using hcurves
  exact ⟨{
    closing := closing, closing_embedded := hclosing_emb,
    closing_zero := hclosing_zero, closing_one := hclosing_one,
    closing_cover := hcover, closing_inter := hinter,
    boundary := c, boundary_image := hc }⟩

/-- The crossings retained on any closing arc, after removing the two surgery
corners, are an actual finite set strictly smaller than the old crossing set. -/
theorem source_surgery_closing_crossings_budget
    {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    let R := (Set.range (B.closing i) ∩ a.image) \ {D.start,D.finish}
    R.Finite ∧ R.ncard + 2 ≤ (a.image ∩ b.image).ncard := by
  classical
  let T := a.image ∩ b.image
  let P : Set S := {D.start,D.finish}
  let R := (Set.range (B.closing i) ∩ a.image) \ P
  have hP : P ⊆ T := by
    intro x hx
    rcases hx with hx | hx
    · exact hx ▸ D.start_mem
    · exact (Set.mem_singleton_iff.mp hx) ▸ D.finish_mem
  have hclosing_sub : Set.range (B.closing i) ⊆ b.image := by
    intro x hx
    rw [← B.closing_cover]
    cases i
    · exact Or.inl hx
    · exact Or.inr hx
  have hR : R ⊆ T \ P := by
    rintro x ⟨⟨hxc,hxa⟩,hxP⟩
    exact ⟨⟨hxa,hclosing_sub hxc⟩,hxP⟩
  have hfin : R.Finite := ht.1.sdiff.subset hR
  have hle : R.ncard ≤ (T \ P).ncard := Set.ncard_le_ncard hR ht.1.sdiff
  have he := Set.ncard_sdiff_add_ncard T P ht.1 (Set.toFinite P)
  rw [Set.union_eq_self_of_subset_right hP,Set.ncard_pair D.distinct] at he
  change R.Finite ∧ R.ncard + 2 ≤ T.ncard
  exact ⟨hfin,by omega⟩

end CurveComplex

#print axioms CurveComplex.source_curve_complementary_arcs
#print axioms CurveComplex.source_first_return_two_surgery_branches
#print axioms CurveComplex.source_surgery_closing_crossings_budget
