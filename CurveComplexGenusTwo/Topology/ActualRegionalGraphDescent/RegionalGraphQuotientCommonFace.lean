import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalCommonFaceInsert

open CurveComplex Set
noncomputable local instance actualGraphDescentRegionalGraphQuotientCommonFacePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- A finite indexed clique exports a literal quotient face, with no
    injectivity assumption on its quotient labels. -/
theorem regional_indexed_quotient_clique_face
    {X : Type*} [TopologicalSpace X] (Arc : Type*) (rel : Arc → Arc → Prop)
    (underlying : Arc → C(Interval,X)) {ι : Type*} [DecidableEq ι]
    (a : ι → Arc) (σ : Finset ι) (hne : σ.Nonempty)
    (hdis : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j →
      Disjoint (Set.range (underlying (a i))) (Set.range (underlying (a j)))) :
    let τ := σ.image (fun i => Quot.mk rel (a i))
    τ.Nonempty ∧ ∃ rep : ↥τ → Arc,
      (∀ z, Quot.mk rel (rep z) = z.val) ∧
      ∀ z w, z ≠ w → Disjoint (Set.range (underlying (rep z)))
        (Set.range (underlying (rep w))) := by
  classical
  dsimp only
  let τ := σ.image (fun i => Quot.mk rel (a i))
  have hex : ∀ z : ↥τ, ∃ i : ↥σ, Quot.mk rel (a i.val) = z.val := by
    intro z
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp z.property
    exact ⟨⟨i,hi⟩,he⟩
  choose pick hpick using hex
  refine ⟨hne.image _,(fun z => a (pick z).val),hpick,?_⟩
  intro z w hzw
  apply hdis (pick z).val (pick z).property (pick w).val (pick w).property
  intro he
  exact hzw (Subtype.ext ((hpick z).symm.trans
    ((congrArg (fun i => Quot.mk rel (a i)) he).trans (hpick w))))

/-- One chosen replacement and old-class copy work on EVERY indexed clique
    containing the selected index. Duplicate quotient labels are handled by
    the existing quotient-face insertion API. -/
theorem regional_indexed_graph_quotient_common_face
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (Arc : Type*) (rel : Arc → Arc → Prop)
    (underlying : Arc → C(Interval,↥F)) {ι : Type*} [DecidableEq ι]
    (a : ι → Arc) (adjacent : ι → ι → Prop)
    (hdis : ∀ i j, adjacent i j →
      Disjoint (Set.range (underlying (a i))) (Set.range (underlying (a j))))
    (k : ι) (branch copy : Arc)
    (hcopyLabel : Quot.mk rel copy = Quot.mk rel (a k))
    (hcopyOther : ∀ i, adjacent k i →
      Disjoint (Set.range (underlying copy)) (Set.range (underlying (a i))))
    (hbranchCopy : Disjoint (Set.range (underlying branch))
      (Set.range (underlying copy)))
    (hbranchOther : ∀ i, adjacent k i →
      Disjoint (Set.range (underlying branch)) (Set.range (underlying (a i))))
    (σ : Finset ι) (hk : k ∈ σ)
    (hclique : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → adjacent i j) :
    let τ := σ.image (fun i => Quot.mk rel (a i))
    (insert (Quot.mk rel branch) τ).Nonempty ∧
      ∃ rep : ↥(insert (Quot.mk rel branch) τ) → Arc,
        (∀ z, Quot.mk rel (rep z) = z.val) ∧
        ∀ z w, z ≠ w → Disjoint (Set.range (underlying (rep z)))
          (Set.range (underlying (rep w))) := by
  classical
  dsimp only
  let τ := σ.image (fun i => Quot.mk rel (a i))
  have hex : ∀ z : ↥τ, ∃ i : ↥σ, Quot.mk rel (a i.val) = z.val := by
    intro z
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp z.property
    exact ⟨⟨i,hi⟩,he⟩
  choose pick hpick using hex
  let chosen : ↥τ → ↥σ := fun z =>
    if z.val = Quot.mk rel (a k) then ⟨k,hk⟩ else pick z
  have hchosen : ∀ z, Quot.mk rel (a (chosen z).val) = z.val := by
    intro z
    by_cases hz : z.val = Quot.mk rel (a k)
    · simpa [chosen,hz] using hz.symm
    · simpa [chosen,hz] using hpick z
  let rep : ↥τ → Arc := fun z => a (chosen z).val
  have hrdis : ∀ z w : ↥τ, z ≠ w →
      Disjoint (Set.range (underlying (rep z))) (Set.range (underlying (rep w))) := by
    intro z w hzw
    apply hdis
    apply hclique (chosen z).val (chosen z).property (chosen w).val (chosen w).property
    intro he
    exact hzw (Subtype.ext ((hchosen z).symm.trans
      ((congrArg (fun i => Quot.mk rel (a i)) he).trans (hchosen w))))
  let u : ↥τ := ⟨Quot.mk rel (a k),Finset.mem_image.mpr ⟨k,hk,rfl⟩⟩
  have hother : ∀ z : ↥τ, z ≠ u → adjacent k (chosen z).val := by
    intro z hzu
    apply hclique k hk (chosen z).val (chosen z).property
    intro he
    have heq : z.val = Quot.mk rel (a k) := by
      rw [← hchosen z,← he]
    exact hzu (Subtype.ext heq)
  exact regional_intrinsic_face_insert_common_vertex Arc rel underlying τ rep
    hchosen hrdis u copy branch hcopyLabel
    (fun z hz => hcopyOther _ (hother z hz)) hbranchCopy
    (fun z hz => hbranchOther _ (hother z hz))

#print axioms regional_indexed_quotient_clique_face
#print axioms regional_indexed_graph_quotient_common_face
