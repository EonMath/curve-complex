import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalGraphQuotientCommonFace

open CurveComplex Set
noncomputable local instance actualGraphDescentRegionalTerminalGraphConeFacePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- Actual terminal anchor disjointness adjoins the anchor class to every
    indexed clique, including collisions among quotient labels. -/
theorem regional_indexed_quotient_clique_anchor_face
    {X : Type*} [TopologicalSpace X]
    (Arc : Type*) (rel : Arc → Arc → Prop) (underlying : Arc → C(Interval,X))
    {ι : Type*} [DecidableEq ι] (a : ι → Arc) (anchor : Arc)
    (σ : Finset ι) (hdis : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j →
      Disjoint (Set.range (underlying (a i))) (Set.range (underlying (a j))))
    (hanchor : ∀ i ∈ σ, Disjoint (Set.range (underlying anchor))
      (Set.range (underlying (a i)))) :
    let τ := insert (Quot.mk rel anchor) (σ.image (fun i => Quot.mk rel (a i)))
    τ.Nonempty ∧ ∃ rep : ↥τ → Arc,
      (∀ z, Quot.mk rel (rep z) = z.val) ∧
      ∀ z w, z ≠ w → Disjoint (Set.range (underlying (rep z)))
        (Set.range (underlying (rep w))) := by
  classical
  dsimp only
  let family : Option ι → Arc := fun i => match i with
    | none => anchor
    | some j => a j
  let δ : Finset (Option ι) := insert none (σ.image some)
  have hδ : ∀ i ∈ δ, ∀ j ∈ δ, i ≠ j →
      Disjoint (Set.range (underlying (family i)))
        (Set.range (underlying (family j))) := by
    intro i hi j hj hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        have hjs : j ∈ σ := by simpa [δ] using hj
        exact hanchor j hjs
    | some i =>
      have his : i ∈ σ := by simpa [δ] using hi
      cases j with
      | none => exact (hanchor i his).symm
      | some j =>
        have hjs : j ∈ σ := by simpa [δ] using hj
        exact hdis i his j hjs (fun he => hij (congrArg some he))
  have hr := regional_indexed_quotient_clique_face Arc rel underlying family δ
    (Finset.insert_nonempty _ _) hδ
  have heq : δ.image (fun i => Quot.mk rel (family i)) =
      insert (Quot.mk rel anchor) (σ.image (fun i => Quot.mk rel (a i))) := by
    simp [δ,family,Finset.image_image,Function.comp_def]
  rw [heq] at hr
  exact hr

#print axioms regional_indexed_quotient_clique_anchor_face
