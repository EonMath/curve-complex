import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.Foundations.ConeRealization

open CurveComplex Set
noncomputable local instance actualGraphDescentRegionalCommonFaceInsertPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- Insert a class-changing surgery vertex while retaining the old label,
    using the actual disjoint copy of the old representative. -/
theorem regional_intrinsic_face_insert_common_vertex
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (Arc : Type*) (rel : Arc → Arc → Prop)
    (underlying : Arc → C(Interval,↥F))
    (τ : Finset (Quot rel)) (rep : ↥τ → Arc)
    (hlabel : ∀ z, Quot.mk rel (rep z) = z.val)
    (hdisjoint : ∀ z w, z ≠ w →
      Disjoint (Set.range (underlying (rep z)))
        (Set.range (underlying (rep w))))
    (u : ↥τ) (copy branch : Arc)
    (hcopyLabel : Quot.mk rel copy = u.val)
    (hcopyOther : ∀ z : ↥τ, z ≠ u →
      Disjoint (Set.range (underlying copy))
        (Set.range (underlying (rep z))))
    (hbranchCopy : Disjoint (Set.range (underlying branch))
      (Set.range (underlying copy)))
    (hbranchOther : ∀ z : ↥τ, z ≠ u →
      Disjoint (Set.range (underlying branch))
        (Set.range (underlying (rep z)))) :
    let newLabel := Quot.mk rel branch
    let commonFace := insert newLabel τ
    commonFace.Nonempty ∧
      ∃ family : ↥commonFace → Arc,
        (∀ z, Quot.mk rel (family z) = z.val) ∧
        ∀ z w, z ≠ w →
          Disjoint (Set.range (underlying (family z)))
            (Set.range (underlying (family w))) := by
  classical
  dsimp only
  let newLabel : Quot rel := Quot.mk rel branch
  let commonFace := insert newLabel τ
  let oldFamily : ↥τ → Arc := fun z => if z = u then copy else rep z
  have hOldLabel : ∀ z : ↥τ, Quot.mk rel (oldFamily z) = z.val := by
    intro z
    by_cases hzu : z = u
    · simpa [oldFamily,hzu] using hcopyLabel
    · simpa [oldFamily,hzu] using hlabel z
  have hOldDisjoint : ∀ z w : ↥τ, z ≠ w →
      Disjoint (Set.range (underlying (oldFamily z)))
        (Set.range (underlying (oldFamily w))) := by
    intro z w hzw
    by_cases hzu : z = u
    · have hwu : w ≠ u := fun h => hzw (hzu.trans h.symm)
      simpa [oldFamily,hzu,hwu] using hcopyOther w hwu
    · by_cases hwu : w = u
      · simpa [oldFamily,hzu,hwu] using (hcopyOther z hzu).symm
      · simpa [oldFamily,hzu,hwu] using hdisjoint z w hzw
  have hNewAvoid : ∀ z : ↥τ,
      Disjoint (Set.range (underlying branch))
        (Set.range (underlying (oldFamily z))) := by
    intro z
    by_cases hzu : z = u
    · simpa [oldFamily,hzu] using hbranchCopy
    · simpa [oldFamily,hzu] using hbranchOther z hzu
  by_cases hdup : newLabel ∈ τ
  · have heq : commonFace = τ := Finset.insert_eq_of_mem hdup
    have hresult : τ.Nonempty ∧
        ∃ family : ↥τ → Arc,
          (∀ z, Quot.mk rel (family z) = z.val) ∧
          ∀ z w, z ≠ w →
            Disjoint (Set.range (underlying (family z)))
              (Set.range (underlying (family w))) :=
      ⟨⟨newLabel,hdup⟩,oldFamily,hOldLabel,hOldDisjoint⟩
    have hgoal : commonFace.Nonempty ∧
        ∃ family : ↥commonFace → Arc,
          (∀ z, Quot.mk rel (family z) = z.val) ∧
          ∀ z w, z ≠ w →
            Disjoint (Set.range (underlying (family z)))
              (Set.range (underlying (family w))) := by
      rw [heq]
      exact hresult
    exact hgoal
  · let family : ↥commonFace → Arc := fun z =>
      if hz : z.val = newLabel then branch
      else oldFamily ⟨z.val,
        (Finset.mem_insert.mp z.property).resolve_left hz⟩
    refine ⟨⟨newLabel,Finset.mem_insert_self _ _⟩,family,?_,?_⟩
    · intro z
      by_cases hz : z.val = newLabel
      · simp [family,hz,newLabel]
      · simpa [family,hz] using hOldLabel
          ⟨z.val,(Finset.mem_insert.mp z.property).resolve_left hz⟩
    · intro z w hzw
      by_cases hz : z.val = newLabel
      · have hw : w.val ≠ newLabel := by
          intro he
          exact hzw (Subtype.ext (hz.trans he.symm))
        simpa [family,hz,hw] using hNewAvoid
          ⟨w.val,(Finset.mem_insert.mp w.property).resolve_left hw⟩
      · by_cases hw : w.val = newLabel
        · simpa [family,hz,hw] using (hNewAvoid
            ⟨z.val,(Finset.mem_insert.mp z.property).resolve_left hz⟩).symm
        · simp only [family,dite_eq_right hz,dite_eq_right hw]
          apply hOldDisjoint
          intro he
          have hv : z.val = w.val :=
            congrArg (fun q : ↥τ => (q : Quot rel)) he
          exact hzw (Subtype.ext hv)

#print axioms regional_intrinsic_face_insert_common_vertex
