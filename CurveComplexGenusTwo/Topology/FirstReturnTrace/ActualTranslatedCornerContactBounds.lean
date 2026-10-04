import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualTranslatedCornerCrossings
namespace CurveComplex
open Set Topology Schoenflies
/-- Derive the exact local crossing budget on an actual translated corner
portion; no finiteness or bound is supplied as a hypothesis. -/
theorem source_translated_corner_contact_bounds
    {S : Type} [TopologicalSpace S]
    (a b : Curve S) (E : OpenPartialHomeomorph S Plane) (T : Set S)
    (hTs : T ⊆ E.source) (v : Plane) (hv0 : v 0 ≠ 0) (hv1 : v 1 ≠ 0)
    (ha : ∀ x ∈ E.source, x ∈ a.image ↔ E x 0=0)
    (hb : ∀ x ∈ E.source, x ∈ b.image ↔ E x 1=0)
    (hshape : ∀ x ∈ T,
      (E x 0=v 0 ∧ v 1≤E x 1) ∨ (v 0≤E x 0 ∧ E x 1=v 1)) :
    (T ∩ a.image).Finite ∧ (T ∩ b.image).Finite ∧
      (T ∩ a.image).ncard≤1 ∧ (T ∩ b.image).ncard≤1 ∧
      (0<v 0 → Disjoint T a.image) ∧ (0<v 1 → Disjoint T b.image) := by
  have hsuba : (T ∩ a.image).Subsingleton := by
    rintro x ⟨hxT,hxa⟩ y ⟨hyT,hya⟩
    have hx0 := (ha x (hTs hxT)).mp hxa
    have hy0 := (ha y (hTs hyT)).mp hya
    have hx1 : E x 1=v 1 := by
      rcases hshape x hxT with hh | hh
      · exact (hv0 (hh.1.symm.trans hx0)).elim
      · exact hh.2
    have hy1 : E y 1=v 1 := by
      rcases hshape y hyT with hh | hh
      · exact (hv0 (hh.1.symm.trans hy0)).elim
      · exact hh.2
    apply E.injOn (hTs hxT) (hTs hyT)
    ext j
    fin_cases j
    · exact hx0.trans hy0.symm
    · exact hx1.trans hy1.symm
  have hsubb : (T ∩ b.image).Subsingleton := by
    rintro x ⟨hxT,hxb⟩ y ⟨hyT,hyb⟩
    have hx1 := (hb x (hTs hxT)).mp hxb
    have hy1 := (hb y (hTs hyT)).mp hyb
    have hx0 : E x 0=v 0 := by
      rcases hshape x hxT with hh | hh
      · exact hh.1
      · exact (hv1 (hh.2.symm.trans hx1)).elim
    have hy0 : E y 0=v 0 := by
      rcases hshape y hyT with hh | hh
      · exact hh.1
      · exact (hv1 (hh.2.symm.trans hy1)).elim
    apply E.injOn (hTs hxT) (hTs hyT)
    ext j
    fin_cases j
    · exact hx0.trans hy0.symm
    · exact hx1.trans hy1.symm
  refine ⟨hsuba.finite,hsubb.finite,
    (Set.ncard_le_one hsuba.finite).mpr (fun _ hx _ hy => hsuba hx hy),
    (Set.ncard_le_one hsubb.finite).mpr (fun _ hx _ hy => hsubb hx hy),?_,?_⟩
  · intro hpos
    apply Set.disjoint_left.mpr
    rintro x hxT hxa
    have hx0 := (ha x (hTs hxT)).mp hxa
    rcases hshape x hxT with hh | hh <;> linarith [hh.1]
  · intro hpos
    apply Set.disjoint_left.mpr
    rintro x hxT hxb
    have hx1 := (hb x (hTs hxT)).mp hxb
    rcases hshape x hxT with hh | hh <;> linarith [hh.2]
end CurveComplex
#print axioms CurveComplex.source_translated_corner_contact_bounds
