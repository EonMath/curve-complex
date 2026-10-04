import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualGraphCrossing
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualBothCornerTranslations
namespace CurveComplex
open Set Topology Schoenflies
/-- Every actual contact of a translated corner with the vertical old axis
is a genuine topological crossing. The other half-axis is excluded on an
open neighborhood produced from its nonzero normal shift. -/
theorem source_translated_corner_vertical_crossing
    {S : Type} [TopologicalSpace S]
    (a d : Curve S) (E : OpenPartialHomeomorph S Plane)
    (V : Set S) (hV : IsOpen V) (hVs : V ⊆ E.source)
    (v : Plane) (hv0 : v 0 ≠ 0)
    (ha : ∀ x ∈ E.source, x ∈ a.image ↔ E x 0=0)
    (hd : ∀ x ∈ V, x ∈ d.image ↔
      (E x 0=v 0 ∧ v 1≤E x 1) ∨ (v 0≤E x 0 ∧ E x 1=v 1))
    (p : S) (hp : p ∈ V ∩ d.image ∩ a.image) : CrossesAt a d p := by
  have hp0 : E p 0=0 := (ha p (hVs hp.1.1)).mp hp.2
  have hp1 : E p 1=v 1 := by
    rcases (hd p hp.1.1).mp hp.1.2 with hh | hh
    · exact (hv0 (hh.1.symm.trans hp0)).elim
    · exact hh.2
  have hvneg : v 0<0 := by
    rcases (hd p hp.1.1).mp hp.1.2 with hh | hh
    · exact (hv0 (hh.1.symm.trans hp0)).elim
    · exact lt_of_le_of_ne (by linarith [hh.1]) hv0
  let W : Set S := V ∩ (E.source ∩ E ⁻¹' {z : Plane | v 0/2<z 0})
  have hW : IsOpen W := hV.inter (E.isOpen_inter_preimage
    (isOpen_lt continuous_const (by fun_prop)))
  have hpW : p ∈ W := ⟨hp.1.1,hVs hp.1.1,by change v 0/2<E p 0; rw [hp0]; linarith⟩
  let F := E.restr W
  have hFs : F.source=E.source ∩ W := by simp [F,hW.interior_eq]
  have hpF : p ∈ F.source := by rw [hFs]; exact ⟨hVs hp.1.1,hpW⟩
  apply source_continuous_graph_crossing a d F p hpF hp0
    (fun _ => v 1) continuous_const hp1
  · intro x hx
    exact ha x ((hFs).le hx).1
  · intro x hx
    have hxW := ((hFs).le hx).2
    have hxgt : v 0/2<E x 0 := hxW.2.2
    change x ∈ d.image ↔ E x 1=v 1
    rw [hd x hxW.1]
    constructor
    · rintro (hh | hh)
      · have he : E x 0=v 0 := hh.1
        linarith
      · exact hh.2
    · intro hh
      exact Or.inr ⟨by linarith,hh⟩

/-- The horizontal-axis contacts are also actual crossings, with the
coordinate swap constructed as an actual plane homeomorphism. -/
theorem source_translated_corner_horizontal_crossing
    {S : Type} [TopologicalSpace S]
    (b d : Curve S) (E : OpenPartialHomeomorph S Plane)
    (V : Set S) (hV : IsOpen V) (hVs : V ⊆ E.source)
    (v : Plane) (hv1 : v 1 ≠ 0)
    (hb : ∀ x ∈ E.source, x ∈ b.image ↔ E x 1=0)
    (hd : ∀ x ∈ V, x ∈ d.image ↔
      (E x 0=v 0 ∧ v 1≤E x 1) ∨ (v 0≤E x 0 ∧ E x 1=v 1))
    (p : S) (hp : p ∈ V ∩ d.image ∩ b.image) : CrossesAt b d p := by
  let J : Plane ≃ₜ Plane := {
    toEquiv := {
      toFun := fun z => Plane.mk (z 1) (z 0)
      invFun := fun z => Plane.mk (z 1) (z 0)
      left_inv := by intro z; ext j; fin_cases j <;> rfl
      right_inv := by intro z; ext j; fin_cases j <;> rfl }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let F := E.trans J.toOpenPartialHomeomorph
  have hFs : F.source=E.source := by simp [F]
  apply source_translated_corner_vertical_crossing b d F V hV
    (fun _ hx => hFs.symm ▸ hVs hx) (Plane.mk (v 1) (v 0)) hv1
    (fun x hx => hb x (hFs ▸ hx)) ?_ p hp
  intro x hx
  change x ∈ d.image ↔
    (E x 1=v 1 ∧ v 0≤E x 0) ∨ (v 1≤E x 1 ∧ E x 0=v 0)
  rw [hd x hx]
  tauto
end CurveComplex
#print axioms CurveComplex.source_translated_corner_vertical_crossing
#print axioms CurveComplex.source_translated_corner_horizontal_crossing
