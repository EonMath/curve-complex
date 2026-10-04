import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourPathCellContactFamily
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual coordinate cell with finite contacts on its four literal sides
produces a contact filling and a genuinely constructed boundary-fixed movie
from the original cell. No cell homotopy or contact family is assumed. -/
theorem actual_convex_cell_contact_redraw
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (original : C(Interval × Interval,V))
    (hbottom : {t : Interval | (original (t,0)).val.2=0}.Finite)
    (hright : {t : Interval | (original (1,t)).val.2=0}.Finite)
    (htop : {t : Interval | (original (t,1)).val.2=0}.Finite)
    (hleft : {t : Interval | (original (0,t)).val.2=0}.Finite)
    (center : V) (hc : center.val.2≠0) :
    ∃ G : C(Interval × Interval,V),∃ H : C((Interval × Interval) × Interval,V),
      (∀ z,H (z,0)=original z) ∧ (∀ z,H (z,1)=G z) ∧
      (∀ z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → H (z,σ)=original z) ∧
    ∃ vertices : Finset (Interval × Interval),
    ∃ A : Type,∃ _hA : Finite A,∃ arc : A → C(Interval,Interval × Interval),
      (∀ e,arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices) ∧
      (∀ e d t u,arc e t=arc d u → (e=d ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1))) ∧
      (∀ e t,t≠0 → t≠1 → arc e t ∉ vertices) ∧
      (∀ e,IsEmbedding (arc e)) ∧
      (∀ e t,0<t.val → t.val<1 →
        0<(arc e t).1.val ∧ (arc e t).1.val<1 ∧ 0<(arc e t).2.val ∧ (arc e t).2.val<1) ∧
      (∀ z,(G z).val.2=0 ↔ z ∈ vertices ∨ ∃ e t,arc e t=z) := by
  let bottom : Path (original (0,0)) (original (1,0)) :=
    ⟨⟨fun t => original (t,0),by fun_prop⟩,rfl,rfl⟩
  let right : Path (original (1,0)) (original (1,1)) :=
    ⟨⟨fun t => original (1,t),by fun_prop⟩,rfl,rfl⟩
  let top : Path (original (0,1)) (original (1,1)) :=
    ⟨⟨fun t => original (t,1),by fun_prop⟩,rfl,rfl⟩
  let left : Path (original (0,0)) (original (0,1)) :=
    ⟨⟨fun t => original (0,t),by fun_prop⟩,rfl,rfl⟩
  obtain ⟨G,hSides,vertices,A,hA,arc,hends,hcollision,hclear,hembed,hinterior,hcoverage⟩ :=
    actual_four_path_cell_contact_family V hV bottom right top left hbottom hright htop hleft center hc
  have hboundary (z : Interval × Interval) (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
      G z=original z := by
    rcases hz with h | h | h | h
    · have he : z=(0,z.2) := Prod.ext h rfl
      rw [he]
      exact (hSides z.2).2.2.2
    · have he : z=(1,z.2) := Prod.ext h rfl
      rw [he]
      exact (hSides z.2).2.1
    · have he : z=(z.1,0) := Prod.ext rfl h
      rw [he]
      exact (hSides z.1).1
    · have he : z=(z.1,1) := Prod.ext rfl h
      rw [he]
      exact (hSides z.1).2.2.1
  let H : C((Interval × Interval) × Interval,V) :=
    ⟨fun z => ⟨(1-z.2.val) • (original z.1).val+z.2.val • (G z.1).val,
      hV (original z.1).property (G z.1).property
        (sub_nonneg.mpr z.2.property.2) z.2.property.1 (by ring)⟩,by fun_prop⟩
  refine ⟨G,H,?_,?_,?_,vertices,A,hA,arc,hends,hcollision,hclear,hembed,hinterior,hcoverage⟩
  · intro z
    apply Subtype.ext
    change (1-(0:ℝ)) • (original z).val+(0:ℝ) • (G z).val=(original z).val
    simp
  · intro z
    apply Subtype.ext
    change (1-(1:ℝ)) • (original z).val+(1:ℝ) • (G z).val=(G z).val
    simp
  · intro z σ hz
    apply Subtype.ext
    change (1-σ.val) • (original z).val+σ.val • (G z).val=(original z).val
    rw [hboundary z hz,← add_smul]
    simp
end CurveComplex.HyperellipticModel
