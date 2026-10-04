import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualConvexCellContactRedraw
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual common-strip surface cell: the coordinate map is obtained by the
embedding inverse, then the contact filling and boundary-fixed mark-free movie
are genuinely constructed. No coordinate filling or homotopy is an input. -/
theorem actual_common_strip_cell_contact_redraw
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (hmarks : ∀ z,BC z ∉ (M.cover.branch : Set S))
    (haxis : ∀ z,BC z ∈ a.val.image ↔ z.2.val=0)
    (original : C(Interval × Interval,S)) (Q : C(Interval × Interval,range BC))
    (hQ : ∀ z,(Q z).val=original z)
    (hbottom : {t : Interval | original (t,0) ∈ a.val.image}.Finite)
    (hright : {t : Interval | original (1,t) ∈ a.val.image}.Finite)
    (htop : {t : Interval | original (t,1) ∈ a.val.image}.Finite)
    (hleft : {t : Interval | original (0,t) ∈ a.val.image}.Finite)
    (center : Interval × Icc (-1:ℝ) 1) (hc : center.2.val≠0) :
    ∃ G : C(Interval × Interval,S),∃ H : C((Interval × Interval) × Interval,S),
      (∀ z,H (z,0)=original z) ∧ (∀ z,H (z,1)=G z) ∧
      (∀ z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → H (z,σ)=original z) ∧
      (∀ z,H z ∉ (M.cover.branch : Set S)) ∧
    ∃ vertices : Finset (Interval × Interval),
    ∃ A : Type,∃ _hA : Finite A,∃ arc : A → C(Interval,Interval × Interval),
      (∀ e,arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices) ∧
      (∀ e d t u,arc e t=arc d u → (e=d ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1))) ∧
      (∀ e t,t≠0 → t≠1 → arc e t ∉ vertices) ∧
      (∀ e,IsEmbedding (arc e)) ∧
      (∀ e t,0<t.val → t.val<1 →
        0<(arc e t).1.val ∧ (arc e t).1.val<1 ∧ 0<(arc e t).2.val ∧ (arc e t).2.val<1) ∧
      (∀ z,G z ∈ a.val.image ↔ z ∈ vertices ∨ ∃ e t,arc e t=z) := by
  let V : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1
  have hV : Convex ℝ V := (convex_Icc (0:ℝ) 1).prod (convex_Icc (-1:ℝ) 1)
  let decode : V → Interval × Icc (-1:ℝ) 1 := fun z =>
    (⟨z.val.1,z.property.1⟩,⟨z.val.2,z.property.2⟩)
  have hdecode : Continuous decode := by fun_prop
  let coord : C(Interval × Interval,V) :=
    ⟨fun z => ⟨(((hBC.toHomeomorph.symm (Q z)).1:ℝ),
      ((hBC.toHomeomorph.symm (Q z)).2:ℝ)),
        (hBC.toHomeomorph.symm (Q z)).1.property,(hBC.toHomeomorph.symm (Q z)).2.property⟩,
      by fun_prop⟩
  have hcoord (z) : BC (decode (coord z))=original z :=
    (congrArg Subtype.val (hBC.toHomeomorph.apply_symm_apply (Q z))).trans (hQ z)
  have hzero (z) : (coord z).val.2=0 ↔ original z ∈ a.val.image := by
    have hh := (haxis (decode (coord z))).symm
    rw [hcoord] at hh
    exact hh
  let c : V := ⟨(center.1.val,center.2.val),center.1.property,center.2.property⟩
  have hf0 : {t : Interval | (coord (t,0)).val.2=0}.Finite := by
    simpa only [hzero] using hbottom
  have hf1 : {t : Interval | (coord (1,t)).val.2=0}.Finite := by
    simpa only [hzero] using hright
  have hf2 : {t : Interval | (coord (t,1)).val.2=0}.Finite := by
    simpa only [hzero] using htop
  have hf3 : {t : Interval | (coord (0,t)).val.2=0}.Finite := by
    simpa only [hzero] using hleft
  obtain ⟨F,R,hstart,hend,hboundary,vertices,A,hA,arc,hends,hcollision,hclear,
    hembed,hinterior,hcoverage⟩ := actual_convex_cell_contact_redraw V hV coord hf0 hf1 hf2 hf3 c hc
  let G : C(Interval × Interval,S) :=
    ⟨fun z => BC (decode (F z)),hBC.continuous.comp (hdecode.comp F.continuous)⟩
  let H : C((Interval × Interval) × Interval,S) :=
    ⟨fun z => BC (decode (R z)),hBC.continuous.comp (hdecode.comp R.continuous)⟩
  refine ⟨G,H,?_,?_,?_,(fun z => hmarks (decode (R z))),vertices,A,hA,arc,
    hends,hcollision,hclear,hembed,hinterior,?_⟩
  · intro z
    change BC (decode (R (z,0)))=original z
    rw [hstart,hcoord]
  · intro z
    change BC (decode (R (z,1)))=BC (decode (F z))
    rw [hend]
  · intro z σ hz
    change BC (decode (R (z,σ)))=original z
    rw [hboundary z σ hz,hcoord]
  · intro z
    exact (haxis (decode (F z))).trans (hcoverage z)
end CurveComplex.HyperellipticModel
