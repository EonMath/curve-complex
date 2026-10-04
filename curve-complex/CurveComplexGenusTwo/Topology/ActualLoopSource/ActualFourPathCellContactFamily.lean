import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourSideFiniteScalarContactBoundary
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Four literal edge paths with actual finite scalar contacts produce a whole
parameter-cell filling and finite proper compatible contact family. The filling
retains all four paths, not just their endpoint images. -/
theorem actual_four_path_cell_contact_family
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V) {bl br tl tr : V}
    (bottom : Path bl br) (right : Path br tr) (top : Path tl tr) (left : Path bl tl)
    (hbottom : {t : Interval | (bottom t).val.2=0}.Finite)
    (hright : {t : Interval | (right t).val.2=0}.Finite)
    (htop : {t : Interval | (top t).val.2=0}.Finite)
    (hleft : {t : Interval | (left t).val.2=0}.Finite)
    (center : V) (hc : center.val.2≠0) :
    ∃ G : C(Interval × Interval,V),
      (∀ t,G (t,0)=bottom t ∧ G (1,t)=right t ∧ G (t,1)=top t ∧ G (0,t)=left t) ∧
    ∃ vertices : Finset (Interval × Interval),
    ∃ A : Type,∃ _hA : Finite A,∃ arc : A → C(Interval,Interval × Interval),
      (∀ e,arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices) ∧
      (∀ e d t u,arc e t=arc d u → (e=d ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1))) ∧
      (∀ e t,t≠0 → t≠1 → arc e t ∉ vertices) ∧
      (∀ e,IsEmbedding (arc e)) ∧
      (∀ e t,0<t.val → t.val<1 →
        0<(arc e t).1.val ∧ (arc e t).1.val<1 ∧ 0<(arc e t).2.val ∧ (arc e t).2.val<1) ∧
      (∀ z,(G z).val.2=0 ↔ z ∈ vertices ∨ ∃ e t,arc e t=z) := by
  classical
  obtain ⟨f,hvalues,hfinite⟩ := actual_four_side_finite_scalar_contact_boundary V
    bottom right top left hbottom hright htop hleft
  obtain ⟨F,hboundary,vertex0,A,hA,arc0,hends,hcollision,hclear,hembed,hinterior,hcoverage⟩ :=
    actual_square_cone_proper_whole_contact_family V hV f center hc hfinite
  let G : C(Interval × Interval,V) :=
    ⟨fun z => F (actualNormalizedMaxNormSquare.symm z),
      F.continuous.comp actualNormalizedMaxNormSquare.symm.continuous⟩
  let vertices := vertex0.image actualNormalizedMaxNormSquare
  let arc : A → C(Interval,Interval × Interval) := fun e =>
    ⟨fun t => actualNormalizedMaxNormSquare (arc0 e t),
      actualNormalizedMaxNormSquare.continuous.comp (arc0 e).continuous⟩
  have hsides (t : Interval) :
      G (t,0)=bottom t ∧ G (1,t)=right t ∧ G (t,1)=top t ∧ G (0,t)=left t := by
    have hb : actualNormalizedMaxNormSquare.symm (t,0)=
        ⟨(actualMaxNormSquareBoundaryFace 0 t).val,(actualMaxNormSquareBoundaryFace 0 t).property.le⟩ := by
      apply Subtype.ext
      change (2*t.val-1,2*(0:ℝ)-1)=(2*t.val-1,-1)
      norm_num
    have hr : actualNormalizedMaxNormSquare.symm (1,t)=
        ⟨(actualMaxNormSquareBoundaryFace 1 t).val,(actualMaxNormSquareBoundaryFace 1 t).property.le⟩ := by
      apply Subtype.ext
      change (2*(1:ℝ)-1,2*t.val-1)=(1,2*t.val-1)
      norm_num
    have ht : actualNormalizedMaxNormSquare.symm (t,1)=
        ⟨(actualMaxNormSquareBoundaryFace 2 t).val,(actualMaxNormSquareBoundaryFace 2 t).property.le⟩ := by
      apply Subtype.ext
      change (2*t.val-1,2*(1:ℝ)-1)=(2*t.val-1,1)
      norm_num
    have hl : actualNormalizedMaxNormSquare.symm (0,t)=
        ⟨(actualMaxNormSquareBoundaryFace 3 t).val,(actualMaxNormSquareBoundaryFace 3 t).property.le⟩ := by
      apply Subtype.ext
      change (2*(0:ℝ)-1,2*t.val-1)=(-1,2*t.val-1)
      norm_num
    change F (actualNormalizedMaxNormSquare.symm (t,0))=bottom t ∧
      F (actualNormalizedMaxNormSquare.symm (1,t))=right t ∧
      F (actualNormalizedMaxNormSquare.symm (t,1))=top t ∧
      F (actualNormalizedMaxNormSquare.symm (0,t))=left t
    rw [hb,hr,ht,hl,hboundary,hboundary,hboundary,hboundary,hvalues,hvalues,hvalues,hvalues]
    norm_num
  refine ⟨G,hsides,vertices,A,hA,arc,?_,?_,?_,?_,?_,?_⟩
  · intro e
    exact ⟨Finset.mem_image.mpr ⟨arc0 e 0,(hends e).1,rfl⟩,
      Finset.mem_image.mpr ⟨arc0 e 1,(hends e).2,rfl⟩⟩
  · intro e d t u he
    exact hcollision e d t u (actualNormalizedMaxNormSquare.injective he)
  · intro e t ht0 ht1 hv
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hv
    exact hclear e t ht0 ht1 ((actualNormalizedMaxNormSquare.injective he) ▸ hv)
  · intro e
    exact actualNormalizedMaxNormSquare.isEmbedding.comp (hembed e)
  · intro e t ht0 ht1
    exact (actual_normalized_max_norm_square_interior _).mp (hinterior e t ht0 ht1)
  · intro z
    change (F (actualNormalizedMaxNormSquare.symm z)).val.2=0 ↔ _
    rw [hcoverage]
    constructor
    · rintro (hv | ⟨e,t,he⟩)
      · exact Or.inl (Finset.mem_image.mpr ⟨_,hv,actualNormalizedMaxNormSquare.apply_symm_apply z⟩)
      · right
        exact ⟨e,t,(congrArg actualNormalizedMaxNormSquare he).trans
          (actualNormalizedMaxNormSquare.apply_symm_apply z)⟩
    · rintro (hv | ⟨e,t,he⟩)
      · obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hv
        left
        have hh : v=actualNormalizedMaxNormSquare.symm z := by
          exact (actualNormalizedMaxNormSquare.symm_apply_apply v).symm.trans
            (congrArg actualNormalizedMaxNormSquare.symm he)
        exact hh ▸ hv
      · right
        refine ⟨e,t,?_⟩
        exact (actualNormalizedMaxNormSquare.symm_apply_apply (arc0 e t)).symm.trans
          (congrArg actualNormalizedMaxNormSquare.symm he)
end CurveComplex.HyperellipticModel
