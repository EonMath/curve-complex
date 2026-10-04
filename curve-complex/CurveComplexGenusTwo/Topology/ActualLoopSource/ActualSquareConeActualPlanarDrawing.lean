import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConeProperWholeContactFamily
import CurveComplexGenusTwo.Topology.FiniteContactDrawing.FiniteCompatiblePlanarArcDrawing
import CurveComplexGenusTwo.Filtration.Geometry.ActualEndpointBigonEnlargement
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
/-- Actual finite four-side scalar contacts produce a proper finite planar
contact drawing of the constructed square filling. The finite embedded family
is constructed above, then passed to the canonical generic drawing producer. -/
theorem actual_square_cone_actual_planar_drawing
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (f : C({z : ℝ × ℝ // ‖z‖=1},V)) (center : V) (hc : center.val.2≠0)
    (hfinite : ∀ i : Fin 4,
      {t : Interval | (f (actualMaxNormSquareBoundaryFace i t)).val.2=0}.Finite) :
    ∃ F : C({z : ℝ × ℝ // ‖z‖≤1},V),
      (∀ z : {z : ℝ × ℝ // ‖z‖=1},F ⟨z.val,z.property.le⟩=f z) ∧
    ∃ A : Type,∃ _hA : Finite A,
    ∃ (D : Graph Plane (A × Fin 3)) (draw : (A × Fin 3) → ℝ → Plane),
      D.vertexSet.Finite ∧ D.edgeSet=univ ∧ Graph.IsDrawing D draw ∧
      actualSupPlaneProductHomeomorph.symm '' Subtype.val ''
        {u : {z : ℝ × ℝ // ‖z‖≤1} | (F u).val.2=0}=
          D.vertexSet ∪ ⋃ e,Graph.edgeArc draw e := by
  classical
  obtain ⟨F,hboundary,vertices,A,hA,arc,hends,hcollision,hclear,hembed,hinterior,hcoverage⟩ :=
    actual_square_cone_proper_whole_contact_family V hV f center hc hfinite
  let : Finite A := hA
  let embed : C({z : ℝ × ℝ // ‖z‖≤1},Plane) :=
    ⟨fun z => actualSupPlaneProductHomeomorph.symm z.val,
      actualSupPlaneProductHomeomorph.symm.continuous.comp continuous_subtype_val⟩
  have hEmbed : IsEmbedding embed := actualSupPlaneProductHomeomorph.symm.isEmbedding.comp
    IsEmbedding.subtypeVal
  let W : Set Plane := embed '' (vertices : Set {z : ℝ × ℝ // ‖z‖≤1})
  have hW : W.Finite := vertices.finite_toSet.image embed
  let p : A → C(Interval,Plane) := fun e => embed.comp (arc e)
  have hp (e) : IsEmbedding (p e) := hEmbed.comp (hembed e)
  have hstart (e) : p e 0 ∈ W := mem_image_of_mem embed (hends e).1
  have hend (e) : p e 1 ∈ W := mem_image_of_mem embed (hends e).2
  have hpclear (e) (t : Interval) (ht : t ∈ Ioo (0:Interval) 1) : p e t ∉ W := by
    rintro ⟨v,hv,he⟩
    exact hclear e t (ne_of_gt ht.1) (ne_of_lt ht.2)
      ((hEmbed.injective he) ▸ hv)
  have hpcompatible (e d) (t u : Interval) (ht : t ∈ Ioo (0:Interval) 1)
      (hu : u ∈ Ioo (0:Interval) 1) (he : p e t=p d u) : e=d := by
    rcases hcollision e d t u (hEmbed.injective he) with ⟨hed,htu⟩ | ⟨hte,hue⟩
    · exact hed
    · exact False.elim (hte.elim (ne_of_gt ht.1) (ne_of_lt ht.2))
  obtain ⟨D,draw,hvertices,hedges,hdrawing,hrange,hWvertices,hverticesW⟩ :=
    LocalSurgery.actual_finite_compatible_planar_arc_family_drawing W hW p hp hstart hend
      hpclear hpcompatible
  have hsource : W ∪ ⋃ e,range (p e)=
      actualSupPlaneProductHomeomorph.symm '' Subtype.val ''
        {u : {z : ℝ × ℝ // ‖z‖≤1} | (F u).val.2=0} := by
    ext w
    constructor
    · rintro (hw | hw)
      · obtain ⟨v,hv,rfl⟩ := hw
        exact ⟨v.val,⟨v,(hcoverage v).mpr (Or.inl hv),rfl⟩,rfl⟩
      · obtain ⟨e,t,he⟩ := mem_iUnion.mp hw
        refine ⟨(arc e t).val,⟨arc e t,(hcoverage _).mpr (Or.inr ⟨e,t,rfl⟩),rfl⟩,?_⟩
        exact he
    · rintro ⟨v,⟨u,hu,rfl⟩,rfl⟩
      rcases (hcoverage u).mp hu with hv | ⟨e,t,he⟩
      · exact Or.inl (mem_image_of_mem embed hv)
      · right
        exact mem_iUnion.mpr ⟨e,t,congrArg embed he⟩
  have harcranges : (⋃ e,range (p e))=⋃ a : A × Fin 3,Graph.edgeArc draw a := by
    ext w
    constructor
    · intro hw
      obtain ⟨e,he⟩ := mem_iUnion.mp hw
      rw [hrange e] at he
      obtain ⟨j,hj⟩ := mem_iUnion.mp he
      exact mem_iUnion.mpr ⟨(e,j),hj⟩
    · intro hw
      obtain ⟨⟨e,j⟩,he⟩ := mem_iUnion.mp hw
      apply mem_iUnion.mpr
      refine ⟨e,?_⟩
      rw [hrange e]
      exact mem_iUnion.mpr ⟨j,he⟩
  refine ⟨F,hboundary,A,hA,D,draw,hvertices,hedges,hdrawing,?_⟩
  rw [← hsource,harcranges]
  apply Subset.antisymm
  · exact union_subset_union hWvertices Subset.rfl
  · apply union_subset
    · simpa only [harcranges] using hverticesW
    · exact subset_union_right
end CurveComplex.HyperellipticModel
