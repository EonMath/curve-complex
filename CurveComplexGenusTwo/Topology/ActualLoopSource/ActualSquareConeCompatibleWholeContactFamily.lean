import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConeCoherentFiniteFaceArcs
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMeshIntervalParameterCover
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourFaceMeshDirectionCollision
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual four-side boundary with finite scalar contacts produces a finite
embedded-arc family covering EVERY contact of the constructed square filling.
Finite vertices and arcs are outputs, not a presumed contact certificate. -/
theorem actual_square_cone_compatible_whole_contact_family
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (f : C({z : ℝ × ℝ // ‖z‖=1},V)) (center : V) (hc : center.val.2≠0)
    (hfinite : ∀ i : Fin 4,
      {t : Interval | (f (actualMaxNormSquareBoundaryFace i t)).val.2=0}.Finite) :
    ∃ G : C({z : ℝ × ℝ // ‖z‖≤1},V),
      (∀ z : {z : ℝ × ℝ // ‖z‖=1},G ⟨z.val,z.property.le⟩=f z) ∧
    ∃ vertices : Finset {z : ℝ × ℝ // ‖z‖≤1},
    ∃ A : Type,∃ _hA : Finite A,∃ arc : A → C(Interval,{z : ℝ × ℝ // ‖z‖≤1}),
      (∀ e,arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices) ∧
      (∀ e f t u,arc e t=arc f u →
        (e=f ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1))) ∧
      (∀ e,IsEmbedding (arc e)) ∧
      (∀ e t,0<t.val → t.val<1 → ‖(arc e t).val‖<1) ∧
      (∀ u,(G u).val.2=0 ↔ u ∈ vertices ∨ ∃ e t,arc e t=u) := by
  classical
  obtain ⟨G,hboundary,q,hinj,hq,hzero,hcomplete,hfaces⟩ :=
    actual_square_cone_coherent_finite_face_arcs V hV f center hc actualMaxNormSquareBoundaryFace
      actual_max_norm_square_boundary_face_embedding hfinite
  choose m mesh negative hmono h0 h1 hnegative hcover arcs hformula hembed harczero harcinterior using hfaces
  let N := {z : {z : ℝ × ℝ // ‖z‖=1} | (f z).val.2/center.val.2≤0}
  let Z : Set {z : ℝ × ℝ // ‖z‖=1} := {z | (f z).val.2=0}
  have hfZ : Z.Finite := by
    have hsub : Z ⊆ ⋃ i : Fin 4,actualMaxNormSquareBoundaryFace i ''
        {t : Interval | (f (actualMaxNormSquareBoundaryFace i t)).val.2=0} := by
      intro z hz
      obtain ⟨i,t,he⟩ := actual_max_norm_square_boundary_cover z
      have ht : (f (actualMaxNormSquareBoundaryFace i t)).val.2=0 := by
        rw [he]
        exact hz
      exact mem_iUnion.mpr ⟨i,t,ht,he⟩
    exact (Set.finite_iUnion (fun i => (hfinite i).image _)).subset hsub
  let ZN : Set N := Subtype.val ⁻¹' Z
  have hfZN : ZN.Finite := hfZ.preimage Subtype.val_injective.injOn
  let A := Σ i : Fin 4,{j : Fin (m i+1) // negative i j}
  let arc : A → C(Interval,{z : ℝ × ℝ // ‖z‖≤1}) := fun e => arcs e.1 e.2
  have hbounds (e : A) (t : Interval) :
      Icc.convexComb (mesh e.1 e.2.val.castSucc) (mesh e.1 e.2.val.succ) t ∈
        Icc (mesh e.1 e.2.val.castSucc) (mesh e.1 e.2.val.succ) :=
    ⟨Icc.le_convexComb ((hmono e.1).monotone (by change e.2.val.val≤e.2.val.val+1; omega)) t,
      Icc.convexComb_le ((hmono e.1).monotone (by change e.2.val.val≤e.2.val.val+1; omega)) t⟩
  let direction (e : A) (t : Interval) : N :=
    ⟨actualMaxNormSquareBoundaryFace e.1
      (Icc.convexComb (mesh e.1 e.2.val.castSucc) (mesh e.1 e.2.val.succ) t),
        hnegative e.1 e.2.val e.2.property _ (hbounds e t)⟩
  have hArcQ (e : A) (t : Interval) : arc e t=q (direction e t) := by
    apply Subtype.ext
    rw [hformula e.1 e.2 t,hq]
  have hforget : Function.Injective (fun e : A =>
      (⟨e.1,e.2.val⟩ : Σ i : Fin 4,Fin (m i+1))) := by
    rintro ⟨i,⟨j,hj⟩⟩ ⟨k,⟨l,hl⟩⟩ he
    cases he
    rfl
  have hcollision (e d : A) (t u : Interval) (he : arc e t=arc d u) :
      (e=d ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1)) := by
    have hd := congrArg Subtype.val (hinj ((hArcQ e t).symm.trans (he.trans (hArcQ d u))))
    rcases actual_four_face_mesh_direction_collision m mesh hmono
      ⟨e.1,e.2.val⟩ ⟨d.1,d.2.val⟩ t u hd with ⟨hed,htu⟩ | hend
    · exact Or.inl ⟨hforget hed,htu⟩
    · exact Or.inr hend
  let endpoints : Set {z : ℝ × ℝ // ‖z‖≤1} :=
    range (fun e : A => arc e 0) ∪ range (fun e : A => arc e 1)
  have hfend : endpoints.Finite := (Set.finite_range _).union (Set.finite_range _)
  let vertexSet := q '' ZN ∪ endpoints
  have hfvertices : vertexSet.Finite := (hfZN.image q).union hfend
  let vertices := hfvertices.toFinset
  have hends (e : A) : arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices := by
    constructor
    · exact hfvertices.mem_toFinset.mpr (Or.inr (Or.inl (mem_range_self e)))
    · exact hfvertices.mem_toFinset.mpr (Or.inr (Or.inr (mem_range_self e)))
  refine ⟨G,hboundary,vertices,A,inferInstance,arc,hends,hcollision,(fun e => hembed e.1 e.2),
    (fun e t ht0 ht1 => harcinterior e.1 e.2 t ht0 ht1),?_⟩
  intro u
  constructor
  · intro hu
    obtain ⟨z,hzu⟩ := (hcomplete u).mp hu
    obtain ⟨i,t,hface⟩ := actual_max_norm_square_boundary_cover z.val
    have ht : (f (actualMaxNormSquareBoundaryFace i t)).val.2/center.val.2≤0 :=
      hface ▸ z.property
    rcases (hcover i t).mp ht with hzt | ⟨j,hj,hjt⟩
    · left
      apply hfvertices.mem_toFinset.mpr
      left
      refine ⟨z,?_,hzu⟩
      change (f z.val).val.2=0
      have hh : (f (actualMaxNormSquareBoundaryFace i t)).val.2=0 := by
        simpa only [div_eq_zero_iff,hc,or_false] using hzt
      exact hface ▸ hh
    · right
      obtain ⟨s,hs⟩ := actual_mesh_interval_parameter_cover _ _ _ hjt
      refine ⟨⟨i,⟨j,hj⟩⟩,s,?_⟩
      apply Subtype.ext
      change (arcs i ⟨j,hj⟩ s).val=u.val
      rw [hformula i ⟨j,hj⟩ s,hs,hface,← hzu,hq]
  · rintro (hv | ⟨e,t,rfl⟩)
    · rcases hfvertices.mem_toFinset.mp hv with hv | hv
      · obtain ⟨z,hz,he⟩ := hv
        rw [← he]
        exact hzero z
      · rcases hv with hv | hv
        · obtain ⟨e,rfl⟩ := hv
          exact harczero e.1 e.2 0
        · obtain ⟨e,rfl⟩ := hv
          exact harczero e.1 e.2 1
    · exact harczero e.1 e.2 t
end CurveComplex.HyperellipticModel
