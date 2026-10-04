import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConeCoherentFiniteFaceArcs
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMeshIntervalParameterCover
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual four-side boundary with finite scalar contacts produces a finite
embedded-arc family covering EVERY contact of the constructed square filling.
Finite vertices and arcs are outputs, not a presumed contact certificate. -/
theorem actual_square_cone_finite_whole_contact_family
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (f : C({z : ℝ × ℝ // ‖z‖=1},V)) (center : V) (hc : center.val.2≠0)
    (hfinite : ∀ i : Fin 4,
      {t : Interval | (f (actualMaxNormSquareBoundaryFace i t)).val.2=0}.Finite) :
    ∃ G : C({z : ℝ × ℝ // ‖z‖≤1},V),
      (∀ z : {z : ℝ × ℝ // ‖z‖=1},G ⟨z.val,z.property.le⟩=f z) ∧
    ∃ vertices : Finset {z : ℝ × ℝ // ‖z‖≤1},
    ∃ A : Type,∃ _hA : Finite A,∃ arc : A → C(Interval,{z : ℝ × ℝ // ‖z‖≤1}),
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
  let vertices := (hfZN.image q).toFinset
  let A := Σ i : Fin 4,{j : Fin (m i+1) // negative i j}
  let arc : A → C(Interval,{z : ℝ × ℝ // ‖z‖≤1}) := fun e => arcs e.1 e.2
  refine ⟨G,hboundary,vertices,A,inferInstance,arc,(fun e => hembed e.1 e.2),
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
      apply (hfZN.image q).mem_toFinset.mpr
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
    · obtain ⟨z,hz,he⟩ := (hfZN.image q).mem_toFinset.mp hv
      rw [← he]
      exact hzero z
    · exact harczero e.1 e.2 t
end CurveComplex.HyperellipticModel
