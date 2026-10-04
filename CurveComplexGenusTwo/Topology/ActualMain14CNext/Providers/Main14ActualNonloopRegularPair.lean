import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualNonloopWholeStraightening
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14RegularSegmentSourceReadOnly

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open ClassificationSchoenflies (standardArcCore exists_regularArcDisk_segment_avoid_finite)
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- Produce a genuine two-mark disk/core pair for the ORIGINAL entire arc.
The central half-diameter is mapped exactly onto the arc, not merely into a
neighborhood. Neither disk, pair, straightening nor marked isotopy is input. -/
theorem actual_nonloop_regular_disk_core_pair (M : HyperellipticModel E S)
    (a : NonLoopArc M) :
    ∃ d : C(Metric.closedBall (0 : Plane) 1,S), IsEmbedding d ∧
      d '' standardArcCore = a.image ∧ a.image ⊆ interior (range d) ∧
      range d ∩ (M.cover.branch : Set S) = {a.val.map 0,a.val.map 1} := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨p,hp,F,hFs,hFt,haF,hFa⟩ := M.actual_nonloop_whole_arc_straightening a
  let f : Plane → S := F.symm
  have hf : IsOpenEmbedding f := F.symm.isOpenEmbedding hFt
  have hleft (x : S) (hx : x ∈ F.source) : f (F x) = x := F.left_inv hx
  have hright (z : Plane) : F (f z) = z := F.right_inv (hFt ▸ mem_univ z)
  have hsource (z : Plane) : f z ∈ F.source := F.map_target (hFt ▸ mem_univ z)
  have hback : f '' sideTop = a.image := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨y,hy,he⟩ := hFa.symm ▸ hz
      rw [← he,hleft y (haF hy)]
      exact hy
    · intro hx
      exact ⟨F x,hFa ▸ Set.mem_image_of_mem F hx,hleft x (haF hx)⟩
  let ends : Set S := {a.val.map 0,a.val.map 1}
  let B : Finset S := M.cover.branch.filter (fun x => x ∈ F.source ∧ x ∉ ends)
  let Z : Finset Plane := B.image F
  have hZ : Disjoint sideTop (Z : Set Plane) := by
    apply Set.disjoint_left.mpr
    intro z hz hzZ
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hzZ
    obtain ⟨hxB,hxs,hxe⟩ := Finset.mem_filter.mp hx
    have hxarc : x ∈ a.image := by rw [← hback]; exact ⟨F x,hz,hleft x hxs⟩
    have hxends : x ∈ ends := by
      change x ∈ ({a.val.map 0,a.val.map 1}:Set S)
      have hh : x ∈ a.val.image ∩ (M.cover.branch : Set S) := ⟨hxarc,hxB⟩
      have hh' := a.image_inter_branch ▸ hh
      convert hh' using 1
    exact hxe hxends
  have hcorners : cornerNE ≠ cornerNW := by
    intro he
    have h := congrArg (fun z : Plane => z 0) he
    norm_num [cornerNE,cornerNW] at h
  obtain ⟨N,hinside,havoid⟩ := exists_regularArcDisk_segment_avoid_finite hcorners Z hZ
  let j : Metric.closedBall (0 : Plane) 1 → Plane := fun z => (N.pair z).val
  have hj : IsEmbedding j := IsEmbedding.subtypeVal.comp N.pair.isEmbedding
  let d : C(Metric.closedBall (0 : Plane) 1,S) := ⟨f ∘ j,hf.continuous.comp hj.continuous⟩
  have hjrange : range j = N.carrier := by
    ext x; constructor
    · rintro ⟨z,rfl⟩; exact (N.pair z).property
    · intro hx
      exact ⟨N.pair.symm ⟨x,hx⟩,congrArg Subtype.val (N.pair.apply_symm_apply ⟨x,hx⟩)⟩
  have hdrange : range d = f '' N.carrier := by
    change range (f ∘ j) = _
    rw [range_comp,hjrange]
  refine ⟨d,hf.isEmbedding.comp hj,?_,?_,?_⟩
  · change (f ∘ j) '' standardArcCore = _
    rw [Set.image_comp,N.core_image]
    exact hback
  · rw [hdrange,← hback]
    exact (Set.image_mono hinside).trans (hf.isOpenMap.image_interior_subset N.carrier)
  · rw [hdrange]
    apply Set.Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hxB⟩
      by_contra hxends
      have hzZ : z ∈ Z := by
        have hxmem : f z ∈ B := Finset.mem_filter.mpr ⟨hxB,hsource z,hxends⟩
        exact Finset.mem_image.mpr ⟨f z,hxmem,hright z⟩
      exact Set.disjoint_left.mp havoid hz hzZ
    · intro x hx
      have hxarc : x ∈ a.image := by
        have hxpair : x ∈ a.val.image ∩ (M.cover.branch : Set S) := by
          rw [a.image_inter_branch]; convert hx using 1
        exact hxpair.1
      have hxB : x ∈ (M.cover.branch : Set S) := by
        have hxpair : x ∈ a.val.image ∩ (M.cover.branch : Set S) := by
          rw [a.image_inter_branch]; convert hx using 1
        exact hxpair.2
      obtain ⟨z,hz,he⟩ := hback.symm ▸ hxarc
      exact ⟨⟨z,interior_subset (hinside hz),he⟩,hxB⟩
end CurveComplex.HyperellipticModel
