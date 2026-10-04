import CurveComplexGenusTwo.Topology.ThetaRetention.SurfaceLocalSides
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

namespace CurveComplex
open Set Topology

/-- Pull actual local tracks back through a chart. The deleted-set equality is
needed only on the open neighborhood, so distant parts of the surface arc do
not enter the planar comparison. -/
noncomputable def SurfaceLocalSides.pullbackChart
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {D P : Set X} {D' P' : Set Y}
    (e : OpenPartialHomeomorph X Y) (C : SurfaceLocalSides D' P')
    (ht : C.nbhd ⊆ e.target) (hD : e.symm '' C.nbhd ⊆ D)
    (hP : ∀ z ∈ C.nbhd, e.symm z ∈ P ↔ z ∈ P') :
    SurfaceLocalSides D P where
  nbhd := e.symm '' C.nbhd
  left := e.symm '' C.left
  right := e.symm '' C.right
  isOpen_nbhd := e.symm.isOpen_image_of_subset_source C.isOpen_nbhd ht
  nbhd_subset := hD
  nbhd_diff := by
    ext x
    constructor
    · rintro ⟨⟨z,hz,rfl⟩,hn⟩
      have hzP : z ∉ P' := by intro hp; exact hn ((hP z hz).mpr hp)
      have htracks : z ∈ C.left ∪ C.right := C.nbhd_diff ▸ ⟨hz,hzP⟩
      exact htracks.elim (fun h => Or.inl ⟨z,h,rfl⟩) (fun h => Or.inr ⟨z,h,rfl⟩)
    · rintro (⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩)
      · have hzN : z ∈ C.nbhd \ P' := by rw [C.nbhd_diff]; exact Or.inl hz
        exact ⟨⟨z,hzN.1,rfl⟩,fun h => hzN.2 ((hP z hzN.1).mp h)⟩
      · have hzN : z ∈ C.nbhd \ P' := by rw [C.nbhd_diff]; exact Or.inr hz
        exact ⟨⟨z,hzN.1,rfl⟩,fun h => hzN.2 ((hP z hzN.1).mp h)⟩
  connected_left := C.connected_left.image _ (e.continuousOn_symm.mono (by
    intro z hz
    apply ht
    have hn : z ∈ C.nbhd \ P' := by rw [C.nbhd_diff]; exact Or.inl hz
    exact hn.1))
  connected_right := C.connected_right.image _ (e.continuousOn_symm.mono (by
    intro z hz
    apply ht
    have hn : z ∈ C.nbhd \ P' := by rw [C.nbhd_diff]; exact Or.inr hz
    exact hn.1))
  limit_left := by
    rintro x ⟨⟨z,hz,rfl⟩,hp⟩
    exact (e.continuousAt_symm (ht hz)).continuousWithinAt.mem_closure_image
      (C.limit_left ⟨hz,(hP z hz).mp hp⟩)
  limit_right := by
    rintro x ⟨⟨z,hz,rfl⟩,hp⟩
    exact (e.continuousAt_symm (ht hz)).continuousWithinAt.mem_closure_image
      (C.limit_right ⟨hz,(hP z hz).mp hp⟩)

end CurveComplex
#print axioms CurveComplex.SurfaceLocalSides.pullbackChart
