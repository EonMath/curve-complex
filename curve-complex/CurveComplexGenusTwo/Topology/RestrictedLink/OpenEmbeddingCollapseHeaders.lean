import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import Mathlib.Topology.Compactification.OnePoint.Basic
namespace CurveComplex.HyperellipticModel
open Set
theorem open_embedding_collapse_continuous {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Topology.IsOpenEmbedding f) :
    ∃ g : Y → OnePoint X, Continuous g ∧
      (∀ x, g (f x) = (x : OnePoint X)) ∧
      (∀ y, y ∉ range f → g y = OnePoint.infty) := by
  classical
  let H := hf.isEmbedding.toHomeomorph
  let g : Y → OnePoint X := fun y => if h : y ∈ range f then
    ((H.symm ⟨y,h⟩ : X) : OnePoint X) else OnePoint.infty
  have hg (x : X) : g (f x) = (x : OnePoint X) := by
    simp [g,H]
  have hout (y : Y) (hy : y ∉ range f) : g y = OnePoint.infty := by
    dsimp only [g]
    rw [dif_neg hy]
  refine ⟨g,?_,hg,hout⟩
  apply continuous_def.mpr
  intro A hA
  by_cases hInf : OnePoint.infty ∈ A
  · let K : Set X := ((↑) : X → OnePoint X) ⁻¹' Aᶜ
    have hK : IsClosed K ∧ IsCompact K := by
      exact (OnePoint.isOpen_iff_of_mem hInf).mp hA
    have he : g ⁻¹' A = (f '' K)ᶜ := by
      ext y
      by_cases hy : y ∈ range f
      · obtain ⟨x,rfl⟩ := hy
        rw [mem_preimage,hg,mem_compl_iff,hf.injective.mem_set_image]
        simp [K]
      · rw [mem_preimage,hout y hy]
        constructor
        · intro _ hmem; exact hy (image_subset_range f K hmem)
        · intro _; exact hInf
    rw [he]
    exact (hK.2.image hf.continuous).isClosed.isOpen_compl
  · have ho : IsOpen (((↑) : X → OnePoint X) ⁻¹' A) :=
      (OnePoint.isOpen_iff_of_notMem hInf).mp hA
    have he : g ⁻¹' A = f '' (((↑) : X → OnePoint X) ⁻¹' A) := by
      ext y
      by_cases hy : y ∈ range f
      · obtain ⟨x,rfl⟩ := hy
        rw [mem_preimage,hg,hf.injective.mem_set_image]
        rfl
      · rw [mem_preimage,hout y hy]
        constructor
        · exact fun h => False.elim (hInf h)
        · exact fun h => False.elim (hy (image_subset_range f _ h))
    rw [he]
    exact hf.isOpenMap _ ho
end CurveComplex.HyperellipticModel
