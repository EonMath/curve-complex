import CurveComplexGenusTwo.Topology.CapBandGeometry.BandCover
import Mathlib.Analysis.Convex.Contractible

open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry

/-- Each literal band window is homeomorphic to its parameter interval times
its full closed transverse interval, including the lateral boundary. -/
noncomputable def bandSliceHomeomorph
    {S : Type*} [TopologicalSpace S]
    (F : I × BandWidth → S) (hF : IsEmbedding F)
    (J : Set ℝ) (hJ : J ⊆ Icc (0 : ℝ) 1) :
    (J × BandWidth) ≃ₜ bandSlice F J := by
  let inc : J × BandWidth → I × BandWidth :=
    Prod.map (Set.inclusion hJ) id
  have hinc : IsEmbedding inc := (IsEmbedding.inclusion hJ).prodMap IsEmbedding.id
  let g : J × BandWidth → S := F ∘ inc
  have hg : IsEmbedding g := hF.comp hinc
  have heq : Set.range g = bandSlice F J := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨inc p, p.1.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(⟨p.1, hp⟩, p.2), ?_⟩
      rfl
  exact hg.toHomeomorph.trans (Homeomorph.setCongr heq)

/-- Every nonempty convex band window is contractible; no ambient collar or
homology assertion is assumed. -/
theorem bandSlice_contractible
    {S : Type*} [TopologicalSpace S]
    (F : I × BandWidth → S) (hF : IsEmbedding F)
    (J : Set ℝ) (hJ : J ⊆ Icc (0 : ℝ) 1)
    (hconv : Convex ℝ J) (hne : J.Nonempty) :
    ContractibleSpace (bandSlice F J) := by
  letI : ContractibleSpace J := hconv.contractibleSpace hne
  letI : ContractibleSpace BandWidth :=
    (convex_Icc (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  exact (bandSliceHomeomorph F hF J hJ).symm.contractibleSpace

theorem bandSlice_disjoint_of_disjoint_parameters
    {S : Type*} (F : I × BandWidth → S) (hF : Function.Injective F)
    (J K : Set ℝ) (hJK : Disjoint J K) :
    Disjoint (bandSlice F J) (bandSlice F K) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, rfl⟩ hK
  exact Set.disjoint_left.mp hJK hp ((bandSlice_mem_iff F hF K p).mp hK)

theorem first_second_slice_disjoint {S : Type} [TopologicalSpace S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D)
    (J K : Set ℝ) : Disjoint (bandSlice B.first J) (bandSlice B.second K) :=
  B.bands_disjoint.mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)

/-- These four explicit windows are the four overlap pieces of the literal cover. -/
def overlapWindow (i : Fin 4) : Set ℝ :=
  if i.val % 2 = 0 then Ioo (1/4 : ℝ) (1/3) else Ioo (2/3 : ℝ) (3/4)

def overlapPiece {S : Type} [TopologicalSpace S] {a b : Curve S}
    {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D) (i : Fin 4) : Set S :=
  if i.val < 2 then bandSlice B.first (overlapWindow i)
    else bandSlice B.second (overlapWindow i)

theorem overlapWindow_subset (i : Fin 4) : overlapWindow i ⊆ Icc (0 : ℝ) 1 := by
  intro t ht
  simp only [overlapWindow] at ht
  split_ifs at ht <;> exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem overlapWindow_convex (i : Fin 4) : Convex ℝ (overlapWindow i) := by
  unfold overlapWindow
  split_ifs <;> exact convex_Ioo _ _

theorem overlapWindow_nonempty (i : Fin 4) : (overlapWindow i).Nonempty := by
  unfold overlapWindow
  split_ifs
  · exact ⟨7/24, by norm_num⟩
  · exact ⟨17/24, by norm_num⟩

theorem overlapPiece_contractible {S : Type} [TopologicalSpace S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D)
    (i : Fin 4) : ContractibleSpace (overlapPiece B i) := by
  by_cases h : i.val < 2
  · rw [show overlapPiece B i = bandSlice B.first (overlapWindow i) from by simp [overlapPiece, h]]
    exact bandSlice_contractible B.first B.first_embedded _ (overlapWindow_subset i)
      (overlapWindow_convex i) (overlapWindow_nonempty i)
  · rw [show overlapPiece B i = bandSlice B.second (overlapWindow i) from by simp [overlapPiece, h]]
    exact bandSlice_contractible B.second B.second_embedded _ (overlapWindow_subset i)
      (overlapWindow_convex i) (overlapWindow_nonempty i)

theorem overlapPiece_pairwise_disjoint {S : Type} [TopologicalSpace S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D) :
    Pairwise (fun i j : Fin 4 => Disjoint (overlapPiece B i) (overlapPiece B j)) := by
  have hinterval : Disjoint (Ioo (1/4 : ℝ) (1/3)) (Ioo (2/3 : ℝ) (3/4)) := by
    apply Set.disjoint_left.mpr
    intro t ht hu
    linarith [ht.2, hu.1]
  have hfirst := bandSlice_disjoint_of_disjoint_parameters B.first
    B.first_embedded.injective _ _ hinterval
  have hsecond := bandSlice_disjoint_of_disjoint_parameters B.second
    B.second_embedded.injective _ _ hinterval
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [overlapPiece, overlapWindow, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Nat.reduceMod, Nat.reduceLT, ↓reduceIte] <;>
    first | exact False.elim (hij rfl) | exact hfirst | exact hfirst.symm |
      exact hsecond | exact hsecond.symm |
      exact first_second_slice_disjoint B _ _ |
      exact (first_second_slice_disjoint B _ _).symm

/-- Exact finite cover of the overlap by the four constructed, disjoint,
contractible pieces. -/
theorem overlapPiece_union {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    (⋃ i : Fin 4, overlapPiece B i) = squareCollars D B ∩ middleBands B := by
  rw [squareCollars_middleBands_intersection D B]
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (Or.inl (Or.inl hi))
    · exact Or.inl (Or.inl (Or.inr hi))
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  · rintro (((h | h) | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩

/-- The middle-band set has two disjoint contractible literal rectangular pieces. -/
theorem middleBands_components {S : Type} [TopologicalSpace S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D) :
    Disjoint (bandSlice B.first (Ioo (1/4 : ℝ) (3/4)))
      (bandSlice B.second (Ioo (1/4 : ℝ) (3/4))) ∧
    ContractibleSpace (bandSlice B.first (Ioo (1/4 : ℝ) (3/4))) ∧
    ContractibleSpace (bandSlice B.second (Ioo (1/4 : ℝ) (3/4))) := by
  have hJ : Ioo (1/4 : ℝ) (3/4) ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hne : (Ioo (1/4 : ℝ) (3/4)).Nonempty := ⟨1/2, by norm_num⟩
  exact ⟨first_second_slice_disjoint B _ _,
    bandSlice_contractible B.first B.first_embedded _ hJ (convex_Ioo _ _) hne,
    bandSlice_contractible B.second B.second_embedded _ hJ (convex_Ioo _ _) hne⟩

#print axioms bandSliceHomeomorph
#print axioms overlapPiece_contractible
#print axioms overlapPiece_pairwise_disjoint
#print axioms overlapPiece_union
#print axioms middleBands_components
end CurveComplex.CapBandGeometry
