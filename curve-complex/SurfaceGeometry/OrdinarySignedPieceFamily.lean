import RegionalWeightedMovieDefinitions
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.GapMatchingTools
import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.CornerGeometryTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.DiskExteriorHalfTools

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open CurveComplex.BranchedDoubleCover
open scoped BigOperators
set_option autoImplicit false
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

structure OrdinarySignedPieceFamily
    {S ι : Type} [TopologicalSpace S] (F : Set S)
    (f : Option ι → C(Interval,↥F)) (v w : ι)
    (d : PairedBigonDisk F {y | y.val ∈ frontier F} (f (some v)) (f (some w)))
    (A B : Interval) (Edisk Eguide : OpenPartialHomeomorph S Plane) where
  l : Interval
  r : Interval
  cuts : A < l ∧ l < min d.aStart d.aFinish ∧
    min d.aStart d.aFinish < max d.aStart d.aFinish ∧
    max d.aStart d.aFinish < r ∧ r < B
  old_in_disk : f (some v) '' Icc l r ⊆ {y | y.val ∈ Edisk.source}
  attachment_clear : ∀ i : Option ι, i ≠ some v →
    Disjoint ((f (some v) '' Icc l r) \ range d.first) (range (f i))
  m : ℕ
  label : Fin m ≃ ↥((range d.second \ ({d.first 0,d.first 1} : Set ↥F)) ∩
    {p | ∃ i : Option ι, i ≠ some w ∧ p ∈ range (f i)})
  label_order : ∀ k j : Fin m, k < j →
    Eguide (label k).val.val 0 < Eguide (label j).val.val 0
  corners : {f (some w) (min d.bStart d.bFinish),
    f (some w) (max d.bStart d.bFinish)} = ({d.first 0,d.first 1} : Set ↥F)
  xL : ↥F
  xR : ↥F
  orientation : (xL = f (some v) l ∧ xR = f (some v) r) ∨
    (xL = f (some v) r ∧ xR = f (some v) l)
  ε : ℝ
  epsilon_pos : 0 < ε
  L : Fin (m+2) → C(Interval,↥F)
  R : Fin (m+2) → C(Interval,↥F)
  piece : Fin (m+2) → Interval → C(Interval,↥F)
  piece_embedded : ∀ τ : Interval, 0 < τ.val → τ.val < ε →
    ∀ k, IsEmbedding (piece k τ)
  piece_in_guide : ∀ τ : Interval, 0 < τ.val → τ.val < ε →
    ∀ k, range (piece k τ) ⊆ {y | y.val ∈ Eguide.source}
  piece_endpoints : ∀ τ : Interval, 0 < τ.val → τ.val < ε →
    ∀ k, piece k τ 0 = L k τ ∧ piece k τ 1 = R k τ
  attachments : ∀ τ : Interval, 0 < τ.val → τ.val < ε →
    L ⟨0,by omega⟩ τ = xL ∧ R ⟨m+1,by omega⟩ τ = xR
  guide_clear : ∀ τ : Interval, 0 < τ.val → τ.val < ε →
    ∀ k, Disjoint (range (piece k τ)) (range (f (some w)))
  selected_meet : ∀ τ : Interval, 0 < τ.val → τ.val < ε →
    range (piece ⟨0,by omega⟩ τ) ∩ range (f (some v)) = {xL} ∧
    range (piece ⟨m+1,by omega⟩ τ) ∩ range (f (some v)) = {xR} ∧
    ∀ k : Fin m, Disjoint (range (piece ⟨k.val+1,by omega⟩ τ)) (range (f (some v)))
  site : Fin (m+2) → ↥F
  site_left : site ⟨0,by omega⟩ = f (some w) (min d.bStart d.bFinish)
  site_right : site ⟨m+1,by omega⟩ = f (some w) (max d.bStart d.bFinish)
  site_event : ∀ k : Fin m, site ⟨k.val+1,by omega⟩ = (label k).val
  piece_contacts_finite : ∀ τ : Interval, 0 < τ.val → τ.val < ε →
    ∀ k i, i ≠ some v → (range (piece k τ) ∩ range (f i)).Finite
  piece_contacts_bound : ∀ τ : Interval, 0 < τ.val → τ.val < ε →
    ∀ k i, i ≠ some v → i ≠ some w →
      (range (piece k τ) ∩ range (f i)).ncard ≤ if site k ∈ range (f i) then 1 else 0
  internal_source : ∀ k : Fin (m+1), ∀ τ : Interval,
    (R ⟨k.val,by omega⟩ τ).val ∈ Eguide.source ∧
    (L ⟨k.val+1,by omega⟩ τ).val ∈ Eguide.source
  internal_clear : ∀ τ : Interval, 0 < τ.val → τ.val < ε →
    ∀ k : Fin (m+1), ∀ i : Option ι,
      R ⟨k.val,by omega⟩ τ ∉ range (f i) ∧ L ⟨k.val+1,by omega⟩ τ ∉ range (f i)
  gapA : Fin (m+1) → ℝ
  gapL : Fin (m+1) → ℝ
  gapR : Fin (m+1) → ℝ
  gapB : Fin (m+1) → ℝ
  gap_order : ∀ k, gapA k < gapL k ∧ gapL k < gapR k ∧ gapR k < gapB k
  gap_zero : ∀ k : Fin (m+1),
    Eguide (R ⟨k.val,by omega⟩ 0).val = Plane.mk (gapL k) 0 ∧
    Eguide (L ⟨k.val+1,by omega⟩ 0).val = Plane.mk (gapR k) 0
  gap_axis : ∀ k, ∀ x ∈ Icc (gapA k) (gapB k),
    Plane.mk x 0 ∈ Eguide.target ∧
    ∀ i : Option ι, i ≠ some w →
      Eguide.symm (Plane.mk x 0) ∉ Subtype.val '' range (f i)
  σ : ℝ
  sign_unit : σ = -1 ∨ σ = 1
  internal_sign : ∀ τ : Interval, 0 < τ.val → τ.val < ε →
    ∀ k : Fin (m+1),
      0 < σ * Eguide (R ⟨k.val,by omega⟩ τ).val 1 ∧
      0 < σ * Eguide (L ⟨k.val+1,by omega⟩ τ).val 1
  small : Interval
  small_pos : 0 < small.val
  small_bound : small.val < ε
  rescaledL : Fin (m+1) → C(Interval,↥{y : ↥F | y.val ∈ Eguide.source})
  rescaledR : Fin (m+1) → C(Interval,↥{y : ↥F | y.val ∈ Eguide.source})
  rescale_eq : ∀ k : Fin (m+1), ∀ τ : Interval,
    (rescaledL k τ).val = R ⟨k.val,by omega⟩ (intervalAffine 0 small τ) ∧
    (rescaledR k τ).val = L ⟨k.val+1,by omega⟩ (intervalAffine 0 small τ)

