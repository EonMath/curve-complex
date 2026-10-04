import CurveComplexGenusTwo.Topology.FrontierCircle.GlobalBandScaffold
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import CurveComplexGenusTwo.Topology.FrontierCircle.BandUnionProbe

open Set Topology unitInterval
namespace CurveComplex

/-- Density of the planar interior transfers to density of the ambient image interior. -/
theorem embedded_planar_region_regular_closed
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : IsCompact K)
    (hreg : K ⊆ closure (interior K)) (f : K → S) (hf : IsEmbedding f) :
    closure (interior (Set.range f)) = Set.range f := by
  let U : Set K := {x | (x : EuclideanSpace ℝ (Fin 2)) ∈ interior K}
  have hUimage : (Subtype.val : K → EuclideanSpace ℝ (Fin 2)) '' U = interior K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, interior_subset hx⟩, hx, rfl⟩
  have hDense : Dense U := Subtype.dense_iff.mpr (hUimage.symm ▸ hreg)
  have hsub : Set.range f ⊆ closure (f '' U) := by
    have hh := image_closure_subset_closure_image hf.continuous (s := U)
    rwa [hDense.closure_eq, Set.image_univ] at hh
  have hsubset := embedded_planar_region_interior_probe K f hf
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact subset_antisymm
    (closure_minimal interior_subset (isCompact_range hf.continuous).isClosed)
    (hsub.trans (closure_mono hsubset))

/-- An embedded closed rectangular band has no thin component or isolated boundary. -/
theorem embedded_band_regular_closed
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (B : I × BandWidth → S) (hB : IsEmbedding B) :
    closure (interior (Set.range B)) = Set.range B := by
  let e : (ℝ × ℝ) ≃ₜ EuclideanSpace ℝ (Fin 2) := {
    toFun := fun p => Schoenflies.Plane.mk p.1 p.2
    invFun := fun q => (q 0, q 1)
    left_inv := by intro p; rfl
    right_inv := by intro q; ext i; fin_cases i <;> rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let R : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  let K := e '' R
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image e.continuous
  have hregR : R ⊆ closure (interior R) := by
    simp only [R, interior_prod_eq, interior_Icc, closure_prod_eq,
      closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num),
      closure_Ioo (show (-1 : ℝ) ≠ 1 by norm_num), subset_refl]
  have hregK : K ⊆ closure (interior K) := by
    rw [← e.image_interior, ← e.image_closure]
    exact Set.image_mono hregR
  let f : K → S := fun z => B
    (⟨(e.symm z).1, by obtain ⟨p, hp, he⟩ := z.property; simpa [← he] using hp.1⟩,
     ⟨(e.symm z).2, by obtain ⟨p, hp, he⟩ := z.property; simpa [← he] using hp.2⟩)
  have hfC : Continuous f := by fun_prop
  have hfI : Function.Injective f := by
    intro z w h
    have hh := hB.injective h
    apply Subtype.ext
    apply e.symm.injective
    exact Prod.ext (congrArg (fun p : I × BandWidth => (p.1 : ℝ)) hh)
      (congrArg (fun p : I × BandWidth => (p.2 : ℝ)) hh)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hf := (hfC.isClosedEmbedding hfI).isEmbedding
  have hRange : Set.range f = Set.range B := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact Set.mem_range_self _
    · rintro ⟨p, rfl⟩
      refine ⟨⟨e ((p.1 : ℝ), (p.2 : ℝ)), ?_⟩, ?_⟩
      · exact ⟨((p.1 : ℝ), (p.2 : ℝ)), ⟨p.1.property, p.2.property⟩, rfl⟩
      · rfl
  rw [← hRange]
  exact embedded_planar_region_regular_closed K hK hregK f hf

end CurveComplex

namespace CurveComplex

/-- The square in the shared witness is likewise the closure of its ambient interior. -/
theorem embedded_crossing_square_regular_closed
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (r : ℝ) (hr : 0 < r)
    (D : Metric.closedBall ((0, 0) : ℝ × ℝ) r → S) (hD : IsEmbedding D) :
    closure (interior (Set.range D)) = Set.range D := by
  let e : (ℝ × ℝ) ≃ₜ EuclideanSpace ℝ (Fin 2) := {
    toFun := fun p => Schoenflies.Plane.mk p.1 p.2
    invFun := fun q => (q 0, q 1)
    left_inv := by intro p; rfl
    right_inv := by intro q; ext i; fin_cases i <;> rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let R := Metric.closedBall ((0, 0) : ℝ × ℝ) r
  let K := e '' R
  have hK : IsCompact K := (isCompact_closedBall ((0, 0) : ℝ × ℝ) r).image e.continuous
  have hregR : R ⊆ closure (interior R) := by
    rw [interior_closedBall _ hr.ne', closure_ball _ hr.ne']
  have hregK : K ⊆ closure (interior K) := by
    rw [← e.image_interior, ← e.image_closure]
    exact Set.image_mono hregR
  let f : K → S := fun z => D ⟨e.symm z, by
    obtain ⟨p, hp, he⟩ := z.property
    simpa [← he, R] using hp⟩
  have hfC : Continuous f := by fun_prop
  have hfI : Function.Injective f := by
    intro z w h
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg Subtype.val (hD.injective h)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hf := (hfC.isClosedEmbedding hfI).isEmbedding
  have hRange : Set.range f = Set.range D := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact Set.mem_range_self _
    · rintro ⟨p, rfl⟩
      refine ⟨⟨e p, ⟨p, p.property, rfl⟩⟩, ?_⟩
      change D ⟨e.symm (e p), _⟩ = D p
      congr 1
  rw [← hRange]
  exact embedded_planar_region_regular_closed K hK hregK f hf

/-- Actual two-dimensional regularity of the square and both attached bands. -/
theorem compatibleOutsideBands_regular_closed
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
    closure (interior N) = N := by
  let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
  have hclosed : IsClosed N :=
    (compatibleOutsideBands_compact_connected_cover_probe D B).1.isClosed
  apply subset_antisymm (closure_minimal interior_subset hclosed)
  have hsub (A : Set S) (hA : closure (interior A) = A) (hAN : A ⊆ N) :
      A ⊆ closure (interior N) := by
    rw [← hA]
    exact closure_mono (interior_mono hAN)
  have hD := hsub _ (embedded_crossing_square_regular_closed D.radius D.radius_pos
    D.square D.square_embedded) (fun _ hx => Or.inl (Or.inl hx))
  have hB := hsub _ (embedded_band_regular_closed B.first B.first_embedded)
    (fun _ hx => Or.inl (Or.inr hx))
  have hC := hsub _ (embedded_band_regular_closed B.second B.second_embedded)
    (fun _ hx => Or.inr hx)
  exact Set.union_subset (Set.union_subset hD hB) hC

/-- Every frontier point of the actual band union is a limit of its inside. -/
theorem compatibleOutsideBands_frontier_approached_from_inside
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
    frontier N ⊆ closure (interior N) := by
  dsimp only
  rw [compatibleOutsideBands_regular_closed D B]
  exact (compatibleOutsideBands_compact_connected_cover_probe D B).1.isClosed.frontier_subset

#print axioms embedded_planar_region_regular_closed
#print axioms embedded_band_regular_closed
#print axioms embedded_crossing_square_regular_closed
#print axioms compatibleOutsideBands_regular_closed
#print axioms compatibleOutsideBands_frontier_approached_from_inside
end CurveComplex
