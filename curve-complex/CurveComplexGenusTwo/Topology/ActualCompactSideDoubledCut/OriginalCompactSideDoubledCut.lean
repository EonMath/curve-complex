import CurveComplexGenusTwo.Topology.ActualCompactSideDoubledCut.CutIntrinsicInterior
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip
import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.OriginalRegionVanishing

open CurveComplex Set Topology
open scoped Manifold ContDiff

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private abbrev UnitDisk := Metric.closedBall (0 : Plane) 1
private abbrev DiskCore : Set UnitDisk :=
  {z | z.val ∈ Metric.ball (0 : Plane) 1}
private abbrev ClosedAnnulus : Set Plane :=
  Metric.closedBall (0 : Plane) 2 \ Metric.ball (0 : Plane) 1
private abbrev AnnulusCore : Set ClosedAnnulus :=
  {z | z.val ∈ Metric.ball (0 : Plane) 2 \ Metric.closedBall (0 : Plane) 1}
private abbrev InnerCircle : Set ClosedAnnulus :=
  {z | z.val ∈ Metric.sphere (0 : Plane) 1}

/-- A compact side-doubled cut of the original exterior along the actual arcs.
Only its open core is identified with the open exterior complement. The two
interior lifts of each cut arc remain distinct in the compact carrier. -/
structure CompactSideDoubledCut
    (S : Type) [TopologicalSpace S] (Q B D : Set S)
    {n : ℕ} (a : Fin n → C(Interval, ↥Q)) where
  Carrier : Type
  topology : TopologicalSpace Carrier
  compact : @CompactSpace Carrier topology
  hausdorff : @T2Space Carrier topology
  charts : letI : TopologicalSpace Carrier := topology
    ChartedSpace (EuclideanHalfSpace 2) Carrier
  manifold :
    letI : TopologicalSpace Carrier := topology
    letI : ChartedSpace (EuclideanHalfSpace 2) Carrier := charts
    IsManifold (𝓡∂ 2) 0 Carrier
  core : Set Carrier
  core_open : @IsOpen Carrier topology core
  core_dense : @closure Carrier topology core = Set.univ
  core_eq_manifold_interior :
    letI : TopologicalSpace Carrier := topology
    letI : ChartedSpace (EuclideanHalfSpace 2) Carrier := charts
    core = ModelWithCorners.interior (I := 𝓡∂ 2) Carrier
  projection : @ContinuousMap Carrier (↥Q) topology inferInstance
  coreEquiv : @Homeomorph (↥core) (↥D) _ _
  core_agrees : ∀ z : core, (projection z.val).val = (coreEquiv z).val
  baseBoundary : Set Carrier
  side : Fin n → Bool → @ContinuousMap Interval Carrier inferInstance topology
  side_agrees : ∀ i b t, projection (side i b t) = a i t
  boundary_exhaustion :
    coreᶜ = baseBoundary ∪ ⋃ i, Set.range (side i false) ∪ Set.range (side i true)
  base_boundary_image :
    Set.range (fun z : ↥baseBoundary => (projection z.val).val) = B
  side_boundary : ∀ i b t, side i b t ∈ coreᶜ
  side_distinct : ∀ i t,
    side i false t ≠ side i true t
  side_endpoint_incidence : ∀ i b,
    side i b 0 ∈ baseBoundary ∧ side i b 1 ∈ baseBoundary
  arc_interior_fiber : ∀ i t, t ∈ Set.Ioo (0 : Interval) 1 →
    {z : Carrier | projection z = a i t} =
      {side i false t, side i true t}
  arc_start_fiber : ∀ i,
    {z : Carrier | projection z = a i 0} =
      {side i false 0, side i true 0}
  arc_end_fiber : ∀ i,
    {z : Carrier | projection z = a i 1} =
      {side i false 1, side i true 1}
  base_regular_fiber : ∀ y : ↥Q, y.val ∈ B →
    (∀ i, y ≠ a i 0 ∧ y ≠ a i 1) →
    ∃! z : Carrier, z ∈ baseBoundary ∧ projection z = y

/-- The side-doubled cut is constructed from the original embedded arc family;
it is not supplied as an additional hypothesis to the count theorem. -/
theorem original_exterior_has_compact_side_doubled_cut
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target) :
    let Q : Set S := exterior S x R
    let B : Set S := originalBoundary S x R
    ∀ (n : ℕ) (a : Fin n → C(Interval, ↥Q)),
      (∀ i, Topology.IsEmbedding (a i)) →
      (∀ i, (a i 0).val ∈ B ∧ (a i 1).val ∈ B) →
      (∀ i t, t ∈ Set.Ioo (0 : Interval) 1 → (a i t).val ∉ B) →
      (∀ i j, i ≠ j → Disjoint (Set.range (a i)) (Set.range (a j))) →
      Nonempty (CompactSideDoubledCut S Q B
        (OriginalBoundaryArc.openDisk S x R ∪ B ∪ arcTrace a)ᶜ a) := by
  intro Q B n a hemb hend hinterior hpairwise
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  obtain ⟨p, E, hp, hE, hdisjoint⟩ :=
    OriginalBoundaryArc.source_finite_disjoint_proper_arc_strips
      S g hg hS x R hR htarget n a hemb hend hinterior hpairwise
  have hOpen : IsOpen (OriginalBoundaryArc.openDisk S x R) :=
    (chartAt Plane x).isOpen_image_symm_of_subset_target Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans htarget)
  have hQclosed : IsClosed Q := hOpen.isClosed_compl
  letI : CompactSpace (↥Q) := isCompact_iff_compactSpace.mp hQclosed.isCompact
  have hopen : ∀ i, IsOpen (bandInterior E i) := fun i => (hE i).2.2.2.2
  have hembE : ∀ i, Topology.IsEmbedding (E i) := fun i => (hE i).1
  have hcenter : ∀ i t, E i (t,⟨0,by norm_num⟩) = a i t :=
    fun i => (hE i).2.1
  let BQ : Set (↥Q) := {y | y.val ∈ B}
  have hBclosed : IsClosed B := by
    exact ((isCompact_sphere ((chartAt Plane x) x) R).image_of_continuousOn
      ((chartAt Plane x).continuousOn_symm.mono
        (Metric.sphere_subset_closedBall.trans htarget))).isClosed
  have hBQclosed : IsClosed BQ := hBclosed.preimage continuous_subtype_val
  have hBsubset : B ⊆ Q := by
    rintro y ⟨z,hz,rfl⟩
    exact source_chart_symm_exterior S x R htarget z
      (htarget (Metric.sphere_subset_closedBall hz))
      (by simpa only [Metric.mem_sphere, dist_eq_norm] using hz.ge)
  letI : CompactSpace (CutQuotient E) := cutQuotient_compact E hopen
  letI : T2Space (CutQuotient E) := cutQuotient_hausdorff E hopen hembE hdisjoint
  obtain ⟨charts,hmanifold⟩ := cutQuotient_has_halfSpace_atlas E hopen hembE hdisjoint
    (sourceExterior_has_halfSpace_charts S x R hR htarget)
  letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
  let D : Set S := (OriginalBoundaryArc.openDisk S x R ∪ B ∪ arcTrace a)ᶜ
  have hcentersVal (y : ↥Q) : y ∈ arcCenters E ↔ y.val ∈ arcTrace a := by
    constructor
    · intro hy
      obtain ⟨i,t,ht⟩ := Set.mem_iUnion.mp hy
      change E i (t,⟨0,by norm_num⟩) = y at ht
      exact Set.mem_iUnion.mpr ⟨i,t,by simpa only [hcenter] using congrArg Subtype.val ht⟩
    · intro hy
      obtain ⟨i,t,ht⟩ := Set.mem_iUnion.mp hy
      refine Set.mem_iUnion.mpr ⟨i,t,?_⟩
      change E i (t,⟨0,by norm_num⟩) = y
      rw [hcenter]
      exact Subtype.ext ht
  let f : ↥(BQ ∪ arcCenters E)ᶜ → ↥D := fun z => ⟨z.val.val,by
    intro hz
    rcases hz with (hDisk | hB) | hA
    · exact z.val.property hDisk
    · exact z.property (Or.inl hB)
    · exact z.property (Or.inr ((hcentersVal z.val).mpr hA))⟩
  let inv : ↥D → ↥(BQ ∪ arcCenters E)ᶜ := fun z =>
    ⟨⟨z.val,fun hDisk => z.property (Or.inl (Or.inl hDisk))⟩,by
      rintro (hB | hA)
      · exact z.property (Or.inl (Or.inr hB))
      · exact z.property (Or.inr ((hcentersVal _).mp hA))⟩
  let bridge : ↥(BQ ∪ arcCenters E)ᶜ ≃ₜ ↥D := {
    toFun := f
    invFun := inv
    left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ => Subtype.ext rfl
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  have hBcenters : ∀ i t, E i (t,⟨0,by norm_num⟩) ∈ BQ → t = 0 ∨ t = 1 := by
    intro i t ht
    by_contra hn
    have h0 : t ≠ 0 := fun h => hn (Or.inl h)
    have h1 : t ≠ 1 := fun h => hn (Or.inr h)
    have hti : t ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne (unitInterval.nonneg t) h0.symm,
        lt_of_le_of_ne (unitInterval.le_one t) h1⟩
    have hB : (a i t).val ∈ B := by
      change (E i (t,⟨0,by norm_num⟩)).val ∈ B at ht
      rw [hcenter] at ht
      exact ht
    exact hinterior i t hti hB
  refine ⟨{
    Carrier := CutQuotient E
    topology := inferInstance
    compact := inferInstance
    hausdorff := inferInstance
    charts := charts
    manifold := hmanifold
    core := cutInteriorCore E BQ
    core_open := cutInteriorCore_isOpen E BQ hBQclosed
    core_dense := sourceCut_core_dense S x R hR htarget E hopen hembE hdisjoint charts
    core_eq_manifold_interior :=
      sourceCut_core_eq_intrinsicInterior S x R hR htarget E hopen hembE hdisjoint charts
    projection := ⟨cutProjection E,continuous_cutProjection E⟩
    coreEquiv := (cutInteriorCoreHomeomorph E BQ hopen).trans bridge
    core_agrees := fun _ => rfl
    baseBoundary := cutBaseBoundary E BQ
    side := cutSide E
    side_agrees := fun i b t => (cutSide_projection E i b t).trans (hcenter i t)
    boundary_exhaustion := cutInteriorCore_boundary_exhaustion E BQ hembE hdisjoint
    base_boundary_image := ?_
    side_boundary := cutSide_not_core E BQ
    side_distinct := cutSide_distinct E
    side_endpoint_incidence := ?_
    arc_interior_fiber := ?_
    arc_start_fiber := ?_
    arc_end_fiber := ?_
    base_regular_fiber := ?_ }⟩
  · ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact z.property
    · intro hy
      obtain ⟨q,hq⟩ := cutProjection_surjective E (⟨y,hBsubset hy⟩ : ↥Q)
      refine ⟨⟨q,?_⟩,?_⟩
      · change (cutProjection E q).val ∈ B
        exact (congrArg Subtype.val hq).symm ▸ hy
      · exact congrArg Subtype.val hq
  · intro i b
    exact cutSide_endpoint_incidence E BQ i b
      (by change (E i (0,⟨0,by norm_num⟩)).val ∈ B
          rw [hcenter]
          exact (hend i).1)
      (by change (E i (1,⟨0,by norm_num⟩)).val ∈ B
          rw [hcenter]
          exact (hend i).2)
  · intro i t _
    change {z : CutQuotient E | cutProjection E z = a i t} =
      {cutSide E i false t, cutSide E i true t}
    simpa only [hcenter] using cut_arc_center_fiber E hembE hdisjoint i t
  · intro i
    change {z : CutQuotient E | cutProjection E z = a i 0} =
      {cutSide E i false 0, cutSide E i true 0}
    simpa only [hcenter] using cut_arc_center_fiber E hembE hdisjoint i 0
  · intro i
    change {z : CutQuotient E | cutProjection E z = a i 1} =
      {cutSide E i false 1, cutSide E i true 1}
    simpa only [hcenter] using cut_arc_center_fiber E hembE hdisjoint i 1
  · intro y hy hregular
    exact cutBaseBoundary_regular_fiber E BQ hBcenters y hy
      (by simpa only [hcenter] using hregular)

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
