import CurveComplexGenusTwo.Intersection.MarkedBarrier

set_option linter.style.haveILetI false

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The inverse stereographic chart, regarded as an open embedding into the
unpunctured sphere. -/
noncomputable def planeToSphere (M : HyperellipticModel E S) (p : S) :
    Schoenflies.Plane → S := fun z => ((M.puncturedPlane p).symm z).val

theorem planeToSphere_isOpenEmbedding (M : HyperellipticModel E S) (p : S) :
    Topology.IsOpenEmbedding (M.planeToSphere p) := by
  haveI : T2Space S := M.sphere.symm.t2Space
  exact (isOpen_compl_singleton.isOpenEmbedding_subtypeVal).comp
    (M.puncturedPlane p).symm.isOpenEmbedding

theorem planeToSphere_injective (M : HyperellipticModel E S) (p : S) :
    Function.Injective (M.planeToSphere p) :=
  (M.planeToSphere_isOpenEmbedding p).injective

theorem planeToSphere_ne_p (M : HyperellipticModel E S) (p : S)
    (z : Schoenflies.Plane) : M.planeToSphere p z ≠ p :=
  ((M.puncturedPlane p).symm z).property

theorem planeToSphere_image_interior (M : HyperellipticModel E S)
    (p : S) (K : Set Schoenflies.Plane) :
    M.planeToSphere p '' interior K =
      interior (M.planeToSphere p '' K) := by
  let f := M.planeToSphere p
  have hf := M.planeToSphere_isOpenEmbedding p
  haveI : T2Space S := M.sphere.symm.t2Space
  apply Set.Subset.antisymm (hf.isOpenMap.image_interior_subset K)
  rintro y hy
  have hyImage : y ∈ f '' K := interior_subset hy
  obtain ⟨x, hxK, rfl⟩ := hyImage
  refine ⟨x, ?_, rfl⟩
  have hopen : IsOpen (f ⁻¹' interior (f '' K)) :=
    isOpen_interior.preimage hf.continuous
  have hsub : f ⁻¹' interior (f '' K) ⊆ K := by
    intro z hz
    have hzImage : f z ∈ f '' K := interior_subset hz
    obtain ⟨u, huK, hzu⟩ := hzImage
    exact hf.injective hzu.symm ▸ huK
  exact (interior_maximal hsub hopen) hy

theorem planeToSphere_image_frontier_of_compact
    (M : HyperellipticModel E S) (p : S)
    {K : Set Schoenflies.Plane} (hK : IsCompact K) :
    M.planeToSphere p '' frontier K =
      frontier (M.planeToSphere p '' K) := by
  haveI : T2Space S := M.sphere.symm.t2Space
  let f := M.planeToSphere p
  have hf := M.planeToSphere_isOpenEmbedding p
  have hKclosed : IsClosed K := hK.isClosed
  have hImageClosed : IsClosed (f '' K) :=
    (hK.image hf.continuous).isClosed
  have hpre := hf.isOpenMap.preimage_frontier_eq_frontier_preimage
    hf.continuous (f '' K)
  have hpreimage : f ⁻¹' (f '' K) = K := by
    ext z
    constructor
    · rintro ⟨u, hu, hzu⟩
      exact hf.injective hzu.symm ▸ hu
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hfrontPre : f ⁻¹' frontier (f '' K) = frontier K := by
    rw [hpre, hpreimage]
  apply Set.Subset.antisymm
  · intro y hy
    change ∃ z ∈ frontier K, f z = y at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact (show z ∈ f ⁻¹' frontier (f '' K) from
      (Set.ext_iff.mp hfrontPre z).mpr hz)
  · intro y hy
    have hyClosure : y ∈ closure (f '' K) := hy.1
    rw [hImageClosed.closure_eq] at hyClosure
    obtain ⟨z, hz, hzy⟩ := hyClosure
    subst y
    have hzFront : z ∈ frontier K := hfrontPre ▸ hy
    exact ⟨z, hzFront, rfl⟩

/-- Avoidance of the finite planar marks is exactly the source dictionary's
marked-point condition for the disk after returning to the sphere. -/
theorem NonLoopArc.marked_inter_planeRegion
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p : S) (hp : p ∉ a.image)
    (K : Set Schoenflies.Plane)
    (hArc : Set.range (chartedArcMap a p hp) ⊆ K)
    (hAvoid : Disjoint K (planeForbiddenMarks a p : Set Schoenflies.Plane)) :
    (M.cover.branch : Set S) ∩ (M.planeToSphere p '' K) =
      {a.val.map ⟨0, by norm_num⟩, a.val.map ⟨1, by norm_num⟩} := by
  classical
  let f := M.planeToSphere p
  apply Set.Subset.antisymm
  · rintro x ⟨hxBranch, z, hzK, hxz⟩
    by_cases hx0 : x = a.val.map ⟨0, by norm_num⟩
    · exact Set.mem_insert_iff.mpr (Or.inl hx0)
    by_cases hx1 : x = a.val.map ⟨1, by norm_num⟩
    · exact Set.mem_insert_iff.mpr (Or.inr (by simpa using hx1))
    have hxp : x ≠ p := by
      intro he
      exact (M.planeToSphere_ne_p p z) (hxz.trans he)
    have hzEq : z = M.puncturedPlane p ⟨x, hxp⟩ := by
      have hsub : (M.puncturedPlane p).symm z = ⟨x, hxp⟩ :=
        Subtype.ext hxz
      exact ((M.puncturedPlane p).apply_symm_apply z).symm.trans
        (congrArg (M.puncturedPlane p) hsub)
    have hzForbidden : z ∈ planeForbiddenMarks a p := by
      rw [hzEq]
      unfold planeForbiddenMarks
      apply Finset.mem_image.mpr
      refine ⟨x, Finset.mem_filter.mpr ⟨hxBranch, hxp, hx0, hx1⟩, ?_⟩
      simp [hxp]
    exact False.elim (Set.disjoint_left.mp hAvoid hzK hzForbidden)
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with hx0 | hx1
    · subst x
      refine ⟨a.val.start_marked, ?_⟩
      let t : Interval := ⟨0, by norm_num⟩
      have ht : chartedArcMap a p hp t ∈ K := hArc ⟨t, rfl⟩
      refine ⟨chartedArcMap a p hp t, ht, ?_⟩
      simp [planeToSphere, chartedArcMap, t]
    · have hx1' : x = a.val.map ⟨1, by norm_num⟩ := by simpa using hx1
      subst x
      refine ⟨a.val.end_marked, ?_⟩
      let t : Interval := ⟨1, by norm_num⟩
      have ht : chartedArcMap a p hp t ∈ K := hArc ⟨t, rfl⟩
      refine ⟨chartedArcMap a p hp t, ht, ?_⟩
      simp [planeToSphere, chartedArcMap, t]

/-- Transport a certified planar disk and its parametrized frontier through
the actual punctured-sphere chart. -/
theorem NonLoopArc.arcNeighborhood_of_planar_disk
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p : S) (hp : p ∉ a.image)
    (K : Set Schoenflies.Plane)
    (hKcompact : IsCompact K)
    (hDisk : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K)
    (hArc : Set.range (chartedArcMap a p hp) ⊆ interior K)
    (hMarks : (M.cover.branch : Set S) ∩ (M.planeToSphere p '' K) =
      {a.val.map ⟨0, by norm_num⟩, a.val.map ⟨1, by norm_num⟩})
    (boundaryMap : Circle → Schoenflies.Plane)
    (hBoundaryEmbedded : Topology.IsEmbedding boundaryMap)
    (hBoundaryRange : Set.range boundaryMap = frontier K) :
    Nonempty (ArcNeighborhood a) := by
  let f := M.planeToSphere p
  have hf := M.planeToSphere_isOpenEmbedding p
  haveI : T2Space S := M.sphere.symm.t2Space
  let D := f '' K
  let disk : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ D :=
    hDisk.trans (hf.isEmbedding.homeomorphImage K)
  let c : Curve S := {
    map := fun t => f (boundaryMap t)
    embedded := hf.isEmbedding.comp hBoundaryEmbedded }
  have hcurve : c.image = frontier D := by
    change Set.range (f ∘ boundaryMap) = frontier D
    rw [Set.range_comp, hBoundaryRange]
    exact M.planeToSphere_image_frontier_of_compact p hKcompact
  have havoids : Disjoint c.image (M.cover.branch : Set S) := by
    rw [hcurve, Set.disjoint_left]
    intro x hxBoundary hxBranch
    have hxD : x ∈ D := (hKcompact.image hf.continuous).isClosed.frontier_subset hxBoundary
    have hxEnd : x ∈ ({a.val.map ⟨0, by norm_num⟩,
        a.val.map ⟨1, by norm_num⟩} : Set S) := by
      rw [← hMarks]
      exact ⟨hxBranch, hxD⟩
    have hxArc : x ∈ a.image := by
      rcases Set.mem_insert_iff.mp hxEnd with h | h
      · exact ⟨⟨0, by norm_num⟩, h.symm⟩
      · have h' : x = a.val.map ⟨1, by norm_num⟩ := by simpa using h
        exact ⟨⟨1, by norm_num⟩, h'.symm⟩
    have hxInterior : x ∈ interior D := by
      obtain ⟨t, ht⟩ := hxArc
      have hchart : chartedArcMap a p hp t ∈ interior K :=
        hArc ⟨t, rfl⟩
      have hfx : f (chartedArcMap a p hp t) = x := by
        subst x
        simp [f, planeToSphere, chartedArcMap]
      rw [← hfx]
      rw [← M.planeToSphere_image_interior p K]
      exact ⟨chartedArcMap a p hp t, hchart, rfl⟩
    exact Set.disjoint_left.mp disjoint_interior_frontier.symm hxBoundary hxInterior
  refine ⟨{
    closedSet := D
    disk := disk
    arc_inside := ?_
    marked_inside := hMarks
    boundary := ⟨c, havoids⟩
    boundary_eq_frontier := hcurve }⟩
  · intro x hx
    obtain ⟨t, ht⟩ := hx
    have hchart : chartedArcMap a p hp t ∈ interior K := hArc ⟨t, rfl⟩
    have hfx : f (chartedArcMap a p hp t) = x := by
      subst x
      simp [f, planeToSphere, chartedArcMap]
    rw [← hfx, ← M.planeToSphere_image_interior p K]
    exact ⟨chartedArcMap a p hp t, hchart, rfl⟩

/-- The geometric interface expected of the polygonal enclosure: the
forbidden-mark condition is expressed entirely in the chart plane. -/
theorem NonLoopArc.arcNeighborhood_of_planar_disk_avoiding_marks
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p : S) (hp : p ∉ a.image)
    (K : Set Schoenflies.Plane)
    (hKcompact : IsCompact K)
    (hDisk : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K)
    (hArc : Set.range (chartedArcMap a p hp) ⊆ interior K)
    (hAvoid : Disjoint K (planeForbiddenMarks a p : Set Schoenflies.Plane))
    (boundaryMap : Circle → Schoenflies.Plane)
    (hBoundaryEmbedded : Topology.IsEmbedding boundaryMap)
    (hBoundaryRange : Set.range boundaryMap = frontier K) :
    Nonempty (ArcNeighborhood a) := by
  apply a.arcNeighborhood_of_planar_disk (p := p) (hp := hp) (K := K)
    (hKcompact := hKcompact) (hDisk := hDisk) (hArc := hArc)
    (boundaryMap := boundaryMap) (hBoundaryEmbedded := hBoundaryEmbedded)
    (hBoundaryRange := hBoundaryRange)
  · exact a.marked_inter_planeRegion p hp K
      (hArc.trans interior_subset) hAvoid

end CurveComplex.HyperellipticModel
