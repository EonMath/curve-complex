import CurveComplexGenusTwo.Topology.ActualNonstandardCutRegion.ActualCutComponentSelection
import CurveComplexGenusTwo.Topology.ActualNonstandardCutRegion.ComponentOpen
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.ExteriorDictionary
import FiniteBoundaryFansBand
import BoundaryBandSupport
import ClassificationOfSurfaces.Triangulation
import Mathlib
import OriginalChartCapAndCutComponentScaffold
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.OriginalThreeArcCutCount
import CurveComplexGenusTwo.Topology.ActualNonstandardCutRegion.ComponentExteriorConnected
import CurveComplexGenusTwo.Topology.ActualNonstandardCutRegion.ActualCutComponentSelection
import CurveComplexGenusTwo.Topology.ActualNonstandardCutRegion.ComponentOpen
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.ExteriorDictionary
open Set Topology CurveComplex
open scoped Manifold ContDiff
open CurveComplexGenusTwo.SourceTopology
open CurveComplexGenusTwo.SourceTopology.ThreeArcCut
set_option autoImplicit false

/--
For the actual side-doubled cut produced from the original proper arc family,
any complete intrinsic-boundary collar family contains a half-level whose
projected circle bounds no embedded unit disk in the original ambient surface.
The statement keeps the literal chart Q/B data and the original
non-boundary-parallel disk exclusions, and permits parallel disjoint arc
labels.  The cut and collar family are intermediate data to be constructed;
neither is an additional assumption on the protected N2 theorem.
-/
theorem CurveComplexGenusTwo.SourceTopology.ThreeArcCut.original_nonempty_at_most_three_essential_proper_arcs_cut_collar_disk_retention
    (S : Type) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2≤g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0<R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    ∀ (n : ℕ),0<n → n≤3 → ∀ a : Fin n → C(Interval,↥Q),
      (∀ i,IsEmbedding (a i)) →
      (∀ i,(a i 0).val∈B ∧ (a i 1).val∈B) →
      (∀ i t,t∈Set.Ioo (0:Interval) 1 → (a i t).val∉B) →
      (∀ i j,i≠j → Disjoint (Set.range (a i)) (Set.range (a j))) →
      (∀ i,¬∃ b : C(Interval,↥Q),IsEmbedding b ∧
        (∀ t,(b t).val∈B) ∧
        ∃ d : C(Metric.closedBall (0:EuclideanSpace ℝ (Fin 2)) 1,↥Q),
          IsEmbedding d ∧
          d '' {z | z.val∈Metric.sphere (0:EuclideanSpace ℝ (Fin 2)) 1}=
            Set.range (a i) ∪ Set.range b) →
      ∀ C : CompactSideDoubledCut S Q B
        (OriginalBoundaryArc.openDisk S x R ∪ B ∪
          ⋃ i, Set.range (fun t => (a i t).val))ᶜ a,
      letI : TopologicalSpace C.Carrier := C.topology
      ∀ (k : ℕ) (H : Fin k → C(Interval × Circle, C.Carrier)),
        (∀ j, IsEmbedding (H j)) →
        (∀ j, IsOpenEmbedding (fun z : Set.Ioo (0 : ℝ) 1 × Circle =>
          H j (⟨z.1.val, ⟨z.1.property.1.le,z.1.property.2.le⟩⟩,z.2))) →
        (∀ j t z, H j (t,z) ∈ C.core ↔ t ≠ 0) →
        (C.coreᶜ = ⋃ j, Set.range (fun z => H j (0,z))) →
        (∀ i j, i ≠ j → Disjoint (Set.range (H i)) (Set.range (H j))) →
        ∃ j : Fin k,
          ¬ ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S),
            IsEmbedding d ∧
            d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              Set.range (fun z => (C.projection (H j (⟨1/2,by norm_num⟩,z))).val) := by
  classical
  intro Q B n hn hn3 a hemb hend hinterior hpairwise hessential C
  letI : TopologicalSpace C.Carrier := C.topology
  intro k H hHembed hHopen hHcore hHcover hHdisjoint
  letI : ClosedSurface S := Classical.choice hS.2.1
  let F : Set S := OriginalBoundaryArc.openDisk S x R ∪ B ∪
    ⋃ i, Set.range (fun t => (a i t).val)
  have hk : 0 < k := by
    have hb := C.side_boundary ⟨0,hn⟩ false 0
    rw [hHcover] at hb
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hb
    exact Nat.zero_lt_of_lt j.isLt
  have hFclosed : IsClosed F :=
    (original_disk_union_boundary_closed S g hS x R htarget).union
      (finite_arcTrace_closed a)
  have hFconnected : IsConnected F := by
    let E := chartAt (EuclideanSpace ℝ (Fin 2)) x
    let D : Set S := E.symm '' Metric.closedBall (E x) R
    have hD : IsConnected D :=
      (Metric.isConnected_closedBall hR.le).image E.symm
        (E.continuousOn_symm.mono htarget)
    have hpartition : D = OriginalBoundaryArc.openDisk S x R ∪ B := by
      dsimp [D, OriginalBoundaryArc.openDisk, B, E]
      rw [← Set.image_union, Metric.ball_union_sphere]
    letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
    let A : Fin n → Set S := fun i => D ∪ Set.range (fun t => (a i t).val)
    have hA : ∀ i, IsConnected (A i) := by
      intro i
      have harc : IsConnected (Set.range (fun t => (a i t).val)) := by
        simpa only [Set.image_univ] using isConnected_univ.image
          (fun t => (a i t).val) (continuous_subtype_val.comp (a i).continuous).continuousOn
      exact hD.union ⟨(a i 0).val, hpartition.symm ▸ Or.inr (hend i).1,
        Set.mem_range_self 0⟩ harc
    have hcommon : (⋂ i, A i).Nonempty := by
      obtain ⟨y,hy⟩ := hD.nonempty
      exact ⟨y, Set.mem_iInter.mpr (fun _ => Or.inl hy)⟩
    have hconn : IsConnected (⋃ i, A i) :=
      ⟨⟨(a ⟨0,hn⟩ 0).val, Set.mem_iUnion.mpr ⟨⟨0,hn⟩, Or.inr ⟨0,rfl⟩⟩⟩,
        isPreconnected_iUnion hcommon (fun i => (hA i).isPreconnected)⟩
    simpa only [A, ← Set.union_iUnion, hpartition] using hconn
  have hprojection : IsEmbedding (fun w : C.core => (C.projection w.val).val) := by
    have heq : (fun w : C.core => (C.projection w.val).val) =
        (Subtype.val : ↥(Fᶜ) → S) ∘ C.coreEquiv := by
      funext w
      exact C.core_agrees w
    rw [heq]
    exact IsEmbedding.subtypeVal.comp C.coreEquiv.isEmbedding
  have hlevels : ∀ j (t : Interval), t ≠ 0 →
      IsEmbedding (fun z => (C.projection (H j (t,z))).val) ∧
      Disjoint F (Set.range (fun z => (C.projection (H j (t,z))).val)) := by
    intro j t ht
    let f : Circle → C.core := fun z => ⟨H j (t,z),(hHcore j t z).mpr ht⟩
    have hf : IsEmbedding f :=
      ((hHembed j).comp (isEmbedding_prodMkRight t)).codRestrict _ _
    refine ⟨hprojection.comp hf, Set.disjoint_left.mpr ?_⟩
    rintro y hy ⟨z,rfl⟩
    have hout := (C.coreEquiv (f z)).property
    rw [← C.core_agrees (f z)] at hout
    exact hout hy
  have hfrontier : ∀ (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S)),
      IsEmbedding d → frontier (Set.range d) ⊆
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    intro d hd
    let f : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 → S :=
      fun z => d ⟨z.val,Metric.ball_subset_closedBall z.property⟩
    have hf : IsEmbedding f := hd.comp (IsEmbedding.inclusion Metric.ball_subset_closedBall)
    have hfopen : IsOpen (Set.range f) :=
      LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isOpen_range_of_isOpen_of_isEmbedding
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) Metric.isOpen_ball f hf
    have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
    intro y hy
    obtain ⟨z,rfl⟩ := hclosed.frontier_subset hy
    refine ⟨z, ?_, rfl⟩
    apply le_antisymm z.property
    apply not_lt.mp
    intro hz
    have hin : d z ∈ interior (Set.range d) :=
      hfopen.subset_interior_iff.mpr
        (by rintro v ⟨w,rfl⟩; exact Set.mem_range_self _) ⟨⟨z.val,hz⟩,rfl⟩
    exact hy.2 hin
  have hside : ∀ (j : Fin k)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S)),
      IsEmbedding d →
      d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range (fun z => (C.projection (H j (⟨1/2,by norm_num⟩,z))).val) →
      F ⊆ interior (Set.range d) ∨ F ⊆ interior (Set.range d)ᶜ := by
    intro j d hd hb
    apply connected_cap_side (Set.range d) F hFconnected.isPreconnected
    apply (hlevels j ⟨1/2,by norm_num⟩ (by
      intro h
      have := congrArg Subtype.val h
      norm_num at this)).2.mono_right
    rw [← hb]
    exact hfrontier d hd
  by_contra hnone
  push_neg at hnone
  choose d hd hboundary using hnone
  have hcapSide : ∀ j, F ⊆ interior (Set.range (d j)) ∨
      F ⊆ interior (Set.range (d j))ᶜ := fun j =>
    hside j (d j) (hd j) (hboundary j)
  let D₀ : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
  have hpartition : D₀ = OriginalBoundaryArc.openDisk S x R ∪ B := by
    dsimp [D₀, OriginalBoundaryArc.openDisk, B]
    rw [← Set.image_union, Metric.ball_union_sphere]
  have hdisks : ∀ j, Disjoint F (Set.range (d j)) := by
    intro j
    rcases hcapSide j with hin | hout
    · exfalso
      apply hessential ⟨0,hn⟩
      apply original_chart_exterior_arc_in_ambient_disk_boundary_parallel
        S x R hR htarget (a ⟨0,hn⟩) (hemb _) (hend _) (hinterior _) (d j) (hd j)
      · apply Set.Subset.trans ?_ hin
        change D₀ ⊆ F
        rw [hpartition]
        exact Set.subset_union_left
      · apply Set.Subset.trans ?_ (hin.trans interior_subset)
        exact (Set.subset_iUnion (fun i => Set.range (fun t => (a i t).val)) ⟨0,hn⟩).trans
          Set.subset_union_right
    · exact Set.disjoint_left.mpr (fun y hy hdy => interior_subset (hout hy) hdy)
  have hmodels : ∀ j, ∃ e :
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₜ
        ↥(connectedComponent (H j (0,1))),
      ∀ u, (e u).val ∈ C.core ↔
        u.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro j
    have hF : D₀ ∪ ⋃ i, Set.range (fun t => (a i t).val) = F := by
      rw [hpartition]
    have hmodel := actual_cut_collar_exterior_disk_component_model
      S x R hR htarget n a hemb hend hinterior hpairwise
    dsimp only at hmodel
    rw [hF] at hmodel
    exact hmodel C (H j) (hHembed j) (hHopen j) (hHcore j)
      (d j) (hd j) (hboundary j) (hdisks j)
  have hregions : ∀ U : Set S, HyperellipticModel.IsComplementComponent F U →
      DiskRegion Q U := by
    intro U hU
    letI : LocallyConnectedSpace S :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
    obtain ⟨z, hzconn, hcoreimage, hcompactimage⟩ :=
      actual_cut_component_above_original_region S Q B F a C U hU
    obtain ⟨y, hyU, hyF⟩ :=
      complement_component_closure_meets_forbidden F U hFclosed hFconnected.nonempty hU
    obtain ⟨w, hwK, hwπ⟩ := hcompactimage.symm ▸ hyU
    have hwboundary : w ∉ C.core := by
      intro hw
      have he := C.core_agrees ⟨w,hw⟩
      have hnot := (C.coreEquiv ⟨w,hw⟩).property
      rw [← he] at hnot
      change (C.projection w).val ∈ Fᶜ at hnot
      change (C.projection w).val = y at hwπ
      rw [hwπ] at hnot
      exact hnot hyF
    change w ∈ C.coreᶜ at hwboundary
    rw [hHcover] at hwboundary
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hwboundary
    obtain ⟨c, hc⟩ := hj
    have hzeroConnected : IsConnected (Set.range (fun c => H j (0,c))) := by
      simpa only [Set.image_univ] using isConnected_univ.image
        (fun c => H j (0,c)) ((H j).continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    have hbaseK : H j (0,1) ∈ connectedComponent z := by
      have hsub := hzeroConnected.subset_connectedComponent (show w ∈ Set.range (fun c => H j (0,c)) from ⟨c,hc⟩)
      exact (connectedComponent_eq hwK).symm ▸ hsub (Set.mem_range_self 1)
    have hKeq : connectedComponent z = connectedComponent (H j (0,1)) :=
      connectedComponent_eq hbaseK
    obtain ⟨e, he⟩ := hmodels j
    rw [hKeq] at hcoreimage hcompactimage
    let dU : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q) :=
      ⟨fun t => C.projection (e t).val,
        C.projection.continuous.comp (continuous_subtype_val.comp e.continuous)⟩
    have hrange : Set.range (fun t => (dU t).val) = closure U := by
      rw [← hcompactimage]
      ext v
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨(e t).val, (e t).property, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        refine ⟨e.symm ⟨v,hv⟩, ?_⟩
        change (C.projection (e (e.symm ⟨v,hv⟩)).val).val = _
        rw [e.apply_symm_apply]
    let DiskCore : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      {t | t.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
    have hmem : ∀ t : DiskCore, (e t.val).val ∈ C.core :=
      fun t => (he t.val).mpr t.property
    have hinnerEmbed : IsEmbedding (fun t : DiskCore =>
        (⟨(e t.val).val, hmem t⟩ : C.core)) :=
      ((IsEmbedding.subtypeVal.comp e.isEmbedding).comp
        IsEmbedding.subtypeVal).codRestrict C.core hmem
    have hdEmbed : IsEmbedding (fun t : DiskCore => dU t.val) :=
      (cut_core_projection_isEmbedding S Q B F a C).comp hinnerEmbed
    have hinnerRange : Set.range (fun t : DiskCore => (dU t.val).val) = U := by
      rw [← hcoreimage]
      ext v
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨(e t.val).val, ⟨(e t.val).property, hmem t⟩, rfl⟩
      · rintro ⟨v, ⟨hvK,hvcore⟩, rfl⟩
        have ht : (e.symm ⟨v,hvK⟩).val ∈ Metric.ball
            (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
          apply (he _).mp
          simpa only [e.apply_symm_apply] using hvcore
        refine ⟨⟨e.symm ⟨v,hvK⟩,ht⟩, ?_⟩
        change (C.projection (e (e.symm ⟨v,hvK⟩)).val).val = _
        rw [e.apply_symm_apply]
    exact ⟨dU, hrange, hdEmbed, hinnerRange⟩
  have hcount := original_proper_arc_cut_count S g hg hS x R hR htarget
    n a hemb hend hinterior hpairwise (fun U hU _ => Or.inl (hregions U hU))
  omega

open Set Topology CurveComplex
open scoped Manifold ContDiff
open CurveComplexGenusTwo.SourceTopology
open CurveComplexGenusTwo.SourceTopology.ThreeArcCut
open CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry
open LeanEval.Topology.ClassificationOfSurfaces
set_option maxHeartbeats 2000000
set_option autoImplicit false

/--
A finite family of complete collars for the intrinsic boundary of a compact
surface with boundary.  This is a lower geometric construction for the N2
frontier route; it is not a collar supplied as an input to the original curve
carrier theorem.  Every collar is an embedded closed cylinder, its positive
cylinder is open in the surface, its zero circle is exactly on the intrinsic
boundary, and the family exhausts that boundary with pairwise disjoint ranges.
-/
theorem CurveComplexGenusTwo.SourceTopology.ThreeArcCut.compact_surface_finite_disjoint_boundary_collars :
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] [IsManifold (𝓡∂ 2) 0 M],
  ∃ (k : ℕ) (H : Fin k → C(Interval × Circle, M)),
    (∀ j, IsEmbedding (H j)) ∧
    (∀ j, IsOpenEmbedding (fun z : Set.Ioo (0 : ℝ) 1 × Circle =>
      H j (⟨z.1.val, ⟨z.1.property.1.le,z.1.property.2.le⟩⟩,z.2))) ∧
    (∀ j t z, H j (t,z) ∈ ModelWithCorners.interior (I := 𝓡∂ 2) M ↔ t ≠ 0) ∧
    (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ =
      ⋃ j, Set.range (fun z => H j (0,z)) ∧
    (∀ i j, i ≠ j → Disjoint (Set.range (H i)) (Set.range (H j))) := by
  classical
  intro M _ _ _ _ _
  have hInteriorOpen : IsOpen (ModelWithCorners.interior (I := 𝓡∂ 2) M) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    let e := chartAt (EuclideanHalfSpace 2) x
    let P : Set (EuclideanHalfSpace 2) := {y | 0 < y.val 0}
    have hPopen : IsOpen P :=
      isOpen_lt continuous_const (by fun_prop)
    have hNopen : IsOpen (e.source ∩ e ⁻¹' P) :=
      e.continuousOn.isOpen_inter_preimage e.open_source hPopen
    have hxP : e x ∈ P := by
      have h := (LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isInteriorPoint_iff_any_chart
        (𝓡∂ 2) (mem_chart_source (EuclideanHalfSpace 2) x)).mp hx
      rw [interior_range_modelWithCornersEuclideanHalfSpace] at h
      exact h
    apply Filter.mem_of_superset (hNopen.mem_nhds ⟨mem_chart_source _ _, hxP⟩)
    intro y hy
    apply (LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isInteriorPoint_iff_any_chart
      (𝓡∂ 2) hy.1).mpr
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    exact hy.2
  have hBoundaryInChart (e : OpenPartialHomeomorph M (EuclideanHalfSpace 2))
      (y : M) (hy : y ∈ e.source) :
      y ∈ (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ ↔ (e y).val 0 = 0 := by
    change ¬ (𝓡∂ 2).IsInteriorPoint y ↔ _
    rw [LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isInteriorPoint_iff_any_chart
      (𝓡∂ 2) hy, interior_range_modelWithCornersEuclideanHalfSpace]
    change ¬ 0 < (e y).val 0 ↔ (e y).val 0 = 0
    constructor
    · intro h
      exact le_antisymm (le_of_not_gt h) (e y).property
    · intro h
      rw [h]
      exact lt_irrefl 0
  have hBoundaryCompact : IsCompact ((ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ) :=
    hInteriorOpen.isClosed_compl.isCompact
  by_cases hBoundaryEmpty : (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ = ∅
  · refine ⟨0, fun j => Fin.elim0 j, ?_⟩
    simp [hBoundaryEmpty]
  · have hBoundaryNonempty : ((ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hBoundaryEmpty
    obtain ⟨boundaryCharts, hBoundaryCharts⟩ :=
      hBoundaryCompact.elim_finite_subcover
        (fun x : ↥((ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ) =>
          (chartAt (EuclideanHalfSpace 2) x.val).source)
        (fun x => (chartAt (EuclideanHalfSpace 2) x.val).open_source)
        (by
          intro x hx
          exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_chart_source _ _⟩)
    have hBoundaryChartsNonempty : boundaryCharts.Nonempty := by
      obtain ⟨x, hx⟩ := hBoundaryNonempty
      obtain ⟨y, hy, _⟩ := Set.mem_iUnion₂.mp (hBoundaryCharts hx)
      exact ⟨y, hy⟩
    have hParameter (V : Type) [Fintype V] [DecidableEq V] (F : Finset (Finset V))
        (m : ℕ) (hm : 3 ≤ m) (v : Fin m → V)
        (hedge : ∀ i, {v i,v (cyclicNext m hm i)} ∈ boundaryEdges F) :
        ∃ r : C(Circle, GeometricRealization V F),
          ∀ (i : Fin m) (s : Interval) (w : V),
            (r (edgeClock m i s)).val w =
            (1-(s:ℝ))*(if v i=w then 1 else 0) +
            (s:ℝ)*(if v (cyclicNext m hm i)=w then 1 else 0) := by
      classical
      let P (i : Fin m) (s : Interval) : GeometricRealization V F :=
        ⟨(1-(s:ℝ)) • Pi.single (v i) 1 + (s:ℝ) • Pi.single (v (cyclicNext m hm i)) 1, by
          obtain ⟨t,ht,_⟩ := boundaryEdge_unique_triangle (hedge i)
          refine ⟨(convex_stdSimplex ℝ V) (single_mem_stdSimplex ℝ (v i))
            (single_mem_stdSimplex ℝ (v (cyclicNext m hm i)))
            (sub_nonneg.mpr s.property.2) s.property.1 (by ring),t,ht.1,?_⟩
          intro w hw
          have h0 : v i ≠ w := fun h => hw (h ▸ ht.2 (by simp))
          have h1 : v (cyclicNext m hm i) ≠ w := fun h => hw (h ▸ ht.2 (by simp))
          simp [Pi.single_apply, h0,h1,Ne.symm h0,Ne.symm h1]⟩
      have hPcontinuous (i : Fin m) : Continuous (P i) := by
        apply Continuous.subtype_mk
        fun_prop
      have hPseam (i : Fin m) : P i 1 = P (cyclicNext m hm i) 0 := by
        apply Subtype.ext
        simp [P]
      have hClockInj (i j : Fin m) (s t : Interval) (hs : (s:ℝ)<1) (ht : (t:ℝ)<1)
          (he : edgeClock m i s = edgeClock m j t) : i=j ∧ s=t := by
        have hmp : (0:ℝ)< m := by exact_mod_cast (by omega : 0< m)
        have hrange (i : Fin m) (s : Interval) (hs : (s:ℝ)<1) :
            2*Real.pi*((i.val:ℝ)+(s:ℝ))/m ∈ Ico (0:ℝ) (2*Real.pi) := by
          refine ⟨div_nonneg (mul_nonneg Real.two_pi_pos.le (add_nonneg (Nat.cast_nonneg _) s.property.1)) hmp.le,?_⟩
          apply (div_lt_iff₀ hmp).mpr
          have hi : (i.val:ℝ)+1 ≤ m := by exact_mod_cast i.isLt
          nlinarith [Real.two_pi_pos]
        have ha := Circle.exp_injOn_Ico (a:=0) (b:=2*Real.pi) (by simp)
          (hrange i s hs) (hrange j t ht) he
        have hab : (i.val:ℝ)+(s:ℝ)=(j.val:ℝ)+(t:ℝ) := by
          have := (div_left_inj' (ne_of_gt hmp)).mp ha
          nlinarith [Real.two_pi_pos]
        have hi : i=j := by
          apply Fin.ext
          apply le_antisymm
          · by_contra h
            have hij : j.val+1 ≤ i.val := by omega
            have hij' : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast hij
            linarith [s.property.1]
          · by_contra h
            have hij : i.val+1 ≤ j.val := by omega
            have hij' : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast hij
            linarith [t.property.1]
        refine ⟨hi,Subtype.ext ?_⟩
        simpa [hi] using hab
      have hNormalize (i : Fin m) (s : Interval) :
          ∃ (j : Fin m) (t : Interval), (t:ℝ)<1 ∧ edgeClock m j t = edgeClock m i s ∧ P j t=P i s := by
        by_cases hs : s=1
        · subst s
          exact ⟨cyclicNext m hm i,0,by norm_num,(edgeClock_whole_seam hm i).symm,(hPseam i).symm⟩
        · exact ⟨i,s,lt_of_le_of_ne s.property.2 (fun h => hs (Subtype.ext h)),rfl,rfl⟩
      let q : Fin m × Interval → Circle := fun x => edgeClock m x.1 x.2
      have hqcont : Continuous q := by
        apply continuous_prod_of_discrete_left.mpr
        intro i
        dsimp [q,edgeClock]
        fun_prop
      have hqsurj : Function.Surjective q := by
        intro z
        obtain ⟨i,s,_,h⟩ := edgeClock_cover hm z
        exact ⟨(i,s),h⟩
      let f : Fin m × Interval → GeometricRealization V F := fun x => P x.1 x.2
      have hfcont : Continuous f := continuous_prod_of_discrete_left.mpr hPcontinuous
      have hfiber (x y : Fin m × Interval) (h : q x=q y) : f x=f y := by
        obtain ⟨i,s,hs,hi,hPi⟩ := hNormalize x.1 x.2
        obtain ⟨j,t,ht,hj,hPj⟩ := hNormalize y.1 y.2
        obtain ⟨rfl,rfl⟩ := hClockInj i j s t hs ht (hi.trans (h.trans hj.symm))
        exact hPi.symm.trans hPj
      have hqquot := Topology.IsQuotientMap.of_surjective_continuous hqsurj hqcont
      choose sec hsection using hqsurj
      let r : Circle → GeometricRealization V F := fun z => f (sec z)
      have hrq (x) : r (q x) = f x := hfiber _ _ (hsection _)
      have hrcont : Continuous r := by
        apply hqquot.continuous_iff.mpr
        convert hfcont using 1
        funext x
        exact hrq x
      refine ⟨⟨r,hrcont⟩,?_⟩
      intro i s w
      have h := congrArg (fun z : GeometricRealization V F => z.val w) (hrq (i,s))
      simpa [f,P,Pi.single_apply,eq_comm] using h
    have hCycles (V : Type) [Fintype V] [DecidableEq V] (F : Finset (Finset V))
        (fans : HasOrderedBoundaryFans F) :
        ∃ (k : ℕ) (cs : Fin k → BoundaryCycle F),
          boundaryLocus F = ⋃ j, Set.range (cs j).circle ∧
          (∀ i j, i ≠ j → Disjoint (Set.range (cs i).circle) (Set.range (cs j).circle)) := by
      classical
      let G : SimpleGraph V := {
        Adj := boundaryAdjacent F
        symm := ⟨by intro a b h; simpa [boundaryAdjacent,Finset.pair_comm] using h⟩
        loopless := ⟨by
          intro v h
          have hc := boundaryEdge_card h
          simpa using hc⟩ }
      have hbound (v : V) : (G.neighborSet v).Nonempty ↔ v ∈ boundaryVertices F := by
        constructor
        · rintro ⟨w,hw⟩
          exact Finset.mem_biUnion.mpr ⟨{v,w},hw,by simp⟩
        · intro hv
          obtain ⟨f⟩ := fans v hv
          exact ⟨f.vertex 0,((f.boundary_edges_exact _).mpr (Or.inl rfl)).1⟩
      have hcycles : G.IsCycles := by
        intro v hv
        obtain ⟨f⟩ := fans v ((hbound v).mp hv)
        have hn : G.neighborSet v = {f.vertex 0, f.vertex (Fin.last f.length)} := by
          ext w
          change {v,w} ∈ boundaryEdges F ↔ _
          have he := f.boundary_edges_exact {v,w}
          constructor
          · intro hw
            rcases he.mp ⟨hw,by simp⟩ with h | h
            · left
              have hw' : w ∈ ({v,f.vertex 0} : Finset V) := h ▸ (by simp)
              simpa [Ne.symm (G.ne_of_adj hw)] using hw'
            · right
              have hw' : w ∈ ({v,f.vertex (Fin.last f.length)} : Finset V) := h ▸ (by simp)
              simpa [Ne.symm (G.ne_of_adj hw)] using hw'
          · rintro (rfl | rfl)
            · exact (he.mpr (Or.inl rfl)).1
            · exact (he.mpr (Or.inr rfl)).1
        rw [hn]
        apply Set.ncard_pair
        intro h
        have h' := congrArg Fin.val (f.injective h)
        have := f.positive
        simp at h'
        omega
      let J := {c : G.ConnectedComponent // ∃ v ∈ c.supp, v ∈ boundaryVertices F}
      have hex (c : J) : ∃ b : BoundaryCycle F, ∀ i, b.vertex i ∈ c.val.supp := by
        obtain ⟨v,hv,hvb⟩ := c.property
        obtain ⟨p,hp,hpc⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv
          ((hbound v).mpr hvb)
        let vert : Fin p.length → V := fun i => p.getVert i.val
        have hnext (i : Fin p.length) : vert (cyclicNext p.length hp.three_le_length i) =
            p.getVert (i.val+1) := by
          dsimp [vert,cyclicNext]
          by_cases hi : i.val+1 < p.length
          · rw [Nat.mod_eq_of_lt hi]
          · have hi' : i.val+1=p.length := by omega
            rw [hi',Nat.mod_self,p.getVert_zero,p.getVert_length]
        have hvert (i : Fin p.length) : vert i ∈ c.val.supp := by
          rw [← hpc,p.mem_verts_toSubgraph]
          exact p.getVert_mem_support _
        have hedge (i : Fin p.length) : {vert i,vert (cyclicNext p.length hp.three_le_length i)}
            ∈ boundaryEdges F := by
          rw [hnext]
          exact p.adj_getVert_succ i.isLt
        obtain ⟨r,hr⟩ := hParameter V F p.length hp.three_le_length vert hedge
        refine ⟨{
          length := p.length
          length_ge_three := hp.three_le_length
          vertex := vert
          vertex_injective := ?_
          component_edges_exact := ?_
          circle := r
          circle_clock := hr },hvert⟩
        · intro i j h
          apply Fin.ext
          exact hp.getVert_injOn' (by change i.val ≤ p.length-1; omega)
            (by change j.val ≤ p.length-1; omega) h
        · intro e
          constructor
          · rintro ⟨he,u,hu,hreach⟩
            have huc : u ∈ c.val.supp := by
              have hreach' : G.Reachable (vert ⟨0,by have := hp.three_le_length; omega⟩) u :=
                (G.reachable_iff_reflTransGen _ _).mpr hreach
              rw [c.val.mem_supp_iff]
              exact (SimpleGraph.ConnectedComponent.sound hreach').symm.trans
                ((c.val.mem_supp_iff _).mp (hvert _))
            obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp (boundaryEdge_card he)
            have hadj : G.Adj a b := he
            have hac : a ∈ c.val.supp := by
              rcases (by simpa using hu : u=a ∨ u=b) with rfl | rfl
              · exact huc
              · exact (c.val.mem_supp_congr_adj hadj).mpr huc
            have hap : a ∈ p.toSubgraph.verts := hpc ▸ hac
            have habp := (hp.adj_toSubgraph_iff_of_isCycles hcycles hap b).mpr hadj
            obtain ⟨i,hi,hiab⟩ := p.mk_mem_edges_iff_exists.mp
              (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp habp)
            refine ⟨⟨i,hi⟩,?_⟩
            rw [hnext]
            change {a,b} = {p.getVert i,p.getVert (i+1)}
            have hpair := congrArg Sym2.toFinset hiab
            simpa [Sym2.toFinset_mk_eq] using hpair.symm
          · rintro ⟨i,rfl⟩
            refine ⟨hedge i,vert i,by simp,?_⟩
            apply (G.reachable_iff_reflTransGen _ _).mp
            exact c.val.reachable_of_mem_supp (hvert _) (hvert i)
      choose cycles hvertices using hex
      have hEdgeCovered (c : BoundaryCycle F) (i : Fin c.length)
          (q : GeometricRealization V F)
          (hq : q.val ∈ GeometricFace V {c.vertex i,c.vertex (cyclicNext c.length c.length_ge_three i)}) :
          q ∈ Set.range c.circle := by
        let a := c.vertex i
        let b := c.vertex (cyclicNext c.length c.length_ge_three i)
        have hab : a ≠ b := c.consecutive_vertices_ne i
        have hsum : q.val a + q.val b = 1 := by
          calc
            _ = ∑ w ∈ ({a,b} : Finset V), q.val w := by simp [hab]
            _ = ∑ w : V, q.val w := by
              apply Finset.sum_subset (Finset.subset_univ _)
              intro w _ hw
              exact hq.2 w hw
            _ = 1 := q.property.1.2
        let t : Interval := ⟨q.val b, q.property.1.1 b, by linarith [q.property.1.1 a]⟩
        refine ⟨edgeClock c.length i t,?_⟩
        apply Subtype.ext
        funext w
        rw [c.circle_clock]
        change (1-q.val b)*(if a=w then 1 else 0) + q.val b*(if b=w then 1 else 0) = q.val w
        by_cases haw : a=w
        · subst w
          simp only [ite_true,if_neg (Ne.symm hab),mul_one,mul_zero,add_zero]
          linarith
        · by_cases hbw : b=w
          · subst w
            simp [hab]
          · have hw : w ∉ ({a,b} : Finset V) := by simp [Ne.symm haw,Ne.symm hbw]
            simp [haw,hbw,hq.2 w hw]
      have hcoverage : boundaryLocus F = ⋃ j : J, Set.range (cycles j).circle := by
        apply Set.Subset.antisymm
        · rintro q ⟨e,he,hqe⟩
          obtain ⟨a,b,hab,hepair⟩ := Finset.card_eq_two.mp (boundaryEdge_card he)
          have ha : a ∈ boundaryVertices F :=
            Finset.mem_biUnion.mpr ⟨e,he,by simp [hepair]⟩
          let j : J := ⟨G.connectedComponentMk a,a,rfl,ha⟩
          have hreach : Relation.ReflTransGen (boundaryAdjacent F)
              ((cycles j).vertex ⟨0,by have := (cycles j).length_ge_three; omega⟩) a := by
            apply (G.reachable_iff_reflTransGen _ _).mp
            apply SimpleGraph.ConnectedComponent.exact
            exact (j.val.mem_supp_iff _).mp (hvertices j _)
          obtain ⟨i,hi⟩ := ((cycles j).component_edges_exact e).mp
            ⟨he,a,by simp [hepair],hreach⟩
          apply Set.mem_iUnion.mpr
          refine ⟨j,hEdgeCovered (cycles j) i q ?_⟩
          simpa [hi] using hqe
        · intro q hq
          obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hq
          exact (cycles j).range_subset_boundary hj
      have hdisjoint (i j : J) (hij : i ≠ j) :
          Disjoint (Set.range (cycles i).circle) (Set.range (cycles j).circle) := by
        rw [Set.disjoint_left]
        rintro q ⟨z,rfl⟩ ⟨w,hw⟩
        obtain ⟨a,s,hs,hz⟩ := edgeClock_cover (cycles i).length_ge_three z
        obtain ⟨b,t,ht,hww⟩ := edgeClock_cover (cycles j).length_ge_three w
        have hpos : 0 < ((cycles j).circle (edgeClock (cycles j).length b t)).val
            ((cycles i).vertex a) := by
          rw [hww,hw,← hz,(cycles i).clock_coordinate_start]
          linarith
        rcases (cycles j).clock_positive_coordinate b t ((cycles i).vertex a) hpos with he | he
        · apply hij
          apply Subtype.ext
          exact SimpleGraph.ConnectedComponent.eq_of_common_vertex (hvertices i a)
            (he ▸ hvertices j b)
        · apply hij
          apply Subtype.ext
          exact SimpleGraph.ConnectedComponent.eq_of_common_vertex (hvertices i a)
            (he ▸ hvertices j _)
      letI : Fintype J := Fintype.ofFinite J
      let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
      refine ⟨Fintype.card J,fun i => cycles (e i),?_,?_⟩
      · rw [hcoverage]
        ext x
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨j,hj⟩
          exact ⟨e.symm j,by simpa using hj⟩
        · rintro ⟨i,hi⟩
          exact ⟨e i,hi⟩
      · intro i j hij
        exact hdisjoint _ _ (fun h => hij (e.injective h))
    have hA2 : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Finset (Finset V))
          (hfaces : ∀ t ∈ F, t.card = 3)
          (fans : (v : ↥(boundaryVertices F)) → OrderedBoundaryFan F v.val)
          (c : BoundaryCycle F) (U : Set (GeometricRealization V F))
          (hU : IsOpen U) (hcontains : Set.range c.circle ⊆ U),
          Nonempty (BoundaryCycleInwardBand c U) := by
      exact finite_boundary_fan_cycle_inward_band
    have hConnected (N : Type) [TopologicalSpace N] [T2Space N] [CompactSpace N] [ConnectedSpace N]
        [ChartedSpace (EuclideanHalfSpace 2) N] [IsManifold (𝓡∂ 2) 0 N] :
      ∃ (k : ℕ) (H : Fin k → C(Interval × Circle, N)),
        (∀ j, IsEmbedding (H j)) ∧
        (∀ j, IsOpenEmbedding (fun z : Set.Ioo (0 : ℝ) 1 × Circle =>
          H j (⟨z.1.val, ⟨z.1.property.1.le,z.1.property.2.le⟩⟩,z.2))) ∧
        (∀ j t z, H j (t,z) ∈ ModelWithCorners.interior (I := 𝓡∂ 2) N ↔ t ≠ 0) ∧
        (ModelWithCorners.interior (I := 𝓡∂ 2) N)ᶜ =
          ⋃ j, Set.range (fun z => H j (0,z)) ∧
        (∀ i j, i ≠ j → Disjoint (Set.range (H i)) (Set.range (H j))) := by
      classical
      obtain ⟨T⟩ := moise_triangulation N
      obtain ⟨hrecognition,hfans⟩ := geometric_surface_triangulation_boundary_fans N T
      obtain ⟨k,cs,hcover,hdisjoint⟩ := hCycles T.Vertex T.faces hfans
      have hclosed (j : Fin k) : IsClosed (Set.range (cs j).circle) :=
        (isCompact_range (cs j).circle.continuous).isClosed
      have hfilters : Pairwise (fun i j : Fin k =>
          Disjoint (𝓝ˢ (Set.range (cs i).circle)) (𝓝ˢ (Set.range (cs j).circle))) := by
        intro i j hij
        exact disjoint_nhdsSet_nhdsSet (hclosed i) (hclosed j) (hdisjoint i j hij)
      obtain ⟨U,hU,hUsep⟩ := hfilters.exists_mem_filter_basis_of_disjoint
        (fun i => hasBasis_nhdsSet (Set.range (cs i).circle))
      let fans : (v : ↥(boundaryVertices T.faces)) → OrderedBoundaryFan T.faces v.val :=
        fun v => Classical.choice (hfans v.val v.property)
      have hbands (j : Fin k) : Nonempty (BoundaryCycleInwardBand (cs j) (U j)) :=
        hA2 T.Vertex T.faces T.faces_card fans (cs j) (U j) (hU j).1 (hU j).2
      let B (j : Fin k) : BoundaryCycleInwardBand (cs j) (U j) := Classical.choice (hbands j)
      let H (j : Fin k) : C(Interval × Circle,N) := ⟨fun x => T.homeo ((B j).band x), T.homeo.continuous.comp (B j).band.continuous⟩
      refine ⟨k,H,?_,?_,?_,?_,?_⟩
      · intro j
        exact T.homeo.isEmbedding.comp (B j).embedded
      · intro j
        exact T.homeo.isOpenEmbedding.comp (B j).positive_open
      · intro j t z
        have he : ¬ H j (t,z) ∈ ModelWithCorners.interior (I := 𝓡∂ 2) N ↔ t=0 :=
          (hrecognition ((B j).band (t,z))).trans ((B j).boundary_exact t z)
        simpa only [not_not] using not_congr he
      · ext y
        constructor
        · intro hy
          have hq : T.homeo.symm y ∈ boundaryLocus T.faces :=
            (hrecognition (T.homeo.symm y)).mp (by simpa using hy)
          rw [hcover] at hq
          obtain ⟨j,z,hz⟩ := Set.mem_iUnion.mp hq
          refine Set.mem_iUnion.mpr ⟨j,z,?_⟩
          change T.homeo ((B j).band (0,z))=y
          rw [(B j).zero_clock,hz,T.homeo.apply_symm_apply]
        · intro hy
          obtain ⟨j,z,hz⟩ := Set.mem_iUnion.mp hy
          rw [← hz]
          exact (hrecognition ((B j).band (0,z))).mpr ((B j).boundary_exact 0 z |>.mpr rfl)
      · intro i j hij
        rw [Set.disjoint_left]
        rintro y ⟨x,hx⟩ ⟨x',hx'⟩
        have he : (B i).band x = (B j).band x' := T.homeo.injective (hx.trans hx'.symm)
        exact Set.disjoint_left.mp (hUsep hij) ((B i).supported ⟨x,rfl⟩)
          (he ▸ (B j).supported ⟨x',rfl⟩)
    letI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) M
    let C := ConnectedComponents M
    letI : Fintype C := Fintype.ofFinite C
    choose rep hrep using (show ∀ c : C, ∃ x : M, ConnectedComponents.mk x=c from
      fun c => ConnectedComponents.surjective_coe c)
    let K (c : C) : TopologicalSpace.Opens M := ⟨connectedComponent (rep c),isOpen_connectedComponent⟩
    have hmem (c : C) (x : M) : x ∈ K c ↔ ConnectedComponents.mk x=c := by
      change x ∈ connectedComponent (rep c) ↔ _
      rw [← ConnectedComponents.coe_eq_coe',hrep]
    letI (c : C) : CompactSpace (K c) :=
      isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
    letI (c : C) : ConnectedSpace (K c) :=
      isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    have hint (c : C) (x : K c) :
        x ∈ ModelWithCorners.interior (I := 𝓡∂ 2) (K c) ↔
        x.val ∈ ModelWithCorners.interior (I := 𝓡∂ 2) M :=
      ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val
    have hlocal (c : C) := hConnected (K c)
    choose k H hemb hopen hinside hcover hdisj using hlocal
    let J := (c : C) × Fin (k c)
    let H' (j : J) : C(Interval × Circle,M) :=
      ⟨fun x => (H j.1 j.2 x).val,continuous_subtype_val.comp (H j.1 j.2).continuous⟩
    have hemb' (j : J) : IsEmbedding (H' j) :=
      (K j.1).isOpenEmbedding'.isEmbedding.comp (hemb j.1 j.2)
    have hopen' (j : J) : IsOpenEmbedding (fun z : Set.Ioo (0 : ℝ) 1 × Circle =>
        H' j (⟨z.1.val, ⟨z.1.property.1.le,z.1.property.2.le⟩⟩,z.2)) :=
      (K j.1).isOpenEmbedding'.comp (hopen j.1 j.2)
    have hinside' (j : J) (t : Interval) (z : Circle) :
        H' j (t,z) ∈ ModelWithCorners.interior (I := 𝓡∂ 2) M ↔ t ≠ 0 :=
      (hint j.1 (H j.1 j.2 (t,z))).symm.trans (hinside j.1 j.2 t z)
    have hcover' : (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ =
        ⋃ j : J, Set.range (fun z => H' j (0,z)) := by
      ext x
      constructor
      · intro hx
        let c : C := ConnectedComponents.mk x
        let y : K c := ⟨x,(hmem c x).mpr rfl⟩
        have hy : y ∈ (ModelWithCorners.interior (I := 𝓡∂ 2) (K c))ᶜ := by
          intro hy
          exact hx ((hint c y).mp hy)
        rw [hcover c] at hy
        obtain ⟨i,z,hz⟩ := Set.mem_iUnion.mp hy
        refine Set.mem_iUnion.mpr ⟨⟨c,i⟩,z,?_⟩
        exact congrArg Subtype.val hz
      · intro hx
        obtain ⟨j,z,hz⟩ := Set.mem_iUnion.mp hx
        rw [← hz]
        exact fun h => (hinside' j 0 z).mp h rfl
    have hdisj' (i j : J) (hij : i ≠ j) : Disjoint (Set.range (H' i)) (Set.range (H' j)) := by
      rw [Set.disjoint_left]
      rintro x ⟨a,ha⟩ ⟨b,hb⟩
      have hci : ConnectedComponents.mk x=i.1 := (hmem i.1 x).mp (ha ▸ (H i.1 i.2 a).property)
      have hcj : ConnectedComponents.mk x=j.1 := (hmem j.1 x).mp (hb ▸ (H j.1 j.2 b).property)
      rcases i with ⟨c,i⟩
      rcases j with ⟨d,j⟩
      have hcd : c=d := hci.symm.trans hcj
      subst d
      have hij' : i ≠ j := fun h => hij (by cases h; rfl)
      have he : H c i a = H c j b := Subtype.ext (ha.trans hb.symm)
      exact Set.disjoint_left.mp (hdisj c i j hij') ⟨a,rfl⟩ ⟨b,he.symm⟩
    letI : Fintype J := Fintype.ofFinite J
    let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
    refine ⟨Fintype.card J,fun i => H' (e i),fun i => hemb' (e i),
      fun i => hopen' (e i),fun i => hinside' (e i),?_,?_⟩
    · rw [hcover']
      exact (e.surjective.iUnion_comp _).symm
    · intro i j hij
      exact hdisj' _ _ (fun h => hij (e.injective h))
