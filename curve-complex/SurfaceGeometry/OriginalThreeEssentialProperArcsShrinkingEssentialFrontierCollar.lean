import OriginalThreeEssentialProperArcsFrontierSupportHelpers
-- Formalizer request only. This declaration has not been approved or registered.
-- Copy the exact original import/definition context and all binders below.
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalBRecognitionConsumer
import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
import CurveComplexGenusTwo.Topology.ActualNonstandardCutRegion.ActualCutComponentSelection
import CurveComplexGenusTwo.Topology.ActualNonstandardCutRegion.ComponentOpen
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.ExteriorDictionary
open Set Topology CurveComplex
open scoped Manifold ContDiff
open CurveComplexGenusTwo.SourceTopology
open CurveComplexGenusTwo.SourceTopology.ThreeArcCut
set_option autoImplicit false

theorem CurveComplexGenusTwo.SourceTopology.ThreeArcCut.original_nonempty_at_most_three_essential_proper_arcs_shrinking_essential_frontier_collar
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
      ∃ E : C(Interval × Circle, S),
        IsOpenEmbedding (fun z : Set.Ioo (0 : ℝ) 1 × Circle =>
          E (⟨z.1.val, ⟨z.1.property.1.le,z.1.property.2.le⟩⟩,z.2)) ∧
        (∀ z, E (0,z) ∈ B ∪ ⋃ i, Set.range (fun t => (a i t).val)) ∧
        (∀ t : Interval, t ∈ Set.Ioo 0 1 →
          Set.range (fun z => E (t,z)) ⊆ interior Q ∧
          ∀ i, Disjoint (Set.range (fun z => E (t,z)))
            (Set.range (fun s => (a i s).val))) ∧
        ∃ c : EssentialCurve S,
          c.val.image = Set.range (fun z => E (⟨1/2,by norm_num⟩,z)) := by
  have hproject (S : Type) [TopologicalSpace S] (Q B F : Set S)
      {n : ℕ} (a : Fin n → C(Interval, ↥Q))
      (C : CompactSideDoubledCut S Q B Fᶜ a)
      (hF : IsClosed F) (hFQ : Fᶜ ⊆ interior Q)
      (ha : ∀ i t, (a i t).val ∈ F) :
      letI : TopologicalSpace C.Carrier := C.topology
      ∀ (H : C(Interval × Circle, C.Carrier)),
        IsOpenEmbedding (fun z : Set.Ioo (0 : ℝ) 1 × Circle =>
          H (⟨z.1.val, ⟨z.1.property.1.le, z.1.property.2.le⟩⟩, z.2)) →
        (∀ z, H (0,z) ∉ C.core) →
        (∀ t : Interval, t ∈ Set.Ioo 0 1 → ∀ z, H (t,z) ∈ C.core) →
        ∃ E : C(Interval × Circle, S),
          (∀ w, E w = (C.projection (H w)).val) ∧
          IsOpenEmbedding (fun z : Set.Ioo (0 : ℝ) 1 × Circle =>
            E (⟨z.1.val, ⟨z.1.property.1.le,z.1.property.2.le⟩⟩,z.2)) ∧
          (∀ z, E (0,z) ∈ B ∪ ⋃ i, Set.range (fun t => (a i t).val)) ∧
          (∀ t : Interval, t ∈ Set.Ioo 0 1 →
            Set.range (fun z => E (t,z)) ⊆ interior Q ∧
            ∀ i, Disjoint (Set.range (fun z => E (t,z)))
              (Set.range (fun s => (a i s).val))) := by
    letI : TopologicalSpace C.Carrier := C.topology
    intro H hH hzero hpositive
    let E : C(Interval × Circle, S) :=
      ⟨fun w => (C.projection (H w)).val,
        continuous_subtype_val.comp (C.projection.continuous.comp H.continuous)⟩
    have hcore : IsOpenEmbedding (fun w : C.core => (C.projection w.val).val) := by
      have heq : (fun w : C.core => (C.projection w.val).val) =
          (Subtype.val : ↥Fᶜ → S) ∘ C.coreEquiv := by
        funext w
        exact C.core_agrees w
      rw [heq]
      exact hF.isOpen_compl.isOpenEmbedding_subtypeVal.comp C.coreEquiv.isOpenEmbedding
    have hmap (w : Set.Ioo (0 : ℝ) 1 × Circle) :
        H (⟨w.1.val, ⟨w.1.property.1.le,w.1.property.2.le⟩⟩,w.2) ∈ C.core :=
      hpositive _ ⟨w.1.property.1, w.1.property.2⟩ w.2
    let Hcore : Set.Ioo (0 : ℝ) 1 × Circle → C.core := fun w =>
      ⟨H (⟨w.1.val, ⟨w.1.property.1.le,w.1.property.2.le⟩⟩,w.2),hmap w⟩
    have hHcore : IsOpenEmbedding Hcore :=
      C.core_open.isOpenEmbedding_subtypeVal.of_comp Hcore hH
    refine ⟨E, fun _ => rfl, hcore.comp hHcore, ?_, ?_⟩
    · intro z
      have hb : H (0,z) ∈ C.coreᶜ := hzero z
      rw [C.boundary_exhaustion] at hb
      rcases hb with hb | hb
      · left
        exact C.base_boundary_image ▸ ⟨⟨H (0,z),hb⟩,rfl⟩
      · right
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hb
        apply Set.mem_iUnion.mpr
        refine ⟨i,?_⟩
        rcases hi with ⟨t,ht⟩ | ⟨t,ht⟩
        · refine ⟨t,?_⟩
          change (a i t).val = (C.projection (H (0,z))).val
          rw [← ht,C.side_agrees]
        · refine ⟨t,?_⟩
          change (a i t).val = (C.projection (H (0,z))).val
          rw [← ht,C.side_agrees]
    · intro t ht
      have hmem (z : Circle) : E (t,z) ∈ Fᶜ := by
        change (C.projection (H (t,z))).val ∈ Fᶜ
        rw [C.core_agrees ⟨H (t,z),hpositive t ht z⟩]
        exact (C.coreEquiv ⟨H (t,z),hpositive t ht z⟩).property
      constructor
      · rintro y ⟨z,rfl⟩
        exact hFQ (hmem z)
      · intro i
        apply Set.disjoint_left.mpr
        rintro y ⟨z,rfl⟩ ⟨s,hs⟩
        change (a i s).val = E (t,z) at hs
        apply hmem z
        rw [← hs]
        exact ha i s
  classical
  intro Q B n hn hn3 a hemb hend hinterior hpairwise hessential
  letI : ClosedSurface S := Classical.choice hS.2.1
  let F : Set S := OriginalBoundaryArc.openDisk S x R ∪ B ∪
    ⋃ i, Set.range (fun t => (a i t).val)
  obtain ⟨C⟩ : Nonempty (CompactSideDoubledCut S Q B Fᶜ a) :=
    original_exterior_has_compact_side_doubled_cut S g hg hS x R hR htarget
      n a hemb hend hinterior hpairwise
  letI : TopologicalSpace C.Carrier := C.topology
  letI : T2Space C.Carrier := C.hausdorff
  letI : CompactSpace C.Carrier := C.compact
  letI : ChartedSpace (EuclideanHalfSpace 2) C.Carrier := C.charts
  letI : IsManifold (𝓡∂ 2) 0 C.Carrier := C.manifold
  have hF : IsClosed F :=
    (original_disk_union_boundary_closed S g hS x R htarget).union
      (finite_arcTrace_closed a)
  have hFQ : Fᶜ ⊆ interior Q := by
    rw [OriginalBoundaryArc.exterior_interior_eq_complement_chart_closed_disk
      S g hS x R hR htarget]
    intro y hy hbase
    exact hy (Or.inl hbase)
  have haF : ∀ i t, (a i t).val ∈ F := by
    intro i t
    exact Or.inr (Set.mem_iUnion.mpr ⟨i,Set.mem_range_self t⟩)

  have hgraph : (fun w : C.Carrier => (C.projection w).val) '' C.coreᶜ =
      B ∪ ⋃ i, Set.range (fun t => (a i t).val) := by
    apply Set.Subset.antisymm
    · rintro y ⟨w,hw,rfl⟩
      rw [C.boundary_exhaustion] at hw
      rcases hw with hw | hw
      · left
        exact (Set.ext_iff.mp C.base_boundary_image _).mp ⟨⟨w,hw⟩,rfl⟩
      · right
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hw
        apply Set.mem_iUnion.mpr
        refine ⟨i,?_⟩
        rcases hi with ⟨t,rfl⟩ | ⟨t,rfl⟩ <;>
          exact ⟨t,congrArg Subtype.val (C.side_agrees _ _ _).symm⟩
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨w,hw⟩ := (Set.ext_iff.mp C.base_boundary_image y).mpr hy
        refine ⟨w.val,?_,hw⟩
        rw [C.boundary_exhaustion]
        exact Or.inl w.property
      · obtain ⟨i,⟨t,rfl⟩⟩ := Set.mem_iUnion.mp hy
        exact ⟨C.side i false t,C.side_boundary i false t,
          congrArg Subtype.val (C.side_agrees i false t)⟩

  -- Generic collar theorem for compact surfaces with boundary.  This is the
  -- first outstanding geometric construction, not an input to the public head.
  have hcollars :
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
    exact compact_surface_finite_disjoint_boundary_collars
  obtain ⟨k,H,hHembed,hHopen,hHcore,hHcover,hHdisjoint⟩ := hcollars C.Carrier
  have hHcore' : ∀ j t z, H j (t,z) ∈ C.core ↔ t ≠ 0 := by
    simpa only [C.core_eq_manifold_interior] using hHcore
  have hHcover' : C.coreᶜ = ⋃ j, Set.range (fun z => H j (0,z)) := by
    simpa only [C.core_eq_manifold_interior] using hHcover

  have hk : 0 < k := by
    have hb := C.side_boundary ⟨0,hn⟩ false 0
    rw [hHcover'] at hb
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hb
    exact Nat.zero_lt_of_lt j.isLt

  -- Capping-sensitive retention.  It quantifies actual embedded disks in S,
  -- rather than merely detecting nonstandard components of the cut surface.
  have hretained : ∃ j : Fin k,
      ¬ ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S),
        IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range (fun z => (C.projection (H j (⟨1/2,by norm_num⟩,z))).val) := by
    exact original_nonempty_at_most_three_essential_proper_arcs_cut_collar_disk_retention
      S g hg hS x R hR htarget n hn hn3 a hemb hend hinterior hpairwise hessential
      C k H hHembed hHopen hHcore' hHcover' hHdisjoint
  obtain ⟨j,hretained⟩ := hretained
  obtain ⟨E,hEprojection,hE,hEzero,hEpositive⟩ :=
    hproject S Q B F a C hF hFQ haF (H j) (hHopen j)
      (fun z => by simpa only [hHcore' j 0 z,ne_self_iff_false,not_false_eq_true])
      (fun t ht z => (hHcore' j t z).mpr (ne_of_gt ht.1))
  have hhalf : (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 := by norm_num
  have hlevel : IsEmbedding (fun z => E (⟨1/2,by norm_num⟩,z)) := by
    have hc : Continuous (fun z => E (⟨1/2,by norm_num⟩,z)) :=
      E.continuous.comp (continuous_const.prodMk continuous_id)
    apply (hc.isClosedEmbedding ?_).isEmbedding
    intro z w hzw
    have hh := hE.injective (a₁ := (⟨1/2,hhalf⟩,z)) (a₂ := (⟨1/2,hhalf⟩,w)) hzw
    exact congrArg Prod.snd hh
  let c : Curve S := ⟨fun z => E (⟨1/2,by norm_num⟩,z),hlevel⟩
  have hc : Essential c := by
    change ¬ ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S),
      IsEmbedding d ∧
      d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range (fun z => E (⟨1/2,by norm_num⟩,z))
    simpa only [hEprojection] using hretained
  exact ⟨E,hE,hEzero,hEpositive,⟨c,hc⟩,rfl⟩

