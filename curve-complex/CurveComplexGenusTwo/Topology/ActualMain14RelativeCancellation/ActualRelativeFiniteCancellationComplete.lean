import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.ActualRelativeBigonSelection
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeCancellationBookkeepingScaffolds
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualJordanDiskTools
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
import Mathlib.Analysis.Convex.Contractible
import CurveComplexGenusTwo.Filtration.Geometry.ActualPuncturedJordanConversion
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroRawSupportedCrosscutMove
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroDiskBigonChartProducer
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualFiniteInteriorAxisFraming
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedArcReverse
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroEmptyDiskCleanSides
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.NonloopPrefixParameters
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.NonloopPaddedRemainder
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.NonloopBaseVanishingTracks
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.NonloopClosedPieceDescent
import CurveComplexGenusTwo.Topology.IntersectionParity.EmptyDiskSidesStatement
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedTwoSideDisk
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingAfterClosedReplacement
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
import CurveComplexGenusTwo.Intersection.SphereRegionTransport
import CurveComplexGenusTwo.Foundations.PlanarDiscRecognition
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEssentialHalfBigonSubdisk
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.NonloopRetainedSupportingRegion
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.NonloopSupportingDisk
import CurveComplexGenusTwo.Topology.CapBandGeometry.CapSide
import CurveComplexGenusTwo.Topology.CapBandGeometry.DiskOpen
import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingSymmetry
import CurveComplexGenusTwo.Topology.ArcTrim.SupportedStrictDiskEnlargementStatement
import Mathlib.Topology.MetricSpace.Thickening
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualHalfBigonCornerOrientation
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem localized_marked_nonloop_empty_disk_produces_retained_supporting_region
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M)
    (hold : ∀ k, ¬ (actualArcLabels M).isLoop
      (Quotient.mk (essentialArcSetoid M) (old k)))
    (hd : ∀ k l, k ≠ l → Disjoint (arcInterior M (old k)) (arcInterior M (old l)))
    (a : EssentialMarkedArc M)
    (ha : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) a))
    (hfinite : ∀ k, (ArcSurgery.crossings M (old k) a).Finite ∧
      ∀ p ∈ ArcSurgery.crossings M (old k) a, ArcSurgery.CrossesInDisk M (old k) a p)
    (i : ι) (D : ActualMarkedTwoSideDisk M a (old i))
    (hlast : D.secondCorner ∉ M.cover.branch)
    (hempty : Disjoint D.openInterior (a.val.image ∪ ⋃ k, (old k).val.image))
    (hbaseB : D.firstCorner = (old i).val.map 0)
    (hbaseA : D.firstCorner = a.val.map 0)
    (U : Set S) (hU : IsOpen U) (hfixedU : (old i).val.image ⊆ U) :
    ∃ (α hi : ℝ) (g : C(Interval,S)) (Ω : Set S), 0 < α ∧ α < hi ∧ hi < 1 ∧
      range D.firstSide = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 α ∧
      IsEmbedding g ∧ g 0 = a.val.map 0 ∧
      g 1 = a.val.map (projIcc 0 1 zero_le_one hi) ∧
      (∀ k, Disjoint (range g) (arcInterior M (old k))) ∧
      range g ∩ a.val.image = {a.val.map 0,g 1} ∧
      g 1 ∉ M.cover.branch ∧
      (∀ t, t ≠ 0 → g t ∉ M.cover.branch) ∧
      Ω.Nonempty ∧ IsConnected Ω ∧
      Ω ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ ∧
      (∀ V : Set S, IsConnected V → Ω ⊆ V →
        V ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ → V=Ω) ∧
      frontier Ω = ((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g ∧
      Disjoint Ω (M.cover.branch : Set S) ∧ range g ⊆ U := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  letI : ClosedSurface S := {}
  have hclean : ∀ k, range D.firstSide ∩ (old k).val.image ⊆ {D.firstCorner,D.secondCorner} := by
    intro k p hp
    rcases hp with ⟨hpf,hpb⟩
    have hlocalempty : Disjoint D.openInterior (a.val.image ∪ (old k).val.image) :=
      hempty.mono_right (by intro z hz; rcases hz with hz | hz; exact Or.inl hz; exact Or.inr (mem_iUnion.mpr ⟨k,hz⟩))
    by_contra hpnot
    have hpBoundary' : p ∈ range D.disk := Set.image_subset_range _ _
      (D.boundary_eq.symm ▸ (show p ∈ range D.firstSide ∪ range D.secondSide from Or.inl hpf))
    have hnotmark : p ∉ M.cover.branch := fun hm => hpnot (D.marks_are_corners p hpBoundary' hm)
    have hpg : p ∉ Set.range D.secondSide := by
      intro h
      by_cases hk : k = i
      · subst k
        exact hpnot (D.sides_inter ▸ ⟨hpf,h⟩)
      · exact Set.disjoint_left.mp (hd k i hk) ⟨hpb,hnotmark⟩
          ⟨D.second_on_curve h,hnotmark⟩
    have hpab : p ∈ a.val.image ∩ (old k).val.image := ⟨D.first_on_curve hpf,hpb⟩
    obtain ⟨U,hU,hpU,hmarkfree,h,hpzero,hbaxis,haaxis⟩ := (hfinite k).2 p ⟨⟨hpab.2,hnotmark⟩,hpab.1,hnotmark⟩
    let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
    have hV : IsOpen V :=
      (isOpen_lt (continuous_fst.abs) continuous_const).inter
        (isOpen_lt (continuous_snd.abs) continuous_const)
    have haxes (z : S) (hz : z ∈ U) :
        (z ∈ a.val.image ↔ (h ⟨z,hz⟩).val.1 = 0) ∧
        (z ∈ (old k).val.image ↔ (h ⟨z,hz⟩).val.2 = 0) := ⟨haaxis ⟨z,hz⟩,hbaxis ⟨z,hz⟩⟩
    have hgclosed : IsClosed (Set.range D.secondSide) :=
      by simpa only [Set.image_univ] using (isCompact_univ.image D.secondSide.continuous).isClosed
    let N : Set U := {x | (x : S) ∉ Set.range D.secondSide}
    have hN : IsOpen N := hgclosed.isOpen_compl.preimage continuous_subtype_val
    let O : Set (ℝ × ℝ) := Subtype.val '' (h '' N)
    have hO : IsOpen O := (hV.isOpenEmbedding_subtypeVal).isOpenMap _ (h.isOpenMap _ hN)
    have hzeroO : (0,0) ∈ O := ⟨h ⟨p,hpU⟩, ⟨⟨p,hpU⟩,hpg,rfl⟩,hpzero⟩
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO (0,0) hzeroO
    have hpBoundary : p ∈ D.disk '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rw [D.boundary_eq]; exact Or.inl hpf
    obtain ⟨w, hw, hwp⟩ := hpBoundary
    have hwn : ‖w.val‖ = 1 := by
      simpa only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right] using hw
    let radial : C(Interval, Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      ⟨fun t => ⟨t.val • w.val, by
        simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg t.property.1, hwn, mul_one]
        exact t.property.2⟩, by fun_prop⟩
    have honecl : (1 : Interval) ∈ closure (Set.Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
      exact ⟨by norm_num,le_rfl⟩
    have hpcl : p ∈ closure D.openInterior := by
      have hcl : (D.disk ∘ radial) '' closure (Set.Ioo (0 : Interval) 1) ⊆
          closure ((D.disk ∘ radial) '' Set.Ioo (0 : Interval) 1) :=
        image_closure_subset_closure_image (D.disk.continuous.comp radial.continuous)
      have him : (D.disk ∘ radial) '' Set.Ioo (0 : Interval) 1 ⊆ D.openInterior := by
        rintro z ⟨t,ht,rfl⟩
        refine ⟨radial t, ?_, rfl⟩
        change t.val • w.val ∈ Metric.ball 0 1
        simp only [Metric.mem_ball,dist_zero_right]
        simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg t.property.1,hwn,mul_one] using (show t.val < (1 : ℝ) from ht.2)
      apply closure_mono him
      apply hcl
      refine ⟨1,honecl,?_⟩
      change D.disk (radial 1) = p
      have hr : radial 1 = w := by apply Subtype.ext; simp [radial]
      rw [hr]; exact hwp
    let T := Metric.ball (0 : ℝ × ℝ) ε
    have hTV : T ⊆ V := by
      intro z hz
      obtain ⟨v,hv,he⟩ := hball hz
      exact he ▸ v.property
    let jV : T → V := fun z => ⟨z.val,hTV z.property⟩
    let j : C(T,S) := ⟨fun z => (h.symm (jV z)).val, by fun_prop⟩
    have hjopen : IsOpenMap j := hU.isOpenMap_subtype_val.comp
      (h.symm.isOpenMap.comp (Metric.isOpen_ball.isOpenMap_subtype_val.subtype_mk _))
    let zeroT : T := ⟨0,by change dist (0 : ℝ × ℝ) 0 < ε; simpa only [dist_self] using hε⟩
    have hjzero : j zeroT = p := by
      have heq : jV zeroT = h ⟨p,hpU⟩ := by apply Subtype.ext; exact hpzero.symm
      change (h.symm (jV zeroT)).val = p
      rw [heq,h.symm_apply_apply]
    have hjN (z : T) : j z ∉ Set.range D.secondSide := by
      obtain ⟨v,⟨u,hu,he⟩,hv⟩ := hball z.property
      have heq : jV z = h u := by apply Subtype.ext; exact hv.symm.trans (congrArg Subtype.val he).symm
      change (h.symm (jV z)).val ∉ _
      rw [heq,h.symm_apply_apply]
      exact hu
    let K := Set.range D.disk
    let J : Set T := j ⁻¹' D.openInterior
    have hJopen : IsOpen J := (LocalSurgery.embedded_surface_disk_interior_isOpen D.disk D.disk_embedded).preimage j.continuous
    have hzeroJcl : zeroT ∈ closure J := by
      apply hjopen.preimage_closure_subset_closure_preimage
      change j zeroT ∈ closure D.openInterior
      rwa [hjzero]
    have hKclosed : IsClosed K := by
      simpa only [Set.image_univ] using (isCompact_univ.image D.disk.continuous).isClosed
    have haxis (z : T) (hz : j z ∈ K) (hznot : z ∉ J) : z.val.1 = 0 := by
      obtain ⟨v,hv⟩ := hz
      have hn : ‖v.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using v.property
      have hnnot : ¬ ‖v.val‖ < 1 := by
        intro hnlt
        apply hznot
        exact ⟨v,by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hnlt,hv⟩
      have hb : j z ∈ Set.range D.firstSide ∪ Set.range D.secondSide := by
        rw [← D.boundary_eq]
        exact ⟨v,by simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using
          le_antisymm hn (le_of_not_gt hnnot),hv⟩
      have ha : j z ∈ a.val.image := D.first_on_curve (hb.resolve_right (hjN z))
      have hh := (haxes (j z) (h.symm (jV z)).property).1.mp ha
      have heq : h ⟨j z,(h.symm (jV z)).property⟩ = jV z := h.apply_symm_apply _
      simpa only [heq] using hh
    obtain ⟨z,hzall,hzJ⟩ := mem_closure_iff_nhds.mp hzeroJcl Set.univ (by simp)
    have hzaxis : z.val.1 ≠ 0 := by
      intro hz0
      have ha : j z ∈ a.val.image := (haxes (j z) (h.symm (jV z)).property).1.mpr (by
        have heq : h ⟨j z,(h.symm (jV z)).property⟩ = jV z := h.apply_symm_apply _
        simpa only [heq] using hz0)
      exact Set.disjoint_left.mp hlocalempty hzJ (Or.inl ha)
    let σ : ℝ := z.val.1
    let H : Set T := {u | 0 < σ * u.val.1}
    have hzH : z ∈ H := by change 0 < z.val.1 * z.val.1; exact mul_self_pos.mpr hzaxis
    let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := σ • LinearMap.fst ℝ ℝ ℝ
    have hconv : Convex ℝ (T ∩ {u : ℝ × ℝ | 0 < σ * u.1}) :=
      (convex_ball (0 : ℝ × ℝ) ε).inter ((convex_Ioi (0 : ℝ)).linear_preimage L)
    have hHconn : IsPreconnected H := by
      apply IsInducing.subtypeVal.isPreconnected_image.mp
      have heq : Subtype.val '' H = T ∩ {u : ℝ × ℝ | 0 < σ * u.1} := by
        ext u
        constructor
        · rintro ⟨v,hv,rfl⟩; exact ⟨v.property,hv⟩
        · rintro ⟨hu,hv⟩; exact ⟨⟨u,hu⟩,hv,rfl⟩
      rw [heq]
      exact hconv.isPreconnected
    letI : PreconnectedSpace H := ⟨by
      apply IsInducing.subtypeVal.isPreconnected_image.mp
      simpa only [Set.image_univ,Subtype.range_val] using hHconn⟩
    let JH : Set H := Subtype.val ⁻¹' J
    have hJHeq : JH = (fun u : H => j u.val) ⁻¹' K := by
      ext u
      constructor
      · rintro ⟨v,hv,he⟩; exact ⟨v,he⟩
      · intro hu
        by_contra huJ
        have huaxis := haxis u.val hu huJ
        have hpos := u.property
        change 0 < σ * u.val.val.1 at hpos
        rw [huaxis,mul_zero] at hpos
        exact lt_irrefl 0 hpos
    have hJHclosed : IsClosed JH := by rw [hJHeq]; exact hKclosed.preimage (j.continuous.comp continuous_subtype_val)
    have hJHopen : IsOpen JH := hJopen.preimage continuous_subtype_val
    have hfull : JH = Set.univ := (show IsClopen JH from ⟨hJHclosed,hJHopen⟩).eq_univ
      ⟨⟨z,hzH⟩,hzJ⟩
    let e : T := ⟨(z.val.1,0),by
      have hzball := z.property
      change dist (z.val.1,0) (0 : ℝ × ℝ) < ε
      apply lt_of_le_of_lt ?_ hzball
      rw [Prod.dist_eq,Prod.dist_eq]
      change max (dist z.val.1 0) (dist (0 : ℝ) 0) ≤ max (dist z.val.1 0) (dist z.val.2 0)
      rw [dist_self]
      exact max_le_max le_rfl dist_nonneg⟩
    have heH : e ∈ H := by change 0 < z.val.1 * z.val.1; exact mul_self_pos.mpr hzaxis
    have heJ : e ∈ J := by
      have hm : (⟨e,heH⟩ : H) ∈ JH := hfull.symm ▸ Set.mem_univ _
      exact hm
    have heb : j e ∈ (old k).val.image := (haxes (j e) (h.symm (jV e)).property).2.mpr (by
      have heq : h ⟨j e,(h.symm (jV e)).property⟩ = jV e := h.apply_symm_apply _
      simpa only [heq] using (show e.val.2 = 0 from rfl))
    exact Set.disjoint_left.mp hlocalempty heJ (Or.inr heb)
  have hcorners : D.firstCorner ≠ D.secondCorner := by
    intro he
    have ht := D.first_embedded.injective (D.first_zero.trans (he.trans D.first_one.symm))
    exact (by norm_num : (0 : Interval) ≠ 1) ht
  have hlastCrossing : D.secondCorner ∈ ArcSurgery.crossings M (old i) a :=
    ⟨⟨D.second_on_curve ⟨1,D.second_one⟩,hlast⟩,
      D.first_on_curve ⟨1,D.first_one⟩,hlast⟩
  let Dswap : ActualMarkedTwoSideDisk M (old i) a :=
    { firstCorner := D.firstCorner, secondCorner := D.secondCorner
      firstSide := D.secondSide, secondSide := D.firstSide
      first_embedded := D.second_embedded, second_embedded := D.first_embedded
      first_zero := D.second_zero, first_one := D.second_one
      second_zero := D.first_zero, second_one := D.first_one
      first_on_curve := D.second_on_curve, second_on_curve := D.first_on_curve
      sides_inter := by simpa only [inter_comm] using D.sides_inter
      disk := D.disk, disk_embedded := D.disk_embedded
      boundary_eq := by simpa only [union_comm] using D.boundary_eq
      marks_are_corners := D.marks_are_corners }
  have hsecondClean : range D.secondSide ∩ a.val.image = {D.firstCorner,D.secondCorner} := by
    apply actual_empty_marked_bigon_first_side_clean M (old i) a
      (fun p hp => actual_marked_crossesInDisk_symm M (old i) a p ((hfinite i).2 p hp)) Dswap
    exact hempty.mono_right (by
      intro z hz
      rcases hz with hz | hz
      · exact Or.inr (mem_iUnion.mpr ⟨i,hz⟩)
      · exact Or.inl hz)
  have hfullDiskSource : range D.disk ∩ a.val.image = range D.firstSide := by
    apply Subset.antisymm
    · rintro z ⟨⟨v,hvz⟩,hza⟩
      have hn : ‖v.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using v.property
      have hnnot : ¬ ‖v.val‖ < 1 := by
        intro hlt
        exact Set.disjoint_left.mp hempty
          ⟨v,by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hlt,hvz⟩ (Or.inl hza)
      have hboundary : z ∈ range D.firstSide ∪ range D.secondSide :=
        D.boundary_eq ▸ ⟨v,by simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using le_antisymm hn (le_of_not_gt hnnot),hvz⟩
      rcases hboundary with hz | hz
      · exact hz
      · have hc : z ∈ ({D.firstCorner,D.secondCorner} : Set S) := hsecondClean ▸ ⟨hz,hza⟩
        rcases mem_insert_iff.mp hc with he | he
        · exact ⟨0,D.first_zero.trans he.symm⟩
        · exact ⟨1,D.first_one.trans (mem_singleton_iff.mp he).symm⟩
    · intro z hz
      have hb : z ∈ D.disk '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
        rw [D.boundary_eq]; exact Or.inl hz
      exact ⟨image_subset_range _ _ hb,D.first_on_curve hz⟩
  have hfamilyHalfTracks (hstart : D.secondCorner ≠ (old i).val.map 0)
      (hbase : D.firstCorner = (old i).val.map 0) :
      ∃ f : Bool → C(Interval,S), ∀ s,
        IsEmbedding (f s) ∧ f s 0 = D.firstCorner ∧
        range (f s) ∩ (M.cover.branch : Set S) = {D.firstCorner} ∧
        (∀ k, Disjoint (range (f s)) (arcInterior M (old k))) := by
    obtain ⟨β,hβ0,hβ1,hprefix,hlastParam⟩ :=
      actual_nonloop_marked_prefix_recovers_original_parameters M (old i) (hold i)
        D.secondSide D.second_embedded D.second_on_curve (D.second_zero.trans hbase) (D.second_one ▸ hlast)
    let P : Set S := (M.cover.branch : Set S) ∪ ⋃ k : {k : ι // k ≠ i}, (old k.val).val.image
    have hP : IsClosed P := M.cover.branch.isClosed.union
      (by simpa only [image_univ,MarkedArc.image] using
        (isCompact_iUnion (fun k : {k : ι // k ≠ i} =>
          isCompact_univ.image (old k.val).val.continuous)).isClosed)
    have hPbase : (old i).val.map 0 ∈ P := Or.inl (old i).val.start_marked
    have haxis : ∀ t : Interval, 0 < (t:ℝ) →
        (old i).val.map ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
          (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩ ∉ P := by
      intro t ht hp
      let u : Interval := ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
        (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩
      have hu0 : 0 < (u:ℝ) := mul_pos hβ0 ht
      have hu1 : (u:ℝ) < 1 :=
        lt_of_le_of_lt (mul_le_of_le_one_right hβ0.le t.property.2) hβ1
      have hnotmark : (old i).val.map u ∉ M.cover.branch := by
        intro hm
        rcases (old i).val.marked_only_at_ends u hm with he | he
        · have hh := congrArg Subtype.val he
          change (u:ℝ) = 0 at hh
          linarith
        · have hh := congrArg Subtype.val he
          change (u:ℝ) = 1 at hh
          linarith
      change (old i).val.map u ∈ P at hp
      rcases hp with hp | hp
      · exact hnotmark hp
      · obtain ⟨k,hk⟩ := mem_iUnion.mp hp
        exact Set.disjoint_left.mp (hd i k.val (Ne.symm k.property))
          ⟨mem_range_self u,hnotmark⟩ ⟨hk,hnotmark⟩
    obtain ⟨E,hE,hcenter,ρ,hρ,hρhalf,h,hh0,hbound,hpositive,hflat,
      f,hcoords,hf⟩ := actual_nonloop_prefix_produces_marked_base_vanishing_tracks
        M (old i) (hold i) β hβ0 hβ1 P hP hPbase haxis
    refine ⟨f,fun s => ⟨(hf s).1,(hf s).2.1.trans hbase.symm,?_,?_⟩⟩
    · apply Subset.antisymm
      · intro z hz
        have hzP : z ∈ range (f s) ∩ P := ⟨hz.1,Or.inl hz.2⟩
        have he : z = (old i).val.map 0 := mem_singleton_iff.mp ((hf s).2.2.1 ▸ hzP)
        exact mem_singleton_iff.mpr (he.trans hbase.symm)
      · intro z hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,(hf s).2.1.trans hbase.symm⟩,hbase.symm ▸ (old i).val.start_marked⟩
    · intro k
      apply Set.disjoint_left.mpr
      intro z hzf hzk
      by_cases hk : k = i
      · subst k
        have he : z = (old i).val.map 0 :=
          mem_singleton_iff.mp ((hf s).2.2.2 ▸ ⟨hzf,hzk.1⟩)
        exact hzk.2 (he.symm ▸ (old i).val.start_marked)
      · have hzP : z ∈ range (f s) ∩ P :=
          ⟨hzf,Or.inr (mem_iUnion.mpr ⟨⟨k,hk⟩,hzk.1⟩)⟩
        have he : z = (old i).val.map 0 := mem_singleton_iff.mp ((hf s).2.2.1 ▸ hzP)
        exact hzk.2 (he.symm ▸ (old i).val.start_marked)
  let K : Set S := ⋃ k, ArcSurgery.crossings M (old k) a
  have hK : K.Finite := Set.finite_iUnion (fun k => (hfinite k).1)
  have hKa : K ⊆ arcInterior M a := by
    intro z hz
    obtain ⟨k,hk⟩ := mem_iUnion.mp hz
    exact hk.2
  have hhalfPadding (hstart : D.firstCorner = a.val.map 0)
      (W : Set S) (hW : IsOpen W) (hcoreW : range D.firstSide ⊆ W) :
      ∃ (β hi : ℝ) (C R : Set S), 0 < β ∧ β < hi ∧ hi < 1 ∧
        range D.firstSide = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 β ∧
        C = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi ∧
        IsCompact C ∧ IsCompact R ∧ C ⊆ W ∧ a.val.image = C ∪ R ∧
        a.val.map 0 ∈ R ∧ a.val.map 1 ∈ R ∧
        range D.disk ∩ R = {a.val.map 0} ∧
        C ∩ K ⊆ range D.firstSide ∧ Disjoint (R ∩ K) C ∧
        (ArcSurgery.crossings M (old i) a ∩ C).Nonempty := by
    obtain ⟨β,hβ0,hβ1,hprefix,hlastParam⟩ :=
      actual_nonloop_marked_prefix_recovers_original_parameters M a ha
        D.firstSide D.first_embedded D.first_on_curve (D.first_zero.trans hstart) (D.first_one ▸ hlast)
    obtain ⟨hi,C,R,hβhi,hhi,hCeq,hC,hR,hCW,himage,hbase,hend,hDR,hCK,hRC⟩ :=
      actual_nonloop_initial_side_produces_padded_remainder M a ha β hβ0 hβ1
        K (range D.disk) W hK hKa hW (hprefix ▸ hcoreW)
        (hfullDiskSource.trans hprefix)
    refine ⟨β,hi,C,R,hβ0,hβhi,hhi,hprefix,hCeq,hC,hR,hCW,himage,hbase,hend,hDR,?_,hRC,?_⟩
    · exact hprefix.symm ▸ hCK
    · refine ⟨D.secondCorner,hlastCrossing,?_⟩
      rw [hCeq]
      refine ⟨β,⟨hβ0.le,hβhi.le⟩,?_⟩
      exact hlastParam.symm.trans D.first_one
  have hlastChart (W : Set S) (hW : IsOpen W) (hpW : D.secondCorner ∈ W) :
      ∃ F : OpenPartialHomeomorph S (ℝ × ℝ),
        D.secondCorner ∈ F.source ∧ F.source ⊆ W ∧ F D.secondCorner = (0,0) ∧
        (∀ x ∈ F.source, x ∈ a.val.image ↔ (F x).1 = 0) ∧
        (∀ x ∈ F.source, x ∈ (old i).val.image ↔ (F x).2 = 0) := by
    let p := D.secondCorner
    classical
    obtain ⟨U,hU,hpU,hmarkfree,e,hep,hbaxis,haaxis⟩ := (hfinite i).2 p hlastCrossing
    let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
    have hV : IsOpen V :=
      (isOpen_lt (continuous_fst.abs) continuous_const).inter
        (isOpen_lt (continuous_snd.abs) continuous_const)
    have : Nonempty U := ⟨⟨p,hpU⟩⟩
    let coeU : OpenPartialHomeomorph U S :=
      hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
    let f : U → ℝ × ℝ := fun u => (e u : ℝ × ℝ)
    have hf : IsOpenEmbedding f := hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
    let coeE : OpenPartialHomeomorph U (ℝ × ℝ) := hf.toOpenPartialHomeomorph f
    let E0 := coeU.symm.trans coeE
    have hE0source : E0.source = U := by
      simp [E0,coeU,coeE,
        IsOpenEmbedding.toOpenPartialHomeomorph_target]
    have hE0 (x : S) (hx : x ∈ U) : E0 x = (e ⟨x,hx⟩ : ℝ × ℝ) := by
      have hu : coeU.symm x = ⟨x,hx⟩ := by
        exact hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv (x := ⟨x,hx⟩)
      change f (coeU.symm x) = _
      rw [hu]
    let F := E0.restr W
    have hEs : F.source = U ∩ W := by
      simp [F,hW.interior_eq,hE0source]
    refine ⟨F,hEs.symm ▸ ⟨hpU,hpW⟩,?_,?_,?_,?_⟩
    · intro x hx
      exact (hEs.le hx).2
    · change E0 p = (0,0)
      exact (hE0 p hpU).trans hep
    · intro x hx
      change x ∈ a.val.image ↔ (E0 x).1 = 0
      rw [hE0 x (hEs.le hx).1]
      exact haaxis ⟨x,(hEs.le hx).1⟩
    · intro x hx
      change x ∈ (old i).val.image ↔ (E0 x).2 = 0
      rw [hE0 x (hEs.le hx).1]
      exact hbaxis ⟨x,(hEs.le hx).1⟩
  have hbaseNormalizes (c : EssentialMarkedArc M)
      (hcorner : D.firstCorner ∈ c.val.image) (hmark : D.firstCorner ∈ M.cover.branch) :
      ∃ c' : EssentialMarkedArc M,
        c'.val.image = c.val.image ∧
        Quotient.mk (essentialArcSetoid M) c' = Quotient.mk (essentialArcSetoid M) c ∧
        c'.val.map 0 = D.firstCorner := by
    obtain ⟨t,ht⟩ := hcorner
    rcases c.val.marked_only_at_ends t (ht.symm ▸ hmark) with he | he
    · subst t
      exact ⟨c,rfl,rfl,ht⟩
    · subst t
      exact ⟨c.reverse,c.reverse_image,c.reverse_class,by simpa using ht⟩
  let Other : Set S := ⋃ k : {k : ι // k ≠ i}, (old k.val).val.image
  have hOtherClosed : IsClosed Other := by
    simpa only [Other,image_univ,MarkedArc.image] using
      (isCompact_iUnion (fun k : {k : ι // k ≠ i} =>
        isCompact_univ.image (old k.val).val.continuous)).isClosed
  have hlastNotOther : D.secondCorner ∉ Other := by
    intro hp
    obtain ⟨k,hk⟩ := mem_iUnion.mp hp
    exact Set.disjoint_left.mp (hd i k.val (Ne.symm k.property))
      hlastCrossing.1 ⟨hk,hlast⟩
  obtain ⟨F,hpF,hFfree,hFzero,haF,hbF⟩ := hlastChart
    (((M.cover.branch : Set S) ∪ Other)ᶜ)
    (M.cover.branch.isClosed.union hOtherClosed).isOpen_compl
    (by simpa only [mem_compl_iff,mem_union,not_or,Finset.mem_coe] using And.intro hlast hlastNotOther)
  let L : (ℝ × ℝ) ≃ₜ Schoenflies.Plane := {
    toEquiv := {
      toFun := fun z => Schoenflies.Plane.mk z.1 z.2
      invFun := fun z => (z 0,z 1)
      left_inv := by intro z; apply Prod.ext <;> rfl
      right_inv := by intro z; ext j; fin_cases j <;> rfl }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let G : OpenPartialHomeomorph S Schoenflies.Plane := F.trans L.toOpenPartialHomeomorph
  have hGs : G.source = F.source := by simp [G]
  have hGcoord (x : S) : G x = Schoenflies.Plane.mk (F x).1 (F x).2 := rfl
  have hGzero : G D.secondCorner = 0 := by
    rw [hGcoord,hFzero]
    ext j; fin_cases j <;> rfl
  have hframedStrip (hbase : D.firstCorner = (old i).val.map 0) :
      ∃ (β : ℝ) (N : Interval × Icc (-1:ℝ) 1 → S),
        0 < β ∧ β < 1 ∧
        range D.secondSide = ((old i).val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 β ∧
        (old i).val.map (projIcc 0 1 zero_le_one β) = D.secondCorner ∧ range N ⊆ U ∧ IsEmbedding N ∧
        (∀ u, N (u,⟨0,by norm_num⟩) = (old i).val.map u) ∧
        (∃ σ δ η : ℝ, (σ = -1 ∨ σ = 1) ∧ 0 < δ ∧ 0 < η ∧
          ∀ (u : Interval) (w : Icc (-1:ℝ) 1), |(u:ℝ)-β| < η →
            N (u,w) ∈ G.source ∧
            G (N (u,w)) = Schoenflies.Plane.mk (G ((old i).val.map u) 0) (σ*δ*(w:ℝ))) := by
    obtain ⟨β,hβ0,hβ1,hprefix,hlastParam⟩ :=
      actual_nonloop_marked_prefix_recovers_original_parameters M (old i) (hold i)
        D.secondSide D.second_embedded D.second_on_curve (D.second_zero.trans hbase) (D.second_one ▸ hlast)
    let b : C(Interval,S) := ⟨(old i).val.map,(old i).val.continuous⟩
    have hb : IsEmbedding b := ((old i).val.continuous.isClosedEmbedding
      (NonLoopArc.injective ⟨(old i).val,actualRepresentative_nonloop M (old i) (hold i)⟩)).isEmbedding
    let θ : Unit → Interval := fun _ => ⟨β,hβ0.le,hβ1.le⟩
    have hθ : Function.Injective θ := fun x y _ => Subsingleton.elim x y
    have hθq : b (θ ()) = D.secondCorner := by
      have hh := hlastParam.symm.trans D.second_one
      simpa only [b,θ,ContinuousMap.coe_mk,projIcc_of_mem zero_le_one ⟨hβ0.le,hβ1.le⟩] using hh
    obtain ⟨N,hN,hNU,hcenter,σ,δ,η,hsign,hpos,hcoords⟩ :=
      CurveComplex.source_finite_interior_axis_framed_arc_strip S b hb Unit θ hθ
        (fun _ => ⟨hβ0,hβ1⟩) (fun _ => G)
        (fun _ => by rw [show b (θ ()) = D.secondCorner from hθq,hGs]; exact hpF)
        (fun _ => by rw [show b (θ ()) = D.secondCorner from hθq]; exact hGzero)
        (fun _ u hu => by
          rw [hGcoord]
          exact (hbF (b u) (hGs ▸ hu)).mp (mem_range_self u))
        U hU hfixedU
    exact ⟨β,N,hβ0,hβ1,hprefix,hlastParam.symm.trans D.second_one,hNU,hN,hcenter,σ (),δ (),η (),hsign (),
      (hpos ()).1,(hpos ()).2,hcoords ()⟩
  have htracksFromChosenStrip (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
      (N : Interval × Icc (-1:ℝ) 1 → S) (hN : IsEmbedding N)
      (hcenter : ∀ t, N (t,⟨0,by norm_num⟩)=(old i).val.map t)
      (P : Set S) (hP : IsClosed P) (hbase : (old i).val.map 0 ∈ P)
      (haxis : ∀ t : Interval, 0 < (t:ℝ) →
        (old i).val.map ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
          (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩ ∉ P) :
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/2 ∧
      ∃ h : C(Interval,ℝ), h 0=0 ∧
        (∀ t, 0 ≤ h t ∧ h t ≤ ρ) ∧
        (∀ t : Interval, 0 < (t:ℝ) → 0 < h t) ∧
        (∀ t : Interval, (1/2:ℝ) ≤ (t:ℝ) → h t=ρ) ∧
      ∃ f : Bool → C(Interval,S),
        (∀ s t, ∃ v : Icc (-1:ℝ) 1,
          (v:ℝ)=(if s then (1:ℝ) else -1)*h t ∧
          f s t=N (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩,v)) ∧
      (∀ s,
        IsEmbedding (f s) ∧ f s 0=(old i).val.map 0 ∧
        range (f s) ∩ P={(old i).val.map 0} ∧
        range (f s) ∩ (old i).val.image={(old i).val.map 0}) ∧
      (∀ (t : Interval) (v : Icc (-1:ℝ) 1), 0 < (t:ℝ) → |(v:ℝ)| ≤ h t →
        N (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
          (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩,v) ∉ P) := by
    let Z := Interval × Icc (-1:ℝ) 1
    let X : Interval → Z := fun t =>
      (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
        (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩,⟨0,by norm_num⟩)
    have hX : Continuous X := by dsimp [X]; fun_prop
    let F : Set Z := N ⁻¹' P
    have hF : IsClosed F := hP.preimage hN.continuous
    have hzeroE : N (X 0)=(old i).val.map 0 := by
      have hx : X 0=(0,⟨0,by norm_num⟩) := by
        apply Prod.ext
        · apply Subtype.ext; simp [X]
        · rfl
      rw [hx,hcenter]
    have hzeroF : X 0 ∈ F := by
      change N (X 0) ∈ P
      rw [hzeroE]
      exact hbase
    have hFne : F.Nonempty := ⟨X 0,hzeroF⟩
    have haxisF (t : Interval) (ht : 0 < (t:ℝ)) : X t ∉ F := by
      change N (X t) ∉ P
      rw [hcenter]
      exact haxis t ht
    let d : Interval → ℝ := fun t => Metric.infDist (X t) F / 4
    have hd : Continuous d := ((Metric.continuous_infDist_pt F).comp hX).div_const 4
    have hdpos (t : Interval) (ht : 0 < (t:ℝ)) : 0 < d t :=
      div_pos ((hF.notMem_iff_infDist_pos hFne).mp (haxisF t ht)) (by norm_num)
    let T : Set Interval := {t | (1/2:ℝ) ≤ (t:ℝ)}
    have hT : IsCompact T := (isClosed_le continuous_const continuous_subtype_val).isCompact
    obtain ⟨δ,hδ,hδd⟩ := hT.exists_forall_le' hd.continuousOn
      (fun t ht => hdpos t (lt_of_lt_of_le (by norm_num) ht))
    let ρ := min δ (1/2)
    have hρ : 0 < ρ := lt_min hδ (by norm_num)
    have hρδ : ρ ≤ δ := min_le_left _ _
    have hρhalf : ρ ≤ 1/2 := min_le_right _ _
    let h : C(Interval,ℝ) := ⟨fun t => min ρ (d t),continuous_const.min hd⟩
    have hn (t : Interval) : 0 ≤ h t :=
      le_min hρ.le (div_nonneg Metric.infDist_nonneg (by norm_num))
    have hb (t : Interval) : h t ≤ ρ := min_le_left _ _
    have hp (t : Interval) (ht : 0 < (t:ℝ)) : 0 < h t := lt_min hρ (hdpos t ht)
    have hzero : h 0=0 := by
      change min ρ (Metric.infDist (X 0) F / 4)=0
      rw [Metric.infDist_zero_of_mem hzeroF,zero_div,min_eq_right hρ.le]
    have htail (t : Interval) (ht : (1/2:ℝ) ≤ (t:ℝ)) : h t=ρ :=
      min_eq_left (hρδ.trans (hδd t ht))
    let sign : Bool → ℝ := fun s => if s then 1 else -1
    have hsign (s : Bool) : |sign s|=1 := by cases s <;> norm_num [sign]
    let Y : Bool → Interval → Z := fun s t =>
      ((X t).1,⟨sign s*h t,abs_le.mp (by
        rw [abs_mul,hsign,one_mul,abs_of_nonneg (hn t)]
        exact (hb t).trans (hρhalf.trans (by norm_num)))⟩)
    have hY (s : Bool) : Continuous (Y s) := by dsimp [Y,sign,X]; fun_prop
    let f : Bool → C(Interval,S) := fun s => ⟨N ∘ Y s,hN.continuous.comp (hY s)⟩
    have f0 (s : Bool) : f s 0=(old i).val.map 0 := by
      have hy : Y s 0=X 0 := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext; change sign s*h 0=0; rw [hzero,mul_zero]
      change N (Y s 0)=_
      rw [hy,hzeroE]
    have hdist (s : Bool) (t : Interval) : dist (X t) (Y s t)=h t := by
      rw [Prod.dist_eq]
      simp only [Y,Subtype.dist_eq,Real.dist_eq,sub_self,abs_zero,zero_sub,
        abs_neg,abs_mul,hsign,one_mul,abs_of_nonneg (hn t),max_eq_right (hn t)]
      change max 0 |(0:ℝ)-sign s*h t|=h t
      simp only [zero_sub,abs_neg,abs_mul,hsign,one_mul,abs_of_nonneg (hn t),
        max_eq_right (hn t)]
    have hYP (s : Bool) (t : Interval) (ht : 0 < (t:ℝ)) : Y s t ∉ F := by
      apply Metric.notMem_of_dist_lt_infDist
      rw [hdist]
      have hsmall : h t ≤ Metric.infDist (X t) F / 4 := min_le_right _ _
      have hpositive : 0 < Metric.infDist (X t) F :=
        (hF.notMem_iff_infDist_pos hFne).mp (haxisF t ht)
      linarith
    have hband (t : Interval) (v : Icc (-1:ℝ) 1) (ht : 0 < (t:ℝ)) (hv : |(v:ℝ)| ≤ h t) :
        N ((X t).1,v) ∉ P := by
      change ((X t).1,v) ∉ F
      apply Metric.notMem_of_dist_lt_infDist
      have hdistv : dist (X t) ((X t).1,v) = |(v:ℝ)| := by
        rw [Prod.dist_eq]
        simp only [X,Subtype.dist_eq,Real.dist_eq,sub_self,abs_zero,zero_sub,abs_neg]
        exact max_eq_right (abs_nonneg _)
      rw [hdistv]
      have hsmall : h t ≤ Metric.infDist (X t) F / 4 := min_le_right _ _
      have hpositive : 0 < Metric.infDist (X t) F :=
        (hF.notMem_iff_infDist_pos hFne).mp (haxisF t ht)
      linarith
    refine ⟨ρ,hρ,hρhalf,h,hzero,fun t => ⟨hn t,hb t⟩,hp,htail,f,fun s t => ⟨(Y s t).2,rfl,rfl⟩,?_,hband⟩
    intro s
    have hfinj : Function.Injective (f s) := by
      intro t u he
      have hh := congrArg (fun z : Z => (z.1:ℝ)) (hN.injective he)
      change β*(t:ℝ)=β*(u:ℝ) at hh
      exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hβ0) hh)
    refine ⟨((f s).continuous.isClosedEmbedding hfinj).isEmbedding,f0 s,?_,?_⟩
    · ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,htP⟩
        have ht : t=0 := by
          apply Subtype.ext
          change (t:ℝ)=0
          by_contra hne
          exact hYP s t (lt_of_le_of_ne t.property.1 (Ne.symm hne)) htP
        rw [ht,f0 s]
        exact mem_singleton _
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,f0 s⟩,hbase⟩
    · ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,⟨u,hu⟩⟩
        have he : Y s t=(u,⟨0,by norm_num⟩) :=
          hN.injective (hu.symm.trans (hcenter u).symm)
        have hy : sign s*h t=0 := congrArg (fun q : Z => (q.2:ℝ)) he
        have ht : t=0 := by
          apply Subtype.ext
          change (t:ℝ)=0
          by_contra hne
          have htp := hp t (lt_of_le_of_ne t.property.1 (Ne.symm hne))
          cases s <;> norm_num [sign,ne_of_gt htp] at hy
        rw [ht,f0 s]
        exact mem_singleton _
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,f0 s⟩,mem_range_self _⟩
  have hsmallFramedSupport (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
      (N : Interval × Icc (-1:ℝ) 1 → S) (hN : IsEmbedding N)
      (hcenter : ∀ u, N (u,⟨0,by norm_num⟩)=(old i).val.map u)
      (hβq : (old i).val.map ⟨β,hβ0.le,hβ1.le⟩ = D.secondCorner)
      (η : ℝ) (hη : 0 < η) :
      ∃ T : Set S, IsOpen T ∧ D.secondCorner ∈ T ∧ T ⊆ G.source ∧
        ∀ z, N z ∈ T → |(z.1:ℝ)-β| < η := by
    let Z := Interval × Icc (-1:ℝ) 1
    let A : Set Z := {z | η ≤ |(z.1:ℝ)-β|}
    have hc : Continuous (fun z : Z => |(z.1:ℝ)-β|) := by
      change Continuous (fun z : Interval × Icc (-1:ℝ) 1 => |(z.1:ℝ)-β|)
      fun_prop
    have hA : IsClosed A := isClosed_le continuous_const hc
    have hAc : IsCompact A := hA.isCompact
    have hqnot : D.secondCorner ∉ N '' A := by
      rintro ⟨z,hz,he⟩
      have hneq : z = (⟨β,hβ0.le,hβ1.le⟩,⟨0,by norm_num⟩) :=
        hN.injective (he.trans (hβq.symm.trans (hcenter _).symm))
      have hh : η ≤ 0 := by
        change η ≤ |(z.1:ℝ)-β| at hz
        rw [hneq] at hz
        change η ≤ |β-β| at hz
        simpa only [sub_self,abs_zero] using hz
      exact (not_le_of_gt hη) hh
    let T : Set S := G.source ∩ (N '' A)ᶜ
    refine ⟨T,G.open_source.inter (hAc.image hN.continuous).isClosed.isOpen_compl,
      ⟨hGs.symm ▸ hpF,hqnot⟩,inter_subset_left,?_⟩
    intro z hz
    by_contra hnot
    exact hz.2 ⟨z,le_of_not_gt hnot,rfl⟩
  have hsourceStraddling (hstart : D.firstCorner = a.val.map 0)
      (r : C(Interval,S)) (hr : IsEmbedding r) (hon : range r ⊆ a.val.image)
      (hmid : r ⟨1/2,by constructor <;> norm_num⟩ = D.secondCorner) :
      ∃ b : Bool, (if b then r 1 else r 0) ∉ range D.firstSide := by
    obtain ⟨α,hα0,hα1,hprefix,hαq⟩ :=
      actual_nonloop_marked_prefix_recovers_original_parameters M a ha D.firstSide
        D.first_embedded D.first_on_curve (D.first_zero.trans hstart) (D.first_one ▸ hlast)
    have hainj := NonLoopArc.injective ⟨a.val,actualRepresentative_nonloop M a ha⟩
    let A : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
    have hA : IsEmbedding A := (a.val.continuous.isClosedEmbedding hainj).isEmbedding
    let q : Interval → Interval := fun t => hA.toHomeomorph.symm ⟨r t,hon (mem_range_self t)⟩
    have hq : Continuous q := hA.toHomeomorph.symm.continuous.comp (r.continuous.subtype_mk _)
    have hqmap (t : Interval) : a.val.map (q t) = r t :=
      congrArg Subtype.val (hA.toHomeomorph.apply_symm_apply ⟨r t,hon (mem_range_self t)⟩)
    have hqi : Function.Injective q := by
      intro t u he
      exact hr.injective ((hqmap t).symm.trans ((congrArg a.val.map he).trans (hqmap u)))
    let mid : Interval := ⟨1/2,by constructor <;> norm_num⟩
    have hqm : q mid = ⟨α,hα0.le,hα1.le⟩ := by
      apply hainj
      rw [hqmap,hmid]
      have hh := hαq.symm.trans D.first_one
      simpa only [projIcc_of_mem zero_le_one ⟨hα0.le,hα1.le⟩] using hh.symm
    have hsidebound (t : Interval) (ht : r t ∈ range D.firstSide) : (q t:ℝ) ≤ α := by
      rw [hprefix] at ht
      obtain ⟨u,hu,he⟩ := ht
      have hui : u ∈ Icc (0:ℝ) 1 := ⟨hu.1,hu.2.trans hα1.le⟩
      have hqu : q t = projIcc 0 1 zero_le_one u := hainj ((hqmap t).trans he.symm)
      rw [hqu,projIcc_of_mem zero_le_one hui]
      exact hu.2
    rcases hq.strictMono_of_inj_boundedOrder' hqi with hm | hm
    · refine ⟨true,?_⟩
      intro ht
      have hh := hm (by change (1/2:ℝ) < 1; norm_num : mid < 1)
      rw [hqm] at hh
      exact (not_lt_of_ge (hsidebound 1 ht)) hh
    · refine ⟨false,?_⟩
      intro ht
      have hh := hm (by change (0:ℝ) < 1/2; norm_num : 0 < mid)
      rw [hqm] at hh
      exact (not_lt_of_ge (hsidebound 0 ht)) hh
  have hretainedPortParameters (hstart : D.firstCorner = a.val.map 0)
      (z : S) (hzA : z ∈ a.val.image) (hzmark : z ∉ M.cover.branch)
      (hzSide : z ∉ range D.firstSide) :
      ∃ α hi : ℝ, 0 < α ∧ α < hi ∧ hi < 1 ∧
        range D.firstSide = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 α ∧
        z = a.val.map (projIcc 0 1 zero_le_one hi) ∧
        D.secondCorner = a.val.map (projIcc 0 1 zero_le_one α) := by
    obtain ⟨α,hα0,hα1,hprefix,hαq⟩ :=
      actual_nonloop_marked_prefix_recovers_original_parameters M a ha D.firstSide
        D.first_embedded D.first_on_curve (D.first_zero.trans hstart) (D.first_one ▸ hlast)
    obtain ⟨t,ht⟩ := hzA
    have ht1 : (t:ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
      intro he
      have hte : t = 1 := Subtype.ext he
      exact hzmark (ht.symm ▸ (hte.symm ▸ a.val.end_marked)))
    have hαt : α < (t:ℝ) := by
      by_contra hn
      apply hzSide
      rw [hprefix]
      exact ⟨(t:ℝ),⟨t.property.1,le_of_not_gt hn⟩,
        by simpa only [Function.comp_apply,projIcc_of_mem zero_le_one t.property] using ht⟩
    exact ⟨α,(t:ℝ),hα0,hαt,ht1,hprefix,
      (by simpa only [projIcc_of_mem zero_le_one t.property] using ht.symm),
      D.first_one.symm.trans hαq⟩
  have hordinaryParameters (b : EssentialMarkedArc M)
      (hb : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) b))
      (f : C(Interval,S)) (hf : IsEmbedding f) (hon : range f ⊆ b.val.image)
      (h0 : f 0 ∉ M.cover.branch) (h1 : f 1 ∉ M.cover.branch) :
      ∃ α β : Interval, α ≠ β ∧ 0 < (α:ℝ) ∧ (α:ℝ) < 1 ∧
        0 < (β:ℝ) ∧ (β:ℝ) < 1 ∧
        f 0 = b.val.map α ∧ f 1 = b.val.map β ∧
        range f = b.val.map '' uIcc α β := by
    have hinj := NonLoopArc.injective ⟨b.val,actualRepresentative_nonloop M b hb⟩
    let A : C(Interval,S) := ⟨b.val.map,b.val.continuous⟩
    have hA : IsEmbedding A := (b.val.continuous.isClosedEmbedding hinj).isEmbedding
    let q : Interval → Interval := fun t => hA.toHomeomorph.symm ⟨f t,hon (mem_range_self t)⟩
    have hq : Continuous q := hA.toHomeomorph.symm.continuous.comp (f.continuous.subtype_mk _)
    have hqmap (t : Interval) : b.val.map (q t) = f t :=
      congrArg Subtype.val (hA.toHomeomorph.apply_symm_apply ⟨f t,hon (mem_range_self t)⟩)
    have hqi : Function.Injective q := by
      intro t u he
      exact hf.injective ((hqmap t).symm.trans ((congrArg b.val.map he).trans (hqmap u)))
    have hinside (t : Interval) (hm : f t ∉ M.cover.branch) :
        0 < (q t:ℝ) ∧ (q t:ℝ) < 1 := by
      constructor
      · apply lt_of_le_of_ne (q t).property.1
        intro he
        have heq : q t = 0 := Subtype.ext he.symm
        exact hm ((hqmap t) ▸ (heq.symm ▸ b.val.start_marked))
      · apply lt_of_le_of_ne (q t).property.2
        intro he
        have heq : q t = 1 := Subtype.ext he
        exact hm ((hqmap t) ▸ (heq.symm ▸ b.val.end_marked))
    have hwhole : Icc (0:Interval) 1 = univ := Set.eq_univ_of_forall (fun t => t.property)
    have hqr : range q = uIcc (q 0) (q 1) := by
      rw [← image_univ,← hwhole]
      rcases hq.strictMono_of_inj_boundedOrder' hqi with hm | hm
      · rw [hq.continuousOn.image_Icc_of_monotoneOn (show (0:Interval) ≤ 1 from by norm_num) (hm.monotone.monotoneOn _)]
        exact (uIcc_of_le (hm.monotone (by norm_num))).symm
      · rw [hq.continuousOn.image_Icc_of_antitoneOn (show (0:Interval) ≤ 1 from by norm_num) (hm.antitone.antitoneOn _)]
        exact (uIcc_of_ge (hm.antitone (by norm_num))).symm
    refine ⟨q 0,q 1,(fun he => (by norm_num : (0:Interval) ≠ 1) (hqi he)),
      (hinside 0 h0).1,(hinside 0 h0).2,(hinside 1 h1).1,(hinside 1 h1).2,
      (hqmap 0).symm,(hqmap 1).symm,?_⟩
    rw [← hqr,← range_comp]
    exact congrArg range (funext (fun t => (hqmap t).symm))
  have hactualDiskSideHomotopy :
      ∃ (hp : D.firstCorner ∈ ((M.cover.branch : Set S) \ {D.firstCorner})ᶜ)
        (hq : D.secondCorner ∈ ((M.cover.branch : Set S) \ {D.firstCorner})ᶜ),
      ∃ α β : Path (⟨D.firstCorner,hp⟩ : ↑(((M.cover.branch : Set S) \ {D.firstCorner})ᶜ)) ⟨D.secondCorner,hq⟩,
        (∀ t, (α t : S)=D.firstSide t) ∧ (∀ t, (β t : S)=D.secondSide t) ∧ α.Homotopic β := by
    let X : Set S := ((M.cover.branch : Set S) \ {D.firstCorner})ᶜ
    let K := Metric.closedBall (0 : Plane) 1
    have hX (y : S) (hy : y ∈ range D.disk) : y ∈ X := by
      rintro ⟨hym,hyne⟩
      have hym' : y ∈ M.cover.branch := hym
      rcases mem_insert_iff.mp (D.marks_are_corners y hy hym') with he | he
      · exact hyne he
      · exact hlast ((mem_singleton_iff.mp he) ▸ hym')
    have hp : D.firstCorner ∈ X := by simp [X]
    have hq : D.secondCorner ∈ X := by
      intro hy
      exact hlast hy.1
    let F : C(K,X) := ⟨fun x => ⟨D.disk x,hX _ (mem_range_self x)⟩,
      D.disk.continuous.subtype_mk _⟩
    have hfirst (t : Interval) : D.firstSide t ∈ range D.disk := by
      apply image_subset_range D.disk _
      rw [D.boundary_eq]; exact Or.inl (mem_range_self t)
    have hsecond (t : Interval) : D.secondSide t ∈ range D.disk := by
      apply image_subset_range D.disk _
      rw [D.boundary_eq]; exact Or.inr (mem_range_self t)
    let e := D.disk_embedded.toHomeomorph
    let f : C(Interval,K) := ⟨fun t => e.symm ⟨D.firstSide t,hfirst t⟩,
      e.symm.continuous.comp (D.firstSide.continuous.subtype_mk _)⟩
    let g : C(Interval,K) := ⟨fun t => e.symm ⟨D.secondSide t,hsecond t⟩,
      e.symm.continuous.comp (D.secondSide.continuous.subtype_mk _)⟩
    have hf (t : Interval) : D.disk (f t)=D.firstSide t :=
      congrArg Subtype.val (e.apply_symm_apply ⟨D.firstSide t,hfirst t⟩)
    have hg (t : Interval) : D.disk (g t)=D.secondSide t :=
      congrArg Subtype.val (e.apply_symm_apply ⟨D.secondSide t,hsecond t⟩)
    let α₀ : Path (f 0) (f 1) := ⟨f,rfl,rfl⟩
    let β₀ : Path (f 0) (f 1) := ⟨g,
      D.disk_embedded.injective ((hg 0).trans (D.second_zero.trans (D.first_zero.symm.trans (hf 0).symm))),
      D.disk_embedded.injective ((hg 1).trans (D.second_one.trans (D.first_one.symm.trans (hf 1).symm)))⟩
    letI : ContractibleSpace K := (convex_closedBall (0 : Plane) 1).contractibleSpace ⟨0,by simp⟩
    have hhom := (SimplyConnectedSpace.paths_homotopic α₀ β₀).map F
    have hsource : (⟨D.firstCorner,hp⟩ : X)=F (f 0) :=
      Subtype.ext ((hf 0).trans D.first_zero).symm
    have htarget : (⟨D.secondCorner,hq⟩ : X)=F (f 1) :=
      Subtype.ext ((hf 1).trans D.first_one).symm
    refine ⟨hp,hq,(α₀.map F.continuous).cast hsource htarget,
      (β₀.map F.continuous).cast hsource htarget,?_,?_,hhom.pathCast hsource htarget⟩
    · exact hf
    · exact hg
  have hactualStripBandMap (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
      (N : Interval × Icc (-1:ℝ) 1 → S) (hN : IsEmbedding N)
      (hcenter : ∀ t, N (t,⟨0,by norm_num⟩)=(old i).val.map t)
      (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
      (h : C(Interval,ℝ)) (hh0 : h 0=0) (hh1 : h 1=ρ)
      (hbound : ∀ t, 0 ≤ h t ∧ h t ≤ ρ)
      (P : Set S) (hmarks : (M.cover.branch : Set S) ⊆ P)
      (hband : ∀ (t : Interval) (v : Icc (-1:ℝ) 1), 0 < (t:ℝ) → |(v:ℝ)| ≤ h t →
        N (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
          (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩,v) ∉ P)
      (s : Bool) :
      ∃ F : C(Interval × Interval,↥(((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)),
        (∀ (t : Interval), (F (t,0):S)=(old i).val.map
          ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩) ∧
        (∀ (w : Interval), (F (0,w):S)=(old i).val.map 0) ∧
        ∀ (t w : Interval), ∃ v : Icc (-1:ℝ) 1,
          (v:ℝ)=(if s then (1:ℝ) else -1)*h t*(w:ℝ) ∧
          (F (t,w):S)=N (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩,v) := by
    let sign : ℝ := if s then 1 else -1
    have habs : |sign|=1 := by cases s <;> norm_num [sign]
    let v : Interval × Interval → Icc (-1:ℝ) 1 := fun x => ⟨sign*h x.1*(x.2:ℝ),by
      apply abs_le.mp
      rw [abs_mul,abs_mul,habs,one_mul,abs_of_nonneg (hbound x.1).1,abs_of_nonneg x.2.property.1]
      have hh : h x.1*(x.2:ℝ) ≤ h x.1 := mul_le_of_le_one_right (hbound x.1).1 x.2.property.2
      exact hh.trans ((hbound x.1).2.trans (hρhalf.trans (by norm_num)))⟩
    let L : Interval × Interval → Interval × Icc (-1:ℝ) 1 := fun x =>
      (⟨β*(x.1:ℝ),⟨mul_nonneg hβ0.le x.1.property.1,
        (mul_le_of_le_one_right hβ0.le x.1.property.2).trans hβ1.le⟩⟩,v x)
    have hL : Continuous L := by dsimp [L,v]; fun_prop
    have hvbound (t w : Interval) : |(v (t,w):ℝ)| ≤ h t := by
      change |sign*h t*(w:ℝ)| ≤ h t
      rw [abs_mul,abs_mul,habs,one_mul,abs_of_nonneg (hbound t).1,abs_of_nonneg w.property.1]
      exact mul_le_of_le_one_right (hbound t).1 w.property.2
    have hbase (w : Interval) : N (L (0,w))=(old i).val.map 0 := by
      have hL0 : L (0,w)=(0,⟨0,by norm_num⟩) := by
        apply Prod.ext
        · apply Subtype.ext; dsimp [L]; norm_num
        · apply Subtype.ext; dsimp [L,v]; rw [hh0]; simp
      rw [hL0,hcenter]
    have hX (x : Interval × Interval) : N (L x) ∈ (((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ) := by
      by_cases hx : x.1=0
      · have he := hbase x.2
        rw [show L x=L (0,x.2) from congrArg L (Prod.ext hx rfl),he]
        simp
      · intro hm
        exact hband x.1 (v x) (lt_of_le_of_ne x.1.property.1 (Ne.symm (by intro he; exact hx (Subtype.ext he))))
          (hvbound _ _) (hmarks hm.1)
    let F : C(Interval × Interval,↥(((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)) :=
      ⟨fun x => ⟨N (L x),hX x⟩,(hN.continuous.comp hL).subtype_mk _⟩
    refine ⟨F,?_,hbase,fun t w => ⟨v (t,w),rfl,rfl⟩⟩
    intro t
    have hv0 : v (t,0)=⟨0,by norm_num⟩ := by apply Subtype.ext; dsimp [v]; simp
    change N (L (t,0)) = _
    dsimp only [L]
    rw [hv0,hcenter]
  have hSquareBoundaryHomotopy {Y : Type} [TopologicalSpace Y]
      (F : C(Interval × Interval,Y)) :
      ∃ (α : Path (F (0,1)) (F (1,1))) (δ : Path (F (0,1)) (F (0,0)))
        (b : Path (F (0,0)) (F (1,0))) (v : Path (F (1,0)) (F (1,1))),
        (∀ t, α t=F (t,1)) ∧ (∀ t, δ t=F (0,unitInterval.symm t)) ∧
        (∀ t, b t=F (t,0)) ∧ (∀ t, v t=F (1,t)) ∧
        α.Homotopic (δ.trans (b.trans v)) := by
    let top : Path ((0,1) : Interval × Interval) (1,1) :=
      ⟨⟨fun t => (t,1),by fun_prop⟩,rfl,rfl⟩
    let left : Path ((0,1) : Interval × Interval) (0,0) :=
      ⟨⟨fun t => (0,unitInterval.symm t),by fun_prop⟩,by simp,by simp⟩
    let bottom : Path ((0,0) : Interval × Interval) (1,0) :=
      ⟨⟨fun t => (t,0),by fun_prop⟩,rfl,rfl⟩
    let right : Path ((1,0) : Interval × Interval) (1,1) :=
      ⟨⟨fun t => (1,t),by fun_prop⟩,rfl,rfl⟩
    letI : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
    have hhom := (SimplyConnectedSpace.paths_homotopic top (left.trans (bottom.trans right))).map F
    refine ⟨top.map F.continuous,left.map F.continuous,bottom.map F.continuous,right.map F.continuous,
      (fun _ => rfl),(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),?_⟩
    simpa only [Path.map_trans] using hhom
  have hBasedSquareBoundaryHomotopy {Y : Type} [TopologicalSpace Y]
      (F : C(Interval × Interval,Y)) (p : Y) (hleft : ∀ w, F (0,w)=p) :
      ∃ (α : Path p (F (1,1))) (b : Path p (F (1,0)))
        (v : Path (F (1,0)) (F (1,1))),
        (∀ t, α t=F (t,1)) ∧ (∀ t, b t=F (t,0)) ∧
        (∀ t, v t=F (1,t)) ∧ α.Homotopic (b.trans v) := by
    obtain ⟨α,δ,b,v,hα,hδ,hb,hv,hhom⟩ := hSquareBoundaryHomotopy F
    let α' := α.cast (hleft 1).symm rfl
    let b' := b.cast (hleft 0).symm rfl
    let δ' := δ.cast (hleft 1).symm (hleft 0).symm
    have hδ' : δ'=Path.refl p := by
      apply Path.ext
      funext t
      exact (hδ t).trans (hleft _)
    have hc : (δ.trans (b.trans v)).cast (hleft 1).symm rfl =
        δ'.trans (b'.trans v) := by
      exact Path.cast_trans δ (b.trans v) (hleft 1).symm (hleft 0).symm rfl
    have hh := hhom.pathCast (hleft 1).symm rfl
    rw [hc,hδ'] at hh
    exact ⟨α',b',v,hα,hb,hv,hh.trans (Path.Homotopic.refl_trans (b'.trans v))⟩
  have hEmbeddedIntervalPathHomotopy {Y : Type} [TopologicalSpace Y]
      (g : C(Interval,Y)) (hg : IsEmbedding g) {u v : Y}
      (α β : Path u v) (hα : range α ⊆ range g) (hβ : range β ⊆ range g) :
      α.Homotopic β := by
    have hu : u ∈ range g := hα ⟨0,α.source⟩
    have hv : v ∈ range g := hα ⟨1,α.target⟩
    let e := hg.toHomeomorph
    let αR : Path (⟨u,hu⟩ : range g) ⟨v,hv⟩ :=
      ⟨⟨fun t => ⟨α t,hα (mem_range_self t)⟩,α.continuous.subtype_mk _⟩,
        Subtype.ext α.source,Subtype.ext α.target⟩
    let βR : Path (⟨u,hu⟩ : range g) ⟨v,hv⟩ :=
      ⟨⟨fun t => ⟨β t,hβ (mem_range_self t)⟩,β.continuous.subtype_mk _⟩,
        Subtype.ext β.source,Subtype.ext β.target⟩
    let αI := αR.map e.symm.continuous
    let βI := βR.map e.symm.continuous
    letI : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
    have hh := (SimplyConnectedSpace.paths_homotopic αI βI).map g
    have hstart : u = g (e.symm ⟨u,hu⟩) :=
      (congrArg Subtype.val (e.apply_symm_apply ⟨u,hu⟩)).symm
    have hend : v = g (e.symm ⟨v,hv⟩) :=
      (congrArg Subtype.val (e.apply_symm_apply ⟨v,hv⟩)).symm
    have hαeq : (αI.map g.continuous).cast hstart hend=α := by
      apply Path.ext
      funext t
      exact congrArg Subtype.val (e.apply_symm_apply ⟨α t,hα (mem_range_self t)⟩)
    have hβeq : (βI.map g.continuous).cast hstart hend=β := by
      apply Path.ext
      funext t
      exact congrArg Subtype.val (e.apply_symm_apply ⟨β t,hβ (mem_range_self t)⟩)
    simpa only [hαeq,hβeq] using hh.pathCast hstart hend
  have hActualPuncturedPrefixHomotopy (b : EssentialMarkedArc M)
      (hb : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) b))
      (hi : ℝ) (hhi0 : 0 < hi) (hhi1 : hi < 1)
      {u v : ↑(((M.cover.branch : Set S) \ {b.val.map 0})ᶜ)}
      (α β : Path u v)
      (hα : ∀ t, (α t:S) ∈ (b.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi)
      (hβ : ∀ t, (β t:S) ∈ (b.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) :
      α.Homotopic β := by
    let X : Set S := ((M.cover.branch : Set S) \ {b.val.map 0})ᶜ
    let q : Interval → Interval := fun t => ⟨hi*(t:ℝ),
      ⟨mul_nonneg hhi0.le t.property.1,
        (mul_le_of_le_one_right hhi0.le t.property.2).trans hhi1.le⟩⟩
    have hq : Continuous q := by dsimp [q]; fun_prop
    have hX (t : Interval) : b.val.map (q t) ∈ X := by
      rintro ⟨hm,hn⟩
      rcases b.val.marked_only_at_ends (q t) hm with he | he
      · exact hn (congrArg b.val.map he)
      · have hh : hi*(t:ℝ)=1 := congrArg Subtype.val he
        have hle := mul_le_of_le_one_right hhi0.le t.property.2
        linarith
    let g : C(Interval,X) := ⟨fun t => ⟨b.val.map (q t),hX t⟩,
      (b.val.continuous.comp hq).subtype_mk _⟩
    have hg : IsEmbedding g := (g.continuous.isClosedEmbedding (by
      intro t w he
      have hh := NonLoopArc.injective ⟨b.val,actualRepresentative_nonloop M b hb⟩
        (congrArg Subtype.val he)
      apply Subtype.ext
      have hh' : hi*(t:ℝ)=hi*(w:ℝ) := congrArg Subtype.val hh
      exact mul_left_cancel₀ (ne_of_gt hhi0) hh')).isEmbedding
    have hLift (γ : Path u v)
        (hγ : ∀ t, (γ t:S) ∈ (b.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) :
        range γ ⊆ range g := by
      rintro z ⟨t,rfl⟩
      obtain ⟨x,hx,hxe⟩ := hγ t
      let tx : Interval := ⟨x/hi,⟨div_nonneg hx.1 hhi0.le,(div_le_one hhi0).mpr hx.2⟩⟩
      refine ⟨tx,Subtype.ext ?_⟩
      change b.val.map (q tx) = (γ t:S)
      have hqt : q tx=projIcc 0 1 zero_le_one x := by
        apply Subtype.ext
        rw [projIcc_of_mem zero_le_one ⟨hx.1,hx.2.trans hhi1.le⟩]
        change hi*(x/hi)=x
        field_simp
      rw [hqt]
      exact hxe
    exact hEmbeddedIntervalPathHomotopy g hg α β (hLift α hα) (hLift β hβ)
  have hActualHalfStripDiskPathHomotopy
      (hbaseB : D.firstCorner=(old i).val.map 0)
      (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
      (hprefixB : range D.secondSide = ((old i).val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 β)
      (hβq : (old i).val.map ⟨β,hβ0.le,hβ1.le⟩=D.secondCorner)
      (N : Interval × Icc (-1:ℝ) 1 → S) (hN : IsEmbedding N)
      (hcenter : ∀ t, N (t,⟨0,by norm_num⟩)=(old i).val.map t)
      (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
      (h : C(Interval,ℝ)) (hh0 : h 0=0) (hh1 : h 1=ρ)
      (hbound : ∀ t, 0 ≤ h t ∧ h t ≤ ρ)
      (P : Set S) (hmarks : (M.cover.branch : Set S) ⊆ P)
      (hband : ∀ (t : Interval) (v : Icc (-1:ℝ) 1), 0 < (t:ℝ) → |(v:ℝ)| ≤ h t →
        N (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
          (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩,v) ∉ P)
      (s : Bool) :
      ∃ (hp : (old i).val.map 0 ∈ ((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)
        (hq : D.secondCorner ∈ ((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)
        (z : ↑(((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)),
      ∃ (rail : Path ⟨(old i).val.map 0,hp⟩ z)
        (side : Path (⟨(old i).val.map 0,hp⟩ : ↑(((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)) ⟨D.secondCorner,hq⟩)
        (normal : Path ⟨D.secondCorner,hq⟩ z),
        (∀ t, (side t:S)=D.firstSide t) ∧
        (∀ t, ∃ v : Icc (-1:ℝ) 1,
          (v:ℝ)=(if s then (1:ℝ) else -1)*h t ∧
          (rail t:S)=N (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩,v)) ∧
        (∀ (t : Interval), ∃ v : Icc (-1:ℝ) 1,
          (v:ℝ)=(if s then (1:ℝ) else -1)*ρ*(t:ℝ) ∧
          (normal t:S)=N (⟨β,hβ0.le,hβ1.le⟩,v)) ∧
        rail.Homotopic (side.trans normal) := by
    let X : Set S := ((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ
    obtain ⟨F,hFcenter,hFbase,hFcoords⟩ := hactualStripBandMap β hβ0 hβ1 N hN
      hcenter ρ hρ hρhalf h hh0 hh1 hbound P hmarks hband s
    have hp : (old i).val.map 0 ∈ X := by simp [X]
    have hq : D.secondCorner ∈ X := by intro hm; exact hlast hm.1
    let p : X := ⟨(old i).val.map 0,hp⟩
    let q : X := ⟨D.secondCorner,hq⟩
    have hleft : ∀ w, F (0,w)=p := fun w => Subtype.ext (hFbase w)
    obtain ⟨rail,b,normal,hrail,hb,hnormal,hhom⟩ := hBasedSquareBoundaryHomotopy F p hleft
    have hqEnd : q=F (1,0) := by
      apply Subtype.ext
      rw [hFcenter]
      simpa only [show ((1:Interval):ℝ)=1 from rfl,mul_one] using hβq.symm
    let b' := b.cast rfl hqEnd
    let normal' := normal.cast hqEnd rfl
    have hD := hactualDiskSideHomotopy
    rw [hbaseB] at hD
    obtain ⟨hpD,hqD,side,target,hside,htarget,hDhom⟩ := hD
    have hbtarget : b'.Homotopic target := by
      apply hActualPuncturedPrefixHomotopy (old i) (hold i) β hβ0 hβ1
      · intro t
        have he : (b' t:S)=(old i).val.map
            ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
              (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩ :=
          (congrArg Subtype.val (hb t)).trans (hFcenter t)
        rw [he]
        refine ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
          mul_le_of_le_one_right hβ0.le t.property.2⟩,?_⟩
        rw [Function.comp_apply,projIcc_of_mem zero_le_one]
        exact ⟨mul_nonneg hβ0.le t.property.1,
          (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩
      · intro t
        rw [htarget t,← hprefixB]
        exact mem_range_self t
    have hhom' : rail.Homotopic (b'.trans normal') := by
      have he : b'.trans normal'=b.trans normal := Path.cast_trans b normal rfl hqEnd rfl |>.symm
      rw [he]
      exact hhom
    refine ⟨hp,hq,F (1,1),rail,side,normal',hside,?_,?_,
      hhom'.trans ((hbtarget.trans hDhom.symm).hcomp (Path.Homotopic.refl normal'))⟩
    · intro t
      obtain ⟨v,hv,hvF⟩ := hFcoords t 1
      refine ⟨v,by simpa only [show ((1:Interval):ℝ)=1 from rfl,mul_one] using hv,?_⟩
      exact (congrArg Subtype.val (hrail t)).trans hvF
    · intro t
      obtain ⟨v,hv,hvF⟩ := hFcoords 1 t
      refine ⟨v,by simpa only [hh1] using hv,?_⟩
      exact (congrArg Subtype.val (hnormal t)).trans
        (by simpa only [show ((1:Interval):ℝ)=1 from rfl,mul_one] using hvF)
  have hTerminalNormalSourceRangeCore (α hi : ℝ)
      (hα : 0 < α) (hαhi : α < hi) (hhi : hi < 1)
      (hαq : D.secondCorner=a.val.map (projIcc 0 1 zero_le_one α))
      (n : C(Interval,S)) (hn : IsEmbedding n) (hon : range n ⊆ a.val.image)
      (hn0 : n 0=D.secondCorner)
      (hn1 : n 1=a.val.map (projIcc 0 1 zero_le_one hi))
      (hn1mark : n 1 ∉ M.cover.branch) :
      range n ⊆ (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi := by
    obtain ⟨u,v,huv,hu0,hu1,hv0,hv1,hu,hv,hrange⟩ := hordinaryParameters a ha n hn hon
      (hn0 ▸ hlast) hn1mark
    have hinj := NonLoopArc.injective ⟨a.val,actualRepresentative_nonloop M a ha⟩
    have hu' : u=projIcc 0 1 zero_le_one α := hinj (hu.symm.trans (hn0.trans hαq))
    have hv' : v=projIcc 0 1 zero_le_one hi := hinj (hv.symm.trans hn1)
    have hαI : α ∈ Icc (0:ℝ) 1 := ⟨hα.le,(hαhi.trans hhi).le⟩
    have hhiI : hi ∈ Icc (0:ℝ) 1 := ⟨(hα.trans hαhi).le,hhi.le⟩
    have huvle : projIcc 0 1 zero_le_one α ≤ projIcc 0 1 zero_le_one hi := by
      change (projIcc 0 1 zero_le_one α:ℝ) ≤ (projIcc 0 1 zero_le_one hi:ℝ)
      rw [projIcc_of_mem zero_le_one hαI,projIcc_of_mem zero_le_one hhiI]
      exact hαhi.le
    rw [hrange,hu',hv',uIcc_of_le huvle]
    rintro y ⟨t,ht,rfl⟩
    have htHi : (t:ℝ) ≤ hi := by
      have hh := ht.2
      change (t:ℝ) ≤ (projIcc 0 1 zero_le_one hi:ℝ) at hh
      simpa only [projIcc_of_mem zero_le_one hhiI] using hh
    refine ⟨(t:ℝ),⟨t.property.1,htHi⟩,?_⟩
    simp only [Function.comp_apply,projIcc_of_mem zero_le_one t.property]
  have hActualPuncturedCorePath (hi : ℝ) (hhi0 : 0 < hi) (hhi1 : hi < 1) :
      ∃ (hp : a.val.map 0 ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ)
        (hq : a.val.map (projIcc 0 1 zero_le_one hi) ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ),
      ∃ γ : Path (⟨a.val.map 0,hp⟩ : ↑(((M.cover.branch : Set S) \ {a.val.map 0})ᶜ))
          ⟨a.val.map (projIcc 0 1 zero_le_one hi),hq⟩,
        IsEmbedding (fun t => (γ t:S)) ∧
        range (fun t => (γ t:S)) = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi := by
    let X : Set S := ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ
    let q : Interval → Interval := fun t => ⟨hi*(t:ℝ),
      ⟨mul_nonneg hhi0.le t.property.1,
        (mul_le_of_le_one_right hhi0.le t.property.2).trans hhi1.le⟩⟩
    have hqcont : Continuous q := by dsimp [q]; fun_prop
    have hX (t : Interval) : a.val.map (q t) ∈ X := by
      rintro ⟨hm,hn⟩
      rcases a.val.marked_only_at_ends (q t) hm with he | he
      · exact hn (congrArg a.val.map he)
      · have hh : hi*(t:ℝ)=1 := congrArg Subtype.val he
        have hle := mul_le_of_le_one_right hhi0.le t.property.2
        linarith
    let c : C(Interval,X) := ⟨fun t => ⟨a.val.map (q t),hX t⟩,
      (a.val.continuous.comp hqcont).subtype_mk _⟩
    have hp : a.val.map 0 ∈ X := by simp [X]
    have hq0 : q 0=0 := by apply Subtype.ext; dsimp [q]; norm_num
    have hq1 : q 1=projIcc 0 1 zero_le_one hi := by
      apply Subtype.ext
      rw [projIcc_of_mem zero_le_one ⟨hhi0.le,hhi1.le⟩]
      dsimp [q]; norm_num
    have hq : a.val.map (projIcc 0 1 zero_le_one hi) ∈ X := hq1 ▸ hX 1
    let γ : Path (⟨a.val.map 0,hp⟩ : X) ⟨a.val.map (projIcc 0 1 zero_le_one hi),hq⟩ :=
      ⟨c,Subtype.ext (congrArg a.val.map hq0),Subtype.ext (congrArg a.val.map hq1)⟩
    have hc : IsEmbedding (fun t => (γ t:S)) :=
      ((a.val.continuous.comp hqcont).isClosedEmbedding (by
        intro t u he
        have hh := NonLoopArc.injective ⟨a.val,actualRepresentative_nonloop M a ha⟩ he
        apply Subtype.ext
        exact mul_left_cancel₀ (ne_of_gt hhi0) (congrArg Subtype.val hh))).isEmbedding
    refine ⟨hp,hq,γ,hc,?_⟩
    apply Subset.antisymm
    · rintro y ⟨t,rfl⟩
      refine ⟨hi*(t:ℝ),⟨mul_nonneg hhi0.le t.property.1,
        mul_le_of_le_one_right hhi0.le t.property.2⟩,?_⟩
      rw [Function.comp_apply,projIcc_of_mem zero_le_one (q t).property]
      rfl
    · rintro y ⟨x,hx,rfl⟩
      let tx : Interval := ⟨x/hi,⟨div_nonneg hx.1 hhi0.le,(div_le_one hhi0).mpr hx.2⟩⟩
      refine ⟨tx,?_⟩
      change a.val.map (q tx)=a.val.map (projIcc 0 1 zero_le_one x)
      congr 1; apply Subtype.ext
      rw [projIcc_of_mem zero_le_one ⟨hx.1,hx.2.trans hhi1.le⟩]
      change hi*(x/hi)=x
      field_simp
  have hSideNormalHomotopyToSourceCore (α hi : ℝ)
      (hα : 0 < α) (hαhi : α < hi) (hhi : hi < 1)
      (hprefix : range D.firstSide=(a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 α)
      (hαq : D.secondCorner=a.val.map (projIcc 0 1 zero_le_one α))
      (hp : a.val.map 0 ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ)
      (hq : D.secondCorner ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ)
      (hz : a.val.map (projIcc 0 1 zero_le_one hi) ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ)
      (side : Path (⟨a.val.map 0,hp⟩ : ↑(((M.cover.branch : Set S) \ {a.val.map 0})ᶜ)) ⟨D.secondCorner,hq⟩)
      (normal : Path (⟨D.secondCorner,hq⟩ : ↑(((M.cover.branch : Set S) \ {a.val.map 0})ᶜ))
        ⟨a.val.map (projIcc 0 1 zero_le_one hi),hz⟩)
      (rail : Path (⟨a.val.map 0,hp⟩ : ↑(((M.cover.branch : Set S) \ {a.val.map 0})ᶜ))
        ⟨a.val.map (projIcc 0 1 zero_le_one hi),hz⟩)
      (hside : ∀ t, (side t:S)=D.firstSide t)
      (hnormal : IsEmbedding (fun t => (normal t:S)))
      (hnormalOn : range (fun t => (normal t:S)) ⊆ a.val.image)
      (hrail : rail.Homotopic (side.trans normal)) :
      ∃ core : Path (⟨a.val.map 0,hp⟩ : ↑(((M.cover.branch : Set S) \ {a.val.map 0})ᶜ))
          ⟨a.val.map (projIcc 0 1 zero_le_one hi),hz⟩,
        IsEmbedding (fun t => (core t:S)) ∧
        range (fun t => (core t:S))=(a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi ∧
        core.Homotopic rail := by
    have hhi0 : 0 < hi := hα.trans hαhi
    have hportUnmarked : a.val.map (projIcc 0 1 zero_le_one hi) ∉ M.cover.branch := by
      intro hm
      rcases a.val.marked_only_at_ends _ hm with he | he
      · have hh := congrArg Subtype.val he
        simp only [projIcc_of_mem zero_le_one ⟨hhi0.le,hhi.le⟩] at hh
        exact hhi0.ne' hh
      · have hh := congrArg Subtype.val he
        simp only [projIcc_of_mem zero_le_one ⟨hhi0.le,hhi.le⟩] at hh
        exact hhi.ne hh
    let n : C(Interval,S) := ⟨fun t => (normal t:S),continuous_subtype_val.comp normal.continuous⟩
    have hnCore := hTerminalNormalSourceRangeCore α hi hα hαhi hhi hαq n
      hnormal hnormalOn (congrArg Subtype.val normal.source)
      (congrArg Subtype.val normal.target)
      (by change (normal 1:S) ∉ M.cover.branch; rw [normal.target]; exact hportUnmarked)
    obtain ⟨hp',hz',core,hcore,hcoreRange⟩ := hActualPuncturedCorePath hi hhi0 hhi
    have hh : core.Homotopic (side.trans normal) := by
      apply hActualPuncturedPrefixHomotopy a ha hi hhi0 hhi
      · intro t
        exact hcoreRange ▸ mem_range_self t
      · intro t
        have ht : (side.trans normal) t ∈ range side ∪ range normal :=
          Path.trans_range side normal ▸ mem_range_self t
        rcases ht with ⟨u,hu⟩ | ⟨u,hu⟩
        · rw [← hu,hside u]
          exact image_mono (Icc_subset_Icc_right hαhi.le) (hprefix ▸ mem_range_self u)
        · rw [← hu]
          exact hnCore (mem_range_self u)
    exact ⟨core,hcore,hcoreRange,hh.trans hrail.symm⟩
  have hCoreHomotopyProducesActualSupportingRegion (hi : ℝ) (hhi0 : 0 < hi) (hhi1 : hi < 1)
      (g : C(Interval,S)) (hg : IsEmbedding g) (hg0 : g 0=a.val.map 0)
      (hg1 : g 1=a.val.map (projIcc 0 1 zero_le_one hi))
      (hgmeet : range g ∩ a.val.image = {a.val.map 0,g 1})
      (hp : a.val.map 0 ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ)
      (hz : a.val.map (projIcc 0 1 zero_le_one hi) ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ)
      (core rail : Path (⟨a.val.map 0,hp⟩ : ↑(((M.cover.branch : Set S) \ {a.val.map 0})ᶜ))
        ⟨a.val.map (projIcc 0 1 zero_le_one hi),hz⟩)
      (hcore : IsEmbedding (fun t => (core t:S)))
      (hcoreRange : range (fun t => (core t:S))=(a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi)
      (hrailMap : ∀ t, (rail t:S)=g t) (hhom : core.Homotopic rail) :
      ∃ Ω : Set S, Ω.Nonempty ∧ IsConnected Ω ∧
        Ω ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ ∧
        (∀ V : Set S, IsConnected V → Ω ⊆ V →
          V ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ → V=Ω) ∧
        frontier Ω = ((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g ∧
        Disjoint Ω (M.cover.branch : Set S) := by
    let f : C(Interval,S) := ⟨fun t => (core t:S),continuous_subtype_val.comp core.continuous⟩
    have hf0 : f 0=a.val.map 0 := congrArg Subtype.val core.source
    have hf1 : f 1=a.val.map (projIcc 0 1 zero_le_one hi) := congrArg Subtype.val core.target
    have hfRange : range f=(a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi := hcoreRange
    have hfa : range f ⊆ a.val.image := by
      rw [hfRange]
      rintro y ⟨t,ht,rfl⟩
      exact mem_range_self _
    have hne : a.val.map 0 ≠ a.val.map (projIcc 0 1 zero_le_one hi) := by
      intro he
      have hh := congrArg Subtype.val
        (NonLoopArc.injective ⟨a.val,actualRepresentative_nonloop M a ha⟩ he)
      simp only [projIcc_of_mem zero_le_one ⟨hhi0.le,hhi1.le⟩] at hh
      exact hhi0.ne hh
    have hinter : range f ∩ range g = {a.val.map 0,a.val.map (projIcc 0 1 zero_le_one hi)} := by
      apply Subset.antisymm
      · intro y hy
        have he : y ∈ ({a.val.map 0,g 1} : Set S) :=
          hgmeet ▸ (show y ∈ range g ∩ a.val.image from ⟨hy.2,hfa hy.1⟩)
        simpa only [hg1] using he
      · intro y hy
        rcases mem_insert_iff.mp hy with he | he
        · exact ⟨⟨0,hf0.trans he.symm⟩,⟨0,hg0.trans he.symm⟩⟩
        · exact ⟨⟨1,hf1.trans (mem_singleton_iff.mp he).symm⟩,
            ⟨1,hg1.trans (mem_singleton_iff.mp he).symm⟩⟩
    obtain ⟨Ω,hΩ⟩ := actual_punctured_homotopic_jordan_sides_have_empty_region M f g
      (a.val.map 0) (a.val.map (projIcc 0 1 zero_le_one hi)) hcore hg hf0 hg0 hf1 hg1
      hne hinter hp hz core rail (fun _ => rfl) hrailMap hhom
    exact ⟨Ω,by simpa only [hfRange] using hΩ⟩
  have hroundedFamilySides (hbase : D.firstCorner = (old i).val.map 0) :
      ∃ f : Bool → C(Interval,S), (∀ s,
        IsEmbedding (f s) ∧ f s 0 = D.firstCorner ∧
        (∀ k, Disjoint (range (f s)) (arcInterior M (old k))) ∧
        range (f s) ∩ a.val.image = {D.firstCorner,f s 1} ∧
        f s 1 ∉ M.cover.branch) ∧
      (D.firstCorner = a.val.map 0 → ∃ s, f s 1 ∉ range D.firstSide) ∧
      (∀ s t, t ≠ 0 → f s t ∉ M.cover.branch) ∧
      (∀ s, ∃ (hp : (old i).val.map 0 ∈ ((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)
        (hq : D.secondCorner ∈ ((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)
        (z : ↑(((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)),
        ∃ (rail : Path ⟨(old i).val.map 0,hp⟩ z)
          (side : Path (⟨(old i).val.map 0,hp⟩ : ↑(((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)) ⟨D.secondCorner,hq⟩)
          (normal : Path ⟨D.secondCorner,hq⟩ z),
          (∀ t, (rail t:S)=f s t) ∧ (∀ t, (side t:S)=D.firstSide t) ∧
          IsEmbedding (fun t => (normal t:S)) ∧
          range (fun t => (normal t:S)) ⊆ a.val.image ∧
          rail.Homotopic (side.trans normal)) ∧ (∀ s, range (f s) ⊆ U) := by
    obtain ⟨β,N,hβ0,hβ1,hprefix,hβq,hNU,hN,hcenter,σ,δ,η,hsign,hδ,hη,hframe⟩ := hframedStrip hbase
    have hβq' : (old i).val.map ⟨β,hβ0.le,hβ1.le⟩ = D.secondCorner := by
      simpa only [projIcc_of_mem zero_le_one ⟨hβ0.le,hβ1.le⟩] using hβq
    obtain ⟨T,hT,hqT,hTG,hTN⟩ := hsmallFramedSupport β hβ0 hβ1 N hN hcenter hβq' η hη
    let P : Set S := (M.cover.branch : Set S) ∪ Other ∪ (a.val.image ∩ Tᶜ)
    have haClosed : IsClosed a.val.image := by
      simpa only [image_univ,MarkedArc.image] using (isCompact_univ.image a.val.continuous).isClosed
    have hP : IsClosed P := (M.cover.branch.isClosed.union hOtherClosed).union
      (haClosed.inter hT.isClosed_compl)
    have hPbase : (old i).val.map 0 ∈ P := Or.inl (Or.inl (old i).val.start_marked)
    have haxis : ∀ t : Interval, 0 < (t:ℝ) →
        (old i).val.map ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
          (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩ ∉ P := by
      intro t ht hp
      let u : Interval := ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
        (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩
      have hu0 : 0 < (u:ℝ) := mul_pos hβ0 ht
      have hu1 : (u:ℝ) < 1 :=
        lt_of_le_of_lt (mul_le_of_le_one_right hβ0.le t.property.2) hβ1
      have hm : (old i).val.map u ∉ M.cover.branch := by
        intro hm
        rcases (old i).val.marked_only_at_ends u hm with he | he
        · have hh : (u:ℝ) = 0 := congrArg Subtype.val he
          linarith
        · have hh : (u:ℝ) = 1 := congrArg Subtype.val he
          linarith
      change (old i).val.map u ∈ P at hp
      rcases hp with hp | hp
      · rcases hp with hp | hp
        · exact hm hp
        · obtain ⟨k,hk⟩ := mem_iUnion.mp hp
          exact Set.disjoint_left.mp (hd i k.val (Ne.symm k.property)) ⟨mem_range_self u,hm⟩ ⟨hk,hm⟩
      · have huSide : (old i).val.map u ∈ range D.secondSide := by
          rw [hprefix]
          exact ⟨(u:ℝ),⟨u.property.1,mul_le_of_le_one_right hβ0.le t.property.2⟩,
            by simp only [Function.comp_apply,projIcc_of_mem zero_le_one u.property]⟩
        have hc := hsecondClean ▸ (show (old i).val.map u ∈ range D.secondSide ∩ a.val.image from ⟨huSide,hp.1⟩)
        rcases mem_insert_iff.mp hc with he | he
        · have hinj := NonLoopArc.injective ⟨(old i).val,actualRepresentative_nonloop M (old i) (hold i)⟩
          have hh : (u:ℝ) = 0 := congrArg Subtype.val (hinj (he.trans hbase))
          linarith
        · exact hp.2 ((mem_singleton_iff.mp he).symm ▸ hqT)
    obtain ⟨ρ,hρ,hρhalf,h,hh0,hbound,hpositive,hflat,f,hcoords,hf,hband⟩ :=
      htracksFromChosenStrip β hβ0 hβ1 N hN hcenter P hP hPbase haxis
    have hnotP (s : Bool) (t : Interval) (ht : t ≠ 0) : f s t ∉ P := by
      intro hp
      have he : f s t = (old i).val.map 0 :=
        mem_singleton_iff.mp ((hf s).2.2.1 ▸ ⟨mem_range_self t,hp⟩)
      exact ht ((hf s).1.injective (he.trans (hf s).2.1.symm))
    have hport (s : Bool) : f s 1 ∈ a.val.image := by
      obtain ⟨v,hv,hfv⟩ := hcoords s 1
      have hfv' : f s 1 = N (⟨β,hβ0.le,hβ1.le⟩,v) := by
        simpa only [show ((1 : Interval) : ℝ) = 1 from rfl,mul_one] using hfv
      have hw := hframe ⟨β,hβ0.le,hβ1.le⟩ v (by simpa only [sub_self,abs_zero] using hη)
      have hg0 : G (f s 1) 0 = 0 := by
        rw [hfv',hw.2,hβq',hGzero]
        rfl
      exact (haF (f s 1) (hGs ▸ (hfv'.symm ▸ hw.1))).mpr (by change (F (f s 1)).1 = 0 at hg0; exact hg0)
    have hselectPort (hstart : D.firstCorner = a.val.map 0) :
        ∃ s : Bool, f s 1 ∉ range D.firstSide := by
      let w : Interval → Icc (-1:ℝ) 1 := fun t => ⟨ρ*(2*(t:ℝ)-1),by
        constructor <;> nlinarith [hρhalf,t.property.1,t.property.2]⟩
      let r : C(Interval,S) := ⟨fun t => N (⟨β,hβ0.le,hβ1.le⟩,w t),by
        apply hN.continuous.comp
        dsimp [w]; fun_prop⟩
      have hr : IsEmbedding r := (r.continuous.isClosedEmbedding (by
        intro t u he
        have hh := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hN.injective he)
        apply Subtype.ext
        change ρ*(2*(t:ℝ)-1)=ρ*(2*(u:ℝ)-1) at hh
        nlinarith [hρ])).isEmbedding
      have hrA : range r ⊆ a.val.image := by
        rintro z ⟨t,rfl⟩
        have hh := hframe ⟨β,hβ0.le,hβ1.le⟩ (w t) (by simpa only [sub_self,abs_zero] using hη)
        apply (haF (r t) (hGs ▸ hh.1)).mpr
        have hx : G (r t) 0 = 0 := by
          change G (N (⟨β,hβ0.le,hβ1.le⟩,w t)) 0 = 0
          rw [hh.2,hβq',hGzero]
          rfl
        exact hx
      have hrmid : r ⟨1/2,by constructor <;> norm_num⟩ = D.secondCorner := by
        have hw : w ⟨1/2,by constructor <;> norm_num⟩ = ⟨0,by norm_num⟩ := by
          apply Subtype.ext; dsimp [w]; ring
        change N (_,w _) = _
        rw [hw,hcenter,hβq']
      have hrend (s : Bool) : (if s then r 1 else r 0) = f s 1 := by
        obtain ⟨v,hv,hfv⟩ := hcoords s 1
        have hv' : (v:ℝ) = (if s then (1:ℝ) else -1)*ρ := by
          rw [hv,hflat 1 (by norm_num)]
        have hfv' : f s 1 = N (⟨β,hβ0.le,hβ1.le⟩,v) := by
          simpa only [show ((1:Interval):ℝ)=1 from rfl,mul_one] using hfv
        rw [hfv']
        cases s
        · change N (⟨β,hβ0.le,hβ1.le⟩,w 0) = N (⟨β,hβ0.le,hβ1.le⟩,v)
          congr 1
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            change ρ*(2*(0:ℝ)-1) = (v:ℝ)
            norm_num at hv' ⊢
            linarith
        · change N (⟨β,hβ0.le,hβ1.le⟩,w 1) = N (⟨β,hβ0.le,hβ1.le⟩,v)
          congr 1
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            change ρ*(2*(1:ℝ)-1) = (v:ℝ)
            norm_num at hv' ⊢
            exact hv'.symm
      obtain ⟨s,hs⟩ := hsourceStraddling hstart r hr hrA hrmid
      exact ⟨s,hrend s ▸ hs⟩
    have hrailMarks : ∀ s t, t ≠ 0 → f s t ∉ M.cover.branch := by
      intro s t ht hm
      exact hnotP s t ht (Or.inl (Or.inl hm))
    have hpaths (s : Bool) :
        ∃ (hp : (old i).val.map 0 ∈ ((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)
          (hq : D.secondCorner ∈ ((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)
          (z : ↑(((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)),
        ∃ (rail : Path ⟨(old i).val.map 0,hp⟩ z)
          (side : Path (⟨(old i).val.map 0,hp⟩ : ↑(((M.cover.branch : Set S) \ {(old i).val.map 0})ᶜ)) ⟨D.secondCorner,hq⟩)
          (normal : Path ⟨D.secondCorner,hq⟩ z),
          (∀ t, (rail t:S)=f s t) ∧ (∀ t, (side t:S)=D.firstSide t) ∧
          IsEmbedding (fun t => (normal t:S)) ∧
          range (fun t => (normal t:S)) ⊆ a.val.image ∧
          rail.Homotopic (side.trans normal) := by
      obtain ⟨hp,hq,z,rail,side,normal,hside,hrail,hnormal,hhom⟩ :=
        hActualHalfStripDiskPathHomotopy hbase β hβ0 hβ1 hprefix hβq'
          N hN hcenter ρ hρ hρhalf h hh0 (hflat 1 (by norm_num))
          hbound P (fun _ hm => Or.inl (Or.inl hm)) hband s
      have hrailMap : ∀ t, (rail t:S)=f s t := by
        intro t
        obtain ⟨v,hv,hvrt⟩ := hrail t
        obtain ⟨w,hw,hwft⟩ := hcoords s t
        rw [hvrt,hwft]
        congr 1
        apply Prod.ext
        · rfl
        · exact Subtype.ext (hv.trans hw.symm)
      have hncont : Continuous (fun t => (normal t:S)) := continuous_subtype_val.comp normal.continuous
      have hnembedding : IsEmbedding (fun t => (normal t:S)) := (hncont.isClosedEmbedding (by
        intro t u he
        obtain ⟨v,hv,hvt⟩ := hnormal t
        obtain ⟨w,hw,hwu⟩ := hnormal u
        have hh := congrArg (fun x : Interval × Icc (-1:ℝ) 1 => (x.2:ℝ))
          (hN.injective (hvt.symm.trans (he.trans hwu)))
        rw [hv,hw] at hh
        apply Subtype.ext
        exact mul_left_cancel₀ (mul_ne_zero (by cases s <;> norm_num) (ne_of_gt hρ)) hh)).isEmbedding
      have hnOn : range (fun t => (normal t:S)) ⊆ a.val.image := by
        rintro y ⟨t,rfl⟩
        obtain ⟨v,hv,hvt⟩ := hnormal t
        have hfr := hframe ⟨β,hβ0.le,hβ1.le⟩ v (by simpa only [sub_self,abs_zero] using hη)
        apply (haF (normal t:S) (hGs ▸ (hvt ▸ hfr.1))).mpr
        have hx : G (normal t:S) 0=0 := by
          rw [hvt,hfr.2,hβq',hGzero]
          rfl
        rw [hGcoord] at hx
        exact hx
      exact ⟨hp,hq,z,rail,side,normal,hrailMap,hside,hnembedding,hnOn,hhom⟩
    have hrails : ∀ s, range (f s) ⊆ U := by
      rintro s z ⟨t,rfl⟩
      obtain ⟨v,hv,he⟩ := hcoords s t
      exact hNU ⟨_,he.symm⟩
    refine ⟨f,?_,hselectPort,hrailMarks,hpaths,hrails⟩
    intro s
    refine ⟨(hf s).1,(hf s).2.1.trans hbase.symm,?_,?_,?_⟩
    · intro k
      apply Set.disjoint_left.mpr
      intro z hzf hzk
      by_cases hk : k = i
      · subst k
        have he : z = (old i).val.map 0 := mem_singleton_iff.mp ((hf s).2.2.2 ▸ ⟨hzf,hzk.1⟩)
        exact hzk.2 (he.symm ▸ (old i).val.start_marked)
      · have hzP : z ∈ P := Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨k,hk⟩,hzk.1⟩))
        have he : z = (old i).val.map 0 := mem_singleton_iff.mp ((hf s).2.2.1 ▸ ⟨hzf,hzP⟩)
        exact hzk.2 (he.symm ▸ (old i).val.start_marked)
    · apply Subset.antisymm
      · rintro z ⟨⟨t,rfl⟩,hta⟩
        by_cases ht : t = 0
        · subst t
          exact mem_insert_iff.mpr (Or.inl ((hf s).2.1.trans hbase.symm))
        · have htT : f s t ∈ T := by
            by_contra hn
            exact hnotP s t ht (Or.inr ⟨hta,hn⟩)
          obtain ⟨v,hv,hft⟩ := hcoords s t
          let u : Interval := ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩
          have huη : |(u:ℝ)-β| < η := hTN (u,v) (hft ▸ htT)
          have hframev := hframe u v huη
          have hframezero := hframe u ⟨0,by norm_num⟩ huη
          have hucenter : (old i).val.map u ∈ G.source := hcenter u ▸ hframezero.1
          have hx : G ((old i).val.map u) 0 = 0 := by
            have hh : G (f s t) 0 = 0 := by
              rw [hGcoord]
              exact (haF (f s t) (hGs ▸ hTG htT)).mp hta
            rw [hft,hframev.2] at hh
            exact hh
          have hy : G ((old i).val.map u) 1 = 0 := by
            rw [hGcoord]
            exact (hbF ((old i).val.map u) (hGs ▸ hucenter)).mp (mem_range_self u)
          have hGq : G ((old i).val.map u) = G D.secondCorner := by
            rw [hGzero]
            ext j; fin_cases j
            · exact hx
            · exact hy
          have heq := G.injOn hucenter (hGs.symm ▸ hpF) hGq
          have huβ := (NonLoopArc.injective ⟨(old i).val,actualRepresentative_nonloop M (old i) (hold i)⟩)
            (heq.trans hβq'.symm)
          have ht1 : t = 1 := by
            apply Subtype.ext
            change (t:ℝ) = 1
            have hh : β*(t:ℝ) = β := congrArg Subtype.val huβ
            exact mul_left_cancel₀ (ne_of_gt hβ0) (by simpa only [mul_one] using hh)
          subst t
          exact mem_insert_of_mem _ (mem_singleton _)
      · intro z hz
        rcases mem_insert_iff.mp hz with he | he
        · subst z
          exact ⟨⟨0,(hf s).2.1.trans hbase.symm⟩,D.first_on_curve ⟨0,D.first_zero⟩⟩
        · subst z
          exact ⟨mem_range_self _,hport s⟩
    · intro hm
      exact hnotP s 1 (by norm_num) (Or.inl (Or.inl hm))
  have hroundedRetainedSide (hbaseB : D.firstCorner = (old i).val.map 0)
      (hbaseA : D.firstCorner = a.val.map 0) :
      ∃ (α hi : ℝ) (g : C(Interval,S)), 0 < α ∧ α < hi ∧ hi < 1 ∧
        range D.firstSide = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 α ∧
        IsEmbedding g ∧ g 0 = a.val.map 0 ∧
        g 1 = a.val.map (projIcc 0 1 zero_le_one hi) ∧
        (∀ k, Disjoint (range g) (arcInterior M (old k))) ∧
        range g ∩ a.val.image = {a.val.map 0,g 1} ∧ g 1 ∉ M.cover.branch ∧
        (∀ t, t ≠ 0 → g t ∉ M.cover.branch) := by
    obtain ⟨f,hf,hselect,hmarks,hpaths,hrails⟩ := hroundedFamilySides hbaseB
    obtain ⟨s,hs⟩ := hselect hbaseA
    have hpA : f s 1 ∈ a.val.image :=
      ((hf s).2.2.2.1.symm ▸ (show f s 1 ∈ ({D.firstCorner,f s 1} : Set S) from mem_insert_of_mem _ (mem_singleton _))).2
    obtain ⟨α,hi,hα,hαhi,hhi,hprefix,hport,hsourceCorner⟩ :=
      hretainedPortParameters hbaseA (f s 1) hpA (hf s).2.2.2.2 hs
    exact ⟨α,hi,f s,hα,hαhi,hhi,hprefix,(hf s).1,
      (hf s).2.1.trans hbaseA,hport,(hf s).2.2.1,
      by simpa only [hbaseA] using (hf s).2.2.2.1,(hf s).2.2.2.2,hmarks s⟩
  have hRoundedRetainedSupportingRegion (hbaseB : D.firstCorner = (old i).val.map 0)
      (hbaseA : D.firstCorner = a.val.map 0) :
      ∃ (α hi : ℝ) (g : C(Interval,S)) (Ω : Set S), 0 < α ∧ α < hi ∧ hi < 1 ∧
        range D.firstSide = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 α ∧
        IsEmbedding g ∧ g 0 = a.val.map 0 ∧
        g 1 = a.val.map (projIcc 0 1 zero_le_one hi) ∧
        (∀ k, Disjoint (range g) (arcInterior M (old k))) ∧
        range g ∩ a.val.image = {a.val.map 0,g 1} ∧ g 1 ∉ M.cover.branch ∧
        (∀ t, t ≠ 0 → g t ∉ M.cover.branch) ∧
        Ω.Nonempty ∧ IsConnected Ω ∧
        Ω ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ ∧
        (∀ V : Set S, IsConnected V → Ω ⊆ V →
          V ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ → V=Ω) ∧
        frontier Ω = ((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g ∧
        Disjoint Ω (M.cover.branch : Set S) ∧ range g ⊆ U := by
    obtain ⟨f,hf,hselect,hmarks,hpaths,hrails⟩ := hroundedFamilySides hbaseB
    obtain ⟨s,hs⟩ := hselect hbaseA
    have hpA : f s 1 ∈ a.val.image :=
      ((hf s).2.2.2.1.symm ▸ (show f s 1 ∈ ({D.firstCorner,f s 1} : Set S) from
        mem_insert_of_mem _ (mem_singleton _))).2
    obtain ⟨α,hi,hα,hαhi,hhi,hprefix,hport,hsourceCorner⟩ :=
      hretainedPortParameters hbaseA (f s 1) hpA (hf s).2.2.2.2 hs
    have hpdata := hpaths s
    rw [← hbaseB,hbaseA] at hpdata
    obtain ⟨hp,hq,z,rail,side,normal,hrailMap,hside,hnormal,hnormalOn,hhom⟩ := hpdata
    rcases z with ⟨z,hz⟩
    have hzport : z=a.val.map (projIcc 0 1 zero_le_one hi) :=
      (congrArg Subtype.val rail.target).symm.trans ((hrailMap 1).trans hport)
    subst z
    obtain ⟨core,hcore,hcoreRange,hcoreHom⟩ := hSideNormalHomotopyToSourceCore α hi
      hα hαhi hhi hprefix hsourceCorner hp hq hz side normal rail hside hnormal hnormalOn hhom
    have hg0 := (hf s).2.1.trans hbaseA
    have hgmeet : range (f s) ∩ a.val.image = {a.val.map 0,f s 1} := by
      simpa only [hbaseA] using (hf s).2.2.2.1
    obtain ⟨Ω,hΩ⟩ := hCoreHomotopyProducesActualSupportingRegion hi (hα.trans hαhi) hhi
      (f s) (hf s).1 hg0 hport hgmeet hp hz core rail hcore hcoreRange hrailMap hcoreHom
    rcases hΩ with ⟨hne,hconn,hfree,hmax,hfront,hmarksΩ⟩
    exact ⟨α,hi,f s,Ω,hα,hαhi,hhi,hprefix,(hf s).1,hg0,hport,
      (hf s).2.2.1,hgmeet,(hf s).2.2.2.2,hmarks s,hne,hconn,hfree,hmax,hfront,hmarksΩ,hrails s⟩
  exact hRoundedRetainedSupportingRegion hbaseB hbaseA

#print axioms localized_marked_nonloop_empty_disk_produces_retained_supporting_region
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem two_sides_inside_original_neighborhood_produce_supported_disk
    (M : HyperellipticModel E S) (a : NonLoopArc M) (N : ArcNeighborhood a)
    (f g : C(Interval,S)) (hf : IsEmbedding f) (hg : IsEmbedding g)
    (h0 : f 0=g 0) (h1 : f 1=g 1)
    (hmeet : range f ∩ range g={f 0,f 1})
    (hfN : range f ⊆ interior N.closedSet) (hgN : range g ⊆ interior N.closedSet) :
    ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S),
      IsEmbedding d ∧
      d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} = range f ∪ range g ∧
      range d ⊆ interior N.closedSet := by
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  letI : CurveComplex.ClosedSurface S := {}
  have hcross (t u : Interval) (he : f t=g u) :
      (t=0 ∧ u=0) ∨ (t=1 ∧ u=1) := by
    have hz : f t ∈ ({f 0,f 1}:Set S) := hmeet ▸ ⟨⟨t,rfl⟩,⟨u,he.symm⟩⟩
    rcases mem_insert_iff.mp hz with hz | hz
    · exact Or.inl ⟨hf.injective hz,hg.injective (he.symm.trans (hz.trans h0))⟩
    · have hz := mem_singleton_iff.mp hz
      exact Or.inr ⟨hf.injective hz,hg.injective (he.symm.trans (hz.trans h1))⟩
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f g hf.injective hg.injective h0 h1 hcross
  let d₀ : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
    ⟨fun x => (N.disk x).val,continuous_subtype_val.comp N.disk.continuous⟩
  have hd₀ : IsEmbedding d₀ := IsEmbedding.subtypeVal.comp N.disk.isEmbedding
  have hd₀range : range d₀=N.closedSet := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩; exact (N.disk x).property
    · intro hz
      exact ⟨N.disk.symm ⟨z,hz⟩,congrArg Subtype.val (N.disk.apply_symm_apply _)⟩
  have hcN : c.image ⊆ interior N.closedSet := by rw [hc]; exact union_subset hfN hgN
  obtain ⟨d,hd,hboundary,hsub⟩ := CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
    c d₀ hd₀ (hd₀range.symm ▸ (hcN.trans interior_subset))
  have hinside : d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
      interior N.closedSet := by
    apply (CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen d hd).subset_interior_iff.mpr
    intro z hz
    rw [← hd₀range]
    exact hsub (image_subset_range _ _ hz)
  refine ⟨d,hd,hboundary.trans hc,?_⟩
  rintro z ⟨x,rfl⟩
  have hxle : dist x.val 0 ≤ 1 := x.property
  rcases lt_or_eq_of_le hxle with hxlt | hxeq
  · exact hinside ⟨x,hxlt,rfl⟩
  · exact hcN (hboundary ▸ (show d x ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} from ⟨x,hxeq,rfl⟩))

private theorem same_boundary_disks_omitting_point_have_same_range
    (M : HyperellipticModel E S) (c : CurveComplex.Curve S)
    (d e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : IsEmbedding d) (he : IsEmbedding e)
    (hdb : d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=c.image)
    (heb : e '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=c.image)
    (p : S) (hpd : p ∉ range d) (hpe : p ∉ range e) : range d=range e := by
  let P := EuclideanSpace ℝ (Fin 2)
  let φ := M.puncturedPlane p
  have hpC : p ∉ c.image := by
    rw [← hdb]
    exact fun hp => hpd (image_subset_range _ _ hp)
  let dl : C(Metric.closedBall (0 : P) 1,{z : S // z ≠ p}) :=
    ⟨fun x => ⟨d x,fun hh => hpd (hh ▸ mem_range_self x)⟩,d.continuous.subtype_mk _⟩
  let el : C(Metric.closedBall (0 : P) 1,{z : S // z ≠ p}) :=
    ⟨fun x => ⟨e x,fun hh => hpe (hh ▸ mem_range_self x)⟩,e.continuous.subtype_mk _⟩
  let cl : Circle → {z : S // z ≠ p} :=
    fun z => ⟨c.map z,fun hh => hpC (hh ▸ mem_range_self z)⟩
  have hdl : IsEmbedding dl := hd.codRestrict {z | z ≠ p} _
  have hel : IsEmbedding el := he.codRestrict {z | z ≠ p} _
  have hcl : IsEmbedding cl := c.embedded.codRestrict {z | z ≠ p} _
  let dp : C(Metric.closedBall (0 : P) 1,P) := ⟨φ ∘ dl,φ.continuous.comp dl.continuous⟩
  let ep : C(Metric.closedBall (0 : P) 1,P) := ⟨φ ∘ el,φ.continuous.comp el.continuous⟩
  let cp : C(Circle,P) := ⟨φ ∘ cl,φ.continuous.comp (c.embedded.continuous.subtype_mk _)⟩
  have hdp : IsEmbedding dp := φ.isEmbedding.comp hdl
  have hep : IsEmbedding ep := φ.isEmbedding.comp hel
  have hcp : Schoenflies.IsJordanCurve (range cp) :=
    CurveComplex.isJordanCurve_range_of_isEmbedding_circle cp (φ.isEmbedding.comp hcl)
  have hboundary (f : C(Metric.closedBall (0 : P) 1,S))
      (hp : p ∉ range f)
      (hb : f '' {x | x.val ∈ Metric.sphere (0 : P) 1}=c.image) :
      (fun x => φ ⟨f x,fun hh => hp (hh ▸ mem_range_self x)⟩) ''
        {x | x.val ∈ Metric.sphere (0 : P) 1} = range cp := by
    apply Subset.antisymm
    · rintro z ⟨x,hx,rfl⟩
      obtain ⟨t,ht⟩ := hb ▸ (show f x ∈ f '' {x | x.val ∈ Metric.sphere (0 : P) 1} from ⟨x,hx,rfl⟩)
      refine ⟨t,?_⟩
      apply congrArg φ
      exact Subtype.ext ht
    · rintro z ⟨t,rfl⟩
      obtain ⟨x,hx,hxt⟩ := hb.symm ▸ (show c.map t ∈ c.image from mem_range_self t)
      refine ⟨x,hx,?_⟩
      apply congrArg φ
      exact Subtype.ext hxt
  have hdpr : range dp=Schoenflies.inside (range cp) ∪ range cp :=
    CurveComplex.embedded_disc_range_eq_closed_inside dp hdp _ hcp (hboundary d hpd hdb)
  have hepr : range ep=Schoenflies.inside (range cp) ∪ range cp :=
    CurveComplex.embedded_disc_range_eq_closed_inside ep hep _ hcp (hboundary e hpe heb)
  have hr : range dp=range ep := hdpr.trans hepr.symm
  apply Subset.antisymm
  · rintro z ⟨x,rfl⟩
    obtain ⟨y,hy⟩ := hr ▸ (show dp x ∈ range dp from mem_range_self x)
    refine ⟨y,?_⟩
    exact congrArg Subtype.val (φ.injective hy)
  · rintro z ⟨y,rfl⟩
    obtain ⟨x,hx⟩ := hr.symm ▸ (show ep y ∈ range ep from mem_range_self y)
    refine ⟨x,?_⟩
    exact congrArg Subtype.val (φ.injective hx)

private theorem marked_free_disk_with_boundary_inside_original_neighborhood_is_inside
    (M : HyperellipticModel E S) (a : NonLoopArc M) (N : ArcNeighborhood a)
    (c : CurveComplex.Curve S) (hcN : c.image ⊆ interior N.closedSet)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : IsEmbedding d)
    (hboundary : d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=c.image)
    (hmarks : Disjoint (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (M.cover.branch : Set S)) : range d ⊆ interior N.closedSet := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  letI : CurveComplex.ClosedSurface S := {}
  have hex : ∃ p ∈ M.cover.branch, p ∉ N.closedSet := by
    by_contra hn
    have hsub : M.cover.branch ⊆ ({a.val.map 0,a.val.map 1}:Finset S) := by
      intro p hp
      have hpN : p ∈ N.closedSet := by
        by_contra hpN
        exact hn ⟨p,hp,hpN⟩
      have he := N.marked_inside ▸ (show p ∈ (M.cover.branch:Set S) ∩ N.closedSet from ⟨hp,hpN⟩)
      simpa using he
    have hcard := Finset.card_le_card hsub
    rw [M.cover.branch_card] at hcard
    have htwo : ({a.val.map 0,a.val.map 1}:Finset S).card ≤ 2 := Finset.card_insert_le _ _
    omega
  obtain ⟨p,hpm,hpN⟩ := hex
  have hpd : p ∉ range d := by
    rintro ⟨x,hxp⟩
    rcases lt_or_eq_of_le (show dist x.val 0 ≤ 1 from x.property) with hxlt | hxeq
    · exact disjoint_left.mp hmarks ⟨x,hxlt,hxp⟩ hpm
    · exact hpN (interior_subset (hcN (hboundary ▸ ⟨x,hxeq,hxp⟩)))
  let d₀ : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
    ⟨fun x => (N.disk x).val,continuous_subtype_val.comp N.disk.continuous⟩
  have hd₀ : IsEmbedding d₀ := IsEmbedding.subtypeVal.comp N.disk.isEmbedding
  have hd₀range : range d₀=N.closedSet := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩; exact (N.disk x).property
    · intro hz
      exact ⟨N.disk.symm ⟨z,hz⟩,congrArg Subtype.val (N.disk.apply_symm_apply _)⟩
  obtain ⟨e,he,heb,heN⟩ := CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
    c d₀ hd₀ (hd₀range.symm ▸ (hcN.trans interior_subset))
  have heinside : e '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
      interior N.closedSet := by
    apply (CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen e he).subset_interior_iff.mpr
    intro z hz
    rw [← hd₀range]
    exact heN (image_subset_range _ _ hz)
  have heN' : range e ⊆ interior N.closedSet := by
    rintro z ⟨x,rfl⟩
    rcases lt_or_eq_of_le (show dist x.val 0 ≤ 1 from x.property) with hxlt | hxeq
    · exact heinside ⟨x,hxlt,rfl⟩
    · exact hcN (heb ▸ ⟨x,hxeq,rfl⟩)
  have hpe : p ∉ range e := fun hp => hpN (interior_subset (heN' hp))
  rw [same_boundary_disks_omitting_point_have_same_range M c d e hd he hboundary heb p hpd hpe]
  exact heN'

#print axioms marked_free_disk_with_boundary_inside_original_neighborhood_is_inside
#print axioms same_boundary_disks_omitting_point_have_same_range
#print axioms two_sides_inside_original_neighborhood_produce_supported_disk
end CurveComplex.HyperellipticModel
set_option maxHeartbeats 4000000
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem localized_normalized_marked_nonloop_empty_disk_relative_closed_piece_replacement
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M)
    (hold : ∀ k, ¬ (actualArcLabels M).isLoop
      (Quotient.mk (essentialArcSetoid M) (old k)))
    (hd : ∀ k l, k ≠ l → Disjoint (arcInterior M (old k)) (arcInterior M (old l)))
    (a : EssentialMarkedArc M)
    (ha : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) a))
    (hfinite : ∀ k, (ArcSurgery.crossings M (old k) a).Finite ∧
      ∀ p ∈ ArcSurgery.crossings M (old k) a, ArcSurgery.CrossesInDisk M (old k) a p)
    (i : ι) (D : ActualMarkedTwoSideDisk M a (old i))
    (hlast : D.secondCorner ∉ M.cover.branch)
    (hempty : Disjoint D.openInterior (a.val.image ∪ ⋃ k, (old k).val.image))
    (hbaseB : D.firstCorner=(old i).val.map 0)
    (hbaseA : D.firstCorner=a.val.map 0)
    (n : NonLoopArc M) (N : ArcNeighborhood n)
    (haN : a.val.image ⊆ interior N.closedSet)
    (holdN : (old i).val.image ⊆ interior N.closedSet) :
    ∃ (H : CurveComplex.AmbientIsotopy S) (C B R : Set S),
      (∀ t p, p ∈ M.cover.branch → H.map (t,p)=p) ∧
      IsCompact C ∧ IsCompact B ∧
      a.val.image=C ∪ R ∧ H.finalMap '' a.val.image=B ∪ R ∧
      (∀ k, Disjoint B (arcInterior M (old k))) ∧
      (∀ k, Disjoint (R ∩ arcInterior M (old k)) C) ∧
      (ArcSurgery.crossings M (old i) a ∩ C).Nonempty ∧
        (∀ t p, p ∉ interior N.closedSet → H.map (t,p)=p) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  letI : ClosedSurface S := {}
  have hlastCrossing : D.secondCorner ∈ ArcSurgery.crossings M (old i) a :=
    ⟨⟨D.second_on_curve ⟨1,D.second_one⟩,hlast⟩,
      D.first_on_curve ⟨1,D.first_one⟩,hlast⟩
  have hcoreAtPort (hi : ℝ) (hhi0 : 0 < hi) (hhi1 : hi < 1)
      (hportFree : ∀ k, a.val.map (projIcc 0 1 zero_le_one hi) ∉ arcInterior M (old k)) :
      ∃ C R : Set S, IsCompact C ∧ IsCompact R ∧ a.val.image = C ∪ R ∧
        C = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi ∧
        C ∩ R = {a.val.map 0,a.val.map (projIcc 0 1 zero_le_one hi)} ∧
        (∀ k, Disjoint (R ∩ arcInterior M (old k)) C) ∧
        R = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc hi 1 ∪ {a.val.map 0} := by
    let g : ℝ → S := a.val.map ∘ projIcc 0 1 zero_le_one
    have hg : Continuous g := a.val.continuous.comp continuous_projIcc
    let C : Set S := g '' Icc 0 hi
    let R : Set S := g '' Icc hi 1 ∪ {a.val.map 0}
    have hc : IsCompact C := isCompact_Icc.image hg
    have hr : IsCompact R := (isCompact_Icc.image hg).union isCompact_singleton
    have hwhole : a.val.image = C ∪ R := by
      apply Subset.antisymm
      · rintro z ⟨t,rfl⟩
        by_cases ht : (t:ℝ) ≤ hi
        · exact Or.inl ⟨(t:ℝ),⟨t.property.1,ht⟩,by simp only [g,Function.comp_apply,projIcc_of_mem zero_le_one t.property]⟩
        · exact Or.inr (Or.inl ⟨(t:ℝ),⟨le_of_not_ge ht,t.property.2⟩,by simp only [g,Function.comp_apply,projIcc_of_mem zero_le_one t.property]⟩)
      · intro z hz
        rcases hz with hz | hz
        · obtain ⟨t,ht,rfl⟩ := hz
          exact mem_range_self _
        · rcases hz with hz | hz
          · obtain ⟨t,ht,rfl⟩ := hz
            exact mem_range_self _
          · exact mem_singleton_iff.mp hz ▸ mem_range_self _
    have hinter : C ∩ R = {a.val.map 0,a.val.map (projIcc 0 1 zero_le_one hi)} := by
      apply Subset.antisymm
      · rintro z ⟨⟨t,ht,he⟩,hzR⟩
        rcases hzR with hzR | hzR
        · obtain ⟨u,hu,hue⟩ := hzR
          have htu : projIcc 0 1 zero_le_one t = projIcc 0 1 zero_le_one u :=
            (NonLoopArc.injective ⟨a.val,actualRepresentative_nonloop M a ha⟩) (he.trans hue.symm)
          have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.trans hhi1.le⟩
          have huI : u ∈ Icc (0:ℝ) 1 := ⟨hhi0.le.trans hu.1,hu.2⟩
          have htuReal : t = u := by
            have hh := congrArg Subtype.val htu
            simpa only [projIcc_of_mem zero_le_one htI,projIcc_of_mem zero_le_one huI] using hh
          have hthi : t = hi := le_antisymm ht.2 (htuReal ▸ hu.1)
          exact mem_insert_of_mem _ (mem_singleton_iff.mpr (he.symm.trans (by rw [hthi]; rfl)))
        · exact mem_insert_iff.mpr (Or.inl (mem_singleton_iff.mp hzR))
      · intro z hz
        rcases mem_insert_iff.mp hz with he | he
        · subst z
          exact ⟨⟨0,⟨le_rfl,hhi0.le⟩,by simp [g]⟩,Or.inr (mem_singleton _)⟩
        · have heq := mem_singleton_iff.mp he
          subst z
          exact ⟨⟨hi,⟨hhi0.le,le_rfl⟩,rfl⟩,Or.inl ⟨hi,⟨le_rfl,hhi1.le⟩,rfl⟩⟩
    refine ⟨C,R,hc,hr,hwhole,rfl,hinter,?_,rfl⟩
    intro k
    apply Set.disjoint_left.mpr
    intro z hzR hzC
    have hz := hinter ▸ (show z ∈ C ∩ R from ⟨hzC,hzR.1⟩)
    rcases mem_insert_iff.mp hz with he | he
    · exact hzR.2.2 (he.symm ▸ a.val.start_marked)
    · exact hportFree k ((mem_singleton_iff.mp he) ▸ hzR.2)
  have embedded_side_isArcBetween (f : C(Interval,Plane))
      (hf : IsEmbedding f) : IsArcBetween (range f) (f 0) (f 1) := by
    let fc : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
    have hfc : Continuous fc := f.continuous.comp continuous_projIcc
    have he (t : Interval) : fc t = f t := by
      simp [fc,Set.projIcc_of_mem zero_le_one t.property]
    refine ⟨fc,hfc.continuousOn,?_,?_,he 0,he 1⟩
    · intro t ht u hu h
      exact congrArg Subtype.val (hf.injective (by
        simpa only [← he] using h : f ⟨t,ht⟩ = f ⟨u,hu⟩))
    · ext x
      constructor
      · rintro ⟨t,ht,rfl⟩
        exact ⟨⟨t,ht⟩,(he ⟨t,ht⟩).symm⟩
      · rintro ⟨t,rfl⟩
        exact ⟨t,t.property,he t⟩
  
  have hrawDiskChart (f₀ f₁ : C(Interval,S)) (hf₀ : IsEmbedding f₀) (hf₁ : IsEmbedding f₁)
      (u0 z0 : S) (hf₀0 : f₀ 0=u0) (hf₁0 : f₁ 0=u0) (hf₀1 : f₀ 1=z0) (hf₁1 : f₁ 1=z0)
      (hinter : range f₀ ∩ range f₁ = {u0,z0})
      (disk : C(Metric.closedBall (0 : Plane) 1,S)) (hdisk : IsEmbedding disk)
      (hboundary : disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range f₀ ∪ range f₁)
      (w : S) (hw : w ∉ range disk) :
      ∃ (f : Plane → S) (A B : Set Plane) (p q : Plane),
        IsOpenEmbedding f ∧ IsArcBetween A p q ∧ IsArcBetween B p q ∧
        A ∪ B = modelCurve ∧ f '' A = range f₀ ∧ f '' B = range f₁ ∧
        f p=u0 ∧ f q=z0 ∧
        f '' Plane.openSquare 0 1 = disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1} := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    let v := w
    have hv : v ∉ range disk := hw
    let e := M.puncturedPlane v
    let j : range disk → {z : S // z ≠ v} :=
      fun z => ⟨z.val,fun hz => hv (hz ▸ z.property)⟩
    let d : C(Metric.closedBall (0 : Plane) 1,Plane) :=
      ⟨fun x => e ⟨disk x,fun h => hv (h ▸ Set.mem_range_self x)⟩,by fun_prop⟩
    have firstDisk (t : Interval) : f₀ t ∈ range disk := by
      apply image_subset_range disk _
      rw [hboundary]
      exact Or.inl (Set.mem_range_self t)
    have secondDisk (t : Interval) : f₁ t ∈ range disk := by
      apply image_subset_range disk _
      rw [hboundary]
      exact Or.inr (Set.mem_range_self t)
    let g : C(Interval,Plane) :=
      ⟨fun t => e ⟨f₀ t,fun h => hv (h ▸ firstDisk t)⟩,by fun_prop⟩
    let h : C(Interval,Plane) :=
      ⟨fun t => e ⟨f₁ t,fun hh => hv (hh ▸ secondDisk t)⟩,by fun_prop⟩
    have hd : IsEmbedding d := (d.continuous.isClosedEmbedding (by
      intro x y hxy
      exact hdisk.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
    have hg : IsEmbedding g := (g.continuous.isClosedEmbedding (by
      intro x y hxy
      exact hf₀.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
    have hh : IsEmbedding h := (h.continuous.isClosedEmbedding (by
      intro x y hxy
      exact hf₁.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
    have hg0 : g 0 = h 0 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact hf₀0.trans hf₁0.symm
    have hg1 : g 1 = h 1 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact hf₀1.trans hf₁1.symm
    have hgA := embedded_side_isArcBetween g hg
    have hhB : IsArcBetween (range h) (g 0) (g 1) := by rw [hg0,hg1]; exact embedded_side_isArcBetween h hh
    have hc : IsJordanCurve (range g ∪ range h) := IsJordanCurve.of_two_arcs hgA hhB.reverse (by
      rintro z ⟨t,ht⟩ ⟨s,hs⟩
      have heq : f₀ t = f₁ s := congrArg Subtype.val (e.injective (ht.trans hs.symm))
      have hm : f₀ t ∈ ({u0,z0} : Set S) :=
        hinter ▸ ⟨Set.mem_range_self t,⟨s,heq.symm⟩⟩
      rcases mem_insert_iff.mp hm with hm | hm
      · left
        have ht0 : t=0 := hf₀.injective (hm.trans hf₀0.symm)
        exact ht.symm.trans (congrArg g ht0)
      · right
        have ht1 : t=1 := hf₀.injective ((mem_singleton_iff.mp hm).trans hf₀1.symm)
        exact ht.symm.trans (congrArg g ht1))
    have hbd : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range g ∪ range h := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        have hxs : disk x ∈ range f₀ ∪ range f₁ := by
          rw [← hboundary]
          exact mem_image_of_mem disk hx
        rcases hxs with ⟨t,ht⟩ | ⟨t,ht⟩
        · left; refine ⟨t,?_⟩; apply congrArg e; apply Subtype.ext; exact ht
        · right; refine ⟨t,?_⟩; apply congrArg e; apply Subtype.ext; exact ht
      · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
        · have htB : f₀ t ∈ disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
            rw [hboundary]; exact Or.inl (Set.mem_range_self t)
          obtain ⟨x,hx,hxt⟩ := htB
          refine ⟨x,hx,?_⟩; apply congrArg e; apply Subtype.ext; exact hxt
        · have htB : f₁ t ∈ disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
            rw [hboundary]; exact Or.inr (Set.mem_range_self t)
          obtain ⟨x,hx,hxt⟩ := htB
          refine ⟨x,hx,?_⟩; apply congrArg e; apply Subtype.ext; exact hxt
    have hrange := CurveComplex.embedded_disc_range_eq_closed_inside d hd _ hc hbd
    have hi : d '' {x | x.val ∈ Metric.ball (0 : Plane) 1} = inside (range g ∪ range h) := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        rcases hrange ▸ Set.mem_range_self x with hi | hb
        · exact hi
        · obtain ⟨y,hy,hyx⟩ := hbd.symm ▸ hb
          have he := congrArg Subtype.val (hd.injective hyx)
          have hyxS : x.val ∈ Metric.sphere (0 : Plane) 1 := he ▸ hy
          have hnlt : ‖x.val‖ < (1 : ℝ) := by
            change dist x.val 0 < 1 at hx
            simpa only [dist_zero_right] using hx
          have hneq : ‖x.val‖ = (1 : ℝ) := by
            change dist x.val 0 = 1 at hyxS
            simpa only [dist_zero_right] using hyxS
          exact False.elim (ne_of_lt hnlt hneq)
      · intro hz
        have hzR : z ∈ range d := by rw [hrange]; exact Or.inl hz
        obtain ⟨x,hx⟩ := hzR
        refine ⟨x,?_,hx⟩
        have hn : ‖x.val‖ ≤ (1 : ℝ) := by
          simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
        have hnb : x.val ∉ Metric.sphere (0 : Plane) 1 := by
          intro hxb
          have hzB : z ∈ range g ∪ range h := by rw [← hbd,← hx]; exact mem_image_of_mem d hxb
          exact Set.disjoint_right.mp (disjoint_curve_inside _) hz hzB
        change dist x.val 0 < 1
        rw [dist_zero_right]
        exact lt_of_le_of_ne hn (by simpa only [Metric.mem_sphere,dist_zero_right] using hnb)
    obtain ⟨ec⟩ := IsJordanCurve.modelCurve_homeomorph hc
    obtain ⟨φ,hφ⟩ := jordan_schoenflies_of_homeomorph isJordanCurve_modelCurve hc ec
    have hφC : φ '' modelCurve = range g ∪ range h := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩; rw [hφ ⟨x,hx⟩]; exact (ec ⟨x,hx⟩).property
      · intro hz
        let x := ec.symm ⟨z,hz⟩
        refine ⟨x.val,x.property,?_⟩
        rw [hφ x]; exact congrArg Subtype.val (ec.apply_symm_apply _)
    have hφI : φ '' Plane.openSquare 0 1 = inside (range g ∪ range h) := by
      rw [← inside_modelCurve]
      simpa only [hφC] using CurveComplex.jordan_inside_homeomorph_image φ modelCurve
    let f : Plane → S := M.planeToSphere v ∘ φ
    let A := φ.symm '' range g
    let B := φ.symm '' range h
    let p := φ.symm (g 0)
    let q := φ.symm (g 1)
    have hcancel (K : Set Plane) : φ '' (φ.symm '' K) = K := by
      ext z; simp
    have hgs (t) : M.planeToSphere v (g t) = f₀ t := congrArg Subtype.val (e.symm_apply_apply _)
    have hhs (t) : M.planeToSphere v (h t) = f₁ t := congrArg Subtype.val (e.symm_apply_apply _)
    refine ⟨f,A,B,p,q,(M.planeToSphere_isOpenEmbedding v).comp φ.isOpenEmbedding,
      hgA.image_of_injOn (Set.subset_univ _) φ.symm.continuous.continuousOn φ.symm.injective.injOn,
      hhB.image_of_injOn (Set.subset_univ _) φ.symm.continuous.continuousOn φ.symm.injective.injOn,?_,?_,?_,?_,?_,?_⟩
    · change φ.symm '' range g ∪ φ.symm '' range h = modelCurve
      rw [← image_union,← hφC]
      ext z; simp
    · change (M.planeToSphere v ∘ φ) '' (φ.symm '' range g) = _
      rw [image_comp,hcancel,← range_comp]; exact congrArg range (funext hgs)
    · change (M.planeToSphere v ∘ φ) '' (φ.symm '' range h) = _
      rw [image_comp,hcancel,← range_comp]; exact congrArg range (funext hhs)
    · change M.planeToSphere v (φ (φ.symm (g 0))) = _
      rw [φ.apply_symm_apply,hgs,hf₀0]
    · change M.planeToSphere v (φ (φ.symm (g 1))) = _
      rw [φ.apply_symm_apply,hgs,hf₀1]
    · change (M.planeToSphere v ∘ φ) '' Plane.openSquare 0 1 = _
      rw [image_comp,hφI,← hi,image_image]
      apply Set.image_congr
      intro x hx
      exact congrArg Subtype.val (e.symm_apply_apply _)
  have hrelativeRawDiskMove
      (f₀ f₁ : C(Interval,S)) (hf₀ : IsEmbedding f₀) (hf₁ : IsEmbedding f₁)
      (u z : S) (hf₀0 : f₀ 0=u) (hf₁0 : f₁ 0=u) (hf₀1 : f₀ 1=z) (hf₁1 : f₁ 1=z)
      (hinter : range f₀ ∩ range f₁ = {u,z})
      (disk : C(Metric.closedBall (0 : Plane) 1,S)) (hdisk : IsEmbedding disk)
      (hboundary : disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range f₀ ∪ range f₁)
      (w : S) (hw : w ∉ range disk)
      (Q : Set S) (hQc : IsClosed Q)
      (hQboundary : ∀ y ∈ range f₀ ∪ range f₁, y ∈ Q → y=u ∨ y=z)
      (hQinside : Disjoint (disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) Q) :
      ∃ H : CurveComplex.AmbientIsotopy S,
        (∀ t y, y ∈ Q → H.map (t,y)=y) ∧ H.finalMap '' range f₀ = range f₁ := by
    obtain ⟨F,A,B,p,q,hF,hA,hB,hwhole,hFA,hFB,hFp,hFq,hFI⟩ :=
      hrawDiskChart f₀ f₁ hf₀ hf₁ u z hf₀0 hf₁0 hf₀1 hf₁1 hinter disk hdisk hboundary w hw
    have hb : ∀ x ∈ modelCurve, F x ∈ Q → x=p ∨ x=q := by
      intro x hx hxQ
      have hxB : F x ∈ range f₀ ∪ range f₁ := by
        rw [← hFA,← hFB,← image_union,hwhole]
        exact mem_image_of_mem F hx
      rcases hQboundary (F x) hxB hxQ with hxu | hxz
      · exact Or.inl (hF.injective (hxu.trans hFp.symm))
      · exact Or.inr (hF.injective (hxz.trans hFq.symm))
    obtain ⟨H,hfix,hmove⟩ := CurveComplex.actual_raw_bigon_supported_replacement F hF A B p q
      hA hB hwhole Q hQc hb (by rwa [hFI])
    exact ⟨H,hfix,by simpa only [hFA,hFB] using hmove⟩
  have hretainedRemainderExterior (hi : ℝ) (hhi0 : 0 < hi) (hhi1 : hi < 1)
      (B Ω : Set S)
      (hBmeet : B ∩ a.val.image = {a.val.map 0,a.val.map (projIcc 0 1 zero_le_one hi)})
      (hΩ : IsConnected Ω)
      (hΩfree : Ω ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ B)ᶜ)
      (hΩmax : ∀ V : Set S, IsConnected V → Ω ⊆ V →
        V ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ B)ᶜ → V=Ω)
      (hΩmarks : Disjoint Ω (M.cover.branch : Set S)) :
      Disjoint Ω (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc hi 1) ∪ {a.val.map 0}) := by
    let g : ℝ → S := a.val.map ∘ projIcc 0 1 zero_le_one
    let Tail : Set S := g '' Ioc hi 1
    have hg : Continuous g := a.val.continuous.comp continuous_projIcc
    have hTail : IsConnected Tail := (isConnected_Ioc hhi1).image g hg.continuousOn
    have hfreeTail : Tail ⊆ ((g '' Icc 0 hi) ∪ B)ᶜ := by
      rintro z ⟨t,ht,rfl⟩ hz
      have htI : t ∈ Icc (0:ℝ) 1 := ⟨(hhi0.trans ht.1).le,ht.2⟩
      have hinj := NonLoopArc.injective ⟨a.val,actualRepresentative_nonloop M a ha⟩
      rcases hz with hz | hz
      · obtain ⟨u,hu,he⟩ := hz
        have huI : u ∈ Icc (0:ℝ) 1 := ⟨hu.1,hu.2.trans hhi1.le⟩
        have hh := congrArg Subtype.val (hinj he)
        have htu : u=t := by simpa only [g,Function.comp_apply,projIcc_of_mem zero_le_one huI,projIcc_of_mem zero_le_one htI,show ((0:Interval):ℝ)=0 from rfl] using hh
        exact (not_le_of_gt ht.1) (htu ▸ hu.2)
      · have hm : g t ∈ ({a.val.map 0,a.val.map (projIcc 0 1 zero_le_one hi)} : Set S) :=
          hBmeet ▸ ⟨hz,mem_range_self _⟩
        rcases mem_insert_iff.mp hm with he | he
        · have hh := congrArg Subtype.val (hinj he)
          have ht0 : t=0 := by simpa only [g,Function.comp_apply,projIcc_of_mem zero_le_one htI,show ((0:Interval):ℝ)=0 from rfl] using hh
          linarith [ht.1]
        · have hh := congrArg Subtype.val (hinj (mem_singleton_iff.mp he))
          have hthi : t=hi := by simpa only [g,Function.comp_apply,projIcc_of_mem zero_le_one htI,projIcc_of_mem zero_le_one ⟨hhi0.le,hhi1.le⟩] using hh
          exact (ne_of_gt ht.1) hthi
    have hd : Disjoint Ω Tail := by
      apply Set.disjoint_left.mpr
      intro z hzΩ hzT
      have hconn : IsConnected (Ω ∪ Tail) := IsConnected.union ⟨z,hzΩ,hzT⟩ hΩ hTail
      have heq := hΩmax (Ω ∪ Tail) hconn subset_union_left (union_subset hΩfree hfreeTail)
      have hendT : a.val.map 1 ∈ Tail := by
        exact ⟨1,⟨hhi1,le_rfl⟩,by simp [g]⟩
      have hendΩ : a.val.map 1 ∈ Ω := heq ▸ Or.inr hendT
      exact Set.disjoint_left.mp hΩmarks hendΩ a.val.end_marked
    apply Set.disjoint_left.mpr
    intro z hzΩ hzR
    rcases hzR with hzR | hzR
    · obtain ⟨t,ht,rfl⟩ := hzR
      by_cases he : t=hi
      · exact hΩfree hzΩ (Or.inl ⟨t,⟨hhi0.le.trans he.ge,he.le⟩,rfl⟩)
      · exact Set.disjoint_left.mp hd hzΩ ⟨t,⟨lt_of_le_of_ne ht.1 (Ne.symm he),ht.2⟩,rfl⟩
    · have he := mem_singleton_iff.mp hzR
      exact hΩfree hzΩ (Or.inl ⟨0,⟨le_rfl,hhi0.le⟩,by simpa [g] using he.symm⟩)
  have hHalfDiskClosedPieceAssembly
      (α hi : ℝ) (hα : 0 < α) (hαhi : α < hi) (hhi : hi < 1)
      (hprefix : range D.firstSide = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 α)
      (g : C(Interval,S)) (hg : IsEmbedding g) (hg0 : g 0=a.val.map 0)
      (hg1 : g 1=a.val.map (projIcc 0 1 zero_le_one hi))
      (hgfree : ∀ k, Disjoint (range g) (arcInterior M (old k)))
      (hgmeet : range g ∩ a.val.image = {a.val.map 0,g 1})
      (hgmarks : ∀ t, t ≠ 0 → g t ∉ M.cover.branch)
      (hgN : range g ⊆ interior N.closedSet)
      (disk : C(Metric.closedBall (0 : Plane) 1,S)) (hdisk : IsEmbedding disk)
      (hboundary : disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} =
        (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi ∪ range g)
      (hinside : Disjoint (disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1})
        ((M.cover.branch : Set S) ∪
          ((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc hi 1 ∪ {a.val.map 0})))
      (w : S) (hw : w ∉ range disk) :
      ∃ (H : CurveComplex.AmbientIsotopy S) (C B R : Set S),
        (∀ t p, p ∈ M.cover.branch → H.map (t,p)=p) ∧
        IsCompact C ∧ IsCompact B ∧
        a.val.image=C ∪ R ∧ H.finalMap '' a.val.image=B ∪ R ∧
        (∀ k, Disjoint B (arcInterior M (old k))) ∧
        (∀ k, Disjoint (R ∩ arcInterior M (old k)) C) ∧
        (ArcSurgery.crossings M (old i) a ∩ C).Nonempty ∧
        (∀ t p, p ∉ interior N.closedSet → H.map (t,p)=p) := by
    have hhi0 : 0 < hi := hα.trans hαhi
    have hportFree : ∀ k, a.val.map (projIcc 0 1 zero_le_one hi) ∉ arcInterior M (old k) := by
      intro k hk
      exact Set.disjoint_left.mp (hgfree k) (hg1 ▸ mem_range_self 1) hk
    obtain ⟨C,R,hC,hR,hwhole,hCeq,hCR,hretained,hReq⟩ := hcoreAtPort hi hhi0 hhi hportFree
    let q : Interval → Interval := fun t => ⟨hi*(t:ℝ),
      ⟨mul_nonneg hhi0.le t.property.1,
        (mul_le_of_le_one_right hhi0.le t.property.2).trans hhi.le⟩⟩
    have hqcont : Continuous q := by dsimp [q]; fun_prop
    let c : C(Interval,S) := ⟨fun t => a.val.map (q t),a.val.continuous.comp hqcont⟩
    have hc : IsEmbedding c := (c.continuous.isClosedEmbedding (by
      intro t u he
      have hh := NonLoopArc.injective ⟨a.val,actualRepresentative_nonloop M a ha⟩ he
      apply Subtype.ext
      exact mul_left_cancel₀ (ne_of_gt hhi0) (congrArg Subtype.val hh))).isEmbedding
    have hc0 : c 0=a.val.map 0 := by
      change a.val.map (q 0)=a.val.map 0
      congr 1; apply Subtype.ext; dsimp [q]; norm_num
    have hc1 : c 1=a.val.map (projIcc 0 1 zero_le_one hi) := by
      change a.val.map (q 1)=a.val.map (projIcc 0 1 zero_le_one hi)
      congr 1; apply Subtype.ext
      rw [projIcc_of_mem zero_le_one ⟨hhi0.le,hhi.le⟩]
      dsimp [q]; norm_num
    have hcR : range c=C := by
      rw [hCeq]
      apply Subset.antisymm
      · rintro y ⟨t,rfl⟩
        refine ⟨hi*(t:ℝ),⟨mul_nonneg hhi0.le t.property.1,
          mul_le_of_le_one_right hhi0.le t.property.2⟩,?_⟩
        rw [Function.comp_apply,projIcc_of_mem zero_le_one (q t).property]
        rfl
      · rintro y ⟨x,hx,rfl⟩
        let tx : Interval := ⟨x/hi,⟨div_nonneg hx.1 hhi0.le,(div_le_one hhi0).mpr hx.2⟩⟩
        refine ⟨tx,?_⟩
        change a.val.map (q tx)=a.val.map (projIcc 0 1 zero_le_one x)
        congr 1; apply Subtype.ext
        rw [projIcc_of_mem zero_le_one ⟨hx.1,hx.2.trans hhi.le⟩]
        change hi*(x/hi)=x
        field_simp
    have hCa : C ⊆ a.val.image := by rw [hwhole]; exact subset_union_left
    have hRa : R ⊆ a.val.image := by rw [hwhole]; exact subset_union_right
    have hmeet : range c ∩ range g = {a.val.map 0,g 1} := by
      rw [hcR]
      apply Subset.antisymm
      · intro y hy
        exact hgmeet ▸ ⟨hy.2,hCa hy.1⟩
      · intro y hy
        have hyends : y ∈ ({a.val.map 0,a.val.map (projIcc 0 1 zero_le_one hi)} : Set S) := by
          simpa only [hg1] using hy
        have hyC : y ∈ C := (hCR.symm ▸ hyends).1
        have hyg : y ∈ range g := by
          rcases mem_insert_iff.mp hy with he | he
          · exact ⟨0,hg0.trans he.symm⟩
          · exact ⟨1,(mem_singleton_iff.mp he).symm⟩
        exact ⟨hyC,hyg⟩
    have hcross (t u : Interval) (he : c t=g u) : (t=0 ∧ u=0) ∨ (t=1 ∧ u=1) := by
      have hz : c t ∈ ({a.val.map 0,g 1}:Set S) := hmeet ▸ ⟨⟨t,rfl⟩,⟨u,he.symm⟩⟩
      rcases mem_insert_iff.mp hz with hz | hz
      · exact Or.inl ⟨hc.injective (hz.trans hc0.symm),hg.injective (he.symm.trans (hz.trans hg0.symm))⟩
      · have hz := mem_singleton_iff.mp hz
        exact Or.inr ⟨hc.injective (hz.trans (hc1.trans hg1.symm).symm),hg.injective (he.symm.trans hz)⟩
    obtain ⟨curve,hcurve⟩ := CurveComplex.exists_curve_of_two_arcs c g hc.injective hg.injective
      (hc0.trans hg0.symm) (hc1.trans hg1.symm) hcross
    have hcurveN : curve.image ⊆ interior N.closedSet := by
      rw [hcurve,hcR]
      exact union_subset (hCa.trans haN) hgN
    have hdiskN : range disk ⊆ interior N.closedSet :=
      marked_free_disk_with_boundary_inside_original_neighborhood_is_inside M n N curve hcurveN
        disk hdisk (by simpa only [hcurve,hcR,hCeq] using hboundary)
        (hinside.mono_right subset_union_left)
    let Q : Set S := ((M.cover.branch : Set S) ∪ R) ∪ (interior N.closedSet)ᶜ
    have hQc : IsClosed Q := (M.cover.branch.isClosed.union hR.isClosed).union isOpen_interior.isClosed_compl
    have hQboundary : ∀ y ∈ range c ∪ range g, y ∈ Q → y=a.val.map 0 ∨ y=g 1 := by
      intro y hy hyQ
      have hyQold : y ∈ (M.cover.branch:Set S) ∪ R := by
        rcases hyQ with hyQ | hyOut
        · exact hyQ
        · have hyIn : y ∈ interior N.closedSet := by
            rcases hy with hyc | hyg
            · exact haN (hCa (hcR ▸ hyc))
            · exact hgN hyg
          exact False.elim (hyOut hyIn)
      rcases hyQold with hym | hyr
      · rcases hy with hyc | hyg
        · obtain ⟨t,rfl⟩ := hyc
          rcases a.val.marked_only_at_ends (q t) hym with he | he
          · exact Or.inl (congrArg a.val.map he)
          · have hh : hi*(t:ℝ)=1 := congrArg Subtype.val he
            have hle := mul_le_of_le_one_right hhi0.le t.property.2
            linarith
        · obtain ⟨t,rfl⟩ := hyg
          by_cases ht : t=0
          · subst t; exact Or.inl hg0
          · exact False.elim (hgmarks t ht hym)
      · rcases hy with hyc | hyg
        · have hyends : y ∈ ({a.val.map 0,a.val.map (projIcc 0 1 zero_le_one hi)} : Set S) :=
            hCR ▸ (show y ∈ C ∩ R from ⟨hcR ▸ hyc,hyr⟩)
          simpa only [mem_insert_iff,mem_singleton_iff,← hg1] using hyends
        · have hyends : y ∈ ({a.val.map 0,g 1} : Set S) :=
            hgmeet ▸ (show y ∈ range g ∩ a.val.image from ⟨hyg,hRa hyr⟩)
          simpa only [mem_insert_iff,mem_singleton_iff] using hyends
    obtain ⟨H,hfix,hmove⟩ := hrelativeRawDiskMove c g hc hg
      (a.val.map 0) (g 1) hc0 hg0 (hc1.trans hg1.symm) rfl hmeet disk hdisk
      (by simpa only [hcR,hCeq] using hboundary) w hw Q hQc hQboundary
      (by
        apply disjoint_union_right.mpr
        constructor
        · simpa only [hReq] using hinside
        · apply disjoint_left.mpr
          intro x hx hxOut
          exact hxOut (hdiskN (image_subset_range _ _ hx)))
    have hRmove : H.finalMap '' R=R := by
      apply Subset.antisymm
      · rintro y ⟨x,hx,rfl⟩
        have he := hfix 1 x (Or.inl (Or.inr hx))
        change H.finalMap x=x at he
        rw [he]
        exact hx
      · intro y hy
        exact ⟨y,hy,hfix 1 y (Or.inl (Or.inr hy))⟩
    refine ⟨H,C,range g,R,fun t p hp => hfix t p (Or.inl (Or.inl hp)),hC,
      (by simpa only [image_univ] using isCompact_univ.image g.continuous),hwhole,?_,hgfree,hretained,?_,?_⟩
    · rw [hwhole,image_union,← hcR,hmove,hRmove]
    · refine ⟨D.secondCorner,hlastCrossing,?_⟩
      have hqprefix : D.secondCorner ∈ (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 α :=
        hprefix ▸ ⟨1,D.first_one⟩
      rw [hCeq]
      exact image_mono (Icc_subset_Icc_right hαhi.le) hqprefix
    · exact fun t p hp => hfix t p (Or.inr hp)
  have hHalfEmptyJordanRegionDiskAssembly
      (α hi : ℝ) (hα : 0 < α) (hαhi : α < hi) (hhi : hi < 1)
      (hprefix : range D.firstSide = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 α)
      (g : C(Interval,S)) (hg : IsEmbedding g) (hg0 : g 0=a.val.map 0)
      (hg1 : g 1=a.val.map (projIcc 0 1 zero_le_one hi))
      (hgfree : ∀ k, Disjoint (range g) (arcInterior M (old k)))
      (hgmeet : range g ∩ a.val.image = {a.val.map 0,g 1})
      (hgmarks : ∀ t, t ≠ 0 → g t ∉ M.cover.branch)
      (hgN : range g ⊆ interior N.closedSet)
      (Ω : Set S) (hΩ : IsConnected Ω)
      (hΩfree : Ω ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ)
      (hΩmax : ∀ V : Set S, IsConnected V → Ω ⊆ V →
        V ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ → V=Ω)
      (hΩmarks : Disjoint Ω (M.cover.branch : Set S))
      (disk : C(Metric.closedBall (0 : Plane) 1,S)) (hdisk : IsEmbedding disk)
      (hboundary : disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} =
        (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi ∪ range g)
      (hinterior : disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}=Ω) :
      ∃ (H : CurveComplex.AmbientIsotopy S) (C B R : Set S),
        (∀ t p, p ∈ M.cover.branch → H.map (t,p)=p) ∧
        IsCompact C ∧ IsCompact B ∧
        a.val.image=C ∪ R ∧ H.finalMap '' a.val.image=B ∪ R ∧
        (∀ k, Disjoint B (arcInterior M (old k))) ∧
        (∀ k, Disjoint (R ∩ arcInterior M (old k)) C) ∧
        (ArcSurgery.crossings M (old i) a ∩ C).Nonempty ∧
        (∀ t p, p ∉ interior N.closedSet → H.map (t,p)=p) := by
    have hhi0 : 0 < hi := hα.trans hαhi
    have hΩR := hretainedRemainderExterior hi hhi0 hhi (range g) Ω
      (by simpa only [hg1] using hgmeet) hΩ hΩfree hΩmax hΩmarks
    have hinside : Disjoint (disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1})
        ((M.cover.branch : Set S) ∪
          ((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc hi 1 ∪ {a.val.map 0})) := by
      rw [hinterior]
      exact disjoint_union_right.mpr ⟨hΩmarks,hΩR⟩
    have hwBoundary : a.val.map 1 ∉
        (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi ∪ range g := by
      intro hw
      have hinj := NonLoopArc.injective ⟨a.val,actualRepresentative_nonloop M a ha⟩
      rcases hw with hw | hw
      · obtain ⟨t,ht,he⟩ := hw
        have hh := congrArg Subtype.val (hinj he)
        have ht1 : t=1 := by
          simpa only [Function.comp_apply,projIcc_of_mem zero_le_one ⟨ht.1,ht.2.trans hhi.le⟩,
            show ((1:Interval):ℝ)=1 from rfl] using hh
        exact not_le_of_gt hhi (ht1 ▸ ht.2)
      · have he : a.val.map 1 ∈ ({a.val.map 0,g 1} : Set S) :=
          hgmeet ▸ (show a.val.map 1 ∈ range g ∩ a.val.image from ⟨hw,mem_range_self 1⟩)
        rcases mem_insert_iff.mp he with he | he
        · have hh := congrArg Subtype.val (hinj he)
          norm_num at hh
        · have hh := congrArg Subtype.val (hinj ((mem_singleton_iff.mp he).trans hg1))
          have hh' : (1:ℝ)=hi := by
            simpa only [projIcc_of_mem zero_le_one ⟨hhi0.le,hhi.le⟩,
              show ((1:Interval):ℝ)=1 from rfl] using hh
          linarith
    have hw : a.val.map 1 ∉ range disk := by
      rintro ⟨x,hx⟩
      have hxle : dist x.val 0 ≤ (1:ℝ) := x.property
      rcases lt_or_eq_of_le hxle with hxlt | hxeq
      · have hwΩ : a.val.map 1 ∈ Ω := hinterior ▸ ⟨x,hxlt,hx⟩
        exact Set.disjoint_left.mp hΩmarks hwΩ a.val.end_marked
      · have hwB : a.val.map 1 ∈
            (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi ∪ range g :=
          hboundary ▸ ⟨x,hxeq,hx⟩
        exact hwBoundary hwB
    exact hHalfDiskClosedPieceAssembly α hi hα hαhi hhi hprefix g hg hg0 hg1
      hgfree hgmeet hgmarks hgN disk hdisk hboundary hinside (a.val.map 1) hw
  have hNormalizedHalfOperation (hbaseB : D.firstCorner=(old i).val.map 0)
      (hbaseA : D.firstCorner=a.val.map 0) :
      ∃ (H : CurveComplex.AmbientIsotopy S) (C B R : Set S),
        (∀ t p, p ∈ M.cover.branch → H.map (t,p)=p) ∧
        IsCompact C ∧ IsCompact B ∧
        a.val.image=C ∪ R ∧ H.finalMap '' a.val.image=B ∪ R ∧
        (∀ k, Disjoint B (arcInterior M (old k))) ∧
        (∀ k, Disjoint (R ∩ arcInterior M (old k)) C) ∧
        (ArcSurgery.crossings M (old i) a ∩ C).Nonempty ∧
        (∀ t p, p ∉ interior N.closedSet → H.map (t,p)=p) := by
    obtain ⟨α,hi,g,Ω,hα,hαhi,hhi,hprefix,hg,hg0,hg1,hgfree,hgmeet,hgport,hgmarks,
      hΩne,hΩ,hΩfree,hΩmax,hfrontier,hΩmarks,hgN⟩ := localized_marked_nonloop_empty_disk_produces_retained_supporting_region M old hold hd a ha hfinite i D hlast hempty hbaseB hbaseA (interior N.closedSet) isOpen_interior holdN
    obtain ⟨disk,hdisk,hboundary,hinterior⟩ := actual_retained_nonloop_jordan_region_produces_supporting_disk M a ha hi (hα.trans hαhi) hhi
      g hg hg0 hg1 hgmeet Ω hΩne hΩ hΩfree hΩmax hfrontier hΩmarks
    exact hHalfEmptyJordanRegionDiskAssembly α hi hα hαhi hhi hprefix g hg hg0 hg1
      hgfree hgmeet hgmarks hgN Ω hΩ hΩfree hΩmax hΩmarks disk hdisk hboundary hinterior
  exact hNormalizedHalfOperation hbaseB hbaseA

end CurveComplex.HyperellipticModel


namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem supported_closed_piece_contact_drop_assembly
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p)
    (H : CurveComplex.AmbientIsotopy S)
    (hsupport : ∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x)
    (hm : ∀ t x, x ∈ M.cover.branch → H.map (t,x)=x)
    (C B R : Set S) (hC : IsCompact C) (hB : IsCompact B)
    (hOld : b.image=C ∪ R) (hNew : H.finalMap '' b.image=B ∪ R)
    (hBfree : Disjoint B (arcInterior M a.toEssential))
    (hRfree : Disjoint (R ∩ arcInterior M a.toEssential) C)
    (hremoved : (ArcSurgery.crossings M a.toEssential b.toEssential ∩ C).Nonempty) :
    ∃ b' : NonLoopArc M,
      H.finalMap '' b.image=b'.image ∧ b'.image ⊆ interior N.closedSet ∧
      ({b'.val.map 0,b'.val.map 1}:Set S) = {b.val.map 0,b.val.map 1} ∧
      (ArcSurgery.crossings M a.toEssential b'.toEssential).Finite ∧
      (∀ p ∈ ArcSurgery.crossings M a.toEssential b'.toEssential,
        ArcSurgery.CrossesInDisk M a.toEssential b'.toEssential p) ∧
      (ArcSurgery.crossings M a.toEssential b'.toEssential).ncard <
        (ArcSurgery.crossings M a.toEssential b.toEssential).ncard := by
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨g,hg⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
  have hgfix : ∀ p, p ∈ M.cover.branch → g p=p :=
    fun p hp => (hg p).trans (hm _ p hp)
  let b' : NonLoopArc M := ⟨b.val.transport g hgfix, fun he => b.property (g.injective he)⟩
  have hcimage : b'.image=H.finalMap '' b.image := by
    change (b.val.transport g hgfix).image=_
    rw [MarkedArc.transport_image]
    exact congrArg (fun f : S → S => f '' b.image) (funext hg)
  have hdecomp : b'.toEssential.val.image=B ∪ R := hcimage.trans hNew
  have hOldE : b.toEssential.val.image=C ∪ R := hOld
  have hretain (p : S) (hp : p ∈ ArcSurgery.crossings M a.toEssential b'.toEssential) :
      p ∈ R ∧ p ∉ C ∪ B := by
    have hpR : p ∈ R := (hdecomp ▸ hp.2.1).resolve_left
      (fun hpB => disjoint_left.mp hBfree hpB hp.1)
    refine ⟨hpR,?_⟩
    rintro (hpC | hpB)
    · exact disjoint_left.mp hRfree ⟨hpR,hp.1⟩ hpC
    · exact disjoint_left.mp hBfree hpB hp.1
  have hsub : ArcSurgery.crossings M a.toEssential b'.toEssential ⊆
      ArcSurgery.crossings M a.toEssential b.toEssential := by
    intro p hp
    exact ⟨hp.1,⟨hOldE.symm ▸ Or.inr (hretain p hp).1,hp.2.2⟩⟩
  have htrans : ∀ p ∈ ArcSurgery.crossings M a.toEssential b'.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b'.toEssential p := by
    intro p hp
    have hsource := actual_marked_crossesInDisk_symm M a.toEssential b.toEssential p
      (hcross p (hsub hp))
    have hchanged := actual_closed_replacement_retained_marked_crossing M b.toEssential
      b'.toEssential a.toEssential C B R hC.isClosed hB.isClosed hOld hdecomp p
      hsource (hretain p hp).2
    exact actual_marked_crossesInDisk_symm M b'.toEssential a.toEssential p hchanged
  refine ⟨b',hcimage.symm,?_,?_,hfinite.subset hsub,htrans,?_⟩
  · rw [hcimage]
    rintro y ⟨x,hx,heq⟩
    by_contra hy
    have hgy : g y=y := (hg y).trans (hsupport 1 y hy)
    have he : x=y := g.injective ((hg x).trans (heq.trans hgy.symm))
    exact hy (he ▸ hb hx)
  · change ({g (b.val.map 0),g (b.val.map 1)}:Set S)=_
    have h0 : g (b.val.map 0)=b.val.map 0 := hgfix _ b.val.start_marked
    have h1 : g (b.val.map 1)=b.val.map 1 := hgfix _ b.val.end_marked
    rw [h0,h1]
  · apply ncard_lt_ncard _ hfinite
    apply ssubset_iff_subset_ne.mpr
    refine ⟨hsub,?_⟩
    intro heq
    obtain ⟨p,hp,hpC⟩ := hremoved
    have hpnew := heq.symm ▸ hp
    exact (hretain p hpnew).2 (Or.inl hpC)

#print axioms supported_closed_piece_contact_drop_assembly
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
private theorem normalized_actual_endpoint_disk_supported_strict_drop
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p)
    (D : ActualMarkedTwoSideDisk M b.toEssential a.toEssential)
    (hlast : D.secondCorner ∉ M.cover.branch)
    (hempty : Disjoint D.openInterior (b.image ∪ a.image))
    (hbaseA : D.firstCorner=a.val.map 0) (hbaseB : D.firstCorner=b.val.map 0) :
    ∃ b' : NonLoopArc M, ∃ H : CurveComplex.AmbientIsotopy S,
      (∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
      H.finalMap '' b.image=b'.image ∧ b'.image ⊆ interior N.closedSet ∧
      ({b'.val.map 0,b'.val.map 1}:Set S) = {b.val.map 0,b.val.map 1} ∧
      (ArcSurgery.crossings M a.toEssential b'.toEssential).Finite ∧
      (∀ p ∈ ArcSurgery.crossings M a.toEssential b'.toEssential,
        ArcSurgery.CrossesInDisk M a.toEssential b'.toEssential p) ∧
      (ArcSurgery.crossings M a.toEssential b'.toEssential).ncard <
        (ArcSurgery.crossings M a.toEssential b.toEssential).ncard := by
  classical
  have hnonloop (v : NonLoopArc M) : ¬ (actualArcLabels M).isLoop
      (Quotient.mk (essentialArcSetoid M) v.toEssential) := by
    change (classEndpoints M (Quotient.mk (essentialArcSetoid M) v.toEssential)).card ≠ 1
    rw [← markedArcEndset_eq_classEndpoints]
    change ({v.val.map 0,v.val.map 1}:Finset S).card ≠ 1
    have hv : v.val.map (0:Interval) ≠ v.val.map 1 := v.property
    simp [hv]
  obtain ⟨H,C,B,R,hm,hC,hB,hOld,hNew,hBfree,hRfree,hremoved,hsupport⟩ :=
    localized_normalized_marked_nonloop_empty_disk_relative_closed_piece_replacement
      M (fun _ : Unit => a.toEssential) (fun _ => hnonloop a)
      (fun k l hkl => False.elim (hkl (Subsingleton.elim k l)))
      b.toEssential (hnonloop b) (fun _ => ⟨hfinite,hcross⟩) () D hlast
      (by simpa only [iUnion_const] using (show Disjoint D.openInterior (b.toEssential.val.image ∪ a.toEssential.val.image) from hempty)) hbaseA hbaseB a N hb N.arc_inside
  obtain ⟨b',himage,hinside,hends,hfin,htrans,hdrop⟩ :=
    supported_closed_piece_contact_drop_assembly M a b N hb hfinite hcross
      H hsupport hm C B R hC hB hOld hNew (hBfree ()) (hRfree ()) hremoved
  exact ⟨b',H,hsupport,hm,himage,hinside,hends,hfin,htrans,hdrop⟩
#print axioms normalized_actual_endpoint_disk_supported_strict_drop
private theorem actual_first_marked_endpoint_disk_supported_closed_piece_replacement
    (M : HyperellipticModel E S) (a b : NonLoopArc M) (N : ArcNeighborhood a)
    (hb : b.image ⊆ interior N.closedSet)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p)
    (D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (h0 : D.firstCorner ∈ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
    (hempty : Disjoint D.openInterior (a.image ∪ b.image)) :
    ∃ (H : CurveComplex.AmbientIsotopy S) (C B R : Set S),
      (∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
      IsCompact C ∧ IsCompact B ∧ b.image=C ∪ R ∧
      H.finalMap '' b.image=B ∪ R ∧ Disjoint B (arcInterior M a.toEssential) ∧
      Disjoint (R ∩ arcInterior M a.toEssential) C ∧
      (ArcSurgery.crossings M a.toEssential b.toEssential ∩ C).Nonempty := by
  classical
  have hnormalizes (c : EssentialMarkedArc M) (hp : D.firstCorner ∈ c.val.image) :
      ∃ c' : EssentialMarkedArc M, c'.val.image=c.val.image ∧
        Quotient.mk (essentialArcSetoid M) c'=Quotient.mk (essentialArcSetoid M) c ∧
        c'.val.map 0=D.firstCorner := by
    obtain ⟨t,ht⟩ := hp
    rcases c.val.marked_only_at_ends t (ht.symm ▸ h0) with he | he
    · subst t
      exact ⟨c,rfl,rfl,ht⟩
    · subst t
      exact ⟨c.reverse,c.reverse_image,c.reverse_class,by simpa using ht⟩
  obtain ⟨a',haImage,haClass,haBase⟩ := hnormalizes a.toEssential (D.first_on_curve ⟨0,D.first_zero⟩)
  obtain ⟨b',hbImage,hbClass,hbBase⟩ := hnormalizes b.toEssential (D.second_on_curve ⟨0,D.second_zero⟩)
  have hnonloop (v : NonLoopArc M) : ¬ (actualArcLabels M).isLoop
      (Quotient.mk (essentialArcSetoid M) v.toEssential) := by
    change (classEndpoints M (Quotient.mk (essentialArcSetoid M) v.toEssential)).card ≠ 1
    rw [← markedArcEndset_eq_classEndpoints]
    change ({v.val.map 0,v.val.map 1}:Finset S).card ≠ 1
    have hv : v.val.map (0:Interval) ≠ v.val.map 1 := v.property
    simp [hv]
  have haNonloop : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) a') := by rw [haClass]; exact hnonloop a
  have hbNonloop : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) b') := by rw [hbClass]; exact hnonloop b
  let D' : ActualMarkedTwoSideDisk M b' a' := {
    firstCorner := D.firstCorner
    secondCorner := D.secondCorner
    firstSide := D.secondSide
    secondSide := D.firstSide
    first_embedded := D.second_embedded
    second_embedded := D.first_embedded
    first_zero := D.second_zero
    first_one := D.second_one
    second_zero := D.first_zero
    second_one := D.first_one
    first_on_curve := hbImage.symm ▸ D.second_on_curve
    second_on_curve := haImage.symm ▸ D.first_on_curve
    sides_inter := by rw [inter_comm]; exact D.sides_inter
    disk := D.disk
    disk_embedded := D.disk_embedded
    boundary_eq := D.boundary_eq.trans (union_comm _ _)
    marks_are_corners := D.marks_are_corners }
  have hcrossEq : ArcSurgery.crossings M a' b'=ArcSurgery.crossings M a.toEssential b.toEssential := by
    simp only [ArcSurgery.crossings,arcInterior,haImage,hbImage]
  have hcross' : ∀ p ∈ ArcSurgery.crossings M a' b', ArcSurgery.CrossesInDisk M a' b' p := by
    intro p hp
    unfold ArcSurgery.CrossesInDisk
    rw [haImage,hbImage]
    exact hcross p (hcrossEq ▸ hp)
  have hempty' : Disjoint D'.openInterior (b'.val.image ∪ ⋃ _ : Unit, a'.val.image) := by
    change Disjoint D.openInterior (b'.val.image ∪ ⋃ _ : Unit, a'.val.image)
    rw [iUnion_const,haImage,hbImage,union_comm]
    exact hempty
  obtain ⟨H,C,B,R,hm,hC,hB,hOld,hNew,hBfree,hRfree,hremoved,hsupport⟩ :=
    localized_normalized_marked_nonloop_empty_disk_relative_closed_piece_replacement M
      (fun _ : Unit => a') (fun _ => haNonloop)
      (fun k l hkl => False.elim (hkl (Subsingleton.elim k l))) b' hbNonloop
      (fun _ => ⟨hcrossEq.symm ▸ hfinite,hcross'⟩) () D' h1 hempty'
      haBase.symm hbBase.symm a N (hbImage.symm ▸ hb) (haImage.symm ▸ N.arc_inside)
  refine ⟨H,C,B,R,hsupport,hm,hC,hB,?_,?_,?_,?_,?_⟩
  · change b.toEssential.val.image = C ∪ R
    simpa only [hbImage] using hOld
  · change H.finalMap '' b.toEssential.val.image = B ∪ R
    simpa only [hbImage] using hNew
  · simpa only [arcInterior,haImage] using hBfree ()
  · simpa only [arcInterior,haImage] using hRfree ()
  · simpa only [hcrossEq] using hremoved

#print axioms actual_first_marked_endpoint_disk_supported_closed_piece_replacement
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem actual_inner_disk_two_corner_framing_inside_original_neighborhood
    (M : HyperellipticModel E S) (a b : NonLoopArc M) (N : ArcNeighborhood a)
    (D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
    (hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p) :
    ∃ (θ : Bool → Interval) (F : Bool → OpenPartialHomeomorph S Plane)
      (R : Interval × Icc (-1:ℝ) 1 → S),
      (∀ k, a.val.map (θ k) = if k then D.secondCorner else D.firstCorner) ∧
      Function.Injective θ ∧ (∀ k, 0 < (θ k:ℝ) ∧ (θ k:ℝ) < 1) ∧
      (∀ k, (F k).source ⊆ interior N.closedSet ∧
        Disjoint (F k).source (M.cover.branch:Set S) ∧ a.val.map (θ k) ∈ (F k).source ∧
        F k (a.val.map (θ k)) = 0 ∧
        (∀ x ∈ (F k).source, x ∈ a.image ↔ F k x 1=0) ∧
        (∀ x ∈ (F k).source, x ∈ b.image ↔ F k x 0=0)) ∧
      IsEmbedding R ∧ range R ⊆ interior N.closedSet ∧
      (∀ t, R (t,⟨0,by norm_num⟩)=a.val.map t) ∧
      ∃ σ δ η : Bool → ℝ,
        (∀ k, σ k = -1 ∨ σ k=1) ∧ (∀ k, 0 < δ k ∧ 0 < η k) ∧
        ∀ k (t : Interval) (v : Icc (-1:ℝ) 1), |(t:ℝ)-(θ k:ℝ)| < η k →
          R (t,v) ∈ (F k).source ∧
          F k (R (t,v)) = Plane.mk (F k (a.val.map t) 0) (σ k*δ k*(v:ℝ)) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  letI : CurveComplex.ClosedSurface S := {}
  let corner : Bool → S := fun k => if k then D.secondCorner else D.firstCorner
  have hcornerA (k : Bool) : corner k ∈ a.image := by
    cases k
    · exact D.first_on_curve ⟨0,D.first_zero⟩
    · exact D.first_on_curve ⟨1,D.first_one⟩
  have hcornerB (k : Bool) : corner k ∈ b.image := by
    cases k
    · exact D.second_on_curve ⟨0,D.second_zero⟩
    · exact D.second_on_curve ⟨1,D.second_one⟩
  have hfree (k : Bool) : corner k ∉ M.cover.branch := by cases k <;> assumption
  let θ : Bool → Interval := fun k => Classical.choose (hcornerA k)
  have hθcorner (k : Bool) : a.val.map (θ k)=corner k := Classical.choose_spec (hcornerA k)
  have hne : D.firstCorner ≠ D.secondCorner := by
    intro he
    exact zero_ne_one (D.first_embedded.injective (D.first_zero.trans (he.trans D.first_one.symm)))
  have hθ : Function.Injective θ := by
    intro k l he
    have hc : corner k=corner l := (hθcorner k).symm.trans ((congrArg a.val.map he).trans (hθcorner l))
    cases k <;> cases l
    · rfl
    · exact False.elim (hne hc)
    · exact False.elim (hne hc.symm)
    · rfl
  have hθint (k : Bool) : 0 < (θ k:ℝ) ∧ (θ k:ℝ) < 1 := by
    have hn0 : θ k ≠ 0 := by
      intro he
      exact hfree k ((hθcorner k).symm ▸ (he.symm ▸ a.val.start_marked))
    have hn1 : θ k ≠ 1 := by
      intro he
      exact hfree k ((hθcorner k).symm ▸ (he.symm ▸ a.val.end_marked))
    constructor
    · exact lt_of_le_of_ne (θ k).property.1 (fun he => hn0 (Subtype.ext he.symm))
    · exact lt_of_le_of_ne (θ k).property.2 (fun he => hn1 (Subtype.ext he))
  have hcharts (k : Bool) : ∃ G : OpenPartialHomeomorph S Plane,
      G.source ⊆ interior N.closedSet ∧ Disjoint G.source (M.cover.branch:Set S) ∧
      corner k ∈ G.source ∧ G (corner k)=0 ∧
      (∀ x ∈ G.source, x ∈ a.image ↔ G x 1=0) ∧
      (∀ x ∈ G.source, x ∈ b.image ↔ G x 0=0) := by
    obtain ⟨U,hU,hpU,hm,e,hep,ha,hb⟩ := hcross (corner k)
      ⟨⟨hcornerA k,hfree k⟩,hcornerB k,hfree k⟩
    let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
    have hV : IsOpen V := (isOpen_lt (continuous_fst.abs) continuous_const).inter
      (isOpen_lt (continuous_snd.abs) continuous_const)
    letI : Nonempty U := ⟨⟨corner k,hpU⟩⟩
    let coeU := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
    let f : U → ℝ × ℝ := fun u => (e u:ℝ × ℝ)
    have hf : IsOpenEmbedding f := hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
    let coeE := hf.toOpenPartialHomeomorph f
    let E0 := coeU.symm.trans coeE
    have hEs : E0.source=U := by simp [E0,coeU,coeE,IsOpenEmbedding.toOpenPartialHomeomorph_target]
    have hE (x : S) (hx : x ∈ U) : E0 x=(e ⟨x,hx⟩:ℝ × ℝ) := by
      have hu : coeU.symm x=⟨x,hx⟩ := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv (x := ⟨x,hx⟩)
      change f (coeU.symm x)=_
      rw [hu]
    let L : (ℝ × ℝ) ≃ₜ Plane := {
      toEquiv := {
        toFun := fun z => Plane.mk z.1 z.2
        invFun := fun z => (z 0,z 1)
        left_inv := by intro z; apply Prod.ext <;> rfl
        right_inv := by intro z; ext j; fin_cases j <;> rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let G := (E0.restr (interior N.closedSet)).trans L.toOpenPartialHomeomorph
    have hGs : G.source=U ∩ interior N.closedSet := by simp [G,hEs]
    have hG (x : S) (hx : x ∈ U) : G x=Plane.mk (e ⟨x,hx⟩).val.1 (e ⟨x,hx⟩).val.2 := by
      change L (E0 x)=_
      rw [hE x hx]; rfl
    refine ⟨G,fun x hx => (hGs.le hx).2,hm.mono_left (fun x hx => (hGs.le hx).1),
      hGs.symm ▸ ⟨hpU,N.arc_inside (hcornerA k)⟩,?_,?_,?_⟩
    · rw [hG _ hpU,hep]; ext j; fin_cases j <;> rfl
    · intro x hx
      rw [hG x (hGs.le hx).1]
      exact ha ⟨x,(hGs.le hx).1⟩
    · intro x hx
      rw [hG x (hGs.le hx).1]
      exact hb ⟨x,(hGs.le hx).1⟩
  choose F hFN hFm hFp hF0 hFa hFb using hcharts
  let f : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  have hf : IsEmbedding f := (f.continuous.isClosedEmbedding a.injective).isEmbedding
  obtain ⟨R,hR,hRN,hcenter,σ,δ,η,hsign,hpos,hcoords⟩ :=
    CurveComplex.source_finite_interior_axis_framed_arc_strip S f hf Bool θ hθ hθint F
      (fun k => by change a.val.map (θ k) ∈ (F k).source; rw [hθcorner]; exact hFp k)
      (fun k => by rw [show f (θ k)=corner k from hθcorner k]; exact hF0 k)
      (fun k t ht => (hFa k (f t) ht).mp (mem_range_self t))
      (interior N.closedSet) isOpen_interior N.arc_inside
  refine ⟨θ,F,R,hθcorner,hθ,hθint,?_,hR,hRN,hcenter,σ,δ,η,hsign,hpos,hcoords⟩
  intro k
  exact ⟨hFN k,hFm k,(hθcorner k).symm ▸ hFp k,(hθcorner k).symm ▸ hF0 k,hFa k,hFb k⟩

private theorem actual_inner_selected_disk_produces_mark_free_enlarged_disk
    (M : HyperellipticModel E S) (a b : NonLoopArc M) (N : ArcNeighborhood a)
    (D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (hN : range D.disk ⊆ interior N.closedSet)
    (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch) :
    ∃ d : C(Metric.closedBall (0 : Plane) 1,S), IsEmbedding d ∧
      range D.disk ⊆ interior (range d) ∧ range d ⊆ interior N.closedSet ∧
      Disjoint (range d) (M.cover.branch:Set S) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  letI : CurveComplex.ClosedSurface S := {}
  let V : Set S := interior N.closedSet ∩ (M.cover.branch:Set S)ᶜ
  have hV : IsOpen V := isOpen_interior.inter M.cover.branch.isClosed.isOpen_compl
  have hDV : range D.disk ⊆ V := by
    intro p hp
    refine ⟨hN hp,?_⟩
    intro hpm
    have hc := D.marks_are_corners p hp hpm
    rcases mem_insert_iff.mp hc with hc | hc
    · exact h0 (hc ▸ hpm)
    · exact h1 ((mem_singleton_iff.mp hc) ▸ hpm)
  obtain ⟨H,d,hd,hstrict,hdV,_,_,_⟩ :=
    CurveComplex.LocalSurgery.exists_supported_strict_disk_enlargement D.disk D.disk_embedded V hV hDV
  refine ⟨d,hd,hstrict,fun p hp => (hdV hp).1,?_⟩
  exact disjoint_left.mpr (fun p hp hpm => (hdV hp).2 hpm)

private theorem compact_axis_produces_uniform_closed_band_inside_open
    (R : Interval × Icc (-1:ℝ) 1 → S) (hR : Continuous R)
    (q : Interval → Interval) (hq : Continuous q)
    (U : Set S) (hU : IsOpen U)
    (haxis : ∀ t, R (q t,⟨0,by norm_num⟩) ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/2 ∧
      ∀ (t : Interval) (v : Icc (-1:ℝ) 1), |(v:ℝ)| ≤ ρ → R (q t,v) ∈ U := by
  let Z := Interval × Icc (-1:ℝ) 1
  let X : Interval → Z := fun t => (q t,⟨0,by norm_num⟩)
  have hX : Continuous X := hq.prodMk continuous_const
  have hK : IsCompact (range X) := isCompact_range hX
  obtain ⟨δ,hδ,hband⟩ := hK.exists_cthickening_subset_open (hU.preimage hR)
    (by rintro z ⟨t,rfl⟩; exact haxis t)
  let ρ : ℝ := min δ (1/2)
  refine ⟨ρ,lt_min hδ (by norm_num),min_le_right _ _,?_⟩
  intro t v hv
  apply hband
  apply Metric.mem_cthickening_of_dist_le (q t,v) (X t) δ (range X) (mem_range_self t)
  have hd : dist (q t,v) (X t)=|(v:ℝ)| := by
    simp [X,Prod.dist_eq,Subtype.dist_eq,Real.dist_eq]
  rw [hd]
  exact hv.trans (min_le_left _ _)

private theorem actual_inner_disk_produces_two_terminal_rails
    (M : HyperellipticModel E S) (a b : NonLoopArc M) (N : ArcNeighborhood a)
    (D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (hDN : range D.disk ⊆ interior N.closedSet)
    (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
    (hempty : Disjoint D.openInterior (a.image ∪ b.image))
    (hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p) :
    ∃ (d : C(Metric.closedBall (0 : Plane) 1,S))
      (g r : Bool → C(Interval,S)), IsEmbedding d ∧
      range D.disk ⊆ interior (range d) ∧ range d ⊆ interior N.closedSet ∧
      Disjoint (range d) (M.cover.branch:Set S) ∧
      (∀ s, IsEmbedding (g s) ∧ range (g s) ⊆ interior (range d) ∧
        Disjoint (range (g s)) a.image ∧
        range (g s) ∩ b.image = {g s 0,g s 1}) ∧
      (∀ k, IsEmbedding (r k) ∧ range (r k) ⊆ interior (range d) ∧
        range (r k) ⊆ b.image ∧
        r k ⟨1/2,by constructor <;> norm_num⟩ =
          (if k then D.secondCorner else D.firstCorner) ∧
        r k 0 = (if k then g false 1 else g false 0) ∧
        r k 1 = (if k then g true 1 else g true 0)) ∧
      Disjoint (range (r false)) (range (r true)) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨d,hd,hstrict,hdN,hdMarks⟩ := actual_inner_selected_disk_produces_mark_free_enlarged_disk M a b N D hDN h0 h1
  obtain ⟨θ,F,R,hθcorner,hθ,hθint,hcharts,hR,hRN,hcenter,σ,δ,η,hsign,hpos,hcoords⟩ :=
    actual_inner_disk_two_corner_framing_inside_original_neighborhood M a b N D h0 h1 hcross
  let A : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  have hA : IsEmbedding A := (A.continuous.isClosedEmbedding a.injective).isEmbedding
  let q : Interval → Interval := fun t => hA.toHomeomorph.symm ⟨D.firstSide t,D.first_on_curve ⟨t,rfl⟩⟩
  have hq : Continuous q := hA.toHomeomorph.symm.continuous.comp (D.firstSide.continuous.subtype_mk _)
  have hmap (t : Interval) : a.val.map (q t)=D.firstSide t :=
    congrArg Subtype.val (hA.toHomeomorph.apply_symm_apply _)
  have hqi : Function.Injective q := by
    intro t u he
    exact D.first_embedded.injective ((hmap t).symm.trans ((congrArg a.val.map he).trans (hmap u)))
  have hq0 : q 0=θ false := a.injective ((hmap 0).trans (D.first_zero.trans (hθcorner false).symm))
  have hq1 : q 1=θ true := a.injective ((hmap 1).trans (D.first_one.trans (hθcorner true).symm))
  have hc0 : a.val.map (θ false)=D.firstCorner := by simpa using hθcorner false
  have hc1 : a.val.map (θ true)=D.secondCorner := by simpa using hθcorner true
  have hsmall (k : Bool) : ∃ T : Set S, IsOpen T ∧ a.val.map (θ k) ∈ T ∧ T ⊆ (F k).source ∧
      ∀ z, R z ∈ T → |(z.1:ℝ)-(θ k:ℝ)| < η k := by
    let Z := Interval × Icc (-1:ℝ) 1
    let K : Set Z := {z | η k ≤ |(z.1:ℝ)-(θ k:ℝ)|}
    have hc : Continuous (fun z : Z => |(z.1:ℝ)-(θ k:ℝ)|) := by
      change Continuous (fun z : Interval × Icc (-1:ℝ) 1 => |(z.1:ℝ)-(θ k:ℝ)|)
      fun_prop
    have hK : IsClosed K := isClosed_le continuous_const hc
    have hpnot : a.val.map (θ k) ∉ R '' K := by
      rintro ⟨z,hz,he⟩
      have hz0 := hR.injective (he.trans (hcenter (θ k)).symm)
      have hle : η k ≤ 0 := by
        change η k ≤ |(z.1:ℝ)-(θ k:ℝ)| at hz
        rw [hz0] at hz
        simpa using hz
      exact (not_le_of_gt (hpos k).2) hle
    let T : Set S := (F k).source ∩ (R '' K)ᶜ
    refine ⟨T,(F k).open_source.inter (hK.isCompact.image hR.continuous).isClosed.isOpen_compl,
      ⟨(hcharts k).2.2.1,hpnot⟩,inter_subset_left,?_⟩
    intro z hz
    by_contra hnot
    exact hz.2 ⟨z,le_of_not_gt hnot,rfl⟩
  choose T hT hTp hTF hnear using hsmall
  have hclean : range D.firstSide ∩ b.image={D.firstCorner,D.secondCorner} :=
    actual_empty_marked_bigon_first_side_clean M a.toEssential b.toEssential
      (fun p hp => actual_marked_crossesInDisk_symm M a.toEssential b.toEssential p (hcross p hp)) D hempty
  let Q : Set S := (M.cover.branch:Set S) ∪ (b.image ∩ (T false ∪ T true)ᶜ)
  have hQ : IsClosed Q := M.cover.branch.isClosed.union
    ((isCompact_range b.val.continuous).isClosed.inter ((hT false).union (hT true)).isClosed_compl)
  have hsideDisk (t : Interval) : D.firstSide t ∈ range D.disk := by
    apply image_subset_range D.disk _
    rw [D.boundary_eq]
    exact Or.inl (mem_range_self t)
  have haxisQ (t : Interval) : D.firstSide t ∉ Q := by
    rintro (hm | ⟨hb,ht⟩)
    · exact disjoint_left.mp hdMarks (interior_subset (hstrict (hsideDisk t))) hm
    · have hc := hclean ▸ (show D.firstSide t ∈ range D.firstSide ∩ b.image from ⟨mem_range_self t,hb⟩)
      rcases mem_insert_iff.mp hc with hc | hc
      · exact ht (Or.inl (hc.symm ▸ (hc0 ▸ hTp false)))
      · exact ht (Or.inr ((mem_singleton_iff.mp hc).symm ▸ (hc1 ▸ hTp true)))
  let U : Set S := interior (range d) ∩ Qᶜ
  have hU : IsOpen U := isOpen_interior.inter hQ.isOpen_compl
  obtain ⟨ρ,hρ,hρhalf,hband⟩ := compact_axis_produces_uniform_closed_band_inside_open R hR.continuous q hq U hU
    (fun t => by rw [hcenter,hmap]; exact ⟨hstrict (hsideDisk t),haxisQ t⟩)
  let v (s : Bool) : Icc (-1:ℝ) 1 := ⟨if s then ρ else -ρ,by cases s <;> constructor <;> dsimp <;> linarith⟩
  have hv (s : Bool) : |(v s:ℝ)|=ρ := by cases s <;> simp [v,abs_of_pos hρ,abs_of_neg (neg_neg_of_pos hρ)]
  have hvne (s : Bool) : (v s:ℝ) ≠ 0 := by intro he; have hh := hv s; rw [he,abs_zero] at hh; linarith
  let g (s : Bool) : C(Interval,S) := ⟨fun t => R (q t,v s),hR.continuous.comp (hq.prodMk continuous_const)⟩
  have hg (s : Bool) : IsEmbedding (g s) := ((g s).continuous.isClosedEmbedding (by
    intro t u he
    exact hqi (congrArg Prod.fst (hR.injective he)))).isEmbedding
  have hgU (s : Bool) (t : Interval) : g s t ∈ U := hband t (v s) (hv s).le
  have hgA (s : Bool) : Disjoint (range (g s)) a.image := by
    apply disjoint_left.mpr
    rintro z ⟨t,rfl⟩ ⟨u,he⟩
    have hh := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ))
      (hR.injective (he.symm.trans (hcenter u).symm))
    exact hvne s hh
  have hBaxis (k : Bool) := (hcharts k).2.2.2.2.2
  have hgB0 (s : Bool) : g s 0 ∈ b.image := by
    have hnear0 : |(q 0:ℝ)-(θ false:ℝ)| < η false := by rw [hq0]; simpa using (hpos false).2
    have hf := hcoords false (q 0) (v s) hnear0
    apply (hBaxis false (g s 0) hf.1).mpr
    change F false (R (q 0,v s)) 0=0
    rw [hf.2,hq0]
    have hzero := (hcharts false).2.2.2.1
    change F false (a.val.map (θ false)) 0=0
    exact congrArg (fun z : Plane => z 0) hzero
  have hgB1 (s : Bool) : g s 1 ∈ b.image := by
    have hnear1 : |(q 1:ℝ)-(θ true:ℝ)| < η true := by rw [hq1]; simpa using (hpos true).2
    have hf := hcoords true (q 1) (v s) hnear1
    apply (hBaxis true (g s 1) hf.1).mpr
    change F true (R (q 1,v s)) 0=0
    rw [hf.2,hq1]
    have hzero := (hcharts true).2.2.2.1
    change F true (a.val.map (θ true)) 0=0
    exact congrArg (fun z : Plane => z 0) hzero
  have hgmeet (s : Bool) : range (g s) ∩ b.image={g s 0,g s 1} := by
    apply Subset.antisymm
    · rintro z ⟨⟨t,rfl⟩,hbt⟩
      have htT : g s t ∈ T false ∪ T true := by
        by_contra ht
        exact (hgU s t).2 (Or.inr ⟨hbt,ht⟩)
      obtain ⟨k,hkt⟩ : ∃ k : Bool, g s t ∈ T k := by
        rcases htT with ht | ht
        · exact ⟨false,ht⟩
        · exact ⟨true,ht⟩
      have hn := hnear k (q t,v s) hkt
      have hf := hcoords k (q t) (v s) hn
      have hcz := hcoords k (q t) ⟨0,by norm_num⟩ hn
      have hbcenter : a.val.map (q t) ∈ b.image := by
        apply (hBaxis k _ ((hcenter _).symm ▸ hcz.1)).mpr
        have hh := (hBaxis k _ (hTF k hkt)).mp hbt
        change F k (R (q t,v s)) 0=0 at hh
        rw [hf.2] at hh
        exact hh
      have hc := hclean ▸ (show D.firstSide t ∈ range D.firstSide ∩ b.image from ⟨mem_range_self t,(hmap t) ▸ hbcenter⟩)
      rcases mem_insert_iff.mp hc with hc | hc
      · have ht : t=0 := D.first_embedded.injective (hc.trans D.first_zero.symm)
        exact mem_insert_iff.mpr (Or.inl (congrArg (g s) ht))
      · have ht : t=1 := D.first_embedded.injective ((mem_singleton_iff.mp hc).trans D.first_one.symm)
        exact mem_insert_of_mem _ (mem_singleton_iff.mpr (congrArg (g s) ht))
    · intro z hz
      rcases mem_insert_iff.mp hz with he | he
      · subst z; exact ⟨mem_range_self _,hgB0 s⟩
      · subst z; exact ⟨mem_range_self _,hgB1 s⟩
  let w : Interval → Icc (-1:ℝ) 1 := fun t => ⟨ρ*(2*(t:ℝ)-1),by constructor <;> nlinarith [t.property.1,t.property.2]⟩
  have hw (t : Interval) : |(w t:ℝ)| ≤ ρ := by rw [abs_le]; dsimp [w]; constructor <;> nlinarith [t.property.1,t.property.2]
  let r (k : Bool) : C(Interval,S) := ⟨fun t => R (θ k,w t),hR.continuous.comp (by dsimp [w]; fun_prop)⟩
  have hr (k : Bool) : IsEmbedding (r k) := ((r k).continuous.isClosedEmbedding (by
    intro t u he
    have hh := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hR.injective he)
    apply Subtype.ext
    dsimp [w] at hh
    nlinarith)).isEmbedding
  have hrU (k : Bool) (t : Interval) : r k t ∈ U := by
    cases k
    · change R (θ false,w t) ∈ U
      rw [← hq0]
      exact hband 0 (w t) (hw t)
    · change R (θ true,w t) ∈ U
      rw [← hq1]
      exact hband 1 (w t) (hw t)
  have hrB (k : Bool) (t : Interval) : r k t ∈ b.image := by
    have hn : |(θ k:ℝ)-(θ k:ℝ)| < η k := by simpa using (hpos k).2
    have hf := hcoords k (θ k) (w t) hn
    apply (hBaxis k (r k t) hf.1).mpr
    change F k (R (θ k,w t)) 0=0
    rw [hf.2,(hcharts k).2.2.2.1]
    rfl
  refine ⟨d,g,r,hd,hstrict,hdN,hdMarks,?_,?_,?_⟩
  · intro s
    exact ⟨hg s,by rintro z ⟨t,rfl⟩; exact (hgU s t).1,hgA s,hgmeet s⟩
  · intro k
    refine ⟨hr k,by rintro z ⟨t,rfl⟩; exact (hrU k t).1,
      by rintro z ⟨t,rfl⟩; exact hrB k t,?_,?_,?_⟩
    · change R (θ k,w _)=_
      have hh : w ⟨1/2,by constructor <;> norm_num⟩ = ⟨0,by norm_num⟩ := by apply Subtype.ext; dsimp [w]; ring
      rw [hh,hcenter,hθcorner]
    · cases k <;> change R (_,w 0)=R (_,v false) <;> simp only [hq0,hq1] <;>
        congr 1 <;> apply Prod.ext <;> try rfl
      all_goals apply Subtype.ext; dsimp [w,v]; ring
    · cases k <;> change R (_,w 1)=R (_,v true) <;> simp only [hq0,hq1] <;>
        congr 1 <;> apply Prod.ext <;> try rfl
      all_goals apply Subtype.ext; dsimp [w,v]; ring

  · apply disjoint_left.mpr
    rintro z ⟨t,ht⟩ ⟨u,hu⟩
    have hh := congrArg Prod.fst (hR.injective (ht.trans hu.symm))
    have he := hθ hh
    exact Bool.false_ne_true he

private theorem embedded_terminal_crosssection_has_endpoint_outside_side
    (b side r : C(Interval,S)) (hb : IsEmbedding b) (hs : IsEmbedding side) (hr : IsEmbedding r)
    (hside : range side ⊆ range b) (hrange : range r ⊆ range b)
    (hmid : r ⟨1/2,by constructor <;> norm_num⟩=side 0) :
    r 0 ∉ range side ∨ r 1 ∉ range side := by
  classical
  by_contra hn
  have he0 : r 0 ∈ range side := by tauto
  have he1 : r 1 ∈ range side := by tauto
  let F : Interval → Interval := fun t => hb.toHomeomorph.symm ⟨side t,hside (mem_range_self t)⟩
  let G : Interval → Interval := fun t => hb.toHomeomorph.symm ⟨r t,hrange (mem_range_self t)⟩
  have hF : Continuous F := hb.toHomeomorph.symm.continuous.comp (side.continuous.subtype_mk _)
  have hG : Continuous G := hb.toHomeomorph.symm.continuous.comp (r.continuous.subtype_mk _)
  have hFm (t : Interval) : b (F t)=side t := congrArg Subtype.val (hb.toHomeomorph.apply_symm_apply _)
  have hGm (t : Interval) : b (G t)=r t := congrArg Subtype.val (hb.toHomeomorph.apply_symm_apply _)
  have hFi : Function.Injective F := fun t u he => hs.injective ((hFm t).symm.trans ((congrArg b he).trans (hFm u)))
  have hGi : Function.Injective G := fun t u he => hr.injective ((hGm t).symm.trans ((congrArg b he).trans (hGm u)))
  obtain ⟨u0,hu0⟩ := he0
  obtain ⟨u1,hu1⟩ := he1
  have h0 : F u0=G 0 := hb.injective ((hFm u0).trans (hu0.trans (hGm 0).symm))
  have h1 : F u1=G 1 := hb.injective ((hFm u1).trans (hu1.trans (hGm 1).symm))
  let mid : Interval := ⟨1/2,by constructor <;> norm_num⟩
  have hm : G mid=F 0 := hb.injective ((hGm mid).trans (hmid.trans (hFm 0).symm))
  have hm0 : (0:Interval) < mid := by change (0:ℝ)<1/2; norm_num
  have hm1 : mid < (1:Interval) := by change (1/2:ℝ)<1; norm_num
  rcases hF.strictMono_of_inj_boundedOrder' hFi with hf | hf <;>
    rcases hG.strictMono_of_inj_boundedOrder' hGi with hg | hg
  · have hle := hf.monotone (show (0:Interval) ≤ u0 from bot_le)
    have hlt := hg hm0
    rw [h0] at hle
    rw [hm] at hlt
    exact (not_lt_of_ge hle) hlt
  · have hle := hf.monotone (show (0:Interval) ≤ u1 from bot_le)
    have hlt := hg hm1
    rw [h1] at hle
    rw [hm] at hlt
    exact (not_lt_of_ge hle) hlt
  · have hle := hf.antitone (show (0:Interval) ≤ u1 from bot_le)
    have hlt := hg hm1
    rw [h1] at hle
    rw [hm] at hlt
    exact (not_lt_of_ge hle) hlt
  · have hle := hf.antitone (show (0:Interval) ≤ u0 from bot_le)
    have hlt := hg hm0
    rw [h0] at hle
    rw [hm] at hlt
    exact (not_lt_of_ge hle) hlt

private theorem moving_core_between_ports_in_connected_trace
    (M : HyperellipticModel E S) (b : NonLoopArc M)
    (g : C(Interval,S)) (hg : IsEmbedding g)
    (J : Set S) (hJ : IsConnected J) (hJb : J ⊆ b.image)
    (h0 : g 0 ∈ J) (h1 : g 1 ∈ J) :
    ∃ (u v : Interval) (c : C(Interval,S)), u ≠ v ∧
      b.val.map u=g 0 ∧ b.val.map v=g 1 ∧ IsEmbedding c ∧
      c 0=g 0 ∧ c 1=g 1 ∧ range c=b.val.map '' uIcc u v ∧ range c ⊆ J := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let B : C(Interval,S) := ⟨b.val.map,b.val.continuous⟩
  have hB : IsEmbedding B := (B.continuous.isClosedEmbedding b.injective).isEmbedding
  let j : J → range B := fun z => ⟨z.val,hJb z.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let f : J → Interval := hB.toHomeomorph.symm ∘ j
  have hf : Continuous f := hB.toHomeomorph.symm.continuous.comp hj
  let u : Interval := f ⟨g 0,h0⟩
  let v : Interval := f ⟨g 1,h1⟩
  have huf : b.val.map u=g 0 := congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)
  have hvf : b.val.map v=g 1 := congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)
  have huv : u ≠ v := by intro he; exact zero_ne_one (hg.injective (huf.symm.trans ((congrArg b.val.map he).trans hvf)))
  let q : Interval → Interval := fun t => ⟨(1-(t:ℝ))*(u:ℝ)+(t:ℝ)*(v:ℝ),by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) u.property.1) (mul_nonneg t.property.1 v.property.1)
    · nlinarith [u.property.1,u.property.2,v.property.1,v.property.2,t.property.1,t.property.2]⟩
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hq0 : q 0=u := by apply Subtype.ext; dsimp [q]; ring
  have hq1 : q 1=v := by apply Subtype.ext; dsimp [q]; ring
  have hqi : Function.Injective q := by
    intro t s he
    have hh := congrArg Subtype.val he
    have huv' : (u:ℝ) ≠ (v:ℝ) := fun he => huv (Subtype.ext he)
    apply Subtype.ext
    dsimp [q] at hh
    have hz : ((t:ℝ)-(s:ℝ))*((v:ℝ)-(u:ℝ))=0 := by nlinarith only [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr huv'.symm))
  have hqr : range q=uIcc u v := by
    have hfreal : Continuous (fun t : Interval => (q t:ℝ)) := continuous_subtype_val.comp hq
    apply Subset.antisymm
    · rintro z ⟨t,rfl⟩
      rw [mem_uIcc]
      by_cases huvle : u ≤ v
      · left
        have hh : (u:ℝ) ≤ (v:ℝ) := huvle
        constructor
        · change (u:ℝ) ≤ (1-(t:ℝ))*(u:ℝ)+(t:ℝ)*(v:ℝ)
          nlinarith [t.property.1,t.property.2]
        · change (1-(t:ℝ))*(u:ℝ)+(t:ℝ)*(v:ℝ) ≤ (v:ℝ)
          nlinarith [t.property.1,t.property.2]
      · right
        have hvule : v ≤ u := le_of_not_ge huvle
        have hh : (v:ℝ) ≤ (u:ℝ) := hvule
        constructor
        · change (v:ℝ) ≤ (1-(t:ℝ))*(u:ℝ)+(t:ℝ)*(v:ℝ)
          nlinarith [t.property.1,t.property.2]
        · change (1-(t:ℝ))*(u:ℝ)+(t:ℝ)*(v:ℝ) ≤ (u:ℝ)
          nlinarith [t.property.1,t.property.2]
    · intro z hz
      have hzreal : (z:ℝ) ∈ uIcc ((q 0:Interval):ℝ) ((q 1:Interval):ℝ) := by
        rw [hq0,hq1]
        exact hz
      obtain ⟨t,ht,hqt⟩ := intermediate_value_uIcc hfreal.continuousOn hzreal
      exact ⟨t,Subtype.ext hqt⟩
  let c : C(Interval,S) := ⟨b.val.map ∘ q,b.val.continuous.comp hq⟩
  have hc : IsEmbedding c := (c.continuous.isClosedEmbedding (fun t s he => hqi (b.injective he))).isEmbedding
  have hcr : range c=b.val.map '' uIcc u v := by rw [← hqr]; exact range_comp b.val.map q
  have hK : IsPreconnected (range f) := by
    letI : PreconnectedSpace J := Subtype.preconnectedSpace hJ.isPreconnected
    exact isPreconnected_range hf
  have huK : u ∈ range f := ⟨⟨g 0,h0⟩,rfl⟩
  have hvK : v ∈ range f := ⟨⟨g 1,h1⟩,rfl⟩
  have hsub : range c ⊆ J := by
    rw [hcr]
    rintro z ⟨t,ht,rfl⟩
    obtain ⟨w,hw⟩ := hK.ordConnected.uIcc_subset huK hvK ht
    have hm : b.val.map (f w)=w.val := congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)
    rw [← hw,hm]
    exact w.property
  exact ⟨u,v,c,huv,huf,hvf,hc,by simpa only [c,ContinuousMap.coe_mk,Function.comp_apply,hq0] using huf,
    by simpa only [c,ContinuousMap.coe_mk,Function.comp_apply,hq1] using hvf,hcr,hsub⟩

private theorem disjoint_terminal_crosssections_select_core_containing_first_corner
    (M : HyperellipticModel E S) (b : NonLoopArc M)
    (g r : Bool → C(Interval,S)) (hr : ∀ k, IsEmbedding (r k))
    (hrb : ∀ k, range (r k) ⊆ b.image)
    (hdis : Disjoint (range (r false)) (range (r true)))
    (hports0 : ∀ k, r k 0=(if k then g false 1 else g false 0))
    (hports1 : ∀ k, r k 1=(if k then g true 1 else g true 0)) :
    ∃ (s : Bool) (u v : Interval), b.val.map u=g s 0 ∧ b.val.map v=g s 1 ∧
      r false ⟨1/2,by constructor <;> norm_num⟩ ∈ b.val.map '' uIcc u v := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let B : C(Interval,S) := ⟨b.val.map,b.val.continuous⟩
  have hB : IsEmbedding B := (B.continuous.isClosedEmbedding b.injective).isEmbedding
  let G (k : Bool) (t : Interval) : Interval :=
    hB.toHomeomorph.symm ⟨r k t,hrb k (mem_range_self t)⟩
  have hG (k : Bool) : Continuous (G k) := hB.toHomeomorph.symm.continuous.comp ((r k).continuous.subtype_mk _)
  have hGm (k : Bool) (t : Interval) : b.val.map (G k t)=r k t :=
    congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)
  have hGi (k : Bool) : Function.Injective (G k) := fun t u he =>
    (hr k).injective ((hGm k t).symm.trans ((congrArg b.val.map he).trans (hGm k u)))
  let mid : Interval := ⟨1/2,by constructor <;> norm_num⟩
  let β0 := G false mid
  let β1 := G true mid
  have hnot : β0 ∉ range (G true) := by
    rintro ⟨t,ht⟩
    have he : r false mid=r true t := (hGm false mid).symm.trans ((congrArg b.val.map ht.symm).trans (hGm true t))
    exact disjoint_left.mp hdis (mem_range_self mid) ⟨t,he.symm⟩
  have hne : β0 ≠ β1 := fun he => hnot ⟨mid,he.symm⟩
  have hK : IsPreconnected (range (G true)) := isPreconnected_range (hG true)
  have hotherUp (hb : β0 < β1) (t : Interval) : β0 < G true t := by
    by_contra hn
    have hle : G true t ≤ β0 := le_of_not_gt hn
    have hm : β0 ∈ uIcc (G true t) β1 := mem_uIcc.mpr (Or.inl ⟨hle,hb.le⟩)
    exact hnot (hK.ordConnected.uIcc_subset (mem_range_self t) (mem_range_self mid) hm)
  have hotherDown (hb : β1 < β0) (t : Interval) : G true t < β0 := by
    by_contra hn
    have hle : β0 ≤ G true t := le_of_not_gt hn
    have hm : β0 ∈ uIcc β1 (G true t) := mem_uIcc.mpr (Or.inl ⟨hb.le,hle⟩)
    exact hnot (hK.ordConnected.uIcc_subset (mem_range_self mid) (mem_range_self t) hm)
  have hm0 : (0:Interval) < mid := by change (0:ℝ)<1/2; norm_num
  have hm1 : mid < (1:Interval) := by change (1/2:ℝ)<1; norm_num
  have hselect : ∃ s : Bool, β0 ∈ uIcc (G false (if s then 1 else 0)) (G true (if s then 1 else 0)) := by
    rcases lt_or_gt_of_ne hne with hb | hb <;>
      rcases (hG false).strictMono_of_inj_boundedOrder' (hGi false) with hg | hg
    · exact ⟨false,mem_uIcc.mpr (Or.inl ⟨(hg hm0).le,(hotherUp hb 0).le⟩)⟩
    · exact ⟨true,mem_uIcc.mpr (Or.inl ⟨(hg hm1).le,(hotherUp hb 1).le⟩)⟩
    · exact ⟨true,mem_uIcc.mpr (Or.inr ⟨(hotherDown hb 1).le,(hg hm1).le⟩)⟩
    · exact ⟨false,mem_uIcc.mpr (Or.inr ⟨(hotherDown hb 0).le,(hg hm0).le⟩)⟩
  obtain ⟨s,hs⟩ := hselect
  refine ⟨s,G false (if s then 1 else 0),G true (if s then 1 else 0),?_,?_,?_⟩
  · cases s
    · exact (hGm false 0).trans (hports0 false)
    · exact (hGm false 1).trans (hports1 false)
  · cases s
    · exact (hGm true 0).trans (hports0 true)
    · exact (hGm true 1).trans (hports1 true)
  · exact ⟨β0,hs,hGm false mid⟩

private theorem actual_inner_disk_produces_enlarged_old_core_and_supporting_disk
    (M : HyperellipticModel E S) (a b : NonLoopArc M) (N : ArcNeighborhood a)
    (D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (hDN : range D.disk ⊆ interior N.closedSet)
    (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
    (hempty : Disjoint D.openInterior (a.image ∪ b.image))
    (hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p) :
    ∃ (u v : Interval) (c g : C(Interval,S)) (e : C(Metric.closedBall (0 : Plane) 1,S)),
      u ≠ v ∧ b.val.map u=g 0 ∧ b.val.map v=g 1 ∧
      IsEmbedding c ∧ IsEmbedding g ∧ c 0=g 0 ∧ c 1=g 1 ∧
      range c=b.val.map '' uIcc u v ∧ D.firstCorner ∈ range c ∧
      Disjoint (range g) a.image ∧ range g ∩ b.image={g 0,g 1} ∧
      range c ∩ range g={g 0,g 1} ∧ IsEmbedding e ∧
      e '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=range c ∪ range g ∧
      range e ⊆ interior N.closedSet ∧ Disjoint (range e) (M.cover.branch:Set S) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨d,g,r,hd,hstrict,hdN,hdMarks,hg,hr,hdis⟩ :=
    actual_inner_disk_produces_two_terminal_rails M a b N D hDN h0 h1 hempty hcross
  obtain ⟨s,u,v,hu,hv,hp⟩ := disjoint_terminal_crosssections_select_core_containing_first_corner
    M b g r (fun k => (hr k).1) (fun k => (hr k).2.2.1) hdis
      (fun k => (hr k).2.2.2.2.1) (fun k => (hr k).2.2.2.2.2)
  let mid : Interval := ⟨1/2,by constructor <;> norm_num⟩
  have hr0 : r false mid=D.firstCorner := (hr false).2.2.2.1
  have hr1 : r true mid=D.secondCorner := (hr true).2.2.2.1
  let J : Set S := (range (r false) ∪ range D.secondSide) ∪ range (r true)
  have hJ : IsConnected J :=
    IsConnected.union ⟨D.secondCorner,Or.inr ⟨1,D.second_one⟩,⟨mid,hr1⟩⟩
      (IsConnected.union ⟨D.firstCorner,⟨mid,hr0⟩,⟨0,D.second_zero⟩⟩
        (isConnected_range (r false).continuous) (isConnected_range D.secondSide.continuous))
      (isConnected_range (r true).continuous)
  have hJb : J ⊆ b.image := union_subset (union_subset (hr false).2.2.1 D.second_on_curve) (hr true).2.2.1
  have hJN : J ⊆ interior (range d) := by
    apply union_subset (union_subset (hr false).2.1 ?_) (hr true).2.1
    intro z hz
    apply hstrict
    apply image_subset_range D.disk _
    rw [D.boundary_eq]
    exact Or.inr hz
  have hg0 : g s 0 ∈ J := by
    cases s
    · exact Or.inl (Or.inl ⟨0,(hr false).2.2.2.2.1⟩)
    · exact Or.inl (Or.inl ⟨1,(hr false).2.2.2.2.2⟩)
  have hg1 : g s 1 ∈ J := by
    cases s
    · exact Or.inr ⟨0,(hr true).2.2.2.2.1⟩
    · exact Or.inr ⟨1,(hr true).2.2.2.2.2⟩
  obtain ⟨u',v',c,huv,huc,hvc,hc,hc0,hc1,hcr,hcJ⟩ :=
    moving_core_between_ports_in_connected_trace M b (g s) (hg s).1 J hJ hJb hg0 hg1
  have heU : u'=u := b.injective (huc.trans hu.symm)
  have heV : v'=v := b.injective (hvc.trans hv.symm)
  have hpC : D.firstCorner ∈ range c := by rw [hcr,heU,heV,← hr0]; exact hp
  have hcB : range c ⊆ b.image := hcJ.trans hJb
  have hcg : range c ∩ range (g s)={g s 0,g s 1} := by
    apply Subset.antisymm
    · intro z hz
      exact (hg s).2.2.2 ▸ ⟨hz.2,hcB hz.1⟩
    · intro z hz
      rcases mem_insert_iff.mp hz with hz | hz
      · subst z; exact ⟨⟨0,hc0⟩,mem_range_self _⟩
      · subst z; exact ⟨⟨1,hc1⟩,mem_range_self _⟩
  have hcrossSide (t w : Interval) (he : c t=g s w) : (t=0 ∧ w=0) ∨ (t=1 ∧ w=1) := by
    have hz := hcg ▸ (show c t ∈ range c ∩ range (g s) from ⟨mem_range_self t,⟨w,he.symm⟩⟩)
    rcases mem_insert_iff.mp hz with hz | hz
    · exact Or.inl ⟨hc.injective (hz.trans hc0.symm),(hg s).1.injective (he.symm.trans hz)⟩
    · have hz := mem_singleton_iff.mp hz
      exact Or.inr ⟨hc.injective (hz.trans hc1.symm),(hg s).1.injective (he.symm.trans hz)⟩
  obtain ⟨curve,hcurve⟩ := CurveComplex.exists_curve_of_two_arcs c (g s) hc.injective (hg s).1.injective hc0 hc1 hcrossSide
  have hcurveD : curve.image ⊆ range d := by
    rw [hcurve]
    exact union_subset ((hcJ.trans hJN).trans interior_subset) ((hg s).2.1.trans interior_subset)
  obtain ⟨e,he,heb,heD⟩ := CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk curve d hd hcurveD
  exact ⟨u',v',c,g s,e,huv,huc,hvc,hc,(hg s).1,hc0,hc1,hcr,hpC,(hg s).2.2.1,
    (hg s).2.2.2,hcg,he,heb.trans hcurve,heD.trans hdN,hdMarks.mono_left heD⟩

private theorem actual_mark_free_inner_support_disk_retained_remainder
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (u v : Interval) (c g : C(Interval,S))
    (hu : b.val.map u=g 0) (hv : b.val.map v=g 1)
    (hc : range c=b.val.map '' uIcc u v)
    (hgA : Disjoint (range g) a.image) (hgB : range g ∩ b.image={g 0,g 1})
    (e : C(Metric.closedBall (0 : Plane) 1,S)) (he : IsEmbedding e)
    (heb : e '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=range c ∪ range g)
    (heMarks : Disjoint (range e) (M.cover.branch:Set S)) :
    ∃ R : Set S, IsCompact R ∧ b.image=range c ∪ R ∧
      (∀ z ∈ range c ∩ R, z=g 0 ∨ z=g 1) ∧
      Disjoint (R ∩ arcInterior M a.toEssential) (range c) ∧
      Disjoint (e '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) R := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  let lo : Interval := min u v
  let hi : Interval := max u v
  have hC : range c=b.val.map '' Icc lo hi := hc
  have hlohi : lo ≤ hi := min_le_max
  have hCbd : range c ⊆ e '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := heb.symm ▸ subset_union_left
  have hloC : b.val.map lo ∈ range c := hC.symm ▸ ⟨lo,⟨le_rfl,hlohi⟩,rfl⟩
  have hhiC : b.val.map hi ∈ range c := hC.symm ▸ ⟨hi,⟨hlohi,le_rfl⟩,rfl⟩
  have hlo : (0:Interval) < lo := by
    apply lt_of_le_of_ne (show (0:Interval) ≤ lo from bot_le)
    intro hz
    have hc0 : b.val.map (0:Interval) ∈ range c := hz.symm ▸ hloC
    have hm0 : b.val.map (0:Interval) ∈ M.cover.branch := b.val.start_marked
    exact disjoint_left.mp heMarks (image_subset_range _ _ (hCbd hc0)) hm0
  have hhi : hi < (1:Interval) := by
    apply lt_of_le_of_ne (show hi ≤ (1:Interval) from le_top)
    intro hz
    have hc1 : b.val.map (1:Interval) ∈ range c := hz ▸ hhiC
    have hm1 : b.val.map (1:Interval) ∈ M.cover.branch := b.val.end_marked
    exact disjoint_left.mp heMarks (image_subset_range _ _ (hCbd hc1)) hm1
  have hportlo : b.val.map lo=g 0 ∨ b.val.map lo=g 1 := by
    by_cases huv : u ≤ v
    · left; simpa only [lo,min_eq_left huv] using hu
    · right; simpa only [lo,min_eq_right (le_of_not_ge huv)] using hv
  have hporthi : b.val.map hi=g 0 ∨ b.val.map hi=g 1 := by
    by_cases huv : u ≤ v
    · right; simpa only [hi,max_eq_right huv] using hv
    · left; simpa only [hi,max_eq_left (le_of_not_ge huv)] using hu
  let R : Set S := b.val.map '' (Iic lo ∪ Ici hi)
  have hR : IsCompact R := (isClosed_Iic.union isClosed_Ici).isCompact.image b.val.continuous
  have hRb : R ⊆ b.image := image_subset_range _ _
  have hOld : b.image=range c ∪ R := by
    rw [hC]
    apply Subset.antisymm
    · rintro z ⟨t,rfl⟩
      by_cases htl : t ≤ lo
      · exact Or.inr ⟨t,Or.inl htl,rfl⟩
      by_cases hth : hi ≤ t
      · exact Or.inr ⟨t,Or.inr hth,rfl⟩
      exact Or.inl ⟨t,⟨(le_of_not_ge htl),(le_of_not_ge hth)⟩,rfl⟩
    · intro z hz
      rcases hz with hz | hz
      · exact image_subset_range _ _ hz
      · exact hRb hz
  have hCR : ∀ z ∈ range c ∩ R, z=g 0 ∨ z=g 1 := by
    rintro z ⟨hzc,⟨t,ht,htz⟩⟩
    obtain ⟨s,hs,hsz⟩ := hC ▸ hzc
    have hst : s=t := b.injective (hsz.trans htz.symm)
    subst s
    rcases ht with ht | ht
    · have heq : t=lo := le_antisymm ht hs.1
      exact htz.symm ▸ (heq ▸ hportlo)
    · have heq : t=hi := le_antisymm hs.2 ht
      exact htz.symm ▸ (heq ▸ hporthi)
  have hRfree : Disjoint (R ∩ arcInterior M a.toEssential) (range c) := by
    apply disjoint_left.mpr
    intro z hzR hzC
    rcases hCR z ⟨hzC,hzR.1⟩ with heq | heq
    · exact disjoint_left.mp hgA (heq ▸ mem_range_self 0) hzR.2.1
    · exact disjoint_left.mp hgA (heq ▸ mem_range_self 1) hzR.2.1
  have hfrontB : frontier (range e) ∩ b.image ⊆ range c := by
    intro z hz
    have hbdy := CurveComplex.embedded_disk_frontier_subset_boundary e he hz.1
    rcases heb ▸ hbdy with hzc | hzg
    · exact hzc
    · have hp : z ∈ ({g 0,g 1}:Set S) := hgB ▸ (show z ∈ range g ∩ b.image from ⟨hzg,hz.2⟩)
      rcases mem_insert_iff.mp hp with hp | hp
      · subst z
        exact hu ▸ (hC.symm ▸ ⟨u,⟨min_le_left _ _,le_max_left _ _⟩,rfl⟩)
      · have hp := mem_singleton_iff.mp hp
        subst z
        exact hv ▸ (hC.symm ▸ ⟨v,⟨min_le_right _ _,le_max_right _ _⟩,rfl⟩)
  have hLavoid : Disjoint (b.val.map '' Iio lo) (frontier (range e)) := by
    apply disjoint_left.mpr
    rintro z ⟨t,ht,rfl⟩ hzF
    obtain ⟨s,hs,heq⟩ := hC ▸ hfrontB ⟨hzF,mem_range_self t⟩
    have hst := b.injective heq
    exact (not_le_of_gt ht) (hst ▸ hs.1)
  have hUavoid : Disjoint (b.val.map '' Ioi hi) (frontier (range e)) := by
    apply disjoint_left.mpr
    rintro z ⟨t,ht,rfl⟩ hzF
    obtain ⟨s,hs,heq⟩ := hC ▸ hfrontB ⟨hzF,mem_range_self t⟩
    have hst := b.injective heq
    exact (not_le_of_gt ht) (hst ▸ hs.2)
  have hLout : b.val.map '' Iio lo ⊆ (range e)ᶜ := by
    rcases CurveComplex.connected_cap_side (range e) (b.val.map '' Iio lo)
      (isPreconnected_Iio.image _ b.val.continuous.continuousOn) hLavoid with hIn | hOut
    · have hp := interior_subset (hIn ⟨0,hlo,rfl⟩)
      exact False.elim (disjoint_left.mp heMarks hp b.val.start_marked)
    · exact hOut.trans interior_subset
  have hUout : b.val.map '' Ioi hi ⊆ (range e)ᶜ := by
    rcases CurveComplex.connected_cap_side (range e) (b.val.map '' Ioi hi)
      (isPreconnected_Ioi.image _ b.val.continuous.continuousOn) hUavoid with hIn | hOut
    · have hp := interior_subset (hIn ⟨1,hhi,rfl⟩)
      exact False.elim (disjoint_left.mp heMarks hp b.val.end_marked)
    · exact hOut.trans interior_subset
  refine ⟨R,hR,hOld,hCR,hRfree,?_⟩
  apply disjoint_left.mpr
  rintro z hzIn ⟨t,ht,rfl⟩
  rcases ht with ht | ht
  · rcases lt_or_eq_of_le (show t ≤ lo from ht) with ht | ht
    · exact hLout ⟨t,ht,rfl⟩ (image_subset_range _ _ hzIn)
    · exact disjoint_left.mp (CurveComplex.embedded_disk_interior_disjoint_boundary e he) hzIn (ht.symm ▸ hCbd hloC)
  · rcases lt_or_eq_of_le (show hi ≤ t from ht) with ht | ht
    · exact hUout ⟨t,ht,rfl⟩ (image_subset_range _ _ hzIn)
    · exact disjoint_left.mp (CurveComplex.embedded_disk_interior_disjoint_boundary e he) hzIn (ht ▸ hCbd hhiC)

private theorem actual_raw_supporting_disk_motion_fixes_closed_obstacle
    (M : HyperellipticModel E S)
    (f₀ f₁ : C(Interval,S)) (hf₀ : IsEmbedding f₀) (hf₁ : IsEmbedding f₁)
    (u z : S) (hf₀0 : f₀ 0=u) (hf₁0 : f₁ 0=u) (hf₀1 : f₀ 1=z) (hf₁1 : f₁ 1=z)
    (hinter : range f₀ ∩ range f₁={u,z})
    (disk : C(Metric.closedBall (0 : Plane) 1,S)) (hdisk : IsEmbedding disk)
    (hboundary : disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=range f₀ ∪ range f₁)
    (w : S) (hw : w ∉ range disk)
    (Q : Set S) (hQc : IsClosed Q)
    (hQboundary : ∀ y ∈ range f₀ ∪ range f₁, y ∈ Q → y=u ∨ y=z)
    (hQinside : Disjoint (disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) Q) :
    ∃ H : CurveComplex.AmbientIsotopy S,
      (∀ t y, y ∈ Q → H.map (t,y)=y) ∧ H.finalMap '' range f₀=range f₁ := by
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  have embedded_side_isArcBetween (f : C(Interval,Plane))
      (hf : IsEmbedding f) : IsArcBetween (range f) (f 0) (f 1) := by
    let fc : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
    have hfc : Continuous fc := f.continuous.comp continuous_projIcc
    have he (t : Interval) : fc t = f t := by
      simp [fc,Set.projIcc_of_mem zero_le_one t.property]
    refine ⟨fc,hfc.continuousOn,?_,?_,he 0,he 1⟩
    · intro t ht u hu h
      exact congrArg Subtype.val (hf.injective (by
        simpa only [← he] using h : f ⟨t,ht⟩ = f ⟨u,hu⟩))
    · ext x
      constructor
      · rintro ⟨t,ht,rfl⟩
        exact ⟨⟨t,ht⟩,(he ⟨t,ht⟩).symm⟩
      · rintro ⟨t,rfl⟩
        exact ⟨t,t.property,he t⟩
  
  have hrawDiskChart (f₀ f₁ : C(Interval,S)) (hf₀ : IsEmbedding f₀) (hf₁ : IsEmbedding f₁)
      (u0 z0 : S) (hf₀0 : f₀ 0=u0) (hf₁0 : f₁ 0=u0) (hf₀1 : f₀ 1=z0) (hf₁1 : f₁ 1=z0)
      (hinter : range f₀ ∩ range f₁ = {u0,z0})
      (disk : C(Metric.closedBall (0 : Plane) 1,S)) (hdisk : IsEmbedding disk)
      (hboundary : disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range f₀ ∪ range f₁)
      (w : S) (hw : w ∉ range disk) :
      ∃ (f : Plane → S) (A B : Set Plane) (p q : Plane),
        IsOpenEmbedding f ∧ IsArcBetween A p q ∧ IsArcBetween B p q ∧
        A ∪ B = modelCurve ∧ f '' A = range f₀ ∧ f '' B = range f₁ ∧
        f p=u0 ∧ f q=z0 ∧
        f '' Plane.openSquare 0 1 = disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1} := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    let v := w
    have hv : v ∉ range disk := hw
    let e := M.puncturedPlane v
    let j : range disk → {z : S // z ≠ v} :=
      fun z => ⟨z.val,fun hz => hv (hz ▸ z.property)⟩
    let d : C(Metric.closedBall (0 : Plane) 1,Plane) :=
      ⟨fun x => e ⟨disk x,fun h => hv (h ▸ Set.mem_range_self x)⟩,by fun_prop⟩
    have firstDisk (t : Interval) : f₀ t ∈ range disk := by
      apply image_subset_range disk _
      rw [hboundary]
      exact Or.inl (Set.mem_range_self t)
    have secondDisk (t : Interval) : f₁ t ∈ range disk := by
      apply image_subset_range disk _
      rw [hboundary]
      exact Or.inr (Set.mem_range_self t)
    let g : C(Interval,Plane) :=
      ⟨fun t => e ⟨f₀ t,fun h => hv (h ▸ firstDisk t)⟩,by fun_prop⟩
    let h : C(Interval,Plane) :=
      ⟨fun t => e ⟨f₁ t,fun hh => hv (hh ▸ secondDisk t)⟩,by fun_prop⟩
    have hd : IsEmbedding d := (d.continuous.isClosedEmbedding (by
      intro x y hxy
      exact hdisk.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
    have hg : IsEmbedding g := (g.continuous.isClosedEmbedding (by
      intro x y hxy
      exact hf₀.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
    have hh : IsEmbedding h := (h.continuous.isClosedEmbedding (by
      intro x y hxy
      exact hf₁.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
    have hg0 : g 0 = h 0 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact hf₀0.trans hf₁0.symm
    have hg1 : g 1 = h 1 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact hf₀1.trans hf₁1.symm
    have hgA := embedded_side_isArcBetween g hg
    have hhB : IsArcBetween (range h) (g 0) (g 1) := by rw [hg0,hg1]; exact embedded_side_isArcBetween h hh
    have hc : IsJordanCurve (range g ∪ range h) := IsJordanCurve.of_two_arcs hgA hhB.reverse (by
      rintro z ⟨t,ht⟩ ⟨s,hs⟩
      have heq : f₀ t = f₁ s := congrArg Subtype.val (e.injective (ht.trans hs.symm))
      have hm : f₀ t ∈ ({u0,z0} : Set S) :=
        hinter ▸ ⟨Set.mem_range_self t,⟨s,heq.symm⟩⟩
      rcases mem_insert_iff.mp hm with hm | hm
      · left
        have ht0 : t=0 := hf₀.injective (hm.trans hf₀0.symm)
        exact ht.symm.trans (congrArg g ht0)
      · right
        have ht1 : t=1 := hf₀.injective ((mem_singleton_iff.mp hm).trans hf₀1.symm)
        exact ht.symm.trans (congrArg g ht1))
    have hbd : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range g ∪ range h := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        have hxs : disk x ∈ range f₀ ∪ range f₁ := by
          rw [← hboundary]
          exact mem_image_of_mem disk hx
        rcases hxs with ⟨t,ht⟩ | ⟨t,ht⟩
        · left; refine ⟨t,?_⟩; apply congrArg e; apply Subtype.ext; exact ht
        · right; refine ⟨t,?_⟩; apply congrArg e; apply Subtype.ext; exact ht
      · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
        · have htB : f₀ t ∈ disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
            rw [hboundary]; exact Or.inl (Set.mem_range_self t)
          obtain ⟨x,hx,hxt⟩ := htB
          refine ⟨x,hx,?_⟩; apply congrArg e; apply Subtype.ext; exact hxt
        · have htB : f₁ t ∈ disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
            rw [hboundary]; exact Or.inr (Set.mem_range_self t)
          obtain ⟨x,hx,hxt⟩ := htB
          refine ⟨x,hx,?_⟩; apply congrArg e; apply Subtype.ext; exact hxt
    have hrange := CurveComplex.embedded_disc_range_eq_closed_inside d hd _ hc hbd
    have hi : d '' {x | x.val ∈ Metric.ball (0 : Plane) 1} = inside (range g ∪ range h) := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        rcases hrange ▸ Set.mem_range_self x with hi | hb
        · exact hi
        · obtain ⟨y,hy,hyx⟩ := hbd.symm ▸ hb
          have he := congrArg Subtype.val (hd.injective hyx)
          have hyxS : x.val ∈ Metric.sphere (0 : Plane) 1 := he ▸ hy
          have hnlt : ‖x.val‖ < (1 : ℝ) := by
            change dist x.val 0 < 1 at hx
            simpa only [dist_zero_right] using hx
          have hneq : ‖x.val‖ = (1 : ℝ) := by
            change dist x.val 0 = 1 at hyxS
            simpa only [dist_zero_right] using hyxS
          exact False.elim (ne_of_lt hnlt hneq)
      · intro hz
        have hzR : z ∈ range d := by rw [hrange]; exact Or.inl hz
        obtain ⟨x,hx⟩ := hzR
        refine ⟨x,?_,hx⟩
        have hn : ‖x.val‖ ≤ (1 : ℝ) := by
          simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
        have hnb : x.val ∉ Metric.sphere (0 : Plane) 1 := by
          intro hxb
          have hzB : z ∈ range g ∪ range h := by rw [← hbd,← hx]; exact mem_image_of_mem d hxb
          exact Set.disjoint_right.mp (disjoint_curve_inside _) hz hzB
        change dist x.val 0 < 1
        rw [dist_zero_right]
        exact lt_of_le_of_ne hn (by simpa only [Metric.mem_sphere,dist_zero_right] using hnb)
    obtain ⟨ec⟩ := IsJordanCurve.modelCurve_homeomorph hc
    obtain ⟨φ,hφ⟩ := jordan_schoenflies_of_homeomorph isJordanCurve_modelCurve hc ec
    have hφC : φ '' modelCurve = range g ∪ range h := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩; rw [hφ ⟨x,hx⟩]; exact (ec ⟨x,hx⟩).property
      · intro hz
        let x := ec.symm ⟨z,hz⟩
        refine ⟨x.val,x.property,?_⟩
        rw [hφ x]; exact congrArg Subtype.val (ec.apply_symm_apply _)
    have hφI : φ '' Plane.openSquare 0 1 = inside (range g ∪ range h) := by
      rw [← inside_modelCurve]
      simpa only [hφC] using CurveComplex.jordan_inside_homeomorph_image φ modelCurve
    let f : Plane → S := M.planeToSphere v ∘ φ
    let A := φ.symm '' range g
    let B := φ.symm '' range h
    let p := φ.symm (g 0)
    let q := φ.symm (g 1)
    have hcancel (K : Set Plane) : φ '' (φ.symm '' K) = K := by
      ext z; simp
    have hgs (t) : M.planeToSphere v (g t) = f₀ t := congrArg Subtype.val (e.symm_apply_apply _)
    have hhs (t) : M.planeToSphere v (h t) = f₁ t := congrArg Subtype.val (e.symm_apply_apply _)
    refine ⟨f,A,B,p,q,(M.planeToSphere_isOpenEmbedding v).comp φ.isOpenEmbedding,
      hgA.image_of_injOn (Set.subset_univ _) φ.symm.continuous.continuousOn φ.symm.injective.injOn,
      hhB.image_of_injOn (Set.subset_univ _) φ.symm.continuous.continuousOn φ.symm.injective.injOn,?_,?_,?_,?_,?_,?_⟩
    · change φ.symm '' range g ∪ φ.symm '' range h = modelCurve
      rw [← image_union,← hφC]
      ext z; simp
    · change (M.planeToSphere v ∘ φ) '' (φ.symm '' range g) = _
      rw [image_comp,hcancel,← range_comp]; exact congrArg range (funext hgs)
    · change (M.planeToSphere v ∘ φ) '' (φ.symm '' range h) = _
      rw [image_comp,hcancel,← range_comp]; exact congrArg range (funext hhs)
    · change M.planeToSphere v (φ (φ.symm (g 0))) = _
      rw [φ.apply_symm_apply,hgs,hf₀0]
    · change M.planeToSphere v (φ (φ.symm (g 1))) = _
      rw [φ.apply_symm_apply,hgs,hf₀1]
    · change (M.planeToSphere v ∘ φ) '' Plane.openSquare 0 1 = _
      rw [image_comp,hφI,← hi,image_image]
      apply Set.image_congr
      intro x hx
      exact congrArg Subtype.val (e.symm_apply_apply _)
  have hrelativeRawDiskMove
      (f₀ f₁ : C(Interval,S)) (hf₀ : IsEmbedding f₀) (hf₁ : IsEmbedding f₁)
      (u z : S) (hf₀0 : f₀ 0=u) (hf₁0 : f₁ 0=u) (hf₀1 : f₀ 1=z) (hf₁1 : f₁ 1=z)
      (hinter : range f₀ ∩ range f₁ = {u,z})
      (disk : C(Metric.closedBall (0 : Plane) 1,S)) (hdisk : IsEmbedding disk)
      (hboundary : disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range f₀ ∪ range f₁)
      (w : S) (hw : w ∉ range disk)
      (Q : Set S) (hQc : IsClosed Q)
      (hQboundary : ∀ y ∈ range f₀ ∪ range f₁, y ∈ Q → y=u ∨ y=z)
      (hQinside : Disjoint (disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) Q) :
      ∃ H : CurveComplex.AmbientIsotopy S,
        (∀ t y, y ∈ Q → H.map (t,y)=y) ∧ H.finalMap '' range f₀ = range f₁ := by
    obtain ⟨F,A,B,p,q,hF,hA,hB,hwhole,hFA,hFB,hFp,hFq,hFI⟩ :=
      hrawDiskChart f₀ f₁ hf₀ hf₁ u z hf₀0 hf₁0 hf₀1 hf₁1 hinter disk hdisk hboundary w hw
    have hb : ∀ x ∈ modelCurve, F x ∈ Q → x=p ∨ x=q := by
      intro x hx hxQ
      have hxB : F x ∈ range f₀ ∪ range f₁ := by
        rw [← hFA,← hFB,← image_union,hwhole]
        exact mem_image_of_mem F hx
      rcases hQboundary (F x) hxB hxQ with hxu | hxz
      · exact Or.inl (hF.injective (hxu.trans hFp.symm))
      · exact Or.inr (hF.injective (hxz.trans hFq.symm))
    obtain ⟨H,hfix,hmove⟩ := CurveComplex.actual_raw_bigon_supported_replacement F hF A B p q
      hA hB hwhole Q hQc hb (by rwa [hFI])
    exact ⟨H,hfix,by simpa only [hFA,hFB] using hmove⟩
  exact hrelativeRawDiskMove f₀ f₁ hf₀ hf₁ u z hf₀0 hf₁0 hf₀1 hf₁1 hinter disk hdisk
    hboundary w hw Q hQc hQboundary hQinside

private theorem actual_inner_disk_supported_closed_piece_replacement
    (M : HyperellipticModel E S) (a b : NonLoopArc M) (N : ArcNeighborhood a)
    (D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (hDN : range D.disk ⊆ interior N.closedSet)
    (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
    (hempty : Disjoint D.openInterior (a.image ∪ b.image))
    (hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p) :
    ∃ (H : CurveComplex.AmbientIsotopy S) (C B R : Set S),
      (∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
      IsCompact C ∧ IsCompact B ∧ b.image=C ∪ R ∧
      H.finalMap '' b.image=B ∪ R ∧ Disjoint B (arcInterior M a.toEssential) ∧
      Disjoint (R ∩ arcInterior M a.toEssential) C ∧
      (ArcSurgery.crossings M a.toEssential b.toEssential ∩ C).Nonempty := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨u,v,c,g,e,huv,hu,hv,hc,hg,hc0,hc1,hcr,hremoved,hgA,hgB,hcg,he,heb,heN,heMarks⟩ :=
    actual_inner_disk_produces_enlarged_old_core_and_supporting_disk M a b N D hDN h0 h1 hempty hcross
  obtain ⟨R,hR,hOld,hCR,hRfree,hInsideR⟩ :=
    actual_mark_free_inner_support_disk_retained_remainder M a b u v c g hu hv hcr hgA hgB e he heb heMarks
  have hRb : R ⊆ b.image := hOld.symm ▸ subset_union_right
  have hBoundaryE : range c ∪ range g ⊆ range e := by rw [← heb]; exact image_subset_range _ _
  let Q : Set S := ((M.cover.branch:Set S) ∪ R) ∪ (interior N.closedSet)ᶜ
  have hQ : IsClosed Q := (M.cover.branch.isClosed.union hR.isClosed).union isOpen_interior.isClosed_compl
  have hQboundary : ∀ z ∈ range c ∪ range g, z ∈ Q → z=g 0 ∨ z=g 1 := by
    intro z hz hzQ
    rcases hzQ with hzQ | hzOut
    · rcases hzQ with hzmark | hzR
      · exact False.elim (disjoint_left.mp heMarks (hBoundaryE hz) hzmark)
      · rcases hz with hzC | hzG
        · exact hCR z ⟨hzC,hzR⟩
        · have hp : z ∈ ({g 0,g 1}:Set S) := hgB ▸ (show z ∈ range g ∩ b.image from ⟨hzG,hRb hzR⟩)
          simpa only [mem_insert_iff,mem_singleton_iff] using hp
    · exact False.elim (hzOut (heN (hBoundaryE hz)))
  have hQinside : Disjoint (e '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) Q := by
    apply disjoint_union_right.mpr
    refine ⟨disjoint_union_right.mpr ⟨heMarks.mono_left (image_subset_range _ _),hInsideR⟩,?_⟩
    exact disjoint_left.mpr (fun z hz hzOut => hzOut (heN (image_subset_range _ _ hz)))
  have hw : b.val.map (0:Interval) ∉ range e := fun hp => disjoint_left.mp heMarks hp b.val.start_marked
  obtain ⟨H,hfix,hmove⟩ := actual_raw_supporting_disk_motion_fixes_closed_obstacle M c g hc hg
    (g 0) (g 1) hc0 rfl hc1 rfl hcg e he heb (b.val.map 0) hw Q hQ hQboundary hQinside
  have hRimage : H.finalMap '' R=R := by
    apply Subset.antisymm
    · rintro z ⟨x,hx,rfl⟩
      have heq := hfix 1 x (Or.inl (Or.inr hx))
      change H.finalMap x=x at heq
      rw [heq]
      exact hx
    · intro z hz
      exact ⟨z,hz,hfix 1 z (Or.inl (Or.inr hz))⟩
  refine ⟨H,range c,range g,R,fun t x hx => hfix t x (Or.inr hx),
    fun t x hx => hfix t x (Or.inl (Or.inl hx)),isCompact_range c.continuous,isCompact_range g.continuous,hOld,?_,
    hgA.mono_right (show arcInterior M a.toEssential ⊆ a.image from inter_subset_left),hRfree,?_⟩
  · rw [hOld,image_union,hmove,hRimage]
  · exact ⟨D.firstCorner,⟨⟨D.first_on_curve ⟨0,D.first_zero⟩,h0⟩,D.second_on_curve ⟨0,D.second_zero⟩,h0⟩,hremoved⟩

private theorem actual_given_inner_disk_supported_strict_contact_drop
    (M : HyperellipticModel E S) (a b : NonLoopArc M) (N : ArcNeighborhood a)
    (hb : b.image ⊆ interior N.closedSet)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p)
    (D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (hDN : range D.disk ⊆ interior N.closedSet)
    (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
    (hempty : Disjoint D.openInterior (a.image ∪ b.image)) :
    ∃ b' : NonLoopArc M, ∃ H : CurveComplex.AmbientIsotopy S,
      (∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
      H.finalMap '' b.image=b'.image ∧ b'.image ⊆ interior N.closedSet ∧
      ({b'.val.map 0,b'.val.map 1}:Set S) = {b.val.map 0,b.val.map 1} ∧
      (ArcSurgery.crossings M a.toEssential b'.toEssential).Finite ∧
      (∀ p ∈ ArcSurgery.crossings M a.toEssential b'.toEssential,
        ArcSurgery.CrossesInDisk M a.toEssential b'.toEssential p) ∧
      (ArcSurgery.crossings M a.toEssential b'.toEssential).ncard <
        (ArcSurgery.crossings M a.toEssential b.toEssential).ncard := by
  obtain ⟨H,C,B,R,hsupport,hm,hC,hB,hOld,hNew,hBfree,hRfree,hremoved⟩ :=
    actual_inner_disk_supported_closed_piece_replacement M a b N D hDN h0 h1 hempty hcross
  obtain ⟨b',himage,hinside,hends,hfin,htrans,hdrop⟩ :=
    supported_closed_piece_contact_drop_assembly M a b N hb hfinite hcross H hsupport hm
      C B R hC hB hOld hNew hBfree hRfree hremoved
  exact ⟨b',H,hsupport,hm,himage,hinside,hends,hfin,htrans,hdrop⟩

#print axioms actual_given_inner_disk_supported_strict_contact_drop
#print axioms actual_inner_disk_supported_closed_piece_replacement
#print axioms actual_raw_supporting_disk_motion_fixes_closed_obstacle
#print axioms actual_mark_free_inner_support_disk_retained_remainder
#print axioms actual_inner_disk_produces_enlarged_old_core_and_supporting_disk
#print axioms disjoint_terminal_crosssections_select_core_containing_first_corner
#print axioms moving_core_between_ports_in_connected_trace
#print axioms embedded_terminal_crosssection_has_endpoint_outside_side
#print axioms actual_inner_disk_produces_two_terminal_rails
#print axioms compact_axis_produces_uniform_closed_band_inside_open
#print axioms actual_inner_selected_disk_produces_mark_free_enlarged_disk
#print axioms actual_inner_disk_two_corner_framing_inside_original_neighborhood
end CurveComplex.HyperellipticModel


namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
private def reversed_actual_two_side_disk (M : HyperellipticModel E S)
    (a b : EssentialMarkedArc M) (D : ActualMarkedTwoSideDisk M a b) :
    ActualMarkedTwoSideDisk M a b where
  firstCorner := D.secondCorner
  secondCorner := D.firstCorner
  firstSide := actualReverseEmbeddedSide D.firstSide
  secondSide := actualReverseEmbeddedSide D.secondSide
  first_embedded := actualReverseEmbeddedSide_embedded _ D.first_embedded
  second_embedded := actualReverseEmbeddedSide_embedded _ D.second_embedded
  first_zero := by simpa using D.first_one
  first_one := by simpa using D.first_zero
  second_zero := by simpa using D.second_one
  second_one := by simpa using D.second_zero
  first_on_curve := by rw [actualReverseEmbeddedSide_range]; exact D.first_on_curve
  second_on_curve := by rw [actualReverseEmbeddedSide_range]; exact D.second_on_curve
  sides_inter := by rw [actualReverseEmbeddedSide_range,actualReverseEmbeddedSide_range,D.sides_inter]; exact pair_comm _ _
  disk := D.disk
  disk_embedded := D.disk_embedded
  boundary_eq := by simpa only [actualReverseEmbeddedSide_range] using D.boundary_eq
  marks_are_corners := by intro p hp hm; exact (D.marks_are_corners p hp hm).symm

private theorem actual_selected_disk_supported_strict_contact_drop
    (M : HyperellipticModel E S) (a b : NonLoopArc M) (N : ArcNeighborhood a)
    (hb : b.image ⊆ interior N.closedSet)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p)
    (D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (hDN : range D.disk ⊆ interior N.closedSet)
    (hpositive : D.firstCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential ∨
      D.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential)
    (hempty : Disjoint D.openInterior (a.image ∪ b.image)) :
    ∃ b' : NonLoopArc M, ∃ H : CurveComplex.AmbientIsotopy S,
      (∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
      H.finalMap '' b.image=b'.image ∧ b'.image ⊆ interior N.closedSet ∧
      ({b'.val.map 0,b'.val.map 1}:Set S) = {b.val.map 0,b.val.map 1} ∧
      (ArcSurgery.crossings M a.toEssential b'.toEssential).Finite ∧
      (∀ p ∈ ArcSurgery.crossings M a.toEssential b'.toEssential,
        ArcSurgery.CrossesInDisk M a.toEssential b'.toEssential p) ∧
      (ArcSurgery.crossings M a.toEssential b'.toEssential).ncard <
        (ArcSurgery.crossings M a.toEssential b.toEssential).ncard := by
  classical
  have hfree : D.firstCorner ∉ M.cover.branch ∨ D.secondCorner ∉ M.cover.branch := by
    rcases hpositive with h | h
    · exact Or.inl h.1.2
    · exact Or.inr h.1.2
  by_cases h0 : D.firstCorner ∈ M.cover.branch
  · have h1 : D.secondCorner ∉ M.cover.branch := hfree.resolve_left (not_not_intro h0)
    obtain ⟨H,C,B,R,hs,hm,hC,hB,hOld,hNew,hBf,hRf,hr⟩ :=
      actual_first_marked_endpoint_disk_supported_closed_piece_replacement M a b N hb hfinite hcross D h0 h1 hempty
    obtain ⟨b',hi,hn,he,hf,ht,hd⟩ := supported_closed_piece_contact_drop_assembly M a b N hb hfinite hcross H hs hm C B R hC hB hOld hNew hBf hRf hr
    exact ⟨b',H,hs,hm,hi,hn,he,hf,ht,hd⟩
  · by_cases h1 : D.secondCorner ∈ M.cover.branch
    · let D' := reversed_actual_two_side_disk M a.toEssential b.toEssential D
      obtain ⟨H,C,B,R,hs,hm,hC,hB,hOld,hNew,hBf,hRf,hr⟩ :=
        actual_first_marked_endpoint_disk_supported_closed_piece_replacement M a b N hb hfinite hcross D' h1 h0 hempty
      obtain ⟨b',hi,hn,he,hf,ht,hd⟩ := supported_closed_piece_contact_drop_assembly M a b N hb hfinite hcross H hs hm C B R hC hB hOld hNew hBf hRf hr
      exact ⟨b',H,hs,hm,hi,hn,he,hf,ht,hd⟩
    · exact actual_given_inner_disk_supported_strict_contact_drop M a b N hb hfinite hcross D hDN h0 h1 hempty

theorem actual_two_mark_disk_supported_strict_contact_drop
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1})
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
      ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p)
    (hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty) :
    ∃ b' : NonLoopArc M, ∃ H : AmbientIsotopy S,
      (∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
      H.finalMap '' b.image=b'.image ∧ b'.image ⊆ interior N.closedSet ∧
      ({b'.val.map 0,b'.val.map 1}:Set S) = {b.val.map 0,b.val.map 1} ∧
      (ArcSurgery.crossings M a.toEssential b'.toEssential).Finite ∧
      (∀ p ∈ ArcSurgery.crossings M a.toEssential b'.toEssential,
        ArcSurgery.CrossesInDisk M a.toEssential b'.toEssential p) ∧
      (ArcSurgery.crossings M a.toEssential b'.toEssential).ncard <
        (ArcSurgery.crossings M a.toEssential b.toEssential).ncard := by
  obtain ⟨D,hDN,hempty,hcorner,_⟩ :=
    actual_two_mark_disk_inner_or_endpoint_bigon_selection M a b N hb hends hfinite hcross hpositive
  exact actual_selected_disk_supported_strict_contact_drop M a b N hb hfinite hcross D hDN
    hcorner (hempty.mono_right (subset_union_left))

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_two_mark_disk_relative_finite_cancellation
(M : HyperellipticModel E S) (a b : NonLoopArc M)
(N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
(hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1})
(hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
(hcross : ∀ p ∈ ArcSurgery.crossings M a.toEssential b.toEssential,
  ArcSurgery.CrossesInDisk M a.toEssential b.toEssential p) :
∃ b' : NonLoopArc M, ∃ H : AmbientIsotopy S,
  (∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x) ∧
  (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
  H.finalMap '' b.image=b'.image ∧ b'.image ⊆ interior N.closedSet ∧
  Disjoint (a.image \ (M.cover.branch:Set S))
    (b'.image \ (M.cover.branch:Set S)) := by
  induction hn : (ArcSurgery.crossings M a.toEssential b.toEssential).ncard
      using Nat.strong_induction_on generalizing b with
  | h n ih =>
    by_cases hzero : (ArcSurgery.crossings M a.toEssential b.toEssential).ncard = 0
    · exact relative_cancellation_zero_ncard M a b N hb hfinite hzero
    have hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty :=
      (Set.ncard_pos hfinite).mp (Nat.pos_of_ne_zero hzero)
    obtain ⟨c,H,hHout,hHmark,hHimage,hcN,hcends,hcfinite,hccross,hdrop⟩ :=
      actual_two_mark_disk_supported_strict_contact_drop M a b N hb hends hfinite hcross hpositive
    obtain ⟨d,K,hKout,hKmark,hKimage,hdN,hdisjoint⟩ :=
      ih (ArcSurgery.crossings M a.toEssential c.toEssential).ncard
        (hdrop.trans_eq hn) c hcN (hends.trans hcends.symm) hcfinite hccross rfl
    let P : Set S := (interior N.closedSet)ᶜ ∪ (M.cover.branch : Set S)
    have hHP : ∀ t x, x ∈ P → H.map (t,x)=x := by
      intro t x hx
      exact hx.elim (hHout t x) (hHmark t x)
    have hKP : ∀ t x, x ∈ P → K.map (t,x)=x := by
      intro t x hx
      exact hx.elim (hKout t x) (hKmark t x)
    obtain ⟨L,hLP,hLfinal⟩ := relative_cancellation_compose_motions H K P hHP hKP
    refine ⟨d,L,fun t x hx => hLP t x (Or.inl hx),
      fun t x hx => hLP t x (Or.inr hx),?_,hdN,hdisjoint⟩
    simp_rw [hLfinal]
    change (K.finalMap ∘ H.finalMap) '' b.image = d.image
    rw [Set.image_comp,hHimage,hKimage]

end CurveComplex.HyperellipticModel
