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
set_option maxHeartbeats 4000000
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_marked_nonloop_empty_disk_produces_retained_supporting_region
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
    (hbaseA : D.firstCorner = a.val.map 0) :
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
      Disjoint Ω (M.cover.branch : Set S) := by
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
        (old i).val.map (projIcc 0 1 zero_le_one β) = D.secondCorner ∧ IsEmbedding N ∧
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
        univ isOpen_univ (subset_univ _)
    exact ⟨β,N,hβ0,hβ1,hprefix,hlastParam.symm.trans D.second_one,hN,hcenter,σ (),δ (),η (),hsign (),
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
          rail.Homotopic (side.trans normal)) := by
    obtain ⟨β,N,hβ0,hβ1,hprefix,hβq,hN,hcenter,σ,δ,η,hsign,hδ,hη,hframe⟩ := hframedStrip hbase
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
    refine ⟨f,?_,hselectPort,hrailMarks,hpaths⟩
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
    obtain ⟨f,hf,hselect,hmarks,hpaths⟩ := hroundedFamilySides hbaseB
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
        Disjoint Ω (M.cover.branch : Set S) := by
    obtain ⟨f,hf,hselect,hmarks,hpaths⟩ := hroundedFamilySides hbaseB
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
    exact ⟨α,hi,f s,Ω,hα,hαhi,hhi,hprefix,(hf s).1,hg0,hport,
      (hf s).2.2.1,hgmeet,(hf s).2.2.2.2,hmarks s,hΩ⟩
  exact hRoundedRetainedSupportingRegion hbaseB hbaseA

end CurveComplex.HyperellipticModel
