import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerDiskQuadrantScaffold
import CurveComplexGenusTwo.Topology.ActualHarerDiskGluing.ActualHarerOptionalCollapseGluingProof
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualFiniteInteriorAxisFraming
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.VerifiedCarrierBridgeComponents
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import CurveComplexGenusTwo.Topology.ArcTrim.SupportedStrictDiskEnlargementStatement
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedSideEndpointMarks
import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.ModelCurve
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualStripSurfaceChart
import Mathlib.Topology.Order.IntermediateValue
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import Schoenflies.CrosscutEncloses
import CurveComplexGenusTwo.Topology.ActualHarerComparisonDisk.ActualHarerExteriorRail


set_option maxHeartbeats 8000000
open CurveComplex Set Topology Schoenflies

namespace ActualHarerWholeAnchorRail

private theorem disjoint_compact_anchor_family_constructs_whole_anchor_clear_strip
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {I : Type} [Finite I] (a : I → C(Interval,S))
    (ha : ∀ i, IsEmbedding (a i))
    (hdisjoint : ∀ i k, i ≠ k → Disjoint (range (a i)) (range (a k)))
    (i : I) :
    ∃ E : C(Interval × Set.Icc (-1:ℝ) 1,S),
      IsEmbedding E ∧
      (∀ t, E (t,⟨0,by norm_num⟩) = a i t) ∧
      (∀ k, k ≠ i → Disjoint (range E) (range (a k))) ∧
      ∀ (t : Interval) (w : Set.Icc (-1:ℝ) 1), (w : ℝ) ≠ 0 → E (t,w) ∉ ⋃ k,range (a k) := by
  classical
  let O : Set S := (⋃ k : {k : I // k≠i},range (a k.val))ᶜ
  have hO : IsOpen O := (isClosed_iUnion_of_finite
    (fun k : {k : I // k≠i} => (isCompact_range (a k.val).continuous).isClosed)).isOpen_compl
  have haiO : range (a i) ⊆ O := by
    intro y hy hother
    obtain ⟨k,hk⟩ := mem_iUnion.mp hother
    exact Set.disjoint_left.mp (hdisjoint i k.val k.property.symm) hy hk
  obtain ⟨E,hE,hcenter,hEO⟩ := source_whole_embedded_arc_strip (a i) (ha i) O hO haiO
  let Ec : C(Interval × Set.Icc (-1:ℝ) 1,S) := ⟨E,hE.continuous⟩
  have hOther : ∀ k,k≠i → Disjoint (range Ec) (range (a k)) := by
    intro k hki
    apply Set.disjoint_left.mpr
    intro y hy hyk
    exact hEO hy (mem_iUnion.mpr ⟨⟨k,hki⟩,hyk⟩)
  refine ⟨Ec,hE,hcenter,hOther,?_⟩
  intro t w hw hy
  obtain ⟨k,hk⟩ := mem_iUnion.mp hy
  by_cases hki : k=i
  · subst k
    obtain ⟨u,hu⟩ := hk
    have he : E (t,w)=E (u,⟨0,by norm_num⟩) := hu.symm.trans (hcenter u).symm
    exact hw (congrArg (fun z : Interval × Set.Icc (-1:ℝ) 1 => (z.2:ℝ)) (hE.injective he))
  · exact Set.disjoint_left.mp (hOther k hki) (Set.mem_range_self (t,w)) hk


private theorem actual_disjoint_whole_moving_family_constructs_local_exact_axis_chart
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {J : Type} [Finite J] (b : J → C(Interval,S))
    (hb : ∀ j,IsEmbedding (b j))
    (hdisjoint : ∀ j k,j≠k → Disjoint (range (b j)) (range (b k)))
    (j : J) (s : Interval) (hs : s∈Ioo (0:Interval) 1)
    (U : Set S) (hU : IsOpen U) (hps : b j s∈U) :
    ∃ Q : OpenPartialHomeomorph S Plane,
      b j s∈Q.source ∧ Q.source⊆U ∧ Q (b j s)=Plane.mk s 0 ∧
      (∀ k,k≠j → Disjoint Q.source (range (b k))) ∧
      (∀ y∈Q.source,y∈range (b j) ↔ Q y 1=0) ∧
      ∀ K : Set Plane,
        ({y : S | y∈Q.source ∧ Q y∈K}∩range (b j))=
        {y : S | y∈Q.source ∧ Q y∈K ∧ Q y 1=0} := by
  obtain ⟨E,hE,hcenter,hOther,_⟩ :=
    disjoint_compact_anchor_family_constructs_whole_anchor_clear_strip b hb hdisjoint j
  obtain ⟨Q,hQs,_,hQcoord,hQaxis⟩ :=
    source_embedded_strip_interior_chart E hE (b j) hcenter
  have hpQ : b j s∈Q.source := by
    rw [hQs]
    exact ⟨(s,⟨0,by norm_num⟩),⟨hs.1,hs.2,by norm_num,by norm_num⟩,hcenter s⟩
  let N := Q.restr U
  have hNs : N.source=Q.source∩U := by
    change Q.source∩interior U=Q.source∩U
    rw [hU.interior_eq]
  have hNp : b j s∈N.source := by rw [hNs];exact ⟨hpQ,hps⟩
  have hNaxis : ∀ y∈N.source,y∈range (b j) ↔ N y 1=0 := by
    intro y hy
    exact hQaxis y (by rw [hNs] at hy;exact hy.1)
  refine ⟨N,hNp,?_,?_,?_,hNaxis,?_⟩
  · rw [hNs];exact inter_subset_right
  · change Q (b j s)=Plane.mk s 0
    rw [← hcenter s]
    exact hQcoord (s,⟨0,by norm_num⟩) hs.1 hs.2 (by norm_num) (by norm_num)
  · intro k hkj
    apply Set.disjoint_left.mpr
    intro y hy hyk
    have hyQ : y∈Q.source := by rw [hNs] at hy;exact hy.1
    have hyE : y∈range E := by
      rw [hQs] at hyQ
      exact image_subset_range E _ hyQ
    exact Set.disjoint_left.mp (hOther k hkj) hyE hyk
  · intro K
    ext y
    constructor
    · rintro ⟨⟨hy,hK⟩,hbj⟩
      exact ⟨hy,hK,(hNaxis y hy).mp hbj⟩
    · rintro ⟨hy,hK,haxis⟩
      exact ⟨⟨hy,hK⟩,(hNaxis y hy).mpr haxis⟩

end ActualHarerWholeAnchorRail

namespace ActualHarerContactSides

private theorem actual_isolated_whole_trace_contact_constructs_two_signed_branch_windows
    {S : Type} [TopologicalSpace S]
    (a b : C(Interval,S)) (ha : IsEmbedding a)
    (Q : OpenPartialHomeomorph S Plane)
    (haxis : ∀ y∈Q.source,y∈range b ↔ Q y 1=0)
    (s : Interval) (hs : s∈Ioo (0:Interval) 1)
    (hpQ : a s∈Q.source)
    (hisolated : Q.source∩(range a∩range b)={a s}) :
    ∃ l r : Interval,l<s ∧ s<r ∧
      (∀ t∈Icc l r,a t∈Q.source) ∧
      ((∀ t∈Ico l s,Q (a t) 1<0) ∨ (∀ t∈Ico l s,0<Q (a t) 1)) ∧
      ((∀ t∈Ioc s r,Q (a t) 1<0) ∨ (∀ t∈Ioc s r,0<Q (a t) 1)) := by
  have hn : a ⁻¹' Q.source∈nhds s := (Q.open_source.preimage a.continuous).mem_nhds hpQ
  obtain ⟨l₀,r₀,hs₀,hlocal⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0,hs.1⟩ ⟨1,hs.2⟩).mp hn
  obtain ⟨l,hl₀,hls⟩ := exists_between hs₀.1
  obtain ⟨r,hsr,hrr₀⟩ := exists_between hs₀.2
  have hin : ∀ t∈Icc l r,a t∈Q.source := by
    intro t ht
    exact hlocal ⟨hl₀.trans_le ht.1,ht.2.trans_lt hrr₀⟩
  let z : Interval → ℝ := fun t => Q (a t) 1
  have hzc : ContinuousOn z (Icc l r) :=
    (Plane.continuous_coord 1).continuousOn.comp
      (Q.continuousOn.comp a.continuous.continuousOn hin) (fun _ _ => Set.mem_univ _)
  have hnz : ∀ t∈Icc l r,t≠s → z t≠0 := by
    intro t ht hts hz
    have hbt : a t∈range b := (haxis _ (hin t ht)).mpr hz
    have he : a t=a s := by
      have hmem : a t∈Q.source∩(range a∩range b) :=
        ⟨hin t ht,Set.mem_range_self t,hbt⟩
      exact Set.mem_singleton_iff.mp (hisolated ▸ hmem)
    exact hts (ha.injective he)
  have hleft : ∀ t∈Ico l s,z t≠0 := by
    intro t ht
    exact hnz t ⟨ht.1,ht.2.le.trans hsr.le⟩ (ne_of_lt ht.2)
  have hright : ∀ t∈Ioc s r,z t≠0 := by
    intro t ht
    exact hnz t ⟨hls.le.trans ht.1.le,ht.2⟩ (ne_of_gt ht.1)
  have hzl : ContinuousOn z (Ico l s) := hzc.mono (fun t ht =>
    ⟨ht.1,ht.2.le.trans hsr.le⟩)
  have hzr : ContinuousOn z (Ioc s r) := hzc.mono (fun t ht =>
    ⟨hls.le.trans ht.1.le,ht.2⟩)
  refine ⟨l,r,hls,hsr,hin,?_,?_⟩
  · have hl : l∈Ico l s := ⟨le_refl _,hls⟩
    rcases lt_or_gt_of_ne (hleft l hl) with hneg | hpos
    · exact Or.inl (fun t ht => isPreconnected_Ico.gt_of_ne hzl hleft ⟨l,hl,hneg⟩ ht)
    · exact Or.inr (fun t ht => isPreconnected_Ico.lt_of_ne hzl hleft ⟨l,hl,hpos⟩ ht)
  · have hr : r∈Ioc s r := ⟨hsr,le_refl _⟩
    rcases lt_or_gt_of_ne (hright r hr) with hneg | hpos
    · exact Or.inl (fun t ht => isPreconnected_Ioc.gt_of_ne hzr hright ⟨r,hr,hneg⟩ ht)
    · exact Or.inr (fun t ht => isPreconnected_Ioc.lt_of_ne hzr hright ⟨r,hr,hpos⟩ ht)



end ActualHarerContactSides

namespace ActualHarerWholeGraph

private theorem actual_disjoint_finite_arc_families_corner_constructs_other_labels_clear_open_neighborhood
    (S : Type) [TopologicalSpace S] [T2Space S]
    (I J : Type) [Finite I] [Finite J]
    (a : I → C(Interval,S)) (b : J → C(Interval,S))
    (ha : ∀ i k,i≠k → Disjoint (Set.range (a i)) (Set.range (a k)))
    (hb : ∀ j k,j≠k → Disjoint (Set.range (b j)) (Set.range (b k)))
    (i : I) (j : J) (p : S)
    (hpa : p∈Set.range (a i)) (hpb : p∈Set.range (b j))
    (V : Set S) (hV : IsOpen V) (hpV : p∈V) :
    ∃ U : Set S, IsOpen U ∧ p∈U ∧ U⊆V ∧
      (∀ k,k≠i → Disjoint U (Set.range (a k))) ∧
      (∀ k,k≠j → Disjoint U (Set.range (b k))) := by
  classical
  let A : Set S := ⋃ k : {k : I // k≠i},Set.range (a k.val)
  let B : Set S := ⋃ k : {k : J // k≠j},Set.range (b k.val)
  have hAc : IsClosed A := isClosed_iUnion_of_finite
    (fun k : {k : I // k≠i} => (isCompact_range (a k.val).continuous).isClosed)
  have hBc : IsClosed B := isClosed_iUnion_of_finite
    (fun k : {k : J // k≠j} => (isCompact_range (b k.val).continuous).isClosed)
  have hpA : p∉A := by
    intro hp
    obtain ⟨k,hk⟩ := mem_iUnion.mp hp
    exact Set.disjoint_left.mp (ha i k.val (Ne.symm k.property)) hpa hk
  have hpB : p∉B := by
    intro hp
    obtain ⟨k,hk⟩ := mem_iUnion.mp hp
    exact Set.disjoint_left.mp (hb j k.val (Ne.symm k.property)) hpb hk
  refine ⟨V∩(A∪B)ᶜ,hV.inter (hAc.union hBc).isOpen_compl,
    ⟨hpV,fun hp => hp.elim hpA hpB⟩,inter_subset_left,?_,?_⟩
  · intro k hki
    apply Set.disjoint_left.mpr
    intro x hx hxk
    exact hx.2 (Or.inl (mem_iUnion.mpr ⟨⟨k,hki⟩,hxk⟩))
  · intro k hkj
    apply Set.disjoint_left.mpr
    intro x hx hxk
    exact hx.2 (Or.inr (mem_iUnion.mpr ⟨⟨k,hkj⟩,hxk⟩))

private theorem actual_finite_whole_graph_genuine_contact_constructs_isolated_clear_open_neighborhood
    {S : Type} [TopologicalSpace S] [T2Space S]
    {I J : Type} [Finite I] [Finite J]
    (a : I → C(Interval,S)) (b : J → C(Interval,S))
    (ha : ∀ i k,i≠k → Disjoint (Set.range (a i)) (Set.range (a k)))
    (hb : ∀ j k,j≠k → Disjoint (Set.range (b j)) (Set.range (b k)))
    (hfinite : ((⋃ i,Set.range (a i))∩⋃ j,Set.range (b j)).Finite)
    (F : Set S) (i : I) (j : J) (p : S)
    (hpa : p∈Set.range (a i)) (hpb : p∈Set.range (b j))
    (hpF : p∈F) (hpFront : p∉frontier F) :
    ∃ U : Set S,IsOpen U ∧ p∈U ∧ U⊆interior F ∧
      (∀ k,k≠i → Disjoint U (Set.range (a k))) ∧
      (∀ k,k≠j → Disjoint U (Set.range (b k))) ∧
      U∩((⋃ k,Set.range (a k))∩⋃ k,Set.range (b k))={p} := by
  classical
  let C : Set S := (⋃ k,Set.range (a k))∩⋃ k,Set.range (b k)
  have hpC : p∈C := ⟨mem_iUnion.mpr ⟨i,hpa⟩,mem_iUnion.mpr ⟨j,hpb⟩⟩
  have hpInt : p∈interior F := by
    by_contra hn
    exact hpFront ((mem_frontier_iff_notMem_interior hpF).mpr hn)
  let V : Set S := interior F∩(C\{p})ᶜ
  have hV : IsOpen V := isOpen_interior.inter
    (hfinite.diff (t := {p})).isClosed.isOpen_compl
  have hpV : p∈V := ⟨hpInt,fun hp => hp.2 (Set.mem_singleton p)⟩
  obtain ⟨U,hU,hpU,hUV,hUa,hUb⟩ :=
    actual_disjoint_finite_arc_families_corner_constructs_other_labels_clear_open_neighborhood
      S I J a b ha hb i j p hpa hpb V hV hpV
  refine ⟨U,hU,hpU,fun y hy => (hUV hy).1,hUa,hUb,?_⟩
  ext y
  constructor
  · rintro ⟨hyU,hyC⟩
    have hyNot : y∉C\{p} := (hUV hyU).2
    by_contra hyn
    exact hyNot ⟨hyC,hyn⟩
  · intro hy
    have hyp : y=p := hy
    subst y
    exact ⟨hpU,hpC⟩

end ActualHarerWholeGraph

namespace ActualHarerSupportedBypass

private theorem embedded_surface_disk_frontier_eq_boundary_image
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d) :
    frontier (Set.range d) =
      d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
  have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
  rw [hclosed.frontier_eq,
    CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd]
  ext p
  constructor
  · rintro ⟨⟨x, rfl⟩, hxnot⟩
    refine ⟨x, ?_, rfl⟩
    have hxle : dist x.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 := x.property
    have hxge : 1 ≤ dist x.val (0 : EuclideanSpace ℝ (Fin 2)) := by
      by_contra hn
      apply hxnot
      exact ⟨x, lt_of_not_ge hn, rfl⟩
    exact le_antisymm hxle hxge
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro ⟨y, hy, he⟩
    have hxy := hd.injective he
    subst y
    change dist x.val (0 : EuclideanSpace ℝ (Fin 2)) < 1 at hy
    change dist x.val (0 : EuclideanSpace ℝ (Fin 2)) = 1 at hx
    linarith





private theorem embedded_disk_interior_chart {S : Type} [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (e : C(Metric.closedBall (0 : Plane) 1,S)) (he : IsEmbedding e) :
    ∃ F : OpenPartialHomeomorph S Plane,
      F.source = interior (range e) ∧ F.target = Metric.ball (0 : Plane) 1 ∧
      ∀ z (hz : z ∈ Metric.ball (0 : Plane) 1),
        F.symm z = e ⟨z,Metric.ball_subset_closedBall hz⟩ := by
  classical
  let B := Metric.ball (0 : Plane) 1
  let incl : B → Metric.closedBall (0 : Plane) 1 :=
    fun z => ⟨z.val,Metric.ball_subset_closedBall z.property⟩
  have hi : IsEmbedding incl :=
    Topology.IsEmbedding.subtypeVal.codRestrict _ _
  let f : B → S := e ∘ incl
  have hf : IsEmbedding f := he.comp hi
  have hr : range f = interior (range e) := by
    rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq e he]
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨incl z,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z.val,hz⟩,rfl⟩
  have hfo : IsOpenEmbedding f := ⟨hf,hr.symm ▸ isOpen_interior⟩
  letI : Nonempty B := ⟨⟨0,by simp [B]⟩⟩
  let G := hfo.toOpenPartialHomeomorph f
  let J := (Metric.isOpen_ball : IsOpen B).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : B → Plane)
  let F := G.symm.trans J
  have hFs : F.source = interior (range e) := by
    simp only [F,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
      G,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
      J,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
    exact hr
  have hFt : F.target = B := by
    simp only [F,OpenPartialHomeomorph.trans_target,OpenPartialHomeomorph.symm_target,
      G,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
      J,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,preimage_univ,inter_univ, Subtype.range_val]
  refine ⟨F,hFs,hFt,?_⟩
  intro z hz
  change G (J.symm z) = _
  change f (J.symm z) = _
  have hJt : J.target = B := by simp [J]
  have hj : (J.symm z).val = z := J.right_inv (hJt.symm ▸ hz)
  change e (incl (J.symm z)) = _
  congr 1
  exact Subtype.ext hj


private theorem actual_embedded_closed_disk_constructs_containing_ambient_chart
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (d : C(Metric.closedBall (0:Plane) 1,S)) (hd : IsEmbedding d) :
    ∃ Q : OpenPartialHomeomorph S Plane,
      range d⊆Q.source ∧ Q.target=Metric.ball (0:Plane) 1 := by
  obtain ⟨_,e,he,hde,_,_,_,_⟩ :=
    CurveComplex.LocalSurgery.exists_supported_strict_disk_enlargement
      d hd univ isOpen_univ (subset_univ _)
  obtain ⟨Q,hQsource,hQtarget,_⟩ := embedded_disk_interior_chart e he
  exact ⟨Q,hQsource.symm ▸ hde,hQtarget⟩

private theorem actual_embedded_closed_disk_constructs_full_plane_ambient_chart
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (d : C(Metric.closedBall (0:Plane) 1,S)) (hd : IsEmbedding d) :
    ∃ E : OpenPartialHomeomorph S Plane,range d⊆E.source ∧ E.target=univ := by
  obtain ⟨Q,hDQ,hQt⟩ := actual_embedded_closed_disk_constructs_containing_ambient_chart d hd
  let H : OpenPartialHomeomorph Plane Plane := OpenPartialHomeomorph.univUnitBall
  let E := Q.trans H.symm
  have hEs : E.source=Q.source := by
    ext x
    simp only [E,OpenPartialHomeomorph.trans_source,mem_inter_iff,mem_preimage]
    constructor
    · exact fun h => h.1
    · intro hx
      refine ⟨hx,?_⟩
      change Q x∈Metric.ball (0:Plane) 1
      exact hQt ▸ Q.map_source hx
  have hEt : E.target=univ := by
    ext z
    simp only [E,OpenPartialHomeomorph.trans_target,mem_inter_iff,mem_preimage]
    constructor
    · intro _;exact mem_univ z
    · intro _
      refine ⟨mem_univ z,?_⟩
      change H z∈Q.target
      rw [hQt]
      exact H.map_source (mem_univ z)
  exact ⟨E,hEs.symm ▸ hDQ,hEt⟩


private theorem actual_disk_boundary_curve {S : Type} [TopologicalSpace S] (d : C(Metric.closedBall (0 : Plane) 1,S)) (hd : Topology.IsEmbedding d) :
  ∃ c : Curve S, c.image = d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
  classical
  let L : ℂ ≃L[ℝ] Plane := Complex.equivRealProdCLM.trans
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
      (EuclideanSpace.equiv (Fin 2) ℝ).symm)
  have hnorm (z : ℂ) : ‖L z‖ = ‖z‖ := by
    change ‖Plane.mk z.re z.im‖ = ‖z‖
    simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk,
      Complex.norm_def,Complex.normSq_apply,Real.norm_eq_abs,pow_two]
  let q : Circle → Metric.closedBall (0 : Plane) 1 := fun z =>
    ⟨L (z : ℂ),Metric.mem_closedBall.mpr (by rw [dist_zero_right,hnorm,Circle.norm_coe])⟩
  have hq : Topology.IsEmbedding q := by
    apply (L.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict
  let c : Curve S := ⟨d ∘ q,hd.comp hq⟩
  refine ⟨c,?_⟩
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    refine ⟨q z,?_,rfl⟩
    change dist (L (z : ℂ)) 0 = 1
    rw [dist_zero_right,hnorm,Circle.norm_coe]
  · rintro ⟨x,hx,rfl⟩
    have hzN : ‖L.symm x.val‖ = 1 := by
      rw [← hnorm (L.symm x.val),L.apply_symm_apply]
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hx
    let z : Circle := ⟨L.symm x.val,by change L.symm x.val ∈ Metric.sphere (0 : ℂ) 1; simpa only [Metric.mem_sphere,dist_zero_right] using hzN⟩
    refine ⟨z,?_⟩
    change d (q z) = d x
    congr 1
    apply Subtype.ext
    exact L.apply_symm_apply x.val

private theorem actual_disk_boundary_sides_intersection
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (q g : C(Interval,S)) (hq : IsEmbedding q) (hg : IsEmbedding g)
    (hzero : q 0=g 0) (hone : q 1=g 1)
    (d : C(Metric.closedBall (0:Plane) 1,S)) (hd : IsEmbedding d)
    (hboundary : d '' {z | z.val∈Metric.sphere (0:Plane) 1}=range q∪range g) :
    range q∩range g=({q 0,q 1}:Set S) := by
  classical
  obtain ⟨E,hDE,_⟩ := actual_embedded_closed_disk_constructs_full_plane_ambient_chart d hd
  obtain ⟨c,hc⟩ := actual_disk_boundary_curve d hd
  have hcE : c.image⊆E.source := by rw [hc];exact (image_subset_range _ _).trans hDE
  let r : C(Circle,Plane) := ⟨E ∘ c.map,
    E.continuousOn.comp_continuous c.embedded.continuous (fun z => hcE (mem_range_self z))⟩
  have hr : IsEmbedding r :=
    (r.continuous.isClosedEmbedding (by
      intro z w he
      exact c.embedded.injective (E.injOn (hcE (mem_range_self z)) (hcE (mem_range_self w)) he))).isEmbedding
  have hrange : range r=E '' (range q∪range g) := by
    change range (E ∘ c.map)=E '' (range q∪range g)
    rw [range_comp,show range c.map=range q∪range g from hc.trans hboundary]
  have hqE : range q⊆E.source := by
    intro x hx
    apply hDE
    apply image_subset_range d _
    rw [hboundary]
    exact Or.inl hx
  have hgE : range g⊆E.source := by
    intro x hx
    apply hDE
    apply image_subset_range d _
    rw [hboundary]
    exact Or.inr hx
  have hArc (f : C(Interval,S)) (hf : IsEmbedding f) (hfE : range f⊆E.source) :
      IsArcBetween (E '' range f) (E (f 0)) (E (f 1)) := by
    let F : ℝ→Plane := fun t => E (f (projIcc 0 1 zero_le_one t))
    have hfc : Continuous F := E.continuousOn.comp_continuous
      (f.continuous.comp continuous_projIcc) (fun t => hfE (mem_range_self _))
    have hfi : InjOn F unitInterval := by
      intro z hz w hw he
      have h := hf.injective (E.injOn (hfE (mem_range_self _)) (hfE (mem_range_self _)) he)
      have h' := congrArg Subtype.val h
      simpa only [projIcc_of_mem zero_le_one hz,projIcc_of_mem zero_le_one hw] using h'
    have hfr : F '' unitInterval=E '' range f := by
      ext y
      constructor
      · rintro ⟨t,ht,rfl⟩;exact ⟨f (projIcc 0 1 zero_le_one t),mem_range_self _,rfl⟩
      · rintro ⟨_,⟨t,rfl⟩,rfl⟩
        exact ⟨t.val,t.property,by simp only [F,projIcc_of_mem zero_le_one t.property]⟩
    refine ⟨F,hfc.continuousOn,hfi,hfr,?_,?_⟩
    · simp [F,projIcc_of_mem]
    · simp [F,projIcc_of_mem]
  have hinter : (E '' range q)∩(E '' range g)={E (q 0),E (q 1)} := by
    apply two_arcs_inter_of_union (C:=range r)
      (CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr) (hArc q hq hqE)
    · simpa only [←hzero,←hone] using hArc g hg hgE
    · rw [←image_union,←hrange]
  ext x
  constructor
  · intro hx
    have hEx : E x∈({E (q 0),E (q 1)}:Set Plane) := hinter ▸ ⟨mem_image_of_mem E hx.1,mem_image_of_mem E hx.2⟩
    rcases hEx with he | he
    · exact Or.inl (E.injOn (hqE hx.1) (hqE (mem_range_self 0)) he)
    · exact Or.inr (E.injOn (hqE hx.1) (hqE (mem_range_self 1)) he)
  · rintro (rfl | rfl)
    · exact ⟨mem_range_self 0,⟨0,hzero.symm⟩⟩
    · exact ⟨mem_range_self 1,⟨1,hone.symm⟩⟩

private theorem actual_embedded_subarc_constructs_exact_unordered_parameter_interval
    {S : Type} [TopologicalSpace S]
    (f g : C(Interval,S)) (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hsub : range g⊆range f) :
    ∃ r t : Interval,r≠t ∧ f r=g 0 ∧ f t=g 1 ∧ range g=f '' uIcc r t := by
  let G : C(Interval,range f) := ⟨fun z => ⟨g z,hsub (mem_range_self z)⟩,
    g.continuous.subtype_mk _⟩
  let k : Interval→Interval := hf.toHomeomorph.symm ∘ G
  have hk : Continuous k := hf.toHomeomorph.symm.continuous.comp G.continuous
  have hfk (z : Interval) : f (k z)=g z :=
    congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply (G z))
  have hki : Function.Injective k := by
    intro z w he
    apply hg.injective
    rw [←hfk z,←hfk w,he]
  have hkrange : range k=uIcc (k 0) (k 1) := by
    have hUniv : (univ:Set Interval)=Icc (0:Interval) 1 := by
      ext z
      simp only [mem_univ,mem_Icc,true_iff]
      exact z.property
    rw [←image_univ,hUniv]
    rcases hk.strictMono_of_inj_boundedOrder' hki with hm | hm
    · rw [hk.continuousOn.image_Icc_of_monotoneOn zero_le_one (hm.monotone.monotoneOn _)]
      exact (uIcc_of_le (hm zero_lt_one).le).symm
    · rw [hk.continuousOn.image_Icc_of_antitoneOn zero_le_one (hm.antitone.antitoneOn _)]
      exact (uIcc_of_ge (hm zero_lt_one).le).symm
  refine ⟨k 0,k 1,fun he => zero_ne_one (hki he),hfk 0,hfk 1,?_⟩
  rw [←hkrange]
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨k z,mem_range_self z,hfk z⟩
  · rintro ⟨z,⟨w,hw⟩,hx⟩
    exact ⟨w,(hfk w).symm.trans ((congrArg f hw).trans hx)⟩

private theorem actual_selected_arc_interval_constructs_embedded_literal_old_subarc
    {S : Type} [TopologicalSpace S] [T2Space S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (α β : Interval) (hαβ : α<β) :
    ∃ old : C(Interval,S),IsEmbedding old ∧ old 0=f α ∧ old 1=f β ∧
      range old=f '' Icc α β := by
  let k : Interval→Interval := fun w =>
    ⟨(1-w.val)*α.val+w.val*β.val,by
      constructor <;> nlinarith [α.property.1,α.property.2,β.property.1,β.property.2,
        w.property.1,w.property.2]⟩
  have hk : Continuous k := by fun_prop
  let old : C(Interval,S) := ⟨f ∘ k,f.continuous.comp hk⟩
  have hdiff : 0<β.val-α.val := sub_pos.mpr hαβ
  have hki : Function.Injective k := by
    intro w z he
    have hv := congrArg Subtype.val he
    apply Subtype.ext
    change (1-w.val)*α.val+w.val*β.val=(1-z.val)*α.val+z.val*β.val at hv
    nlinarith
  have hOld : IsEmbedding old :=
    ((f.continuous.comp hk).isClosedEmbedding (hf.injective.comp hki)).isEmbedding
  refine ⟨old,hOld,?_,?_,?_⟩
  · change f (k 0)=f α
    congr 1
    apply Subtype.ext
    norm_num [k]
  · change f (k 1)=f β
    congr 1
    apply Subtype.ext
    norm_num [k]
  · ext x
    constructor
    · rintro ⟨w,rfl⟩
      refine ⟨k w,?_,rfl⟩
      change α.val≤(1-w.val)*α.val+w.val*β.val ∧
        (1-w.val)*α.val+w.val*β.val≤β.val
      constructor <;> nlinarith [w.property.1,w.property.2]
    · rintro ⟨t,ht,rfl⟩
      let w : Interval := ⟨(t.val-α.val)/(β.val-α.val),by
        constructor
        · exact div_nonneg (sub_nonneg.mpr ht.1) hdiff.le
        · exact (div_le_one hdiff).mpr (by have htβ : t.val≤β.val := ht.2; linarith)⟩
      refine ⟨w,?_⟩
      change f (k w)=f t
      congr 1
      apply Subtype.ext
      change (1-(t.val-α.val)/(β.val-α.val))*α.val+
        ((t.val-α.val)/(β.val-α.val))*β.val=t.val
      field_simp
      ring


theorem actual_clean_crossing_disk_constructs_whole_moving_trace_comparison_disk
    (S : Type) [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (I J : Type) [Finite I] [Finite J]
    (a : I → C(Interval, ↥F)) (b : J → C(Interval, ↥F))
    (ha : ∀ i, IsEmbedding (a i))
    (hb : ∀ j, IsEmbedding (b j))
    (hadisjoint : ∀ i k, i ≠ k →
      Disjoint (Set.range (a i)) (Set.range (a k)))
    (hbdisjoint : ∀ j k, j ≠ k →
      Disjoint (Set.range (b j)) (Set.range (b k)))
    (hfinite : ((⋃ i, Set.range (a i)) ∩ (⋃ j, Set.range (b j))).Finite)
    (ha0 : ∀ i, (a i 0).val ∈ frontier F)
    (ha1 : ∀ i, (a i 1).val ∈ frontier F)
    (hb0 : ∀ j, (b j 0).val ∈ frontier F)
    (hb1 : ∀ j, (b j 1).val ∈ frontier F)
    (haClear : ∀ i t, t ∈ Set.Ioo (0 : Interval) 1 →
      (a i t).val ∉ frontier F)
    (hbClear : ∀ j t, t ∈ Set.Ioo (0 : Interval) 1 →
      (b j t).val ∉ frontier F)
    (i : I) (j : J) (q g : C(Interval, S))
    (hq : IsEmbedding q) (hg : IsEmbedding g)
    (hqa : Set.range q ⊆ Set.range (fun t : Interval => (a i t).val))
    (hgb : Set.range g ⊆ Set.range (fun t : Interval => (b j t).val))
    (hzero : q 0 = g 0) (hone : q 1 = g 1)
    (d : C(Metric.closedBall (0 : Plane) 1, S))
    (hd : IsEmbedding d)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      Set.range q ∪ Set.range g)
    (hdF : Set.range d ⊆ F)
    (hempty : Disjoint (d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
      ((⋃ k, Set.range (fun t : Interval => (a k t).val)) ∪
        (⋃ k, Set.range (fun t : Interval => (b k t).val))))
    (hgenuine : q 0 ∉ frontier F ∨ q 1 ∉ frontier F)
    (hcleanA : range d∩(⋃ k,range (fun t:Interval => (a k t).val))=range q)
    (hcleanB : range d∩(⋃ k,range (fun t:Interval => (b k t).val))=range g)
    (hcross : ∀ v:Interval,(v=0 ∨ v=1) → q v∉frontier F →
      ∃ (s t l h : Interval) (Q : OpenPartialHomeomorph S Plane) (ε : ℝ),
        s∈Ioo (0:Interval) 1 ∧ t∈Ioo (0:Interval) 1 ∧
        (a i s).val=q v ∧ (b j t).val=q v ∧ l<s ∧ s<h ∧
        (ε=(-1:ℝ) ∨ ε=1) ∧ q v∈Q.source ∧ Q.source⊆interior F ∧
        (∀ y:↥F,y.val∈Q.source → (y∈range (b j) ↔ Q y.val 1=0)) ∧
        (∀ w∈Icc l h,(a i w).val∈Q.source) ∧
        (∀ w∈Ico l s,ε*(Q ((a i w).val)) 1<0) ∧
        (∀ w∈Ioc s h,0<ε*(Q ((a i w).val)) 1)) :
    ∃ (α β : Interval) (old new : C(Interval,S))
      (e : C(Metric.closedBall (0:Plane) 1,S)),
      α<β ∧ IsEmbedding old ∧ IsEmbedding new ∧ IsEmbedding e ∧
      old 0=(b j α).val ∧ old 1=(b j β).val ∧
      range old=(fun t:Interval => (b j t).val) '' Icc α β ∧
      range g⊆range old ∧ new 0=old 0 ∧ new 1=old 1 ∧
      range old∩range new=({old 0,old 1}:Set S) ∧
      e '' {z | z.val∈Metric.sphere (0:Plane) 1}=range old∪range new ∧
      range d⊆range e ∧ range e⊆F ∧
      range e∩(⋃ k,range (fun t:Interval => (b k t).val))=range old ∧
      range e∩frontier F⊆({old 0,old 1}:Set S) ∧
      Disjoint (range new\{old 0,old 1})
        (⋃ k,range (fun t:Interval => (a k t).val)) ∧
      ∃ v:Interval,(v=0 ∨ v=1) ∧ q v∉frontier F ∧
        q v∈range old\{old 0,old 1} := by
  classical
  obtain ⟨DiskChart,hDiskChart,hDiskChartTarget⟩ :=
    actual_embedded_closed_disk_constructs_full_plane_ambient_chart d hd
  obtain ⟨v,hv,hvFront⟩ : ∃ v : Interval, (v=0 ∨ v=1) ∧ q v∉frontier F := by
    rcases hgenuine with h0 | h1
    · exact ⟨0,Or.inl rfl,h0⟩
    · exact ⟨1,Or.inr rfl,h1⟩
  have hqg : q v=g v := by
    rcases hv with rfl | rfl
    · exact hzero
    · exact hone
  obtain ⟨s,hs⟩ := hqa (Set.mem_range_self v)
  obtain ⟨t,ht⟩ := hgb (show q v∈range g from ⟨v,hqg.symm⟩)
  have hs0 : s≠0 := by
    intro he
    exact hvFront (hs ▸ he ▸ ha0 i)
  have hs1 : s≠1 := by
    intro he
    exact hvFront (hs ▸ he ▸ ha1 i)
  have ht0 : t≠0 := by
    intro he
    exact hvFront (ht ▸ he ▸ hb0 j)
  have ht1 : t≠1 := by
    intro he
    exact hvFront (ht ▸ he ▸ hb1 j)
  have hsInterior : s∈Ioo (0:Interval) 1 :=
    ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),lt_of_le_of_ne s.property.2 hs1⟩
  have htInterior : t∈Ioo (0:Interval) 1 :=
    ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
  have hcontact : (a i s).val=(b j t).val := hs.trans ht.symm
  let av : I → C(Interval,S) := fun k => ⟨fun t => (a k t).val,continuous_subtype_val.comp (a k).continuous⟩
  let bv : J → C(Interval,S) := fun k => ⟨fun t => (b k t).val,continuous_subtype_val.comp (b k).continuous⟩
  have had : ∀ k m,k≠m → Disjoint (range (av k)) (range (av m)) := by
    intro k m hkm
    apply Set.disjoint_left.mpr
    rintro x ⟨r,hr⟩ ⟨t,ht⟩
    have he : a k r=a m t := Subtype.ext (hr.trans ht.symm)
    exact Set.disjoint_left.mp (hadisjoint k m hkm) (mem_range_self r) ⟨t,he.symm⟩
  have hbd : ∀ k m,k≠m → Disjoint (range (bv k)) (range (bv m)) := by
    intro k m hkm
    apply Set.disjoint_left.mpr
    rintro x ⟨r,hr⟩ ⟨t,ht⟩
    have he : b k r=b m t := Subtype.ext (hr.trans ht.symm)
    exact Set.disjoint_left.mp (hbdisjoint k m hkm) (mem_range_self r) ⟨t,he.symm⟩
  have hfin : ((⋃ k,range (av k))∩⋃ k,range (bv k)).Finite := by
    apply (hfinite.image (fun y:↥F => y.val)).subset
    rintro x ⟨hxA,hxB⟩
    obtain ⟨k,r,hr⟩ := mem_iUnion.mp hxA
    obtain ⟨m,t,ht⟩ := mem_iUnion.mp hxB
    refine ⟨a k r,⟨mem_iUnion.mpr ⟨k,mem_range_self r⟩,?_⟩,hr⟩
    exact mem_iUnion.mpr ⟨m,⟨t,Subtype.ext (ht.trans hr.symm)⟩⟩
  obtain ⟨U,hU,hpU,hUF,hUa,hUb,hiso⟩ :=
    ActualHarerWholeGraph.actual_finite_whole_graph_genuine_contact_constructs_isolated_clear_open_neighborhood
      av bv had hbd hfin F i j (q v) ⟨s,hs⟩ ⟨t,ht⟩
      (hs ▸ (a i s).property) hvFront
  have hbemb : ∀ k,IsEmbedding (bv k) := by
    intro k
    exact IsEmbedding.subtypeVal.comp (hb k)
  obtain ⟨Q,hpQ,hQU,hQp,hOther,haxis,htrace⟩ :=
    ActualHarerWholeAnchorRail.actual_disjoint_whole_moving_family_constructs_local_exact_axis_chart
      bv hbemb hbd j t htInterior U hU (by have ht' : (b j t).val=q v := ht; change (b j t).val∈U; rw [ht']; exact hpU)
  have hgInternalClear : ∀ w∈Ioo (0:Interval) 1,g w∉frontier F := by
    intro w hw hFront
    obtain ⟨z,hz⟩ := hgb (mem_range_self w)
    have hzEnd : z=0 ∨ z=1 := by
      by_cases hz0 : z=0
      · exact Or.inl hz0
      by_cases hz1 : z=1
      · exact Or.inr hz1
      have hzInt : z∈Ioo (0:Interval) 1 :=
        ⟨lt_of_le_of_ne z.property.1 (Ne.symm hz0),lt_of_le_of_ne z.property.2 hz1⟩
      exact (hbClear j z hzInt (by have hz' : (b j z).val=g w := hz; rw [hz']; exact hFront)).elim
    have hbvalg : range g⊆range (bv j) := hgb
    have he : g w=bv j 0 ∨ g w=bv j 1 := by
      rcases hzEnd with rfl | rfl
      · exact Or.inl hz.symm
      · exact Or.inr hz.symm
    have hwEnd := CurveComplex.HyperellipticModel.actual_embedded_side_source_endpoint
      (bv j) g (hbemb j) hg hbvalg w he
    rcases hwEnd with rfl | rfl
    · exact (lt_irrefl (0:Interval)) hw.1
    · exact (lt_irrefl (1:Interval)) hw.2
  have hqInternalClear : ∀ w∈Ioo (0:Interval) 1,q w∉frontier F := by
    intro w hw hFront
    obtain ⟨z,hz⟩ := hqa (mem_range_self w)
    have hzEnd : z=0 ∨ z=1 := by
      by_cases hz0 : z=0
      · exact Or.inl hz0
      by_cases hz1 : z=1
      · exact Or.inr hz1
      have hzInt : z∈Ioo (0:Interval) 1 :=
        ⟨lt_of_le_of_ne z.property.1 (Ne.symm hz0),lt_of_le_of_ne z.property.2 hz1⟩
      exact (haClear i z hzInt (by have hz' : (a i z).val=q w := hz; rw [hz']; exact hFront)).elim
    have he : q w=av i 0 ∨ q w=av i 1 := by
      rcases hzEnd with rfl | rfl
      · exact Or.inl hz.symm
      · exact Or.inr hz.symm
    have hwEnd := CurveComplex.HyperellipticModel.actual_embedded_side_source_endpoint
      (av i) q (IsEmbedding.subtypeVal.comp (ha i)) hq hqa w he
    rcases hwEnd with rfl | rfl
    · exact (lt_irrefl (0:Interval)) hw.1
    · exact (lt_irrefl (1:Interval)) hw.2
  have hdInteriorF : interior (range d)⊆interior F := interior_mono hdF
  have hdBoundary : frontier (range d)=range q∪range g :=
    (embedded_surface_disk_frontier_eq_boundary_image d hd).trans hboundary
  have hdClear : Disjoint (interior (range d)) ((⋃ k,range (av k))∪⋃ k,range (bv k)) := by
    rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd]
    exact hempty
  have hdFrontierCorners : range d∩frontier F⊆{q 0,q 1} := by
    rintro y ⟨hyD,hyF⟩
    have hyNotInterior : y∉interior (range d) := by
      intro hi
      exact ((mem_frontier_iff_notMem_interior (hdF hyD)).mp hyF) (hdInteriorF hi)
    have hdClosed : IsClosed (range d) := (isCompact_range d.continuous).isClosed
    have hyBoundary : y∈range q∪range g := by
      rw [←hdBoundary,hdClosed.frontier_eq]
      exact ⟨hyD,hyNotInterior⟩
    rcases hyBoundary with ⟨w,hw⟩ | ⟨w,hw⟩
    · by_cases hw0 : w=0
      · left;exact hw0 ▸ hw.symm
      by_cases hw1 : w=1
      · right;exact hw1 ▸ hw.symm
      exact (hqInternalClear w
        ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
        (hw ▸ hyF)).elim
    · by_cases hw0 : w=0
      · left;exact (hw0 ▸ hw.symm).trans hzero.symm
      by_cases hw1 : w=1
      · right;exact (hw1 ▸ hw.symm).trans hone.symm
      exact (hgInternalClear w
        ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
        (hw ▸ hyF)).elim
  have hdAtMostOneFrontier : ∀ x∈range d∩frontier F,∀ y∈range d∩frontier F,x=y := by
    intro x hx y hy
    have hxEnds := hdFrontierCorners hx
    have hyEnds := hdFrontierCorners hy
    rcases hgenuine with h0 | h1
    · have hx1 : x=q 1 := by
        rcases hxEnds with he | he
        · exact (h0 (he ▸ hx.2)).elim
        · exact Set.mem_singleton_iff.mp he
      have hy1 : y=q 1 := by
        rcases hyEnds with he | he
        · exact (h0 (he ▸ hy.2)).elim
        · exact Set.mem_singleton_iff.mp he
      exact hx1.trans hy1.symm
    · have hx0 : x=q 0 := by
        rcases hxEnds with he | he
        · exact he
        · exact (h1 ((Set.mem_singleton_iff.mp he) ▸ hx.2)).elim
      have hy0 : y=q 0 := by
        rcases hyEnds with he | he
        · exact he
        · exact (h1 ((Set.mem_singleton_iff.mp he) ▸ hy.2)).elim
      exact hx0.trans hy0.symm
  have hdOrdinary : q 0∉frontier F → q 1∉frontier F → range d⊆interior F := by
    intro h0 h1 y hyD
    by_contra hn
    have hyFront : y∈frontier F := (mem_frontier_iff_notMem_interior (hdF hyD)).mpr hn
    rcases hdFrontierCorners ⟨hyD,hyFront⟩ with he | he
    · exact h0 (he ▸ hyFront)
    · exact h1 ((Set.mem_singleton_iff.mp he) ▸ hyFront)
  have hgOrdinary : g 0∉frontier F → g 1∉frontier F → range g⊆interior F := by
    intro h0 h1 x hx
    obtain ⟨w,rfl⟩ := hx
    have hgF : g w∈F := by
      obtain ⟨z,hz⟩ := hgb (mem_range_self w)
      exact hz ▸ (b j z).property
    have hgNot : g w∉frontier F := by
      by_cases hw0 : w=0
      · simpa only [hw0] using h0
      by_cases hw1 : w=1
      · simpa only [hw1] using h1
      exact hgInternalClear w
        ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
    by_contra hn
    exact hgNot ((mem_frontier_iff_notMem_interior hgF).mpr hn)
  have hOrdinaryStrip : g 0∉frontier F → g 1∉frontier F →
      ∃ R : Interval×Icc (-1:ℝ) 1→S,IsEmbedding R ∧
        (∀ w,R (w,⟨0,by norm_num⟩)=g w) ∧ range R⊆interior F ∧
        ∀ k,k≠j → Disjoint (range R) (range (bv k)) := by
    intro h0 h1
    let Other : Set S := ⋃ k : {k:J // k≠j},range (bv k.val)
    have hOtherClosed : IsClosed Other := isClosed_iUnion_of_finite
      (fun k : {k:J // k≠j} => (isCompact_range (bv k.val).continuous).isClosed)
    let O : Set S := interior F∩Otherᶜ
    have hO : IsOpen O := isOpen_interior.inter hOtherClosed.isOpen_compl
    have hgO : range g⊆O := by
      intro x hx
      refine ⟨hgOrdinary h0 h1 hx,?_⟩
      intro hxO
      obtain ⟨k,hk⟩ := mem_iUnion.mp hxO
      exact Set.disjoint_left.mp (hbd j k.val (Ne.symm k.property)) (hgb hx) hk
    obtain ⟨R,hR,hcenter,hRO⟩ := source_whole_embedded_arc_strip g hg O hO hgO
    refine ⟨R,hR,hcenter,fun x hx => (hRO hx).1,?_⟩
    intro k hk
    apply Set.disjoint_left.mpr
    intro x hxR hxk
    exact (hRO hxR).2 (mem_iUnion.mpr ⟨⟨k,hk⟩,hxk⟩)
  have haemb : IsEmbedding (av i) := IsEmbedding.subtypeVal.comp (ha i)
  have hpQa : av i s∈Q.source := by
    change (a i s).val∈Q.source
    rw [hcontact]
    exact hpQ
  have hpair : Q.source∩(range (av i)∩range (bv j))={av i s} := by
    ext x
    constructor
    · rintro ⟨hxQ,hxA,hxB⟩
      have hxU : x∈U∩((⋃ k,range (av k))∩⋃ k,range (bv k)) :=
        ⟨hQU hxQ,mem_iUnion.mpr ⟨i,hxA⟩,mem_iUnion.mpr ⟨j,hxB⟩⟩
      rw [hiso] at hxU
      change x=av i s
      exact hxU.trans hs.symm
    · intro hx
      have he : x=av i s := hx
      subst x
      exact ⟨hpQa,mem_range_self s,⟨t,hcontact.symm⟩⟩
  obtain ⟨l,r,hls,hsr,hwin,hleft,hright⟩ :=
    ActualHarerContactSides.actual_isolated_whole_trace_contact_constructs_two_signed_branch_windows
      (av i) (bv j) haemb Q haxis s hsInterior hpQa hpair
  have hQF : Q.source⊆interior F := hQU.trans hUF
  have hFaxis : ∀ y:↥F,y.val∈Q.source → (y∈range (b j) ↔ Q y.val 1=0) := by
    intro y hy
    have hrange : y∈range (b j) ↔ y.val∈range (bv j) := by
      constructor
      · rintro ⟨w,rfl⟩;exact mem_range_self w
      · rintro ⟨w,hw⟩;exact ⟨w,Subtype.ext hw⟩
    exact hrange.trans (haxis y.val hy)
  have hFotherA : ∀ k,k≠i → ∀ y∈range (a k),y.val∉Q.source := by
    intro k hk y hy hyQ
    obtain ⟨w,rfl⟩ := hy
    exact Set.disjoint_left.mp (hUa k hk) (hQU hyQ) (mem_range_self w)
  have hFotherB : ∀ k,k≠j → ∀ y∈range (b k),y.val∉Q.source := by
    intro k hk y hy hyQ
    obtain ⟨w,rfl⟩ := hy
    exact Set.disjoint_left.mp (hOther k hk) hyQ (mem_range_self w)
  have haxisP : Q (av i s) 1=0 := (haxis (av i s) hpQa).mp ⟨t,hcontact.symm⟩
  obtain ⟨gStart,gEnd,hgEndsNe,hgStart,hgEnd,hgParamTrace⟩ :=
    actual_embedded_subarc_constructs_exact_unordered_parameter_interval
      (bv j) g (hbemb j) hg hgb
  have hMovingDiskParamTrace : range d∩range (bv j)=(bv j) '' uIcc gStart gEnd := by
    rw [←hgParamTrace]
    apply Set.Subset.antisymm
    · intro x hx
      exact hcleanB ▸ ⟨hx.1,mem_iUnion.mpr ⟨j,hx.2⟩⟩
    · intro x hx
      have hxAll : x∈range d∩(⋃ k,range (bv k)) := hcleanB.symm ▸ hx
      exact ⟨hxAll.1,hgb hx⟩
  have hSelectedMovingExterior : ∀ z:Interval,z∉uIcc gStart gEnd → bv j z∉range d := by
    intro z hz hxD
    have hx : bv j z∈(bv j) '' uIcc gStart gEnd :=
      hMovingDiskParamTrace ▸ ⟨hxD,mem_range_self z⟩
    obtain ⟨w,hw,he⟩ := hx
    exact hz ((hbemb j).injective he ▸ hw)
  have hIsolatedMovingGermWholeAnchorClear : ∀ z:Interval,z≠t →
      bv j z∈U → bv j z∉⋃ k,range (av k) := by
    intro z hzt hzU hzA
    have hx : bv j z∈U∩((⋃ k,range (av k))∩⋃ k,range (bv k)) :=
      ⟨hzU,hzA,mem_iUnion.mpr ⟨j,mem_range_self z⟩⟩
    rw [hiso] at hx
    have he : bv j z=bv j t := hx.trans ht.symm
    exact hzt ((hbemb j).injective he)
  have hMovingContactParameterEnd : t=gStart ∨ t=gEnd := by
    rcases hv with hv0 | hv1
    · left
      apply (hbemb j).injective
      have he : q v=g 0 := by rw [hv0];exact hzero
      exact ht.trans (he.trans hgStart.symm)
    · right
      apply (hbemb j).injective
      have he : q v=g 1 := by rw [hv1];exact hone
      exact ht.trans (he.trans hgEnd.symm)
  have hContactFreeExteriorCut : ∃ c:Interval,c∈Ioo (0:Interval) 1 ∧
      c∉uIcc gStart gEnd ∧ bv j c∈U ∧ bv j c∉⋃ k,range (av k) := by
    have htU : bv j t∈U := by
      have ht' : (b j t).val=q v := ht
      change (b j t).val∈U
      rw [ht']
      exact hpU
    have hn : (bv j) ⁻¹' U∈nhds t := (hU.preimage (bv j).continuous).mem_nhds htU
    obtain ⟨l₀,r₀,htr,hlocal⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨0,htInterior.1⟩ ⟨1,htInterior.2⟩).mp hn
    obtain ⟨lc,hlc,hclt⟩ := exists_between htr.1
    obtain ⟨rc,htrc,hcr⟩ := exists_between htr.2
    have hlU : bv j lc∈U := hlocal ⟨hlc,hclt.trans htr.2⟩
    have hrU : bv j rc∈U := hlocal ⟨htr.1.trans htrc,hcr⟩
    have hlInterior : lc∈Ioo (0:Interval) 1 :=
      ⟨(bot_le : (0:Interval)≤l₀).trans_lt hlc,hclt.trans htInterior.2⟩
    have hrInterior : rc∈Ioo (0:Interval) 1 :=
      ⟨htInterior.1.trans htrc,hcr.trans_le (le_top : r₀≤(1:Interval))⟩
    rcases lt_or_gt_of_ne hgEndsNe with hSE | hES
    · rcases hMovingContactParameterEnd with htS | htE
      · refine ⟨lc,hlInterior,?_,hlU,hIsolatedMovingGermWholeAnchorClear lc hclt.ne hlU⟩
        rw [uIcc,min_eq_left hSE.le,max_eq_right hSE.le]
        intro hc
        exact (hclt.trans_le (htS ▸ hc.1)).false
      · refine ⟨rc,hrInterior,?_,hrU,hIsolatedMovingGermWholeAnchorClear rc htrc.ne' hrU⟩
        rw [uIcc,min_eq_left hSE.le,max_eq_right hSE.le]
        intro hc
        exact (htrc.trans_le (htE ▸ hc.2)).false
    · rcases hMovingContactParameterEnd with htS | htE
      · refine ⟨rc,hrInterior,?_,hrU,hIsolatedMovingGermWholeAnchorClear rc htrc.ne' hrU⟩
        rw [uIcc,min_eq_right hES.le,max_eq_left hES.le]
        intro hc
        exact (htrc.trans_le (htS ▸ hc.2)).false
      · refine ⟨lc,hlInterior,?_,hlU,hIsolatedMovingGermWholeAnchorClear lc hclt.ne hlU⟩
        rw [uIcc,min_eq_right hES.le,max_eq_left hES.le]
        intro hc
        exact (hclt.trans_le (htE ▸ hc.1)).false
  have hOtherAonDisk : ∀ k,k≠i → Disjoint (range d) (range (av k)) := by
    intro k hk
    apply Set.disjoint_left.mpr
    intro x hxD hxk
    have hxQ : x∈range q := hcleanA ▸ ⟨hxD,mem_iUnion.mpr ⟨k,hxk⟩⟩
    exact Set.disjoint_left.mp (had i k (Ne.symm hk)) (hqa hxQ) hxk
  have hOtherBonDisk : ∀ k,k≠j → Disjoint (range d) (range (bv k)) := by
    intro k hk
    apply Set.disjoint_left.mpr
    intro x hxD hxk
    have hxG : x∈range g := hcleanB ▸ ⟨hxD,mem_iUnion.mpr ⟨k,hxk⟩⟩
    exact Set.disjoint_left.mp (hbd j k (Ne.symm hk)) (hgb hxG) hxk
  have hOrdinaryCleanDiskChart : q 0∉frontier F → q 1∉frontier F →
      ∃ E : OpenPartialHomeomorph S Plane,range d⊆E.source ∧
        E.source⊆interior F ∧
        (∀ k,k≠i → Disjoint E.source (range (av k))) ∧
        (∀ k,k≠j → Disjoint E.source (range (bv k))) := by
    intro h0 h1
    let AOther : Set S := ⋃ k : {k:I // k≠i},range (av k.val)
    let BOther : Set S := ⋃ k : {k:J // k≠j},range (bv k.val)
    have hAc : IsClosed AOther := isClosed_iUnion_of_finite
      (fun k : {k:I // k≠i} => (isCompact_range (av k.val).continuous).isClosed)
    have hBc : IsClosed BOther := isClosed_iUnion_of_finite
      (fun k : {k:J // k≠j} => (isCompact_range (bv k.val).continuous).isClosed)
    let O : Set S := interior F∩(AOther∪BOther)ᶜ
    have hO : IsOpen O := isOpen_interior.inter (hAc.union hBc).isOpen_compl
    have hDO : range d⊆O := by
      intro x hxD
      refine ⟨hdOrdinary h0 h1 hxD,?_⟩
      rintro (hxA | hxB)
      · obtain ⟨k,hk⟩ := mem_iUnion.mp hxA
        exact Set.disjoint_left.mp (hOtherAonDisk k.val k.property) hxD hk
      · obtain ⟨k,hk⟩ := mem_iUnion.mp hxB
        exact Set.disjoint_left.mp (hOtherBonDisk k.val k.property) hxD hk
    obtain ⟨_,e,he,hde,heO,_,_,_⟩ :=
      CurveComplex.LocalSurgery.exists_supported_strict_disk_enlargement d hd O hO hDO
    obtain ⟨E,hEs,_,_⟩ := embedded_disk_interior_chart e he
    have hEO : E.source⊆O := by
      rw [hEs]
      exact interior_subset.trans heO
    refine ⟨E,hEs.symm ▸ hde,fun x hx => (hEO hx).1,?_,?_⟩
    · intro k hk
      apply Set.disjoint_left.mpr
      intro x hx hxk
      exact (hEO hx).2 (Or.inl (mem_iUnion.mpr ⟨⟨k,hk⟩,hxk⟩))
    · intro k hk
      apply Set.disjoint_left.mpr
      intro x hx hxk
      exact (hEO hx).2 (Or.inr (mem_iUnion.mpr ⟨⟨k,hk⟩,hxk⟩))
  let lo := min gStart gEnd
  let hi := max gStart gEnd
  have hlohi : lo<hi := by
    rcases lt_or_gt_of_ne hgEndsNe with hlt | hgt
    · simpa only [lo,hi,min_eq_left hlt.le,max_eq_right hlt.le] using hlt
    · simpa only [lo,hi,min_eq_right hgt.le,max_eq_left hgt.le] using hgt
  have hCornerWindow : ∀ w:Interval,(w=0 ∨ w=1) → q w∉frontier F →
      ∃ (τ L R : Interval) (C : OpenPartialHomeomorph S Plane),
        bv j τ=q w ∧ 0<L ∧ L<τ ∧ τ<R ∧ R<1 ∧
        C.source⊆interior F ∧
        (∀ z∈Icc L R,bv j z∈C.source) ∧
        (∀ z∈Icc L R,z≠τ → bv j z∉⋃ k,range (av k)) := by
    intro w hw hwF
    obtain ⟨s₁,t₁,l₁,h₁,C,ε,hs₁,ht₁,has₁,hbt₁,hl₁,hh₁,
      hε,hpC,hCF,hCaxis,haC,hneg,hpos⟩ := hcross w hw hwF
    obtain ⟨V,hV,hpV,hVF,hVa,hVb,hViso⟩ :=
      ActualHarerWholeGraph.actual_finite_whole_graph_genuine_contact_constructs_isolated_clear_open_neighborhood
        av bv had hbd hfin F i j (q w) ⟨s₁,has₁⟩ ⟨t₁,hbt₁⟩
        (has₁ ▸ (a i s₁).property) hwF
    have hn : (bv j) ⁻¹' (V∩C.source)∈nhds t₁ :=
      ((hV.inter C.open_source).preimage (bv j).continuous).mem_nhds
        (by change (b j t₁).val∈V∩C.source; rw [hbt₁]; exact ⟨hpV,hpC⟩)
    obtain ⟨L₀,R₀,htLR,hsub⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨0,ht₁.1⟩ ⟨1,ht₁.2⟩).mp hn
    obtain ⟨L,hL₀,hLt⟩ := exists_between htLR.1
    obtain ⟨R,htR,hRR₀⟩ := exists_between htLR.2
    have hlocal : ∀ z∈Icc L R,bv j z∈V∩C.source := by
      intro z hz
      exact hsub ⟨hL₀.trans_le hz.1,hz.2.trans_lt hRR₀⟩
    refine ⟨t₁,L,R,C,hbt₁,(bot_le : (0:Interval)≤L₀).trans_lt hL₀,
      hLt,htR,hRR₀.trans_le (le_top : R₀≤(1:Interval)),hCF,
      fun z hz => (hlocal z hz).2,?_⟩
    intro z hz hzt hzA
    have hcontact' : bv j z∈V∩((⋃ k,range (av k))∩⋃ k,range (bv k)) :=
      ⟨(hlocal z hz).1,hzA,mem_iUnion.mpr ⟨j,mem_range_self z⟩⟩
    rw [hViso] at hcontact'
    exact hzt ((hbemb j).injective (hcontact'.trans hbt₁.symm))
  have hEnds : ∀ τ:Interval,τ=lo ∨ τ=hi →
      ∃ w:Interval,(w=0 ∨ w=1) ∧ bv j τ=q w := by
    intro τ hτ
    have he : τ=gStart ∨ τ=gEnd := by
      rcases hτ with hτ | hτ
      · rcases le_total gStart gEnd with h | h
        · exact Or.inl (hτ.trans (min_eq_left h))
        · exact Or.inr (hτ.trans (min_eq_right h))
      · rcases le_total gStart gEnd with h | h
        · exact Or.inr (hτ.trans (max_eq_right h))
        · exact Or.inl (hτ.trans (max_eq_left h))
    rcases he with rfl | rfl
    · exact ⟨0,Or.inl rfl,hgStart.trans hzero.symm⟩
    · exact ⟨1,Or.inr rfl,hgEnd.trans hone.symm⟩
  obtain ⟨α,hαlo,hαstrict,hαFront,hLeftClear,hLeftInterior⟩ :
      ∃ α:Interval,α≤lo ∧ (0<lo → α<lo) ∧ (lo=0 → α=lo) ∧
        (∀ z∈Ico α lo,bv j z∉⋃ k,range (av k)) ∧
        (∀ z∈Icc α lo,lo≠0 → bv j z∈interior F) := by
    by_cases hlo0 : lo=0
    · refine ⟨lo,le_rfl,fun h => (h.ne hlo0.symm).elim,fun _ => rfl,?_,?_⟩
      · intro z hz; exact (not_lt_of_ge hz.1 hz.2).elim
      · intro z hz hne; exact (hne hlo0).elim
    · have hloInt : lo∈Ioo (0:Interval) 1 :=
        ⟨bot_lt_iff_ne_bot.mpr hlo0,hlohi.trans_le (le_top : hi≤(1:Interval))⟩
      obtain ⟨w,hw,hτw⟩ := hEnds lo (Or.inl rfl)
      have hwF : q w∉frontier F := hτw ▸ hbClear j lo hloInt
      obtain ⟨τ,L,R,C,hτ,hL0,hLt,htR,hR1,hCF,hwin,hclear⟩ := hCornerWindow w hw hwF
      have he : τ=lo := (hbemb j).injective (hτ.trans hτw.symm)
      subst τ
      refine ⟨L,hLt.le,fun _ => hLt,fun he => (hlo0 he).elim,?_,?_⟩
      · intro z hz
        exact hclear z ⟨hz.1,hz.2.le.trans htR.le⟩ hz.2.ne
      · intro z hz _
        exact hCF (hwin z ⟨hz.1,hz.2.trans htR.le⟩)
  obtain ⟨β,hhiβ,hβstrict,hβFront,hRightClear,hRightInterior⟩ :
      ∃ β:Interval,hi≤β ∧ (hi<1 → hi<β) ∧ (hi=1 → β=hi) ∧
        (∀ z∈Ioc hi β,bv j z∉⋃ k,range (av k)) ∧
        (∀ z∈Icc hi β,hi≠1 → bv j z∈interior F) := by
    by_cases hhi1 : hi=1
    · refine ⟨hi,le_rfl,fun h => (h.ne hhi1).elim,fun _ => rfl,?_,?_⟩
      · intro z hz; exact (not_lt_of_ge hz.2 hz.1).elim
      · intro z hz hne; exact (hne hhi1).elim
    · have hhiInt : hi∈Ioo (0:Interval) 1 :=
        ⟨(bot_le : (0:Interval)≤lo).trans_lt hlohi,lt_top_iff_ne_top.mpr hhi1⟩
      obtain ⟨w,hw,hτw⟩ := hEnds hi (Or.inr rfl)
      have hwF : q w∉frontier F := hτw ▸ hbClear j hi hhiInt
      obtain ⟨τ,L,R,C,hτ,hL0,hLt,htR,hR1,hCF,hwin,hclear⟩ := hCornerWindow w hw hwF
      have he : τ=hi := (hbemb j).injective (hτ.trans hτw.symm)
      subst τ
      refine ⟨R,htR.le,fun _ => htR,fun he => (hhi1 he).elim,?_,?_⟩
      · intro z hz
        exact hclear z ⟨hLt.le.trans hz.1.le,hz.2⟩ hz.1.ne'
      · intro z hz _
        exact hCF (hwin z ⟨hLt.le.trans hz.1,hz.2⟩)
  have hαβ : α<β := hαlo.trans_lt (hlohi.trans_le hhiβ)
  obtain ⟨old,hOld,hOld0,hOld1,hOldRange⟩ :=
    actual_selected_arc_interval_constructs_embedded_literal_old_subarc (bv j) (hbemb j) α β hαβ
  have hgOld : range g⊆range old := by
    rw [hgParamTrace,hOldRange,uIcc]
    apply image_mono
    intro w hw
    exact ⟨hαlo.trans hw.1,hw.2.trans hhiβ⟩
  have hOldF : range old⊆F := by
    rintro x ⟨w,rfl⟩
    have hxR : old w∈(bv j) '' Icc α β := hOldRange ▸ mem_range_self w
    obtain ⟨z,_,hz⟩ := hxR
    exact hz ▸ (b j z).property
  have hOldFrontier : range old∩frontier F⊆({old 0,old 1}:Set S) := by
    rintro x ⟨hxOld,hxFront⟩
    obtain ⟨z,hz,hzx⟩ := hOldRange ▸ hxOld
    have hzFront : (b j z).val∈frontier F := by
      change bv j z∈frontier F
      exact hzx ▸ hxFront
    by_cases hz0 : z=0
    · have hα0 : α=0 := le_antisymm (hz0 ▸ hz.1) (bot_le : (0:Interval)≤α)
      left
      calc x = bv j z := hzx.symm
           _ = bv j α := congrArg (bv j) (hz0.trans hα0.symm)
           _ = old 0 := hOld0.symm
    by_cases hz1 : z=1
    · have hβ1 : β=1 := le_antisymm (le_top : β≤(1:Interval)) (hz1 ▸ hz.2)
      right
      apply mem_singleton_iff.mpr
      calc x = bv j z := hzx.symm
           _ = bv j β := congrArg (bv j) (hz1.trans hβ1.symm)
           _ = old 1 := hOld1.symm
    exact (hbClear j z ⟨bot_lt_iff_ne_bot.mpr hz0,lt_top_iff_ne_top.mpr hz1⟩ hzFront).elim
  have hDiskFrontierOldEnds : range d∩frontier F⊆({old 0,old 1}:Set S) := by
    rintro x ⟨hxD,hxFront⟩
    have hxG : x∈range g := by
      rcases hdFrontierCorners ⟨hxD,hxFront⟩ with hx0 | hx1
      · exact ⟨0,hzero.symm.trans hx0.symm⟩
      · exact ⟨1,hone.symm.trans (mem_singleton_iff.mp hx1).symm⟩
    exact hOldFrontier ⟨hgOld hxG,hxFront⟩
  have hOldOtherLabels : ∀ k,k≠j → Disjoint (range old) (range (bv k)) := by
    intro k hk
    apply (hbd j k (Ne.symm hk)).mono_left
    rw [hOldRange]
    exact image_subset_range _ _
  have hGenuineOldInterior : q v∈range old\{old 0,old 1} := by
    have hvG : q v∈range g := ⟨v,hqg.symm⟩
    have htCore : t∈uIcc gStart gEnd := by
      have hqtG : bv j t∈range g := by have ht' : (b j t).val=q v := ht; change (b j t).val∈range g; rw [ht']; exact hvG
      rw [hgParamTrace] at hqtG
      obtain ⟨z,hz,he⟩ := hqtG
      exact (hbemb j).injective he ▸ hz
    have hαt : α<t := by
      have hloT : lo≤t := htCore.1
      by_cases hlt : lo<t
      · exact hαlo.trans_lt hlt
      · have he : lo=t := le_antisymm hloT (le_of_not_gt hlt)
        exact he ▸ hαstrict (he.symm ▸ htInterior.1)
    have htβ : t<β := by
      have htHi : t≤hi := htCore.2
      by_cases hlt : t<hi
      · exact hlt.trans_le hhiβ
      · have he : t=hi := le_antisymm htHi (le_of_not_gt hlt)
        exact he.symm ▸ hβstrict (he ▸ htInterior.2)
    refine ⟨hgOld hvG,?_⟩
    intro he
    rcases he with he | he
    · have hαtEq : α=t := (hbemb j).injective (hOld0.symm.trans (he.symm.trans ht.symm))
      exact hαt.ne hαtEq
    · have hβtEq : β=t := (hbemb j).injective (hOld1.symm.trans ((mem_singleton_iff.mp he).symm.trans ht.symm))
      exact htβ.ne hβtEq.symm
  have hSides : range q∩range g=({q 0,q 1}:Set S) :=
    actual_disk_boundary_sides_intersection q g hq hg hzero hone d hd hboundary
  have hOldExtraClear : Disjoint (range old\range g) (⋃ k,range (av k)) := by
    apply disjoint_left.mpr
    rintro x ⟨hxOld,hxg⟩ hxA
    obtain ⟨z,hz,rfl⟩ := hOldRange ▸ hxOld
    have hzCore : z∉Icc lo hi := by
      intro hzC
      apply hxg
      rw [hgParamTrace]
      exact ⟨z,hzC,rfl⟩
    by_cases hzlo : z<lo
    · exact hLeftClear z ⟨hz.1,hzlo⟩ hxA
    · have hhiz : hi<z := by
        by_contra hn
        exact hzCore ⟨le_of_not_gt hzlo,le_of_not_gt hn⟩
      exact hRightClear z ⟨hhiz,hz.2⟩ hxA
  have hOldAnchorTrace : range old∩(⋃ k,range (av k))=({q 0,q 1}:Set S) := by
    apply Subset.antisymm
    · rintro x ⟨hxOld,hxA⟩
      have hxg : x∈range g := by
        by_contra hn
        exact disjoint_left.mp hOldExtraClear ⟨hxOld,hn⟩ hxA
      have hxD : x∈range d := by
        apply image_subset_range d _
        rw [hboundary]
        exact Or.inr hxg
      have hxq : x∈range q := hcleanA ▸ ⟨hxD,hxA⟩
      exact hSides ▸ ⟨hxq,hxg⟩
    · intro x hx
      have hxSides : x∈range q∩range g := hSides.symm ▸ hx
      exact ⟨hgOld hxSides.2,mem_iUnion.mpr ⟨i,hqa hxSides.1⟩⟩
  have hLeftTailDisk : (bv j '' Icc α lo)∩range d=({bv j lo}:Set S) := by
    apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hzD⟩
      have hzCore : z∈Icc lo hi := by
        by_contra hn
        exact hSelectedMovingExterior z hn hzD
      exact mem_singleton_iff.mpr (congrArg (bv j) (le_antisymm hz.2 hzCore.1))
    · intro x hx
      have he : x=bv j lo := hx
      subst x
      refine ⟨⟨lo,⟨hαlo,le_rfl⟩,rfl⟩,?_⟩
      have hxg : bv j lo∈range g := by rw [hgParamTrace];exact ⟨lo,⟨le_rfl,hlohi.le⟩,rfl⟩
      exact (show bv j lo∈range d∩(⋃ k,range (bv k)) from hcleanB.symm ▸ hxg).1
  have hRightTailDisk : (bv j '' Icc hi β)∩range d=({bv j hi}:Set S) := by
    apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hzD⟩
      have hzCore : z∈Icc lo hi := by
        by_contra hn
        exact hSelectedMovingExterior z hn hzD
      exact mem_singleton_iff.mpr (congrArg (bv j) (le_antisymm hzCore.2 hz.1))
    · intro x hx
      have he : x=bv j hi := hx
      subst x
      refine ⟨⟨hi,⟨le_rfl,hhiβ⟩,rfl⟩,?_⟩
      have hxg : bv j hi∈range g := by rw [hgParamTrace];exact ⟨hi,⟨hlohi.le,le_rfl⟩,rfl⟩
      exact (show bv j hi∈range d∩(⋃ k,range (bv k)) from hcleanB.symm ▸ hxg).1
  have hTailDisjoint : Disjoint (bv j '' Icc α lo) (bv j '' Icc hi β) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,he⟩ ⟨w,hw,hwe⟩
    have hzw : z=w := (hbemb j).injective (he.trans hwe.symm)
    have hhilo : hi≤lo := hw.1.trans (hzw ▸ hz.2)
    exact (not_le_of_gt hlohi) hhilo
  have hOldDiskTrace : range old∩range d=range g := by
    apply Subset.antisymm
    · rintro x ⟨hxOld,hxD⟩
      obtain ⟨z,_,hz⟩ := hOldRange ▸ hxOld
      exact hcleanB ▸ ⟨hxD,mem_iUnion.mpr ⟨j,⟨z,hz⟩⟩⟩
    · intro x hxg
      exact ⟨hgOld hxg,(show x∈range d∩(⋃ k,range (bv k)) from hcleanB.symm ▸ hxg).1⟩
  obtain ⟨qStart,qEnd,hqEndsNe,hqStart,hqEnd,hqParamTrace⟩ :=
    actual_embedded_subarc_constructs_exact_unordered_parameter_interval
      (av i) q haemb hq hqa
  let qlo := min qStart qEnd
  let qhi := max qStart qEnd
  have hqlohi : qlo<qhi := by
    rcases lt_or_gt_of_ne hqEndsNe with h | h
    · simpa only [qlo,qhi,min_eq_left h.le,max_eq_right h.le] using h
    · simpa only [qlo,qhi,min_eq_right h.le,max_eq_left h.le] using h
  let Urail : Set S := interior F∩(⋃ k,range (bv k))ᶜ
  have hUrail : IsOpen Urail := isOpen_interior.inter
    (isClosed_iUnion_of_finite (fun k => (isCompact_range (bv k).continuous).isClosed)).isOpen_compl
  have hqCore : ∀ z∈Ioo qlo qhi,av i z∈frontier (range d)∩Urail := by
    intro z hz
    have hxq : av i z∈range q := by rw [hqParamTrace];exact ⟨z,⟨hz.1.le,hz.2.le⟩,rfl⟩
    have hxFront : av i z∈frontier (range d) := hdBoundary.symm ▸ Or.inl hxq
    have hzInt : z∈Ioo (0:Interval) 1 :=
      ⟨(bot_le : (0:Interval)≤qlo).trans_lt hz.1,hz.2.trans_le (le_top : qhi≤(1:Interval))⟩
    have hxF : av i z∈interior F := by
      by_contra hn
      exact haClear i z hzInt
        ((mem_frontier_iff_notMem_interior (a i z).property).mpr hn)
    refine ⟨hxFront,hxF,?_⟩
    intro hxB
    have hxD : av i z∈range d := (isCompact_range d.continuous).isClosed.frontier_subset hxFront
    have hxg : av i z∈range g := hcleanB ▸ ⟨hxD,hxB⟩
    have hxEnds : av i z∈({q 0,q 1}:Set S) := hSides ▸ ⟨hxq,hxg⟩
    have hze : z=qStart ∨ z=qEnd := by
      rcases hxEnds with he | he
      · exact Or.inl (haemb.injective (he.trans hqStart.symm))
      · exact Or.inr (haemb.injective (he.trans hqEnd.symm))
    rcases hze with he | he
    · subst z
      rcases le_total qStart qEnd with h | h
      · have hh : qlo=qStart := min_eq_left h
        exact (hh ▸ hz.1).false
      · have hh : qhi=qStart := max_eq_left h
        exact (hh ▸ hz.2).false
    · subst z
      rcases le_total qStart qEnd with h | h
      · have hh : qhi=qEnd := max_eq_right h
        exact (hh ▸ hz.2).false
      · have hh : qlo=qEnd := min_eq_right h
        exact (hh ▸ hz.1).false
  obtain ⟨AnchorStrip,hAnchorStrip,hAnchorCenter,hAnchorOther,hAnchorClear⟩ :=
    ActualHarerWholeAnchorRail.disjoint_compact_anchor_family_constructs_whole_anchor_clear_strip
      av (fun k => IsEmbedding.subtypeVal.comp (ha k)) had i
  have hUrailG : Disjoint Urail (range g) := by
    apply disjoint_left.mpr
    intro x hx hxg
    exact hx.2 (mem_iUnion.mpr ⟨j,hgb hxg⟩)
  have hExteriorCompact : ∀ c e:Interval,qlo<c → c<e → e<qhi →
      ∃ H:C(Interval×Interval,S),IsEmbedding H ∧ range H⊆Urail ∧
        (∀ t w:Interval,0<w → H (t,w)∉range d ∧ H (t,w)∉⋃ k,range (av k)) ∧
        range H∩range d=av i '' Icc c e := by
    intro c e hqc hce heq
    obtain ⟨L,hqL,hLc⟩ := exists_between hqc
    obtain ⟨R,heR,hRq⟩ := exists_between heq
    have hL0 : (0:Interval)<L := (bot_le : (0:Interval)≤qlo).trans_lt hqL
    have hR1 : R<(1:Interval) := hRq.trans_le (le_top : qhi≤(1:Interval))
    obtain ⟨H,hH,hHU,hHcenter,hHout,hHD⟩ :=
      ActualHarerComparisonGeometry.compact_exterior_half_strip
        AnchorStrip hAnchorStrip (av i) hAnchorCenter (range d)
        (⋃ k,range (av k)) (range g) Urail
        (isCompact_range d.continuous).isClosed
        (by rw [actual_embedded_disk_closure_interior d hd])
        (by intro x hx;rw [hdBoundary] at hx;exact hx.elim (fun h => Or.inl (hqa h)) Or.inr)
        hAnchorClear hUrail hUrailG L R c e hL0 hLc hce heR hR1
        (fun z hz => hqCore z ⟨hqL.trans_le hz.1,hz.2.trans_lt hRq⟩)
    exact ⟨H,hH,hHU,hHout,hHD⟩
  let qLift : C(Interval,range (av i)) :=
    ⟨fun t => ⟨q t,hqa (mem_range_self t)⟩,q.continuous.subtype_mk _⟩
  let qClock : C(Interval,Interval) :=
    ⟨haemb.toHomeomorph.symm ∘ qLift,haemb.toHomeomorph.symm.continuous.comp qLift.continuous⟩
  have hqClock (t : Interval) : av i (qClock t)=q t :=
    congrArg Subtype.val (haemb.toHomeomorph.apply_symm_apply (qLift t))
  have hqClockInj : Function.Injective qClock := by
    intro t u he
    exact hq.injective ((hqClock t).symm.trans ((congrArg (av i) he).trans (hqClock u)))
  have hqClock0 : qClock 0=qStart := haemb.injective ((hqClock 0).trans hqStart.symm)
  have hqClock1 : qClock 1=qEnd := haemb.injective ((hqClock 1).trans hqEnd.symm)
  let endAt : Bool → Interval := fun k => if k then 1 else 0
  have hendAt (k : Bool) : endAt k=0 ∨ endAt k=1 := by cases k <;> simp [endAt]
  have hendAtInj : Function.Injective endAt := by
    intro k l he
    cases k <;> cases l
    · rfl
    · exact (zero_ne_one (show (0:Interval)=1 from he)).elim
    · exact (one_ne_zero (show (1:Interval)=0 from he)).elim
    · rfl
  let K := {k : Bool // q (endAt k)∉frontier F}
  letI : Fintype K := Fintype.ofFinite K
  let θ : K → Interval := fun k => qClock (endAt k.val)
  have hθ : Function.Injective θ := by
    intro k l he
    exact Subtype.ext (hendAtInj (hqClockInj he))
  have hθcenter (k : K) : av i (θ k)=q (endAt k.val) := hqClock _
  have hθint (k : K) : 0<(θ k:ℝ) ∧ (θ k:ℝ)<1 := by
    have h0 : θ k≠0 := by
      intro he
      exact k.property ((hθcenter k) ▸ he ▸ ha0 i)
    have h1 : θ k≠1 := by
      intro he
      exact k.property ((hθcenter k) ▸ he ▸ ha1 i)
    exact ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩
  have hcornerAxes (k : K) : ∃ (l h : Interval) (E : OpenPartialHomeomorph S Plane),
      ActualHarerCornerGeometry.OrderedWholePairAxes (av i) (bv j)
        (θ k) (ActualHarerCornerGeometry.endpointParameter (endAt k.val) gStart gEnd) l h E ∧
      E.source⊆interior F ∧
      (∀ m,m≠i → Disjoint E.source (range (av m))) ∧
      (∀ m,m≠j → Disjoint E.source (range (bv m))) := by
    let v := endAt k.val
    obtain ⟨s,t,l,h,Q,ε,hs,ht,has,hbt,hls,hsh,hε,hpQ,hQF,haxis,hwin,hbefore,hafter⟩ :=
      hcross v (hendAt k.val) k.property
    change av i s=q v at has
    change bv j t=q v at hbt
    have hsθ : s=θ k := haemb.injective (has.trans (hθcenter k).symm)
    have htEnd : t=ActualHarerCornerGeometry.endpointParameter v gStart gEnd := by
      apply (hbemb j).injective
      rcases hendAt k.val with hv | hv
      · have hv0 : v=0 := hv
        rw [hv0] at hbt ⊢
        simpa [ActualHarerCornerGeometry.endpointParameter] using hbt.trans (hzero.trans hgStart.symm)
      · have hv1 : v=1 := hv
        rw [hv1] at hbt ⊢
        simpa [ActualHarerCornerGeometry.endpointParameter] using hbt.trans (hone.trans hgEnd.symm)
    obtain ⟨U,hU,hpU,hUF,hUA,hUB,hiso⟩ :=
      ActualHarerWholeGraph.actual_finite_whole_graph_genuine_contact_constructs_isolated_clear_open_neighborhood
        av bv had hbd hfin F i j (q v) ⟨s,has⟩ ⟨t,hbt⟩
        (has ▸ (a i s).property) k.property
    have hmAxis : ∀ x∈Q.source,x∈range (bv j) ↔ Q x 1=0 := by
      intro x hx
      let y : F := ⟨x,interior_subset (hQF hx)⟩
      have hh := haxis y hx
      constructor
      · rintro ⟨u,hu⟩
        exact hh.mp ⟨u,Subtype.ext hu⟩
      · intro hz
        obtain ⟨u,hu⟩ := hh.mpr hz
        exact ⟨u,congrArg Subtype.val hu⟩
    obtain ⟨E,hEsub,hE⟩ :=
      ActualHarerCornerGeometry.actual_opposite_signed_arc_germs_construct_whole_pair_axis_chart
        S (av i) (bv j) haemb (hbemb j) s t l h Q ε U hs ht
        (has.trans hbt.symm) hls hsh hε (by change av i s∈Q.source; rw [has]; exact hpQ) hU
        (by change av i s∈U; rw [has]; exact hpU)
        hmAxis hwin hbefore hafter
    refine ⟨l,h,E,?_,fun x hx => hQF (hEsub hx).1,?_,?_⟩
    · simpa only [hsθ,htEnd,v] using hE
    · intro m hm
      exact (hUA m hm).mono_left (fun x hx => (hEsub hx).2)
    · intro m hm
      exact (hUB m hm).mono_left (fun x hx => (hEsub hx).2)
  choose cornerL cornerR cornerE hcornerE hcornerF hcornerOtherA hcornerOtherB using hcornerAxes
  have hθend (k : K) : θ k=ActualHarerCornerGeometry.endpointParameter (endAt k.val) qStart qEnd := by
    cases hk : k.val <;> simp [θ,endAt,hk,ActualHarerCornerGeometry.endpointParameter,hqClock0,hqClock1]
  have hcornerQuadrant (k : K) : ∃ r : ℝ,0<r ∧ r≤1 ∧
      Plane.closedSquare 0 r⊆(cornerE k).target ∧
      ∀ z : Plane,|z 0|<r → |z 1|<r →
        ((cornerE k).symm z∈range q ↔ z 1=0 ∧
          0≤ActualHarerCornerGeometry.inwardParameterSign (endAt k.val) qStart qEnd*z 0) ∧
        ((cornerE k).symm z∈range g ↔ z 0=0 ∧
          0≤ActualHarerCornerGeometry.inwardParameterSign (endAt k.val) gStart gEnd*z 1) ∧
        ((cornerE k).symm z∈range d ↔
          0≤ActualHarerCornerGeometry.inwardParameterSign (endAt k.val) qStart qEnd*z 0 ∧
          0≤ActualHarerCornerGeometry.inwardParameterSign (endAt k.val) gStart gEnd*z 1) := by
    obtain ⟨r,hr,hr1,hrE,hz⟩ :=
      ActualHarerCornerGeometry.actual_clean_corner_axis_chart_constructs_signed_disk_quadrant
        S F I J a b ha hb hadisjoint hbdisjoint hfinite ha0 ha1 hb0 hb1 haClear hbClear
        i j q g hq hg hqa hgb hzero hone d hd hboundary hdF hempty hgenuine hcleanA hcleanB hcross
        (endAt k.val) (hendAt k.val) k.property qStart qEnd gStart gEnd hqStart hqEnd hgStart hgEnd
        (cornerL k) (cornerR k) (cornerE k) (hθend k ▸ hcornerE k)
        (hcornerF k) (hcornerOtherA k) (hcornerOtherB k)
    exact ⟨r,hr,hr1,hrE,fun z hx hy => ⟨(hz z hx hy).1,(hz z hx hy).2.1,(hz z hx hy).2.2.1⟩⟩
  choose cornerRad hcornerRad hcornerRadOne hcornerSquare hcornerBank using hcornerQuadrant
  let anchorOpen : Set S := (⋃ k : {k : I // k≠i},range (av k.val))ᶜ
  have hanchorOpen : IsOpen anchorOpen := (isClosed_iUnion_of_finite
    (fun k : {k : I // k≠i} => (isCompact_range (av k.val).continuous).isClosed)).isOpen_compl
  have hanchorRange : range (av i)⊆anchorOpen := by
    intro x hx hn
    obtain ⟨k,hk⟩ := mem_iUnion.mp hn
    exact disjoint_left.mp (had i k.val k.property.symm) hx hk
  obtain ⟨N,hN,hNopen,hNcenter,σ,δ,η,hσ,hδη,hNframe⟩ :=
    source_finite_interior_axis_framed_arc_strip S (av i) haemb K θ hθ hθint cornerE
      (fun k => (hcornerE k).center_mem) (fun k => (hcornerE k).center_zero)
      (fun k u hu => ((hcornerE k).anchor_axis _ hu).mp (mem_range_self u))
      anchorOpen hanchorOpen hanchorRange
  let Nc : C(Interval×Icc (-1:ℝ) 1,S) := ⟨N,hN.continuous⟩
  have hNclear (t : Interval) (w : Icc (-1:ℝ) 1) (hw : (w:ℝ)≠0) :
      N (t,w)∉⋃ k,range (av k) := by
    intro hx
    obtain ⟨k,u,hu⟩ := mem_iUnion.mp hx
    by_cases hk : k=i
    · subst k
      exact hw (congrArg (fun z : Interval×Icc (-1:ℝ) 1 => (z.2:ℝ))
        (hN.injective (hu.symm.trans (hNcenter u).symm)))
    · exact hNopen (mem_range_self (t,w)) (mem_iUnion.mpr ⟨⟨k,hk⟩,⟨u,hu⟩⟩)
  have hcornerSmall (k : K) : ∃ T : Set S,IsOpen T ∧ av i (θ k)∈T ∧
      T⊆(cornerE k).source ∧
      (∀ x∈T,|(cornerE k) x 0|<cornerRad k ∧ |(cornerE k) x 1|<cornerRad k) ∧
      ∀ z,N z∈T → |(z.1:ℝ)-(θ k:ℝ)|<η k := by
    let Z := Interval×Icc (-1:ℝ) 1
    let Far : Set Z := {z | η k≤|(z.1:ℝ)-(θ k:ℝ)|}
    have hc : Continuous (fun z:Interval×Icc (-1:ℝ) 1 => |(z.1:ℝ)-(θ k:ℝ)|) := by fun_prop
    have hFar : IsClosed Far := isClosed_le continuous_const hc
    have hpFar : av i (θ k)∉N '' Far := by
      rintro ⟨z,hz,he⟩
      have hz0 := hN.injective (he.trans (hNcenter (θ k)).symm)
      have hn : η k≤0 := by
        change η k≤|(z.1:ℝ)-(θ k:ℝ)| at hz
        rw [hz0] at hz
        simpa using hz
      exact (not_le_of_gt (hδη k).2) hn
    let V : Set Plane := {z | |z 0|<cornerRad k ∧ |z 1|<cornerRad k}
    have hV : IsOpen V :=
      (isOpen_lt (show Continuous (fun z:Plane => |z 0|) by fun_prop) continuous_const).inter
        (isOpen_lt (show Continuous (fun z:Plane => |z 1|) by fun_prop) continuous_const)
    let T : Set S := ((cornerE k).source ∩ (cornerE k) ⁻¹' V) \ N '' Far
    have hT : IsOpen T := ((cornerE k).isOpen_inter_preimage hV).sdiff
      (hFar.isCompact.image hN.continuous).isClosed
    have hpT : av i (θ k)∈T := by
      refine ⟨⟨(hcornerE k).center_mem,?_⟩,hpFar⟩
      change |cornerE k (av i (θ k)) 0|<cornerRad k ∧ |cornerE k (av i (θ k)) 1|<cornerRad k
      rw [(hcornerE k).center_zero]
      simpa using And.intro (hcornerRad k) (hcornerRad k)
    refine ⟨T,hT,hpT,fun x hx => hx.1.1,fun x hx => hx.1.2,?_⟩
    intro z hz
    by_contra hn
    exact hz.2 ⟨z,le_of_not_gt hn,rfl⟩
  choose cornerT hcornerT hcornerTp hcornerTE hcornerTcoords hcornerTnear using hcornerSmall
  let movingBad : Set S := (⋃ k,range (bv k))∩(⋃ k:K,cornerT k)ᶜ
  have hmovingBad : IsClosed movingBad :=
    (isClosed_iUnion_of_finite (fun k => (isCompact_range (bv k).continuous).isClosed)).inter
      (isOpen_iUnion hcornerT).isClosed_compl
  let collarOpen : Set S := interior F∩movingBadᶜ
  have hcollarOpen : IsOpen collarOpen := isOpen_interior.inter hmovingBad.isOpen_compl
  have hqInF (t : Interval) : q t∈F := by
    obtain ⟨u,hu⟩ := hqa (mem_range_self t)
    exact hu ▸ (a i u).property
  have hqMovingEnds (t : Interval) (ht : q t∈⋃ k,range (bv k)) : t=0 ∨ t=1 := by
    have hqtD : q t∈range d := by
      apply image_subset_range d _
      rw [hboundary]
      exact Or.inl (mem_range_self t)
    have hqtG : q t∈range g := hcleanB ▸ ⟨hqtD,ht⟩
    have he := hSides ▸ (show q t∈range q∩range g from ⟨mem_range_self t,hqtG⟩)
    rcases he with he|he
    · exact Or.inl (hq.injective he)
    · exact Or.inr (hq.injective (mem_singleton_iff.mp he))
  have hqCollarOpen (t : Interval) (ht : q t∉frontier F) : q t∈collarOpen := by
    refine ⟨?_,?_⟩
    · exact by_contra (fun hn => ht ((mem_frontier_iff_notMem_interior (hqInF t)).mpr hn))
    · rintro ⟨htB,htNo⟩
      rcases hqMovingEnds t htB with h0|h1
      · let k : K := ⟨false,by simpa [endAt,←h0] using ht⟩
        apply htNo
        apply mem_iUnion.mpr
        refine ⟨k,?_⟩
        have he : av i (θ k)=q t := by simpa [k,endAt,h0] using hθcenter k
        exact he ▸ hcornerTp k
      · let k : K := ⟨true,by simpa [endAt,←h1] using ht⟩
        apply htNo
        apply mem_iUnion.mpr
        refine ⟨k,?_⟩
        have he : av i (θ k)=q t := by simpa [k,endAt,h1] using hθcenter k
        exact he ▸ hcornerTp k
  let Z := Interval×Icc (-1:ℝ) 1
  let zz : Icc (-1:ℝ) 1 := ⟨0,by norm_num⟩
  let topWidth : Icc (-1:ℝ) 1 := ⟨1,by norm_num⟩
  let goodDomain : Set Z := N ⁻¹' collarOpen ∩
    ⋂ k:K,({z:Z | z.1≠θ k} ∪ N ⁻¹' cornerT k)
  have hgoodDomain : IsOpen goodDomain := (hcollarOpen.preimage hN.continuous).inter
    (isOpen_iInter_of_finite (fun k =>
      (isClosed_eq continuous_fst continuous_const).isOpen_compl.union
        ((hcornerT k).preimage hN.continuous)))
  have hbaseGood (t : Interval) (ht : q t∉frontier F) : (qClock t,zz)∈goodDomain := by
    refine ⟨?_,mem_iInter.mpr ?_⟩
    · change N (qClock t,zz)∈collarOpen
      rw [hNcenter,hqClock]
      exact hqCollarOpen t ht
    · intro k
      by_cases he : qClock t=θ k
      · right
        change N (qClock t,zz)∈cornerT k
        rw [he,hNcenter]
        exact hcornerTp k
      · exact Or.inl he
  let badDomain : Set Z := goodDomainᶜ∪{z:Z | z.2=topWidth}
  have hbadDomain : IsClosed badDomain := hgoodDomain.isClosed_compl.union
    (isClosed_eq continuous_snd continuous_const)
  have hbadNonempty : badDomain.Nonempty := ⟨(0,topWidth),Or.inr rfl⟩
  let width : C(Interval,ℝ) := ⟨fun t => min (1/2) (Metric.infDist (qClock t,zz) badDomain/2),
    continuous_const.min (((Metric.continuous_infDist_pt badDomain).comp
      (qClock.continuous.prodMk continuous_const)).div_const 2)⟩
  have hwidthNonneg (t : Interval) : 0≤width t :=
    le_min (by norm_num) (div_nonneg Metric.infDist_nonneg (by norm_num))
  have hwidthHalf (t : Interval) : width t≤1/2 := min_le_left _ _
  have hwidthDist (t : Interval) : width t≤Metric.infDist (qClock t,zz) badDomain/2 := min_le_right _ _
  have hwidthPos (t : Interval) (ht : q t∉frontier F) : 0<width t := by
    have hn : (qClock t,zz)∉badDomain := by
      rintro (hn|he)
      · exact hn (hbaseGood t ht)
      · have he' : (0:ℝ)=1 := congrArg Subtype.val he
        norm_num at he'
    exact lt_min (by norm_num)
      (half_pos ((hbadDomain.notMem_iff_infDist_pos hbadNonempty).mp hn))
  have hwidthZero (t : Interval) (ht : q t∈frontier F) : width t=0 := by
    have hb : (qClock t,zz)∈badDomain := by
      left
      intro hg
      have hi : q t∈interior F := by
        have hh := hg.1.1
        rwa [hNcenter,hqClock] at hh
      exact (mem_frontier_iff_notMem_interior (hqInF t)).mp ht hi
    have he := Metric.infDist_zero_of_mem hb
    change min (1/2) (Metric.infDist (qClock t,zz) badDomain/2)=0
    rw [he]
    norm_num
  have hwidthZeroIff (t : Interval) : width t=0 ↔ q t∈frontier F := by
    constructor
    · intro he
      by_contra hn
      have hp := hwidthPos t hn
      rw [he] at hp
      exact (lt_irrefl 0) hp
    · exact hwidthZero t
  have hbandGood (t : Interval) (w : Icc (-1:ℝ) 1)
      (ht : q t∉frontier F) (hw : |(w:ℝ)|≤width t) : (qClock t,w)∈goodDomain := by
    by_contra hn
    have hb : (qClock t,w)∈badDomain := Or.inl hn
    have hdist : dist (qClock t,zz) (qClock t,w)=|(w:ℝ)| := by
      rw [Prod.dist_eq,dist_self,Subtype.dist_eq,Real.dist_eq]
      change max 0 |0-(w:ℝ)|=|(w:ℝ)|
      rw [zero_sub,abs_neg,max_eq_right (abs_nonneg _)]
    have hle := Metric.infDist_le_dist_of_mem hb (x:=(qClock t,zz))
    rw [hdist] at hle
    have hp := hwidthPos t ht
    linarith [hwidthDist t]
  have hKnonempty : Nonempty K := by
    rcases hgenuine with h0|h1
    · exact ⟨⟨false,by simpa [endAt] using h0⟩⟩
    · exact ⟨⟨true,by simpa [endAt] using h1⟩⟩
  let chosenCorner : K := Classical.choice hKnonempty
  let movingSign : K → ℝ := fun k =>
    ActualHarerCornerGeometry.inwardParameterSign (endAt k.val) gStart gEnd
  have hmovingSign (k : K) : movingSign k=-1 ∨ movingSign k=1 := by
    dsimp [movingSign,ActualHarerCornerGeometry.inwardParameterSign]
    split_ifs <;> simp
  let τ : ℝ := -movingSign chosenCorner*σ chosenCorner
  have hτ : τ=-1 ∨ τ=1 := by
    rcases hmovingSign chosenCorner with hm|hm <;> rcases hσ chosenCorner with hs|hs <;>
      simp [τ,hm,hs]
  have hτabs : |τ|=1 := by rcases hτ with ht|ht <;> norm_num [ht]
  have hτne : τ≠0 := by rcases hτ with ht|ht <;> norm_num [ht]
  have hChosenSign : movingSign chosenCorner*σ chosenCorner*τ=-1 := by
    rcases hmovingSign chosenCorner with hm|hm <;> rcases hσ chosenCorner with hs|hs <;>
      norm_num [τ,hm,hs]
  let signedWidth : Interval×Interval → Icc (-1:ℝ) 1 := fun p =>
    ⟨p.2.val*(τ*width p.1),by
      apply abs_le.mp
      rw [abs_mul,abs_of_nonneg p.2.property.1,abs_mul,hτabs,one_mul,
        abs_of_nonneg (hwidthNonneg p.1)]
      exact (mul_le_of_le_one_left (hwidthNonneg p.1) p.2.property.2).trans
        ((hwidthHalf p.1).trans (by norm_num))⟩
  have hsignedWidth : Continuous signedWidth := by
    apply Continuous.subtype_mk
    exact continuous_snd.subtype_val.mul
      (continuous_const.mul (width.continuous.comp continuous_fst))
  let H : C(Interval×Interval,S) :=
    ⟨fun p => N (qClock p.1,signedWidth p),hN.continuous.comp
      ((qClock.continuous.comp continuous_fst).prodMk hsignedWidth)⟩
  have hHcenter (t : Interval) : H (t,0)=q t := by
    change N (qClock t,signedWidth (t,0))=q t
    have hw : signedWidth (t,0)=zz := Subtype.ext (zero_mul _)
    rw [hw,hNcenter,hqClock]
  have hHcollapse (t u : Interval) (ht : q t∈frontier F) : H (t,u)=q t := by
    change N (qClock t,signedWidth (t,u))=q t
    have hw : signedWidth (t,u)=zz := by
      apply Subtype.ext
      change u.val*(τ*width t)=0
      rw [hwidthZero t ht,mul_zero,mul_zero]
    rw [hw,hNcenter,hqClock]
  have hHcollision (t u t' u' : Interval) : H (t,u)=H (t',u') ↔
      t=t' ∧ (u=u' ∨ q t∈frontier F) := by
    constructor
    · intro he
      have hp := hN.injective he
      have htt : t=t' := hqClockInj (congrArg Prod.fst hp)
      refine ⟨htt,?_⟩
      subst t'
      by_cases ht : q t∈frontier F
      · exact Or.inr ht
      · left
        apply Subtype.ext
        have hv := congrArg (fun p:Z => (p.2:ℝ)) hp
        change u.val*(τ*width t)=u'.val*(τ*width t) at hv
        exact mul_right_cancel₀ (mul_ne_zero hτne (ne_of_gt (hwidthPos t ht))) hv
    · rintro ⟨rfl,hu|ht⟩
      · rw [hu]
      · exact (hHcollapse t u ht).trans (hHcollapse t u' ht).symm
  have hHgood (t u : Interval) (ht : q t∉frontier F) :
      (qClock t,signedWidth (t,u))∈goodDomain := by
    apply hbandGood t _ ht
    change |u.val*(τ*width t)|≤width t
    rw [abs_mul,abs_of_nonneg u.property.1,abs_mul,hτabs,one_mul,abs_of_nonneg (hwidthNonneg t)]
    exact mul_le_of_le_one_left (hwidthNonneg t) u.property.2
  have hHF : range H⊆F := by
    rintro x ⟨⟨t,u⟩,rfl⟩
    by_cases ht : q t∈frontier F
    · rw [hHcollapse t u ht]
      exact hqInF t
    · exact interior_subset (hHgood t u ht).1.1
  have hHfrontier (t u : Interval) (hu : H (t,u)∈frontier F) :
      q t∈frontier F ∧ H (t,u)=q t := by
    have ht : q t∈frontier F := by
      by_contra hn
      have hInt : H (t,u)∈interior F := (hHgood t u hn).1.1
      exact (mem_frontier_iff_notMem_interior (hHF (mem_range_self (t,u)))).mp hu hInt
    exact ⟨ht,hHcollapse t u ht⟩
  have hHclear (t u : Interval) (ht : q t∉frontier F) (hu : 0<u) :
      H (t,u)∉⋃ k,range (av k) :=
    hNclear (qClock t) (signedWidth (t,u))
      (mul_ne_zero (show (u:ℝ)≠0 from ne_of_gt hu) (mul_ne_zero hτne (ne_of_gt (hwidthPos t ht))))
  have hHcornerT (k : K) (u : Interval) : H (endAt k.val,u)∈cornerT k := by
    have hh := mem_iInter.mp (hHgood (endAt k.val) u k.property).2 k
    exact hh.resolve_left (by intro hn; exact hn rfl)
  have hHcornerFrame (k : K) (u : Interval) :
      (cornerE k) (H (endAt k.val,u)) =
        Plane.mk 0 (σ k*δ k*(u.val*(τ*width (endAt k.val)))) := by
    have hh := (hNframe k (θ k) (signedWidth (endAt k.val,u))
      (by simpa only [sub_self,abs_zero] using (hδη k).2)).2
    change cornerE k (H (endAt k.val,u))=_ at hh
    rw [(hcornerE k).center_zero] at hh
    exact hh
  have hHcornerMoving (k : K) (u : Interval) : H (endAt k.val,u)∈range (bv j) := by
    apply ((hcornerE k).moving_axis _ (hcornerTE k (hHcornerT k u))).mpr
    rw [hHcornerFrame]
    rfl
  have hHmovingOnlyEnds (t u : Interval) (hxB : H (t,u)∈⋃ k,range (bv k)) : t=0 ∨ t=1 := by
    by_cases ht : q t∈frontier F
    · by_cases h0 : t=0
      · exact Or.inl h0
      by_cases h1 : t=1
      · exact Or.inr h1
      exact (hqInternalClear t ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩ ht).elim
    · have hGood := hHgood t u ht
      have hSome : H (t,u)∈⋃ k:K,cornerT k := by
        by_contra hn
        exact hGood.1.2 ⟨hxB,hn⟩
      obtain ⟨k,hk⟩ := mem_iUnion.mp hSome
      have hNear := hcornerTnear k (qClock t,signedWidth (t,u)) hk
      have hFrame := hNframe k (qClock t) (signedWidth (t,u)) hNear
      have hxj : H (t,u)∈range (bv j) := by
        obtain ⟨m,hm⟩ := mem_iUnion.mp hxB
        by_cases he : m=j
        · exact he ▸ hm
        · exact (disjoint_left.mp (hcornerOtherB k m he) hFrame.1 hm).elim
      have hx0 := ((hcornerE k).moving_axis _ hFrame.1).mp hxj
      rw [hFrame.2] at hx0
      change cornerE k (av i (qClock t)) 0=0 at hx0
      have hBase := hNframe k (qClock t) zz hNear
      rw [hNcenter] at hBase
      have hy0 := ((hcornerE k).anchor_axis _ hBase.1).mp (mem_range_self (qClock t))
      have hZero : cornerE k (av i (qClock t))=0 := by ext n;fin_cases n <;> assumption
      have htθ : qClock t=θ k := haemb.injective
        ((cornerE k).injOn hBase.1 (hcornerE k).center_mem
          (hZero.trans (hcornerE k).center_zero.symm))
      have htv : t=endAt k.val := hqClockInj htθ
      exact htv.symm ▸ hendAt k.val
  have hHendsMoving (v : Interval) (hv : v=0 ∨ v=1) (u : Interval) :
      H (v,u)∈range (bv j) := by
    by_cases ht : q v∈frontier F
    · rw [hHcollapse v u ht]
      apply hgb
      rcases hv with rfl|rfl
      · exact ⟨0,hzero.symm⟩
      · exact ⟨1,hone.symm⟩
    · rcases hv with rfl|rfl
      · exact hHcornerMoving ⟨false,by simpa [endAt] using ht⟩ u
      · exact hHcornerMoving ⟨true,by simpa [endAt] using ht⟩ u
  have hHmoving : range H∩(⋃ k,range (bv k))=
      range (fun u:Interval => H (0,u))∪range (fun u:Interval => H (1,u)) := by
    ext x
    constructor
    · rintro ⟨⟨⟨t,u⟩,rfl⟩,hx⟩
      rcases hHmovingOnlyEnds t u hx with rfl|rfl
      · exact Or.inl ⟨u,rfl⟩
      · exact Or.inr ⟨u,rfl⟩
    · rintro (⟨u,rfl⟩|⟨u,rfl⟩)
      · exact ⟨mem_range_self (0,u),mem_iUnion.mpr ⟨j,hHendsMoving 0 (Or.inl rfl) u⟩⟩
      · exact ⟨mem_range_self (1,u),mem_iUnion.mpr ⟨j,hHendsMoving 1 (Or.inr rfl) u⟩⟩
  have hHcornerDisk (k : K) (u : Interval) : H (endAt k.val,u)∈range d ↔
      0 ≤ movingSign k*(σ k*δ k*(u.val*(τ*width (endAt k.val)))) := by
    have hx := hcornerTcoords k _ (hHcornerT k u)
    have hb := (hcornerBank k ((cornerE k) (H (endAt k.val,u))) hx.1 hx.2).2.2
    rw [(cornerE k).left_inv (hcornerTE k (hHcornerT k u))] at hb
    rw [hHcornerFrame] at hb
    change H (endAt k.val,u)∈range d ↔
      0≤ActualHarerCornerGeometry.inwardParameterSign (endAt k.val) qStart qEnd*0 ∧
      0 ≤ movingSign k*(σ k*δ k*(u.val*(τ*width (endAt k.val)))) at hb
    simpa only [mul_zero,le_refl,true_and] using hb
  have hChosenOutside : H (endAt chosenCorner.val,1)∉range d := by
    intro hi
    have hh := (hHcornerDisk chosenCorner 1).mp hi
    have he : movingSign chosenCorner*(σ chosenCorner*δ chosenCorner*
        ((1:Interval).val*(τ*width (endAt chosenCorner.val))))=
        -δ chosenCorner*width (endAt chosenCorner.val) := by
      calc
        _ = (movingSign chosenCorner*σ chosenCorner*τ)*δ chosenCorner*width (endAt chosenCorner.val) := by norm_num;ring
        _ = _ := by rw [hChosenSign];ring
    rw [he] at hh
    have hp := mul_pos (hδη chosenCorner).1 (hwidthPos _ chosenCorner.property)
    nlinarith
  let strictBand : Set (Interval×Interval) := Ioo 0 1 ×ˢ Ioc 0 1
  have hStrictConn : IsPreconnected (H '' strictBand) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioc).image H H.continuous.continuousOn
  have hStrictAvoid : Disjoint (H '' strictBand) (frontier (range d)) := by
    apply disjoint_left.mpr
    rintro x ⟨⟨t,u⟩,⟨ht,hu⟩,rfl⟩ hx
    have htn := hqInternalClear t ht
    rcases (hdBoundary ▸ hx) with hxq|hxg
    · exact hHclear t u htn hu.1 (mem_iUnion.mpr ⟨i,hqa hxq⟩)
    · rcases hHmovingOnlyEnds t u (mem_iUnion.mpr ⟨j,hgb hxg⟩) with he|he
      · exact (he ▸ ht.1).false
      · exact (he ▸ ht.2).false
  have hStrictClassify : H '' strictBand⊆interior (range d) ∨ H '' strictBand⊆(range d)ᶜ := by
    apply hStrictConn.subset_or_subset isOpen_interior (isCompact_range d.continuous).isClosed.isOpen_compl
      (disjoint_left.mpr (fun x hx hn => hn (interior_subset hx)))
    intro x hx
    by_cases hd' : x∈range d
    · left
      by_contra hn
      exact disjoint_left.mp hStrictAvoid hx
        ((isCompact_range d.continuous).isClosed.frontier_eq ▸ ⟨hd',hn⟩)
    · exact Or.inr hd'
  have hIntervalClosure : closure (Ioo (0:Interval) 1)=univ := by
    rw [closure_Ioo zero_ne_one]
    exact Icc_bot_top
  have hStrictOutside : ∀ t∈Ioo (0:Interval) 1,∀ u:Interval,0<u → H (t,u)∉range d := by
    rcases hStrictClassify with hi|ho
    · have hClosed : IsClosed {t:Interval | H (t,1)∈range d} :=
        (isCompact_range d.continuous).isClosed.preimage
          (H.continuous.comp (continuous_id.prodMk continuous_const))
      have hContain : Ioo (0:Interval) 1⊆{t:Interval | H (t,1)∈range d} := by
        intro t ht
        change H (t,1)∈range d
        exact interior_subset (hi ⟨(t,1),⟨ht,⟨zero_lt_one,le_rfl⟩⟩,rfl⟩)
      have hAll := closure_minimal hContain hClosed
      rw [hIntervalClosure] at hAll
      exact (hChosenOutside (hAll (mem_univ _))).elim
    · intro t ht u hu
      exact ho ⟨(t,u),⟨ht,⟨hu,le_top⟩⟩,rfl⟩
  have hsignCompatibility (k : K) : movingSign k*σ k*τ=-1 := by
    have hnhds : {t:Interval | H (t,1)∈cornerT k}∈nhds (endAt k.val) :=
      ((hcornerT k).preimage (H.continuous.comp (continuous_id.prodMk continuous_const))).mem_nhds
        (hHcornerT k 1)
    have hClosure : endAt k.val∈closure (Ioo (0:Interval) 1) := hIntervalClosure.symm ▸ mem_univ _
    obtain ⟨t,htT,htInt⟩ := mem_closure_iff_nhds.mp hClosure _ hnhds
    have hNear := hcornerTnear k (qClock t,signedWidth (t,1)) htT
    have hFrame := hNframe k (qClock t) (signedWidth (t,1)) hNear
    change H (t,1)∈(cornerE k).source ∧ cornerE k (H (t,1))=
      Plane.mk (cornerE k (av i (qClock t)) 0) (σ k*δ k*((1:Interval).val*(τ*width t))) at hFrame
    simp only [show (1:Interval).val=(1:ℝ) from rfl,one_mul] at hFrame
    rw [hqClock] at hFrame
    have hBase := hNframe k (qClock t) zz hNear
    rw [hNcenter,hqClock] at hBase
    have hCoords := hcornerTcoords k _ htT
    have hCoordsX : |cornerE k (q t) 0|<cornerRad k := by
      have he : cornerE k (H (t,1)) 0=cornerE k (q t) 0 := by
        rw [hFrame.2]
        rfl
      rw [he] at hCoords
      exact hCoords.1
    have hBaseZero : cornerE k (q t) 1=0 :=
      ((hcornerE k).anchor_axis _ hBase.1).mp (hqa (mem_range_self t))
    have hqin := (hcornerBank k (cornerE k (q t)) hCoordsX
      (by rw [hBaseZero,abs_zero];exact hcornerRad k)).1
    rw [(cornerE k).left_inv hBase.1] at hqin
    have hxIn := (hqin.mp (mem_range_self t)).2
    have hnotD := hStrictOutside t htInt 1 zero_lt_one
    have hBank := (hcornerBank k (cornerE k (H (t,1))) hCoords.1 hCoords.2).2.2
    rw [(cornerE k).left_inv hFrame.1] at hBank
    have hYneg : movingSign k*(σ k*δ k*(τ*width t))<0 := by
      apply lt_of_not_ge
      intro hy
      apply hnotD
      apply hBank.mpr
      rw [hFrame.2]
      exact ⟨hxIn,hy⟩
    rcases hmovingSign k with hm|hm <;> rcases hσ k with hs|hs <;> rcases hτ with ht|ht
    all_goals norm_num [hm,hs,ht] at hYneg ⊢
    all_goals have hp := mul_pos (hδη k).1 (hwidthPos t (hqInternalClear t htInt));nlinarith
  have hCornerOutside (k : K) (u : Interval) (hu : 0<u) : H (endAt k.val,u)∉range d := by
    intro hi
    have hh := (hHcornerDisk k u).mp hi
    have he : movingSign k*(σ k*δ k*(u.val*(τ*width (endAt k.val))))=
        -(δ k*u.val*width (endAt k.val)) := by
      calc
        _ = (movingSign k*σ k*τ)*δ k*u.val*width (endAt k.val) := by ring
        _ = _ := by rw [hsignCompatibility];ring
    rw [he] at hh
    have hp := mul_pos (mul_pos (hδη k).1 (show (0:ℝ)<u from hu)) (hwidthPos _ k.property)
    linarith
  have hHoutside (t u : Interval) (ht : q t∉frontier F) (hu : 0<u) : H (t,u)∉range d := by
    by_cases h0 : t=0
    · subst t
      exact hCornerOutside ⟨false,by simpa [endAt] using ht⟩ u hu
    by_cases h1 : t=1
    · subst t
      exact hCornerOutside ⟨true,by simpa [endAt] using ht⟩ u hu
    exact hStrictOutside t ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩ u hu
  have hHdisk : range H∩range d=range q := by
    ext x
    constructor
    · rintro ⟨⟨⟨t,u⟩,rfl⟩,hxD⟩
      by_cases ht : q t∈frontier F
      · exact ⟨t,(hHcollapse t u ht).symm⟩
      by_cases hu : u=0
      · subst u
        exact ⟨t,(hHcenter t).symm⟩
      exact (hHoutside t u ht (bot_lt_iff_ne_bot.mpr hu) hxD).elim
    · rintro ⟨t,rfl⟩
      refine ⟨⟨(t,0),hHcenter t⟩,?_⟩
      apply image_subset_range d _
      rw [hboundary]
      exact Or.inl (mem_range_self t)
  let originalEnd : Bool → Interval := fun k => if k then gEnd else gStart
  have hOriginalEnd (k : Bool) : bv j (originalEnd k)=q (endAt k) := by
    cases k
    · exact hgStart.trans hzero.symm
    · exact hgEnd.trans hone.symm
  have hCutsExist (k : Bool) : ∃ z:Interval,bv j z=H (endAt k,1) :=
    hHendsMoving (endAt k) (hendAt k) 1
  choose cut hcut using hCutsExist
  have hCutCollapse (k : Bool) (hk : q (endAt k)∈frontier F) : cut k=originalEnd k :=
    (hbemb j).injective ((hcut k).trans ((hHcollapse _ 1 hk).trans (hOriginalEnd k).symm))
  have hCutDirection (k : K) :
      (movingSign k=1 → cut k.val<originalEnd k.val) ∧
      (movingSign k=-1 → originalEnd k.val<cut k.val) := by
    have hsource : bv j (cut k.val)∈(cornerE k).source :=
      (hcut k.val).symm ▸ hcornerTE k (hHcornerT k 1)
    have horder := (hcornerE k).moving_order (cut k.val) hsource
    have hp : ActualHarerCornerGeometry.endpointParameter (endAt k.val) gStart gEnd=originalEnd k.val := by
      cases hk : k.val <;> simp [endAt,originalEnd,hk,ActualHarerCornerGeometry.endpointParameter]
    rw [hp,hcut k.val,hHcornerFrame] at horder
    have hs : movingSign k*(σ k*δ k*((1:Interval).val*(τ*width (endAt k.val))))<0 := by
      have he : movingSign k*(σ k*δ k*((1:Interval).val*(τ*width (endAt k.val))))=
          -(δ k*width (endAt k.val)) := by
        calc
          _ = (movingSign k*σ k*τ)*δ k*width (endAt k.val) := by norm_num;ring
          _ = _ := by rw [hsignCompatibility];ring
      rw [he]
      exact neg_neg_of_pos (mul_pos (hδη k).1 (hwidthPos _ k.property))
    constructor
    · intro hm
      apply horder.1.mp
      change σ k*δ k*((1:Interval).val*(τ*width (endAt k.val)))<0
      simpa only [hm,one_mul] using hs
    · intro hm
      apply horder.2.mp
      change 0<σ k*δ k*((1:Interval).val*(τ*width (endAt k.val)))
      rw [hm,neg_one_mul] at hs
      exact neg_neg_iff_pos.mp hs
  let port : Bool → C(Interval,S) := fun k =>
    ⟨fun u => H (endAt k,u),H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hPortRange (k : Bool) : range (port k)=bv j '' uIcc (originalEnd k) (cut k) := by
    by_cases hk : q (endAt k)∈frontier F
    · rw [hCutCollapse k hk,uIcc_self,image_singleton]
      ext x
      constructor
      · rintro ⟨u,rfl⟩
        exact mem_singleton_iff.mpr ((hHcollapse _ u hk).trans (hOriginalEnd k).symm)
      · intro hx
        refine ⟨0,?_⟩
        exact (hHcenter _).trans ((hOriginalEnd k).symm.trans (mem_singleton_iff.mp hx).symm)
    · have hp : IsEmbedding (port k) := ((port k).continuous.isClosedEmbedding (by
        intro u u' he
        exact ((hHcollision (endAt k) u (endAt k) u').mp he).2.resolve_right hk)).isEmbedding
      obtain ⟨r,s,hrs,hr,hs,htrace⟩ :=
        actual_embedded_subarc_constructs_exact_unordered_parameter_interval
          (bv j) (port k) (hbemb j) hp
          (by rintro x ⟨u,rfl⟩;exact hHendsMoving _ (hendAt k) u)
      have hr' : r=originalEnd k := (hbemb j).injective
        (hr.trans ((hHcenter _).trans (hOriginalEnd k).symm))
      have hs' : s=cut k := (hbemb j).injective (hs.trans (hcut k).symm)
      simpa only [hr',hs'] using htrace
  have hCutOrderForward (horder : gStart<gEnd) :
      cut false≤gStart ∧ gEnd≤cut true ∧
      (q 0∉frontier F → cut false<gStart) ∧ (q 1∉frontier F → gEnd<cut true) := by
    have h0 (hk : q 0∉frontier F) : cut false<gStart := by
      let k : K := ⟨false,by simpa [endAt] using hk⟩
      exact (hCutDirection k).1 (by simp [movingSign,k,endAt,ActualHarerCornerGeometry.inwardParameterSign,horder])
    have h1 (hk : q 1∉frontier F) : gEnd<cut true := by
      let k : K := ⟨true,by simpa [endAt] using hk⟩
      exact (hCutDirection k).2 (by simp [movingSign,k,endAt,ActualHarerCornerGeometry.inwardParameterSign,not_lt.mpr horder.le])
    refine ⟨?_,?_,h0,h1⟩
    · by_cases hk : q 0∈frontier F
      · have he := hCutCollapse false (show q (endAt false)∈frontier F from hk)
        exact (show cut false=gStart from he).le
      · exact (h0 hk).le
    · by_cases hk : q 1∈frontier F
      · have he := hCutCollapse true (show q (endAt true)∈frontier F from hk)
        exact (show cut true=gEnd from he).ge
      · exact (h1 hk).le
  have hCutOrderReverse (horder : gEnd<gStart) :
      cut true≤gEnd ∧ gStart≤cut false ∧
      (q 1∉frontier F → cut true<gEnd) ∧ (q 0∉frontier F → gStart<cut false) := by
    have h0 (hk : q 0∉frontier F) : gStart<cut false := by
      let k : K := ⟨false,by simpa [endAt] using hk⟩
      exact (hCutDirection k).2 (by simp [movingSign,k,endAt,ActualHarerCornerGeometry.inwardParameterSign,not_lt.mpr horder.le])
    have h1 (hk : q 1∉frontier F) : cut true<gEnd := by
      let k : K := ⟨true,by simpa [endAt] using hk⟩
      exact (hCutDirection k).1 (by simp [movingSign,k,endAt,ActualHarerCornerGeometry.inwardParameterSign,horder])
    refine ⟨?_,?_,h1,h0⟩
    · by_cases hk : q 1∈frontier F
      · have he := hCutCollapse true (show q (endAt true)∈frontier F from hk)
        exact (show cut true=gEnd from he).le
      · exact (h1 hk).le
    · by_cases hk : q 0∈frontier F
      · have he := hCutCollapse false (show q (endAt false)∈frontier F from hk)
        exact (show cut false=gStart from he).ge
      · exact (h0 hk).le
  have hCutNe : cut false≠cut true := by
    rcases lt_or_gt_of_ne hgEndsNe with ho|ho
    · have h := hCutOrderForward ho
      exact ne_of_lt (h.1.trans_lt (ho.trans_le h.2.1))
    · have h := hCutOrderReverse ho
      exact ne_of_gt (h.1.trans_lt (ho.trans_le h.2.1))
  let c₀ : Bool := decide (q 0∈frontier F)
  let c₁ : Bool := decide (q 1∈frontier F)
  have hnotBoth : ¬(c₀=true ∧ c₁=true) := by
    simp only [c₀,c₁,decide_eq_true_eq]
    intro hh
    exact hgenuine.elim (fun hn => hn hh.1) (fun hn => hn hh.2)
  have hcollapseIff (t : Interval) : ActualHarerDiskGluing.collapsedEndpoint c₀ c₁ t ↔ q t∈frontier F := by
    simp only [ActualHarerDiskGluing.collapsedEndpoint,c₀,c₁,decide_eq_true_eq]
    constructor
    · rintro (⟨h,rfl⟩|⟨h,rfl⟩) <;> exact h
    · intro ht
      by_cases h0 : t=0
      · exact Or.inl ⟨h0 ▸ ht,h0⟩
      by_cases h1 : t=1
      · exact Or.inr ⟨h1 ▸ ht,h1⟩
      exact (hqInternalClear t ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩ ht).elim
  have hqgCollision (s t : Interval) (he : q s=g t) : (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
    have hh := hSides ▸ (show q s∈range q∩range g from ⟨mem_range_self s,⟨t,he.symm⟩⟩)
    rcases hh with hh|hh
    · have hs : s=0 := hq.injective hh
      exact Or.inl ⟨hs,hg.injective (he.symm.trans (hh.trans hzero))⟩
    · have hs : s=1 := hq.injective (mem_singleton_iff.mp hh)
      exact Or.inr ⟨hs,hg.injective (he.symm.trans ((mem_singleton_iff.mp hh).trans hone))⟩
  obtain ⟨comparisonDisk,hComparisonDisk,hComparisonRange,hComparisonBoundary⟩ :=
    ActualHarerDiskGluing.actual_disk_attach_half_collar_with_optional_endpoint_collapse
      q g d hq hg hd hzero hone hboundary hqgCollision H c₀ c₁ hnotBoth hHcenter
      (by intro t u t' u';rw [hHcollision,hcollapseIff]) hHdisk
  let cutLo := min (cut false) (cut true)
  let cutHi := max (cut false) (cut true)
  have hCutLoHi : cutLo<cutHi := by
    rcases lt_or_gt_of_ne hCutNe with he|he
    · simpa only [cutLo,cutHi,min_eq_left he.le,max_eq_right he.le] using he
    · simpa only [cutLo,cutHi,min_eq_right he.le,max_eq_left he.le] using he
  obtain ⟨longOld,hLongOld,hLong0,hLong1,hLongRange⟩ :=
    actual_selected_arc_interval_constructs_embedded_literal_old_subarc (bv j) (hbemb j) cutLo cutHi hCutLoHi
  have hThreeIntervals (a b c d : Interval) (hab : a≤b) (hbc : b≤c) (hcd : c≤d) :
      Icc a d=Icc b c∪uIcc b a∪uIcc c d := by
    rw [uIcc_of_ge hab,uIcc_of_le hcd]
    ext z
    simp only [mem_union,mem_Icc]
    constructor
    · intro hz
      by_cases hzb : z≤b
      · exact Or.inl (Or.inr ⟨hz.1,hzb⟩)
      by_cases hzc : z≤c
      · exact Or.inl (Or.inl ⟨le_of_not_ge hzb,hzc⟩)
      · exact Or.inr ⟨le_of_not_ge hzc,hz.2⟩
    · rintro ((hz|hz)|hz)
      · exact ⟨hab.trans hz.1,hz.2.trans hcd⟩
      · exact ⟨hz.1,hz.2.trans (hbc.trans hcd)⟩
      · exact ⟨(hab.trans hbc).trans hz.1,hz.2⟩
  have hLongUnion : range longOld=range g∪range (port false)∪range (port true) := by
    rw [hLongRange,hgParamTrace,hPortRange false,hPortRange true]
    change bv j '' Icc cutLo cutHi=bv j '' uIcc gStart gEnd∪
      bv j '' uIcc gStart (cut false)∪bv j '' uIcc gEnd (cut true)
    rcases lt_or_gt_of_ne hgEndsNe with ho|ho
    · have hc := hCutOrderForward ho
      have hh : cut false≤cut true := hc.1.trans (ho.le.trans hc.2.1)
      rw [show cutLo=cut false from min_eq_left hh,show cutHi=cut true from max_eq_right hh,
        uIcc_of_le ho.le,hThreeIntervals _ _ _ _ hc.1 ho.le hc.2.1,image_union,image_union]
    · have hc := hCutOrderReverse ho
      have hh : cut true≤cut false := hc.1.trans (ho.le.trans hc.2.1)
      rw [show cutLo=cut true from min_eq_right hh,show cutHi=cut false from max_eq_left hh,
        uIcc_of_ge ho.le,hThreeIntervals _ _ _ _ hc.1 ho.le hc.2.1,image_union,image_union]
      exact union_right_comm _ _ _
  have hgLong : range g⊆range longOld := by rw [hLongUnion];exact subset_union_of_subset_left subset_union_left _
  let rail : C(Interval,S) := ⟨fun t => H (t,1),H.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hRail : IsEmbedding rail := (rail.continuous.isClosedEmbedding (by
    intro t t' he
    exact ((hHcollision t 1 t' 1).mp he).1)).isEmbedding
  have hRailEnds : ({longOld 0,longOld 1}:Set S)={rail 0,rail 1} := by
    rw [hLong0,hLong1]
    rcases le_total (cut false) (cut true) with hc|hc
    · rw [show cutLo=cut false from min_eq_left hc,show cutHi=cut true from max_eq_right hc,hcut false,hcut true]
      rfl
    · rw [show cutLo=cut true from min_eq_right hc,show cutHi=cut false from max_eq_left hc,hcut false,hcut true]
      exact pair_comm _ _
  have hNewExists : ∃ new : C(Interval,S),IsEmbedding new ∧ range new=range rail ∧
      new 0=longOld 0 ∧ new 1=longOld 1 := by
    rcases lt_or_gt_of_ne hCutNe with hc|hc
    · refine ⟨rail,hRail,rfl,?_,?_⟩
      · rw [hLong0,show cutLo=cut false from min_eq_left hc.le,hcut false]
        rfl
      · rw [hLong1,show cutHi=cut true from max_eq_right hc.le,hcut true]
        rfl
    · let revRail : C(Interval,S) := ⟨rail ∘ unitInterval.symmHomeomorph,
        rail.continuous.comp unitInterval.symmHomeomorph.continuous⟩
      refine ⟨revRail,hRail.comp unitInterval.symmHomeomorph.isEmbedding,?_,?_,?_⟩
      · exact unitInterval.symmHomeomorph.surjective.range_comp rail
      · rw [hLong0,show cutLo=cut true from min_eq_right hc.le,hcut true]
        change rail (unitInterval.symm 0)=rail 1
        rw [unitInterval.symm_zero]
      · rw [hLong1,show cutHi=cut false from max_eq_left hc.le,hcut false]
        change rail (unitInterval.symm 1)=rail 0
        rw [unitInterval.symm_one]
  obtain ⟨new,hNew,hNewRange,hNew0,hNew1⟩ := hNewExists
  have hFrontEnd (t : Interval) (ht : q t∈frontier F) : t=0 ∨ t=1 := by
    by_cases h0 : t=0
    · exact Or.inl h0
    by_cases h1 : t=1
    · exact Or.inr h1
    exact (hqInternalClear t ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩ ht).elim
  have hOldRail : range longOld∩range rail=({rail 0,rail 1}:Set S) := by
    ext x
    constructor
    · rintro ⟨hxOld,t,rfl⟩
      rw [hLongUnion] at hxOld
      rcases hxOld with (hxg|⟨u,hu⟩)|⟨u,hu⟩
      · have hxD : rail t∈range d := by
          apply image_subset_range d _
          rw [hboundary]
          exact Or.inr hxg
        have hxq : rail t∈range q := hHdisk ▸ ⟨mem_range_self (t,1),hxD⟩
        obtain ⟨s,hs⟩ := hxq
        have he : H (t,1)=H (s,0) := hs.symm.trans (hHcenter s).symm
        have htF : q t∈frontier F := ((hHcollision t 1 s 0).mp he).2.resolve_left one_ne_zero
        rcases hFrontEnd t htF with rfl|rfl
        · exact Or.inl rfl
        · exact Or.inr (mem_singleton _)
      · have he : H (t,1)=H (0,u) := hu.symm
        have ht0 := ((hHcollision t 1 0 u).mp he).1
        exact Or.inl (congrArg rail ht0)
      · have he : H (t,1)=H (1,u) := hu.symm
        have ht1 := ((hHcollision t 1 1 u).mp he).1
        exact Or.inr (mem_singleton_iff.mpr (congrArg rail ht1))
    · rintro (rfl|hx)
      · refine ⟨?_,mem_range_self 0⟩
        rw [hLongUnion]
        exact Or.inl (Or.inr ⟨1,rfl⟩)
      · have he : x=rail 1 := hx
        subst x
        refine ⟨?_,mem_range_self 1⟩
        rw [hLongUnion]
        exact Or.inr ⟨1,rfl⟩
  have hComparisonF : range comparisonDisk⊆F := by
    rw [hComparisonRange]
    exact union_subset hdF hHF
  have hComparisonMoving : range comparisonDisk∩(⋃ k,range (bv k))=range longOld := by
    have hcleanBv : range d∩(⋃ k,range (bv k))=range g := hcleanB
    rw [hComparisonRange,union_inter_distrib_right,hcleanBv,hHmoving,hLongUnion]
    exact (union_assoc _ _ _).symm
  have hComparisonFrontier : range comparisonDisk∩frontier F⊆({longOld 0,longOld 1}:Set S) := by
    rw [hRailEnds]
    rintro x ⟨hx,hxF⟩
    rw [hComparisonRange] at hx
    rcases hx with hxD|⟨⟨t,u⟩,rfl⟩
    · rcases hdFrontierCorners ⟨hxD,hxF⟩ with hx0|hx1
      · have hq0F : q 0∈frontier F := hx0 ▸ hxF
        exact Or.inl (hx0.trans (hHcollapse 0 1 hq0F).symm)
      · have he : x=q 1 := hx1
        have hq1F : q 1∈frontier F := he ▸ hxF
        exact Or.inr (mem_singleton_iff.mpr (he.trans (hHcollapse 1 1 hq1F).symm))
    · obtain ⟨htF,he⟩ := hHfrontier t u hxF
      rcases hFrontEnd t htF with rfl|rfl
      · exact Or.inl (he.trans (hHcollapse 0 1 htF).symm)
      · exact Or.inr (mem_singleton_iff.mpr (he.trans (hHcollapse 1 1 htF).symm))
  have hRailClear : Disjoint (range rail\{rail 0,rail 1}) (⋃ k,range (av k)) := by
    apply disjoint_left.mpr
    rintro x ⟨⟨t,rfl⟩,hnot⟩ hxA
    have ht : q t∉frontier F := by
      intro ht
      rcases hFrontEnd t ht with rfl|rfl
      · exact hnot (Or.inl rfl)
      · exact hnot (Or.inr (mem_singleton _))
    exact hHclear t 1 ht zero_lt_one hxA
  have hGenuineLong : q v∈range longOld\{longOld 0,longOld 1} := by
    refine ⟨hgLong ⟨v,hqg.symm⟩,?_⟩
    rw [hRailEnds]
    intro he
    have hImpossible (w : Interval) (he : q v=rail w) : False := by
      have hh : H (v,0)=H (w,1) := (hHcenter v).trans he
      exact hvFront (((hHcollision v 0 w 1).mp hh).2.resolve_left zero_ne_one)
    rcases he with he|he
    · exact hImpossible 0 he
    · exact hImpossible 1 (mem_singleton_iff.mp he)
  refine ⟨cutLo,cutHi,longOld,new,comparisonDisk,hCutLoHi,hLongOld,hNew,hComparisonDisk,
    hLong0,hLong1,hLongRange,hgLong,hNew0,hNew1,?_,?_,?_,hComparisonF,hComparisonMoving,
    hComparisonFrontier,?_,v,hv,hvFront,hGenuineLong⟩
  · rw [hNewRange,hOldRail,hRailEnds]
  · rw [hComparisonBoundary,hNewRange,hLongUnion]
    rfl
  · rw [hComparisonRange]
    exact subset_union_left
  · rw [hNewRange,hRailEnds]
    exact hRailClear


end ActualHarerSupportedBypass
