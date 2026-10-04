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

set_option maxHeartbeats 5000000


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


private theorem actual_axis_chart_constructs_normalized_closed_square
    {S : Type} [TopologicalSpace S]
    (Q : OpenPartialHomeomorph S Plane) (p : S) (hp : p∈Q.source)
    (hc : Q p 1=0) :
    ∃ N : OpenPartialHomeomorph S Plane,
      N.source=Q.source ∧ N p=0 ∧ Plane.closedSquare 0 1⊆N.target ∧
      ∀ y,N y 1=0 ↔ Q y 1=0 := by
  let f : ℝ × Plane → Plane := fun z => z.1 • z.2+Q p
  have hf : Continuous f := by dsimp [f];fun_prop
  have hprod : ({0} : Set ℝ) ×ˢ Plane.closedSquare 0 1⊆f ⁻¹' Q.target := by
    rintro ⟨t,z⟩ ⟨ht,_⟩
    have ht0 : t=0 := ht
    subst t
    simpa [f] using Q.map_source hp
  obtain ⟨V,W,hV,_,h0V,hKW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_closedSquare 0 1)
      (Q.open_target.preimage hf) hprod
  obtain ⟨ε,hε,hεV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (Set.mem_singleton 0))
  let δ := ε/2
  have hδ : 0<δ := by dsimp [δ];linarith
  have hδne : δ≠0 := ne_of_gt hδ
  have hδV : δ∈V := hεV (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hδ]
    dsimp [δ];linarith)
  let H : Plane ≃ₜ Plane := (Homeomorph.subRight (Q p)).trans
    (Homeomorph.smulOfNeZero δ hδne).symm
  let N := Q.trans H.toOpenPartialHomeomorph
  have hNs : N.source=Q.source := by simp [N,OpenPartialHomeomorph.trans_source]
  have hNval (y : S) : N y=δ⁻¹ • (Q y-Q p) := rfl
  have hHinv (z : Plane) : H.symm z=δ • z+Q p := rfl
  refine ⟨N,hNs,?_,?_,?_⟩
  · rw [hNval,sub_self,smul_zero]
  · intro z hz
    have htarget : H.symm z∈Q.target := by
      rw [hHinv]
      exact hVW (show (δ,z)∈V ×ˢ W from ⟨hδV,hKW hz⟩)
    simpa [N,OpenPartialHomeomorph.trans_target] using htarget
  · intro y
    rw [hNval,PiLp.smul_apply,Plane.sub_apply,hc,sub_zero]
    simp [hδne]


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


private theorem actual_axis_chart_closed_square_normalization_preserves_transverse_halfplanes
    {S : Type} [TopologicalSpace S]
    (Q : OpenPartialHomeomorph S Plane) (p : S) (hp : p∈Q.source)
    (hc : Q p 1=0) :
    ∃ N : OpenPartialHomeomorph S Plane,
      N.source=Q.source ∧ N p=0 ∧ Plane.closedSquare 0 1⊆N.target ∧
      (∀ y,N y 1=0 ↔ Q y 1=0) ∧
      ∀ ε y,ε*N y 1≤0 ↔ ε*Q y 1≤0 := by
  let f : ℝ × Plane → Plane := fun z => z.1 • z.2+Q p
  have hf : Continuous f := by dsimp [f];fun_prop
  have hprod : ({0} : Set ℝ) ×ˢ Plane.closedSquare 0 1⊆f ⁻¹' Q.target := by
    rintro ⟨t,z⟩ ⟨ht,_⟩
    have ht0 : t=0 := ht
    subst t
    simpa [f] using Q.map_source hp
  obtain ⟨V,W,hV,_,h0V,hKW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_closedSquare 0 1)
      (Q.open_target.preimage hf) hprod
  obtain ⟨ε,hε,hεV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (Set.mem_singleton 0))
  let δ := ε/2
  have hδ : 0<δ := by dsimp [δ];linarith
  have hδne : δ≠0 := ne_of_gt hδ
  have hδV : δ∈V := hεV (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hδ]
    dsimp [δ];linarith)
  let H : Plane ≃ₜ Plane := (Homeomorph.subRight (Q p)).trans
    (Homeomorph.smulOfNeZero δ hδne).symm
  let N := Q.trans H.toOpenPartialHomeomorph
  have hNs : N.source=Q.source := by simp [N,OpenPartialHomeomorph.trans_source]
  have hNval (y : S) : N y=δ⁻¹ • (Q y-Q p) := rfl
  have hHinv (z : Plane) : H.symm z=δ • z+Q p := rfl
  have hcoord (y : S) : N y 1=δ⁻¹*(Q y 1) := by
    rw [hNval,PiLp.smul_apply,Plane.sub_apply,hc,sub_zero]
    rfl
  refine ⟨N,hNs,?_,?_,?_,?_⟩
  · rw [hNval,sub_self,smul_zero]
  · intro z hz
    have htarget : H.symm z∈Q.target := by
      rw [hHinv]
      exact hVW (show (δ,z)∈V ×ˢ W from ⟨hδV,hKW hz⟩)
    simpa [N,OpenPartialHomeomorph.trans_target] using htarget
  · intro y
    rw [hcoord]
    simp [hδne]
  · intro ε y
    rw [hcoord]
    have heq : ε*(δ⁻¹*Q y 1)=δ⁻¹*(ε*Q y 1) := by ring
    rw [heq]
    constructor
    · intro h
      by_contra hn
      have hpos : 0<ε*Q y 1 := lt_of_not_ge hn
      have hprod := mul_pos (inv_pos.mpr hδ) hpos
      linarith
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hδ).le h


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




private theorem actual_embedded_subarc_internal_point_constructs_whole_arc_local_trace
    {S : Type} [TopologicalSpace S] [T2Space S]
    (f q : C(Interval,S)) (hf : IsEmbedding f) (hq : IsEmbedding q)
    (hsub : range q⊆range f) (w : Interval) (hw : w∈Ioo (0:Interval) 1) :
    ∃ U : Set S,IsOpen U ∧ q w∈U ∧ ∀ x∈U,x∈range f ↔ x∈range q := by
  classical
  let Q : C(Interval,range f) := ⟨fun t => ⟨q t,hsub (mem_range_self t)⟩,
    q.continuous.subtype_mk _⟩
  let k : Interval→Interval := hf.toHomeomorph.symm ∘ Q
  have hk : Continuous k := hf.toHomeomorph.symm.continuous.comp Q.continuous
  have hfk (t : Interval) : f (k t)=q t :=
    congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply (Q t))
  have hki : Function.Injective k := by
    intro t u he
    apply hq.injective
    rw [←hfk t,←hfk u,he]
  have hkw : k w∈Ioo (min (k 0) (k 1)) (max (k 0) (k 1)) := by
    rcases hk.strictMono_of_inj_boundedOrder' hki with hm | hm
    · exact ⟨(min_le_left _ _).trans_lt (hm hw.1),
        (hm hw.2).trans_le (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans_lt (hm hw.2),
        (hm hw.1).trans_le (le_max_left _ _)⟩
  let Far : Set S := f '' (Ioo (min (k 0) (k 1)) (max (k 0) (k 1)))ᶜ
  have hFar : IsClosed Far := ((isCompact_univ.of_isClosed_subset
    isOpen_Ioo.isClosed_compl (subset_univ _)).image f.continuous).isClosed
  have hpFar : q w∉Far := by
    rintro ⟨t,ht,he⟩
    have htEq : t=k w := hf.injective (he.trans (hfk w).symm)
    exact ht (htEq.symm ▸ hkw)
  refine ⟨Farᶜ,hFar.isOpen_compl,hpFar,?_⟩
  intro x hx
  constructor
  · rintro ⟨t,rfl⟩
    have ht : t∈Ioo (min (k 0) (k 1)) (max (k 0) (k 1)) := by
      by_contra hn
      exact hx ⟨t,hn,rfl⟩
    have htImage : t∈k '' Icc (0:Interval) 1 := by
      rcases le_total (k 0) (k 1) with hle | hle
      · apply intermediate_value_Icc zero_le_one hk.continuousOn
        exact ⟨by simpa only [min_eq_left hle] using ht.1.le,
          by simpa only [max_eq_right hle] using ht.2.le⟩
      · apply intermediate_value_Icc' zero_le_one hk.continuousOn
        exact ⟨by simpa only [min_eq_right hle] using ht.1.le,
          by simpa only [max_eq_left hle] using ht.2.le⟩
    obtain ⟨z,_,hz⟩ := htImage
    exact ⟨z,(hfk z).symm.trans (congrArg f hz)⟩
  · exact fun h => hsub h

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

private theorem actual_straight_disk_frontier_chart_constructs_positive_interior_bank_chart
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (d : C(Metric.closedBall (0:Plane) 1,S)) (hd : IsEmbedding d)
    (Q : OpenPartialHomeomorph S Plane) (p : S)
    (hp : p∈Q.source) (hzero : Q p=0)
    (hSquare : Plane.closedSquare 0 1⊆Q.target)
    (hfrontier : ∀ x∈Q.source,(x∈frontier (range d) ↔ Q x 1=0)) :
    ∃ E : OpenPartialHomeomorph S Plane,
      p∈E.source ∧ E p=0 ∧ E.source⊆Q.source ∧
      (∀ x,E x 1=0 ↔ Q x 1=0) ∧
      ∀ x∈E.source,(x∈interior (range d) ↔ 0<E x 1) := by
  have hBox (z : Plane) (hz : -1<z 0 ∧ z 0<1 ∧ -1<z 1 ∧ z 1<1) :
      z∈Plane.closedSquare 0 1 := by
    apply mem_closedSquare_zero_one.mpr
    change max |z 0| |z 1|≤1
    rw [max_le_iff,abs_le,abs_le]
    exact ⟨⟨hz.1.le,hz.2.1.le⟩,⟨hz.2.2.1.le,hz.2.2.2.le⟩⟩
  have hTarget : {z : Plane | -1<z 0 ∧ z 0<1 ∧ -1<z 1 ∧ z 1<1}⊆Q.target :=
    fun z hz => hSquare (hBox z hz)
  have hFront : ∀ z : Plane,-1<z 0 → z 0<1 → -1<z 1 → z 1<1 →
      (Q.symm z∈frontier (range d) ↔ z 1=0) := by
    intro z h0 h1 h2 h3
    have hzT := hTarget ⟨h0,h1,h2,h3⟩
    simpa only [Q.right_inv hzT] using hfrontier (Q.symm z) (Q.map_target hzT)
  obtain ⟨G,hGs,hGx,hGy,hGinside⟩ :=
    CurveComplex.actual_embedded_disk_signed_interior_chart d hd Q (-1) 1 1
      (by norm_num) (by norm_num) hTarget hFront
  let U : Set S := Q.source∩Q ⁻¹' Plane.openSquare 0 1
  have hU : IsOpen U := Q.isOpen_inter_preimage (Plane.isOpen_openSquare 0 1)
  let E := G.restr U
  have hEs : E.source=G.source∩U := by simp only [E,OpenPartialHomeomorph.restr_source,hU.interior_eq]
  have hpU : p∈U := by
    refine ⟨hp,?_⟩
    change Q p∈Plane.openSquare 0 1
    rw [hzero]
    exact mem_openSquare_zero_one.mpr (by change max |(0:ℝ)| |(0:ℝ)|<1; norm_num)
  have hGzero : G p=0 := by
    ext k
    fin_cases k
    · change G p 0=0
      rw [hGx,hzero];rfl
    · change G p 1=0
      rcases hGy p with he | he
      · rw [he,hzero];rfl
      · rw [he,hzero];simp
  refine ⟨E,hEs.symm ▸ ⟨hGs.symm ▸ hp,hpU⟩,hGzero,?_,?_,?_⟩
  · intro x hx
    rw [hEs] at hx
    exact hx.2.1
  · intro x
    change G x 1=0 ↔ Q x 1=0
    rcases hGy x with he | he
    · rw [he]
    · rw [he,neg_eq_zero]
  · intro x hx
    have hxG : x∈G.source := (hEs ▸ hx).1
    have hxSq : Q x∈Plane.openSquare 0 1 := (hEs ▸ hx).2.2
    have hSup := mem_openSquare_zero_one.mp hxSq
    change max |Q x 0| |Q x 1|<1 at hSup
    have h0 := abs_lt.mp ((le_max_left _ _).trans_lt hSup)
    have h1 := abs_lt.mp ((le_max_right _ _).trans_lt hSup)
    exact hGinside x hxG h0.1 h0.2 h1.1 h1.2

private theorem actual_noncorner_disk_side_constructs_whole_arc_axis_interior_bank_chart
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (f q g : C(Interval,S)) (hf : IsEmbedding f) (hq : IsEmbedding q)
    (hsub : range q⊆range f)
    (d : C(Metric.closedBall (0:Plane) 1,S)) (hd : IsEmbedding d)
    (hboundary : d '' {z | z.val∈Metric.sphere (0:Plane) 1}=range q∪range g)
    (w : Interval) (hw : w∈Ioo (0:Interval) 1) (hpg : q w∉range g)
    (Q : OpenPartialHomeomorph S Plane) (hp : q w∈Q.source)
    (haxis : ∀ x∈Q.source,(x∈range f ↔ Q x 1=0)) :
    ∃ E : OpenPartialHomeomorph S Plane,
      q w∈E.source ∧ E (q w)=0 ∧ E.source⊆Q.source ∧
      (∀ x∈E.source,(x∈range f ↔ E x 1=0)) ∧
      ∀ x∈E.source,(x∈interior (range d) ↔ 0<E x 1) := by
  obtain ⟨U,hU,hpU,htrace⟩ :=
    actual_embedded_subarc_internal_point_constructs_whole_arc_local_trace f q hf hq hsub w hw
  let W := U∩(range g)ᶜ
  have hW : IsOpen W := hU.inter (isCompact_range g.continuous).isClosed.isOpen_compl
  let P := Q.restr W
  have hPs : P.source=Q.source∩W := by simp only [P,OpenPartialHomeomorph.restr_source,hW.interior_eq]
  have hpP : q w∈P.source := hPs.symm ▸ ⟨hp,hpU,hpg⟩
  have hpZero : P (q w) 1=0 := (haxis (q w) hp).mp (hsub (mem_range_self w))
  obtain ⟨N,hNs,hNp,hSquare,hZero⟩ :=
    ActualHarerWholeAnchorRail.actual_axis_chart_constructs_normalized_closed_square P (q w) hpP hpZero
  have hNQ : N.source⊆Q.source := by
    intro x hx
    exact (hPs ▸ (hNs ▸ hx)).1
  have hDiskFrontier : ∀ x∈N.source,(x∈frontier (range d) ↔ N x 1=0) := by
    intro x hx
    have hxP : x∈P.source := hNs ▸ hx
    have hxU : x∈U := (hPs ▸ hxP).2.1
    have hxg : x∉range g := (hPs ▸ hxP).2.2
    rw [embedded_surface_disk_frontier_eq_boundary_image d hd,hboundary]
    change (x∈range q ∨ x∈range g) ↔ N x 1=0
    rw [or_iff_left hxg,←htrace x hxU,haxis x (hNQ hx),hZero x]
    rfl
  obtain ⟨E,hpE,hE0,hEN,hEz,hBank⟩ :=
    actual_straight_disk_frontier_chart_constructs_positive_interior_bank_chart
      d hd N (q w) (hNs.symm ▸ hpP) hNp hSquare hDiskFrontier
  refine ⟨E,hpE,hE0,hEN.trans hNQ,?_,hBank⟩
  intro x hx
  exact (haxis x (hNQ (hEN hx))).trans
    ((hZero x).symm.trans (hEz x).symm)


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

private theorem actual_empty_bank_constructs_moving_axis_same_side_window
    {S : Type} [TopologicalSpace S]
    (a b : C(Interval,S)) (ha : IsEmbedding a)
    (s : Interval) (hs : s∈Ioo (0:Interval) 1)
    (d : C(Metric.closedBall (0:Plane) 1,S))
    (hempty : Disjoint (interior (range d)) (range b))
    (Q P : OpenPartialHomeomorph S Plane)
    (hp : a s∈P.source) (hPzero : P (a s)=0) (hPQ : P.source⊆Q.source)
    (hPaxis : ∀ x∈P.source,x∈range a ↔ P x 1=0)
    (hbank : ∀ x∈P.source,x∈interior (range d) ↔ 0<P x 1)
    (hQaxis : ∀ x∈Q.source,x∈range b ↔ Q x 1=0)
    (hiso : Q.source∩(range a∩range b)={a s}) :
    ∃ l h : Interval,∃ ε : ℝ,l<s ∧ s<h ∧ (ε=(-1:ℝ) ∨ ε=1) ∧
      (∀ w∈Icc l h,a w∈Q.source) ∧
      ∀ w∈Ioo l h,w≠s → ε*Q (a w) 1<0 := by
  obtain ⟨N,hNs,hNzero,hSquare,hNz,hNsign⟩ :=
    ActualHarerContactSides.actual_axis_chart_closed_square_normalization_preserves_transverse_halfplanes
      P (a s) hp (by rw [hPzero];rfl)
  have hNQ : N.source⊆Q.source := hNs.symm ▸ hPQ
  have hNbank (x : S) (hx : x∈N.source) :
      x∈interior (range d) ↔ 0<N x 1 := by
    have hsign := hNsign 1 x
    simp only [one_mul] at hsign
    exact (hbank x (hNs ▸ hx)).trans (by simpa only [not_le] using hsign.not.symm)
  let H : Set Plane := {z | -1<z 0 ∧ z 0<1 ∧ 0<z 1 ∧ z 1<1}
  let T : Set Plane := H∪{z | -1<z 0 ∧ z 0<1 ∧ z 1=0 ∧ N.symm z∉range b}
  have hHconv : Convex ℝ H :=
    (Plane.convex_coord_gt 0 (-1)).inter
      ((Plane.convex_coord_lt 0 1).inter
        ((Plane.convex_coord_gt 1 0).inter (Plane.convex_coord_lt 1 1)))
  have hTtarget : T⊆N.target := by
    intro z hz
    apply hSquare
    apply mem_closedSquare_zero_one.mpr
    change max |z 0| |z 1|≤1
    rw [max_le_iff,abs_le,abs_le]
    rcases hz with hz | hz
    · exact ⟨⟨hz.1.le,hz.2.1.le⟩,⟨by linarith [hz.2.2.1],hz.2.2.2.le⟩⟩
    · exact ⟨⟨hz.1.le,hz.2.1.le⟩,by rw [hz.2.2.1];norm_num⟩
  have hTclosure : T⊆closure H := by
    intro z hz
    rcases hz with hz | hz
    · exact subset_closure hz
    · let f : ℝ→Plane := fun t => Plane.mk (z 0) t
      have hf : Continuous f := by dsimp [f];fun_prop
      have h0 : (0:ℝ)∈closure (Ioo (0:ℝ) 1) := by rw [closure_Ioo zero_ne_one];exact ⟨le_rfl,zero_le_one⟩
      have hzcl : f 0∈closure (f '' Ioo (0:ℝ) 1) := hf.continuousAt.continuousWithinAt.mem_closure_image h0
      have he : f 0=z := by ext j;fin_cases j <;> simp [f,hz.2.2.1]
      rw [he] at hzcl
      apply closure_mono (s:=f '' Ioo (0:ℝ) 1) (t:=H) ?_ hzcl
      rintro y ⟨t,ht,rfl⟩
      exact ⟨hz.1,hz.2.1,ht.1,ht.2⟩
  have hTconn : IsPreconnected T := hHconv.isPreconnected.subset_closure subset_union_left hTclosure
  let f : Plane→ℝ := fun z => Q (N.symm z) 1
  have hfc : ContinuousOn f T := (Plane.continuous_coord 1).continuousOn.comp
    (Q.continuousOn.comp (N.symm.continuousOn.mono hTtarget)
      (fun z hz => hNQ (N.map_target (hTtarget hz)))) (fun _ _ => mem_univ _)
  have hfnz : ∀ z∈T,f z≠0 := by
    intro z hz he
    have hxQ := hNQ (N.map_target (hTtarget hz))
    have hxb : N.symm z∈range b := (hQaxis _ hxQ).mpr he
    rcases hz with hz | hz
    · have hxin : N.symm z∈interior (range d) := (hNbank _ (N.map_target (hTtarget (Or.inl hz)))).mpr (by rw [N.right_inv (hTtarget (Or.inl hz))];exact hz.2.2.1)
      exact Set.disjoint_left.mp hempty hxin hxb
    · exact hz.2.2.2 hxb
  let V : Set S := N.source∩N ⁻¹' Plane.openSquare 0 1
  have hV : IsOpen V := N.isOpen_inter_preimage (Plane.isOpen_openSquare 0 1)
  have hpV : a s∈V := by
    refine ⟨hNs.symm ▸ hp,?_⟩
    change N (a s)∈Plane.openSquare 0 1
    rw [hNzero]
    exact mem_openSquare_zero_one.mpr (by change max |(0:ℝ)| |(0:ℝ)|<1;norm_num)
  have hn : a ⁻¹' V∈nhds s := (hV.preimage a.continuous).mem_nhds hpV
  obtain ⟨l₀,h₀,hs₀,hlocal⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨0,hs.1⟩ ⟨1,hs.2⟩).mp hn
  obtain ⟨l,hl₀,hls⟩ := exists_between hs₀.1
  obtain ⟨h,hsh,hhh₀⟩ := exists_between hs₀.2
  have hwin : ∀ w∈Icc l h,a w∈V := fun w hw => hlocal ⟨hl₀.trans_le hw.1,hw.2.trans_lt hhh₀⟩
  have hcoord : ∀ w∈Ioo l h,w≠s → N (a w)∈T := by
    intro w hw hws
    have hwV := hwin w ⟨hw.1.le,hw.2.le⟩
    have hwN : a w∈N.source := hwV.1
    have hbound := mem_openSquare_zero_one.mp hwV.2
    change max |N (a w) 0| |N (a w) 1|<1 at hbound
    have h0 := abs_lt.mp ((le_max_left _ _).trans_lt hbound)
    have hzero : N (a w) 1=0 := (hNz _).mpr ((hPaxis _ (hNs ▸ hwN)).mp (mem_range_self w))
    have hnb : a w∉range b := by
      intro hwb
      have he : a w=a s := Set.mem_singleton_iff.mp (hiso ▸ (show a w∈Q.source∩(range a∩range b) from ⟨hNQ hwN,mem_range_self w,hwb⟩))
      exact hws (ha.injective he)
    exact Or.inr ⟨h0.1,h0.2,hzero,by rw [N.left_inv hwN];exact hnb⟩
  rcases hTconn.mapsTo_Ioi_or_Iio hfc hfnz with hpos | hneg
  · refine ⟨l,h,-1,hls,hsh,Or.inl rfl,fun w hw => hNQ (hwin w hw).1,?_⟩
    intro w hw hws
    have hwT := hcoord w hw hws
    have hh := hpos hwT
    dsimp [f] at hh
    rw [N.left_inv (hwin w ⟨hw.1.le,hw.2.le⟩).1] at hh
    change 0<Q (a w) 1 at hh
    linarith
  · refine ⟨l,h,1,hls,hsh,Or.inr rfl,fun w hw => hNQ (hwin w hw).1,?_⟩
    intro w hw hws
    have hh := hneg (hcoord w hw hws)
    dsimp [f] at hh
    rw [N.left_inv (hwin w ⟨hw.1.le,hw.2.le⟩).1] at hh
    simpa only [one_mul,mem_Iio] using hh

theorem actual_empty_whole_graph_disk_noncorner_contact_constructs_tangency_window
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
    (x : S) (hxD : x∈range d)
    (hxA : x∈⋃ k,range (fun t:Interval => (a k t).val))
    (hxB : x∈⋃ k,range (fun t:Interval => (b k t).val))
    (hxcorner : x∉({q 0,q 1} : Set S)) :
    ∃ (k : I) (r : J) (s t l h : Interval)
      (Q : OpenPartialHomeomorph S Plane) (ε : ℝ),
      s∈Ioo (0:Interval) 1 ∧ t∈Ioo (0:Interval) 1 ∧
      (a k s).val=x ∧ (b r t).val=x ∧
      l<s ∧ s<h ∧ (ε=(-1:ℝ) ∨ ε=1) ∧
      x∈Q.source ∧ Q x 1=0 ∧ Q.source⊆interior F ∧
      (∀ y:↥F,y.val∈Q.source → (y∈range (b r) ↔ Q y.val 1=0)) ∧
      (∀ k',k'≠k → ∀ y∈range (a k'),y.val∉Q.source) ∧
      (∀ r',r'≠r → ∀ y∈range (b r'),y.val∉Q.source) ∧
      (∀ w∈Icc l h,(a k w).val∈Q.source) ∧
      (∀ w∈Ioo l h,w≠s → ε*(Q ((a k w).val)) 1<0) := by
  classical
  let av : I → C(Interval,S) := fun k => ⟨fun t => (a k t).val,continuous_subtype_val.comp (a k).continuous⟩
  let bv : J → C(Interval,S) := fun k => ⟨fun t => (b k t).val,continuous_subtype_val.comp (b k).continuous⟩
  have haemb : ∀ k,IsEmbedding (av k) := fun k => IsEmbedding.subtypeVal.comp (ha k)
  have hbemb : ∀ k,IsEmbedding (bv k) := fun k => IsEmbedding.subtypeVal.comp (hb k)
  have had : ∀ k m,k≠m → Disjoint (range (av k)) (range (av m)) := by
    intro k m hkm
    apply Set.disjoint_left.mpr
    rintro y ⟨u,hu⟩ ⟨v,hv⟩
    have he : a k u=a m v := Subtype.ext (hu.trans hv.symm)
    exact Set.disjoint_left.mp (hadisjoint k m hkm) (mem_range_self u) ⟨v,he.symm⟩
  have hbd : ∀ k m,k≠m → Disjoint (range (bv k)) (range (bv m)) := by
    intro k m hkm
    apply Set.disjoint_left.mpr
    rintro y ⟨u,hu⟩ ⟨v,hv⟩
    have he : b k u=b m v := Subtype.ext (hu.trans hv.symm)
    exact Set.disjoint_left.mp (hbdisjoint k m hkm) (mem_range_self u) ⟨v,he.symm⟩
  have hfin : ((⋃ k,range (av k))∩⋃ k,range (bv k)).Finite := by
    apply (hfinite.image (fun y:↥F => y.val)).subset
    rintro y ⟨hyA,hyB⟩
    obtain ⟨k,u,hu⟩ := mem_iUnion.mp hyA
    obtain ⟨m,v,hv⟩ := mem_iUnion.mp hyB
    refine ⟨a k u,⟨mem_iUnion.mpr ⟨k,mem_range_self u⟩,?_⟩,hu⟩
    exact mem_iUnion.mpr ⟨m,⟨v,Subtype.ext (hv.trans hu.symm)⟩⟩
  have hgInternalClear : ∀ w∈Ioo (0:Interval) 1,g w∉frontier F := by
    intro w hw hFront
    obtain ⟨z,hz⟩ := hgb (mem_range_self w)
    have hzEnd : z=0 ∨ z=1 := by
      by_cases hz0 : z=0
      · exact Or.inl hz0
      by_cases hz1 : z=1
      · exact Or.inr hz1
      exact (hbClear j z
        ⟨lt_of_le_of_ne z.property.1 (Ne.symm hz0),lt_of_le_of_ne z.property.2 hz1⟩
        (by have hz' := hz; change (b j z).val=g w at hz';rw [hz'];exact hFront)).elim
    have he : g w=bv j 0 ∨ g w=bv j 1 := by
      rcases hzEnd with rfl | rfl
      · exact Or.inl hz.symm
      · exact Or.inr hz.symm
    have hwEnd := CurveComplex.HyperellipticModel.actual_embedded_side_source_endpoint
      (bv j) g (hbemb j) hg hgb w he
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
      exact (haClear i z
        ⟨lt_of_le_of_ne z.property.1 (Ne.symm hz0),lt_of_le_of_ne z.property.2 hz1⟩
        (by have hz' := hz; change (a i z).val=q w at hz';rw [hz'];exact hFront)).elim
    have he : q w=av i 0 ∨ q w=av i 1 := by
      rcases hzEnd with rfl | rfl
      · exact Or.inl hz.symm
      · exact Or.inr hz.symm
    have hwEnd := CurveComplex.HyperellipticModel.actual_embedded_side_source_endpoint
      (av i) q (haemb i) hq hqa w he
    rcases hwEnd with rfl | rfl
    · exact (lt_irrefl (0:Interval)) hw.1
    · exact (lt_irrefl (1:Interval)) hw.2
  have hdClear : Disjoint (interior (range d)) ((⋃ k,range (av k))∪⋃ k,range (bv k)) := by
    rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd]
    exact hempty
  have hxNotInt : x∉interior (range d) := fun hx => Set.disjoint_left.mp hdClear hx (Or.inl hxA)
  have hxBoundary : x∈range q∪range g := by
    rw [←hboundary,←embedded_surface_disk_frontier_eq_boundary_image d hd,
      (isCompact_range d.continuous).isClosed.frontier_eq]
    exact ⟨hxD,hxNotInt⟩
  have hxNotFront : x∉frontier F := by
    rcases hxBoundary with ⟨w,hw⟩ | ⟨w,hw⟩
    · have hw0 : w≠0 := by intro he;exact hxcorner (Or.inl (hw.symm.trans (congrArg q he)))
      have hw1 : w≠1 := by intro he;exact hxcorner (Or.inr (hw.symm.trans (congrArg q he)))
      exact hw ▸ hqInternalClear w ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
    · have hw0 : w≠0 := by intro he;exact hxcorner (Or.inl ((hw.symm.trans (congrArg g he)).trans hzero.symm))
      have hw1 : w≠1 := by intro he;exact hxcorner (Or.inr ((hw.symm.trans (congrArg g he)).trans hone.symm))
      exact hw ▸ hgInternalClear w ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
  obtain ⟨k,s,hsx⟩ := mem_iUnion.mp hxA
  obtain ⟨r,t,htx⟩ := mem_iUnion.mp hxB
  change (a k s).val=x at hsx
  change (b r t).val=x at htx
  have hasx : av k s=x := hsx
  have hbtx : bv r t=x := htx
  have hs0 : s≠0 := by intro he;exact hxNotFront (hsx ▸ he ▸ ha0 k)
  have hs1 : s≠1 := by intro he;exact hxNotFront (hsx ▸ he ▸ ha1 k)
  have ht0 : t≠0 := by intro he;exact hxNotFront (htx ▸ he ▸ hb0 r)
  have ht1 : t≠1 := by intro he;exact hxNotFront (htx ▸ he ▸ hb1 r)
  have hs : s∈Ioo (0:Interval) 1 := ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),lt_of_le_of_ne s.property.2 hs1⟩
  have ht : t∈Ioo (0:Interval) 1 := ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
  obtain ⟨U,hU,hxU,hUF,hUa,hUb,hiso⟩ :=
    ActualHarerWholeGraph.actual_finite_whole_graph_genuine_contact_constructs_isolated_clear_open_neighborhood
      av bv had hbd hfin F k r x ⟨s,hsx⟩ ⟨t,htx⟩ (hdF hxD) hxNotFront
  obtain ⟨Q,hpQ,hQU,hQp,_,haxis,_⟩ :=
    ActualHarerWholeAnchorRail.actual_disjoint_whole_moving_family_constructs_local_exact_axis_chart
      bv hbemb hbd r t ht U hU (by change (b r t).val∈U;rw [htx];exact hxU)
  have hxQ : x∈Q.source := hbtx ▸ hpQ
  have hQzero : Q x 1=0 := (haxis x hxQ).mp ⟨t,hbtx⟩
  have hpQa : av k s∈Q.source := hasx.symm ▸ hxQ
  have hpair : Q.source∩(range (av k)∩range (bv r))={av k s} := by
    ext y
    constructor
    · rintro ⟨hyQ,hyA,hyB⟩
      have hymem : y∈U∩((⋃ m,range (av m))∩⋃ m,range (bv m)) :=
        ⟨hQU hyQ,mem_iUnion.mpr ⟨k,hyA⟩,mem_iUnion.mpr ⟨r,hyB⟩⟩
      rw [hiso] at hymem
      exact hymem.trans hsx.symm
    · intro hy
      have he : y=av k s := hy
      subst y
      exact ⟨hpQa,mem_range_self s,⟨t,htx.trans hsx.symm⟩⟩
  have hsides := actual_disk_boundary_sides_intersection q g hq hg hzero hone d hd hboundary
  have hwindows : ∃ (M : OpenPartialHomeomorph S Plane) (ε : ℝ) (l h : Interval),
      x∈M.source ∧ M x 1=0 ∧ M.source⊆U ∧
      (∀ y∈M.source,y∈range (bv r) ↔ M y 1=0) ∧
      l<s ∧ s<h ∧ (ε=(-1:ℝ) ∨ ε=1) ∧
      (∀ w∈Icc l h,av k w∈M.source) ∧
      (∀ w∈Ioo l h,w≠s → ε*M (av k w) 1<0) := by
    rcases hxBoundary with hxq | hxg
    · obtain ⟨w,hw⟩ := hxq
      have hw0 : w≠0 := by intro he;exact hxcorner (Or.inl (hw.symm.trans (congrArg q he)))
      have hw1 : w≠1 := by intro he;exact hxcorner (Or.inr (hw.symm.trans (congrArg q he)))
      have hwInt : w∈Ioo (0:Interval) 1 := ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
      have hxgNot : x∉range g := by intro hgx;exact hxcorner (hsides ▸ ⟨⟨w,hw⟩,hgx⟩)
      have hki : k=i := by
        by_contra hne
        exact Set.disjoint_left.mp (had k i hne) ⟨s,hsx⟩ (hqa ⟨w,hw⟩)
      have hqk : range q⊆range (av k) := hki.symm ▸ hqa
      obtain ⟨R,hpR,hRQ,_,_,hRaxis,_⟩ :=
        ActualHarerWholeAnchorRail.actual_disjoint_whole_moving_family_constructs_local_exact_axis_chart
          av haemb had k s hs Q.source Q.open_source hpQa
      obtain ⟨P,hpP,hP0,hPR,hPaxis,hBank⟩ :=
        actual_noncorner_disk_side_constructs_whole_arc_axis_interior_bank_chart
          (av k) q g (haemb k) hq hqk d hd hboundary w hwInt (hw.symm ▸ hxgNot) R
          (by rw [hw,←hasx];exact hpR) hRaxis
      have hPsrc : P.source⊆Q.source := hPR.trans hRQ
      have hBP : Disjoint (interior (range d)) (range (bv r)) :=
        hdClear.mono_right (fun _ hy => Or.inr (mem_iUnion.mpr ⟨r,hy⟩))
      obtain ⟨l,h,ε,hls,hsh,hε,hwin,hside⟩ :=
        actual_empty_bank_constructs_moving_axis_same_side_window
          (av k) (bv r) (haemb k) s hs d hBP Q P
          (by rw [hasx,←hw];exact hpP)
          (by rw [hasx,←hw];exact hP0)
          hPsrc hPaxis hBank haxis hpair
      exact ⟨Q,ε,l,h,hxQ,hQzero,hQU,haxis,hls,hsh,hε,hwin,hside⟩
    · obtain ⟨w,hw⟩ := hxg
      have hw0 : w≠0 := by intro he;exact hxcorner (Or.inl ((hw.symm.trans (congrArg g he)).trans hzero.symm))
      have hw1 : w≠1 := by intro he;exact hxcorner (Or.inr ((hw.symm.trans (congrArg g he)).trans hone.symm))
      have hwInt : w∈Ioo (0:Interval) 1 := ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
      have hxqNot : x∉range q := by intro hqx;exact hxcorner (hsides ▸ ⟨hqx,⟨w,hw⟩⟩)
      have hrj : r=j := by
        by_contra hne
        exact Set.disjoint_left.mp (hbd r j hne) ⟨t,htx⟩ (hgb ⟨w,hw⟩)
      have hgr : range g⊆range (bv r) := hrj.symm ▸ hgb
      have hbdy : d '' {z | z.val∈Metric.sphere (0:Plane) 1}=range g∪range q := hboundary.trans (union_comm _ _)
      obtain ⟨P,hpP,hP0,hPQ,hPaxis,hBank⟩ :=
        actual_noncorner_disk_side_constructs_whole_arc_axis_interior_bank_chart
          (bv r) g q (hbemb r) hg hgr d hd hbdy w hwInt (hw.symm ▸ hxqNot) Q
          (by rw [hw];exact hxQ) haxis
      have hxP : x∈P.source := hw ▸ hpP
      have hPzero : P x 1=0 := by rw [←hw,hP0];rfl
      have hpAP : av k s∈P.source := hasx.symm ▸ hxP
      have hpairP : P.source∩(range (av k)∩range (bv r))={av k s} := by
        apply subset_antisymm
        · intro y hy
          exact hpair ▸ ⟨hPQ hy.1,hy.2⟩
        · rintro y rfl
          exact ⟨hpAP,mem_range_self s,⟨t,htx.trans hsx.symm⟩⟩
      obtain ⟨l,h,hls,hsh,hwin,_,_⟩ :=
        ActualHarerContactSides.actual_isolated_whole_trace_contact_constructs_two_signed_branch_windows
          (av k) (bv r) (haemb k) P hPaxis s hs hpAP hpairP
      refine ⟨P,1,l,h,hxP,hPzero,hPQ.trans hQU,hPaxis,hls,hsh,Or.inr rfl,hwin,?_⟩
      intro u hu hus
      have huP := hwin u ⟨hu.1.le,hu.2.le⟩
      have hnotB : av k u∉range (bv r) := by
        intro huB
        have he : av k u=av k s := Set.mem_singleton_iff.mp (hpairP ▸ ⟨huP,mem_range_self u,huB⟩)
        exact hus ((haemb k).injective he)
      have hne : P (av k u) 1≠0 := fun he => hnotB ((hPaxis _ huP).mpr he)
      have hle : P (av k u) 1≤0 := by
        by_contra hn
        have hin := (hBank _ huP).mpr (lt_of_not_ge hn)
        exact Set.disjoint_left.mp hdClear hin (Or.inl (mem_iUnion.mpr ⟨k,mem_range_self u⟩))
      simpa only [one_mul] using lt_of_le_of_ne hle hne
  obtain ⟨M,ε,l,h,hxM,hMz,hMU,hMaxis,hls,hsh,hε,hwin,hside⟩ := hwindows
  refine ⟨k,r,s,t,l,h,M,ε,hs,ht,hsx,htx,hls,hsh,hε,hxM,hMz,hMU.trans hUF,?_,?_,?_,hwin,hside⟩
  · intro y hy
    have he : y∈range (b r) ↔ y.val∈range (bv r) := by
      constructor
      · rintro ⟨u,rfl⟩;exact mem_range_self u
      · rintro ⟨u,hu⟩;exact ⟨u,Subtype.ext hu⟩
    exact he.trans (hMaxis y.val hy)
  · intro k' hne y hy hyM
    obtain ⟨u,rfl⟩ := hy
    exact Set.disjoint_left.mp (hUa k' hne) (hMU hyM) (mem_range_self u)
  · intro r' hne y hy hyM
    obtain ⟨u,rfl⟩ := hy
    exact Set.disjoint_left.mp (hUb r' hne) (hMU hyM) (mem_range_self u)

end ActualHarerSupportedBypass
