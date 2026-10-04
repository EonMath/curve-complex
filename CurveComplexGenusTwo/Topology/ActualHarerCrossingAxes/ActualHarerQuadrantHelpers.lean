import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerCornerGeometryDefinitions
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.VerifiedCarrierBridgeComponents
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import Mathlib.Topology.Order.IntermediateValue

open CurveComplex Set Topology Schoenflies
namespace ActualHarerCornerGeometry
set_option maxHeartbeats 2000000

theorem embedded_subarc_parameter_interval {S : Type} [TopologicalSpace S]
    (f q : C(Interval,S)) (hf : IsEmbedding f) (hq : IsEmbedding q)
    (hsub : range q ⊆ range f) (s₀ s₁ : Interval)
    (h₀ : f s₀ = q 0) (h₁ : f s₁ = q 1) :
    s₀ ≠ s₁ ∧ range q = f '' uIcc s₀ s₁ := by
  let G : C(Interval,range f) := ⟨fun z => ⟨q z,hsub (mem_range_self z)⟩,
    q.continuous.subtype_mk _⟩
  let k : Interval → Interval := hf.toHomeomorph.symm ∘ G
  have hk : Continuous k := hf.toHomeomorph.symm.continuous.comp G.continuous
  have hfk (z : Interval) : f (k z) = q z :=
    congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply (G z))
  have hki : Function.Injective k := by
    intro z w he
    apply hq.injective
    rw [←hfk z,←hfk w,he]
  have hk₀ : k 0 = s₀ := hf.injective ((hfk 0).trans h₀.symm)
  have hk₁ : k 1 = s₁ := hf.injective ((hfk 1).trans h₁.symm)
  have hkrange : range k = uIcc (k 0) (k 1) := by
    have hUniv : (univ:Set Interval) = Icc (0:Interval) 1 := by
      ext z
      simp only [mem_univ,mem_Icc,true_iff]
      exact z.property
    rw [←image_univ,hUniv]
    rcases hk.strictMono_of_inj_boundedOrder' hki with hm | hm
    · rw [hk.continuousOn.image_Icc_of_monotoneOn zero_le_one (hm.monotone.monotoneOn _)]
      exact (uIcc_of_le (hm zero_lt_one).le).symm
    · rw [hk.continuousOn.image_Icc_of_antitoneOn zero_le_one (hm.antitone.antitoneOn _)]
      exact (uIcc_of_ge (hm zero_lt_one).le).symm
  refine ⟨fun he => zero_ne_one (hq.injective (h₀.symm.trans ((congrArg f he).trans h₁))),?_⟩
  rw [←hk₀,←hk₁,←hkrange]
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨k z,mem_range_self z,hfk z⟩
  · rintro ⟨z,⟨w,hw⟩,hx⟩
    exact ⟨w,(hfk w).symm.trans ((congrArg f hw).trans hx)⟩

theorem endpoint_ordered_subarc_germ {S : Type} [TopologicalSpace S] [T2Space S]
    (f q : C(Interval,S)) (hf : IsEmbedding f) (hq : IsEmbedding q)
    (hsub : range q ⊆ range f) (s₀ s₁ : Interval)
    (h₀ : f s₀ = q 0) (h₁ : f s₁ = q 1)
    (v : Interval) (hv : v = 0 ∨ v = 1)
    (E : OpenPartialHomeomorph S Plane) (j k : Fin 2)
    (haxis : ∀ x ∈ E.source, x ∈ range f ↔ E x k = 0)
    (hp : f (endpointParameter v s₀ s₁) ∈ E.source)
    (horder : ∀ u, f u ∈ E.source →
      (E (f u) j < 0 ↔ u < endpointParameter v s₀ s₁) ∧
      (0 < E (f u) j ↔ endpointParameter v s₀ s₁ < u)) :
    ∃ W : Set S, IsOpen W ∧ q v ∈ W ∧ W ⊆ E.source ∧
      ∀ x ∈ W, x ∈ range q ↔ E x k = 0 ∧ 0 ≤ inwardParameterSign v s₀ s₁ * E x j := by
  classical
  obtain ⟨hne,hrange⟩ := embedded_subarc_parameter_interval f q hf hq hsub s₀ s₁ h₀ h₁
  let c := endpointParameter v s₀ s₁
  let o := if v = 0 then s₁ else s₀
  have hco : c ≠ o := by
    rcases hv with rfl|rfl
    · simpa [c,o,endpointParameter] using hne
    · simpa [c,o,endpointParameter] using hne.symm
  have hfc : f c = q v := by
    rcases hv with rfl|rfl
    · simpa [c,endpointParameter] using h₀
    · simpa [c,endpointParameter] using h₁
  have hrange' : range q = f '' uIcc c o := by
    rcases hv with rfl|rfl
    · simpa [c,o,endpointParameter] using hrange
    · simpa [c,o,endpointParameter,uIcc_comm] using hrange
  have hsign : inwardParameterSign v s₀ s₁ = if c < o then 1 else -1 := by
    rcases hv with rfl|rfl <;> simp [c,o,endpointParameter,inwardParameterSign]
  let K : Set S := f '' (if c < o then Ici o else Iic o)
  have hK : IsClosed K := by
    dsimp [K]
    split_ifs
    · exact (isClosed_Ici.isCompact.image f.continuous).isClosed
    · exact (isClosed_Iic.isCompact.image f.continuous).isClosed
  have hpc : f c ∉ K := by
    rintro ⟨u,hu,he⟩
    have heq := hf.injective he
    subst u
    split_ifs at hu with h
    · exact not_le_of_gt h hu
    · exact hco (le_antisymm hu (le_of_not_gt h))
  let W := E.source \ K
  refine ⟨W,E.open_source.sdiff hK,hfc ▸ ⟨hp,hpc⟩,fun x hx => hx.1,?_⟩
  intro x hx
  rw [hrange',hsign]
  constructor
  · rintro ⟨u,hu,rfl⟩
    refine ⟨(haxis _ hx.1).mp (mem_range_self u),?_⟩
    have hh := horder u hx.1
    by_cases hco' : c < o
    · rw [if_pos hco',one_mul]
      have hu' := (uIcc_of_le hco'.le ▸ hu).1
      exact le_of_not_gt (fun hneg => not_lt_of_ge hu' (hh.1.mp hneg))
    · rw [if_neg hco',neg_one_mul]
      have hu' := (uIcc_of_ge (le_of_not_gt hco') ▸ hu).2
      exact neg_nonneg.mpr (le_of_not_gt (fun hpos => not_lt_of_ge hu' (hh.2.mp hpos)))
  · rintro ⟨hax,hsgn⟩
    obtain ⟨u,rfl⟩ := (haxis _ hx.1).mpr hax
    refine ⟨u,?_,rfl⟩
    have hh := horder u hx.1
    by_cases hco' : c < o
    · rw [uIcc_of_le hco'.le]
      rw [if_pos hco',one_mul] at hsgn
      refine ⟨le_of_not_gt (fun hlt => not_lt_of_ge hsgn (hh.1.mpr hlt)),?_⟩
      have hnot : ¬ o ≤ u := by intro hu; exact hx.2 ⟨u,by simpa [K,hco'] using hu,rfl⟩
      exact (lt_of_not_ge hnot).le
    · rw [uIcc_of_ge (le_of_not_gt hco')]
      rw [if_neg hco',neg_one_mul] at hsgn
      refine ⟨?_,le_of_not_gt (fun hlt => by have hh' := hh.2.mpr hlt; linarith)⟩
      have hnot : ¬ u ≤ o := by intro hu; exact hx.2 ⟨u,by simpa [K,hco'] using hu,rfl⟩
      exact (lt_of_not_ge hnot).le

end ActualHarerCornerGeometry

namespace ActualHarerCornerGeometry

theorem positive_corner_closed_regular_set {S : Type*} [TopologicalSpace S]
    (E : OpenPartialHomeomorph S Plane) (D : Set S) (hD : IsClosed D)
    (hregular : D ⊆ closure (interior D)) (r : ℝ) (hr : 0 < r)
    (hTarget : ∀ z : Plane, |z 0| < r → |z 1| < r → z ∈ E.target)
    (hFrontier : ∀ z : Plane, |z 0| < r → |z 1| < r →
      (E.symm z ∈ frontier D ↔ (z 1 = 0 ∧ 0 ≤ z 0) ∨ (z 0 = 0 ∧ 0 ≤ z 1)))
    (hNegative : E.symm (Plane.mk (-r/2) 0) ∉ D) :
    ∀ z : Plane, |z 0| < r → |z 1| < r →
      (E.symm z ∈ D ↔ 0 ≤ z 0 ∧ 0 ≤ z 1) := by
  let rect : Set Plane := {z | |z 0| < r ∧ |z 1| < r}
  have hrect : rect = Plane.openSquare 0 r := by
    ext z
    simp [rect,Plane.openSquare,Plane.supDist,Plane.supNorm,max_lt_iff]
  have hrectOpen : IsOpen rect := hrect ▸ Plane.isOpen_openSquare 0 r
  have hrectConv : Convex ℝ rect := hrect ▸ Plane.convex_openSquare 0 r
  have hrectT : rect ⊆ E.target := fun z hz => hTarget z hz.1 hz.2
  let pos : Set Plane := rect ∩ ({z | 0 < z 0} ∩ {z | 0 < z 1})
  let negX : Set Plane := rect ∩ {z | z 0 < 0}
  let negY : Set Plane := rect ∩ {z | z 1 < 0}
  let neg : Set Plane := negX ∪ negY
  have hPosConn : IsPreconnected pos :=
    (hrectConv.inter ((Plane.convex_coord_gt 0 0).inter (Plane.convex_coord_gt 1 0))).isPreconnected
  have hNXConn : IsPreconnected negX := (hrectConv.inter (Plane.convex_coord_lt 0 0)).isPreconnected
  have hNYConn : IsPreconnected negY := (hrectConv.inter (Plane.convex_coord_lt 1 0)).isPreconnected
  have hnSample : |(-r/2)| < r := by rw [abs_of_neg (by linarith)]; linarith
  have hNegConn : IsPreconnected neg := hNXConn.union (Plane.mk (-r/2) (-r/2))
    ⟨⟨hnSample,hnSample⟩,by change -r/2 < 0; linarith⟩
    ⟨⟨hnSample,hnSample⟩,by change -r/2 < 0; linarith⟩ hNYConn
  have hNegRect : neg ⊆ rect := fun z hz => hz.elim And.left And.left
  let P := E.symm '' pos
  let N := E.symm '' neg
  have hPConn : IsPreconnected P := hPosConn.image E.symm
    (E.symm.continuousOn.mono (inter_subset_left.trans hrectT))
  have hNConn : IsPreconnected N := hNegConn.image E.symm
    (E.symm.continuousOn.mono (hNegRect.trans hrectT))
  have hPAvoid : Disjoint P (frontier D) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hx
    rcases (hFrontier z hz.1.1 hz.1.2).mp hx with hx|hx
    · exact ne_of_gt hz.2.2 hx.1
    · exact ne_of_gt hz.2.1 hx.1
  have hNAvoid : Disjoint N (frontier D) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hx
    have hzR := hNegRect hz
    have hh := (hFrontier z hzR.1 hzR.2).mp hx
    rcases hz with hz|hz <;> rcases hh with hh|hh
    · exact not_le_of_gt hz.2 hh.2
    · exact ne_of_lt hz.2 hh.1
    · exact ne_of_lt hz.2 hh.1
    · exact not_le_of_gt hz.2 hh.2
  have hClassify (C : Set S) (hc : IsPreconnected C) (ha : Disjoint C (frontier D)) :
      C ⊆ interior D ∨ C ⊆ Dᶜ := by
    have hcover : C ⊆ interior D ∪ Dᶜ := by
      intro x hx
      by_cases hxD : x ∈ D
      · left
        by_contra hn
        exact disjoint_left.mp ha hx (hD.frontier_eq ▸ ⟨hxD,hn⟩)
      · exact Or.inr hxD
    exact hc.subset_or_subset isOpen_interior hD.isOpen_compl
      (disjoint_left.mpr (fun x hx hn => hn (interior_subset hx))) hcover
  have hNOut : N ⊆ Dᶜ := by
    rcases hClassify N hNConn hNAvoid with hin|hout
    · have hs : E.symm (Plane.mk (-r/2) 0) ∈ N :=
        ⟨_,Or.inl ⟨⟨hnSample,by simpa using hr⟩,by change -r/2 < 0; linarith⟩,rfl⟩
      exact (hNegative (interior_subset (hin hs))).elim
    · exact hout
  have hcenterF : E.symm 0 ∈ frontier D :=
    (hFrontier 0 (by simpa using hr) (by simpa using hr)).mpr (Or.inl ⟨rfl,le_rfl⟩)
  let O := E.symm '' rect
  have hO : IsOpen O := E.symm.isOpen_image_of_subset_source hrectOpen hrectT
  have hpO : E.symm 0 ∈ O := ⟨0,⟨by simpa using hr,by simpa using hr⟩,rfl⟩
  have hinside : (O ∩ interior D).Nonempty :=
    mem_closure_iff_nhds.mp (hregular (hD.frontier_subset hcenterF)) _ (hO.mem_nhds hpO)
  have hPIn : P ⊆ interior D := by
    rcases hClassify P hPConn hPAvoid with hin|hout
    · exact hin
    · obtain ⟨x,⟨z,hz,rfl⟩,hzi⟩ := hinside
      have hzx : 0 ≤ z 0 := le_of_not_gt (fun hneg =>
        hNOut ⟨z,Or.inl ⟨hz,hneg⟩,rfl⟩ (interior_subset hzi))
      have hzy : 0 ≤ z 1 := le_of_not_gt (fun hneg =>
        hNOut ⟨z,Or.inr ⟨hz,hneg⟩,rfl⟩ (interior_subset hzi))
      have hnfront : E.symm z ∉ frontier D := by
        intro hh
        exact (hD.frontier_eq ▸ hh).2 hzi
      have hzx0 : z 0 ≠ 0 := fun he => hnfront ((hFrontier z hz.1 hz.2).mpr (Or.inr ⟨he,hzy⟩))
      have hzy0 : z 1 ≠ 0 := fun he => hnfront ((hFrontier z hz.1 hz.2).mpr (Or.inl ⟨he,hzx⟩))
      have hp : E.symm z ∈ P := ⟨z,⟨hz,lt_of_le_of_ne hzx (Ne.symm hzx0),lt_of_le_of_ne hzy (Ne.symm hzy0)⟩,rfl⟩
      exact (hout hp (interior_subset hzi)).elim
  intro z hz₀ hz₁
  constructor
  · intro hzD
    exact ⟨le_of_not_gt (fun hneg => hNOut ⟨z,Or.inl ⟨⟨hz₀,hz₁⟩,hneg⟩,rfl⟩ hzD),
      le_of_not_gt (fun hneg => hNOut ⟨z,Or.inr ⟨⟨hz₀,hz₁⟩,hneg⟩,rfl⟩ hzD)⟩
  · rintro ⟨hx,hy⟩
    by_cases hx0 : z 0 = 0
    · exact hD.frontier_subset ((hFrontier z hz₀ hz₁).mpr (Or.inr ⟨hx0,hy⟩))
    by_cases hy0 : z 1 = 0
    · exact hD.frontier_subset ((hFrontier z hz₀ hz₁).mpr (Or.inl ⟨hy0,hx⟩))
    exact interior_subset (hPIn ⟨z,⟨⟨hz₀,hz₁⟩,lt_of_le_of_ne hx (Ne.symm hx0),
      lt_of_le_of_ne hy (Ne.symm hy0)⟩,rfl⟩)

end ActualHarerCornerGeometry

namespace ActualHarerCornerGeometry

noncomputable def signedPlaneHomeomorph (σ τ : ℝ)
    (hσ : σ = -1 ∨ σ = 1) (hτ : τ = -1 ∨ τ = 1) : Plane ≃ₜ Plane where
  toEquiv := {
    toFun := fun z => Plane.mk (σ*z 0) (τ*z 1)
    invFun := fun z => Plane.mk (σ*z 0) (τ*z 1)
    left_inv := by
      intro z
      ext j
      fin_cases j
      · rcases hσ with rfl|rfl <;> simp
      · rcases hτ with rfl|rfl <;> simp
    right_inv := by
      intro z
      ext j
      fin_cases j
      · rcases hσ with rfl|rfl <;> simp
      · rcases hτ with rfl|rfl <;> simp }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem small_closed_square_in_open (W : Set Plane) (hW : IsOpen W) (h0 : (0:Plane) ∈ W) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ Plane.closedSquare 0 r ⊆ W := by
  obtain ⟨ε,hε,hεW⟩ := Metric.isOpen_iff.mp hW 0 h0
  let r := min 1 (ε/4)
  have hr : 0 < r := lt_min zero_lt_one (by positivity)
  refine ⟨r,hr,min_le_left _ _,?_⟩
  intro z hz
  apply hεW
  rw [Metric.mem_ball,dist_zero_right]
  have hzS : Plane.supNorm z ≤ r := by simpa [Plane.closedSquare,Plane.supDist] using hz
  have hnorm := Plane.norm_le_sqrt_two_mul_supNorm z
  have hsqrt : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg 2]
  have hbound : Real.sqrt 2 * Plane.supNorm z ≤ 2*r :=
    mul_le_mul hsqrt hzS (Plane.supNorm_nonneg z) (by norm_num)
  have hrr : r ≤ ε/4 := min_le_right _ _
  linarith

theorem signed_corner_closed_regular_set {S : Type*} [TopologicalSpace S]
    (E : OpenPartialHomeomorph S Plane) (D : Set S) (hD : IsClosed D)
    (hregular : D ⊆ closure (interior D)) (r σ τ : ℝ) (hr : 0 < r)
    (hσ : σ = -1 ∨ σ = 1) (hτ : τ = -1 ∨ τ = 1)
    (hTarget : ∀ z : Plane, |z 0| < r → |z 1| < r → z ∈ E.target)
    (hFrontier : ∀ z : Plane, |z 0| < r → |z 1| < r →
      (E.symm z ∈ frontier D ↔ (z 1 = 0 ∧ 0 ≤ σ*z 0) ∨ (z 0 = 0 ∧ 0 ≤ τ*z 1)))
    (hNegative : E.symm (Plane.mk (σ*(-r/2)) 0) ∉ D) :
    ∀ z : Plane, |z 0| < r → |z 1| < r →
      (E.symm z ∈ D ↔ 0 ≤ σ*z 0 ∧ 0 ≤ τ*z 1) := by
  let L := signedPlaneHomeomorph σ τ hσ hτ
  let F := E.trans L.toOpenPartialHomeomorph
  have hσsq : σ*σ = 1 := by rcases hσ with rfl|rfl <;> norm_num
  have hτsq : τ*τ = 1 := by rcases hτ with rfl|rfl <;> norm_num
  have hσne : σ ≠ 0 := by rcases hσ with rfl|rfl <;> norm_num
  have hτne : τ ≠ 0 := by rcases hτ with rfl|rfl <;> norm_num
  have hL (z : Plane) : L.symm z = Plane.mk (σ*z 0) (τ*z 1) := rfl
  have hσabs (x : ℝ) : |σ*x| = |x| := by rcases hσ with rfl|rfl <;> simp
  have hτabs (x : ℝ) : |τ*x| = |x| := by rcases hτ with rfl|rfl <;> simp
  have hFT (z : Plane) (hx : |z 0| < r) (hy : |z 1| < r) : z ∈ F.target := by
    change z ∈ univ ∧ L.symm z ∈ E.target
    refine ⟨mem_univ _,hTarget (L.symm z) ?_ ?_⟩
    · simpa [hL,hσabs] using hx
    · simpa [hL,hτabs] using hy
  have hFF (z : Plane) (hx : |z 0| < r) (hy : |z 1| < r) :
      F.symm z ∈ frontier D ↔ (z 1 = 0 ∧ 0 ≤ z 0) ∨ (z 0 = 0 ∧ 0 ≤ z 1) := by
    have hh := hFrontier (L.symm z) (by simpa [hL,hσabs] using hx) (by simpa [hL,hτabs] using hy)
    change E.symm (L.symm z) ∈ frontier D ↔ _
    simpa [hL,←mul_assoc,hσsq,hτsq,hσne,hτne] using hh
  have hFN : F.symm (Plane.mk (-r/2) 0) ∉ D := by
    change E.symm (L.symm (Plane.mk (-r/2) 0)) ∉ D
    simpa [hL] using hNegative
  have hh := positive_corner_closed_regular_set F D hD hregular r hr hFT hFF hFN
  intro z hx hy
  have hhz := hh (L z) (by change |σ*z 0| < r; rwa [hσabs]) (by change |τ*z 1| < r; rwa [hτabs])
  change E.symm (L.symm (L z)) ∈ D ↔ _ at hhz
  rw [L.symm_apply_apply] at hhz
  exact hhz

end ActualHarerCornerGeometry

namespace ActualHarerCornerGeometry

theorem embedded_disk_frontier_image
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

end ActualHarerCornerGeometry
