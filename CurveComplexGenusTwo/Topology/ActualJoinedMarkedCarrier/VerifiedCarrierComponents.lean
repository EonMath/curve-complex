import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualEmbeddedLocalLineTools
import CurveComplexGenusTwo.Topology.Smoothing.ActualGermArcs
import Mathlib.Topology.Order.IntermediateValue
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem selected_disk_intersection
    {S : Type} [TopologicalSpace S]
    (A : Set S) (u z : S) (f g : C(Interval,S))
    (hf0 : f 0 = u) (hf1 : f 1 = z) (hfA : Set.range f ⊆ A)
    (hgA : Set.range g ∩ A = {u,z})
    (d : C(Metric.closedBall (0 : Plane) 1,S))
    (hb : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = Set.range f ∪ Set.range g)
    (he : Disjoint (d '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) A) :
    Set.range d ∩ A = Set.range f := by
  ext x
  constructor
  · rintro ⟨⟨a,rfl⟩,haA⟩
    have ha : dist a.val (0 : Plane) ≤ 1 := a.property
    have has : dist a.val (0 : Plane) = 1 := by
      apply le_antisymm ha
      by_contra hn
      have hai : a ∈ {x : Metric.closedBall (0 : Plane) 1 | x.val ∈ Metric.ball (0 : Plane) 1} :=
        lt_of_not_ge hn
      exact Set.disjoint_left.mp he ⟨a,hai,rfl⟩ haA
    have hab : d a ∈ d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := ⟨a,has,rfl⟩
    rw [hb] at hab
    rcases hab with hfa | hga
    · exact hfa
    · have hc : d a ∈ ({u,z} : Set S) := hgA ▸ ⟨hga,haA⟩
      rcases hc with hc | hc
      · exact ⟨0,hf0.trans hc.symm⟩
      · exact ⟨1,hf1.trans hc.symm⟩
  · intro hx
    exact ⟨Set.image_subset_range _ _ (hb.symm ▸ (show x ∈ range f ∪ range g from Or.inl hx)),hfA hx⟩

theorem actual_marked_disk_remainder_support
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (htab : ∀ p ∈ ArcSurgery.crossings M a b, ArcSurgery.CrossesInDisk M a b p)
    (B : ActualMarkedTwoSideDisk M a b)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image))
    (Kraw : Set S) (hdecompRaw : a.val.image = range B.firstSide ∪ Kraw)
    (hmeetRaw : range B.firstSide ∩ Kraw = ({B.firstCorner,B.secondCorner} : Set S)) :
    range B.disk ∩ Kraw = ({B.firstCorner,B.secondCorner} : Set S) := by
  classical
  let Bswap : ActualMarkedTwoSideDisk M b a := {
    firstCorner := B.firstCorner
    secondCorner := B.secondCorner
    firstSide := B.secondSide
    secondSide := B.firstSide
    first_embedded := B.second_embedded
    second_embedded := B.first_embedded
    first_zero := B.second_zero
    first_one := B.second_one
    second_zero := B.first_zero
    second_one := B.first_one
    first_on_curve := B.second_on_curve
    second_on_curve := B.first_on_curve
    sides_inter := (Set.inter_comm _ _).trans B.sides_inter
    disk := B.disk
    disk_embedded := B.disk_embedded
    boundary_eq := B.boundary_eq.trans (Set.union_comm _ _)
    marks_are_corners := B.marks_are_corners }
  have hswapempty : Disjoint Bswap.openInterior (b.val.image ∪ a.val.image) := by
    simpa only [Bswap,ActualMarkedTwoSideDisk.openInterior,Set.union_comm] using hempty
  have hsecondclean : range B.secondSide ∩ a.val.image = {B.firstCorner,B.secondCorner} :=
    actual_empty_marked_bigon_first_side_clean M b a
      (fun p hp => htab p (by simpa only [ArcSurgery.crossings,Set.inter_comm] using hp)) Bswap hswapempty
  have hDiskA : range B.disk ∩ a.val.image = range B.firstSide :=
    selected_disk_intersection a.val.image B.firstCorner B.secondCorner B.firstSide B.secondSide
      B.first_zero B.first_one B.first_on_curve hsecondclean B.disk B.boundary_eq
      (hempty.mono_right Set.subset_union_left)
  ext x
  constructor
  · rintro ⟨hxD,hxK⟩
    have hxa : x ∈ a.val.image := hdecompRaw.symm ▸ Or.inr hxK
    have hxs : x ∈ range B.firstSide := hDiskA ▸ ⟨hxD,hxa⟩
    exact hmeetRaw ▸ ⟨hxs,hxK⟩
  · intro hxc
    have hxs : x ∈ range B.firstSide ∩ Kraw := hmeetRaw.symm ▸ hxc
    exact ⟨image_subset_range _ _ (B.boundary_eq.symm ▸ (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inl hxs.1)),hxs.2⟩

theorem actual_marked_joined_path_cap_inside_original_disk
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (B : ActualMarkedTwoSideDisk M a b) (Kraw : Set S)
    (hret : range B.disk ∩ Kraw = ({B.firstCorner,B.secondCorner} : Set S))
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (hf0 : f 0 = B.firstCorner) (hf1 : f 1 = B.secondCorner)
    (hinter : range B.firstSide ∩ range f = ({B.firstCorner,B.secondCorner} : Set S))
    (hinside : range f ⊆ range B.disk) :
    ∃ Q : C(Metric.closedBall (0 : Plane) 1,S),
      IsEmbedding Q ∧
      Q '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range B.firstSide ∪ range f ∧
      range Q ⊆ range B.disk ∧
      (∀ p ∈ range Q, p ∈ M.cover.branch → p ∈ ({B.firstCorner,B.secondCorner} : Set S)) ∧
      Disjoint (Q '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) Kraw := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have hcollision (s t : Interval) (he : B.firstSide s = f t) :
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    have hcorner : B.firstSide s ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
      hinter ▸ (show B.firstSide s ∈ range B.firstSide ∩ range f from ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩)
    rcases hcorner with hc | hc
    · exact Or.inl ⟨B.first_embedded.injective (hc.trans B.first_zero.symm),
        hf.injective (he.symm.trans (hc.trans hf0.symm))⟩
    · exact Or.inr ⟨B.first_embedded.injective (hc.trans B.first_one.symm),
        hf.injective (he.symm.trans (hc.trans hf1.symm))⟩
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs B.firstSide f
    B.first_embedded.injective hf.injective (B.first_zero.trans hf0.symm)
    (B.first_one.trans hf1.symm) hcollision
  have hfirst : range B.firstSide ⊆ range B.disk := fun x hx =>
    image_subset_range _ _ (B.boundary_eq.symm ▸ (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inl hx))
  obtain ⟨Q,hQ,hboundary,hQinside⟩ := CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
    c B.disk B.disk_embedded (hc.symm ▸ Set.union_subset hfirst hinside)
  have hQboundary : Q '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range B.firstSide ∪ range f :=
    hboundary.trans hc
  refine ⟨Q,hQ,hQboundary,hQinside,?_,?_⟩
  · intro p hp hm
    exact B.marks_are_corners p (hQinside hp) hm
  · apply Set.disjoint_left.mpr
    rintro p ⟨x,hx,rfl⟩ hpK
    have hcorner : Q x ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
      hret ▸ ⟨hQinside (Set.mem_range_self x),hpK⟩
    have hfirstcorner : Q x ∈ range B.firstSide := by
      rcases hcorner with hc | hc
      · exact ⟨0,B.first_zero.trans hc.symm⟩
      · exact ⟨1,B.first_one.trans hc.symm⟩
    have hbd : Q x ∈ Q '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} :=
      hQboundary.symm ▸ (show Q x ∈ range B.firstSide ∪ range f from Or.inl hfirstcorner)
    obtain ⟨y,hy,he⟩ := hbd
    have hyx : y = x := hQ.injective he
    rw [hyx] at hy
    have hxnorm : dist x.val (0 : Plane) < 1 := hx
    have hynorm : dist x.val (0 : Plane) = 1 := hy
    linarith
end CurveComplex.HyperellipticModel

open Set Topology Schoenflies

/-- Once the actual assembled carrier is embedded, a compact complement of its
local horizontal piece is removed before deriving the whole-carrier axis iff.
No full-carrier trace certificate is assumed. -/
theorem actual_joined_carrier_local_axis_chart
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (f : C(CurveComplex.Interval,S)) (hf : IsEmbedding f)
    (A R K marks old : Set S) (hR : IsClosed R) (hK : IsClosed K)
    (hcover : range f ⊆ A ∪ R)
    (p : S) (hpf : p ∈ range f) (hpR : p ∉ R) (hpK : p ∉ K)
    (hp0 : p ≠ f 0) (hp1 : p ≠ f 1)
    (F : OpenPartialHomeomorph S Plane) (hpF : p ∈ F.source) (hFp : F p = 0)
    (hmarks : Disjoint F.source marks)
    (hline : ∀ x ∈ A ∩ F.source, F x 1 = 0)
    (hold : ∀ x ∈ F.source, x ∈ old ↔ F x 0 = 0) :
    ∃ G : OpenPartialHomeomorph S Plane,
      p ∈ G.source ∧ G p = 0 ∧ Disjoint G.source marks ∧ Disjoint G.source K ∧
      ∀ x ∈ G.source, (x ∈ range f ↔ G x 1 = 0) ∧ (x ∈ old ↔ G x 0 = 0) := by
  classical
  let U := Rᶜ ∩ Kᶜ
  have hU : IsOpen U := hR.isOpen_compl.inter hK.isOpen_compl
  let F' := F.restrOpen U hU
  have hpF' : p ∈ F'.source := ⟨hpF,hpR,hpK⟩
  have hF'p : F' p = 0 := hFp
  have hline' (x : S) (hx : x ∈ range f ∩ F'.source) : F' x 1 = 0 := by
    have hxA : x ∈ A := (hcover hx.1).resolve_right hx.2.2.1
    exact hline x ⟨hxA,hx.2.1⟩
  obtain ⟨t,ht⟩ := hpf
  have ht0 : 0 < t.val := by
    by_contra hn
    have he : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt hn) t.property.1)
    exact hp0 (ht.symm.trans (congrArg f he))
  have ht1 : t.val < 1 := by
    by_contra hn
    have he : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt hn))
    exact hp1 (ht.symm.trans (congrArg f he))
  let L : Plane ≃ₜ ℝ × ℝ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
  let E := F'.trans L.toOpenPartialHomeomorph
  have hEs : E.source = F'.source := by simp [E]
  have hE1 (x : S) : (E x).2 = F' x 1 := rfl
  have hEp : E p = (0,0) := by
    change L (F' p) = (0,0)
    rw [hF'p]
    rfl
  obtain ⟨ε,hε,hεtarget,htrace⟩ := CurveComplex.actual_embedded_arc_local_chart_horizontal_trace
    f hf t ht0 ht1 E (hEs.symm ▸ (ht.symm ▸ hpF')) 0
    (fun x hx => hE1 x ▸ hline' x ⟨hx.1,hEs ▸ hx.2⟩)
  rw [ht] at htrace
  let O := E.source ∩ E ⁻¹' Metric.ball (E p) ε
  have hO : IsOpen O := E.isOpen_inter_preimage Metric.isOpen_ball
  let G := F'.restrOpen O hO
  have hpG : p ∈ G.source := ⟨hpF',hEs.symm ▸ hpF',by simp [hε]⟩
  refine ⟨G,hpG,hF'p,hmarks.mono_left (fun x hx => hx.1.1),?_,?_⟩
  · exact disjoint_left.mpr (fun x hx h => hx.1.2.2 h)
  · intro x hx
    constructor
    · change x ∈ range f ↔ F' x 1 = 0
      simpa only [hE1] using htrace x hx.2.1 hx.2.2
    · exact hold x hx.1.1

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_side_parameter_selects_literal_marked_germ
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M)
    (side : C(Interval,S)) (α : C(Interval,Interval))
    (hα : Function.Injective α) (hparam : ∀ t, b.val.map (α t) = side t)
    (hp : side 0 ∈ M.cover.branch) :
    ∃ terminal : Bool, ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrhalf : r < 1/2,
      α 0 = (if terminal then 1 else 0) ∧
      (if terminal then b.val.map 1 else b.val.map 0) = side 0 ∧
      range (b.val.map ∘ endpointGermParameter terminal r hr (by linarith)) ⊆ range side := by
  have hends : α 0 = 0 ∨ α 0 = 1 := b.val.marked_only_at_ends (α 0) ((hparam 0).symm ▸ hp)
  have hne : α 1 ≠ α 0 := fun h => one_ne_zero (hα h)
  have hconn : Set.OrdConnected (range α) := (isPreconnected_range α.continuous).ordConnected
  rcases hends with hzero | hone
  · have hpos : 0 < (α 1).val := by
      have hn : (α 1).val ≠ 0 := fun h => hne ((Subtype.ext h).trans hzero.symm)
      exact lt_of_le_of_ne (α 1).property.1 (Ne.symm hn)
    let r := min ((α 1).val) (1/4) / 2
    have hr : 0 < r := half_pos (lt_min hpos (by norm_num))
    have hrhalf : r < 1/2 := by dsimp [r]; linarith [min_le_right ((α 1).val) (1/4)]
    have hrα : r ≤ (α 1).val := by dsimp [r]; linarith [min_le_left ((α 1).val) (1/4)]
    refine ⟨false,r,hr,hrhalf,hzero,by simpa [hzero] using hparam 0,?_⟩
    rintro x ⟨t,rfl⟩
    let u := endpointGermParameter false r hr (by linarith) t
    have hu : u ∈ Set.Icc (α 0) (α 1) := by
      rw [hzero]
      constructor
      · exact u.property.1
      · change r*t.val ≤ (α 1).val
        exact (mul_le_of_le_one_right hr.le t.property.2).trans hrα
    obtain ⟨s,hs⟩ := hconn.out (Set.mem_range_self 0) (Set.mem_range_self 1) hu
    exact ⟨s,(hparam s).symm.trans (congrArg b.val.map hs)⟩
  · have hpos : 0 < 1-(α 1).val := by
      have hn : (α 1).val ≠ 1 := fun h => hne ((Subtype.ext h).trans hone.symm)
      have hl : (α 1).val < 1 := lt_of_le_of_ne (α 1).property.2 hn
      linarith
    let r := min (1-(α 1).val) (1/4) / 2
    have hr : 0 < r := half_pos (lt_min hpos (by norm_num))
    have hrhalf : r < 1/2 := by dsimp [r]; linarith [min_le_right (1-(α 1).val) (1/4)]
    have hrα : r ≤ 1-(α 1).val := by dsimp [r]; linarith [min_le_left (1-(α 1).val) (1/4)]
    refine ⟨true,r,hr,hrhalf,hone,by simpa [hone] using hparam 0,?_⟩
    rintro x ⟨t,rfl⟩
    let u := endpointGermParameter true r hr (by linarith) t
    have hu : u ∈ Set.Icc (α 1) (α 0) := by
      rw [hone]
      constructor
      · change (α 1).val ≤ 1-r*t.val
        have hh := mul_le_of_le_one_right hr.le t.property.2
        linarith
      · exact u.property.2
    obtain ⟨s,hs⟩ := hconn.out (Set.mem_range_self 1) (Set.mem_range_self 0) hu
    exact ⟨s,(hparam s).symm.trans (congrArg b.val.map hs)⟩
end CurveComplex.HyperellipticModel
