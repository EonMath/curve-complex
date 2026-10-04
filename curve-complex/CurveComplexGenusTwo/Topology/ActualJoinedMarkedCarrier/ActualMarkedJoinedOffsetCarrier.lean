import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedPositiveRadialHorizontalCrossingChart
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.StrengthenedActualMarkedCornerFamily
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.StrengthenedActualUnmarkedCornerFamily
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedCornerFamily
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualUnmarkedCornerFamily
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualWholeInteriorAxisChart
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualDiskArcJoin
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.GlobalEndpointFamilies
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.SimultaneousGapMatching
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.VerifiedCarrierComponents
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedEndpointSourceFanChart
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedInteriorContactFanPreprocessing
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteSurfaceReplacement
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.GapMatchingTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.CornerGeometryTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualChartArcTools

import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedAffineCrossingDisk
import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.DiskExteriorHalfTools
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedAnchorPointChart
import Mathlib.Topology.LocalAtTarget
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualRawTailBigonReplacement
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkFreeBigonLoopExclusion
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance actualJoinedMarkedCarrierDecidableEqEssentialArcClass (M : HyperellipticModel E S) : DecidableEq (EssentialArcClass M) := Classical.decEq _
open ArcSurgery Set Topology Metric Schoenflies CurveComplex.ActualCrossingSlide
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
/- Exact private producer request; compact remainder is already constructed in the original body.
Source: JOINED_OFFSET_CARRIER_HELPER_REQUEST.md and ACTUAL_JOINED_OFFSET_CARRIER_PENDING_INTERFACE.md.
No ordered marked-endpoint labels or successful replacement are inputs. -/
theorem actual_marked_joined_offset_carrier
(M : HyperellipticModel E S) {J : Type} [Fintype J]
(old : J → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
(hOld : ∀ i j, i ≠ j → (ArcSurgery.crossings M (old i) (old j)).Finite ∧
  ∀ p ∈ ArcSurgery.crossings M (old i) (old j),
    ArcSurgery.CrossesInDisk M (old i) (old j) p)
(hab : (ArcSurgery.crossings M a b).Finite)
(htab : ∀ p ∈ ArcSurgery.crossings M a b, ArcSurgery.CrossesInDisk M a b p)
(ha : ∀ j, (ArcSurgery.crossings M a (old j)).Finite ∧
  ∀ p ∈ ArcSurgery.crossings M a (old j), ArcSurgery.CrossesInDisk M a (old j) p)
(hb : ∀ j, (ArcSurgery.crossings M b (old j)).Finite ∧
  ∀ p ∈ ArcSurgery.crossings M b (old j), ArcSurgery.CrossesInDisk M b (old j) p)
(B : ActualMarkedTwoSideDisk M a b)
(hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image))
(hhit : (B.firstCorner ∈ ArcSurgery.crossings M a b ∨
  B.secondCorner ∈ ArcSurgery.crossings M a b))
(hcorners : ∀ j p, p ∈ ({B.firstCorner,B.secondCorner} : Set S) →
  p ∉ M.cover.branch → p ∉ (old j).val.image)
(Kraw : Set S)
(hKraw : IsCompact Kraw)
(hdecompRaw : a.val.image = range B.firstSide ∪ Kraw)
(hmeetRaw : range B.firstSide ∩ Kraw = ({B.firstCorner,B.secondCorner} : Set S)) :
∃ f : C(Interval,S), IsEmbedding f ∧
  f 0 = B.firstCorner ∧ f 1 = B.secondCorner ∧
  range f ∩ b.val.image = ({B.firstCorner,B.secondCorner} : Set S) ∧
  range B.firstSide ∩ range f = ({B.firstCorner,B.secondCorner} : Set S) ∧
  range f ∩ Kraw = ({B.firstCorner,B.secondCorner} : Set S) ∧
  (∀ p ∈ range f, p ∈ M.cover.branch →
    p ∈ ({B.firstCorner,B.secondCorner} : Set S)) ∧
  (∀ j, (range f ∩ arcInterior M (old j)).Finite ∧
    (range f ∩ arcInterior M (old j)).ncard ≤
      (crossings M b (old j) ∩ range B.secondSide).ncard) ∧
  (∀ j p, p ∈ range f ∩ arcInterior M (old j) →
    ∃ F : OpenPartialHomeomorph S Plane,
      p ∈ F.source ∧ F p=0 ∧
      Disjoint F.source (M.cover.branch : Set S) ∧ Disjoint F.source Kraw ∧
      ∀ x ∈ F.source, (x ∈ range f ↔ F x 1=0) ∧
        (x ∈ (old j).val.image ↔ F x 0=0)) ∧
  ∃ Q : C(Metric.closedBall (0 : Plane) 1,S),
    IsEmbedding Q ∧
    Q '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} =
      range B.firstSide ∪ range f ∧
    (∀ p ∈ range Q, p ∈ M.cover.branch →
      p ∈ ({B.firstCorner,B.secondCorner} : Set S)) ∧
    Disjoint (Q '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) Kraw := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have hMarkedContactFreeGapConnector {J : Type} [Fintype J]
      (d : J → EssentialMarkedArc M) (g : EssentialMarkedArc M)
      (U : Set S) (V : Set (ℝ × ℝ)) (hV : IsOpen V) (e : U ≃ₜ V)
      (l r : ℝ) (hlr : l < r)
      (haxis : ∀ x ∈ Icc l r, ∃ y : V, y.val = (x,0) ∧
        ∀ j, (e.symm y : S) ∉ (d j).val.image)
      (hgaxis : ∀ u : U, (u : S) ∈ g.val.image ↔ (e u : ℝ × ℝ).2 = 0) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h < ε →
        ∃ f : C(unitInterval,S), IsEmbedding f ∧
          (∀ t, ∃ u : U, (u : S) = f t ∧
            (e u : ℝ × ℝ) = (l+(t : ℝ)*(r-l),h)) ∧
          Disjoint (Set.range f) g.val.image ∧
          ∀ j, Disjoint (Set.range f) (d j).val.image := by
    classical
    have hinverse : Continuous (fun y : V => (e.symm y : S)) :=
      continuous_subtype_val.comp e.symm.continuous
    let Q : Set V := {y | ∀ j, (e.symm y : S) ∉ (d j).val.image}
    have hQ : IsOpen Q := by
      have hO (j : J) : IsOpen {y : V | (e.symm y : S) ∉ (d j).val.image} :=
        (isCompact_range (d j).val.continuous).isClosed.isOpen_compl.preimage hinverse
      convert isOpen_iInter_of_finite hO using 1
      ext y
      simp [Q]
    let O : Set (ℝ × ℝ) := Subtype.val '' Q
    have hO : IsOpen O := hV.isOpenMap_subtype_val Q hQ
    let K : Set (ℝ × ℝ) := (fun x : ℝ => (x,0)) '' Icc l r
    have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
    have hKO : K ⊆ O := by
      rintro z ⟨x,hx,rfl⟩
      obtain ⟨y,hy,havoid⟩ := haxis x hx
      exact ⟨y,havoid,hy⟩
    obtain ⟨ε,hε,hclear⟩ := hK.exists_thickening_subset_open hO hKO
    have hrectangle (x y : ℝ) (hx : x ∈ Icc l r) (hy : |y| < ε) : (x,y) ∈ O := by
      apply hclear
      apply Metric.mem_thickening_iff.mpr
      refine ⟨(x,0),⟨x,hx,rfl⟩,?_⟩
      simpa [Prod.dist_eq,Real.dist_eq] using hy
    have hsafe (x y : ℝ) (hx : x ∈ Icc l r) (hy : |y| < ε) :
        ∃ hz : (x,y) ∈ V, ∀ j, (e.symm ⟨(x,y),hz⟩ : S) ∉ (d j).val.image := by
      obtain ⟨v,hv,hve⟩ := hrectangle x y hx hy
      have hz : (x,y) ∈ V := hve ▸ v.property
      refine ⟨hz,?_⟩
      have heq : v = ⟨(x,y),hz⟩ := Subtype.ext hve
      rwa [← heq]
    refine ⟨ε,hε,?_⟩
    intro h hh hhe
    have hparam (t : unitInterval) : l+(t : ℝ)*(r-l) ∈ Icc l r := by
      constructor <;> nlinarith [t.property.1,t.property.2]
    have hpoint (t : unitInterval) := hsafe (l+(t : ℝ)*(r-l)) h (hparam t)
      (by simpa [abs_of_pos hh] using hhe)
    let v : unitInterval → V := fun t => ⟨(l+(t : ℝ)*(r-l),h),(hpoint t).choose⟩
    have hv : Continuous v := (by fun_prop : Continuous (fun t : unitInterval =>
      (l+(t : ℝ)*(r-l),h))).subtype_mk _
    let f : C(unitInterval,S) := ⟨fun t => (e.symm (v t) : S),hinverse.comp hv⟩
    have hinj : Function.Injective f := by
      intro t s he
      have heU : e.symm (v t) = e.symm (v s) := Subtype.ext he
      have heV := e.symm.injective heU
      have hx := congrArg (fun z : V => z.val.1) heV
      change l+(t : ℝ)*(r-l) = l+(s : ℝ)*(r-l) at hx
      apply Subtype.ext
      nlinarith
    refine ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,?_,?_,?_⟩
    · intro t
      exact ⟨e.symm (v t),rfl,congrArg Subtype.val (e.apply_symm_apply (v t))⟩
    · apply Set.disjoint_left.mpr
      rintro x ⟨t,rfl⟩ hx
      have hzero := (hgaxis (e.symm (v t))).mp hx
      rw [e.apply_symm_apply] at hzero
      change h = 0 at hzero
      linarith
    · intro j
      apply Set.disjoint_left.mpr
      rintro x ⟨t,rfl⟩ hx
      exact (hpoint t).choose_spec j hx

  have hMarkedContactGapMatching {J : Type} [Fintype J]
      (d : J → EssentialMarkedArc M) (g : EssentialMarkedArc M)
      (U : Set S) (V : Set (ℝ × ℝ)) (hV : IsOpen V) (e : U ≃ₜ V)
      (A l r B : ℝ) (hAl : A < l) (hlr : l < r) (hrB : r < B)
      (haxis : ∀ x ∈ Icc A B, ∃ y : V, y.val = (x,0) ∧
        ∀ j, (e.symm y : S) ∉ (d j).val.image)
      (hgaxis : ∀ u : U, (u : S) ∈ g.val.image ↔ (e u : ℝ × ℝ).2 = 0)
      (L R : C(unitInterval,U))
      (hL : (e (L 0) : ℝ × ℝ) = (l,0))
      (hR : (e (R 0) : ℝ × ℝ) = (r,0))
      (hside : ∀ t : unitInterval, t ≠ 0 →
        0 < (e (L t) : ℝ × ℝ).2 ∧ 0 < (e (R t) : ℝ × ℝ).2) :
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < ρ →
        ∃ f : Path (L t : S) (R t : S), IsEmbedding f ∧
          Disjoint (Set.range f) g.val.image ∧
          (∀ j, Disjoint (Set.range f) (d j).val.image) ∧
          (∀ s, ∃ u : U, (u : S) = f s ∧
            (e u : ℝ × ℝ) =
              (1-(s : ℝ)) • (e (L t) : ℝ × ℝ) +
                (s : ℝ) • (e (R t) : ℝ × ℝ)) := by
    classical
    have hinverse : Continuous (fun y : V => (e.symm y : S)) :=
      continuous_subtype_val.comp e.symm.continuous
    let Q : Set V := {y | ∀ j, (e.symm y : S) ∉ (d j).val.image}
    have hQ : IsOpen Q := by
      have hO (j : J) : IsOpen {y : V | (e.symm y : S) ∉ (d j).val.image} :=
        (isCompact_range (d j).val.continuous).isClosed.isOpen_compl.preimage hinverse
      convert isOpen_iInter_of_finite hO using 1
      ext y
      simp [Q]
    let O : Set (ℝ × ℝ) := Subtype.val '' Q
    have hO : IsOpen O := hV.isOpenMap_subtype_val Q hQ
    let K : Set (ℝ × ℝ) := (fun x : ℝ => (x,0)) '' Icc A B
    have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
    have hKO : K ⊆ O := by
      rintro z ⟨x,hx,rfl⟩
      obtain ⟨y,hy,havoid⟩ := haxis x hx
      exact ⟨y,havoid,hy⟩
    obtain ⟨ε,hε,hclear⟩ := hK.exists_thickening_subset_open hO hKO
    have hsafe (x y : ℝ) (hx : x ∈ Icc A B) (hy : |y| < ε) :
        ∃ hz : (x,y) ∈ V, ∀ j, (e.symm ⟨(x,y),hz⟩ : S) ∉ (d j).val.image := by
      have hxy : (x,y) ∈ O := by
        apply hclear
        apply Metric.mem_thickening_iff.mpr
        refine ⟨(x,0),⟨x,hx,rfl⟩,?_⟩
        simpa [Prod.dist_eq,Real.dist_eq] using hy
      obtain ⟨v,hv,hve⟩ := hxy
      have hz : (x,y) ∈ V := hve ▸ v.property
      refine ⟨hz,?_⟩
      have heq : v = ⟨(x,y),hz⟩ := Subtype.ext hve
      rwa [← heq]
    let qL : unitInterval → ℝ × ℝ := fun t => e (L t)
    let qR : unitInterval → ℝ × ℝ := fun t => e (R t)
    have hqL : Continuous qL := by dsimp [qL]; fun_prop
    have hqR : Continuous qR := by dsimp [qR]; fun_prop
    let N : Set unitInterval := {t | A < (qL t).1 ∧ (qL t).1 < (l+r)/2 ∧
        (l+r)/2 < (qR t).1 ∧ (qR t).1 < B ∧
        |(qL t).2| < ε ∧ |(qR t).2| < ε}
    have hN : IsOpen N := by
      exact (isOpen_lt continuous_const hqL.fst).inter
        ((isOpen_lt hqL.fst continuous_const).inter
        ((isOpen_lt continuous_const hqR.fst).inter
        ((isOpen_lt hqR.fst continuous_const).inter
        ((isOpen_lt hqL.snd.abs continuous_const).inter
          (isOpen_lt hqR.snd.abs continuous_const)))))
    have h0N : (0 : unitInterval) ∈ N := by
      dsimp [N,qL,qR]
      rw [hL,hR]
      simp only [abs_zero]
      exact ⟨hAl,by linarith,by linarith,hrB,hε,hε⟩
    obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hN 0 h0N
    refine ⟨ρ,hρ,?_⟩
    intro t ht htρ
    have htN : t ∈ N := hball (by
      change dist t (0 : unitInterval) < ρ
      simpa [Subtype.dist_eq,Real.dist_eq,abs_of_pos ht] using htρ)
    obtain ⟨hAx,hxm,hmy,hyB,hLy,hRy⟩ := htN
    have ht0 : t ≠ 0 := by intro he; rw [he] at ht; simp at ht
    obtain ⟨hLp,hRp⟩ := hside t ht0
    let q (s : unitInterval) : ℝ × ℝ :=
      (1-(s : ℝ)) • qL t + (s : ℝ) • qR t
    have hcoord (s : unitInterval) :
        (q s).1 ∈ Icc A B ∧ 0 < (q s).2 ∧ (q s).2 < ε := by
      have hLε := lt_of_le_of_lt (le_abs_self (qL t).2) hLy
      have hRε := lt_of_le_of_lt (le_abs_self (qR t).2) hRy
      change 0 < (qL t).2 at hLp
      change 0 < (qR t).2 at hRp
      constructor
      · change A ≤ (1-(s : ℝ))*(qL t).1+(s : ℝ)*(qR t).1 ∧
          (1-(s : ℝ))*(qL t).1+(s : ℝ)*(qR t).1 ≤ B
        constructor <;> nlinarith [s.property.1,s.property.2,
          mul_nonneg (sub_nonneg.mpr s.property.2) (show 0 ≤ (qL t).1-A by linarith),
          mul_nonneg s.property.1 (show 0 ≤ (qR t).1-A by linarith),
          mul_nonneg (sub_nonneg.mpr s.property.2) (show 0 ≤ B-(qL t).1 by linarith),
          mul_nonneg s.property.1 (show 0 ≤ B-(qR t).1 by linarith)]
      · constructor
        · change 0 < (1-(s : ℝ))*(qL t).2+(s : ℝ)*(qR t).2
          nlinarith [s.property.1,s.property.2,
            mul_nonneg (sub_nonneg.mpr s.property.2) hLp.le,
            mul_nonneg s.property.1 hRp.le]
        · change (1-(s : ℝ))*(qL t).2+(s : ℝ)*(qR t).2 < ε
          nlinarith [s.property.1,s.property.2,
            mul_nonneg (sub_nonneg.mpr s.property.2) (show 0 ≤ ε-(qL t).2 by linarith),
            mul_nonneg s.property.1 (show 0 ≤ ε-(qR t).2 by linarith)]
    have hpoint (s : unitInterval) := hsafe (q s).1 (q s).2 (hcoord s).1
      (by simpa [abs_of_pos (hcoord s).2.1] using (hcoord s).2.2)
    let v : unitInterval → V := fun s => ⟨q s,(hpoint s).choose⟩
    have hv : Continuous v := (by dsimp [q]; fun_prop : Continuous q).subtype_mk _
    have hv0 : v 0 = e (L t) := by apply Subtype.ext; simp [v,q,qL]
    have hv1 : v 1 = e (R t) := by apply Subtype.ext; simp [v,q,qR]
    let f : Path (L t : S) (R t : S) := {
      toFun := fun s => (e.symm (v s) : S)
      continuous_toFun := hinverse.comp hv
      source' := by simp [hv0]
      target' := by simp [hv1] }
    have hinj : Function.Injective f := by
      intro s u he
      have hev := e.symm.injective (Subtype.ext he)
      have hx := congrArg (fun z : V => z.val.1) hev
      change (1-(s : ℝ))*(qL t).1+(s : ℝ)*(qR t).1 =
        (1-(u : ℝ))*(qL t).1+(u : ℝ)*(qR t).1 at hx
      apply Subtype.ext
      nlinarith
    refine ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,?_,?_,?_⟩
    · apply Set.disjoint_left.mpr
      rintro y ⟨s,rfl⟩ hy
      have hz := (hgaxis (e.symm (v s))).mp hy
      rw [e.apply_symm_apply] at hz
      change (q s).2 = 0 at hz
      linarith [(hcoord s).2.1]
    · intro j
      apply Set.disjoint_left.mpr
      rintro y ⟨s,rfl⟩ hy
      exact (hpoint s).choose_spec j hy
    · intro s
      exact ⟨e.symm (v s),rfl,congrArg Subtype.val (e.apply_symm_apply (v s))⟩

  have hMarkedUniformContactPatch {J : Type} [Fintype J]
      (old : J → EssentialMarkedArc M) (side : EssentialMarkedArc M)
      (F : OpenPartialHomeomorph S Plane)
      (hmark : Disjoint F.source (M.cover.branch : Set S))
      (η : ℝ) (hη : 0 < η) (hball : Metric.ball (0 : Plane) η ⊆ F.target)
      (haAxis : ∀ x ∈ F.source, x ∈ side.val.image ↔ F x 1=0)
      (a b : J → Plane) (ha : ∀ j, 0 < a j 1) (hb : ∀ j, b j 1 < 0)
      (hmodel : ∀ j x, x ∈ F.source → F x ∈ Metric.ball (0 : Plane) η →
        (x ∈ (old j).val.image ↔ F x ∈ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))) :
      ∃ δ H : ℝ, 0 < δ ∧ 0 < H ∧
        Plane.mk (-δ) 0 ∈ F.target ∧ Plane.mk δ 0 ∈ F.target ∧
        (∀ h : ℝ, 0 < h → h < H → segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ F.target) ∧
        ∀ h : ℝ, 0 < h → h < H →
        ∃ f : C(Interval,S), IsEmbedding f ∧
          range f=F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          f 0=F.symm (Plane.mk (-δ) h) ∧ f 1=F.symm (Plane.mk δ h) ∧
          range f ⊆ F.source ∧ (∀ x ∈ range f, F x 1=h) ∧ Disjoint (range f) (M.cover.branch : Set S) ∧
          Disjoint (range f) side.val.image ∧ ∀ j,
            f 0 ∉ (old j).val.image ∧ f 1 ∉ (old j).val.image ∧
            (range f ∩ (old j).val.image).Finite ∧
            (range f ∩ (old j).val.image).ncard ≤ 1 := by
    obtain ⟨δ,H,hδ,hH,hleft0,hright0,hpatch⟩ := CurveComplex.actual_uniform_radial_contact_patch a b ha hb η hη
    refine ⟨δ,H,hδ,hH,hball hleft0,hball hright0,?_,?_⟩
    · intro h hh hhH q hq
      exact hball ((hpatch h hh hhH).1 hq)
    intro h hh hhH
    obtain ⟨hC,hleft,hright,haxis,hcounts⟩ := hpatch h hh hhH
    let C := segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h)
    have hCt : C ⊆ F.target := fun q hq => hball (hC hq)
    have hlC : Plane.mk (-δ) h ∈ C := left_mem_segment ℝ _ _
    have hrC : Plane.mk δ h ∈ C := right_mem_segment ℝ _ _
    have hlS : F.symm (Plane.mk (-δ) h) ∈ F.source := F.map_target (hCt hlC)
    have hrS : F.symm (Plane.mk δ h) ∈ F.source := F.map_target (hCt hrC)
    have hne : Plane.mk (-δ) h ≠ Plane.mk δ h := by
      intro he
      have hh := congrArg (fun q : Plane => q 0) he
      change -δ=δ at hh
      linarith
    have hArc : IsArcBetween C
        (F (F.symm (Plane.mk (-δ) h))) (F (F.symm (Plane.mk δ h))) := by
      rw [F.right_inv (hCt hlC),F.right_inv (hCt hrC)]
      exact Schoenflies.isArcBetween_segment hne
    obtain ⟨f,hfi,hf,hf0,hf1⟩ := CurveComplex.actual_pullback_chart_arc F
      (F.symm (Plane.mk (-δ) h)) (F.symm (Plane.mk δ h)) hlS hrS C hArc hCt
    have hsub : range f ⊆ F.source := by
      rw [hf]
      rintro x ⟨q,hq,rfl⟩
      exact F.map_target (hCt hq)
    have hcoord (q : Plane) (hq : q ∈ C) : F (F.symm q)=q := F.right_inv (hCt hq)
    have hnorm (q : Plane) (hq : q ∈ C) : F (F.symm q) ∈ Metric.ball (0 : Plane) η := by
      rw [hcoord q hq]
      exact hC hq
    have hinter (j : J) : range f ∩ (old j).val.image =
        F.symm '' (C ∩ (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))) := by
      rw [hf]
      ext x
      constructor
      · rintro ⟨⟨q,hq,rfl⟩,hx⟩
        refine ⟨q,⟨hq,?_⟩,rfl⟩
        have hm := (hmodel j _ (F.map_target (hCt hq)) (hnorm q hq)).mp hx
        simpa only [hcoord q hq] using hm
      · rintro ⟨q,⟨hq,hqr⟩,rfl⟩
        refine ⟨⟨q,hq,rfl⟩,?_⟩
        apply (hmodel j _ (F.map_target (hCt hq)) (hnorm q hq)).mpr
        simpa only [hcoord q hq] using hqr
    refine ⟨f,hfi,hf,hf0,hf1,hsub,?_,hmark.mono_left hsub,?_,?_⟩
    · intro x hx
      obtain ⟨q,hq,rfl⟩ := hf ▸ hx
      rw [hcoord q hq]
      dsimp [C] at hq
      rw [segment_eq_image'] at hq
      obtain ⟨t,ht,he⟩ := hq
      have hh := congrArg (fun z : Plane => z 1) he
      change h+t*(h-h)=q 1 at hh
      linarith
    · apply Set.disjoint_left.mpr
      rintro x hx hxside
      rw [hf] at hx
      obtain ⟨q,hq,rfl⟩ := hx
      have hzero := (haAxis _ (F.map_target (hCt hq))).mp hxside
      rw [hcoord q hq] at hzero
      exact Set.disjoint_left.mp haxis hq hzero
    · intro j
      refine ⟨?_,?_,?_,?_⟩
      · rw [hf0]
        intro hx
        have hm := (hmodel j _ hlS (hnorm _ hlC)).mp hx
        rw [hcoord _ hlC] at hm
        exact hleft j hm
      · rw [hf1]
        intro hx
        have hm := (hmodel j _ hrS (hnorm _ hrC)).mp hx
        rw [hcoord _ hrC] at hm
        exact hright j hm
      · rw [hinter j]
        exact ((hcounts j).1).image F.symm
      · rw [hinter j]
        exact (Set.ncard_image_le (hcounts j).1).trans (hcounts j).2
  have hMarkedSignedCornerPatch {J : Type} [Fintype J]
      (old : J → EssentialMarkedArc M) (side : EssentialMarkedArc M)
      (F : OpenPartialHomeomorph S Plane)
      (hmark : Disjoint F.source (M.cover.branch : Set S))
      (η : ℝ) (hη : 0 < η) (hball : Metric.ball (0 : Plane) η ⊆ F.target)
      (haAxis : ∀ x ∈ F.source, x ∈ side.val.image ↔ F x 1=0)
      (a b : J → Plane) (ha : ∀ j, 0 < a j 1) (hb : ∀ j, b j 1 < 0)
      (hmodel : ∀ j x, x ∈ F.source → F x ∈ Metric.ball (0 : Plane) η →
        (x ∈ (old j).val.image ↔ F x ∈ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)))
      (δ ξ h : ℝ) (hδ : 0 < δ) (hh : h ≠ 0)
      (hC : segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) ⊆ Metric.ball (0 : Plane) η) :
      ∃ f : C(Interval,S), IsEmbedding f ∧
        range f=F.symm '' segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) ∧
        f 0=F.symm (Plane.mk (-δ) 0) ∧ f 1=F.symm (Plane.mk ξ h) ∧
        range f ⊆ F.source ∧ Disjoint (range f) (M.cover.branch : Set S) ∧
        ∀ j, (range f ∩ (old j).val.image).Finite ∧
          (range f ∩ (old j).val.image).ncard ≤ 1 := by
    have hcounts := CurveComplex.actual_signed_corner_segment_counts a b ha hb δ ξ h hδ hh
    let C := segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h)
    have hCt : C ⊆ F.target := fun q hq => hball (hC hq)
    have hlC : Plane.mk (-δ) 0 ∈ C := left_mem_segment ℝ _ _
    have hrC : Plane.mk ξ h ∈ C := right_mem_segment ℝ _ _
    have hlS : F.symm (Plane.mk (-δ) 0) ∈ F.source := F.map_target (hCt hlC)
    have hrS : F.symm (Plane.mk ξ h) ∈ F.source := F.map_target (hCt hrC)
    have hne : Plane.mk (-δ) 0 ≠ Plane.mk ξ h := by
      intro he
      have hy := congrArg (fun q : Plane => q 1) he
      exact hh (by simpa [Plane.mk] using hy.symm)
    have hArc : IsArcBetween C
        (F (F.symm (Plane.mk (-δ) 0))) (F (F.symm (Plane.mk ξ h))) := by
      rw [F.right_inv (hCt hlC),F.right_inv (hCt hrC)]
      exact Schoenflies.isArcBetween_segment hne
    obtain ⟨f,hfi,hf,hf0,hf1⟩ := CurveComplex.actual_pullback_chart_arc F
      (F.symm (Plane.mk (-δ) 0)) (F.symm (Plane.mk ξ h)) hlS hrS C hArc hCt
    have hsub : range f ⊆ F.source := by
      rw [hf]
      rintro x ⟨q,hq,rfl⟩
      exact F.map_target (hCt hq)
    have hcoord (q : Plane) (hq : q ∈ C) : F (F.symm q)=q := F.right_inv (hCt hq)
    have hnorm (q : Plane) (hq : q ∈ C) : F (F.symm q) ∈ Metric.ball (0 : Plane) η := by
      rw [hcoord q hq]
      exact hC hq
    have hinter (j : J) : range f ∩ (old j).val.image =
        F.symm '' (C ∩ (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))) := by
      rw [hf]
      ext x
      constructor
      · rintro ⟨⟨q,hq,rfl⟩,hx⟩
        refine ⟨q,⟨hq,?_⟩,rfl⟩
        have hm := (hmodel j _ (F.map_target (hCt hq)) (hnorm q hq)).mp hx
        simpa only [hcoord q hq] using hm
      · rintro ⟨q,⟨hq,hqr⟩,rfl⟩
        refine ⟨⟨q,hq,rfl⟩,?_⟩
        apply (hmodel j _ (F.map_target (hCt hq)) (hnorm q hq)).mpr
        simpa only [hcoord q hq] using hqr
    refine ⟨f,hfi,hf,hf0,hf1,hsub,hmark.mono_left hsub,?_⟩
    intro j
    constructor
    · rw [hinter j]
      exact ((hcounts j).1).image F.symm
    · rw [hinter j]
      exact (Set.ncard_image_le (hcounts j).1).trans (hcounts j).2
  have hMarkedReplacementContactAccounting {J K : Type} [Fintype J] [Fintype K]
      (old : J → EssentialMarkedArc M) (c : EssentialMarkedArc M)
      (hfinite : ∀ j, (crossings M c (old j)).Finite)
      (E : K → OpenPartialHomeomorph S Plane)
      (hdis : ∀ i j, i ≠ j → Disjoint (E i).source (E j).source)
      (hmarks : ∀ k, Disjoint (E k).source (M.cover.branch : Set S))
      (hSquare : ∀ k, Plane.closedSquare 0 1 ⊆ (E k).target)
      (A : Set Plane)
      (hA : IsArcBetween A (Plane.mk (-1) 0) (Plane.mk 1 0))
      (hAi : A \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1)
      (hc : ∀ k, {x : S | x ∈ (E k).source ∧ E k x ∈ Plane.closedSquare 0 1} ∩
        c.val.image = {x : S | x ∈ (E k).source ∧ E k x ∈ A})
      (B : K → Set Plane)
      (hB : ∀ k, IsArcBetween (B k) (Plane.mk (-1) 0) (Plane.mk 1 0))
      (hBi : ∀ k, B k \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1)
      (hBC : ∀ k j, (B k ∩ (E k) '' ((old j).val.image ∩ (E k).source)).Finite) :
      ∃ H : AmbientIsotopy S, ∃ d : EssentialMarkedArc M,
        vertex M d=vertex M c ∧
        (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
        d.val.image=H.finalMap '' c.val.image ∧
        ∀ j, (crossings M d (old j)).Finite ∧
          (crossings M d (old j)).ncard ≤
            (crossings M c (old j) \ ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ A}).ncard +
            ∑ k, (B k ∩ (E k) '' ((old j).val.image ∩ (E k).source)).ncard := by
    obtain ⟨H,d,hdim,hdclass,hHm,hd⟩ := actual_marked_finite_surface_replacement M c K E
      hdis hmarks hSquare A hA hAi hc B hB hBi
    let Ap : Set S := ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ A}
    let Bp : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ B k}
    have hBpmark (k : K) : Disjoint (Bp k) (M.cover.branch : Set S) :=
      (hmarks k).mono_left (fun _ hx => hx.1)
    have hBimage (k : K) (j : J) : Bp k ∩ (old j).val.image =
        (E k).symm '' (B k ∩ (E k) '' ((old j).val.image ∩ (E k).source)) := by
      ext x
      constructor
      · rintro ⟨⟨hx,hxb⟩,hxo⟩
        exact ⟨E k x,⟨hxb,⟨x,⟨hxo,hx⟩,rfl⟩⟩,(E k).left_inv hx⟩
      · rintro ⟨q,⟨hqb,⟨y,⟨hyo,hys⟩,hyq⟩⟩,rfl⟩
        have hqt : q ∈ (E k).target := hyq ▸ (E k).map_source hys
        have hqy : (E k).symm q=y := by rw [← hyq,(E k).left_inv hys]
        exact ⟨⟨(E k).map_target hqt,by simpa only [(E k).right_inv hqt] using hqb⟩,
          hqy.symm ▸ hyo⟩
    have hsplit (j : J) : crossings M d (old j) =
        (crossings M c (old j) \ Ap) ∪ ⋃ k, Bp k ∩ (old j).val.image := by
      ext x
      constructor
      · rintro ⟨⟨hxd,hxm⟩,hxo,hxom⟩
        rw [hd] at hxd
        rcases hxd with hr|hn
        · exact Or.inl ⟨⟨⟨hr.1,hxm⟩,hxo,hxom⟩,hr.2⟩
        · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hn
          exact Or.inr (Set.mem_iUnion.mpr ⟨k,hk,hxo⟩)
      · intro hx
        rcases hx with hr|hn
        · refine ⟨⟨?_,hr.1.1.2⟩,hr.1.2⟩
          rw [hd]
          exact Or.inl ⟨hr.1.1.1,hr.2⟩
        · obtain ⟨k,hk,hxo⟩ := Set.mem_iUnion.mp hn
          have hxm : x ∉ M.cover.branch := fun hm => Set.disjoint_left.mp (hBpmark k) hk hm
          refine ⟨⟨?_,hxm⟩,hxo,hxm⟩
          rw [hd]
          exact Or.inr (Set.mem_iUnion.mpr ⟨k,hk⟩)
    refine ⟨H,d,hdclass,hHm,hdim,?_⟩
    intro j
    have hpieces (k : K) : (Bp k ∩ (old j).val.image).Finite := by
      rw [hBimage k j]
      exact (hBC k j).image (E k).symm
    obtain ⟨hU,hUcard⟩ := CurveComplex.actual_finite_union_card_bound
      (fun k => Bp k ∩ (old j).val.image) hpieces
    have hrem : (crossings M c (old j) \ Ap).Finite := (hfinite j).subset Set.diff_subset
    constructor
    · rw [hsplit j]
      exact hrem.union hU
    · rw [hsplit j]
      apply (Set.ncard_union_le _ _).trans
      apply Nat.add_le_add_left
      apply hUcard.trans
      apply Finset.sum_le_sum
      intro k hk
      rw [hBimage k j]
      exact Set.ncard_image_le (hBC k j)
  have hActualMarkedSubarcRemainder (c : EssentialMarkedArc M)
      (L R : ℝ) (hL : 0 ≤ L) (hLR : L < R) (hR : R ≤ 1)
      (hproper : 0 < L ∨ R < 1) :
      let γ := c.val.map ∘ Set.projIcc 0 1 zero_le_one
      ∃ f : C(Interval,S), IsEmbedding f ∧
        f 0=γ L ∧ f 1=γ R ∧ range f=γ '' Set.Icc L R ∧
        ∃ K : Set S, IsCompact K ∧ c.val.image=range f ∪ K ∧
          range f ∩ K={γ L,γ R} := by
    let γ := c.val.map ∘ Set.projIcc 0 1 zero_le_one
    have hγ : Continuous γ := c.val.continuous.comp continuous_projIcc
    have hparam (t : Interval) : L+t.val*(R-L) ∈ Set.Icc L R := by
      constructor <;> nlinarith [t.property.1,t.property.2]
    let f : C(Interval,S) := ⟨fun t => γ (L+t.val*(R-L)),hγ.comp (by fun_prop)⟩
    have hγinj (x y : ℝ) (hx : x ∈ Set.Icc L R) (hy : y ∈ Set.Icc L R)
        (he : γ x=γ y) : x=y := by
      have hx01 : x ∈ Set.Icc (0:ℝ) 1 := ⟨hL.trans hx.1,hx.2.trans hR⟩
      have hy01 : y ∈ Set.Icc (0:ℝ) 1 := ⟨hL.trans hy.1,hy.2.trans hR⟩
      simp only [γ,Function.comp_apply,Set.projIcc_of_mem zero_le_one hx01,
        Set.projIcc_of_mem zero_le_one hy01] at he
      rcases c.val.injective_except_loop_closure _ _ he with he|he|he
      · exact congrArg Subtype.val he
      · have hx0 := congrArg Subtype.val he.1
        have hy1 := congrArg Subtype.val he.2
        change x=0 at hx0; change y=1 at hy1
        rcases hproper with hp|hp <;> linarith [hx.1,hy.2]
      · have hx1 := congrArg Subtype.val he.1
        have hy0 := congrArg Subtype.val he.2
        change x=1 at hx1; change y=0 at hy0
        rcases hproper with hp|hp <;> linarith [hy.1,hx.2]
    have hfi : Function.Injective f := by
      intro t u he
      have hh := hγinj _ _ (hparam t) (hparam u) he
      apply Subtype.ext
      nlinarith
    have hf : range f=γ '' Set.Icc L R := by
      ext x
      constructor
      · rintro ⟨t,rfl⟩; exact ⟨_,hparam t,rfl⟩
      · rintro ⟨θ,hθ,rfl⟩
        have ht : (θ-L)/(R-L) ∈ Set.Icc (0:ℝ) 1 := by
          constructor
          · exact div_nonneg (by linarith [hθ.1]) (by linarith)
          · apply (div_le_one (by linarith : 0 < R-L)).mpr
            linarith [hθ.2]
        refine ⟨⟨(θ-L)/(R-L),ht⟩,?_⟩
        change γ (L+(θ-L)/(R-L)*(R-L))=γ θ
        rw [div_mul_cancel₀ _ (by linarith : R-L ≠ 0)]
        congr 1; ring
    let K : Set S := γ '' Set.Icc 0 L ∪ γ '' Set.Icc R 1
    have hK : IsCompact K := (isCompact_Icc.image hγ).union (isCompact_Icc.image hγ)
    have hfull : c.val.image=range f ∪ K := by
      rw [hf]
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        have hgt : γ t.val=c.val.map t := by
          simp only [γ,Function.comp_apply,Set.projIcc_of_mem zero_le_one t.property]
        by_cases htL : t.val < L
        · exact Or.inr (Or.inl ⟨t.val,⟨t.property.1,htL.le⟩,hgt⟩)
        · by_cases htR : R < t.val
          · exact Or.inr (Or.inr ⟨t.val,⟨htR.le,t.property.2⟩,hgt⟩)
          · exact Or.inl ⟨t.val,⟨le_of_not_gt htL,le_of_not_gt htR⟩,hgt⟩
      · rintro (⟨θ,hθ,rfl⟩| (⟨θ,hθ,rfl⟩|⟨θ,hθ,rfl⟩)) <;>
          exact Set.mem_range_self _
    have hmeet : range f ∩ K={γ L,γ R} := by
      rw [hf]
      ext x
      constructor
      · rintro ⟨⟨θ,hθ,hθx⟩,hxK⟩
        rcases hxK with ⟨ψ,hψ,hψx⟩|⟨ψ,hψ,hψx⟩
        all_goals
          have hθ01 : θ ∈ Set.Icc (0:ℝ) 1 := ⟨hL.trans hθ.1,hθ.2.trans hR⟩
          have hψ01 : ψ ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hψ.1,hψ.2]
          have he := hθx.trans hψx.symm
          simp only [γ,Function.comp_apply,Set.projIcc_of_mem zero_le_one hθ01,
            Set.projIcc_of_mem zero_le_one hψ01] at he
          rcases c.val.injective_except_loop_closure _ _ he with he|he|he
        · have heR := congrArg Subtype.val he
          have hθL : θ=L := by linarith [hθ.1,hψ.2]
          exact Or.inl (hθx.symm.trans (congrArg γ hθL))
        · have hθ0 := congrArg Subtype.val he.1
          change θ=0 at hθ0
          have hθL : θ=L := by linarith [hθ.1]
          exact Or.inl (hθx.symm.trans (congrArg γ hθL))
        · have hθ1 := congrArg Subtype.val he.1
          change θ=1 at hθ1
          have hθR : θ=R := by linarith [hθ.2]
          exact Or.inr (hθx.symm.trans (congrArg γ hθR))
        · have heR := congrArg Subtype.val he
          have hθR : θ=R := by linarith [hθ.2,hψ.1]
          exact Or.inr (hθx.symm.trans (congrArg γ hθR))
        · have hθ0 := congrArg Subtype.val he.1
          change θ=0 at hθ0
          have hθL : θ=L := by linarith [hθ.1]
          exact Or.inl (hθx.symm.trans (congrArg γ hθL))
        · have hθ1 := congrArg Subtype.val he.1
          change θ=1 at hθ1
          have hθR : θ=R := by linarith [hθ.2]
          exact Or.inr (hθx.symm.trans (congrArg γ hθR))
      · rintro (rfl|rfl)
        · exact ⟨⟨L,⟨le_rfl,hLR.le⟩,rfl⟩,Or.inl ⟨L,⟨hL,le_rfl⟩,rfl⟩⟩
        · exact ⟨⟨R,⟨hLR.le,le_rfl⟩,rfl⟩,Or.inr ⟨R,⟨le_rfl,hR⟩,rfl⟩⟩
    refine ⟨f,(f.continuous.isClosedEmbedding hfi).isEmbedding,?_,?_,hf,K,hK,hfull,hmeet⟩
    · change γ (L+(0:ℝ)*(R-L))=γ L; simp
    · change γ (L+(1:ℝ)*(R-L))=γ R; congr 1; ring
  have hActualUnmarkedSideParameters (c : EssentialMarkedArc M)
      (f : C(Interval,S)) (hf : IsEmbedding f) (hfc : range f ⊆ c.val.image)
      (h0 : c.val.map 0 ∉ range f) (h1 : c.val.map 1 ∉ range f) :
      ∃ L R : ℝ, 0 < L ∧ L < R ∧ R < 1 ∧
        range f=(c.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc L R := by
    classical
    let T : Set Interval := c.val.map ⁻¹' range f
    have hTc : IsCompact T := (isCompact_range f.continuous).isClosed.preimage c.val.continuous |>.isCompact
    have hTne : T.Nonempty := by
      obtain ⟨t,ht⟩ := hfc (Set.mem_range_self (0:Interval))
      exact ⟨t,⟨0,ht.symm⟩⟩
    obtain ⟨l,hl⟩ := hTc.exists_isLeast hTne
    obtain ⟨r,hr⟩ := hTc.exists_isGreatest hTne
    have hlr : l ≤ r := hl.2 hr.1
    have hl0 : 0 < l.val := by
      have hne : l ≠ 0 := fun he => h0 (he ▸ hl.1)
      exact lt_of_le_of_ne l.property.1 (fun he => hne (Subtype.ext he.symm))
    have hr1 : r.val < 1 := by
      have hne : r ≠ 1 := fun he => h1 (he ▸ hr.1)
      exact lt_of_le_of_ne r.property.2 (fun he => hne (Subtype.ext he))
    have hlt : l.val < r.val := by
      by_contra hn
      have he : l=r := le_antisymm hlr (le_of_not_gt hn)
      have hconst (t : Interval) : f t=c.val.map l := by
        obtain ⟨u,hu⟩ := hfc (Set.mem_range_self t)
        have huT : u ∈ T := ⟨t,hu.symm⟩
        have hul : u=l := le_antisymm (he ▸ hr.2 huT) (hl.2 huT)
        exact hu.symm.trans (congrArg c.val.map hul)
      have h01 : (0:Interval)=1 := hf.injective ((hconst 0).trans (hconst 1).symm)
      have hh := congrArg Subtype.val h01
      norm_num at hh
    let g : Set.Icc l.val r.val → S := fun t => c.val.map ⟨t.val,
      ⟨hl0.le.trans t.property.1,t.property.2.trans hr1.le⟩⟩
    have hgc : Continuous g := c.val.continuous.comp (by fun_prop)
    have hgi : Function.Injective g := by
      intro t u he
      rcases c.val.injective_except_loop_closure _ _ he with he|he|he
      · apply Subtype.ext; exact congrArg (fun z : Interval => z.val) he
      · have ht0 := congrArg Subtype.val he.1
        change t.val=0 at ht0
        linarith [t.property.1]
      · have ht1 := congrArg Subtype.val he.1
        change t.val=1 at ht1
        linarith [t.property.2]
    let e : Set.Icc l.val r.val ≃ₜ range g := (hgc.isClosedEmbedding hgi).isEmbedding.toHomeomorph
    have hfr (t : Interval) : f t ∈ range g := by
      obtain ⟨u,hu⟩ := hfc (Set.mem_range_self t)
      have huT : u ∈ T := ⟨t,hu.symm⟩
      refine ⟨⟨u.val,⟨hl.2 huT,hr.2 huT⟩⟩,?_⟩
      exact hu
    let α : Interval → ℝ := fun t => (e.symm ⟨f t,hfr t⟩).val
    have hαc : Continuous α := continuous_subtype_val.comp
      (e.symm.continuous.comp (f.continuous.subtype_mk _))
    have hαf (t : Interval) : g (e.symm ⟨f t,hfr t⟩)=f t :=
      congrArg Subtype.val (e.apply_symm_apply _)
    have hRangeL : l.val ∈ range α := by
      obtain ⟨t,ht⟩ := hl.1
      refine ⟨t,?_⟩
      change (e.symm ⟨f t,hfr t⟩).val=(⟨l.val,⟨le_rfl,hlr⟩⟩ : Set.Icc l.val r.val).val
      apply congrArg (fun z : Set.Icc l.val r.val => z.val)
      apply e.injective
      apply Subtype.ext
      exact (hαf t).trans ht
    have hRangeR : r.val ∈ range α := by
      obtain ⟨t,ht⟩ := hr.1
      refine ⟨t,?_⟩
      change (e.symm ⟨f t,hfr t⟩).val=(⟨r.val,⟨hlr,le_rfl⟩⟩ : Set.Icc l.val r.val).val
      apply congrArg (fun z : Set.Icc l.val r.val => z.val)
      apply e.injective
      apply Subtype.ext
      exact (hαf t).trans ht
    have hConnected : IsPreconnected (range α) := by
      simpa only [Set.image_univ] using isPreconnected_univ.image α hαc.continuousOn
    have hRange : range α=Set.Icc l.val r.val := by
      apply Set.Subset.antisymm
      · rintro x ⟨t,rfl⟩; exact (e.symm ⟨f t,hfr t⟩).property
      · exact hConnected.ordConnected.out hRangeL hRangeR
    refine ⟨l.val,r.val,hl0,hlt,hr1,?_⟩
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨α t,hRange ▸ Set.mem_range_self t,?_⟩
      simp only [Function.comp_apply,Set.projIcc_of_mem zero_le_one
        (show α t ∈ Set.Icc (0:ℝ) 1 from
          ⟨hl0.le.trans (e.symm ⟨f t,hfr t⟩).property.1,
            (e.symm ⟨f t,hfr t⟩).property.2.trans hr1.le⟩)]
      exact hαf t
    · rintro ⟨θ,hθ,rfl⟩
      obtain ⟨t,ht⟩ := hRange.symm ▸ hθ
      refine ⟨t,?_⟩
      rw [← ht]
      simp only [Function.comp_apply,Set.projIcc_of_mem zero_le_one
        (show α t ∈ Set.Icc (0:ℝ) 1 from
          ⟨hl0.le.trans (e.symm ⟨f t,hfr t⟩).property.1,
            (e.symm ⟨f t,hfr t⟩).property.2.trans hr1.le⟩)]
      exact (hαf t).symm
  have hActualMarkedPaddedRemainder (c : EssentialMarkedArc M)
      (L R : ℝ) (hL : 0 < L) (hLR : L < R) (hR : R < 1)
      (V D : Set S) (hV : IsOpen V)
      (hFV : (c.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc L R ⊆ V)
      (hD : D ∩ c.val.image=(c.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc L R) :
      let γ := c.val.map ∘ Set.projIcc 0 1 zero_le_one
      ∃ A B : ℝ, ∃ K : Set S,
        0 < A ∧ A < L ∧ R < B ∧ B < 1 ∧ γ '' Set.Icc A B ⊆ V ∧
        IsCompact K ∧ c.val.image=γ '' Set.Icc A B ∪ K ∧
        Disjoint (γ '' Set.Icc L R) K ∧ Disjoint D K := by
    let γ := c.val.map ∘ Set.projIcc 0 1 zero_le_one
    have hγ : Continuous γ := c.val.continuous.comp continuous_projIcc
    have hpre : IsOpen (γ ⁻¹' V) := hV.preimage hγ
    have hLV : L ∈ γ ⁻¹' V := hFV ⟨L,⟨le_rfl,hLR.le⟩,rfl⟩
    have hRV : R ∈ γ ⁻¹' V := hFV ⟨R,⟨hLR.le,le_rfl⟩,rfl⟩
    obtain ⟨r,hr,hra⟩ := Metric.isOpen_iff.mp hpre L hLV
    obtain ⟨s,hs,hsb⟩ := Metric.isOpen_iff.mp hpre R hRV
    let ε := min r (min s (min L (1-R)))/2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεr : ε < r := by dsimp [ε]; linarith [min_le_left r (min s (min L (1-R)))]
    have hεs : ε < s := by
      have hh := (min_le_right r (min s (min L (1-R)))).trans (min_le_left s (min L (1-R)))
      dsimp [ε]; linarith
    have hεL : ε < L := by
      have hh := ((min_le_right r (min s (min L (1-R)))).trans
        (min_le_right s (min L (1-R)))).trans (min_le_left L (1-R))
      dsimp [ε]; linarith
    have hεR : ε < 1-R := by
      have hh := ((min_le_right r (min s (min L (1-R)))).trans
        (min_le_right s (min L (1-R)))).trans (min_le_right L (1-R))
      dsimp [ε]; linarith
    let A := L-ε
    let B := R+ε
    have hA : 0 < A := by dsimp [A]; linarith
    have hAL : A < L := by dsimp [A]; linarith
    have hRB : R < B := by dsimp [B]; linarith
    have hB : B < 1 := by dsimp [B]; linarith
    have hAB : A < B := hAL.trans (hLR.trans hRB)
    have hpad : γ '' Set.Icc A B ⊆ V := by
      rintro x ⟨t,ht,rfl⟩
      by_cases htL : t < L
      · apply hra
        rw [Metric.mem_ball,Real.dist_eq,abs_of_neg (sub_neg.mpr htL)]
        dsimp [A] at ht
        linarith [ht.1]
      · by_cases hRt : R < t
        · apply hsb
          rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr hRt)]
          dsimp [B] at ht
          linarith [ht.2]
        · exact hFV ⟨t,⟨le_of_not_gt htL,le_of_not_gt hRt⟩,rfl⟩
    obtain ⟨f,hfi,hf0,hf1,hf,K,hK,hfull,hmeet⟩ :=
      hActualMarkedSubarcRemainder c A B hA.le hAB hB.le (Or.inl hA)
    have hFK : Disjoint (γ '' Set.Icc L R) K := by
      apply Set.disjoint_left.mpr
      rintro x ⟨t,ht,he⟩ hxK
      have hcore : x ∈ range f := by
        rw [hf]
        exact ⟨t,⟨hAL.le.trans ht.1,ht.2.trans hRB.le⟩,he⟩
      have hend : x=γ A ∨ x=γ B := by
        have hh : x ∈ range f ∩ K := ⟨hcore,hxK⟩
        rw [hmeet] at hh
        exact hh
      have ht01 : t ∈ Set.Icc (0:ℝ) 1 := ⟨hL.le.trans ht.1,ht.2.trans hR.le⟩
      have hport (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (heq : γ t=γ q) : t=q := by
        simp only [γ,Function.comp_apply,Set.projIcc_of_mem zero_le_one ht01,
          Set.projIcc_of_mem zero_le_one hq] at heq
        rcases c.val.injective_except_loop_closure _ _ heq with heq|heq|heq
        · exact congrArg Subtype.val heq
        · have hh := congrArg Subtype.val heq.1
          change t=0 at hh; linarith [ht.1]
        · have hh := congrArg Subtype.val heq.1
          change t=1 at hh; linarith [ht.2]
      rcases hend with hend|hend
      · have hh := hport A ⟨hA.le,(hAL.trans hLR).trans hR |>.le⟩ (he.trans hend)
        linarith [ht.1]
      · have hh := hport B ⟨(hL.trans hLR).trans hRB |>.le,hB.le⟩ (he.trans hend)
        linarith [ht.2]
    refine ⟨A,B,K,hA,hAL,hRB,hB,hpad,hK,?_,hFK,?_⟩
    · rw [hf] at hfull; exact hfull
    · apply Set.disjoint_left.mpr
      intro x hxD hxK
      have hxc : x ∈ c.val.image := hfull.symm ▸ Or.inr hxK
      have hxf : x ∈ γ '' Set.Icc L R := hD ▸ (show x ∈ D ∩ c.val.image from ⟨hxD,hxc⟩)
      exact Set.disjoint_left.mp hFK hxf hxK
  have hSelectedDiskIntersection {S : Type} [TopologicalSpace S]
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
        have hai : a ∈ {x : Metric.closedBall (0 : Plane) 1 | x.val ∈ Metric.ball (0 : Plane) 1} := by
          change dist a.val (0 : Plane) < 1
          exact lt_of_not_ge hn
        exact Set.disjoint_left.mp he ⟨a,hai,rfl⟩ haA
      have ham : a ∈ {x : Metric.closedBall (0 : Plane) 1 | x.val ∈ Metric.sphere (0 : Plane) 1} := by
        change dist a.val (0 : Plane) = 1
        exact has
      have hab : d a ∈ d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} :=
        ⟨a,ham,rfl⟩
      rw [hb] at hab
      rcases hab with hfa | hga
      · exact hfa
      · have hc : d a ∈ ({u,z} : Set S) := hgA ▸ ⟨hga,haA⟩
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hc
        rcases hc with hc | hc
        · exact ⟨0,hf0.trans hc.symm⟩
        · exact ⟨1,hf1.trans hc.symm⟩
    · intro hx
      refine ⟨?_,hfA hx⟩
      have hxb : x ∈ d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} :=
        hb.symm ▸ Or.inl hx
      exact Set.image_subset_range _ _ hxb
  have hSymm (a b : EssentialMarkedArc M) (p : S)
      (hc : CrossesInDisk M a b p) : CrossesInDisk M b a p := by
    obtain ⟨U,hU,hp,hmark,e,he0,ha,hb⟩ := hc
    let Q := {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}
    let swap : Q ≃ₜ Q := (Homeomorph.prodComm ℝ ℝ).subtype (fun _ => and_comm)
    refine ⟨U,hU,hp,hmark,e.trans swap,?_,?_,?_⟩
    · change ((e ⟨p,hp⟩).val.2,(e ⟨p,hp⟩).val.1)=(0,0)
      rw [he0]
    · exact hb
    · exact ha
  have hfirstclean : range B.firstSide ∩ b.val.image={B.firstCorner,B.secondCorner} :=
    actual_empty_marked_bigon_first_side_clean M a b
      (fun p hp => hSymm a b p (htab p hp)) B hempty
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
  have hsecondclean : range B.secondSide ∩ a.val.image={B.firstCorner,B.secondCorner} :=
    actual_empty_marked_bigon_first_side_clean M b a
      (fun p hp => htab p (by simpa only [ArcSurgery.crossings,Set.inter_comm] using hp)) Bswap hswapempty
  have hDiskA : range B.disk ∩ a.val.image=range B.firstSide :=
    hSelectedDiskIntersection a.val.image B.firstCorner B.secondCorner B.firstSide B.secondSide
      B.first_zero B.first_one B.first_on_curve hsecondclean B.disk B.boundary_eq
      (hempty.mono_right Set.subset_union_left)
  have hDiskB : range B.disk ∩ b.val.image=range B.secondSide :=
    hSelectedDiskIntersection b.val.image B.firstCorner B.secondCorner B.secondSide B.firstSide
      B.second_zero B.second_one B.second_on_curve hfirstclean B.disk
      (B.boundary_eq.trans (Set.union_comm _ _)) (hempty.mono_right Set.subset_union_right)
  have hcornersNe : B.firstCorner ≠ B.secondCorner := by
    intro he
    have h01 : (0:Interval)=1 := B.first_embedded.injective
      (B.first_zero.trans (he.trans B.first_one.symm))
    have hh := congrArg Subtype.val h01
    norm_num at hh
  have hOrdinarySideParameters
      (hcm0 : B.firstCorner ∉ M.cover.branch) (hcm1 : B.secondCorner ∉ M.cover.branch) :
      ∃ L R : ℝ, 0 < L ∧ L < R ∧ R < 1 ∧
        range B.firstSide=(a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc L R := by
    have hfree : Disjoint (range B.firstSide) (M.cover.branch : Set S) := by
      apply Set.disjoint_left.mpr
      intro p hp hm
      have hpD : p ∈ range B.disk := image_subset_range _ _ (B.boundary_eq.symm ▸ (show p ∈ range B.firstSide ∪ range B.secondSide from Or.inl hp))
      rcases B.marks_are_corners p hpD hm with he|he
      · exact hcm0 (he ▸ hm)
      · exact hcm1 (he ▸ hm)
    exact hActualUnmarkedSideParameters a B.firstSide B.first_embedded B.first_on_curve
      (fun hp => Set.disjoint_left.mp hfree hp a.val.start_marked)
      (fun hp => Set.disjoint_left.mp hfree hp a.val.end_marked)
  have hOrdinarySelectedRetainedSupport
      (hcm0 : B.firstCorner ∉ M.cover.branch) (hcm1 : B.secondCorner ∉ M.cover.branch)
      (V : Set S) (hV : IsOpen V) (hDV : range B.disk ⊆ V) :
      ∃ A C : ℝ, ∃ K : Set S, 0 < A ∧ A < C ∧ C < 1 ∧
        (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc A C ⊆ V ∧
        IsCompact K ∧ a.val.image=
          ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc A C) ∪ K ∧
        Disjoint (range B.disk) K := by
    obtain ⟨L,R,hL,hLR,hR,hSide⟩ := hOrdinarySideParameters hcm0 hcm1
    have hFV : (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc L R ⊆ V := by
      rw [← hSide]
      intro p hp
      exact hDV ((hDiskA.symm ▸ hp).1)
    obtain ⟨A,C,K,hA,hAL,hRC,hC,hpad,hK,hfull,hSideK,hDK⟩ :=
      hActualMarkedPaddedRemainder a L R hL hLR hR V (range B.disk) hV hFV (hDiskA.trans hSide)
    exact ⟨A,C,K,hA,hAL.trans (hLR.trans hRC),hC,hpad,hK,hfull,hDK⟩
  have hActualRawMarkedSideMove
      (L R : ℝ) (hL : 0 ≤ L) (hLR : L < R) (hR : R ≤ 1)
      (hproper : 0 < L ∨ R < 1)
      (hSide : range B.firstSide=(a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc L R) :
      ∃ G : AmbientIsotopy S, ∃ c : EssentialMarkedArc M, ∃ K : Set S,
        IsCompact K ∧ a.val.image=range B.firstSide ∪ K ∧
        range B.firstSide ∩ K=({B.firstCorner,B.secondCorner} : Set S) ∧
        (∀ t x, x ∈ M.cover.branch → G.map (t,x)=x) ∧
        (∀ t x, x ∈ K → G.map (t,x)=x) ∧
        vertex M c=vertex M a ∧ c.val.image=range B.secondSide ∪ K := by
    obtain ⟨f,hfi,hf0,hf1,hf,K,hK,hfull,hmeet⟩ :=
      hActualMarkedSubarcRemainder a L R hL hLR hR hproper
    have hfSide : range f=range B.firstSide := hf.trans hSide.symm
    rw [hfSide] at hfull hmeet
    have hports : {(a.val.map ∘ Set.projIcc 0 1 zero_le_one) L,
        (a.val.map ∘ Set.projIcc 0 1 zero_le_one) R}=({B.firstCorner,B.secondCorner} : Set S) := by
      have hEndSame : range f=range B.firstSide := hfSide
      -- The shared actual carrier has exactly its two topological endpoints.
      -- Derive equality by parameter monotonicity through the honest embedding f.
      let e := hfi.toHomeomorph
      have hsub (t : Interval) : B.firstSide t ∈ range f := hEndSame.symm ▸ Set.mem_range_self t
      let α : Interval → Interval := fun t => e.symm ⟨B.firstSide t,hsub t⟩
      have hαc : Continuous α := e.symm.continuous.comp (B.firstSide.continuous.subtype_mk _)
      have hαi : Function.Injective α := by
        intro t u he
        apply B.first_embedded.injective
        have hh := congrArg Subtype.val (congrArg e he)
        simpa only [α,e.apply_symm_apply] using hh
      have hαsurj : Function.Surjective α := by
        intro t
        have ht : f t ∈ range B.firstSide := hEndSame ▸ Set.mem_range_self t
        obtain ⟨u,hu⟩ := ht
        refine ⟨u,?_⟩
        apply e.injective; apply Subtype.ext
        change (e (e.symm ⟨B.firstSide u,hsub u⟩)).val=(e t).val
        rw [e.apply_symm_apply]
        change B.firstSide u=f t
        exact hu
      rcases hαc.strictMono_of_inj_boundedOrder' hαi with hm|hm
      all_goals
        have hlow := hαsurj (0:Interval)
        have hhigh := hαsurj (1:Interval)
      · have h0 : α 0=0 := by
          obtain ⟨t,ht⟩ := hlow
          have hh := hm.monotone (show (0:Interval)≤t from bot_le)
          rw [ht] at hh
          exact le_antisymm hh bot_le
        have h1 : α 1=1 := by
          obtain ⟨t,ht⟩ := hhigh
          have hh := hm.monotone (show t≤(1:Interval) from le_top)
          rw [ht] at hh
          exact le_antisymm le_top hh
        have hp0 : f 0=B.firstCorner := by
          have he := congrArg (fun t => f t) h0
          have hαf : f (α 0)=B.firstSide 0 := congrArg Subtype.val (e.apply_symm_apply _)
          exact he.symm.trans (hαf.trans B.first_zero)
        have hp1 : f 1=B.secondCorner := by
          have he := congrArg (fun t => f t) h1
          have hαf : f (α 1)=B.firstSide 1 := congrArg Subtype.val (e.apply_symm_apply _)
          exact he.symm.trans (hαf.trans B.first_one)
        rw [← hf0,← hf1,hp0,hp1]
      · have h0 : α 0=1 := by
          obtain ⟨t,ht⟩ := hhigh
          have hh := hm.antitone (show (0:Interval)≤t from bot_le)
          rw [ht] at hh
          exact le_antisymm le_top hh
        have h1 : α 1=0 := by
          obtain ⟨t,ht⟩ := hlow
          have hh := hm.antitone (show t≤(1:Interval) from le_top)
          rw [ht] at hh
          exact le_antisymm hh bot_le
        have hp0 : f 1=B.firstCorner := by
          have he := congrArg (fun t => f t) h0
          have hαf : f (α 0)=B.firstSide 0 := congrArg Subtype.val (e.apply_symm_apply _)
          exact he.symm.trans (hαf.trans B.first_zero)
        have hp1 : f 0=B.secondCorner := by
          have he := congrArg (fun t => f t) h1
          have hαf : f (α 1)=B.firstSide 1 := congrArg Subtype.val (e.apply_symm_apply _)
          exact he.symm.trans (hαf.trans B.first_one)
        rw [← hf0,← hf1,hp0,hp1]
        exact Set.pair_comm _ _
    rw [hports] at hmeet
    have hKa : K ⊆ a.val.image := fun x hx => hfull.symm ▸ Or.inr hx
    let Q : Set S := (M.cover.branch : Set S) ∪ K
    have hQc : IsClosed Q := M.cover.branch.finite_toSet.isClosed.union hK.isClosed
    have hQboundary : ∀ x ∈ range B.firstSide ∪ range B.secondSide,
        x ∈ Q → x=B.firstCorner ∨ x=B.secondCorner := by
      intro x hx hxQ
      rcases hxQ with hxm|hxK
      · have hxD : x ∈ range B.disk := image_subset_range _ _ (B.boundary_eq.symm ▸ hx)
        exact B.marks_are_corners x hxD hxm
      · rcases hx with hxf|hxg
        · have hh : x ∈ range B.firstSide ∩ K := ⟨hxf,hxK⟩
          rw [hmeet] at hh; exact hh
        · have hh : x ∈ range B.secondSide ∩ a.val.image := ⟨hxg,hKa hxK⟩
          rw [hsecondclean] at hh; exact hh
    have hQinside : Disjoint B.openInterior Q := by
      apply Set.disjoint_left.mpr
      intro x hx hxQ
      rcases hxQ with hxm|hxK
      · have hxD : x ∈ range B.disk := image_subset_range _ _ hx
        have hc := B.marks_are_corners x hxD hxm
        have hxa : x ∈ a.val.image := by
          rcases hc with he|he
          · exact he ▸ B.first_on_curve ⟨0,B.first_zero⟩
          · exact he ▸ B.first_on_curve ⟨1,B.first_one⟩
        exact Set.disjoint_left.mp hempty hx (Or.inl hxa)
      · exact Set.disjoint_left.mp hempty hx (Or.inl (hKa hxK))
    obtain ⟨G,hGfix,hGmove⟩ := CurveComplex.HyperellipticModel.actual_raw_disk_bigon_supported_replacement
      M a b B Q hQc hQboundary hQinside
    obtain ⟨g,hg⟩ := G.homeomorphism_at (1:Interval)
    have hgfix : ∀ x, x ∈ M.cover.branch → g x=x := fun x hx => (hg x).trans (hGfix 1 x (Or.inl hx))
    let c := a.transport g hgfix
    have hfinal : G.finalMap=g := funext (fun x => (hg x).symm)
    have hclass : vertex M c=vertex M a := by
      apply Eq.symm; apply Quotient.sound
      refine ⟨G,fun t x hx => hGfix t x (Or.inl hx),?_⟩
      change G.finalMap '' a.val.image=(a.val.transport g hgfix).image
      rw [MarkedArc.transport_image,hfinal]
    have hGK : G.finalMap '' K=K := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩; simpa only [AmbientIsotopy.finalMap,hGfix _ _ (Or.inr hy)] using hy
      · intro hx; exact ⟨x,hx,hGfix 1 x (Or.inr hx)⟩
    refine ⟨G,c,K,hK,hfull,hmeet,fun t x hx => hGfix t x (Or.inl hx),
      fun t x hx => hGfix t x (Or.inr hx),hclass,?_⟩
    change (a.val.transport g hgfix).image=_
    rw [MarkedArc.transport_image,← hfinal,hfull,Set.image_union,hGmove,hGK]
  have hActualInteriorParameterHomeomorph (c : EssentialMarkedArc M) :
      ∃ e : (c.val.map ⁻¹' arcInterior M c) ≃ₜ arcInterior M c,
        ∀ t, (e t).val=c.val.map t.val := by
    let f := (arcInterior M c).restrictPreimage c.val.map
    have hf : Continuous f := (c.val.continuous.comp continuous_subtype_val).subtype_mk _
    have hfi : Function.Injective f := by
      intro t u he
      have hh : c.val.map t.val=c.val.map u.val := congrArg Subtype.val he
      rcases c.val.injective_except_loop_closure _ _ hh with hh|hh|hh
      · exact Subtype.ext hh
      · have hm : c.val.map t.val ∈ M.cover.branch := hh.1.symm ▸ c.val.start_marked
        exact (t.property.2 hm).elim
      · have hm : c.val.map t.val ∈ M.cover.branch := hh.1.symm ▸ c.val.end_marked
        exact (t.property.2 hm).elim
    have hfs : Function.Surjective f := by
      intro x
      obtain ⟨t,ht⟩ := x.property.1
      refine ⟨⟨t,?_⟩,?_⟩
      · change c.val.map t ∈ arcInterior M c
        exact ht.symm ▸ x.property
      · exact Subtype.ext ht
    have hfc : IsClosedMap f := c.val.continuous.isClosedMap.restrictPreimage _
    let q := Equiv.ofBijective f ⟨hfi,hfs⟩
    exact ⟨q.toHomeomorphOfContinuousClosed hf hfc,fun _ => rfl⟩
  have hActualSideInteriorParameters :
      ∃ α : C(Set.Ioo (0:Interval) 1,ℝ),
        Function.Injective α ∧
        (∀ t, 0 < α t ∧ α t < 1) ∧
        ∀ t, a.val.map (Set.projIcc 0 1 zero_le_one (α t))=B.firstSide t.val := by
    have hfree (t : Set.Ioo (0:Interval) 1) : B.firstSide t.val ∉ M.cover.branch := by
      intro hm
      have hpD : B.firstSide t.val ∈ range B.disk := image_subset_range _ _
        (B.boundary_eq.symm ▸ (show B.firstSide t.val ∈ range B.firstSide ∪ range B.secondSide from
          Or.inl (Set.mem_range_self t.val)))
      rcases B.marks_are_corners _ hpD hm with he|he
      · have ht : t.val=0 := B.first_embedded.injective (he.trans B.first_zero.symm)
        exact (ne_of_gt t.property.1) ht
      · have ht : t.val=1 := B.first_embedded.injective (he.trans B.first_one.symm)
        exact (ne_of_lt t.property.2) ht
    obtain ⟨e,he⟩ := hActualInteriorParameterHomeomorph a
    let point : C(Set.Ioo (0:Interval) 1,arcInterior M a) :=
      ⟨fun t => ⟨B.firstSide t.val,⟨B.first_on_curve (Set.mem_range_self _),hfree t⟩⟩,
        (B.firstSide.continuous.comp continuous_subtype_val).subtype_mk _⟩
    let α : C(Set.Ioo (0:Interval) 1,ℝ) :=
      ⟨fun t => (e.symm (point t)).val.val,
        continuous_subtype_val.comp (continuous_subtype_val.comp (e.symm.continuous.comp point.continuous))⟩
    have hαf (t : Set.Ioo (0:Interval) 1) :
        a.val.map (e.symm (point t)).val=B.firstSide t.val := by
      rw [← he]
      exact congrArg Subtype.val (e.apply_symm_apply _)
    have hαi : Function.Injective α := by
      intro t u hh
      apply Subtype.ext
      apply B.first_embedded.injective
      have hp : (e.symm (point t)).val=(e.symm (point u)).val := Subtype.ext hh
      exact (hαf t).symm.trans ((congrArg a.val.map hp).trans (hαf u))
    have hα01 (t : Set.Ioo (0:Interval) 1) : 0 < α t ∧ α t < 1 := by
      have hnot : a.val.map (e.symm (point t)).val ∉ M.cover.branch := (e.symm (point t)).property.2
      constructor
      · have hne : (e.symm (point t)).val ≠ 0 := fun he => hnot (he.symm ▸ a.val.start_marked)
        exact lt_of_le_of_ne (e.symm (point t)).val.property.1
          (fun hh => hne (Subtype.ext hh.symm))
      · have hne : (e.symm (point t)).val ≠ 1 := fun he => hnot (he.symm ▸ a.val.end_marked)
        exact lt_of_le_of_ne (e.symm (point t)).val.property.2
          (fun hh => hne (Subtype.ext hh))
    refine ⟨α,hαi,hα01,?_⟩
    intro t
    rw [Set.projIcc_of_mem zero_le_one ⟨(hα01 t).1.le,(hα01 t).2.le⟩]
    exact hαf t
  have hActualWholeSideClosedParameters :
      ∃ L R : ℝ, 0 ≤ L ∧ L < R ∧ R ≤ 1 ∧
        range B.firstSide=(a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc L R := by
    obtain ⟨α,hαi,hα01,hαf⟩ := hActualSideInteriorParameters
    letI : Nonempty (Set.Ioo (0:Interval) 1) := by
      refine ⟨⟨⟨(1/2:ℝ),by constructor <;> norm_num⟩,?_⟩⟩
      constructor
      · change (0:ℝ)<1/2; norm_num
      · change (1/2:ℝ)<1; norm_num
    letI : PreconnectedSpace (Set.Ioo (0:Interval) 1) := Subtype.preconnectedSpace isPreconnected_Ioo
    let C : Set ℝ := closure (range α)
    have hsub : C ⊆ Set.Icc (0:ℝ) 1 := by
      apply closure_minimal _ isClosed_Icc
      rintro x ⟨t,rfl⟩
      exact ⟨(hα01 t).1.le,(hα01 t).2.le⟩
    have hCc : IsCompact C := isCompact_Icc.of_isClosed_subset isClosed_closure hsub
    have hCne : C.Nonempty := (Set.range_nonempty α).mono subset_closure
    have hCconn : IsConnected C := by
      refine ⟨hCne,?_⟩
      apply IsPreconnected.closure
      simpa only [Set.image_univ] using isPreconnected_univ.image α α.continuous.continuousOn
    let L := sInf C
    let R := sSup C
    have hC : C=Set.Icc L R := eq_Icc_of_connected_compact hCconn hCc
    have hLC : L ∈ C := hCc.isClosed.csInf_mem hCne hCc.bddBelow
    have hRC : R ∈ C := hCc.isClosed.csSup_mem hCne hCc.bddAbove
    have hL : 0 ≤ L := (hsub hLC).1
    have hR : R ≤ 1 := (hsub hRC).2
    have hLR : L ≤ R := (hC ▸ hLC).2
    let γ := a.val.map ∘ Set.projIcc 0 1 zero_le_one
    have hγ : Continuous γ := a.val.continuous.comp continuous_projIcc
    have him : γ '' range α=B.firstSide '' Set.Ioo (0:Interval) 1 := by
      ext x
      constructor
      · rintro ⟨θ,⟨t,ht⟩,he⟩
        exact ⟨t.val,t.property,(hαf t).symm.trans (ht ▸ he)⟩
      · rintro ⟨t,ht,he⟩
        exact ⟨α ⟨t,ht⟩,Set.mem_range_self _,(hαf ⟨t,ht⟩).trans he⟩
    have himclosure : γ '' C=closure (γ '' range α) := by
      apply Set.Subset.antisymm
      · exact image_closure_subset_closure_image hγ
      · apply closure_minimal
        · exact Set.image_mono subset_closure
        · exact (hCc.image hγ).isClosed
    have hfclosed : IsClosedEmbedding B.firstSide :=
      B.firstSide.continuous.isClosedEmbedding B.first_embedded.injective
    have hfclosure : closure (B.firstSide '' Set.Ioo (0:Interval) 1)=range B.firstSide := by
      rw [hfclosed.closure_image_eq,closure_Ioo (by norm_num : (0:Interval) ≠ 1)]
      have hh : Set.Icc (0:Interval) 1=Set.univ := by
        ext t
        simp only [Set.mem_Icc,Set.mem_univ,iff_true]
        exact ⟨t.property.1,t.property.2⟩
      rw [hh,Set.image_univ]
    have hSide : range B.firstSide=γ '' Set.Icc L R := by
      rw [← hC,himclosure,him,hfclosure]
    have hlt : L < R := by
      apply lt_of_le_of_ne hLR
      intro he
      rw [← he,Set.Icc_self,Set.image_singleton] at hSide
      have h0 : B.firstSide 0=γ L := by
        have hh : B.firstSide 0 ∈ range B.firstSide := Set.mem_range_self (0:Interval)
        rw [hSide] at hh; exact hh
      have h1 : B.firstSide 1=γ L := by
        have hh : B.firstSide 1 ∈ range B.firstSide := Set.mem_range_self (1:Interval)
        rw [hSide] at hh; exact hh
      have h01 := B.first_embedded.injective (h0.trans h1.symm)
      have hh := congrArg Subtype.val h01
      norm_num at hh
    exact ⟨L,R,hL,hlt,hR,hSide⟩
  have hActualWholeSideProperParameters :
      ∃ L R : ℝ, 0 ≤ L ∧ L < R ∧ R ≤ 1 ∧ (0 < L ∨ R < 1) ∧
        range B.firstSide=(a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc L R := by
    obtain ⟨L,R,hL,hLR,hR,hSide⟩ := hActualWholeSideClosedParameters
    have hproper : 0 < L ∨ R < 1 := by
      by_contra hn
      have hL0 : L=0 := le_antisymm (le_of_not_gt (fun hh => hn (Or.inl hh))) hL
      have hR1 : R=1 := le_antisymm hR (le_of_not_gt (fun hh => hn (Or.inr hh)))
      have hfull : range B.firstSide=a.val.image := by
        rw [hL0,hR1] at hSide
        rw [hSide]
        ext x
        constructor
        · rintro ⟨t,ht,rfl⟩; exact Set.mem_range_self _
        · rintro ⟨t,rfl⟩
          refine ⟨t.val,t.property,?_⟩
          simp only [Function.comp_apply,Set.projIcc_of_mem zero_le_one t.property]
      obtain ⟨f,Aq,Bq,p,q,hf,hAq,hBq,hwhole,hfA,hfB,hfp,hfq,hfi⟩ :=
        actual_two_side_disk_produces_bigon_chart M a b B
      have hAc : Aq ⊆ Plane.closedSquare 0 1 := by
        intro z hz
        have hzC : z ∈ modelCurve := hwhole ▸ Or.inl hz
        exact mem_closedSquare_zero_one.mpr (by
          have hh : Plane.supNorm z=1 := hzC
          rw [hh])
      have haSquare : a.val.image ⊆ f '' Plane.closedSquare 0 1 := by
        rw [← hfull,← hfA]
        exact Set.image_mono hAc
      have hfree : ∀ z ∈ Plane.openSquare 0 1, f z ∉ M.cover.branch := by
        intro z hz hm
        have hx : f z ∈ B.openInterior := hfi ▸ Set.mem_image_of_mem f hz
        have hxD : f z ∈ range B.disk := Set.image_subset_range _ _ hx
        have hc := B.marks_are_corners _ hxD hm
        have hxa : f z ∈ a.val.image := by
          rcases hc with he|he
          · exact he ▸ B.first_on_curve ⟨0,B.first_zero⟩
          · exact he ▸ B.first_on_curve ⟨1,B.first_one⟩
        exact Set.disjoint_left.mp hempty hx (Or.inl hxa)
      have hnonloop := actual_essential_arc_in_mark_free_square_nonloop M a f hf haSquare hfree
      have hEndDisk (t : Interval) : a.val.map t ∈ range B.disk := by
        have hs : a.val.map t ∈ range B.firstSide := hfull.symm ▸ Set.mem_range_self t
        exact image_subset_range _ _ (B.boundary_eq.symm ▸
          (show a.val.map t ∈ range B.firstSide ∪ range B.secondSide from Or.inl hs))
      have h0 := B.marks_are_corners _ (hEndDisk 0) a.val.start_marked
      have h1 := B.marks_are_corners _ (hEndDisk 1) a.val.end_marked
      have hboth : B.firstCorner ∈ M.cover.branch ∧ B.secondCorner ∈ M.cover.branch := by
        rcases h0 with h0|h0 <;> rcases h1 with h1|h1
        · exact (hnonloop (h0.trans h1.symm)).elim
        · exact ⟨h0 ▸ a.val.start_marked,h1 ▸ a.val.end_marked⟩
        · exact ⟨h1 ▸ a.val.end_marked,h0 ▸ a.val.start_marked⟩
        · exact (hnonloop (h0.trans h1.symm)).elim
      rcases hhit with hh|hh
      · exact hh.1.2 hboth.1
      · exact hh.1.2 hboth.2
    exact ⟨L,R,hL,hLR,hR,hproper,hSide⟩
  obtain ⟨L,R,hL,hLR,hR,hproper,hSide⟩ := hActualWholeSideProperParameters
  obtain ⟨Graw,araw,KrawDerived,hKrawDerived,hdecompRawDerived,hmeetRawDerived,hGrawMarks,hGrawK,hclassRaw,himageRaw⟩ :=
    hActualRawMarkedSideMove L R hL hLR hR hproper hSide
  have hRawRetainedCrossings (j : J) :
      KrawDerived ∩ arcInterior M (old j)=crossings M a (old j) \ range B.firstSide := by
    have hKa : KrawDerived ⊆ a.val.image := fun x hx => hdecompRawDerived.symm ▸ Or.inr hx
    ext x
    constructor
    · rintro ⟨hxK,hxo,hxm⟩
      refine ⟨⟨⟨hKa hxK,hxm⟩,hxo,hxm⟩,?_⟩
      intro hxf
      have hxcorner : x ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hmeetRawDerived ▸ (show x ∈ range B.firstSide ∩ KrawDerived from ⟨hxf,hxK⟩)
      exact hcorners j x hxcorner hxm hxo
    · rintro ⟨⟨⟨hxa,hxm⟩,hxo,hxom⟩,hxf⟩
      refine ⟨?_,hxo,hxm⟩
      rw [hdecompRawDerived] at hxa
      exact hxa.resolve_left hxf
  have hRawSideCrossings (j : J) :
      range B.secondSide ∩ arcInterior M (old j)=
        crossings M b (old j) ∩ range B.secondSide := by
    ext x
    constructor
    · rintro ⟨hxg,hxo,hxm⟩
      exact ⟨⟨⟨B.second_on_curve hxg,hxm⟩,hxo,hxm⟩,hxg⟩
    · rintro ⟨⟨hxb,hxo⟩,hxg⟩
      exact ⟨hxg,hxo⟩
  have hRawCrossingsEquality (j : J) : crossings M araw (old j)=
      (crossings M a (old j) \ range B.firstSide) ∪
      (crossings M b (old j) ∩ range B.secondSide) := by
    change (araw.val.image \ (M.cover.branch : Set S)) ∩ arcInterior M (old j)=_
    rw [himageRaw]
    have hsplit : ((range B.secondSide ∪ KrawDerived) \ (M.cover.branch : Set S)) ∩
        arcInterior M (old j)=(range B.secondSide ∩ arcInterior M (old j)) ∪
          (KrawDerived ∩ arcInterior M (old j)) := by
      ext x
      constructor
      · rintro ⟨⟨hx,hxm⟩,hxo⟩
        exact hx.elim (fun hg => Or.inl ⟨hg,hxo⟩) (fun hK => Or.inr ⟨hK,hxo⟩)
      · rintro (⟨hg,hxo⟩|⟨hK,hxo⟩)
        · exact ⟨⟨Or.inl hg,hxo.2⟩,hxo⟩
        · exact ⟨⟨Or.inr hK,hxo.2⟩,hxo⟩
    rw [hsplit,hRawRetainedCrossings,hRawSideCrossings,Set.union_comm]
  have hRawContactCost (j : J) :
      (crossings M araw (old j)).Finite ∧
        (crossings M araw (old j)).ncard ≤
          (crossings M a (old j) \ range B.firstSide).ncard +
          (crossings M b (old j) ∩ range B.secondSide).ncard := by
    rw [hRawCrossingsEquality j]
    exact ⟨((ha j).1.subset Set.diff_subset).union
      ((hb j).1.subset Set.inter_subset_left),Set.ncard_union_le _ _⟩
  have hRawExactContactCost (j : J) :
      (crossings M araw (old j)).ncard =
        (crossings M a (old j) \ range B.firstSide).ncard +
        (crossings M b (old j) ∩ range B.secondSide).ncard := by
    rw [hRawCrossingsEquality j]
    apply Set.ncard_union_eq
    · apply Set.disjoint_left.mpr
      intro x hret hside
      have hc : x ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hsecondclean ▸ (show x ∈ range B.secondSide ∩ a.val.image from
          ⟨hside.2,hret.1.1.1⟩)
      exact hcorners j x hc hret.1.1.2 hret.1.2.1
    · exact (ha j).1.subset Set.diff_subset
    · exact (hb j).1.subset Set.inter_subset_left
  have hRawPreservesAnchorMinimum (j : J)
      (hmin : ∀ d : EssentialMarkedArc M, vertex M d=vertex M a →
        (crossings M d (old j)).Finite →
        (crossings M a (old j)).ncard ≤ (crossings M d (old j)).ncard)
      (hsideCost : (crossings M b (old j) ∩ range B.secondSide).ncard ≤
        (crossings M a (old j) ∩ range B.firstSide).ncard) :
      (crossings M araw (old j)).ncard=(crossings M a (old j)).ncard := by
    apply Nat.le_antisymm
    · calc
        (crossings M araw (old j)).ncard ≤
          (crossings M a (old j) \ range B.firstSide).ncard +
          (crossings M b (old j) ∩ range B.secondSide).ncard := (hRawContactCost j).2
        _ ≤ (crossings M a (old j) \ range B.firstSide).ncard +
          (crossings M a (old j) ∩ range B.firstSide).ncard := Nat.add_le_add_left hsideCost _
        _ = (crossings M a (old j)).ncard := by
          rw [Nat.add_comm]
          exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (ha j).1
    · exact hmin araw hclassRaw (hRawContactCost j).1
  have hMarkedLocalizedCrossingChart
      (c d : EssentialMarkedArc M) (p : S) (hp : CrossesInDisk M c d p)
      (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
      ∃ F : OpenPartialHomeomorph S (ℝ × ℝ),
        p ∈ F.source ∧ F.source ⊆ W ∧ F p=(0,0) ∧
        Disjoint F.source (M.cover.branch : Set S) ∧
        (∀ x ∈ F.source, x ∈ c.val.image ↔ (F x).2=0) ∧
        (∀ x ∈ F.source, x ∈ d.val.image ↔ (F x).1=0) := by
    obtain ⟨U,hU,hpU,hfree,e,hep,hc,hd⟩ := hp
    have : Nonempty U := ⟨⟨p,hpU⟩⟩
    let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
    have hV : IsOpen V :=
      (isOpen_lt (continuous_fst.abs) continuous_const).inter
        (isOpen_lt (continuous_snd.abs) continuous_const)
    let coeU : OpenPartialHomeomorph U S :=
      hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
    let f : U → ℝ × ℝ := fun u => (e u).val
    have hf : IsOpenEmbedding f := hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
    let coeE : OpenPartialHomeomorph U (ℝ × ℝ) := hf.toOpenPartialHomeomorph f
    let E0 := coeU.symm.trans coeE
    have hE0source : E0.source=U := by
      simp [E0,coeU,coeE,IsOpenEmbedding.toOpenPartialHomeomorph_target]
    have hE0 (x : S) (hx : x ∈ U) : E0 x=(e ⟨x,hx⟩).val := by
      have hu : coeU.symm x=⟨x,hx⟩ :=
        hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv (x := ⟨x,hx⟩)
      change f (coeU.symm x)=_
      rw [hu]
    let F := E0.restr W
    have hFs : F.source=U ∩ W := by simp [F,hW.interior_eq,hE0source]
    refine ⟨F,hFs.symm ▸ ⟨hpU,hpW⟩,?_,?_,?_,?_,?_⟩
    · intro x hx; exact (hFs.le hx).2
    · change E0 p=(0,0); exact (hE0 p hpU).trans hep
    · exact hfree.mono_left (fun x hx => (hFs.le hx).1)
    · intro x hx
      change x ∈ c.val.image ↔ (E0 x).2=0
      rw [hE0 x (hFs.le hx).1]
      exact hc ⟨x,(hFs.le hx).1⟩
    · intro x hx
      change x ∈ d.val.image ↔ (E0 x).1=0
      rw [hE0 x (hFs.le hx).1]
      exact hd ⟨x,(hFs.le hx).1⟩
  have hRawActualRetainedChart (j : J) (p : S)
      (hp : p ∈ crossings M a (old j) \ range B.firstSide) :
      ∃ F : OpenPartialHomeomorph S (ℝ × ℝ),
        p ∈ F.source ∧ F p=(0,0) ∧
        Disjoint F.source (M.cover.branch : Set S) ∧
        Disjoint F.source (range B.firstSide ∪ range B.secondSide) ∧
        (∀ x ∈ F.source, x ∈ araw.val.image ↔ (F x).2=0) ∧
        (∀ x ∈ F.source, x ∈ (old j).val.image ↔ (F x).1=0) := by
    have hpSecond : p ∉ range B.secondSide := by
      intro hps
      have hc : p ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hsecondclean ▸ (show p ∈ range B.secondSide ∩ a.val.image from ⟨hps,hp.1.1.1⟩)
      exact hcorners j p hc hp.1.1.2 hp.1.2.1
    let W : Set S := (range B.firstSide ∪ range B.secondSide)ᶜ
    have hW : IsOpen W :=
      ((isCompact_range B.firstSide.continuous).union
        (isCompact_range B.secondSide.continuous)).isClosed.isOpen_compl
    have hpW : p ∈ W := by
      rintro (hf|hs)
      · exact hp.2 hf
      · exact hpSecond hs
    obtain ⟨F,hpF,hFW,hF0,hfree,hFa,hFo⟩ :=
      hMarkedLocalizedCrossingChart a (old j) p ((ha j).2 p hp.1) W hW hpW
    refine ⟨F,hpF,hF0,hfree,Set.disjoint_left.mpr (fun x hx hs => hFW hx hs),?_,hFo⟩
    intro x hx
    have hxf : x ∉ range B.firstSide := fun hh => hFW hx (Or.inl hh)
    have hxg : x ∉ range B.secondSide := fun hh => hFW hx (Or.inr hh)
    have he : x ∈ araw.val.image ↔ x ∈ a.val.image := by
      rw [himageRaw,hdecompRawDerived]
      simp only [Set.mem_union,hxf,hxg,false_or]
    exact he.trans (hFa x hx)
  have hRawRetainedTransverse (j : J) (p : S)
      (hp : p ∈ crossings M a (old j) \ range B.firstSide) :
      CrossesInDisk M araw (old j) p := by
    obtain ⟨F,hpF,hF0,hfree,havoid,hFa,hFo⟩ := hRawActualRetainedChart j p hp
    let L : Plane ≃ₜ ℝ × ℝ :=
      ((EuclideanSpace.equiv (Fin 2) ℝ).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
    let e0 := F.trans L.symm.toOpenPartialHomeomorph
    have hs : e0.source=F.source := by
      simp [e0,OpenPartialHomeomorph.trans_source]
    have hc0 (x : S) : e0 x 0=(F x).1 := by rfl
    have hc1 (x : S) : e0 x 1=(F x).2 := by rfl
    have hz0 : e0 p 0=0 := by rw [hc0,hF0]
    have hz1 : e0 p 1=0 := by rw [hc1,hF0]
    apply hSymm
    apply actual_affine_graph_crosses_in_disk M (old j) araw e0 p
      (hs.symm ▸ hpF) (hs.symm ▸ hfree) hz0 0
    · intro x hx
      rw [hc0]
      exact hFo x (hs ▸ hx)
    · intro x hx
      rw [hz1,zero_mul,add_zero,hc1]
      exact hFa x (hs ▸ hx)
  have hOtherSideInteriorParameters :
      ∃ α : C(Set.Ioo (0:Interval) 1,ℝ),
        Function.Injective α ∧
        (∀ t, 0 < α t ∧ α t < 1) ∧
        ∀ t, b.val.map (Set.projIcc 0 1 zero_le_one (α t))=Bswap.firstSide t.val := by
    have hfree (t : Set.Ioo (0:Interval) 1) : Bswap.firstSide t.val ∉ M.cover.branch := by
      intro hm
      have hpD : Bswap.firstSide t.val ∈ range Bswap.disk := image_subset_range _ _
        (Bswap.boundary_eq.symm ▸ (show Bswap.firstSide t.val ∈ range Bswap.firstSide ∪ range Bswap.secondSide from
          Or.inl (Set.mem_range_self t.val)))
      rcases Bswap.marks_are_corners _ hpD hm with he|he
      · have ht : t.val=0 := Bswap.first_embedded.injective (he.trans Bswap.first_zero.symm)
        exact (ne_of_gt t.property.1) ht
      · have ht : t.val=1 := Bswap.first_embedded.injective (he.trans Bswap.first_one.symm)
        exact (ne_of_lt t.property.2) ht
    obtain ⟨e,he⟩ := hActualInteriorParameterHomeomorph b
    let point : C(Set.Ioo (0:Interval) 1,arcInterior M b) :=
      ⟨fun t => ⟨Bswap.firstSide t.val,⟨Bswap.first_on_curve (Set.mem_range_self _),hfree t⟩⟩,
        (Bswap.firstSide.continuous.comp continuous_subtype_val).subtype_mk _⟩
    let α : C(Set.Ioo (0:Interval) 1,ℝ) :=
      ⟨fun t => (e.symm (point t)).val.val,
        continuous_subtype_val.comp (continuous_subtype_val.comp (e.symm.continuous.comp point.continuous))⟩
    have hαf (t : Set.Ioo (0:Interval) 1) :
        b.val.map (e.symm (point t)).val=Bswap.firstSide t.val := by
      rw [← he]
      exact congrArg Subtype.val (e.apply_symm_apply _)
    have hαi : Function.Injective α := by
      intro t u hh
      apply Subtype.ext
      apply Bswap.first_embedded.injective
      have hp : (e.symm (point t)).val=(e.symm (point u)).val := Subtype.ext hh
      exact (hαf t).symm.trans ((congrArg b.val.map hp).trans (hαf u))
    have hα01 (t : Set.Ioo (0:Interval) 1) : 0 < α t ∧ α t < 1 := by
      have hnot : b.val.map (e.symm (point t)).val ∉ M.cover.branch := (e.symm (point t)).property.2
      constructor
      · have hne : (e.symm (point t)).val ≠ 0 := fun he => hnot (he.symm ▸ b.val.start_marked)
        exact lt_of_le_of_ne (e.symm (point t)).val.property.1
          (fun hh => hne (Subtype.ext hh.symm))
      · have hne : (e.symm (point t)).val ≠ 1 := fun he => hnot (he.symm ▸ b.val.end_marked)
        exact lt_of_le_of_ne (e.symm (point t)).val.property.2
          (fun hh => hne (Subtype.ext hh))
    refine ⟨α,hαi,hα01,?_⟩
    intro t
    rw [Set.projIcc_of_mem zero_le_one ⟨(hα01 t).1.le,(hα01 t).2.le⟩]
    exact hαf t
  have hOtherWholeSideClosedParameters :
      ∃ L R : ℝ, 0 ≤ L ∧ L < R ∧ R ≤ 1 ∧
        range Bswap.firstSide=(b.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc L R := by
    obtain ⟨α,hαi,hα01,hαf⟩ := hOtherSideInteriorParameters
    letI : Nonempty (Set.Ioo (0:Interval) 1) := by
      refine ⟨⟨⟨(1/2:ℝ),by constructor <;> norm_num⟩,?_⟩⟩
      constructor
      · change (0:ℝ)<1/2; norm_num
      · change (1/2:ℝ)<1; norm_num
    letI : PreconnectedSpace (Set.Ioo (0:Interval) 1) := Subtype.preconnectedSpace isPreconnected_Ioo
    let C : Set ℝ := closure (range α)
    have hsub : C ⊆ Set.Icc (0:ℝ) 1 := by
      apply closure_minimal _ isClosed_Icc
      rintro x ⟨t,rfl⟩
      exact ⟨(hα01 t).1.le,(hα01 t).2.le⟩
    have hCc : IsCompact C := isCompact_Icc.of_isClosed_subset isClosed_closure hsub
    have hCne : C.Nonempty := (Set.range_nonempty α).mono subset_closure
    have hCconn : IsConnected C := by
      refine ⟨hCne,?_⟩
      apply IsPreconnected.closure
      simpa only [Set.image_univ] using isPreconnected_univ.image α α.continuous.continuousOn
    let L := sInf C
    let R := sSup C
    have hC : C=Set.Icc L R := eq_Icc_of_connected_compact hCconn hCc
    have hLC : L ∈ C := hCc.isClosed.csInf_mem hCne hCc.bddBelow
    have hRC : R ∈ C := hCc.isClosed.csSup_mem hCne hCc.bddAbove
    have hL : 0 ≤ L := (hsub hLC).1
    have hR : R ≤ 1 := (hsub hRC).2
    have hLR : L ≤ R := (hC ▸ hLC).2
    let γ := b.val.map ∘ Set.projIcc 0 1 zero_le_one
    have hγ : Continuous γ := b.val.continuous.comp continuous_projIcc
    have him : γ '' range α=Bswap.firstSide '' Set.Ioo (0:Interval) 1 := by
      ext x
      constructor
      · rintro ⟨θ,⟨t,ht⟩,he⟩
        exact ⟨t.val,t.property,(hαf t).symm.trans (ht ▸ he)⟩
      · rintro ⟨t,ht,he⟩
        exact ⟨α ⟨t,ht⟩,Set.mem_range_self _,(hαf ⟨t,ht⟩).trans he⟩
    have himclosure : γ '' C=closure (γ '' range α) := by
      apply Set.Subset.antisymm
      · exact image_closure_subset_closure_image hγ
      · apply closure_minimal
        · exact Set.image_mono subset_closure
        · exact (hCc.image hγ).isClosed
    have hfclosed : IsClosedEmbedding Bswap.firstSide :=
      Bswap.firstSide.continuous.isClosedEmbedding Bswap.first_embedded.injective
    have hfclosure : closure (Bswap.firstSide '' Set.Ioo (0:Interval) 1)=range Bswap.firstSide := by
      rw [hfclosed.closure_image_eq,closure_Ioo (by norm_num : (0:Interval) ≠ 1)]
      have hh : Set.Icc (0:Interval) 1=Set.univ := by
        ext t
        simp only [Set.mem_Icc,Set.mem_univ,iff_true]
        exact ⟨t.property.1,t.property.2⟩
      rw [hh,Set.image_univ]
    have hSide : range Bswap.firstSide=γ '' Set.Icc L R := by
      rw [← hC,himclosure,him,hfclosure]
    have hlt : L < R := by
      apply lt_of_le_of_ne hLR
      intro he
      rw [← he,Set.Icc_self,Set.image_singleton] at hSide
      have h0 : Bswap.firstSide 0=γ L := by
        have hh : Bswap.firstSide 0 ∈ range Bswap.firstSide := Set.mem_range_self (0:Interval)
        rw [hSide] at hh; exact hh
      have h1 : Bswap.firstSide 1=γ L := by
        have hh : Bswap.firstSide 1 ∈ range Bswap.firstSide := Set.mem_range_self (1:Interval)
        rw [hSide] at hh; exact hh
      have h01 := Bswap.first_embedded.injective (h0.trans h1.symm)
      have hh := congrArg Subtype.val h01
      norm_num at hh
    exact ⟨L,R,hL,hlt,hR,hSide⟩
  have hOtherWholeSideProperParameters :
      ∃ L R : ℝ, 0 ≤ L ∧ L < R ∧ R ≤ 1 ∧ (0 < L ∨ R < 1) ∧
        range Bswap.firstSide=(b.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc L R := by
    obtain ⟨L,R,hL,hLR,hR,hSide⟩ := hOtherWholeSideClosedParameters
    have hproper : 0 < L ∨ R < 1 := by
      by_contra hn
      have hL0 : L=0 := le_antisymm (le_of_not_gt (fun hh => hn (Or.inl hh))) hL
      have hR1 : R=1 := le_antisymm hR (le_of_not_gt (fun hh => hn (Or.inr hh)))
      have hfull : range Bswap.firstSide=b.val.image := by
        rw [hL0,hR1] at hSide
        rw [hSide]
        ext x
        constructor
        · rintro ⟨t,ht,rfl⟩; exact Set.mem_range_self _
        · rintro ⟨t,rfl⟩
          refine ⟨t.val,t.property,?_⟩
          simp only [Function.comp_apply,Set.projIcc_of_mem zero_le_one t.property]
      obtain ⟨f,Aq,Bq,p,q,hf,hAq,hBq,hwhole,hfA,hfB,hfp,hfq,hfi⟩ :=
        actual_two_side_disk_produces_bigon_chart M b a Bswap
      have hAc : Aq ⊆ Plane.closedSquare 0 1 := by
        intro z hz
        have hzC : z ∈ modelCurve := hwhole ▸ Or.inl hz
        exact mem_closedSquare_zero_one.mpr (by
          have hh : Plane.supNorm z=1 := hzC
          rw [hh])
      have haSquare : b.val.image ⊆ f '' Plane.closedSquare 0 1 := by
        rw [← hfull,← hfA]
        exact Set.image_mono hAc
      have hfree : ∀ z ∈ Plane.openSquare 0 1, f z ∉ M.cover.branch := by
        intro z hz hm
        have hx : f z ∈ Bswap.openInterior := hfi ▸ Set.mem_image_of_mem f hz
        have hxD : f z ∈ range Bswap.disk := Set.image_subset_range _ _ hx
        have hc := Bswap.marks_are_corners _ hxD hm
        have hxa : f z ∈ b.val.image := by
          rcases hc with he|he
          · exact he ▸ Bswap.first_on_curve ⟨0,Bswap.first_zero⟩
          · exact he ▸ Bswap.first_on_curve ⟨1,Bswap.first_one⟩
        exact Set.disjoint_left.mp hempty hx (Or.inr hxa)
      have hnonloop := actual_essential_arc_in_mark_free_square_nonloop M b f hf haSquare hfree
      have hEndDisk (t : Interval) : b.val.map t ∈ range Bswap.disk := by
        have hs : b.val.map t ∈ range Bswap.firstSide := hfull.symm ▸ Set.mem_range_self t
        exact image_subset_range _ _ (Bswap.boundary_eq.symm ▸
          (show b.val.map t ∈ range Bswap.firstSide ∪ range Bswap.secondSide from Or.inl hs))
      have h0 := Bswap.marks_are_corners _ (hEndDisk 0) b.val.start_marked
      have h1 := Bswap.marks_are_corners _ (hEndDisk 1) b.val.end_marked
      have hboth : Bswap.firstCorner ∈ M.cover.branch ∧ Bswap.secondCorner ∈ M.cover.branch := by
        rcases h0 with h0|h0 <;> rcases h1 with h1|h1
        · exact (hnonloop (h0.trans h1.symm)).elim
        · exact ⟨h0 ▸ b.val.start_marked,h1 ▸ b.val.end_marked⟩
        · exact ⟨h1 ▸ b.val.end_marked,h0 ▸ b.val.start_marked⟩
        · exact (hnonloop (h0.trans h1.symm)).elim
      rcases hhit with hh|hh
      · exact hh.1.2 hboth.1
      · exact hh.1.2 hboth.2
    exact ⟨L,R,hL,hLR,hR,hproper,hSide⟩
  have hOtherCompactRemainder : ∃ K : Set S, IsCompact K ∧
      b.val.image=range B.secondSide ∪ K ∧
      range B.secondSide ∩ K=({B.firstCorner,B.secondCorner} : Set S) ∧
      ∃ L R : ℝ, 0 ≤ L ∧ L < R ∧ R ≤ 1 ∧ (0 < L ∨ R < 1) ∧
        range B.secondSide=(b.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc L R ∧
        {(b.val.map ∘ Set.projIcc 0 1 zero_le_one) L,
          (b.val.map ∘ Set.projIcc 0 1 zero_le_one) R}=({B.firstCorner,B.secondCorner} : Set S) := by
    obtain ⟨L,R,hL,hLR,hR,hproper,hSide⟩ := hOtherWholeSideProperParameters
    obtain ⟨f,hfi,hf0,hf1,hf,K,hK,hfull,hmeet⟩ :=
      hActualMarkedSubarcRemainder b L R hL hLR hR hproper
    have hfSide : range f=range Bswap.firstSide := hf.trans hSide.symm
    rw [hfSide] at hfull hmeet
    have hports : {(b.val.map ∘ Set.projIcc 0 1 zero_le_one) L,
        (b.val.map ∘ Set.projIcc 0 1 zero_le_one) R}=({Bswap.firstCorner,Bswap.secondCorner} : Set S) := by
      have hEndSame : range f=range Bswap.firstSide := hfSide
      -- The shared actual carrier has exactly its two topological endpoints.
      -- Derive equality by parameter monotonicity through the honest embedding f.
      let e := hfi.toHomeomorph
      have hsub (t : Interval) : Bswap.firstSide t ∈ range f := hEndSame.symm ▸ Set.mem_range_self t
      let α : Interval → Interval := fun t => e.symm ⟨Bswap.firstSide t,hsub t⟩
      have hαc : Continuous α := e.symm.continuous.comp (Bswap.firstSide.continuous.subtype_mk _)
      have hαi : Function.Injective α := by
        intro t u he
        apply Bswap.first_embedded.injective
        have hh := congrArg Subtype.val (congrArg e he)
        simpa only [α,e.apply_symm_apply] using hh
      have hαsurj : Function.Surjective α := by
        intro t
        have ht : f t ∈ range Bswap.firstSide := hEndSame ▸ Set.mem_range_self t
        obtain ⟨u,hu⟩ := ht
        refine ⟨u,?_⟩
        apply e.injective; apply Subtype.ext
        change (e (e.symm ⟨Bswap.firstSide u,hsub u⟩)).val=(e t).val
        rw [e.apply_symm_apply]
        change Bswap.firstSide u=f t
        exact hu
      rcases hαc.strictMono_of_inj_boundedOrder' hαi with hm|hm
      all_goals
        have hlow := hαsurj (0:Interval)
        have hhigh := hαsurj (1:Interval)
      · have h0 : α 0=0 := by
          obtain ⟨t,ht⟩ := hlow
          have hh := hm.monotone (show (0:Interval)≤t from bot_le)
          rw [ht] at hh
          exact le_antisymm hh bot_le
        have h1 : α 1=1 := by
          obtain ⟨t,ht⟩ := hhigh
          have hh := hm.monotone (show t≤(1:Interval) from le_top)
          rw [ht] at hh
          exact le_antisymm le_top hh
        have hp0 : f 0=Bswap.firstCorner := by
          have he := congrArg (fun t => f t) h0
          have hαf : f (α 0)=Bswap.firstSide 0 := congrArg Subtype.val (e.apply_symm_apply _)
          exact he.symm.trans (hαf.trans Bswap.first_zero)
        have hp1 : f 1=Bswap.secondCorner := by
          have he := congrArg (fun t => f t) h1
          have hαf : f (α 1)=Bswap.firstSide 1 := congrArg Subtype.val (e.apply_symm_apply _)
          exact he.symm.trans (hαf.trans Bswap.first_one)
        rw [← hf0,← hf1,hp0,hp1]
      · have h0 : α 0=1 := by
          obtain ⟨t,ht⟩ := hhigh
          have hh := hm.antitone (show (0:Interval)≤t from bot_le)
          rw [ht] at hh
          exact le_antisymm le_top hh
        have h1 : α 1=0 := by
          obtain ⟨t,ht⟩ := hlow
          have hh := hm.antitone (show t≤(1:Interval) from le_top)
          rw [ht] at hh
          exact le_antisymm hh bot_le
        have hp0 : f 1=Bswap.firstCorner := by
          have he := congrArg (fun t => f t) h0
          have hαf : f (α 0)=Bswap.firstSide 0 := congrArg Subtype.val (e.apply_symm_apply _)
          exact he.symm.trans (hαf.trans Bswap.first_zero)
        have hp1 : f 0=Bswap.secondCorner := by
          have he := congrArg (fun t => f t) h1
          have hαf : f (α 1)=Bswap.firstSide 1 := congrArg Subtype.val (e.apply_symm_apply _)
          exact he.symm.trans (hαf.trans Bswap.first_one)
        rw [← hf0,← hf1,hp0,hp1]
        exact Set.pair_comm _ _
    rw [hports] at hmeet
    exact ⟨K,hK,hfull,hmeet,L,R,hL,hLR,hR,hproper,hSide,hports⟩
  obtain ⟨Kother,hKother,hOtherDecomp,hOtherMeet,Lother,Rother,hLother,hLRother,hRother,hOtherProper,hOtherSide,hOtherPorts⟩ := hOtherCompactRemainder
  have hRawOppositeContactChart (j : J) (p : S)
      (hp : p ∈ crossings M b (old j) ∩ range B.secondSide) :
      ∃ F : OpenPartialHomeomorph S (ℝ × ℝ),
        p ∈ F.source ∧ F p=(0,0) ∧
        Disjoint F.source (M.cover.branch : Set S) ∧
        Disjoint F.source (KrawDerived ∪ Kother) ∧
        (∀ x ∈ F.source, x ∈ araw.val.image ↔ (F x).2=0) ∧
        (∀ x ∈ F.source, x ∈ (old j).val.image ↔ (F x).1=0) := by
    have hpKraw : p ∉ KrawDerived := by
      intro hk
      have hpa : p ∈ a.val.image := hdecompRawDerived.symm ▸ Or.inr hk
      have hc : p ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hsecondclean ▸ (show p ∈ range B.secondSide ∩ a.val.image from ⟨hp.2,hpa⟩)
      exact hcorners j p hc hp.1.1.2 hp.1.2.1
    have hpKother : p ∉ Kother := by
      intro hk
      have hc : p ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hOtherMeet ▸ (show p ∈ range B.secondSide ∩ Kother from ⟨hp.2,hk⟩)
      exact hcorners j p hc hp.1.1.2 hp.1.2.1
    let W : Set S := (KrawDerived ∪ Kother)ᶜ
    have hW : IsOpen W := (hKrawDerived.union hKother).isClosed.isOpen_compl
    have hpW : p ∈ W := fun h => h.elim hpKraw hpKother
    obtain ⟨F,hpF,hFW,hF0,hfree,hFb,hFo⟩ :=
      hMarkedLocalizedCrossingChart b (old j) p ((hb j).2 p hp.1) W hW hpW
    refine ⟨F,hpF,hF0,hfree,Set.disjoint_left.mpr (fun x hx hs => hFW hx hs),?_,hFo⟩
    intro x hx
    have hxK : x ∉ KrawDerived := fun hh => hFW hx (Or.inl hh)
    have hxO : x ∉ Kother := fun hh => hFW hx (Or.inr hh)
    have he : x ∈ araw.val.image ↔ x ∈ b.val.image := by
      rw [himageRaw,hOtherDecomp]
      simp only [Set.mem_union,hxK,hxO,or_false]
    exact he.trans (hFb x hx)
  have hRawOppositeTransverse (j : J) (p : S)
      (hp : p ∈ crossings M b (old j) ∩ range B.secondSide) :
      CrossesInDisk M araw (old j) p := by
    obtain ⟨F,hpF,hF0,hfree,havoid,hFa,hFo⟩ := hRawOppositeContactChart j p hp
    let L : Plane ≃ₜ ℝ × ℝ :=
      ((EuclideanSpace.equiv (Fin 2) ℝ).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
    let e0 := F.trans L.symm.toOpenPartialHomeomorph
    have hs : e0.source=F.source := by simp [e0]
    have hc0 (x : S) : e0 x 0=(F x).1 := by rfl
    have hc1 (x : S) : e0 x 1=(F x).2 := by rfl
    have hz0 : e0 p 0=0 := by rw [hc0,hF0]
    have hz1 : e0 p 1=0 := by rw [hc1,hF0]
    apply hSymm
    apply actual_affine_graph_crosses_in_disk M (old j) araw e0 p
      (hs.symm ▸ hpF) (hs.symm ▸ hfree) hz0 0
    · intro x hx
      rw [hc0]
      exact hFo x (hs ▸ hx)
    · intro x hx
      rw [hz1,zero_mul,add_zero,hc1]
      exact hFa x (hs ▸ hx)
  have hRawAllOldTransverse (j : J) :
      ∀ p ∈ crossings M araw (old j), CrossesInDisk M araw (old j) p := by
    intro p hp
    rw [hRawCrossingsEquality j] at hp
    exact hp.elim (hRawRetainedTransverse j p) (hRawOppositeTransverse j p)
  let P : Set S := ⋃ j, crossings M b (old j) ∩ range B.secondSide
  have hPfinite : P.Finite := Set.finite_iUnion (fun j =>
    (hb j).1.subset Set.inter_subset_left)
  have hPold (p : S) (hp : p ∈ P) :
      ∃ j, p ∈ crossings M b (old j) ∩ range B.secondSide := Set.mem_iUnion.mp hp
  have hPcorners : Disjoint P ({B.firstCorner,B.secondCorner} : Set S) := by
    apply Set.disjoint_left.mpr
    intro p hp hc
    obtain ⟨j,hj⟩ := hPold p hp
    exact hcorners j p hc hj.1.1.2 hj.1.2.1
  let T : Set Interval := B.secondSide ⁻¹' P
  have hTfinite : T.Finite := hPfinite.preimage B.second_embedded.injective.injOn
  have hTinterior : ∀ t ∈ T, 0 < t.val ∧ t.val < 1 := by
    intro t ht
    have h0 : t ≠ 0 := by
      intro hh
      have hp : B.firstCorner ∈ P := B.second_zero ▸ (hh ▸ ht)
      exact Set.disjoint_left.mp hPcorners hp (Set.mem_insert _ _)
    have h1 : t ≠ 1 := by
      intro hh
      have hp : B.secondCorner ∈ P := B.second_one ▸ (hh ▸ ht)
      exact Set.disjoint_left.mp hPcorners hp (by simp)
    exact ⟨lt_of_le_of_ne t.property.1 (fun hh => h0 (Subtype.ext hh.symm)),
      lt_of_le_of_ne t.property.2 (fun hh => h1 (Subtype.ext hh))⟩
  have hTuniform : ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      ∀ t ∈ T, δ < t.val ∧ t.val < 1-δ := by
    have hfiniteBound : ∀ A : Set Interval, A.Finite →
        (∀ t ∈ A, 0 < t.val ∧ t.val < 1) →
        ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧ ∀ t ∈ A, δ < t.val ∧ t.val < 1-δ := by
      intro A hA
      induction A,hA using Set.Finite.induction_on with
      | empty =>
          intro h
          refine ⟨1/4,by norm_num,by norm_num,?_⟩
          simp
      | @insert t A ht hA ih =>
          intro hi
          obtain ⟨δ,hδ,hδhalf,hbound⟩ := ih (fun u hu => hi u (Set.mem_insert_of_mem _ hu))
          have ht01 := hi t (Set.mem_insert _ _)
          let ε := min δ (min t.val (1-t.val))/2
          have hε : 0 < ε := half_pos (lt_min hδ (lt_min ht01.1 (sub_pos.mpr ht01.2)))
          have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ (min t.val (1-t.val))]
          have hεt : ε < t.val := by
            dsimp [ε]
            linarith [min_le_right δ (min t.val (1-t.val)),min_le_left t.val (1-t.val)]
          have htε : t.val < 1-ε := by
            dsimp [ε]
            linarith [min_le_right δ (min t.val (1-t.val)),min_le_right t.val (1-t.val)]
          refine ⟨ε,hε,hεδ.trans hδhalf,?_⟩
          intro u hu
          rcases Set.mem_insert_iff.mp hu with rfl|hu
          · exact ⟨hεt,htε⟩
          · have hh := hbound u hu
            exact ⟨hεδ.trans hh.1,by linarith [hh.2]⟩
    exact hfiniteBound T hTfinite hTinterior
  have hLiteralContactIncidence (j : J) :
      B.secondSide '' {t : Interval | t ∈ T ∧ B.secondSide t ∈ (old j).val.image}=
        crossings M b (old j) ∩ range B.secondSide := by
    ext p
    constructor
    · rintro ⟨t,⟨ht,hj⟩,rfl⟩
      obtain ⟨i,hi⟩ := hPold _ ht
      exact ⟨⟨hi.1.1,⟨hj,hi.1.1.2⟩⟩,Set.mem_range_self t⟩
    · intro hp
      obtain ⟨t,ht⟩ := hp.2
      refine ⟨t,⟨?_,ht ▸ hp.1.2.1⟩,ht⟩
      change B.secondSide t ∈ P
      exact ht.symm ▸ Set.mem_iUnion.mpr ⟨j,hp⟩
  have hLiteralContactIncidenceCard (j : J) :
      {t : Interval | t ∈ T ∧ B.secondSide t ∈ (old j).val.image}.ncard=
        (crossings M b (old j) ∩ range B.secondSide).ncard := by
    rw [← hLiteralContactIncidence j]
    exact (Set.ncard_image_of_injective _ B.second_embedded.injective).symm
  let r : Option J → EssentialMarkedArc M := fun i => i.elim araw old
  have hRpairFinite (i k : Option J) (hik : i ≠ k) :
      (crossings M (r i) (r k)).Finite := by
    cases i with
    | none =>
      cases k with
      | none => exact (hik rfl).elim
      | some j => exact (hRawContactCost j).1
    | some i =>
      cases k with
      | none =>
          have he : crossings M (old i) araw=crossings M araw (old i) := Set.inter_comm _ _
          exact he.symm ▸ (hRawContactCost i).1
      | some k => exact (hOld i k (fun he => hik (congrArg Option.some he))).1
  let nodes : Set S := ⋃ i : Option J, ⋃ k : Option J,
    if i=k then ∅ else crossings M (r i) (r k)
  have hNodesFinite : nodes.Finite := Set.finite_iUnion (fun i => Set.finite_iUnion (fun k => by
    split_ifs with h
    · exact Set.finite_empty
    · exact hRpairFinite i k h))
  letI : Fintype P := hPfinite.fintype
  obtain ⟨N,hN,hNdis⟩ := hPfinite.t2_separation
  have hActualContactNeighborhoods (p : P) :
      ∃ U : Set S, IsOpen U ∧ p.val ∈ U ∧ U ⊆ N p.val ∧
        Disjoint U (M.cover.branch : Set S) ∧ Disjoint U (KrawDerived ∪ Kother) ∧
        (∀ j, p.val ∉ (old j).val.image → Disjoint U (old j).val.image) ∧
        ∀ i k : Option J, i ≠ k →
          U ∩ ((r i).val.image ∩ (r k).val.image) ⊆ {p.val} := by
    obtain ⟨j,hj⟩ := hPold p.val p.property
    obtain ⟨F,hpF,hF0,hfree,hKavoid,hFa,hFo⟩ := hRawOppositeContactChart j p.val hj
    let C : Set S := ⋂ j, if p.val ∈ (old j).val.image then Set.univ else (old j).val.imageᶜ
    have hC : IsOpen C := isOpen_iInter_of_finite (fun j => by
      split_ifs
      · exact isOpen_univ
      · exact (isCompact_range (old j).val.continuous).isClosed.isOpen_compl)
    have hpC : p.val ∈ C := by
      apply Set.mem_iInter.mpr
      intro j
      split_ifs with h
      · exact Set.mem_univ _
      · exact h
    let U : Set S := ((F.source ∩ N p.val) ∩ (nodes \ {p.val})ᶜ) ∩ C
    have hU : IsOpen U :=
      ((F.open_source.inter (hN p.val).2).inter
        (hNodesFinite.subset Set.diff_subset).isClosed.isOpen_compl).inter hC
    have hpU : p.val ∈ U := by
      refine ⟨⟨⟨hpF,(hN p.val).1⟩,?_⟩,hpC⟩
      intro h
      exact h.2 (Set.mem_singleton _)
    have hUF : U ⊆ F.source := fun x hx => hx.1.1.1
    refine ⟨U,hU,hpU,(fun x hx => hx.1.1.2),hfree.mono_left hUF,
      hKavoid.mono_left hUF,?_,?_⟩
    · intro j hpj
      apply Set.disjoint_left.mpr
      intro x hx hxj
      have hh := Set.mem_iInter.mp hx.2 j
      change x ∈ (if p.val ∈ (old j).val.image then Set.univ else (old j).val.imageᶜ) at hh
      rw [if_neg hpj] at hh
      exact hh hxj
    · intro i k hik x hx
      have hxm : x ∉ M.cover.branch := fun hm => Set.disjoint_left.mp hfree (hUF hx.1) hm
      have hxn : x ∈ nodes := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
        ⟨k,by rw [if_neg hik]; exact ⟨⟨hx.2.1,hxm⟩,hx.2.2,hxm⟩⟩⟩
      by_contra hxp
      exact hx.1.1.2 ⟨hxn,hxp⟩
  choose contactU hContactUOpen hContactPoint hContactUN hContactUMarks hContactURemainders
    hContactUNonincident hContactUMeet using hActualContactNeighborhoods
  have hContactUDisjoint (p q : P) (hpq : p ≠ q) : Disjoint (contactU p) (contactU q) :=
    (hNdis p.property q.property (fun he => hpq (Subtype.ext he))).mono
      (hContactUN p) (hContactUN q)
  have hContactOnlyInNeighborhood (p : P) (q : S) (hq : q ∈ P) (hqu : q ∈ contactU p) : q=p.val := by
    by_contra hne
    have hd := hNdis p.property hq (Ne.symm hne)
    exact Set.disjoint_left.mp hd (hContactUN p hqu) (hN q).1
  let ψ : ℝ → S := B.secondSide ∘ Set.projIcc 0 1 zero_le_one
  have hψ : Continuous ψ := B.secondSide.continuous.comp continuous_projIcc
  have hActualContactCore (t : T) :
      ∃ l u : ℝ, 0 < l ∧ l < t.val.val ∧ t.val.val < u ∧ u < 1 ∧
        ψ '' Set.Icc l u ⊆ contactU ⟨B.secondSide t.val,t.property⟩ ∧
        ∀ q : Interval, q ∈ T → q.val ∈ Set.Icc l u → q=t.val := by
    let p : P := ⟨B.secondSide t.val,t.property⟩
    have htp : ψ t.val.val=p.val := by
      dsimp [ψ,p,Function.comp_def]
      rw [Set.projIcc_of_mem zero_le_one t.val.property]
    have hp : t.val.val ∈ ψ ⁻¹' contactU p := by
      change ψ t.val.val ∈ contactU p
      rw [htp]
      exact hContactPoint p
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ((hContactUOpen p).preimage hψ) t.val.val hp
    have ht01 := hTinterior t.val t.property
    let δ := min ε (min t.val.val (1-t.val.val))/2
    have hδ : 0 < δ := half_pos (lt_min hε (lt_min ht01.1 (sub_pos.mpr ht01.2)))
    have hδε : δ < ε := by dsimp [δ]; linarith [min_le_left ε (min t.val.val (1-t.val.val))]
    have hδt : δ < t.val.val := by
      dsimp [δ]
      linarith [min_le_right ε (min t.val.val (1-t.val.val)),min_le_left t.val.val (1-t.val.val)]
    have hδ1 : δ < 1-t.val.val := by
      dsimp [δ]
      linarith [min_le_right ε (min t.val.val (1-t.val.val)),min_le_right t.val.val (1-t.val.val)]
    have hsub : ψ '' Set.Icc (t.val.val-δ) (t.val.val+δ) ⊆ contactU p := by
      rintro x ⟨θ,hθ,rfl⟩
      apply hball
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith [hθ.1,hθ.2]
    refine ⟨t.val.val-δ,t.val.val+δ,by linarith,by linarith,by linarith,by linarith,hsub,?_⟩
    intro q hq hqc
    have hqψ : ψ q.val=B.secondSide q := by
      dsimp [ψ,Function.comp_def]
      rw [Set.projIcc_of_mem zero_le_one q.property]
    have hqU : B.secondSide q ∈ contactU p := hqψ ▸ hsub (Set.mem_image_of_mem ψ hqc)
    have he := hContactOnlyInNeighborhood p (B.secondSide q) hq hqU
    exact B.second_embedded.injective he
  have hMarkedGermRadialCore {I : Type} [Fintype I]
      (c : I → EssentialMarkedArc M) (p : S)
      (E0 : OpenPartialHomeomorph S Plane) (hEp : E0 p=0)
      (U : Set S) (hU : IsOpen U) (hpU : p ∈ U) (hUE : U ⊆ E0.source)
      (g : I × Bool → Interval → S)
      (hg : ∀ j, IsClosedEmbedding (g j) ∧ g j 0=p ∧ range (g j) ⊆ U)
      (hmeet : ∀ i j, i ≠ j → range (g i) ∩ range (g j)={p})
      (K : I → Set S) (hK : ∀ i, IsCompact (K i) ∧ p ∉ K i ∧
        (c i).val.image=range (g (i,false)) ∪ range (g (i,true)) ∪ K i)
      (i0 : I) :
      let γ : I × Bool → Interval → Plane := fun j => E0 ∘ g j
      ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E0 '' U),
        R.vector (i0,true) = -R.vector (i0,false) ∧
        ∀ i x, x ∈ E0.source → ‖R.H (E0 x)‖ ≤ R.coreRadius →
          (x ∈ (c i).val.image ↔ R.H (E0 x) ∈
            segment ℝ (0:Plane) (R.vector (i,false)) ∪
            segment ℝ (0:Plane) (R.vector (i,true))) := by
    let γ : I × Bool → Interval → Plane := fun j => E0 ∘ g j
    have hsource (j : I × Bool) (t : Interval) : g j t ∈ E0.source :=
      hUE ((hg j).2.2 (Set.mem_range_self t))
    have hγ (j : I × Bool) : IsClosedEmbedding (γ j) := by
      have hc : Continuous (γ j) := E0.continuousOn.comp_continuous (hg j).1.continuous
        (fun t => hsource j t)
      apply hc.isClosedEmbedding
      intro t u he
      exact (hg j).1.injective (E0.injOn (hsource j t) (hsource j u) he)
    have hγ0 (j : I × Bool) : γ j 0=0 := by
      change E0 (g j 0)=0
      rw [(hg j).2.1,hEp]
    have hγmeet (i j : I × Bool) (hij : i ≠ j) : range (γ i) ∩ range (γ j)={0} := by
      ext x
      constructor
      · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
        have he := E0.injOn (hsource i t) (hsource j u) (ht.trans hu.symm)
        have hp : g i t=p := by
          have hh : g i t ∈ range (g i) ∩ range (g j) := ⟨⟨t,rfl⟩,⟨u,he.symm⟩⟩
          rw [hmeet i j hij] at hh
          exact hh
        exact Set.mem_singleton_iff.mpr (ht.symm.trans ((congrArg E0 hp).trans hEp))
      · rintro rfl
        exact ⟨⟨0,hγ0 i⟩,⟨0,hγ0 j⟩⟩
    let bad : Set S := ⋃ i, K i
    have hBad : IsClosed bad := isClosed_iUnion_of_finite (fun i => (hK i).1.isClosed)
    have hpBad : p ∉ bad := by
      intro hp
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
      exact (hK i).2.1 hi
    let W := U \ bad
    have hW : IsOpen W := hU.sdiff hBad
    have hpW : p ∈ W := ⟨hpU,hpBad⟩
    have hWE : W ⊆ E0.source := fun x hx => hUE hx.1
    have hPlaneW : IsOpen (E0 '' W) := E0.isOpen_image_of_subset_source hW hWE
    have hzeroW : (0:Plane) ∈ E0 '' W := ⟨p,hpW,hEp⟩
    obtain ⟨R0,hRop⟩ := prescribed_pair_finite_actual_star_radialization_zero
      γ hγ hγ0 hγmeet (i0,false) (i0,true) (by simp) (E0 '' W) hPlaneW hzeroW
    let R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E0 '' U) := {R0 with
      support_subset := R0.support_subset.trans (Set.image_mono Set.diff_subset)}
    have hNotK (i : I) (x : S) (hxE : x ∈ E0.source)
        (hxN : ‖R.H (E0 x)‖ ≤ R.coreRadius) : x ∉ K i := by
      intro hxK
      have hxPlane : E0 x ∉ E0 '' W := by
        rintro ⟨y,hy,he⟩
        have hyx : y=x := E0.injOn (hWE hy) hxE he
        exact hy.2 (hyx.symm ▸ Set.mem_iUnion.mpr ⟨i,hxK⟩)
      have hxOut : E0 x ∉ Metric.ball (0:Plane) R0.supportRadius := by
        intro hx
        exact hxPlane (R0.support_subset (Metric.ball_subset_closedBall hx))
      have hxFix : R.H (E0 x)=E0 x := R0.fixes_exterior _ hxOut
      rw [hxFix] at hxN
      have hxBall : E0 x ∈ Metric.closedBall (0:Plane) R0.supportRadius := by
        rw [Metric.mem_closedBall,dist_zero_right]
        exact hxN.trans R0.core_lt_support.le
      exact hxPlane (R0.support_subset hxBall)
    refine ⟨R,hRop,?_⟩
    intro i x hxE hxN
    constructor
    · intro hx
      have hxG : x ∈ range (g (i,false)) ∪ range (g (i,true)) := by
        rw [(hK i).2.2] at hx
        exact hx.resolve_right (hNotK i x hxE hxN)
      have hrecover (sign : Bool) (hxg : x ∈ range (g (i,sign))) :
          R.H (E0 x) ∈ segment ℝ (0:Plane) (R.vector (i,sign)) := by
        obtain ⟨t,ht⟩ := hxg
        have hγx : γ (i,sign) t=E0 x := congrArg E0 ht
        have hcut : t.val ≤ (R.cut (i,sign)).val := by
          by_contra hn
          have htail : R.H (γ (i,sign) t) ∈ R.H ''
              CurveComplex.FiniteStarGeometry.tail γ (i,sign) (R.cut (i,sign)) :=
            ⟨γ (i,sign) t,⟨t,(lt_of_not_ge hn).le,rfl⟩,rfl⟩
          have hball : R.H (γ (i,sign) t) ∈ Metric.closedBall (0:Plane) R.coreRadius := by
            rw [hγx,Metric.mem_closedBall,dist_zero_right]
            exact hxN
          exact Set.disjoint_left.mp (R.excludes_tails (i,sign)) htail hball
        have hh : R.H (γ (i,sign) t) ∈ R.H ''
            CurveComplex.FiniteStarGeometry.armPrefix γ (i,sign) (R.cut (i,sign)) :=
          ⟨γ (i,sign) t,⟨t,hcut,rfl⟩,rfl⟩
        simpa only [R.prefix_image,zero_add,hγx] using hh
      exact hxG.elim (fun h => Or.inl (hrecover false h)) (fun h => Or.inr (hrecover true h))
    · intro hx
      have hrecover (sign : Bool) (hray : R.H (E0 x) ∈ segment ℝ (0:Plane) (R.vector (i,sign))) :
          x ∈ (c i).val.image := by
        have hh : R.H (E0 x) ∈ R.H ''
            CurveComplex.FiniteStarGeometry.armPrefix γ (i,sign) (R.cut (i,sign)) := by
          rw [R.prefix_image,zero_add]
          exact hray
        obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := hh
        have hEx : γ (i,sign) t=E0 x := R.H.injective he
        have hsx : g (i,sign) t=x := E0.injOn (hsource (i,sign) t) hxE hEx
        rw [(hK i).2.2]
        cases sign
        · exact Or.inl (Or.inl ⟨t,hsx⟩)
        · exact Or.inl (Or.inr ⟨t,hsx⟩)
      exact hx.elim (hrecover false) (hrecover true)
  have hMarkedNormalizeRadialCore
      {J : Type} [Fintype J] (c : J → EssentialMarkedArc M) (p : S)
      (E : OpenPartialHomeomorph S Plane) (hpE : p ∈ E.source) (hEp : E p = 0)
      (γ : (J × Bool) → CurveComplex.Interval → Plane)
      (R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E '' E.source)) (j₀ : J)
      (hop : R.vector (j₀,true) = -R.vector (j₀,false)) (β : Bool)
      (hcore : ∀ j x, x ∈ E.source → ‖R.H (E x)‖ ≤ R.coreRadius →
        (x ∈ (c j).val.image ↔ R.H (E x) ∈ segment ℝ (0 : Plane) (R.vector (j,false)) ∪
          segment ℝ (0 : Plane) (R.vector (j,true)))) :
      ∃ T : Plane ≃L[ℝ] Plane, ∃ F : OpenPartialHomeomorph S Plane, ∃ ρ : ℝ,
        F.source = E.source ∧ F p = 0 ∧ 0 < ρ ∧ ρ < 1 ∧
        (∀ x, F x = T (R.H (E x))) ∧ T (R.vector (j₀,β)) = Plane.mk 1 0 ∧
        (∀ x, ‖F x‖ < ρ → ‖R.H (E x)‖ ≤ R.coreRadius) ∧
        (∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ (c j₀).val.image ↔ F x 1 = 0)) ∧
        (∀ j x, x ∈ F.source → ‖F x‖ < ρ →
          (x ∈ (c j).val.image ↔ F x ∈ segment ℝ (0 : Plane) (T (R.vector (j,false))) ∪
            segment ℝ (0 : Plane) (T (R.vector (j,true))))) := by
    classical
    have hLinear (v : Plane) (hv : v ≠ 0) :
        ∃ T : Plane ≃L[ℝ] Plane, T v = Plane.mk 1 0 ∧
          T (-v) = Plane.mk (-1) 0 ∧ ∀ t : ℝ, T (t • v) = Plane.mk t 0 := by
      let L : ℂ ≃L[ℝ] Plane := Complex.equivRealProdCLM.trans
        ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm)
      let ζ : ℂ := L.symm v
      have hζ : ζ ≠ 0 := by
        intro hz
        apply hv
        have hh := congrArg L hz
        simpa [ζ] using hh
      let M : ℂ ≃L[ℂ] ℂ := (LinearEquiv.smulOfNeZero ℂ ℂ ζ⁻¹ (inv_ne_zero hζ)).toContinuousLinearEquiv
      let T : Plane ≃L[ℝ] Plane := L.symm.trans ((M.restrictScalars ℝ).trans L)
      have hTv : T v = Plane.mk 1 0 := by
        change L (ζ⁻¹ * ζ) = Plane.mk 1 0
        rw [inv_mul_cancel₀ hζ]
        rfl
      refine ⟨T,hTv,?_,?_⟩
      · rw [map_neg,hTv]
        ext i
        fin_cases i <;> simp [Plane.mk]
      · intro t
        rw [map_smul,hTv]
        ext i
        fin_cases i <;> simp [Plane.mk]
    obtain ⟨T,hTv,hTneg,hTline⟩ := hLinear (R.vector (j₀,β)) (R.vector_nonzero (j₀,β))
    let F := E.transHomeomorph (R.H.trans T.toHomeomorph)
    have hFp : F p = 0 := by
      change T (R.H (E p)) = 0
      rw [hEp,R.fixes_center,map_zero]
    have hOpen : IsOpen (T.symm ⁻¹' Metric.ball (0 : Plane) R.coreRadius) :=
      isOpen_ball.preimage T.symm.continuous
    have h0 : (0 : Plane) ∈ T.symm ⁻¹' Metric.ball (0 : Plane) R.coreRadius := by
      change T.symm 0 ∈ Metric.ball (0 : Plane) R.coreRadius
      rw [map_zero]
      simpa using R.core_pos
    obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp hOpen 0 h0
    let ρ := min r 1 / 2
    have hρ : 0 < ρ := half_pos (lt_min hr zero_lt_one)
    have hρr : ρ < r := by dsimp [ρ]; linarith [min_le_left r 1]
    have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [min_le_right r 1]
    have hCoreNorm (x : S) (hx : ‖F x‖ < ρ) : ‖R.H (E x)‖ ≤ R.coreRadius := by
      have hh : T.symm (F x) ∈ Metric.ball (0 : Plane) R.coreRadius :=
        hBall (Metric.mem_ball.mpr (by rw [dist_zero_right]; exact hx.trans hρr))
      change T.symm (T (R.H (E x))) ∈ Metric.ball (0 : Plane) R.coreRadius at hh
      rw [T.symm_apply_apply,Metric.mem_ball,dist_zero_right] at hh
      exact hh.le
    have hSegment (v z : Plane) : z ∈ segment ℝ (0 : Plane) v ↔
        T z ∈ segment ℝ (0 : Plane) (T v) := by
      have hi := image_segment ℝ T.toLinearMap.toAffineMap (0 : Plane) v
      change T '' segment ℝ (0 : Plane) v = segment ℝ (T 0) (T v) at hi
      rw [map_zero] at hi
      rw [← hi]
      exact ⟨fun hz => ⟨z,hz,rfl⟩,fun ⟨w,hw,he⟩ => (T.injective he) ▸ hw⟩
    have hModel (j : J) (x : S) (hxE : x ∈ F.source) (hxN : ‖F x‖ < ρ) :
        x ∈ (c j).val.image ↔ F x ∈ segment ℝ (0 : Plane) (T (R.vector (j,false))) ∪
          segment ℝ (0 : Plane) (T (R.vector (j,true))) := by
      rw [hcore j x hxE (hCoreNorm x hxN)]
      exact or_congr (hSegment _ _) (hSegment _ _)
    have hAxisModel (z : Plane) (hz : ‖z‖ < 1) :
        z ∈ segment ℝ (0 : Plane) (Plane.mk 1 0) ∪ segment ℝ (0 : Plane) (Plane.mk (-1) 0) ↔ z 1 = 0 := by
      constructor
      · intro hseg
        have hzero (v : Plane) (hv : v 1 = 0) (hz : z ∈ segment ℝ (0 : Plane) v) : z 1 = 0 := by
          rw [segment_eq_image'] at hz
          obtain ⟨t,ht,he⟩ := hz
          have hh := congrArg (fun z : Plane => z 1) he
          change 0+t*(v 1-0) = z 1 at hh
          rw [hv] at hh
          simpa using hh.symm
        exact hseg.elim (hzero _ rfl) (hzero _ rfl)
      · intro hz1
        have hxabs : |z 0| < 1 := (show ‖z 0‖ ≤ ‖z‖ from PiLp.norm_apply_le z 0).trans_lt hz
        by_cases hx : 0 ≤ z 0
        · left
          rw [segment_eq_image']
          refine ⟨z 0,⟨hx,(abs_lt.mp hxabs).2.le⟩,?_⟩
          ext i
          fin_cases i <;> simp [Plane.mk,hz1]
        · right
          rw [segment_eq_image']
          refine ⟨-z 0,⟨by linarith,(by linarith [(abs_lt.mp hxabs).1])⟩,?_⟩
          ext i
          fin_cases i <;> simp [Plane.mk,hz1]
    refine ⟨T,F,ρ,rfl,hFp,hρ,hρ1,(fun _ => rfl),hTv,hCoreNorm,?_,hModel⟩
    intro x hxE hxN
    cases β
    · rw [hModel j₀ x hxE hxN,hop,hTv,hTneg]
      exact hAxisModel _ (hxN.trans hρ1)
    · have hrev : R.vector (j₀,false) = -R.vector (j₀,true) := by rw [hop,neg_neg]
      rw [hModel j₀ x hxE hxN,hrev,hTneg,hTv,Set.union_comm]
      exact hAxisModel _ (hxN.trans hρ1)
  have hMarkedCrossingCannotStayInHalf
      (c d : EssentialMarkedArc M) (p : S) (hc : CrossesInDisk M c d p)
      (E : OpenPartialHomeomorph S Plane) (hpE : p ∈ E.source) (hEp : E p = 0)
      (ρ σ : ℝ) (hρ : 0 < ρ)
      (haxis : ∀ x ∈ E.source, ‖E x‖ < ρ → (x ∈ c.val.image ↔ E x 1 = 0))
      (hhalf : ∀ x ∈ E.source, ‖E x‖ < ρ → x ∈ d.val.image → x ≠ p → 0 < σ * E x 1) : False := by
    classical
    have hCrossChart : ∃ U : Set S, ∃ V : Set (ℝ × ℝ), ∃ hpU : p ∈ U,
        ∃ h : U ≃ₜ V, IsOpen U ∧ IsOpen V ∧ (h ⟨p,hpU⟩).val=(0,0) ∧
          ∀ x (hx : x ∈ U),
            (x ∈ c.val.image ↔ (h ⟨x,hx⟩).val.1=0) ∧
            (x ∈ d.val.image ↔ (h ⟨x,hx⟩).val.2=0) := by
      obtain ⟨U,hU,hpU,hmarks,e,he0,hcA,hdA⟩ := hc
      let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
      let swap : V ≃ₜ V := (Homeomorph.prodComm ℝ ℝ).subtype (fun _ => and_comm)
      have hV : IsOpen V :=
        (isOpen_lt continuous_fst.abs continuous_const).inter
          (isOpen_lt continuous_snd.abs continuous_const)
      refine ⟨U,V,hpU,e.trans swap,hU,hV,?_,?_⟩
      · change ((e ⟨p,hpU⟩).val.2,(e ⟨p,hpU⟩).val.1)=(0,0)
        rw [he0]
      · intro x hx
        exact ⟨hcA ⟨x,hx⟩,hdA ⟨x,hx⟩⟩
    obtain ⟨U,V,hpU,h,hU,hV,hpH,haxes⟩ := hCrossChart
    have hQ : IsOpen (E.source ∩ U) := E.open_source.inter hU
    have hImageQ : IsOpen (E '' (E.source ∩ U)) := E.isOpen_image_of_subset_source hQ Set.inter_subset_left
    have h0ImageQ : (0 : Plane) ∈ E '' (E.source ∩ U) := ⟨p,⟨hpE,hpU⟩,hEp⟩
    obtain ⟨r₀,hr₀,hr₀Q⟩ := Metric.isOpen_iff.mp hImageQ 0 h0ImageQ
    let r := min r₀ ρ / 2
    have hr : 0 < r := half_pos (lt_min hr₀ hρ)
    have hrr₀ : r < r₀ := by dsimp [r]; linarith [min_le_left r₀ ρ]
    have hrρ : r < ρ := by dsimp [r]; linarith [min_le_right r₀ ρ]
    have hBallData (y : Plane) (hy : y ∈ Metric.ball (0 : Plane) r) :
        y ∈ E.target ∧ E.symm y ∈ U ∧ E.symm y ∈ E.source := by
      obtain ⟨x,hx,hxy⟩ := hr₀Q (Metric.ball_subset_ball hrr₀.le hy)
      have hyT : y ∈ E.target := hxy ▸ E.map_source hx.1
      have he : E.symm y = x := by rw [← hxy]; exact E.left_inv hx.1
      exact ⟨hyT,he ▸ hx.2,he ▸ hx.1⟩
    let P : Set Plane := Metric.ball (0 : Plane) r ∩ {y | 0 < σ * y 1}
    have hP : IsPreconnected P := (convex_ball (0 : Plane) r).inter
      (convex_halfSpace_gt (𝕜 := ℝ) (f := fun y : Plane => σ * y 1)
        ⟨by intros x y; change σ * (x 1 + y 1) = σ*x 1 + σ*y 1; ring,
         by intros a x; change σ * (a*x 1) = a*(σ*x 1); ring⟩ 0) |>.isPreconnected
    have hPU (y : P) : E.symm y.val ∈ U := (hBallData y.val y.property.1).2.1
    let Q : P → U := fun y => ⟨E.symm y.val,hPU y⟩
    have hQc : Continuous Q := (E.symm.continuousOn.comp_continuous continuous_subtype_val
      (fun y => (hBallData y.val y.property.1).1)).subtype_mk _
    let F : P → ℝ := fun y => ((h (Q y) : V) : ℝ × ℝ).1
    have hF : Continuous F := continuous_fst.comp
      (continuous_subtype_val.comp (h.continuous.comp hQc))
    have hFne (y : P) : F y ≠ 0 := by
      intro he
      have hcX : E.symm y.val ∈ c.val.image := (haxes _ (hPU y)).1.mpr he
      have hxy : E (E.symm y.val) = y.val := E.right_inv (hBallData y.val y.property.1).1
      have hyρ : ‖E (E.symm y.val)‖ < ρ := by
        rw [hxy]
        have hh : ‖y.val‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using y.property.1
        exact hh.trans hrρ
      have hy0 := (haxis _ (hBallData y.val y.property.1).2.2 hyρ).mp hcX
      rw [hxy] at hy0
      have hh := y.property.2
      change 0 < σ * y.val 1 at hh
      rw [hy0,mul_zero] at hh
      exact (lt_irrefl 0) hh
    let O : Set V := (fun y : V => (h.symm y : S)) ⁻¹'
      (E.source ∩ E ⁻¹' Metric.ball (0 : Plane) r)
    have hO : IsOpen O := (E.isOpen_inter_preimage isOpen_ball).preimage
      (continuous_subtype_val.comp h.symm.continuous)
    have hGlobalO : IsOpen (Subtype.val '' O : Set (ℝ × ℝ)) := hV.isOpenEmbedding_subtypeVal.isOpenMap _ hO
    have h0O : ((0,0) : ℝ × ℝ) ∈ Subtype.val '' O := by
      refine ⟨h ⟨p,hpU⟩,?_,hpH⟩
      change (h.symm (h ⟨p,hpU⟩) : S) ∈ E.source ∩ E ⁻¹' Metric.ball (0 : Plane) r
      simp only [h.symm_apply_apply]
      exact ⟨hpE,by change E p ∈ Metric.ball (0 : Plane) r; rw [hEp]; simpa using hr⟩
    obtain ⟨δ,hδ,hδO⟩ := Metric.isOpen_iff.mp hGlobalO (0,0) h0O
    have hpm (s : ℝ) (hs : s = -δ/2 ∨ s = δ/2) : (s,0) ∈ Metric.ball (0 : ℝ × ℝ) δ := by
      rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
      constructor
      · rw [Real.dist_eq]
        change |s-0| < δ
        rw [sub_zero]
        rcases hs with rfl | rfl <;> rw [abs_div] <;> simp [abs_of_pos hδ,abs_of_neg (neg_neg_of_pos hδ)] <;> linarith
      · simpa using hδ
    have hPoint (s : ℝ) (hs : s = -δ/2 ∨ s = δ/2) :
        ∃ y : P, F y = s := by
      obtain ⟨v,hv,hvs⟩ := hδO (hpm s hs)
      have hxE : (h.symm v : S) ∈ E.source := hv.1
      have hxBall : E (h.symm v : S) ∈ Metric.ball (0 : Plane) r := hv.2
      have hxNr : ‖E (h.symm v : S)‖ < r := by
        simpa only [Metric.mem_ball,dist_zero_right] using hxBall
      have hxN : ‖E (h.symm v : S)‖ < ρ := hxNr.trans hrρ
      have hHvalue : ((h ⟨(h.symm v : S),(h.symm v).property⟩ : V) : ℝ × ℝ) = (s,0) := by
        simpa using hvs
      have hxd : (h.symm v : S) ∈ d.val.image := (haxes _ (h.symm v).property).2.mpr (by rw [hHvalue])
      have hxp : (h.symm v : S) ≠ p := by
        intro he
        have hv0 : ((h ⟨(h.symm v : S),(h.symm v).property⟩ : V) : ℝ × ℝ) = (0,0) := by
          convert hpH using 1
          congr 2
          exact Subtype.ext he
        have hs0 : s = 0 := congrArg Prod.fst (hHvalue.symm.trans hv0)
        rcases hs with hs | hs <;> linarith
      have hxUp := hhalf _ hxE hxN hxd hxp
      let y : P := ⟨E (h.symm v : S),⟨hxBall,hxUp⟩⟩
      refine ⟨y,?_⟩
      have hQy : Q y = h.symm v := by
        apply Subtype.ext
        exact E.left_inv hxE
      change ((h (Q y) : V) : ℝ × ℝ).1 = s
      rw [hQy]
      simpa using congrArg Prod.fst hvs
    obtain ⟨yn,hyn⟩ := hPoint (-δ/2) (Or.inl rfl)
    obtain ⟨yp,hyp⟩ := hPoint (δ/2) (Or.inr rfl)
    have hRangeConn : IsPreconnected (Set.range F) := by
      have : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp hP
      exact isPreconnected_range hF
    have hRangeSub : Set.range F ⊆ Set.Iio 0 ∪ Set.Ioi 0 := by
      rintro x ⟨y,rfl⟩
      exact lt_or_gt_of_ne (hFne y)
    have hLeft : Set.range F ⊆ Set.Iio 0 :=
      hRangeConn.subset_left_of_subset_union isOpen_Iio isOpen_Ioi
        (Set.disjoint_left.mpr (by intro x hx hy; change x < 0 at hx; change 0 < x at hy; linarith)) hRangeSub
        ⟨F yn,⟨⟨yn,rfl⟩,by change F yn < 0; rw [hyn]; linarith⟩⟩
    have hbad := hLeft ⟨yp,rfl⟩
    change F yp < 0 at hbad
    rw [hyp] at hbad
    linarith
  have hMarkedCrossingSigns
      (c d : EssentialMarkedArc M) (p : S) (hc : CrossesInDisk M c d p)
      (E : OpenPartialHomeomorph S Plane) (hpE : p ∈ E.source) (hEp : E p = 0)
      (ρ : ℝ) (hρ : 0 < ρ) (a b : Plane)
      (haxis : ∀ x ∈ E.source, ‖E x‖ < ρ → (x ∈ c.val.image ↔ E x 1 = 0))
      (hmeet : ∀ x ∈ E.source, x ∈ c.val.image ∩ d.val.image → x = p)
      (hmodel : ∀ x ∈ E.source, ‖E x‖ < ρ → x ∈ d.val.image →
        E x ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b) : a 1 * b 1 < 0 := by
    by_contra hn
    have hprod : 0 ≤ a 1 * b 1 := le_of_not_gt hn
    have hchoice : ∃ σ : ℝ, σ ≠ 0 ∧ 0 ≤ σ*a 1 ∧ 0 ≤ σ*b 1 := by
      by_cases ha : 0 ≤ a 1
      · by_cases hb : 0 ≤ b 1
        · exact ⟨1,one_ne_zero,by simpa,by simpa⟩
        · have hblt : b 1 < 0 := lt_of_not_ge hb
          have hale : a 1 ≤ 0 := by nlinarith
          exact ⟨-1,neg_ne_zero.mpr one_ne_zero,by nlinarith,by nlinarith⟩
      · have halt : a 1 < 0 := lt_of_not_ge ha
        have hble : b 1 ≤ 0 := by nlinarith
        exact ⟨-1,neg_ne_zero.mpr one_ne_zero,by nlinarith,by nlinarith⟩
    obtain ⟨σ,hσ,ha,hb⟩ := hchoice
    apply hMarkedCrossingCannotStayInHalf c d p hc E hpE hEp ρ σ hρ haxis
    intro x hxE hxρ hxd hxp
    have hRayNN (v : Plane) (hv : 0 ≤ σ*v 1) (hx : E x ∈ segment ℝ (0 : Plane) v) :
        0 ≤ σ*E x 1 := by
      rw [segment_eq_image'] at hx
      obtain ⟨t,ht,he⟩ := hx
      have hh := congrArg (fun z : Plane => z 1) he
      change 0 + t*(v 1-0) = E x 1 at hh
      have hmul := mul_nonneg ht.1 hv
      calc
        0 ≤ t*(σ*v 1) := hmul
        _ = σ*E x 1 := by rw [← hh]; ring
    have hxNN : 0 ≤ σ*E x 1 := (hmodel x hxE hxρ hxd).elim (hRayNN a ha) (hRayNN b hb)
    apply lt_of_le_of_ne hxNN
    intro he
    have hx0 : E x 1 = 0 := (mul_eq_zero.mp he.symm).resolve_left hσ
    have hxc : x ∈ c.val.image := (haxis x hxE hxρ).mpr hx0
    exact hxp (hmeet x hxE ⟨hxc,hxd⟩)
  have hActualSourceContactRadialCore (p : P) (V : Set S) (hV : IsOpen V) (hpV : p.val ∈ V) :
      let I := {i : Option J // p.val ∈ (r i).val.image}
      let c : I → EssentialMarkedArc M := fun i => r i.val
      ∃ E0 : OpenPartialHomeomorph S Plane,
        p.val ∈ E0.source ∧ E0.source ⊆ contactU p ∩ V ∧
        Disjoint E0.source (M.cover.branch : Set S) ∧ E0 p.val=0 ∧
        ∃ g : I × Bool → Interval → S,
        ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => E0 ∘ g j) 0 (E0 '' E0.source),
        ∃ i0 : I, i0.val=none ∧ R.vector (i0,true) = -R.vector (i0,false) ∧
        ∀ i x, x ∈ E0.source → ‖R.H (E0 x)‖ ≤ R.coreRadius →
          (x ∈ (c i).val.image ↔ R.H (E0 x) ∈
            segment ℝ (0:Plane) (R.vector (i,false)) ∪
            segment ℝ (0:Plane) (R.vector (i,true))) := by
    let I := {i : Option J // p.val ∈ (r i).val.image}
    let c : I → EssentialMarkedArc M := fun i => r i.val
    have hpRaw : p.val ∈ araw.val.image := by
      obtain ⟨j,hj⟩ := hPold p.val p.property
      exact himageRaw.symm ▸ Or.inl hj.2
    let i0 : I := ⟨none,hpRaw⟩
    letI : Nonempty I := ⟨i0⟩
    obtain ⟨j,hj⟩ := hPold p.val p.property
    have hpcross : p.val ∈ crossings M araw (old j) := ⟨⟨hpRaw,hj.1.1.2⟩,hj.1.2⟩
    obtain ⟨F,hpF,hFU,hF0,hFmark,hFa,hFo⟩ :=
      hMarkedLocalizedCrossingChart araw (old j) p.val (hRawAllOldTransverse j p.val hpcross)
        (contactU p ∩ V) ((hContactUOpen p).inter hV) ⟨hContactPoint p,hpV⟩
    let L : Plane ≃ₜ ℝ × ℝ :=
      ((EuclideanSpace.equiv (Fin 2) ℝ).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
    let E0 := F.trans L.symm.toOpenPartialHomeomorph
    have hs : E0.source=F.source := by simp [E0]
    have hpE : p.val ∈ E0.source := hs.symm ▸ hpF
    have hEU : E0.source ⊆ contactU p ∩ V := hs.symm ▸ hFU
    have hEmark : Disjoint E0.source (M.cover.branch : Set S) := hs.symm ▸ hFmark
    have hE0 : E0 p.val=0 := by
      change L.symm (F p.val)=0
      rw [hF0]
      ext i
      fin_cases i <;> rfl
    have hpfree : p.val ∉ M.cover.branch := fun hm => Set.disjoint_left.mp hEmark hpE hm
    have hcfinite (i k : I) (hik : i ≠ k) : (crossings M (c i) (c k)).Finite :=
      hRpairFinite i.val k.val (fun he => hik (Subtype.ext he))
    obtain ⟨τ,ε,hε,hτ,hg,hmeet,hK⟩ := actual_marked_interior_contact_fan_preprocessing M c p.val
      hpfree (fun i => i.property) hcfinite E0.source E0.open_source hpE
    let g : I × Bool → Interval → S := fun j t =>
      (c j.1).val.map (Set.projIcc 0 1 zero_le_one
        (if j.2 then (τ j.1 : ℝ)+ε*(t : ℝ) else (τ j.1 : ℝ)-ε*(t : ℝ)))
    let K : I → Set S := fun i => (c i).val.map ''
      {t : Interval | (t : ℝ) ≤ (τ i : ℝ)-ε ∨ (τ i : ℝ)+ε ≤ (t : ℝ)}
    obtain ⟨R,hRop,hmodel⟩ := hMarkedGermRadialCore c p.val E0 hE0 E0.source
      E0.open_source hpE (fun _ h => h) g hg hmeet K hK i0
    exact ⟨E0,hpE,hEU,hEmark,hE0,g,R,i0,rfl,hRop,hmodel⟩
  have hMarkedActualFanPatch {I D : Type} [Fintype I] [Fintype D]
      (c : I → EssentialMarkedArc M) (p : S)
      (E0 : OpenPartialHomeomorph S Plane) (hpE : p ∈ E0.source) (hE0 : E0 p=0)
      (hmarks : Disjoint E0.source (M.cover.branch : Set S))
      (γ : I × Bool → Interval → Plane)
      (R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E0 '' E0.source))
      (i0 : I) (hop : R.vector (i0,true) = -R.vector (i0,false))
      (hcore : ∀ i x, x ∈ E0.source → ‖R.H (E0 x)‖ ≤ R.coreRadius →
        (x ∈ (c i).val.image ↔ R.H (E0 x) ∈
          segment ℝ (0:Plane) (R.vector (i,false)) ∪
          segment ℝ (0:Plane) (R.vector (i,true))))
      (label : D → I)
      (hcross : ∀ j, CrossesInDisk M (c i0) (c (label j)) p)
      (hmeet : ∀ j x, x ∈ E0.source → x ∈ (c i0).val.image ∩ (c (label j)).val.image → x=p) :
      ∃ F : OpenPartialHomeomorph S Plane, ∃ δ H : ℝ,
        F.source ⊆ E0.source ∧ Disjoint F.source (M.cover.branch : Set S) ∧
        0 < δ ∧ 0 < H ∧ ∀ h : ℝ, 0 < h → h < H →
        ∃ f : C(Interval,S), IsEmbedding f ∧ range f ⊆ F.source ∧
          range f=F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          f 0=F.symm (Plane.mk (-δ) h) ∧ f 1=F.symm (Plane.mk δ h) ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧
          Disjoint (range f) (c i0).val.image ∧ ∀ j,
            f 0 ∉ (c (label j)).val.image ∧ f 1 ∉ (c (label j)).val.image ∧
            (range f ∩ (c (label j)).val.image).Finite ∧
            (range f ∩ (c (label j)).val.image).ncard ≤ 1 := by
    obtain ⟨T,F0,ρ,hs,hFp,hρ,hρ1,hFformula,hTv,hCoreNorm,hAxis,hModel⟩ :=
      hMarkedNormalizeRadialCore c p E0 hpE hE0 γ R i0 hop false hcore
    have hSign (j : D) : (T (R.vector (label j,false))) 1 * (T (R.vector (label j,true))) 1 < 0 :=
      hMarkedCrossingSigns (c i0) (c (label j)) p (hcross j) F0 (hs.symm ▸ hpE) hFp ρ hρ
        (T (R.vector (label j,false))) (T (R.vector (label j,true))) hAxis
        (fun x hx => hmeet j x (hs ▸ hx))
        (fun x hx hn hd => (hModel (label j) x hx hn).mp hd)
    let a : D → Plane := fun j => if 0 < (T (R.vector (label j,false))) 1
      then T (R.vector (label j,false)) else T (R.vector (label j,true))
    let b : D → Plane := fun j => if 0 < (T (R.vector (label j,false))) 1
      then T (R.vector (label j,true)) else T (R.vector (label j,false))
    have ha (j : D) : 0 < a j 1 := by
      dsimp [a]
      split_ifs with hh
      · exact hh
      · nlinarith [hSign j]
    have hb (j : D) : b j 1 < 0 := by
      dsimp [b]
      split_ifs with hh
      · nlinarith [hSign j]
      · have hne : (T (R.vector (label j,false))) 1 ≠ 0 := by
          intro he
          have hh := hSign j
          rw [he,zero_mul] at hh
          exact (lt_irrefl 0) hh
        exact lt_of_le_of_ne (le_of_not_gt hh) hne
    let F := F0.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0:Plane) ρ) isOpen_ball)
    have hFs : F.source=F0.source ∩ F0 ⁻¹' Metric.ball (0:Plane) ρ := by
      simp [F,OpenPartialHomeomorph.trans_source]
    have hFv (x : S) : F x=F0 x := rfl
    have hFsub : F.source ⊆ E0.source := fun x hx => hs ▸ (hFs ▸ hx).1
    have hpF : p ∈ F.source := by
      rw [hFs]
      refine ⟨hs.symm ▸ hpE,?_⟩
      change F0 p ∈ Metric.ball (0:Plane) ρ
      rw [hFp]
      simpa using hρ
    have hzeroTarget : (0:Plane) ∈ F.target := by
      have hh := F.map_source hpF
      rw [hFv,hFp] at hh
      exact hh
    obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp F.open_target 0 hzeroTarget
    have hFmark : Disjoint F.source (M.cover.branch : Set S) := hmarks.mono_left hFsub
    have hFaxis (x : S) (hx : x ∈ F.source) : x ∈ (c i0).val.image ↔ F x 1=0 := by
      have hh := hFs ▸ hx
      rw [hFv]
      exact hAxis x hh.1 (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hh.2)
    have hFmodel (j : D) (x : S) (hx : x ∈ F.source) (hn : F x ∈ Metric.ball (0:Plane) η) :
        x ∈ (c (label j)).val.image ↔ F x ∈ segment ℝ (0:Plane) (a j) ∪ segment ℝ (0:Plane) (b j) := by
      have hh := hFs ▸ hx
      have hhN : ‖F0 x‖ < ρ := by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hh.2
      rw [hFv]
      dsimp [a,b]
      split_ifs
      · exact hModel (label j) x hh.1 hhN
      · rw [Set.union_comm]
        exact hModel (label j) x hh.1 hhN
    obtain ⟨δ,H,hδ,hH,_hleft0,_hright0,_hsegments,hpatch⟩ := hMarkedUniformContactPatch (fun j => c (label j)) (c i0)
      F hFmark η hη hball hFaxis a b ha hb hFmodel
    refine ⟨F,δ,H,hFsub,hFmark,hδ,hH,?_⟩
    intro h hh hhH
    obtain ⟨f,hfi,hfr,hf0,hf1,hfsub,_hcoordinates,hfmark,hfoff,hcounts⟩ := hpatch h hh hhH
    exact ⟨f,hfi,hfsub,hfr,hf0,hf1,hfmark,hfoff,hcounts⟩
  have hActualSourceContactPatch (p : P) :
      ∃ F : OpenPartialHomeomorph S Plane, ∃ δ H : ℝ,
        F.source ⊆ contactU p ∧ 0 < δ ∧ 0 < H ∧
        ∀ h : ℝ, 0 < h → h < H →
        ∃ f : C(Interval,S), IsEmbedding f ∧ range f ⊆ F.source ∧
          range f=F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          f 0=F.symm (Plane.mk (-δ) h) ∧ f 1=F.symm (Plane.mk δ h) ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧ Disjoint (range f) b.val.image ∧
          ∀ j, f 0 ∉ (old j).val.image ∧ f 1 ∉ (old j).val.image ∧
            (range f ∩ (old j).val.image).Finite ∧
            (range f ∩ (old j).val.image).ncard ≤ if p.val ∈ (old j).val.image then 1 else 0 := by
    let I := {i : Option J // p.val ∈ (r i).val.image}
    let c : I → EssentialMarkedArc M := fun i => r i.val
    let D := {j : J // p.val ∈ (old j).val.image}
    obtain ⟨E0,hpE,hEU,hEmark,hE0,g,R,i0,hi0,hRop,hmodel⟩ := hActualSourceContactRadialCore p Set.univ isOpen_univ (Set.mem_univ _)
    have hEU : E0.source ⊆ contactU p := fun x hx => hEU hx |>.1
    have hselected : c i0=araw := by
      change r i0.val=araw
      rw [hi0]
      rfl
    let label : D → I := fun j => ⟨some j.val,j.property⟩
    have hcross (j : D) : CrossesInDisk M (c i0) (c (label j)) p.val := by
      rw [hselected]
      have hpfree : p.val ∉ M.cover.branch := fun hm => Set.disjoint_left.mp hEmark hpE hm
      have hpraw : p.val ∈ araw.val.image := hselected ▸ i0.property
      apply hRawAllOldTransverse j.val p.val
      exact ⟨⟨hpraw,hpfree⟩,j.property,hpfree⟩
    have hmeet (j : D) (x : S) (hx : x ∈ E0.source)
        (hc : x ∈ (c i0).val.image ∩ (c (label j)).val.image) : x=p.val := by
      rw [hselected] at hc
      exact hContactUMeet p none (some j.val) (by simp) ⟨hEU hx,hc⟩
    obtain ⟨F,δ,H,hFE,hFmark,hδ,hH,hpatch⟩ := hMarkedActualFanPatch c p.val E0 hpE hE0
      hEmark (fun j => E0 ∘ g j) R i0 hRop hmodel label hcross hmeet
    have hFU : F.source ⊆ contactU p := hFE.trans hEU
    refine ⟨F,δ,H,hFU,hδ,hH,?_⟩
    intro h hh hhH
    obtain ⟨f,hfi,hfF,hfr,hf0,hf1,hfmark,hfoff,hcounts⟩ := hpatch h hh hhH
    have hfU : range f ⊆ contactU p := hfF.trans hFU
    have hfb : Disjoint (range f) b.val.image := by
      apply Set.disjoint_left.mpr
      intro x hx hxb
      have hxU := hfU hx
      have hxK : x ∉ KrawDerived ∪ Kother := fun hk => Set.disjoint_left.mp (hContactURemainders p) hxU hk
      have hxs : x ∈ range B.secondSide := by
        rw [hOtherDecomp] at hxb
        exact hxb.resolve_right (fun hk => hxK (Or.inr hk))
      have hxa : x ∈ (c i0).val.image := by
        rw [hselected,himageRaw]
        exact Or.inl hxs
      exact Set.disjoint_left.mp hfoff hx hxa
    refine ⟨f,hfi,hfF,hfr,hf0,hf1,hfmark,hfb,?_⟩
    intro j
    by_cases hj : p.val ∈ (old j).val.image
    · rw [if_pos hj]
      exact hcounts ⟨j,hj⟩
    · rw [if_neg hj]
      have hd : Disjoint (range f) (old j).val.image :=
        (hContactUNonincident p j hj).mono_left hfU
      have he : range f ∩ (old j).val.image=∅ := Set.disjoint_iff_inter_eq_empty.mp hd
      refine ⟨(fun hx => Set.disjoint_left.mp hd (Set.mem_range_self 0) hx),
        (fun hx => Set.disjoint_left.mp hd (Set.mem_range_self 1) hx),?_,?_⟩
      · rw [he]; exact Set.finite_empty
      · rw [he,Set.ncard_empty]
  choose coreLeft coreRight hCore0 hCoreLeft hCoreRight hCore1 hCoreSub hCoreOnly
    using hActualContactCore
  have hCoreIntervalsDisjoint (t u : T) (htu : t ≠ u) :
      Disjoint (Set.Icc (coreLeft t) (coreRight t)) (Set.Icc (coreLeft u) (coreRight u)) := by
    apply Set.disjoint_left.mpr
    intro θ ht hu
    have hpt : ψ θ ∈ contactU ⟨B.secondSide t.val,t.property⟩ :=
      hCoreSub t (Set.mem_image_of_mem ψ ht)
    have hpu : ψ θ ∈ contactU ⟨B.secondSide u.val,u.property⟩ :=
      hCoreSub u (Set.mem_image_of_mem ψ hu)
    have hpne : (⟨B.secondSide t.val,t.property⟩ : P) ≠ ⟨B.secondSide u.val,u.property⟩ := by
      intro he
      apply htu
      apply Subtype.ext
      exact B.second_embedded.injective (congrArg Subtype.val he)
    exact Set.disjoint_left.mp (hContactUDisjoint _ _ hpne) hpt hpu
  have hCoreOrder (t u : T) (htu : t.val.val < u.val.val) : coreRight t < coreLeft u := by
    by_contra hn
    have hle : coreLeft u ≤ coreRight t := le_of_not_gt hn
    let θ := max (coreLeft t) (coreLeft u)
    have ht : θ ∈ Set.Icc (coreLeft t) (coreRight t) := by
      refine ⟨le_max_left _ _,max_le ((hCoreLeft t).le.trans (hCoreRight t).le) hle⟩
    have hu : θ ∈ Set.Icc (coreLeft u) (coreRight u) := by
      refine ⟨le_max_right _ _,max_le ?_ ((hCoreLeft u).le.trans (hCoreRight u).le)⟩
      exact (hCoreLeft t).le.trans (htu.le.trans (hCoreRight u).le)
    have hne : t ≠ u := fun he => (ne_of_lt htu) (congrArg (fun x : T => x.val.val) he)
    exact Set.disjoint_left.mp (hCoreIntervalsDisjoint t u hne) ht hu
  let contactCoordinates : Finset ℝ := hTfinite.toFinset.image Subtype.val
  have hCoordinateMembership (x : ℝ) : x ∈ contactCoordinates ↔ ∃ t : T, t.val.val=x := by
    simp only [contactCoordinates,Finset.mem_image,Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨t,ht,he⟩; exact ⟨⟨t,ht⟩,he⟩
    · rintro ⟨t,he⟩; exact ⟨t.val,t.property,he⟩
  have hOrderedLabel (i : Fin contactCoordinates.card) :
      ∃ t : T, t.val.val=contactCoordinates.orderEmbOfFin rfl i :=
    (hCoordinateMembership _).mp (contactCoordinates.orderEmbOfFin_mem rfl i)
  choose orderedLabel hOrderedLabelCoord using hOrderedLabel
  have hOrderedLabelInjective : Function.Injective orderedLabel := by
    intro i j hij
    apply (contactCoordinates.orderEmbOfFin rfl).injective
    exact (hOrderedLabelCoord i).symm.trans ((congrArg (fun t : T => t.val.val) hij).trans (hOrderedLabelCoord j))
  have hAdjacentSourceGap (i j : Fin contactCoordinates.card) (hij : j.val=i.val+1) :
      coreRight (orderedLabel i) < coreLeft (orderedLabel j) ∧
      ∀ θ ∈ Set.Icc (coreRight (orderedLabel i)) (coreLeft (orderedLabel j)),
        ∀ k, ψ θ ∉ (old k).val.image := by
    have hiOrder : i < j := by change i.val<j.val; omega
    have hcoord : (orderedLabel i).val.val < (orderedLabel j).val.val := by
      rw [hOrderedLabelCoord,hOrderedLabelCoord]
      exact (contactCoordinates.orderEmbOfFin rfl).strictMono hiOrder
    refine ⟨hCoreOrder _ _ hcoord,?_⟩
    intro θ hθ k hOldθ
    have hθ0 : 0 ≤ θ := (hCore0 _).le.trans ((hCoreLeft _).le.trans ((hCoreRight _).le.trans hθ.1))
    have hθ1 : θ ≤ 1 := hθ.2.trans ((hCoreLeft _).le.trans ((hCoreRight _).le.trans (hCore1 _).le))
    let t : Interval := ⟨θ,hθ0,hθ1⟩
    have hψt : ψ θ=B.secondSide t := by
      dsimp [ψ,Function.comp_def]
      rw [Set.projIcc_of_mem zero_le_one ⟨hθ0,hθ1⟩]
    have htFree : B.secondSide t ∉ M.cover.branch := by
      intro hm
      have hpD : B.secondSide t ∈ range B.disk := image_subset_range _ _
        (B.boundary_eq.symm ▸ (show B.secondSide t ∈ range B.firstSide ∪ range B.secondSide from Or.inr (Set.mem_range_self t)))
      rcases B.marks_are_corners _ hpD hm with he|he
      · have ht0 := B.second_embedded.injective (he.trans B.second_zero.symm)
        have hh := congrArg Subtype.val ht0
        change θ=0 at hh
        linarith [hCore0 (orderedLabel i),hCoreLeft (orderedLabel i),hCoreRight (orderedLabel i),hθ.1]
      · have ht1 := B.second_embedded.injective (he.trans B.second_one.symm)
        have hh := congrArg Subtype.val ht1
        change θ=1 at hh
        linarith [hCore1 (orderedLabel j),hCoreLeft (orderedLabel j),hCoreRight (orderedLabel j),hθ.2]
    have htT : t ∈ T := by
      change B.secondSide t ∈ P
      apply Set.mem_iUnion.mpr
      exact ⟨k,⟨⟨⟨B.second_on_curve (Set.mem_range_self t),htFree⟩,
        hψt ▸ hOldθ,htFree⟩,Set.mem_range_self t⟩⟩
    have hθc : θ ∈ contactCoordinates := (hCoordinateMembership θ).mpr ⟨⟨t,htT⟩,rfl⟩
    have hbetween : θ ∈ Set.Ioo (contactCoordinates.orderEmbOfFin rfl i)
        (contactCoordinates.orderEmbOfFin rfl j) := by
      rw [← hOrderedLabelCoord i,← hOrderedLabelCoord j]
      exact ⟨(hCoreRight _).trans_le hθ.1,hθ.2.trans_lt (hCoreLeft _)⟩
    exact Set.disjoint_left.mp (CurveComplex.actual_finite_boundary_adjacent_contact_gap contactCoordinates i j hij)
      hbetween hθc
  have hExplicitMarkedAxisStripChart
      (anchor : EssentialMarkedArc M)
      (B : Interval × Icc (-1:ℝ) 1 → S) (hB : IsEmbedding B)
      (hmarks : ∀ z, B z ∉ M.cover.branch)
      (haxis : ∀ z, B z ∈ anchor.val.image ↔ z.2.val = 0) :
      ∃ U : Set S, ∃ V : Set Plane, ∃ _hU : IsOpen U, ∃ e : U ≃ₜ V,
        IsOpen V ∧ Plane.closedSquare 0 1 ⊆ V ∧ Disjoint U (M.cover.branch : Set S) ∧
        (∀ q : U, q.val ∈ anchor.val.image ↔ (e q).val 1 = 0) ∧
        (∀ t : Interval, 0 < t.val → t.val < 1 →
          ∃ ht : B (t,⟨0,by norm_num⟩) ∈ U,
            (e ⟨B (t,⟨0,by norm_num⟩),ht⟩).val=Plane.mk (4*t.val-2) 0) ∧
        ∃ hp : B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) ∈ U,
          (e ⟨B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),hp⟩).val = 0 := by
    let := (actualSphereSmoothAtlas M).charts
    let q : UnitBox → Interval × Icc (-1:ℝ) 1 := fun z =>
      (⟨(z.val.1+1)/2,by have h := abs_lt.mp z.property.1; constructor <;> linarith⟩,
        ⟨z.val.2,(abs_lt.mp z.property.2).1.le,(abs_lt.mp z.property.2).2.le⟩)
    have hqc : Continuous q := by unfold q; fun_prop
    let inv : Interval × Icc (-1:ℝ) 1 → ℝ × ℝ := fun z => (2*z.1.val-1,z.2.val)
    have hinv : Continuous inv := by unfold inv; fun_prop
    have hqi : IsEmbedding q := by
      apply IsEmbedding.of_comp hqc hinv
      have he : inv ∘ q = (Subtype.val : UnitBox → ℝ × ℝ) := by
        funext z; apply Prod.ext
        · dsimp [inv,q]; ring
        · rfl
      rw [he]
      exact IsEmbedding.subtypeVal
    let f : UnitBox → S := B ∘ q
    have hf : IsEmbedding f := hB.comp hqi
    let U : Set S := range f
    let F : Plane → S := fun z => B (projIcc 0 1 zero_le_one ((z 0+1)/2),
      projIcc (-1) 1 (by norm_num) (z 1))
    have hFc : Continuous F := by
      apply hB.continuous.comp
      exact (continuous_projIcc.comp (by fun_prop)).prodMk (continuous_projIcc.comp (by fun_prop))
    have hFU : F '' Plane.openSquare 0 1 = U := by
      ext x
      constructor
      · rintro ⟨z,hz,rfl⟩
        have hz' : |z 0| < 1 ∧ |z 1| < 1 :=
          max_lt_iff.mp (mem_openSquare_zero_one.mp hz)
        refine ⟨⟨(z 0,z 1),hz'⟩,?_⟩
        apply congrArg B
        apply Prod.ext <;> apply Subtype.ext
        · have h := abs_lt.mp hz'.1
          rw [projIcc_of_mem zero_le_one
            (show (z 0+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
        · rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
            ⟨(abs_lt.mp hz'.2).1.le,(abs_lt.mp hz'.2).2.le⟩]
      · rintro ⟨z,rfl⟩
        refine ⟨Plane.mk z.val.1 z.val.2,?_,?_⟩
        · apply mem_openSquare_zero_one.mpr
          exact max_lt_iff.mpr z.property
        · apply congrArg B
          apply Prod.ext <;> apply Subtype.ext
          · have h := abs_lt.mp z.property.1
            change (projIcc 0 1 zero_le_one ((z.val.1+1)/2)).val = (z.val.1+1)/2
            rw [projIcc_of_mem zero_le_one (show (z.val.1+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
          · change (projIcc (-1) 1 (by norm_num) z.val.2).val = z.val.2
            rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
                ⟨(abs_lt.mp z.property.2).1.le,(abs_lt.mp z.property.2).2.le⟩]
    have hFi : InjOn F (Plane.openSquare 0 1) := by
      intro z hz w hw he
      have hz' := max_lt_iff.mp (mem_openSquare_zero_one.mp hz)
      have hw' := max_lt_iff.mp (mem_openSquare_zero_one.mp hw)
      have hqcoord (z : Plane) (hz : |z 0| < 1 ∧ |z 1| < 1) :
          F z = f ⟨(z 0,z 1),hz⟩ := by
        apply congrArg B
        apply Prod.ext <;> apply Subtype.ext
        · have h := abs_lt.mp hz.1
          rw [projIcc_of_mem zero_le_one
            (show (z 0+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
        · rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
            ⟨(abs_lt.mp hz.2).1.le,(abs_lt.mp hz.2).2.le⟩]
      rw [hqcoord z hz',hqcoord w hw'] at he
      have h := congrArg Subtype.val (hf.injective he)
      ext i
      fin_cases i
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    have hU : IsOpen U := hFU ▸ surface_invariance_of_domain_probe F _
      (Plane.isOpen_openSquare 0 1) hFc.continuousOn hFi
    let j : UnitBox ≃ₜ U := hf.toHomeomorph
    let V : Set Plane := doublePlaneCoordinates '' {z : ℝ × ℝ | |z.1|<1 ∧ |z.2|<1}
    let e : U ≃ₜ V := j.symm.trans (doublePlaneCoordinates.image _)
    have hVOpen : IsOpen V := doublePlaneCoordinates.isOpenMap _
      ((isOpen_lt continuous_fst.abs continuous_const).inter
        (isOpen_lt continuous_snd.abs continuous_const))
    have hCV : Plane.closedSquare 0 1 ⊆ V := by
      intro z hz
      have h := max_le_iff.mp (mem_closedSquare_zero_one.mp hz)
      refine ⟨(z 0/2,z 1/2),?_,?_⟩
      · change |z 0/2| < 1 ∧ |z 1/2| < 1
        rw [abs_div,abs_div]; norm_num
        constructor <;> linarith [h.1,h.2]
      · apply planeCoordinates.injective
        apply Prod.ext
        · change 2*(z 0/2) = z 0; ring
        · change 2*(z 1/2) = z 1; ring
    have hj (z : U) : B (q (j.symm z)) = z.val := congrArg Subtype.val (j.apply_symm_apply z)
    let z0 : UnitBox := ⟨(0,0),by norm_num⟩
    have hz0 : f z0 = B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) := by
      apply congrArg B
      apply Prod.ext <;> apply Subtype.ext <;> norm_num [q,z0]
    have hpU : B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) ∈ U := ⟨z0,hz0⟩
    refine ⟨U,V,hU,e,hVOpen,hCV,?_,?_,?_,hpU,?_⟩
    · apply Set.disjoint_left.mpr
      rintro z ⟨w,rfl⟩ hz
      exact hmarks (q w) hz
    · intro z
      rw [← hj z,haxis]
      change (j.symm z).val.2 = 0 ↔ 2*(j.symm z).val.2 = 0
      constructor <;> intro h <;> linarith
    · intro t ht0 ht1
      let z : UnitBox := ⟨(2*t.val-1,0),by
        constructor
        · rw [abs_lt]; constructor <;> linarith
        · norm_num⟩
      have hz : f z=B (t,⟨0,by norm_num⟩) := by
        apply congrArg B
        apply Prod.ext <;> apply Subtype.ext
        · change (2*t.val-1+1)/2=t.val
          ring
        · rfl
      have ht : B (t,⟨0,by norm_num⟩) ∈ U := ⟨z,hz⟩
      refine ⟨ht,?_⟩
      have he : j.symm ⟨B (t,⟨0,by norm_num⟩),ht⟩=z := by
        apply j.injective
        rw [j.apply_symm_apply]
        apply Subtype.ext
        exact hz.symm
      change doublePlaneCoordinates (j.symm _).val=Plane.mk (4*t.val-2) 0
      rw [he]
      ext i
      fin_cases i
      · change 2*(2*t.val-1)=4*t.val-2
        ring
      · change 2*(0:ℝ)=0
        ring
    · have he : j.symm ⟨B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),hpU⟩ = z0 := by
        apply j.injective
        rw [j.apply_symm_apply]
        apply Subtype.ext
        exact hz0.symm
      change doublePlaneCoordinates (j.symm _).val = 0
      rw [he]
      apply planeCoordinates.injective
      apply Prod.ext
      · change 2*(0:ℝ) = 0; ring
      · change 2*(0:ℝ) = 0; ring
  have hActualWholeInteriorAxisChart (c : EssentialMarkedArc M)
      (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) :
      ∃ U : Set S, ∃ V : Set Plane, ∃ hU : IsOpen U, ∃ e : U ≃ₜ V,
        IsOpen V ∧ Plane.closedSquare 0 1 ⊆ V ∧ Disjoint U (M.cover.branch : Set S) ∧
        (∀ q : U, q.val ∈ c.val.image ↔ (e q).val 1=0) ∧
        ∀ θ ∈ Set.Ioo α β,
          ∃ hx : c.val.map (Set.projIcc 0 1 zero_le_one θ) ∈ U,
            (e ⟨c.val.map (Set.projIcc 0 1 zero_le_one θ),hx⟩).val=
              Plane.mk (4*((θ-α)/(β-α))-2) 0 := by
    obtain ⟨B,hB,hcenter,hmarks,haxis⟩ := actual_anchor_interior_core_exact_strip M c α β hα hβ hαβ
    obtain ⟨U,V,hU,e,hV,hCV,hUMarks,hUAxis,hcover,hmid,hmid0⟩ :=
      hExplicitMarkedAxisStripChart c B hB hmarks haxis
    refine ⟨U,V,hU,e,hV,hCV,hUMarks,hUAxis,?_⟩
    intro θ hθ
    have hd : 0 < β-α := sub_pos.mpr hαβ
    let t : Interval := ⟨(θ-α)/(β-α),
      (div_pos (sub_pos.mpr hθ.1) hd).le,
      ((div_lt_one hd).mpr (by linarith [hθ.2])).le⟩
    have ht0 : 0 < t.val := div_pos (sub_pos.mpr hθ.1) hd
    have ht1 : t.val < 1 := (div_lt_one hd).mpr (by linarith [hθ.2])
    have hparam : actualCoreParameter α β hα.le hβ.le hαβ.le t=Set.projIcc 0 1 zero_le_one θ := by
      rw [Set.projIcc_of_mem zero_le_one ⟨hα.le.trans hθ.1.le,hθ.2.le.trans hβ.le⟩]
      apply Subtype.ext
      dsimp [actualCoreParameter,t]
      field_simp
      ring
    have htmap : B (t,⟨0,by norm_num⟩)=c.val.map (Set.projIcc 0 1 zero_le_one θ) :=
      (hcenter t).trans (congrArg c.val.map hparam)
    obtain ⟨ht,hcoord⟩ := hcover t ht0 ht1
    have hx : c.val.map (Set.projIcc 0 1 zero_le_one θ) ∈ U := htmap ▸ ht
    refine ⟨hx,?_⟩
    have he : (⟨B (t,⟨0,by norm_num⟩),ht⟩ : U)=
        ⟨c.val.map (Set.projIcc 0 1 zero_le_one θ),hx⟩ := Subtype.ext htmap
    rw [he] at hcoord
    exact hcoord
  have hActualCompactMarkFreeCarrierAxisChart (c : EssentialMarkedArc M)
      (f : C(Interval,S)) (hsub : range f ⊆ arcInterior M c) :
      ∃ U : Set S, ∃ V : Set Plane, ∃ hU : IsOpen U, ∃ e : U ≃ₜ V,
        IsOpen V ∧ Plane.closedSquare 0 1 ⊆ V ∧ Disjoint U (M.cover.branch : Set S) ∧
        (∀ q : U, q.val ∈ c.val.image ↔ (e q).val 1=0) ∧ range f ⊆ U := by
    obtain ⟨q,hq⟩ := hActualInteriorParameterHomeomorph c
    let point : C(Interval,arcInterior M c) :=
      ⟨fun t => ⟨f t,hsub (Set.mem_range_self t)⟩,f.continuous.subtype_mk _⟩
    let τ : C(Interval,ℝ) := ⟨fun t => (q.symm (point t)).val.val,
      continuous_subtype_val.comp (continuous_subtype_val.comp (q.symm.continuous.comp point.continuous))⟩
    have hτf (t : Interval) : c.val.map (q.symm (point t)).val=f t := by
      rw [← hq]
      exact congrArg Subtype.val (q.apply_symm_apply _)
    have hτ01 (t : Interval) : 0 < τ t ∧ τ t < 1 := by
      have hm : c.val.map (q.symm (point t)).val ∉ M.cover.branch := (q.symm (point t)).property.2
      constructor
      · have hn : (q.symm (point t)).val ≠ 0 := fun he => hm (he.symm ▸ c.val.start_marked)
        exact lt_of_le_of_ne (q.symm (point t)).val.property.1 (fun he => hn (Subtype.ext he.symm))
      · have hn : (q.symm (point t)).val ≠ 1 := fun he => hm (he.symm ▸ c.val.end_marked)
        exact lt_of_le_of_ne (q.symm (point t)).val.property.2 (fun he => hn (Subtype.ext he))
    let C : Set ℝ := range τ
    have hC : IsCompact C := isCompact_range τ.continuous
    have hCne : C.Nonempty := Set.range_nonempty τ
    let l := sInf C
    let u := sSup C
    have hl : l ∈ C := hC.isClosed.csInf_mem hCne hC.bddBelow
    have hu : u ∈ C := hC.isClosed.csSup_mem hCne hC.bddAbove
    have hl0 : 0 < l := by obtain ⟨t,ht⟩ := hl; exact ht ▸ (hτ01 t).1
    have hu1 : u < 1 := by obtain ⟨t,ht⟩ := hu; exact ht ▸ (hτ01 t).2
    have hlu : l ≤ u := csInf_le hC.bddBelow hu
    let α := l/2
    let β := (u+1)/2
    have hα : 0 < α := half_pos hl0
    have hβ : β < 1 := by dsimp [β]; linarith
    have hαβ : α < β := by dsimp [α,β]; linarith
    obtain ⟨U,V,hU,e,hV,hCV,hUMark,hAxis,hCover⟩ := hActualWholeInteriorAxisChart c α β hα hαβ hβ
    refine ⟨U,V,hU,e,hV,hCV,hUMark,hAxis,?_⟩
    rintro x ⟨t,rfl⟩
    have hτC : τ t ∈ C := Set.mem_range_self t
    have hτlo : l ≤ τ t := csInf_le hC.bddBelow hτC
    have hτhi : τ t ≤ u := le_csSup hC.bddAbove hτC
    have hτAB : τ t ∈ Set.Ioo α β := by dsimp [α,β]; constructor <;> linarith
    obtain ⟨hx,hcoord⟩ := hCover (τ t) hτAB
    have htmap : c.val.map (Set.projIcc 0 1 zero_le_one (τ t))=f t := by
      rw [Set.projIcc_of_mem zero_le_one ⟨(hτ01 t).1.le,(hτ01 t).2.le⟩]
      exact hτf t
    exact htmap ▸ hx
  have hMarkedPositiveHalfChoice
      (c : EssentialMarkedArc M) (p : S) (E F : OpenPartialHomeomorph S Plane)
      (hFE : F.source ⊆ E.source) (hpF : p ∈ F.source) (hFp : F p = 0) (hEp : E p 1 = 0)
      (ρ η : ℝ) (hη : 0 < η)
      (hBall : Metric.ball (0 : Plane) η ⊆ F.target ∩ Metric.ball (0 : Plane) ρ)
      (hEaxis : ∀ x ∈ E.source, x ∈ c.val.image ↔ E x 1 = 0)
      (hFaxis : ∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ c.val.image ↔ F x 1 = 0)) :
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∀ y ∈ Metric.ball (0 : Plane) η, 0 < σ*y 1 → 0 < E (F.symm y) 1 := by
    classical
    let C := F.source ∩ F ⁻¹' Metric.ball (0 : Plane) η
    have hC : IsOpen C := F.isOpen_inter_preimage isOpen_ball
    have hEC : IsOpen (E '' C) := E.isOpen_image_of_subset_source hC (fun x hx => hFE hx.1)
    have hpEC : E p ∈ E '' C := ⟨p,⟨hpF,by change F p ∈ Metric.ball (0 : Plane) η; rw [hFp]; simpa using hη⟩,rfl⟩
    let v : ℝ → Plane := fun t => E p + Plane.mk 0 t
    have hv : Continuous v := by fun_prop
    have hOpen : IsOpen (v ⁻¹' (E '' C)) := hEC.preimage hv
    have h0 : (0 : ℝ) ∈ v ⁻¹' (E '' C) := by
      have hz : Plane.mk (0 : ℝ) 0 = (0 : Plane) := by ext i; fin_cases i <;> rfl
      simpa [v,hz] using hpEC
    obtain ⟨r,hr,hvr⟩ := Metric.isOpen_iff.mp hOpen 0 h0
    let τ := r/2
    have hτ : 0 < τ := half_pos hr
    obtain ⟨x,hx,hEx⟩ := hvr (show τ ∈ Metric.ball (0 : ℝ) r by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hτ]; dsimp [τ]; linarith)
    have hExy : E x 1 = τ := by
      have hh := congrArg (fun z : Plane => z 1) hEx
      change E x 1 = E p 1 + τ at hh
      simpa [hEp] using hh
    let q := F x
    have hqBall : q ∈ Metric.ball (0 : Plane) η := hx.2
    have hqx : F.symm q = x := F.left_inv hx.1
    have hqN : ‖F x‖ < ρ := by simpa using (hBall hqBall).2
    have hqNe : q 1 ≠ 0 := by
      intro he
      have hc := (hFaxis x hx.1 hqN).mpr he
      have hh := (hEaxis x (hFE hx.1)).mp hc
      linarith
    let σ : ℝ := if 0 < q 1 then 1 else -1
    have hσ : σ = 1 ∨ σ = -1 := by dsimp [σ]; split_ifs <;> simp
    have hqSign : 0 < σ*q 1 := by
      dsimp [σ]
      split_ifs with hq
      · simpa using hq
      · have hn : q 1 < 0 := lt_of_le_of_ne (le_of_not_gt hq) hqNe
        simpa using neg_pos.mpr hn
    let P : Set Plane := Metric.ball (0 : Plane) η ∩ {y | 0 < σ*y 1}
    have hP : IsPreconnected P := (convex_ball (0 : Plane) η).inter
      (convex_halfSpace_gt (𝕜 := ℝ) (f := fun y : Plane => σ*y 1)
        ⟨by intros x y; change σ*(x 1+y 1)=σ*x 1+σ*y 1; ring,
         by intros a x; change σ*(a*x 1)=a*(σ*x 1); ring⟩ 0) |>.isPreconnected
    let G : P → ℝ := fun y => E (F.symm y.val) 1
    have hFS : Continuous (fun y : P => F.symm y.val) :=
      F.symm.continuousOn.comp_continuous continuous_subtype_val (fun y => (hBall y.property.1).1)
    have hEFS : Continuous (fun y : P => E (F.symm y.val)) :=
      E.continuousOn.comp_continuous hFS (fun y => hFE (F.map_target (hBall y.property.1).1))
    have hG : Continuous G := (show Continuous (fun z : Plane => z 1) by fun_prop).comp hEFS
    have hGNe (y : P) : G y ≠ 0 := by
      intro he
      have hyS := F.map_target (hBall y.property.1).1
      have hyE := hFE hyS
      have hc := (hEaxis _ hyE).mpr he
      have hyN : ‖F (F.symm y.val)‖ < ρ := by
        rw [F.right_inv (hBall y.property.1).1]
        simpa using (hBall y.property.1).2
      have hh := (hFaxis _ hyS hyN).mp hc
      rw [F.right_inv (hBall y.property.1).1] at hh
      have hp := y.property.2
      change 0 < σ*y.val 1 at hp
      rw [hh,mul_zero] at hp
      exact (lt_irrefl 0) hp
    have hRangeConn : IsPreconnected (Set.range G) := by
      have : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp hP
      exact isPreconnected_range hG
    have hRangeSub : Set.range G ⊆ Set.Ioi 0 ∪ Set.Iio 0 := by
      rintro z ⟨y,rfl⟩
      exact (lt_or_gt_of_ne (hGNe y)).symm
    let qp : P := ⟨q,⟨hqBall,hqSign⟩⟩
    have hqp : 0 < G qp := by
      change 0 < E (F.symm q) 1
      rw [hqx,hExy]
      exact hτ
    have hPositive : Set.range G ⊆ Set.Ioi 0 :=
      hRangeConn.subset_left_of_subset_union isOpen_Ioi isOpen_Iio
        (Set.disjoint_left.mpr (by intro z hz hz'; change 0 < z at hz; change z < 0 at hz'; linarith))
        hRangeSub ⟨G qp,⟨⟨qp,rfl⟩,hqp⟩⟩
    refine ⟨σ,hσ,?_⟩
    intro y hy hys
    exact hPositive ⟨⟨y,⟨hy,hys⟩⟩,rfl⟩
  have hMarkedMirrorPositiveCore {J : Type}
      (E F : OpenPartialHomeomorph S Plane) (c : EssentialMarkedArc M) (p : S)
      (hFp : F p = 0) (ρ η : ℝ) (a b : J → Plane)
      (hBall : Metric.ball (0 : Plane) η ⊆ F.target ∩ Metric.ball (0 : Plane) ρ)
      (haxis : ∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ c.val.image ↔ F x 1 = 0))
      (ha : ∀ j, 0 < a j 1) (hb : ∀ j, b j 1 < 0)
      (d : J → EssentialMarkedArc M)
      (hmodel : ∀ j x, x ∈ F.source → ‖F x‖ < ρ →
        (x ∈ (d j).val.image ↔ F x ∈ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)))
      (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
      (hPositive : ∀ y ∈ Metric.ball (0 : Plane) η, 0 < σ*y 1 → 0 < E (F.symm y) 1) :
      ∃ F' : OpenPartialHomeomorph S Plane, ∃ a' b' : J → Plane,
        F'.source = F.source ∧ F' p = 0 ∧
        (Metric.ball (0 : Plane) η ⊆ F'.target ∩ Metric.ball (0 : Plane) ρ) ∧
        (∀ x ∈ F'.source, ‖F' x‖ < ρ → (x ∈ c.val.image ↔ F' x 1 = 0)) ∧
        (∀ j, 0 < a' j 1) ∧ (∀ j, b' j 1 < 0) ∧
        (∀ j x, x ∈ F'.source → ‖F' x‖ < ρ →
          (x ∈ (d j).val.image ↔ F' x ∈ segment ℝ (0 : Plane) (a' j) ∪ segment ℝ (0 : Plane) (b' j))) ∧
        (∀ y ∈ Metric.ball (0 : Plane) η, 0 < y 1 → 0 < E (F'.symm y) 1) := by
    rcases hσ with rfl | rfl
    · exact ⟨F,a,b,rfl,hFp,hBall,haxis,ha,hb,hmodel,by simpa using hPositive⟩
    · let N : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.neg ℝ
      let F' := F.transHomeomorph N.toHomeomorph
      have hFormula (x : S) : F' x = -F x := rfl
      have hInvFormula (y : Plane) : F'.symm y = F.symm (-y) := rfl
      have hSegment (v z : Plane) : z ∈ segment ℝ (0 : Plane) v ↔
          -z ∈ segment ℝ (0 : Plane) (-v) := by
        have hi := image_segment ℝ N.toLinearMap.toAffineMap (0 : Plane) v
        change N '' segment ℝ (0 : Plane) v = segment ℝ (N 0) (N v) at hi
        rw [map_zero] at hi
        change z ∈ segment ℝ (0 : Plane) v ↔ N z ∈ segment ℝ (0 : Plane) (N v)
        rw [← hi]
        exact ⟨fun hz => ⟨z,hz,rfl⟩,fun ⟨w,hw,he⟩ => N.injective he ▸ hw⟩
      refine ⟨F',fun j => -b j,fun j => -a j,rfl,?_,?_,?_,?_,?_,?_,?_⟩
      · rw [hFormula,hFp,neg_zero]
      · intro y hy
        have hyneg : -y ∈ Metric.ball (0 : Plane) η := by simpa [Metric.mem_ball,dist_zero_right] using hy
        have hyF := (hBall hyneg).1
        refine ⟨?_,(hBall hy).2⟩
        change N.symm y ∈ F.target
        exact hyF
      · intro x hx hxN
        have hxNorm : ‖F x‖ < ρ := by simpa [hFormula] using hxN
        rw [haxis x hx hxNorm,hFormula]
        change (F x 1 = 0 ↔ (-F x) 1 = 0)
        simp
      · intro j
        change 0 < -(b j) 1
        exact neg_pos.mpr (hb j)
      · intro j
        change -(a j) 1 < 0
        exact neg_neg_of_pos (ha j)
      · intro j x hx hxN
        have hxNorm : ‖F x‖ < ρ := by simpa [hFormula] using hxN
        rw [hmodel j x hx hxNorm,hFormula]
        change (F x ∈ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)) ↔
          (-F x ∈ segment ℝ (0 : Plane) (-b j) ∪ segment ℝ (0 : Plane) (-a j))
        simp only [Set.mem_union]
        exact (or_congr (hSegment (a j) (F x)) (hSegment (b j) (F x))).trans or_comm
      · intro y hy hyPos
        rw [hInvFormula]
        apply hPositive (-y) (by simpa [Metric.mem_ball,dist_zero_right] using hy)
        simpa using hyPos
  have hMarkedCommonBankUniformPatch {D : Type} [Fintype D]
      (c : EssentialMarkedArc M) (d : D → EssentialMarkedArc M) (p : S)
      (E F : OpenPartialHomeomorph S Plane)
      (hFE : F.source ⊆ E.source) (hp : p ∈ F.source) (hFp : F p=0)
      (hEp : E p 1=0) (hmark : Disjoint F.source (M.cover.branch : Set S))
      (ρ η : ℝ) (hρ : 0 < ρ) (hη : 0 < η)
      (hball : Metric.ball (0:Plane) η ⊆ F.target ∩ Metric.ball (0:Plane) ρ)
      (hEaxis : ∀ x ∈ E.source, x ∈ c.val.image ↔ E x 1=0)
      (haxis : ∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ c.val.image ↔ F x 1=0))
      (a b : D → Plane) (ha : ∀ j, 0 < a j 1) (hb : ∀ j, b j 1 < 0)
      (hmodel : ∀ j x, x ∈ F.source → ‖F x‖ < ρ →
        (x ∈ (d j).val.image ↔ F x ∈ segment ℝ (0:Plane) (a j) ∪ segment ℝ (0:Plane) (b j))) :
      ∃ G : OpenPartialHomeomorph S Plane, ∃ δ H : ℝ,
        G.source ⊆ F.source ∧ 0 < δ ∧ 0 < H ∧
        Plane.mk (-δ) 0 ∈ G.target ∧ Plane.mk δ 0 ∈ G.target ∧
        (∀ h : ℝ, 0 < h → h < H → segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ G.target) ∧
        ∀ h : ℝ, 0 < h → h < H → ∃ f : C(Interval,S),
          IsEmbedding f ∧ range f ⊆ G.source ∧
          range f=G.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          f 0=G.symm (Plane.mk (-δ) h) ∧ f 1=G.symm (Plane.mk δ h) ∧
          (∀ x ∈ range f, 0 < E x 1) ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧ Disjoint (range f) c.val.image ∧
          ∀ j, f 0 ∉ (d j).val.image ∧ f 1 ∉ (d j).val.image ∧
            (range f ∩ (d j).val.image).Finite ∧ (range f ∩ (d j).val.image).ncard ≤ 1 := by
    obtain ⟨σ,hσ,hpos⟩ := hMarkedPositiveHalfChoice c p E F hFE hp hFp hEp ρ η hη hball hEaxis haxis
    obtain ⟨F',a',b',hs,hp',hball',haxis',ha',hb',hmodel',hpos'⟩ :=
      hMarkedMirrorPositiveCore E F c p hFp ρ η a b hball haxis ha hb d hmodel σ hσ hpos
    let G := F'.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0:Plane) η) isOpen_ball)
    have hGs : G.source=F'.source ∩ F' ⁻¹' Metric.ball (0:Plane) η := by
      simp [G,OpenPartialHomeomorph.trans_source]
    have hGval (x : S) : G x=F' x := rfl
    have hGsub : G.source ⊆ F.source := fun x hx => hs ▸ (hGs ▸ hx).1
    have hGmark : Disjoint G.source (M.cover.branch : Set S) := hmark.mono_left hGsub
    have hpG : p ∈ G.source := by
      rw [hGs]
      refine ⟨hs.symm ▸ hp,?_⟩
      change F' p ∈ Metric.ball (0:Plane) η
      rw [hp']
      simpa using hη
    have hz : (0:Plane) ∈ G.target := by
      have hh := G.map_source hpG
      rw [hGval,hp'] at hh
      exact hh
    obtain ⟨ζ,hζ,hζball⟩ := Metric.isOpen_iff.mp G.open_target 0 hz
    have hGaxis (x : S) (hx : x ∈ G.source) : x ∈ c.val.image ↔ G x 1=0 := by
      have hh := hGs ▸ hx
      have hn := (hball' hh.2).2
      exact haxis' x hh.1 (by simpa [Metric.mem_ball,dist_zero_right] using hn)
    have hGmodel (j : D) (x : S) (hx : x ∈ G.source) (_ : G x ∈ Metric.ball (0:Plane) ζ) :
        x ∈ (d j).val.image ↔ G x ∈ segment ℝ (0:Plane) (a' j) ∪ segment ℝ (0:Plane) (b' j) := by
      have hh := hGs ▸ hx
      exact hmodel' j x hh.1 (by simpa [Metric.mem_ball,dist_zero_right] using (hball' hh.2).2)
    obtain ⟨δ,H,hδ,hH,hleft0,hright0,hsegments,hpatch⟩ := hMarkedUniformContactPatch d c G hGmark ζ hζ hζball
      hGaxis a' b' ha' hb' hGmodel
    refine ⟨G,δ,H,hGsub,hδ,hH,hleft0,hright0,hsegments,?_⟩
    intro h hh hhH
    obtain ⟨f,hfi,hfr,hf0,hf1,hfsub,hcoordinates,hfm,hfo,hcounts⟩ := hpatch h hh hhH
    refine ⟨f,hfi,hfsub,hfr,hf0,hf1,?_,hfm,hfo,hcounts⟩
    intro x hx
    have hxG := hfsub hx
    have hxF := (hGs ▸ hxG).1
    have hxball := (hGs ▸ hxG).2
    have hy : F' x 1=h := hcoordinates x hx
    have hpbank := hpos' (F' x) hxball (hy ▸ hh)
    rwa [F'.left_inv hxF] at hpbank
  have hActualOffsetEndpointFamilies
      (F : OpenPartialHomeomorph S Plane) (δ H : ℝ) (hH : 0 < H)
      (hleft0 : Plane.mk (-δ) 0 ∈ F.target) (hright0 : Plane.mk δ 0 ∈ F.target)
      (hsegments : ∀ h : ℝ, 0 < h → h < H →
        segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ F.target) :
      ∃ L R : C(Interval,S),
        (∀ t, L t=F.symm (Plane.mk (-δ) ((H/2)*t.val))) ∧
        (∀ t, R t=F.symm (Plane.mk δ ((H/2)*t.val))) ∧
        (∀ t, L t ∈ F.source ∧ R t ∈ F.source) ∧
        (∀ t, F (L t)=Plane.mk (-δ) ((H/2)*t.val) ∧
          F (R t)=Plane.mk δ ((H/2)*t.val)) ∧
        L 0=F.symm (Plane.mk (-δ) 0) ∧ R 0=F.symm (Plane.mk δ 0) := by
    let qL : Interval → Plane := fun t => Plane.mk (-δ) ((H/2)*t.val)
    let qR : Interval → Plane := fun t => Plane.mk δ ((H/2)*t.val)
    have hheight (t : Interval) : 0 ≤ (H/2)*t.val ∧ (H/2)*t.val < H := by
      constructor
      · exact mul_nonneg (half_pos hH).le t.property.1
      · nlinarith [t.property.2]
    have htargets (t : Interval) : qL t ∈ F.target ∧ qR t ∈ F.target := by
      rcases eq_or_lt_of_le (hheight t).1 with hz|hpos
      · have he : (H/2)*t.val=0 := hz.symm
        simpa [qL,qR,he] using And.intro hleft0 hright0
      · have hsub := hsegments ((H/2)*t.val) hpos (hheight t).2
        exact ⟨hsub (left_mem_segment ℝ _ _),hsub (right_mem_segment ℝ _ _)⟩
    let L : C(Interval,S) := ⟨fun t => F.symm (qL t),
      F.symm.continuousOn.comp_continuous (by dsimp [qL]; fun_prop) (fun t => (htargets t).1)⟩
    let R : C(Interval,S) := ⟨fun t => F.symm (qR t),
      F.symm.continuousOn.comp_continuous (by dsimp [qR]; fun_prop) (fun t => (htargets t).2)⟩
    refine ⟨L,R,fun t => rfl,fun t => rfl,?_,?_,?_,?_⟩
    · intro t
      exact ⟨F.map_target (htargets t).1,F.map_target (htargets t).2⟩
    · intro t
      exact ⟨F.right_inv (htargets t).1,F.right_inv (htargets t).2⟩
    · simp [L,qL]
    · simp [R,qR]
  have hMarkedBankedActualFanPatch {I D : Type} [Fintype I] [Fintype D]
      (c : I → EssentialMarkedArc M) (p : S)
      (E0 : OpenPartialHomeomorph S Plane) (hpE : p ∈ E0.source) (hE0 : E0 p=0)
      (hmarks : Disjoint E0.source (M.cover.branch : Set S))
      (γ : I × Bool → Interval → Plane)
      (R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E0 '' E0.source))
      (i0 : I) (hop : R.vector (i0,true) = -R.vector (i0,false))
      (hcore : ∀ i x, x ∈ E0.source → ‖R.H (E0 x)‖ ≤ R.coreRadius →
        (x ∈ (c i).val.image ↔ R.H (E0 x) ∈
          segment ℝ (0:Plane) (R.vector (i,false)) ∪
          segment ℝ (0:Plane) (R.vector (i,true))))
      (label : D → I)
      (hcross : ∀ j, CrossesInDisk M (c i0) (c (label j)) p)
      (hmeet : ∀ j x, x ∈ E0.source → x ∈ (c i0).val.image ∩ (c (label j)).val.image → x=p)
      (E : OpenPartialHomeomorph S Plane) (hE0E : E0.source ⊆ E.source)
      (hEp : E p 1=0) (hEaxis : ∀ x ∈ E.source, x ∈ (c i0).val.image ↔ E x 1=0) :
      ∃ F : OpenPartialHomeomorph S Plane, ∃ δ H : ℝ,
        F.source ⊆ E0.source ∧ 0 < δ ∧ 0 < H ∧
        Plane.mk (-δ) 0 ∈ F.target ∧ Plane.mk δ 0 ∈ F.target ∧
        (∀ h : ℝ, 0 < h → h < H → segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ F.target) ∧
        ∀ h : ℝ, 0 < h → h < H → ∃ f : C(Interval,S),
          IsEmbedding f ∧ range f ⊆ F.source ∧
          range f=F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          f 0=F.symm (Plane.mk (-δ) h) ∧ f 1=F.symm (Plane.mk δ h) ∧
          (∀ x ∈ range f, 0 < E x 1) ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧ Disjoint (range f) (c i0).val.image ∧
          ∀ j, f 0 ∉ (c (label j)).val.image ∧ f 1 ∉ (c (label j)).val.image ∧
            (range f ∩ (c (label j)).val.image).Finite ∧ (range f ∩ (c (label j)).val.image).ncard ≤ 1 := by
    obtain ⟨T,F0,ρ,hs,hFp,hρ,hρ1,hFformula,hTv,hCoreNorm,hAxis,hModel⟩ :=
      hMarkedNormalizeRadialCore c p E0 hpE hE0 γ R i0 hop false hcore
    have hSign (j : D) : (T (R.vector (label j,false))) 1 * (T (R.vector (label j,true))) 1 < 0 :=
      hMarkedCrossingSigns (c i0) (c (label j)) p (hcross j) F0 (hs.symm ▸ hpE) hFp ρ hρ
        (T (R.vector (label j,false))) (T (R.vector (label j,true))) hAxis
        (fun x hx => hmeet j x (hs ▸ hx))
        (fun x hx hn hd => (hModel (label j) x hx hn).mp hd)
    let a : D → Plane := fun j => if 0 < (T (R.vector (label j,false))) 1
      then T (R.vector (label j,false)) else T (R.vector (label j,true))
    let b : D → Plane := fun j => if 0 < (T (R.vector (label j,false))) 1
      then T (R.vector (label j,true)) else T (R.vector (label j,false))
    have ha (j : D) : 0 < a j 1 := by
      dsimp [a]
      split_ifs with hh
      · exact hh
      · nlinarith [hSign j]
    have hb (j : D) : b j 1 < 0 := by
      dsimp [b]
      split_ifs with hh
      · nlinarith [hSign j]
      · have hne : (T (R.vector (label j,false))) 1 ≠ 0 := by
          intro he
          have hh := hSign j
          rw [he,zero_mul] at hh
          exact (lt_irrefl 0) hh
        exact lt_of_le_of_ne (le_of_not_gt hh) hne
    have hF0E : F0.source ⊆ E.source := fun x hx => hE0E (hs ▸ hx)
    have hF0mark : Disjoint F0.source (M.cover.branch : Set S) := hs.symm ▸ hmarks
    have hz : (0:Plane) ∈ F0.target ∩ Metric.ball (0:Plane) ρ := by
      refine ⟨?_,by simpa using hρ⟩
      have hh := F0.map_source (hs.symm ▸ hpE)
      rwa [hFp] at hh
    obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp (F0.open_target.inter isOpen_ball) 0 hz
    have hmodelAB (j : D) (x : S) (hx : x ∈ F0.source) (hn : ‖F0 x‖ < ρ) :
        x ∈ (c (label j)).val.image ↔ F0 x ∈ segment ℝ (0:Plane) (a j) ∪ segment ℝ (0:Plane) (b j) := by
      dsimp [a,b]
      split_ifs
      · exact hModel (label j) x hx hn
      · rw [Set.union_comm]
        exact hModel (label j) x hx hn
    obtain ⟨F,δ,H,hFF0,hδ,hH,hleft0,hright0,hsegments,hpatch⟩ :=
      hMarkedCommonBankUniformPatch (c i0) (fun j => c (label j)) p E F0 hF0E
        (hs.symm ▸ hpE) hFp hEp hF0mark ρ η hρ hη hball hEaxis hAxis a b ha hb hmodelAB
    exact ⟨F,δ,H,fun x hx => hs ▸ hFF0 hx,hδ,hH,hleft0,hright0,hsegments,hpatch⟩
  have hActualCommonSideCoreChart : ∃ E0 : OpenPartialHomeomorph S Plane,
      Disjoint E0.source (M.cover.branch : Set S) ∧ P ⊆ E0.source ∧
      (∀ x ∈ E0.source, x ∈ b.val.image ↔ E0 x 1=0) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
        ψ '' Set.Icc δ (1-δ) ⊆ E0.source ∧
        (∀ t ∈ T, δ < t.val ∧ t.val < 1-δ) := by
    obtain ⟨δ,hδ,hδhalf,hTcore⟩ := hTuniform
    let f : C(Interval,S) := ⟨fun t => ψ (δ+t.val*(1-2*δ)),hψ.comp (by fun_prop)⟩
    have hθ (t : Interval) : δ ≤ δ+t.val*(1-2*δ) ∧ δ+t.val*(1-2*δ) ≤ 1-δ := by
      constructor <;> nlinarith [t.property.1,t.property.2]
    have hparam (t : Interval) : 0 < δ+t.val*(1-2*δ) ∧ δ+t.val*(1-2*δ) < 1 :=
      ⟨hδ.trans_le (hθ t).1,(hθ t).2.trans_lt (by linarith)⟩
    have hfree (t : Interval) : f t ∉ M.cover.branch := by
      intro hm
      let u := Set.projIcc 0 1 zero_le_one (δ+t.val*(1-2*δ))
      have hu : u.val=δ+t.val*(1-2*δ) := by
        dsimp [u]
        rw [Set.projIcc_of_mem zero_le_one ⟨(hparam t).1.le,(hparam t).2.le⟩]
      have hpD : B.secondSide u ∈ range B.disk := image_subset_range _ _
        (B.boundary_eq.symm ▸ (show B.secondSide u ∈ range B.firstSide ∪ range B.secondSide from
          Or.inr (Set.mem_range_self u)))
      have hm' : B.secondSide u ∈ M.cover.branch := hm
      rcases B.marks_are_corners _ hpD hm' with he|he
      · have ht0 := B.second_embedded.injective (he.trans B.second_zero.symm)
        have hh := congrArg Subtype.val ht0
        rw [hu] at hh
        change δ+t.val*(1-2*δ)=0 at hh
        linarith [(hparam t).1]
      · have ht1 := B.second_embedded.injective (he.trans B.second_one.symm)
        have hh := congrArg Subtype.val ht1
        rw [hu] at hh
        change δ+t.val*(1-2*δ)=1 at hh
        linarith [(hparam t).2]
    have hfsub : range f ⊆ arcInterior M b := by
      rintro x ⟨t,rfl⟩
      exact ⟨B.second_on_curve (Set.mem_range_self _),hfree t⟩
    have hfRange : range f=ψ '' Set.Icc δ (1-δ) := by
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨δ+t.val*(1-2*δ),hθ t,rfl⟩
      · rintro ⟨θ,hθ,rfl⟩
        have hd : 0 < 1-2*δ := by linarith
        let t : Interval := ⟨(θ-δ)/(1-2*δ),
          div_nonneg (sub_nonneg.mpr hθ.1) hd.le,
          (div_le_one hd).mpr (by linarith [hθ.2])⟩
        refine ⟨t,?_⟩
        change ψ (δ+((θ-δ)/(1-2*δ))*(1-2*δ))=ψ θ
        congr 1
        rw [div_mul_cancel₀ _ (ne_of_gt hd)]
        ring
    obtain ⟨U,V,hU,e,hV,hCV,hUMarks,hAxis,hfU⟩ := hActualCompactMarkFreeCarrierAxisChart b f hfsub
    have : Nonempty U := ⟨⟨f 0,hfU (Set.mem_range_self 0)⟩⟩
    let coeU : OpenPartialHomeomorph U S := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
    let z : U → Plane := fun u => (e u).val
    have hz : IsOpenEmbedding z := hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
    let coeE := hz.toOpenPartialHomeomorph z
    let E0 := coeU.symm.trans coeE
    have hs : E0.source=U := by simp [E0,coeU,coeE,IsOpenEmbedding.toOpenPartialHomeomorph_target]
    have hValue (x : S) (hx : x ∈ U) : E0 x=(e ⟨x,hx⟩).val := by
      have hu : coeU.symm x=⟨x,hx⟩ :=
        hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv (x := ⟨x,hx⟩)
      change z (coeU.symm x)=_
      rw [hu]
    have hCoreSource : ψ '' Set.Icc δ (1-δ) ⊆ E0.source := by
      rw [hs,← hfRange]
      exact hfU
    refine ⟨E0,hs.symm ▸ hUMarks,?_,?_,δ,hδ,hδhalf,hCoreSource,hTcore⟩
    · intro p hp
      obtain ⟨j,hj⟩ := hPold p hp
      obtain ⟨t,ht⟩ := hj.2
      have htT : t ∈ T := by change B.secondSide t ∈ P; exact ht.symm ▸ hp
      have htb := hTcore t htT
      apply hCoreSource
      refine ⟨t.val,⟨htb.1.le,htb.2.le⟩,?_⟩
      dsimp [ψ,Function.comp_def]
      rw [Set.projIcc_of_mem zero_le_one t.property]
      exact ht
    · intro x hx
      rw [hValue x (hs ▸ hx)]
      exact hAxis ⟨x,hs ▸ hx⟩
  have hActualBankedSourceContactPatch
      (E : OpenPartialHomeomorph S Plane)
      (hEaxis : ∀ x ∈ E.source, x ∈ b.val.image ↔ E x 1=0) (p : P)
      (hpCommon : p.val ∈ E.source) :
      ∃ F : OpenPartialHomeomorph S Plane, ∃ δ H : ℝ,
        F.source ⊆ contactU p ∩ E.source ∧ 0 < δ ∧ 0 < H ∧
        Plane.mk (-δ) 0 ∈ F.target ∧ Plane.mk δ 0 ∈ F.target ∧
        (∀ h : ℝ, 0 < h → h < H → segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ F.target) ∧
        ∀ h : ℝ, 0 < h → h < H → ∃ f : C(Interval,S),
          IsEmbedding f ∧ range f ⊆ F.source ∧
          range f=F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          f 0=F.symm (Plane.mk (-δ) h) ∧ f 1=F.symm (Plane.mk δ h) ∧
          (∀ x ∈ range f, 0 < E x 1) ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧ Disjoint (range f) b.val.image ∧
          ∀ j, f 0 ∉ (old j).val.image ∧ f 1 ∉ (old j).val.image ∧
            (range f ∩ (old j).val.image).Finite ∧
            (range f ∩ (old j).val.image).ncard ≤ if p.val ∈ (old j).val.image then 1 else 0 := by
    let I := {i : Option J // p.val ∈ (r i).val.image}
    let c : I → EssentialMarkedArc M := fun i => r i.val
    let D := {j : J // p.val ∈ (old j).val.image}
    obtain ⟨E0,hpE,hEU,hEmark,hE0,g,R,i0,hi0,hRop,hmodel⟩ :=
      hActualSourceContactRadialCore p E.source E.open_source hpCommon
    have hselected : c i0=araw := by
      change r i0.val=araw
      rw [hi0]
      rfl
    have hlocalEq (x : S) (hx : x ∈ contactU p) : x ∈ araw.val.image ↔ x ∈ b.val.image := by
      have hnot : x ∉ KrawDerived ∪ Kother := fun hk => Set.disjoint_left.mp (hContactURemainders p) hx hk
      rw [himageRaw,hOtherDecomp]
      constructor
      · intro hh
        exact Or.inl (hh.resolve_right (fun hk => hnot (Or.inl hk)))
      · intro hh
        exact Or.inl (hh.resolve_right (fun hk => hnot (Or.inr hk)))
    let E' := E.restrOpen (contactU p) (hContactUOpen p)
    have hE's : E'.source=E.source ∩ contactU p := rfl
    have hE0E' : E0.source ⊆ E'.source := fun x hx => ⟨(hEU hx).2,(hEU hx).1⟩
    have hpB : p.val ∈ b.val.image := by
      obtain ⟨j,hj⟩ := hPold p.val p.property
      exact B.second_on_curve hj.2
    have hE'p : E' p.val 1=0 := (hEaxis _ hpCommon).mp hpB
    have hE'axis (x : S) (hx : x ∈ E'.source) : x ∈ (c i0).val.image ↔ E' x 1=0 := by
      rw [hselected,hlocalEq x hx.2]
      exact hEaxis x hx.1
    let label : D → I := fun j => ⟨some j.val,j.property⟩
    have hcross (j : D) : CrossesInDisk M (c i0) (c (label j)) p.val := by
      rw [hselected]
      have hpfree : p.val ∉ M.cover.branch := fun hm => Set.disjoint_left.mp hEmark hpE hm
      have hpraw : p.val ∈ araw.val.image := hselected ▸ i0.property
      exact hRawAllOldTransverse j.val p.val ⟨⟨hpraw,hpfree⟩,j.property,hpfree⟩
    have hmeet (j : D) (x : S) (hx : x ∈ E0.source)
        (hc : x ∈ (c i0).val.image ∩ (c (label j)).val.image) : x=p.val := by
      rw [hselected] at hc
      exact hContactUMeet p none (some j.val) (by simp) ⟨(hEU hx).1,hc⟩
    obtain ⟨F,δ,H,hFE,hδ,hH,hleft0,hright0,hsegments,hpatch⟩ :=
      hMarkedBankedActualFanPatch c p.val E0 hpE hE0 hEmark (fun j => E0 ∘ g j)
        R i0 hRop hmodel label hcross hmeet E' hE0E' hE'p hE'axis
    have hFU : F.source ⊆ contactU p ∩ E.source := hFE.trans hEU
    refine ⟨F,δ,H,hFU,hδ,hH,hleft0,hright0,hsegments,?_⟩
    intro h hh hhH
    obtain ⟨f,hfi,hfF,hfr,hf0,hf1,hbank,hfmark,hfoff,hcounts⟩ := hpatch h hh hhH
    have hfU : range f ⊆ contactU p := fun x hx => (hFU (hfF hx)).1
    have hfb : Disjoint (range f) b.val.image := by
      apply Set.disjoint_left.mpr
      intro x hx hxb
      have hxa : x ∈ (c i0).val.image := by
        rw [hselected]
        exact (hlocalEq x (hfU hx)).mpr hxb
      exact Set.disjoint_left.mp hfoff hx hxa
    refine ⟨f,hfi,hfF,hfr,hf0,hf1,hbank,hfmark,hfb,?_⟩
    intro j
    by_cases hj : p.val ∈ (old j).val.image
    · rw [if_pos hj]
      exact hcounts ⟨j,hj⟩
    · rw [if_neg hj]
      have hd : Disjoint (range f) (old j).val.image :=
        (hContactUNonincident p j hj).mono_left hfU
      have he : range f ∩ (old j).val.image=∅ := Set.disjoint_iff_inter_eq_empty.mp hd
      refine ⟨(fun hx => Set.disjoint_left.mp hd (Set.mem_range_self 0) hx),
        (fun hx => Set.disjoint_left.mp hd (Set.mem_range_self 1) hx),?_,?_⟩
      · rw [he]; exact Set.finite_empty
      · rw [he,Set.ncard_empty]
  have hMarkedEndpointRayClearance {I : Type} [Fintype I]
      (v : I → Plane) (hside : ∀ i, v i 1=0 → v i 0 ≤ 0) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, |h| < ε →
        ∀ i, segment ℝ (0:Plane) (Plane.mk 1 h) ∩ segment ℝ (0:Plane) (v i)={0} := by
    let Q : I → Set Plane := fun i => if v i 1=0 then {z | z 0 ≤ 0}
      else {z | v i 1*z 0-v i 0*z 1=0}
    have hQclosed (i : I) : IsClosed (Q i) := by
      dsimp [Q]
      split_ifs
      · exact isClosed_le (by fun_prop) continuous_const
      · exact isClosed_eq (by fun_prop) continuous_const
    let W : Set Plane := (⋃ i, Q i)ᶜ
    have hW : IsOpen W := (isClosed_iUnion_of_finite hQclosed).isOpen_compl
    have hbase : Plane.mk 1 0 ∈ W := by
      intro hh
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hh
      dsimp [Q] at hi
      split_ifs at hi with hv
      · change (1:ℝ) ≤ 0 at hi; linarith
      · change v i 1*1-v i 0*0=0 at hi
        exact hv (by simpa using hi)
    let q : ℝ → Plane := fun h => Plane.mk 1 h
    have hq : Continuous q := by fun_prop
    have hz : (0:ℝ) ∈ q ⁻¹' W := hbase
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (hW.preimage hq) 0 hz
    refine ⟨ε,hε,?_⟩
    intro h hh i
    have hendpoint : Plane.mk 1 h ∈ W := hball (by simpa [Metric.mem_ball,Real.dist_eq] using hh)
    have hnotQ : Plane.mk 1 h ∉ Q i := fun hx => hendpoint (Set.mem_iUnion.mpr ⟨i,hx⟩)
    ext z
    constructor
    · rintro ⟨hzNew,hzOld⟩
      rw [segment_eq_image'] at hzNew hzOld
      obtain ⟨t,ht,he⟩ := hzNew
      obtain ⟨u,hu,hue⟩ := hzOld
      have hz0 : z 0=t := by
        have hh := congrArg (fun z : Plane => z 0) he
        change 0+t*(1-0)=z 0 at hh
        simpa using hh.symm
      have hz1 : z 1=t*h := by
        have hh := congrArg (fun z : Plane => z 1) he
        change 0+t*(h-0)=z 1 at hh
        simpa using hh.symm
      have hzOld0 : z 0=u*v i 0 := by
        have hh := congrArg (fun z : Plane => z 0) hue
        change 0+u*(v i 0-0)=z 0 at hh
        simpa using hh.symm
      have hzOld1 : z 1=u*v i 1 := by
        have hh := congrArg (fun z : Plane => z 1) hue
        change 0+u*(v i 1-0)=z 1 at hh
        simpa using hh.symm
      have ht0 : t=0 := by
        by_contra hn
        have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hn)
        apply hnotQ
        dsimp [Q]
        split_ifs with hv
        · change (1:ℝ) ≤ 0
          have hvx := hside i hv
          have hzneg : z 0 ≤ 0 := hzOld0 ▸ mul_nonpos_of_nonneg_of_nonpos hu.1 hvx
          rw [hz0] at hzneg
          linarith
        · change v i 1*1-v i 0*h=0
          have hcancel : t*(v i 1-v i 0*h)=0 := by
            calc
              t*(v i 1-v i 0*h)=t*v i 1-v i 0*(t*h) := by ring
              _ = z 0*v i 1-v i 0*z 1 := by rw [← hz1,← hz0]
              _ = 0 := by rw [hzOld0,hzOld1]; ring
          simpa using (mul_eq_zero.mp hcancel).resolve_left hn
      have hz : z=0 := by
        ext k
        fin_cases k
        · simpa [ht0] using hz0
        · simpa [ht0] using hz1
      exact Set.mem_singleton_iff.mpr hz
    · rintro rfl
      exact ⟨left_mem_segment ℝ _ _,left_mem_segment ℝ _ _⟩
  have hMarkedEndpointSectorConnector {I : Type} [Fintype I]
      (d : I → EssentialMarkedArc M) (side : EssentialMarkedArc M)
      (p : S) (hpmark : p ∈ M.cover.branch)
      (F : OpenPartialHomeomorph S Plane) (hpF : p ∈ F.source) (hFp : F p=0)
      (hmarks : ∀ x ∈ F.source, x ∈ M.cover.branch ↔ x=p)
      (hpSide : p ∈ side.val.image)
      (haxis : ∀ x ∈ F.source, x ∈ side.val.image → F x 1=0)
      (η : ℝ) (hη : 0 < η) (hball : Metric.ball (0:Plane) η ⊆ F.target)
      (v : I × Bool → Plane) (hv : ∀ i, v i 1=0 → v i 0 ≤ 0)
      (hmodel : ∀ i x, x ∈ F.source → F x ∈ Metric.ball (0:Plane) η →
        (x ∈ (d i).val.image ↔ F x ∈ segment ℝ (0:Plane) (v (i,false)) ∪
          segment ℝ (0:Plane) (v (i,true)))) :
      ∃ ell ε : ℝ, 0 < ell ∧ ell < 1 ∧ 0 < ε ∧ ∀ h : ℝ, h ≠ 0 → |h| < ε →
        ∃ f : C(Interval,S), IsEmbedding f ∧ f 0=p ∧
          f 1=F.symm (Plane.mk ell (ell*h)) ∧ range f ⊆ F.source ∧
          range f ∩ side.val.image={p} ∧ range f ∩ (M.cover.branch : Set S)={p} ∧
          ∀ i, Disjoint (range f) (arcInterior M (d i)) := by
    obtain ⟨ε0,hε0,havoid⟩ := hMarkedEndpointRayClearance v hv
    have hOpenell : IsOpen {ell : ℝ | Plane.mk ell 0 ∈ Metric.ball (0:Plane) η} :=
      isOpen_ball.preimage (by fun_prop)
    have hzell : (0:ℝ) ∈ {ell : ℝ | Plane.mk ell 0 ∈ Metric.ball (0:Plane) η} := by
      have hz : Plane.mk (0:ℝ) 0=(0:Plane) := by ext i; fin_cases i <;> rfl
      change Plane.mk (0:ℝ) 0 ∈ Metric.ball (0:Plane) η
      rw [hz]
      simpa using hη
    obtain ⟨r,hr,hrball⟩ := Metric.isOpen_iff.mp hOpenell 0 hzell
    let ell := min r 1/2
    have hell : 0 < ell := half_pos (lt_min hr zero_lt_one)
    have hellr : ell < r := by dsimp [ell]; linarith [min_le_left r 1]
    have hell1 : ell < 1 := by dsimp [ell]; linarith [min_le_right r 1]
    have hbase : Plane.mk ell 0 ∈ Metric.ball (0:Plane) η :=
      hrball (by simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hell] using hellr)
    have hOpenh : IsOpen {h : ℝ | Plane.mk ell (ell*h) ∈ Metric.ball (0:Plane) η} :=
      isOpen_ball.preimage (by fun_prop)
    have h0h : (0:ℝ) ∈ {h : ℝ | Plane.mk ell (ell*h) ∈ Metric.ball (0:Plane) η} := by simpa using hbase
    obtain ⟨ε1,hε1,hεball⟩ := Metric.isOpen_iff.mp hOpenh 0 h0h
    let ε := min ε0 ε1
    have hε : 0 < ε := lt_min hε0 hε1
    refine ⟨ell,ε,hell,hell1,hε,?_⟩
    intro h hne hh
    have hh0 : |h| < ε0 := hh.trans_le (min_le_left _ _)
    have hh1 : |h| < ε1 := hh.trans_le (min_le_right _ _)
    let z := Plane.mk ell (ell*h)
    let C := segment ℝ (0:Plane) z
    have hzball : z ∈ Metric.ball (0:Plane) η := hεball (by simpa [Metric.mem_ball,Real.dist_eq] using hh1)
    have hCball : C ⊆ Metric.ball (0:Plane) η :=
      (convex_ball (0:Plane) η).segment_subset (by simpa using hη) hzball
    have hCt : C ⊆ F.target := hCball.trans hball
    have hzne : (0:Plane) ≠ z := by
      intro he
      have hh := congrArg (fun z : Plane => z 0) he
      change 0=ell at hh
      linarith
    have hEnd : F.symm z ∈ F.source := F.map_target (hCt (right_mem_segment ℝ _ _))
    have hArc : Schoenflies.IsArcBetween C (F p) (F (F.symm z)) := by
      rw [hFp,F.right_inv (hCt (right_mem_segment ℝ _ _))]
      exact Schoenflies.isArcBetween_segment hzne
    obtain ⟨f,hfi,hfr,hf0,hf1⟩ := CurveComplex.actual_pullback_chart_arc F p (F.symm z) hpF hEnd C hArc hCt
    have hfsub : range f ⊆ F.source := by
      rw [hfr]
      rintro x ⟨q,hq,rfl⟩
      exact F.map_target (hCt hq)
    have hzray : z ∈ segment ℝ (0:Plane) (Plane.mk 1 h) := by
      rw [segment_eq_image']
      refine ⟨ell,⟨hell.le,hell1.le⟩,?_⟩
      ext i
      fin_cases i <;> simp [z,Plane.mk] <;> ring
    have hCray : C ⊆ segment ℝ (0:Plane) (Plane.mk 1 h) :=
      (convex_segment (0:Plane) (Plane.mk 1 h)).segment_subset (left_mem_segment ℝ _ _) hzray
    have hFyZero (q : Plane) (hq : q ∈ C) (hy : q 1=0) : q=0 := by
      change q ∈ segment ℝ (0:Plane) z at hq
      rw [segment_eq_image'] at hq
      obtain ⟨t,ht,he⟩ := hq
      have hy' := congrArg (fun z : Plane => z 1) he
      change 0+t*(ell*h-0)=q 1 at hy'
      have ht0 : t=0 := (mul_eq_zero.mp (by simpa [hy] using hy')).resolve_right (mul_ne_zero (ne_of_gt hell) hne)
      subst t
      simpa using he.symm
    have hSurfaceZero (q : Plane) (hq : q ∈ C) (hq0 : q=0) : F.symm q=p := by
      rw [hq0,← hFp,F.left_inv hpF]
    have hSideMeet : range f ∩ side.val.image={p} := by
      ext x
      constructor
      · rintro ⟨hxf,hxs⟩
        rw [hfr] at hxf
        obtain ⟨q,hq,rfl⟩ := hxf
        have hy := haxis _ (F.map_target (hCt hq)) hxs
        rw [F.right_inv (hCt hq)] at hy
        exact Set.mem_singleton_iff.mpr (hSurfaceZero q hq (hFyZero q hq hy))
      · intro hxP
        change x=p at hxP
        subst x
        refine ⟨⟨0,hf0⟩,?_⟩
        exact hpSide
    have hMarkMeet : range f ∩ (M.cover.branch : Set S)={p} := by
      ext x
      constructor
      · rintro ⟨hxf,hxm⟩
        exact Set.mem_singleton_iff.mpr ((hmarks x (hfsub hxf)).mp hxm)
      · intro hxP
        change x=p at hxP
        subst x
        exact ⟨⟨0,hf0⟩,hpmark⟩
    refine ⟨f,hfi,hf0,hf1,hfsub,hSideMeet,hMarkMeet,?_⟩
    intro i
    apply Set.disjoint_left.mpr
    intro x hxf hxi
    rw [hfr] at hxf
    obtain ⟨q,hq,rfl⟩ := hxf
    have hqS := F.map_target (hCt hq)
    have hqN : F (F.symm q) ∈ Metric.ball (0:Plane) η := by rw [F.right_inv (hCt hq)]; exact hCball hq
    have hvRay := (hmodel i _ hqS hqN).mp hxi.1
    rw [F.right_inv (hCt hq)] at hvRay
    have hq0 : q=0 := by
      rcases hvRay with hvRay|hvRay
      · have hm : q ∈ segment ℝ (0:Plane) (Plane.mk 1 h) ∩ segment ℝ (0:Plane) (v (i,false)) := ⟨hCray hq,hvRay⟩
        rw [havoid h hh0 (i,false)] at hm
        exact hm
      · have hm : q ∈ segment ℝ (0:Plane) (Plane.mk 1 h) ∩ segment ℝ (0:Plane) (v (i,true)) := ⟨hCray hq,hvRay⟩
        rw [havoid h hh0 (i,true)] at hm
        exact hm
    exact hxi.2 ((hSurfaceZero q hq hq0).symm ▸ hpmark)
  have hActualSelectedSideEndpointLabel
      (p : S) (hpmark : p ∈ M.cover.branch)
      (hpcorner : p ∈ ({B.firstCorner,B.secondCorner} : Set S)) :
      ∃ terminal : Bool, ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrhalf : r < 1/2,
        (if terminal then b.val.map 1 else b.val.map 0)=p ∧
        range (b.val.map ∘ endpointGermParameter terminal r hr (by linarith)) ⊆ range B.secondSide := by
    let γ := b.val.map ∘ Set.projIcc 0 1 zero_le_one
    have hpends : p ∈ ({γ Lother,γ Rother} : Set S) := hOtherPorts.symm ▸ hpcorner
    rcases hpends with hpL|hpR
    · have hm : γ Lother ∈ M.cover.branch := hpL ▸ hpmark
      have hL01 : Lother ∈ Set.Icc (0:ℝ) 1 := ⟨hLother,hLRother.le.trans hRother⟩
      obtain he|he := b.val.marked_only_at_ends (Set.projIcc 0 1 zero_le_one Lother) hm
      all_goals have hh := congrArg Subtype.val he
      · have hL0 : Lother=0 := by simpa only [Set.projIcc_of_mem zero_le_one hL01] using hh
        let r := Rother/4
        have hr : 0 < r := by dsimp [r]; linarith
        have hrhalf : r < 1/2 := by dsimp [r]; linarith
        refine ⟨false,r,hr,hrhalf,?_,?_⟩
        · have hep : γ Lother=b.val.map 0 := by simp [γ,hL0]
          exact hep.symm.trans hpL.symm
        · rintro x ⟨t,rfl⟩
          rw [hOtherSide]
          have hθ : r*t.val ∈ Set.Icc Lother Rother := by
            constructor <;> dsimp [r] <;> nlinarith [t.property.1,t.property.2]
          refine ⟨r*t.val,hθ,?_⟩
          dsimp only [Function.comp_apply]
          rw [Set.projIcc_of_mem zero_le_one ⟨hLother.trans hθ.1,hθ.2.trans hRother⟩]
          rfl
      · have hL1 : Lother=1 := by simpa only [Set.projIcc_of_mem zero_le_one hL01] using hh
        linarith
    · have hm : γ Rother ∈ M.cover.branch := hpR ▸ hpmark
      have hR01 : Rother ∈ Set.Icc (0:ℝ) 1 := ⟨hLother.trans hLRother.le,hRother⟩
      obtain he|he := b.val.marked_only_at_ends (Set.projIcc 0 1 zero_le_one Rother) hm
      all_goals have hh := congrArg Subtype.val he
      · have hR0 : Rother=0 := by simpa only [Set.projIcc_of_mem zero_le_one hR01] using hh
        linarith
      · have hR1 : Rother=1 := by simpa only [Set.projIcc_of_mem zero_le_one hR01] using hh
        let r := (1-Lother)/4
        have hr : 0 < r := by dsimp [r]; linarith
        have hrhalf : r < 1/2 := by dsimp [r]; linarith
        refine ⟨true,r,hr,hrhalf,?_,?_⟩
        · have hep : γ Rother=b.val.map 1 := by simp [γ,hR1]
          exact hep.symm.trans hpR.symm
        · rintro x ⟨t,rfl⟩
          rw [hOtherSide]
          have hθ : 1-r*t.val ∈ Set.Icc Lother Rother := by
            constructor <;> dsimp [r] <;> nlinarith [t.property.1,t.property.2]
          refine ⟨1-r*t.val,hθ,?_⟩
          dsimp only [Function.comp_apply]
          rw [Set.projIcc_of_mem zero_le_one ⟨hLother.trans hθ.1,hθ.2.trans hRother⟩]
          rfl
  have hActualMarkedEndpointSector
      (p : S) (hpmark : p ∈ M.cover.branch) (W : Set S) (hW : IsOpen W) (hpW : p ∈ W)
      (terminal : Bool) (hendpoint : (if terminal then b.val.map 1 else b.val.map 0)=p) :
      ∃ F : OpenPartialHomeomorph S Plane,
        p ∈ F.source ∧ F p=0 ∧ F.source ⊆ W ∧
        ∃ ell ε : ℝ, 0 < ell ∧ ell < 1 ∧ 0 < ε ∧ ∀ h : ℝ, h ≠ 0 → |h| < ε →
        ∃ f : C(Interval,S), IsEmbedding f ∧ f 0=p ∧
          f 1=F.symm (Plane.mk ell (ell*h)) ∧ range f ⊆ F.source ∧
          range f ∩ b.val.image={p} ∧ range f ∩ (M.cover.branch : Set S)={p} ∧
          ∀ j, Disjoint (range f) (arcInterior M (old j)) := by
    let c : Option J → EssentialMarkedArc M := fun i => i.elim b old
    have hcfinite (i k : Option J) (hik : i ≠ k) : (crossings M (c i) (c k)).Finite := by
      cases i with
      | none =>
        cases k with
        | none => exact (hik rfl).elim
        | some j => exact (hb j).1
      | some i =>
        cases k with
        | none =>
          have he : crossings M (old i) b=crossings M b (old i) := Set.inter_comm _ _
          exact he.symm ▸ (hb i).1
        | some k => exact (hOld i k (fun he => hik (congrArg Option.some he))).1
    let incident : Option J × Bool → Prop := fun g =>
      (if g.2 then (c g.1).val.map 1 else (c g.1).val.map 0)=p
    obtain ⟨F0,hpF0,hF0p,hF0W,hF0marks,r0,hr0,hr0half,v,hvn,hunit,hopp,hnegative,
      hmeet,hgerms,δ,hδ,hδball,hδnorm,hwhole,htails⟩ :=
      actual_marked_endpoint_source_fan_chart M c hcfinite p hpmark W hW hpW (none,terminal) hendpoint
    let F := F0.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0:Plane) δ) isOpen_ball)
    have hFs : F.source=F0.source ∩ F0 ⁻¹' Metric.ball (0:Plane) δ := by
      simp [F,OpenPartialHomeomorph.trans_source]
    have hFval (x : S) : F x=F0 x := rfl
    have hpF : p ∈ F.source := by
      rw [hFs]
      refine ⟨hpF0,?_⟩
      change F0 p ∈ Metric.ball (0:Plane) δ
      rw [hF0p]
      simpa using hδ
    have hFp : F p=0 := hF0p
    have hFsub : F.source ⊆ F0.source := fun x hx => (hFs ▸ hx).1
    have hFmodel (i : Option J) (x : S) (hx : x ∈ F.source) :
        x ∈ (c i).val.image ↔ ∃ t : Bool, incident (i,t) ∧ F x ∈ segment ℝ (0:Plane) (v (i,t)) :=
      hwhole i x (hFsub hx) (hFs ▸ hx).2
    have hFmarks (x : S) (hx : x ∈ F.source) : x ∈ M.cover.branch ↔ x=p := by
      constructor
      · intro hm
        exact Set.mem_singleton_iff.mp (hF0marks ▸ ⟨hFsub hx,hm⟩)
      · intro he
        exact he.symm ▸ hpmark
    have hpB : p ∈ b.val.image := by
      cases terminal
      · exact ⟨0,hendpoint⟩
      · exact ⟨1,hendpoint⟩
    have hAxis (x : S) (hx : x ∈ F.source) (hxb : x ∈ b.val.image) : F x 1=0 := by
      obtain ⟨t,ht,hseg⟩ := (hFmodel none x hx).mp hxb
      have hvy : v (none,t) 1=0 := by
        have hchoice : t=terminal ∨ t=(!terminal) := by cases t <;> cases terminal <;> simp
        rcases hchoice with rfl|rfl
        · rw [hunit]; rfl
        · rw [hopp ht]; rfl
      rw [segment_eq_image'] at hseg
      obtain ⟨u,hu,he⟩ := hseg
      have hh := congrArg (fun z : Plane => z 1) he
      change 0+u*(v (none,t) 1-0)=F x 1 at hh
      simpa [hvy] using hh.symm
    let D := {j : J // p ∈ (old j).val.image}
    let d : D → EssentialMarkedArc M := fun j => old j.val
    let w : D × Bool → Plane := fun g => if incident (some g.1.val,g.2) then v (some g.1.val,g.2) else 0
    have hw (g : D × Bool) (hy : w g 1=0) : w g 0 ≤ 0 := by
      dsimp [w] at hy ⊢
      split_ifs with hi
      · exact hnegative (some g.1.val,g.2) hi (by intro he; have hh := congrArg Prod.fst he; cases hh) (by simpa only [if_pos hi] using hy)
      · simp
    have hdmodel (j : D) (x : S) (hx : x ∈ F.source) :
        x ∈ (d j).val.image ↔ F x ∈ segment ℝ (0:Plane) (w (j,false)) ∪ segment ℝ (0:Plane) (w (j,true)) := by
      constructor
      · intro hh
        obtain ⟨t,ht,hseg⟩ := (hFmodel (some j.val) x hx).mp hh
        have hwv : w (j,t)=v (some j.val,t) := by simp only [w,if_pos ht]
        cases t
        · exact Or.inl (hwv.symm ▸ hseg)
        · exact Or.inr (hwv.symm ▸ hseg)
      · intro hh
        have hOne (t : Bool) (hseg : F x ∈ segment ℝ (0:Plane) (w (j,t))) : x ∈ (d j).val.image := by
          by_cases hi : incident (some j.val,t)
          · apply (hFmodel (some j.val) x hx).mpr
            refine ⟨t,hi,?_⟩
            simpa only [w,if_pos hi] using hseg
          · have hz : F x=0 := by simpa [w,hi] using hseg
            have he : x=p := F.injOn hx hpF (hz.trans hFp.symm)
            exact he.symm ▸ j.property
        exact hh.elim (hOne false) (hOne true)
    have hzTarget : (0:Plane) ∈ F.target := hFp ▸ F.map_source hpF
    obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp F.open_target 0 hzTarget
    obtain ⟨ell,ε,hell,hell1,hε,hsector⟩ := hMarkedEndpointSectorConnector d b p hpmark F hpF hFp
      hFmarks hpB hAxis η hη hball w hw (fun j x hx _ => hdmodel j x hx)
    refine ⟨F,hpF,hFp,hFsub.trans hF0W,ell,ε,hell,hell1,hε,?_⟩
    intro h hh hhε
    obtain ⟨f,hfi,hf0,hf1,hfF,hfb,hfm,hfd⟩ := hsector h hh hhε
    refine ⟨f,hfi,hf0,hf1,hfF,hfb,hfm,?_⟩
    intro j
    by_cases hj : p ∈ (old j).val.image
    · exact hfd ⟨j,hj⟩
    · apply Set.disjoint_left.mpr
      intro x hx hxold
      obtain ⟨t,ht,hseg⟩ := (hFmodel (some j) x (hfF hx)).mp hxold.1
      have hpold : p ∈ (old j).val.image := by
        cases t
        · exact ⟨0,ht⟩
        · exact ⟨1,ht⟩
      exact hj hpold
  have hPositiveRadialGraph (a b z : Plane) (ha : 0 < a 1) (hb : b 1 < 0)
      (hz : 0 < z 1) (hzn : ‖z‖ < ‖a‖) :
      (z ∈ segment ℝ (0:Plane) a ∪ segment ℝ (0:Plane) b) ↔ z 0=(a 0/a 1)*z 1 := by
    have ha0 : a 1 ≠ 0 := ne_of_gt ha
    constructor
    · intro hseg
      rcases hseg with hseg|hseg
      · rw [segment_eq_image'] at hseg
        obtain ⟨t,ht,he⟩ := hseg
        have h0 := congrArg (fun z : Plane => z 0) he
        have h1 := congrArg (fun z : Plane => z 1) he
        change 0+t*(a 0-0)=z 0 at h0
        change 0+t*(a 1-0)=z 1 at h1
        rw [← h0,← h1]
        field_simp
        ring
      · rw [segment_eq_image'] at hseg
        obtain ⟨t,ht,he⟩ := hseg
        have h1 := congrArg (fun z : Plane => z 1) he
        change 0+t*(b 1-0)=z 1 at h1
        have hle := mul_nonpos_of_nonneg_of_nonpos ht.1 hb.le
        nlinarith
    · intro hgraph
      let t := z 1/a 1
      have ht : 0 < t := div_pos hz ha
      have hvec : z=t • a := by
        ext i
        fin_cases i
        · change z 0=t*a 0
          rw [hgraph]
          dsimp [t]
          ring
        · change z 1=t*a 1
          dsimp [t]
          rw [div_mul_cancel₀ _ ha0]
      have han : 0 < ‖a‖ := norm_pos_iff.mpr (fun he => by
        have hh := congrArg (fun z : Plane => z 1) he
        change a 1=0 at hh
        linarith)
      have ht1 : t < 1 := by
        rw [hvec,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hzn
        nlinarith
      left
      rw [segment_eq_image']
      refine ⟨t,⟨ht.le,ht1.le⟩,?_⟩
      rw [hvec]
      ext i
      simp
  have hMarkedRadialHorizontalTransverse
      (d c : EssentialMarkedArc M) (F : OpenPartialHomeomorph S Plane)
      (p : S) (hpF : p ∈ F.source) (hmark : Disjoint F.source (M.cover.branch : Set S))
      (a b : Plane) (ha : 0 < a 1) (hb : b 1 < 0) (h : ℝ) (hh : 0 < h)
      (hpy : F p 1=h) (hpn : ‖F p‖ < ‖a‖)
      (hOld : ∀ x ∈ F.source, x ∈ d.val.image ↔ F x ∈
        segment ℝ (0:Plane) a ∪ segment ℝ (0:Plane) b)
      (hNew : ∀ x ∈ F.source, x ∈ c.val.image ↔ F x 1=h)
      (hpd : p ∈ d.val.image) : CrossesInDisk M c d p := by
    let O : Set S := F.source ∩ F ⁻¹' (Metric.ball (0:Plane) ‖a‖ ∩ {z : Plane | 0 < z 1})
    have hO : IsOpen O := F.isOpen_inter_preimage
      (isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop)))
    have hpO : p ∈ O := ⟨hpF,by simpa [Metric.mem_ball,dist_zero_right] using hpn,by change 0 < F p 1; rw [hpy]; exact hh⟩
    let Q := F.restrOpen O hO
    have hQs : Q.source=F.source ∩ O := rfl
    have hpQ : p ∈ Q.source := ⟨hpF,hpO⟩
    have hQold (x : S) (hx : x ∈ Q.source) : x ∈ d.val.image ↔ F x 0=(a 0/a 1)*F x 1 := by
      rw [hOld x hx.1]
      exact hPositiveRadialGraph a b (F x) ha hb hx.2.2.2
        (by simpa [Metric.mem_ball,dist_zero_right] using hx.2.2.1)
    let k := a 0/a 1
    let shear : Plane ≃ₜ Plane := {
      toEquiv := {
        toFun := fun z => Plane.mk (z 0-k*z 1) (z 1)
        invFun := fun z => Plane.mk (z 0+k*z 1) (z 1)
        left_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk] <;> ring
        right_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk] <;> ring }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let E0 := Q.transHomeomorph shear
    have hEs : E0.source=Q.source := rfl
    have hE0 (x : S) : E0 x 0=F x 0-k*F x 1 := rfl
    have hE1 (x : S) : E0 x 1=F x 1 := rfl
    have hp0 : E0 p 0=0 := by
      rw [hE0]
      exact sub_eq_zero.mpr ((hQold p hpQ).mp hpd)
    apply hSymm
    apply actual_affine_graph_crosses_in_disk M d c E0 p hpQ
      (hmark.mono_left (fun x hx => hx.1)) hp0 0
    · intro x hx
      rw [hE0,sub_eq_zero]
      exact hQold x hx
    · intro x hx
      rw [hE1,hE1,hpy,zero_mul,add_zero]
      exact hNew x hx.1
  have hActualContactCoreTailNeighborhood
      (E : OpenPartialHomeomorph S Plane) (t : T)
      (hpE : ψ t.val.val ∈ E.source) :
      ∃ V : Set S, IsOpen V ∧ ψ t.val.val ∈ V ∧ V ⊆ E.source ∧
        ∀ u : ℝ, u ∈ Set.Icc 0 1 → ψ u ∈ V → coreLeft t < u ∧ u < coreRight t := by
    let K : Set S := ψ '' Set.Icc 0 (coreLeft t) ∪ ψ '' Set.Icc (coreRight t) 1
    have hK : IsCompact K :=
      (isCompact_Icc.image hψ).union (isCompact_Icc.image hψ)
    have hψinj (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
        (he : ψ u=ψ v) : u=v := by
      change B.secondSide (Set.projIcc 0 1 zero_le_one u)=
        B.secondSide (Set.projIcc 0 1 zero_le_one v) at he
      have hh := congrArg Subtype.val (B.second_embedded.injective he)
      simpa only [Set.projIcc_of_mem zero_le_one hu,Set.projIcc_of_mem zero_le_one hv] using hh
    have hpnot : ψ t.val.val ∉ K := by
      intro hh
      rcases hh with ⟨u,hu,he⟩|⟨u,hu,he⟩
      · have hueq := hψinj u t.val.val ⟨hu.1,hu.2.trans ((hCoreLeft t).le.trans ((hCoreRight t).le.trans (hCore1 t).le))⟩ t.val.property he
        have htl := hu.2
        rw [hueq] at htl
        exact (not_le_of_gt (hCoreLeft t)) htl
      · have hueq := hψinj u t.val.val ⟨(hCore0 t).le.trans ((hCoreLeft t).le.trans ((hCoreRight t).le.trans hu.1)),hu.2⟩ t.val.property he
        have htr := hu.1
        rw [hueq] at htr
        exact (not_le_of_gt (hCoreRight t)) htr
    let V : Set S := E.source ∩ Kᶜ
    refine ⟨V,E.open_source.inter hK.isClosed.isOpen_compl,⟨hpE,hpnot⟩,fun x hx => hx.1,?_⟩
    intro u hu hx
    constructor
    · by_contra hh
      exact hx.2 (Or.inl ⟨u,⟨hu.1,le_of_not_gt hh⟩,rfl⟩)
    · by_contra hh
      exact hx.2 (Or.inr ⟨u,⟨le_of_not_gt hh,hu.2⟩,rfl⟩)
  obtain ⟨commonE,hCommonMark,hCommonP,hCommonAxis,commonδ,hCommonδ,hCommonδhalf,
    hCommonCarrier,hCommonContactCore⟩ := hActualCommonSideCoreChart
  have hActualContactSourceParameter (p : P) :
      ∃ t : T, B.secondSide t.val=p.val ∧ ψ t.val.val=p.val := by
    obtain ⟨j,hj⟩ := hPold p.val p.property
    obtain ⟨t,ht⟩ := hj.2
    have htT : t ∈ T := by
      change B.secondSide t ∈ P
      exact ht.symm ▸ p.property
    refine ⟨⟨t,htT⟩,ht,?_⟩
    change B.secondSide (Set.projIcc 0 1 zero_le_one t.val)=p.val
    rw [Set.projIcc_of_mem zero_le_one t.property]
    exact ht
  choose contactParam hContactParam hContactParamΨ using hActualContactSourceParameter
  have hActualContactLocalizedOpen (p : P) :
      ∃ V : Set S, IsOpen V ∧ p.val ∈ V ∧ V ⊆ commonE.source ∧
        ∀ u : ℝ, u ∈ Set.Icc 0 1 → ψ u ∈ V →
          coreLeft (contactParam p) < u ∧ u < coreRight (contactParam p) := by
    obtain ⟨V,hV,hpV,hVE,hparameters⟩ := hActualContactCoreTailNeighborhood commonE (contactParam p)
      (hContactParamΨ p |>.symm ▸ hCommonP p.property)
    exact ⟨V,hV,hContactParamΨ p ▸ hpV,hVE,hparameters⟩
  choose contactCoreV hContactCoreVOpen hContactCoreVPoint hContactCoreVGlobal hContactCoreVParameters
    using hActualContactLocalizedOpen
  choose patchF patchδ patchH hPatchSource hPatchδ hPatchH hPatchLeft0 hPatchRight0
    hPatchSegments hPatchFamily using
      (fun p : P => hActualBankedSourceContactPatch
        (commonE.restrOpen (contactCoreV p) (hContactCoreVOpen p))
        (fun x hx => hCommonAxis x hx.1) p ⟨hCommonP p.property,hContactCoreVPoint p⟩)
  have hActualPatchSourceParameterLocal (p : P) (u : ℝ) (hu : u ∈ Set.Icc 0 1)
      (hx : ψ u ∈ (patchF p).source) :
      coreLeft (contactParam p) < u ∧ u < coreRight (contactParam p) :=
    hContactCoreVParameters p u hu (hPatchSource p hx).2.2
  have hCommonHeight : ∃ H : ℝ, 0 < H ∧ ∀ p : P, H < patchH p := by
    let O : Set ℝ := {h | ∀ p : P, h < patchH p}
    have hO : IsOpen O := by
      have hh : O=⋂ p : P, Set.Iio (patchH p) := by ext h; simp [O]
      rw [hh]
      exact isOpen_iInter_of_finite (fun p => isOpen_Iio)
    have hz : (0:ℝ) ∈ O := hPatchH
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO 0 hz
    refine ⟨ε/2,half_pos hε,?_⟩
    exact hball (by rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hε)]; linarith)
  obtain ⟨commonH,hCommonH,hCommonHlt⟩ := hCommonHeight
  have hCommonPatchSegments (p : P) (h : ℝ) (hh : 0 < h) (hhH : h < commonH) :
      segment ℝ (Plane.mk (-patchδ p) h) (Plane.mk (patchδ p) h) ⊆ (patchF p).target :=
    hPatchSegments p h hh (hhH.trans (hCommonHlt p))
  choose patchLeft patchRight hPatchLeftFormula hPatchRightFormula hPatchEndsSource
    hPatchEndsCoords hPatchLeftBase hPatchRightBase using
      (fun p : P => hActualOffsetEndpointFamilies (patchF p) (patchδ p) commonH hCommonH
        (hPatchLeft0 p) (hPatchRight0 p) (hCommonPatchSegments p))
  have hCommonHeightAt (t : Interval) : 0 ≤ (commonH/2)*t.val ∧ (commonH/2)*t.val < commonH := by
    constructor
    · exact mul_nonneg (half_pos hCommonH).le t.property.1
    · nlinarith [t.property.2]
  have hActualCommonPatchAt (p : P) (t : Interval) (ht : 0 < t.val) :
      ∃ f : C(Interval,S), IsEmbedding f ∧ range f ⊆ (patchF p).source ∧
        f 0=patchLeft p t ∧ f 1=patchRight p t ∧
        (∀ x ∈ range f, 0 < commonE x 1) ∧
        Disjoint (range f) (M.cover.branch : Set S) ∧ Disjoint (range f) b.val.image ∧
        ∀ j, f 0 ∉ (old j).val.image ∧ f 1 ∉ (old j).val.image ∧
          (range f ∩ (old j).val.image).Finite ∧
          (range f ∩ (old j).val.image).ncard ≤ if p.val ∈ (old j).val.image then 1 else 0 := by
    have hh : 0 < (commonH/2)*t.val := mul_pos (half_pos hCommonH) ht
    obtain ⟨f,hfi,hfsub,hfr,hf0,hf1,hbank,hmarks,hb,hcounts⟩ :=
      hPatchFamily p ((commonH/2)*t.val) hh ((hCommonHeightAt t).2.trans (hCommonHlt p))
    refine ⟨f,hfi,hfsub,?_,?_,hbank,hmarks,hb,hcounts⟩
    · rw [hPatchLeftFormula p t]
      exact hf0
    · rw [hPatchRightFormula p t]
      exact hf1
  have hActualCommonPatchEndpoints (p : P) (t : Interval) (ht : 0 < t.val) :
      0 < commonE (patchLeft p t) 1 ∧ 0 < commonE (patchRight p t) 1 ∧
      (∀ j, patchLeft p t ∉ (old j).val.image ∧ patchRight p t ∉ (old j).val.image) := by
    obtain ⟨f,hfi,hfsub,hf0,hf1,hbank,hmarks,hb,hcounts⟩ := hActualCommonPatchAt p t ht
    refine ⟨?_,?_,?_⟩
    · rw [← hf0]
      exact hbank _ (Set.mem_range_self 0)
    · rw [← hf1]
      exact hbank _ (Set.mem_range_self 1)
    · intro j
      rw [← hf0,← hf1]
      exact ⟨(hcounts j).1,(hcounts j).2.1⟩
  have hActualOriginalDiskRetainedSupport :
      range B.disk ∩ KrawDerived=({B.firstCorner,B.secondCorner} : Set S) := by
    ext x
    constructor
    · rintro ⟨hxD,hxK⟩
      have hxa : x ∈ a.val.image := hdecompRawDerived.symm ▸ Or.inr hxK
      have hxs : x ∈ range B.firstSide := hDiskA ▸ ⟨hxD,hxa⟩
      exact hmeetRawDerived ▸ ⟨hxs,hxK⟩
    · intro hxc
      have hxs : x ∈ range B.firstSide ∩ KrawDerived := hmeetRawDerived.symm ▸ hxc
      refine ⟨?_,hxs.2⟩
      apply image_subset_range _ _
      exact B.boundary_eq.symm ▸ (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inl hxs.1)
  have hActualProducedDiskSupport
      (Q : C(Metric.closedBall (0:Plane) 1,S)) (hQ : range Q ⊆ range B.disk) :
      (∀ x ∈ range Q, x ∈ M.cover.branch → x ∈ ({B.firstCorner,B.secondCorner} : Set S)) ∧
      range Q ∩ KrawDerived ⊆ ({B.firstCorner,B.secondCorner} : Set S) := by
    constructor
    · intro x hx hm
      exact B.marks_are_corners x (hQ hx) hm
    · intro x hx
      exact hActualOriginalDiskRetainedSupport ▸ ⟨hQ hx.1,hx.2⟩
  have hActualSideIncidenceBudget (j : J) :
      (∑ p : P, if p.val ∈ (old j).val.image then 1 else 0)=
        (crossings M b (old j) ∩ range B.secondSide).ncard := by
    let Q : Set P := {p | p.val ∈ (old j).val.image}
    have hQI : Subtype.val '' Q=crossings M b (old j) ∩ range B.secondSide := by
      ext x
      constructor
      · rintro ⟨p,hp,rfl⟩
        obtain ⟨i,hi⟩ := hPold p.val p.property
        exact ⟨⟨hi.1.1,⟨hp,hi.1.1.2⟩⟩,hi.2⟩
      · intro hx
        have hp : x ∈ P := Set.mem_iUnion.mpr ⟨j,hx⟩
        exact ⟨⟨x,hp⟩,hx.1.2.1,rfl⟩
    have hcard : (∑ p : P, if p.val ∈ (old j).val.image then 1 else 0)=Q.ncard := by
      rw [← Set.fintypeCard_eq_ncard Q,Fintype.card_subtype]
      exact (Finset.card_filter (fun p : P => p.val ∈ (old j).val.image) Finset.univ).symm
    rw [hcard,← hQI]
    exact (Set.ncard_image_of_injective Q Subtype.val_injective).symm
  have hActualCommonPatchUnionBudget (t : Interval) (ht : 0 < t.val) :
      ∃ f : P → C(Interval,S),
        (∀ p, IsEmbedding (f p) ∧ range (f p) ⊆ (patchF p).source ∧
          (f p) 0=patchLeft p t ∧ (f p) 1=patchRight p t ∧
          (∀ x ∈ range (f p), 0 < commonE x 1) ∧
          Disjoint (range (f p)) (M.cover.branch : Set S) ∧ Disjoint (range (f p)) b.val.image) ∧
        (∀ p q, p ≠ q → Disjoint (range (f p)) (range (f q))) ∧
        ∀ j, (⋃ p, range (f p) ∩ (old j).val.image).Finite ∧
          (⋃ p, range (f p) ∩ (old j).val.image).ncard ≤
            (crossings M b (old j) ∩ range B.secondSide).ncard := by
    choose f hfembed hfsource hfleft hfright hfbank hfmarks hfb hfcount
      using (fun p : P => hActualCommonPatchAt p t ht)
    refine ⟨f,?_,?_,?_⟩
    · intro p
      exact ⟨hfembed p,hfsource p,hfleft p,hfright p,hfbank p,hfmarks p,hfb p⟩
    · intro p q hpq
      exact (hContactUDisjoint p q hpq).mono
        (fun x hx => (hPatchSource p (hfsource p hx)).1)
        (fun x hx => (hPatchSource q (hfsource q hx)).1)
    · intro j
      refine ⟨Set.finite_iUnion (fun p => (hfcount p j).2.2.1),?_⟩
      have hUnion := Finset.set_ncard_biUnion_le (Finset.univ : Finset P)
        (fun p => range (f p) ∩ (old j).val.image)
      have hUnion' : (⋃ p, range (f p) ∩ (old j).val.image).ncard ≤
          ∑ p : P, (range (f p) ∩ (old j).val.image).ncard := by simpa using hUnion
      calc
        _ ≤ ∑ p : P, (range (f p) ∩ (old j).val.image).ncard := hUnion'
        _ ≤ ∑ p : P, if p.val ∈ (old j).val.image then 1 else 0 :=
          Finset.sum_le_sum (fun p hp => (hfcount p j).2.2.2)
        _ = _ := hActualSideIncidenceBudget j
  have hActualCornerFamily (p : S)
      (hpc : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
      (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
      ∃ F : OpenPartialHomeomorph S Plane, ∃ L : C(Interval,S),
        p ∈ F.source ∧ F p=0 ∧ F.source ⊆ W ∧
        L 0 ∈ F.source ∧ L 0 ∈ range B.secondSide ∧ L 0 ∉ a.val.image ∧
        (∀ j, L 0 ∉ (old j).val.image) ∧
        ∀ t : Interval, 0 < t.val →
          ∃ f : C(Interval,S), IsEmbedding f ∧ f 0=p ∧ f 1=L t ∧
            range f ⊆ F.source ∧ range f \ {p} ⊆ B.openInterior ∧
            range f ∩ a.val.image={p} ∧ range f ∩ b.val.image={p} ∧
            (∀ x ∈ range f, x ∈ M.cover.branch → x=p) ∧
            ∀ j, Disjoint (range f) (arcInterior M (old j)) := by
    by_cases hpmark : p ∈ M.cover.branch
    · obtain ⟨terminal,r,hr,hrhalf,hend,hgerm⟩ :=
        hActualSelectedSideEndpointLabel p hpmark hpc
      obtain ⟨F,L,hpF,hFp,hFW,hmarks,hLsource,hLside,hLa,hLo,hpaths⟩ :=
        strengthened_actual_marked_disk_corner_endpoint_family M old a b
          (fun i j hij => (hOld i j hij).1) hab (fun j => (ha j).1)
          (fun j => (hb j).1) B hempty p hpmark hpc W hW hpW
          terminal hend r hr hrhalf hgerm
      refine ⟨F,L,hpF,hFp,hFW,hLsource,hLside,hLa,hLo,?_⟩
      intro t ht
      obtain ⟨f,hf,hf0,hf1,hfs,hfi,hfa,hfb,hfm,hfo⟩ := hpaths t ht
      refine ⟨f,hf,hf0,hf1,hfs,hfi,hfa,hfb,?_,hfo⟩
      intro x hx hm
      exact Set.mem_singleton_iff.mp (hfm ▸ (show x ∈ range f ∩ (M.cover.branch : Set S) from ⟨hx,hm⟩))
    · obtain ⟨F,L,hpF,hFp,hFW,hmarks,hLsource,hLside,hLa,hLo,hpaths⟩ :=
        strengthened_actual_unmarked_disk_corner_endpoint_family M old a b B hempty htab hcorners
          p hpmark hpc W hW hpW
      refine ⟨F,L,hpF,hFp,hFW,hLsource,hLside,hLa,hLo,?_⟩
      intro t ht
      obtain ⟨f,hf,hf0,hf1,hfs,hfi,hfa,hfb,hfm,hfo⟩ := hpaths t ht
      refine ⟨f,hf,hf0,hf1,hfs,hfi,hfa,hfb,?_,?_⟩
      · intro x hx hm
        exact False.elim (Set.disjoint_left.mp hfm hx hm)
      · intro j
        exact (hfo j).mono_right (fun x hx => hx.1)
  have hOriginalRemainderSupport :
      range B.disk ∩ Kraw=({B.firstCorner,B.secondCorner} : Set S) := by
    ext x
    constructor
    · rintro ⟨hxD,hxK⟩
      have hxa : x ∈ a.val.image := hdecompRaw.symm ▸ Or.inr hxK
      exact hmeetRaw ▸ (show x ∈ range B.firstSide ∩ Kraw from ⟨hDiskA ▸ ⟨hxD,hxa⟩,hxK⟩)
    · intro hxc
      have hxs : x ∈ range B.firstSide ∩ Kraw := hmeetRaw.symm ▸ hxc
      refine ⟨?_,hxs.2⟩
      exact image_subset_range _ _ (B.boundary_eq.symm ▸ (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inl hxs.1))
  let corner : Bool → S := fun i => if i then B.secondCorner else B.firstCorner
  let tail : Bool → Set Interval := fun i =>
    if i then {t | t.val ≤ 1-commonδ/2} else {t | commonδ/2 ≤ t.val}
  have hTailCompact (i : Bool) : IsCompact (tail i) := by
    dsimp [tail]
    split_ifs
    · exact (isClosed_le continuous_subtype_val continuous_const).isCompact
    · exact (isClosed_le continuous_const continuous_subtype_val).isCompact
  let cornerW : Bool → Set S := fun i => (B.secondSide '' tail i)ᶜ
  have hCornerWOpen (i : Bool) : IsOpen (cornerW i) :=
    ((hTailCompact i).image B.secondSide.continuous).isClosed.isOpen_compl
  have hCornerInW (i : Bool) : corner i ∈ cornerW i := by
    rintro ⟨t,ht,he⟩
    cases i
    · have ht0 := B.second_embedded.injective (he.trans B.second_zero.symm)
      subst t
      change commonδ/2 ≤ 0 at ht
      linarith
    · have ht1 := B.second_embedded.injective (he.trans B.second_one.symm)
      subst t
      change 1 ≤ 1-commonδ/2 at ht
      linarith
  have hCornerMember (i : Bool) : corner i ∈ ({B.firstCorner,B.secondCorner} : Set S) := by
    cases i <;> simp [corner]
  choose cornerF cornerL hCornerPoint hCornerCenter hCornerSource
    hCornerBaselineSource hCornerBaselineSide hCornerBaselineA hCornerBaselineOld hCornerPaths using
      fun i => hActualCornerFamily (corner i) (hCornerMember i)
        (cornerW i) (hCornerWOpen i) (hCornerInW i)
  choose cornerParam hCornerParam using hCornerBaselineSide
  have hCornerParamOrder :
      0 < (cornerParam false).val ∧ (cornerParam false).val < commonδ/2 ∧
      1-commonδ/2 < (cornerParam true).val ∧ (cornerParam true).val < 1 := by
    have h0W : cornerL false 0 ∈ cornerW false :=
      hCornerSource false (hCornerBaselineSource false)
    have h1W : cornerL true 0 ∈ cornerW true :=
      hCornerSource true (hCornerBaselineSource true)
    have hl : (cornerParam false).val < commonδ/2 := by
      by_contra hn
      exact h0W ⟨cornerParam false,le_of_not_gt hn,hCornerParam false⟩
    have hr : 1-commonδ/2 < (cornerParam true).val := by
      by_contra hn
      exact h1W ⟨cornerParam true,le_of_not_gt hn,hCornerParam true⟩
    have hl0 : 0 < (cornerParam false).val := by
      by_contra hn
      have hz : cornerParam false=0 := Subtype.ext (le_antisymm (le_of_not_gt hn) (cornerParam false).property.1)
      have he : cornerL false 0=B.firstCorner := by rw [← hCornerParam false,hz,B.second_zero]
      exact hCornerBaselineA false (he.symm ▸ B.first_on_curve (B.first_zero ▸ Set.mem_range_self 0))
    have hr1 : (cornerParam true).val < 1 := by
      by_contra hn
      have hz : cornerParam true=1 := Subtype.ext (le_antisymm (cornerParam true).property.2 (le_of_not_gt hn))
      have he : cornerL true 0=B.secondCorner := by rw [← hCornerParam true,hz,B.second_one]
      exact hCornerBaselineA true (he.symm ▸ B.first_on_curve (B.first_one ▸ Set.mem_range_self 1))
    exact ⟨hl0,hl,hr,hr1⟩
  let α : ℝ := (cornerParam false).val/2
  let β : ℝ := (1+(cornerParam true).val)/2
  have hα : 0 < α := half_pos hCornerParamOrder.1
  have hβ : β < 1 := by dsimp [β]; linarith [hCornerParamOrder.2.2.2]
  have hαβ : α < β := by
    dsimp [α,β]
    linarith [hCornerParamOrder.2.1,hCornerParamOrder.2.2.1,hCommonδhalf]
  let core : C(Interval,S) := ⟨fun t => ψ (α+t.val*(β-α)), hψ.comp (by fun_prop)⟩
  have hCoreθ (t : Interval) : α ≤ α+t.val*(β-α) ∧ α+t.val*(β-α) ≤ β := by
    constructor <;> nlinarith [t.property.1,t.property.2]
  have hCoreθ01 (t : Interval) : 0 < α+t.val*(β-α) ∧ α+t.val*(β-α) < 1 :=
    ⟨hα.trans_le (hCoreθ t).1,(hCoreθ t).2.trans_lt hβ⟩
  have hψInjective (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
      (he : ψ u=ψ v) : u=v := by
    have hh := congrArg Subtype.val (B.second_embedded.injective he)
    simpa only [Set.projIcc_of_mem zero_le_one hu,Set.projIcc_of_mem zero_le_one hv] using hh
  have hCoreEmbed : IsEmbedding core := by
    apply (core.continuous.isClosedEmbedding ?_).isEmbedding
    intro t u he
    have hh := hψInjective _ _ ⟨(hCoreθ01 t).1.le,(hCoreθ01 t).2.le⟩
      ⟨(hCoreθ01 u).1.le,(hCoreθ01 u).2.le⟩ he
    apply Subtype.ext
    nlinarith [sub_pos.mpr hαβ]
  have hCoreNoCorner (t : Interval) :
      core t ∉ ({B.firstCorner,B.secondCorner} : Set S) := by
    rintro (he|he)
    · have hh := congrArg Subtype.val (B.second_embedded.injective (he.trans B.second_zero.symm))
      rw [Set.projIcc_of_mem zero_le_one ⟨(hCoreθ01 t).1.le,(hCoreθ01 t).2.le⟩] at hh
      change α+t.val*(β-α)=0 at hh
      linarith [(hCoreθ01 t).1]
    · have hh := congrArg Subtype.val (B.second_embedded.injective (he.trans B.second_one.symm))
      rw [Set.projIcc_of_mem zero_le_one ⟨(hCoreθ01 t).1.le,(hCoreθ01 t).2.le⟩] at hh
      change α+t.val*(β-α)=1 at hh
      linarith [(hCoreθ01 t).2]
  have hCoreSide (t : Interval) : core t ∈ range B.secondSide := Set.mem_range_self _
  have hCoreInterior : range core ⊆ arcInterior M b := by
    rintro x ⟨t,rfl⟩
    refine ⟨B.second_on_curve (hCoreSide t),?_⟩
    intro hm
    have hD : core t ∈ range B.disk := image_subset_range _ _
      (B.boundary_eq.symm ▸ (show core t ∈ range B.firstSide ∪ range B.secondSide from Or.inr (hCoreSide t)))
    exact hCoreNoCorner t (B.marks_are_corners _ hD hm)
  obtain ⟨globalF0,χ,hχ,hCoreSource,hGlobalMarks,hGlobalAxis,hCoreCoords⟩ :=
    actual_compact_mark_free_increasing_axis_chart M b core hCoreEmbed hCoreInterior
  have hCoreRange : range core=ψ '' Set.Icc α β := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨α+t.val*(β-α),hCoreθ t,rfl⟩
    · rintro ⟨θ,hθ,rfl⟩
      let t : Interval := ⟨(θ-α)/(β-α),div_nonneg (sub_nonneg.mpr hθ.1) (sub_pos.mpr hαβ).le,
        (div_le_one (sub_pos.mpr hαβ)).mpr (by linarith [hθ.2])⟩
      refine ⟨t,?_⟩
      change ψ (α+((θ-α)/(β-α))*(β-α))=ψ θ
      congr 1
      rw [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hαβ))]
      ring
  have hCornerBaselineInCore (i : Bool) : cornerL i 0 ∈ range core := by
    rw [hCoreRange]
    refine ⟨(cornerParam i).val,?_,?_⟩
    · cases i
      · dsimp [α,β]
        constructor <;> linarith [hCornerParamOrder.1,hCornerParamOrder.2.1,hCornerParamOrder.2.2.1,hCommonδhalf]
      · dsimp [α,β]
        constructor <;> linarith [hCornerParamOrder.1,hCornerParamOrder.2.1,hCornerParamOrder.2.2.1,hCornerParamOrder.2.2.2,hCommonδhalf]
    · change B.secondSide (Set.projIcc 0 1 zero_le_one (cornerParam i).val)=cornerL i 0
      rw [Set.projIcc_of_mem zero_le_one (cornerParam i).property]
      exact hCornerParam i
  have hContactsInGlobalCore : P ⊆ range core := by
    intro p hp
    obtain ⟨j,hj⟩ := hPold p hp
    obtain ⟨t,ht⟩ := hj.2
    have htT : t ∈ T := by
      change B.secondSide t ∈ P
      exact ht.symm ▸ hp
    rw [hCoreRange]
    refine ⟨t.val,?_,?_⟩
    · dsimp [α,β]
      have hbds := hCommonContactCore t htT
      constructor <;> linarith [hbds.1,hbds.2,hCornerParamOrder.2.1,hCornerParamOrder.2.2.1]
    · change B.secondSide (Set.projIcc 0 1 zero_le_one t.val)=p
      rw [Set.projIcc_of_mem zero_le_one t.property]
      exact ht
  have hCoreAvoid (t : Interval) : core t ∉ a.val.image ∧ core t ∉ Kother := by
    constructor
    · intro ha
      exact hCoreNoCorner t (hsecondclean ▸ (show core t ∈ range B.secondSide ∩ a.val.image from ⟨hCoreSide t,ha⟩))
    · intro hk
      exact hCoreNoCorner t (hOtherMeet ▸ (show core t ∈ range B.secondSide ∩ Kother from ⟨hCoreSide t,hk⟩))
  let globalW : Set S := (a.val.image ∪ Kother)ᶜ
  have hGlobalWOpen : IsOpen globalW :=
    ((isCompact_range a.val.continuous).union hKother).isClosed.isOpen_compl
  let globalF1 := globalF0.restrOpen globalW hGlobalWOpen
  have hGlobalF1Source : globalF1.source=globalF0.source ∩ globalW := by simp [globalF1]
  have hGlobalF1Value (x : S) : globalF1 x=globalF0 x := rfl
  have hCoreF1Source : range core ⊆ globalF1.source := by
    rintro x ⟨t,rfl⟩
    rw [hGlobalF1Source]
    exact ⟨hCoreSource (Set.mem_range_self t),fun hh => hh.elim (hCoreAvoid t).1 (hCoreAvoid t).2⟩
  have hF1Axis (x : S) (hx : x ∈ globalF1.source) :
      x ∈ b.val.image ↔ globalF1 x 1=0 := hGlobalAxis x (hGlobalF1Source ▸ hx).1
  have hF1FirstFree : Disjoint globalF1.source (range B.firstSide) := by
    apply Set.disjoint_left.mpr
    intro x hx hf
    exact (hGlobalF1Source ▸ hx).2 (Or.inl (B.first_on_curve hf))
  have hF1SideLocal (x : S) (hx : x ∈ globalF1.source) :
      x ∈ b.val.image ↔ x ∈ range B.secondSide := by
    have hxK : x ∉ Kother := fun hk => (hGlobalF1Source ▸ hx).2 (Or.inr hk)
    rw [hOtherDecomp]
    simp only [Set.mem_union,hxK,or_false]
  have hGlobalWholeAxis : ∀ x ∈ Set.Icc (χ 0) (χ 1),
      ∃ y : S, y ∈ globalF1.source ∧ globalF1 y=Plane.mk x 0 ∧ y ∉ a.val.image := by
    intro x hx
    have hinterval : χ '' Set.Icc (0:Interval) 1=Set.Icc (χ 0) (χ 1) :=
      χ.continuous.image_Icc_of_strictMono hχ
    obtain ⟨t,ht,hxt⟩ := hinterval.symm ▸ hx
    refine ⟨core t,hCoreF1Source (Set.mem_range_self t),?_,(hCoreAvoid t).1⟩
    rw [hGlobalF1Value,hCoreCoords,hxt]
  have hGlobalStripExists : ∃ ε : ℝ, 0 < ε ∧ ∀ z : Plane,
      z 0 ∈ Icc (χ 0) (χ 1) → |z 1| < ε → z ∈ globalF1.target := by
    let xy : Plane ≃ₜ ℝ × ℝ := {
      toFun := fun z => (z 0,z 1)
      invFun := fun z => Plane.mk z.1 z.2
      left_inv := by intro z; ext i; fin_cases i <;> rfl
      right_inv := by intro z; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let O := xy '' globalF1.target
    have hO : IsOpen O := xy.isOpenMap _ globalF1.open_target
    let K : Set (ℝ × ℝ) := (fun x : ℝ => (x,0)) '' Icc (χ 0) (χ 1)
    have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
    have hKO : K ⊆ O := by
      rintro z ⟨x,hx,rfl⟩
      obtain ⟨y,hyE,hEy,hAvoid⟩ := hGlobalWholeAxis x hx
      refine ⟨globalF1 y,globalF1.map_source hyE,?_⟩
      rw [hEy]
      rfl
    obtain ⟨ε,hε,hclear⟩ := hK.exists_thickening_subset_open hO hKO
    refine ⟨ε,hε,?_⟩
    intro z hz hy
    have hxy : xy z ∈ O := by
      apply hclear
      apply Metric.mem_thickening_iff.mpr
      refine ⟨(z 0,0),⟨z 0,hz,rfl⟩,?_⟩
      change dist (z 0,z 1) (z 0,0) < ε
      simpa [Prod.dist_eq,Real.dist_eq] using hy
    obtain ⟨v,hv,hve⟩ := hxy
    exact xy.injective hve ▸ hv
  obtain ⟨globalε,hGlobalε,hGlobalStrip⟩ := hGlobalStripExists
  have hχ01 : χ 0 < χ 1 := hχ (by norm_num)
  obtain ⟨globalE,hGlobalESource,hGlobalEX,hGlobalEY,hGlobalEAxis,hGlobalInsideBank⟩ :=
    actual_marked_two_side_disk_interior_bank M a b B globalF1 (χ 0) (χ 1) globalε hχ01 hGlobalε
      (fun z hz => hGlobalStrip z ⟨hz.1.le,hz.2.1.le⟩ (abs_lt.mpr ⟨hz.2.2.1,hz.2.2.2⟩))
      hF1FirstFree hF1SideLocal hF1Axis
  let bankO : Set S := {x | χ 0 < globalF1 x 0 ∧ globalF1 x 0 < χ 1 ∧
    -globalε < globalF1 x 1 ∧ globalF1 x 1 < globalε}
  have hBankOOpen : IsOpen (globalE.source ∩ bankO) := by
    rw [hGlobalESource]
    let O : Set Plane := {z | χ 0 < z 0 ∧ z 0 < χ 1 ∧ -globalε < z 1 ∧ z 1 < globalε}
    have hO : IsOpen O := by
      change IsOpen ({z : Plane | χ 0 < z 0} ∩
        ({z : Plane | z 0 < χ 1} ∩ ({z : Plane | -globalε < z 1} ∩ {z : Plane | z 1 < globalε})))
      exact (isOpen_lt continuous_const (by fun_prop)).inter
        ((isOpen_lt (by fun_prop) continuous_const).inter
          ((isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const)))
    exact globalF1.continuousOn.isOpen_inter_preimage globalF1.open_source hO
  have hRealBank (x : S) (hx : x ∈ globalE.source ∩ bankO) :
      x ∈ B.openInterior ↔ 0 < globalE x 1 :=
    hGlobalInsideBank x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2
  have hRetainedBankedActualFanPatch {I D : Type} [Fintype I] [Fintype D]
      (c : I → EssentialMarkedArc M) (p : S)
      (E0 : OpenPartialHomeomorph S Plane) (hpE : p ∈ E0.source) (hE0 : E0 p=0)
      (hmarks : Disjoint E0.source (M.cover.branch : Set S))
      (γ : I × Bool → Interval → Plane)
      (R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E0 '' E0.source))
      (i0 : I) (hop : R.vector (i0,true) = -R.vector (i0,false))
      (hcore : ∀ i x, x ∈ E0.source → ‖R.H (E0 x)‖ ≤ R.coreRadius →
        (x ∈ (c i).val.image ↔ R.H (E0 x) ∈
          segment ℝ (0:Plane) (R.vector (i,false)) ∪
          segment ℝ (0:Plane) (R.vector (i,true))))
      (label : D → I)
      (hcross : ∀ j, CrossesInDisk M (c i0) (c (label j)) p)
      (hmeet : ∀ j x, x ∈ E0.source → x ∈ (c i0).val.image ∩ (c (label j)).val.image → x=p)
      (E : OpenPartialHomeomorph S Plane) (hE0E : E0.source ⊆ E.source)
      (hEp : E p 1=0) (hEaxis : ∀ x ∈ E.source, x ∈ (c i0).val.image ↔ E x 1=0) :
      ∃ F : OpenPartialHomeomorph S Plane, ∃ δ H : ℝ,
        p ∈ F.source ∧ F p=0 ∧
        (∀ x ∈ F.source, x ∈ (c i0).val.image ↔ F x 1=0) ∧
        (∃ v w : D → Plane, (∀ j, 0 < v j 1) ∧ (∀ j, w j 1 < 0) ∧
          ∀ j x, x ∈ F.source →
            (x ∈ (c (label j)).val.image ↔ F x ∈ segment ℝ (0:Plane) (v j) ∪ segment ℝ (0:Plane) (w j))) ∧
        F.source ⊆ E0.source ∧ 0 < δ ∧ 0 < H ∧
        Plane.mk (-δ) 0 ∈ F.target ∧ Plane.mk δ 0 ∈ F.target ∧
        (∀ u ∈ Icc (-δ) δ, Plane.mk u 0 ∈ F.target) ∧
        (∀ h : ℝ, 0 < h → h < H → segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ F.target) ∧
        ∀ h : ℝ, 0 < h → h < H → ∃ f : C(Interval,S),
          IsEmbedding f ∧ range f ⊆ F.source ∧
          range f=F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          f 0=F.symm (Plane.mk (-δ) h) ∧ f 1=F.symm (Plane.mk δ h) ∧
          (∀ x ∈ range f, 0 < E x 1) ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧ Disjoint (range f) (c i0).val.image ∧
          ∀ j, f 0 ∉ (c (label j)).val.image ∧ f 1 ∉ (c (label j)).val.image ∧
            (range f ∩ (c (label j)).val.image).Finite ∧ (range f ∩ (c (label j)).val.image).ncard ≤ 1 := by
    obtain ⟨T,F0,ρ,hs,hFp,hρ,hρ1,hFformula,hTv,hCoreNorm,hAxis,hModel⟩ :=
      hMarkedNormalizeRadialCore c p E0 hpE hE0 γ R i0 hop false hcore
    have hSign (j : D) : (T (R.vector (label j,false))) 1 * (T (R.vector (label j,true))) 1 < 0 :=
      hMarkedCrossingSigns (c i0) (c (label j)) p (hcross j) F0 (hs.symm ▸ hpE) hFp ρ hρ
        (T (R.vector (label j,false))) (T (R.vector (label j,true))) hAxis
        (fun x hx => hmeet j x (hs ▸ hx))
        (fun x hx hn hd => (hModel (label j) x hx hn).mp hd)
    let a : D → Plane := fun j => if 0 < (T (R.vector (label j,false))) 1
      then T (R.vector (label j,false)) else T (R.vector (label j,true))
    let b : D → Plane := fun j => if 0 < (T (R.vector (label j,false))) 1
      then T (R.vector (label j,true)) else T (R.vector (label j,false))
    have ha (j : D) : 0 < a j 1 := by
      dsimp [a]
      split_ifs with hh
      · exact hh
      · nlinarith [hSign j]
    have hb (j : D) : b j 1 < 0 := by
      dsimp [b]
      split_ifs with hh
      · nlinarith [hSign j]
      · have hne : (T (R.vector (label j,false))) 1 ≠ 0 := by
          intro he
          have hh := hSign j
          rw [he,zero_mul] at hh
          exact (lt_irrefl 0) hh
        exact lt_of_le_of_ne (le_of_not_gt hh) hne
    have hF0E : F0.source ⊆ E.source := fun x hx => hE0E (hs ▸ hx)
    have hF0mark : Disjoint F0.source (M.cover.branch : Set S) := hs.symm ▸ hmarks
    have hz : (0:Plane) ∈ F0.target ∩ Metric.ball (0:Plane) ρ := by
      refine ⟨?_,by simpa using hρ⟩
      have hh := F0.map_source (hs.symm ▸ hpE)
      rwa [hFp] at hh
    obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp (F0.open_target.inter isOpen_ball) 0 hz
    have hmodelAB (j : D) (x : S) (hx : x ∈ F0.source) (hn : ‖F0 x‖ < ρ) :
        x ∈ (c (label j)).val.image ↔ F0 x ∈ segment ℝ (0:Plane) (a j) ∪ segment ℝ (0:Plane) (b j) := by
      dsimp [a,b]
      split_ifs
      · exact hModel (label j) x hx hn
      · rw [Set.union_comm]
        exact hModel (label j) x hx hn
    obtain ⟨F,δ,H,hpF,hFpF,hAxisF,hModelF,hFF0,hδ,hH,hleft0,hright0,hAxisTarget,hsegments,hpatch⟩ :=
      CurveComplex.HyperellipticModel.hMarkedCommonBankUniformPatch M (c i0) (fun j => c (label j)) p E F0 hF0E
        (hs.symm ▸ hpE) hFp hEp hF0mark ρ η hρ hη hball hEaxis hAxis a b ha hb hmodelAB
    exact ⟨F,δ,H,hpF,hFpF,hAxisF,hModelF,fun x hx => hs ▸ hFF0 hx,hδ,hH,hleft0,hright0,hAxisTarget,hsegments,hpatch⟩
  have hRetainedBankedSourceContactPatch
      (E : OpenPartialHomeomorph S Plane)
      (hEaxis : ∀ x ∈ E.source, x ∈ b.val.image ↔ E x 1=0) (p : P)
      (hpCommon : p.val ∈ E.source) :
      ∃ F : OpenPartialHomeomorph S Plane, ∃ δ H : ℝ,
        p.val ∈ F.source ∧ F p.val=0 ∧
        (∀ x ∈ F.source, x ∈ b.val.image ↔ F x 1=0) ∧
        (∃ v w : {j : J // p.val ∈ (old j).val.image} → Plane,
          (∀ j, 0 < v j 1) ∧ (∀ j, w j 1 < 0) ∧
          ∀ j x, x ∈ F.source →
            (x ∈ (old j.val).val.image ↔ F x ∈ segment ℝ (0:Plane) (v j) ∪ segment ℝ (0:Plane) (w j))) ∧
        F.source ⊆ contactU p ∩ E.source ∧ 0 < δ ∧ 0 < H ∧
        Plane.mk (-δ) 0 ∈ F.target ∧ Plane.mk δ 0 ∈ F.target ∧
        (∀ u ∈ Icc (-δ) δ, Plane.mk u 0 ∈ F.target) ∧
        (∀ h : ℝ, 0 < h → h < H → segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ F.target) ∧
        ∀ h : ℝ, 0 < h → h < H → ∃ f : C(Interval,S),
          IsEmbedding f ∧ range f ⊆ F.source ∧
          range f=F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          f 0=F.symm (Plane.mk (-δ) h) ∧ f 1=F.symm (Plane.mk δ h) ∧
          (∀ x ∈ range f, 0 < E x 1) ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧ Disjoint (range f) b.val.image ∧
          ∀ j, f 0 ∉ (old j).val.image ∧ f 1 ∉ (old j).val.image ∧
            (range f ∩ (old j).val.image).Finite ∧
            (range f ∩ (old j).val.image).ncard ≤ if p.val ∈ (old j).val.image then 1 else 0 := by
    let I := {i : Option J // p.val ∈ (r i).val.image}
    let c : I → EssentialMarkedArc M := fun i => r i.val
    let D := {j : J // p.val ∈ (old j).val.image}
    obtain ⟨E0,hpE,hEU,hEmark,hE0,g,R,i0,hi0,hRop,hmodel⟩ :=
      hActualSourceContactRadialCore p E.source E.open_source hpCommon
    have hselected : c i0=araw := by
      change r i0.val=araw
      rw [hi0]
      rfl
    have hlocalEq (x : S) (hx : x ∈ contactU p) : x ∈ araw.val.image ↔ x ∈ b.val.image := by
      have hnot : x ∉ KrawDerived ∪ Kother := fun hk => Set.disjoint_left.mp (hContactURemainders p) hx hk
      rw [himageRaw,hOtherDecomp]
      constructor
      · intro hh
        exact Or.inl (hh.resolve_right (fun hk => hnot (Or.inl hk)))
      · intro hh
        exact Or.inl (hh.resolve_right (fun hk => hnot (Or.inr hk)))
    let E' := E.restrOpen (contactU p) (hContactUOpen p)
    have hE's : E'.source=E.source ∩ contactU p := rfl
    have hE0E' : E0.source ⊆ E'.source := fun x hx => ⟨(hEU hx).2,(hEU hx).1⟩
    have hpB : p.val ∈ b.val.image := by
      obtain ⟨j,hj⟩ := hPold p.val p.property
      exact B.second_on_curve hj.2
    have hE'p : E' p.val 1=0 := (hEaxis _ hpCommon).mp hpB
    have hE'axis (x : S) (hx : x ∈ E'.source) : x ∈ (c i0).val.image ↔ E' x 1=0 := by
      rw [hselected,hlocalEq x hx.2]
      exact hEaxis x hx.1
    let label : D → I := fun j => ⟨some j.val,j.property⟩
    have hcross (j : D) : CrossesInDisk M (c i0) (c (label j)) p.val := by
      rw [hselected]
      have hpfree : p.val ∉ M.cover.branch := fun hm => Set.disjoint_left.mp hEmark hpE hm
      have hpraw : p.val ∈ araw.val.image := hselected ▸ i0.property
      exact hRawAllOldTransverse j.val p.val ⟨⟨hpraw,hpfree⟩,j.property,hpfree⟩
    have hmeet (j : D) (x : S) (hx : x ∈ E0.source)
        (hc : x ∈ (c i0).val.image ∩ (c (label j)).val.image) : x=p.val := by
      rw [hselected] at hc
      exact hContactUMeet p none (some j.val) (by simp) ⟨(hEU hx).1,hc⟩
    obtain ⟨F,δ,H,hpF,hFpF,hAxisF,hModelF,hFE,hδ,hH,hleft0,hright0,hAxisTarget,hsegments,hpatch⟩ :=
      hRetainedBankedActualFanPatch c p.val E0 hpE hE0 hEmark (fun j => E0 ∘ g j)
        R i0 hRop hmodel label hcross hmeet E' hE0E' hE'p hE'axis
    have hFU : F.source ⊆ contactU p ∩ E.source := hFE.trans hEU
    refine ⟨F,δ,H,hpF,hFpF,?_,hModelF,hFU,hδ,hH,hleft0,hright0,hAxisTarget,hsegments,?_⟩
    · intro x hx
      rw [← hlocalEq x (hFU hx).1,← hselected]
      exact hAxisF x hx
    
    · intro h hh hhH
      obtain ⟨f,hfi,hfF,hfr,hf0,hf1,hbank,hfmark,hfoff,hcounts⟩ := hpatch h hh hhH
      have hfU : range f ⊆ contactU p := fun x hx => (hFU (hfF hx)).1
      have hfb : Disjoint (range f) b.val.image := by
        apply Set.disjoint_left.mpr
        intro x hx hxb
        have hxa : x ∈ (c i0).val.image := by
          rw [hselected]
          exact (hlocalEq x (hfU hx)).mpr hxb
        exact Set.disjoint_left.mp hfoff hx hxa
      refine ⟨f,hfi,hfF,hfr,hf0,hf1,hbank,hfmark,hfb,?_⟩
      intro j
      by_cases hj : p.val ∈ (old j).val.image
      · rw [if_pos hj]
        exact hcounts ⟨j,hj⟩
      · rw [if_neg hj]
        have hd : Disjoint (range f) (old j).val.image :=
          (hContactUNonincident p j hj).mono_left hfU
        have he : range f ∩ (old j).val.image=∅ := Set.disjoint_iff_inter_eq_empty.mp hd
        refine ⟨(fun hx => Set.disjoint_left.mp hd (Set.mem_range_self 0) hx),
          (fun hx => Set.disjoint_left.mp hd (Set.mem_range_self 1) hx),?_,?_⟩
        · rw [he]; exact Set.finite_empty
        · rw [he,Set.ncard_empty]
  let Ebank := globalE.restrOpen (globalE.source ∩ bankO) hBankOOpen
  have hEbankSource : Ebank.source=globalE.source ∩ bankO := by
    ext x
    simp [Ebank,OpenPartialHomeomorph.restrOpen_source,Set.inter_assoc]
  have hEbankValue (x : S) : Ebank x=globalE x := rfl
  have hEbankAxis (x : S) (hx : x ∈ Ebank.source) : x ∈ b.val.image ↔ Ebank x 1=0 :=
    hGlobalEAxis x ((hEbankSource ▸ hx).1)
  have hEbankInside (x : S) (hx : x ∈ Ebank.source) :
      x ∈ B.openInterior ↔ 0 < Ebank x 1 := hRealBank x (hEbankSource ▸ hx)
  have hGlobalParameterBank (θ : ℝ) (hθα : α < θ) (hθβ : θ < β) : ψ θ ∈ Ebank.source := by
    let t : Interval := ⟨(θ-α)/(β-α),
      (div_pos (sub_pos.mpr hθα) (sub_pos.mpr hαβ)).le,
      ((div_lt_one (sub_pos.mpr hαβ)).mpr (by linarith)).le⟩
    have ht0 : (0:Interval) < t := by
      change 0 < (θ-α)/(β-α)
      exact div_pos (sub_pos.mpr hθα) (sub_pos.mpr hαβ)
    have ht1 : t < (1:Interval) := by
      change (θ-α)/(β-α) < 1
      exact (div_lt_one (sub_pos.mpr hαβ)).mpr (by linarith)
    have hct : core t=ψ θ := by
      change ψ (α+((θ-α)/(β-α))*(β-α))=ψ θ
      congr 1
      rw [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hαβ))]
      ring
    rw [hEbankSource,← hct]
    have hsource : core t ∈ globalE.source := hGlobalESource.symm ▸ hCoreF1Source (Set.mem_range_self t)
    refine ⟨hsource,?_⟩
    change χ 0 < globalF1 (core t) 0 ∧ globalF1 (core t) 0 < χ 1 ∧
      -globalε < globalF1 (core t) 1 ∧ globalF1 (core t) 1 < globalε
    rw [hGlobalF1Value,hCoreCoords]
    exact ⟨hχ ht0,hχ ht1,by change -globalε<0; linarith,by change 0<globalε; exact hGlobalε⟩
  have hCornerBaselineBank (i : Bool) : cornerL i 0 ∈ Ebank.source := by
    have hθ : α < (cornerParam i).val ∧ (cornerParam i).val < β := by
      cases i
      · dsimp [α,β]
        constructor <;> linarith [hCornerParamOrder.1,hCornerParamOrder.2.1,hCornerParamOrder.2.2.1,hCommonδhalf]
      · dsimp [α,β]
        constructor <;> linarith [hCornerParamOrder.1,hCornerParamOrder.2.1,hCornerParamOrder.2.2.1,hCornerParamOrder.2.2.2,hCommonδhalf]
    have hψbase : ψ (cornerParam i).val=cornerL i 0 := by
      change B.secondSide (Set.projIcc 0 1 zero_le_one (cornerParam i).val)=cornerL i 0
      rw [Set.projIcc_of_mem zero_le_one (cornerParam i).property]
      exact hCornerParam i
    exact hψbase ▸ hGlobalParameterBank _ hθ.1 hθ.2
  have hContactBank (p : P) : p.val ∈ Ebank.source := by
    have hbds := hCommonContactCore (contactParam p).val (contactParam p).property
    have hθ : α < (contactParam p).val.val ∧ (contactParam p).val.val < β := by
      dsimp [α,β]
      constructor <;> linarith [hbds.1,hbds.2,hCornerParamOrder.2.1,hCornerParamOrder.2.2.1]
    exact hContactParamΨ p ▸ hGlobalParameterBank _ hθ.1 hθ.2
  let middleTail : Set S := ψ '' Icc (0:ℝ) (commonδ/2) ∪ ψ '' Icc (1-commonδ/2) 1
  have hMiddleTailCompact : IsCompact middleTail :=
    (isCompact_Icc.image hψ).union (isCompact_Icc.image hψ)
  let middleContactV : P → Set S := fun p => contactCoreV p ∩ middleTailᶜ
  have hMiddleContactOpen (p : P) : IsOpen (middleContactV p) :=
    (hContactCoreVOpen p).inter hMiddleTailCompact.isClosed.isOpen_compl
  have hMiddleContactPoint (p : P) : p.val ∈ middleContactV p := by
    refine ⟨hContactCoreVPoint p,?_⟩
    have hbds := hCommonContactCore (contactParam p).val (contactParam p).property
    rintro (⟨θ,hθ,he⟩|⟨θ,hθ,he⟩)
    · have hh := hψInjective θ (contactParam p).val.val
        ⟨hθ.1,by linarith [hθ.2,hCommonδhalf]⟩ (contactParam p).val.property
        (he.trans (hContactParamΨ p).symm)
      linarith [hθ.2]
    · have hh := hψInjective θ (contactParam p).val.val
        ⟨by linarith [hθ.1,hCommonδhalf],hθ.2⟩ (contactParam p).val.property
        (he.trans (hContactParamΨ p).symm)
      linarith [hθ.1]
  choose bankPatchF bankPatchδ bankPatchH hBankPatchPoint hBankPatchCenter hBankPatchAxis
    hBankPatchModel hBankPatchSource hBankPatchδ hBankPatchH hBankPatchLeft0 hBankPatchRight0
    hBankPatchWholeAxis hBankPatchSegments hBankPatchFamily using
      fun p : P => hRetainedBankedSourceContactPatch
        (Ebank.restrOpen (middleContactV p) (hMiddleContactOpen p))
        (fun x hx => hEbankAxis x hx.1) p ⟨hContactBank p,hMiddleContactPoint p⟩
  have hBankPatchInside (p : P) (h : ℝ) (hh : 0 < h) (hhH : h < bankPatchH p) :
      ∃ f : C(Interval,S), IsEmbedding f ∧ range f ⊆ (bankPatchF p).source ∧
        range f=(bankPatchF p).symm '' segment ℝ (Plane.mk (-bankPatchδ p) h) (Plane.mk (bankPatchδ p) h) ∧
        f 0=(bankPatchF p).symm (Plane.mk (-bankPatchδ p) h) ∧
        f 1=(bankPatchF p).symm (Plane.mk (bankPatchδ p) h) ∧
        range f ⊆ B.openInterior ∧
        Disjoint (range f) (M.cover.branch : Set S) ∧ Disjoint (range f) b.val.image ∧
        ∀ j, f 0 ∉ (old j).val.image ∧ f 1 ∉ (old j).val.image ∧
          (range f ∩ (old j).val.image).Finite ∧
          (range f ∩ (old j).val.image).ncard ≤ if p.val ∈ (old j).val.image then 1 else 0 := by
    obtain ⟨f,hf,hfs,hfr,hf0,hf1,hbank,hmarks,hbfree,hcounts⟩ := hBankPatchFamily p h hh hhH
    refine ⟨f,hf,hfs,hfr,hf0,hf1,?_,hmarks,hbfree,hcounts⟩
    intro x hx
    exact (hEbankInside x (hBankPatchSource p (hfs hx)).2.1).mpr (hbank x hx)
  have hCornerFamiliesInside (i : Bool) :
      ∀ t : Interval, 0 < t.val → cornerL i t ∈ B.openInterior := by
    apply CurveComplex.actual_corner_endpoint_family_attaches_inside (corner i) B.openInterior (cornerL i)
    intro t ht
    obtain ⟨f,hf,hf0,hf1,hfs,hfi,hfa,hfb,hfm,hfo⟩ := hCornerPaths i t ht
    exact ⟨f,hf,hf0,hf1,hfi⟩
  obtain ⟨cornerη,hCornerη,hCornerη1,bankCornerL,hBankCornerFormula,hBankCornerBaseline,hBankCornerPositive⟩ :=
    CurveComplex.actual_finite_endpoint_families_common_bank Ebank B.openInterior cornerL
      (fun _ => Set.univ) (fun _ => isOpen_univ)
      (fun i => ⟨hCornerBaselineBank i,Set.mem_univ _⟩)
      hCornerFamiliesInside (fun i x hx => hEbankInside x hx.1)
  have hBankPatchSideAxis (p : P) (u : ℝ) (hu : u ∈ Icc (-bankPatchδ p) (bankPatchδ p)) :
      (bankPatchF p).symm (Plane.mk u 0) ∈ range B.secondSide := by
    have hz := hBankPatchWholeAxis p u hu
    have hs := (bankPatchF p).map_target hz
    have hbaxis : (bankPatchF p) ((bankPatchF p).symm (Plane.mk u 0)) 1=0 := by
      rw [(bankPatchF p).right_inv hz]
      rfl
    have hbtrace := (hBankPatchAxis p ((bankPatchF p).symm (Plane.mk u 0)) hs).mpr hbaxis
    have hsource := (hBankPatchSource p hs).2.1
    have hGlobalSource : (bankPatchF p).symm (Plane.mk u 0) ∈ globalF1.source :=
      hGlobalESource ▸ (hEbankSource ▸ hsource).1
    exact (hF1SideLocal ((bankPatchF p).symm (Plane.mk u 0)) hGlobalSource).mp hbtrace
  have hBankPatchSourceParameter (p : P) (u : Interval)
      (hu : B.secondSide u ∈ (bankPatchF p).source) :
      coreLeft (contactParam p) < u.val ∧ u.val < coreRight (contactParam p) := by
    apply hContactCoreVParameters p u.val u.property
    have hψu : ψ u.val=B.secondSide u := by
      dsimp [ψ,Function.comp_def]
      rw [Set.projIcc_of_mem zero_le_one u.property]
    exact hψu.symm ▸ (hBankPatchSource p hu).2.2.1
  have hOrderedBankPatchBaselines (p : P) :
      ∃ u v : Interval, coreLeft (contactParam p) < u.val ∧
        u < (contactParam p).val ∧ (contactParam p).val < v ∧
        v.val < coreRight (contactParam p) ∧
        ((B.secondSide u=(bankPatchF p).symm (Plane.mk (-bankPatchδ p) 0) ∧
          B.secondSide v=(bankPatchF p).symm (Plane.mk (bankPatchδ p) 0)) ∨
         (B.secondSide u=(bankPatchF p).symm (Plane.mk (bankPatchδ p) 0) ∧
          B.secondSide v=(bankPatchF p).symm (Plane.mk (-bankPatchδ p) 0))) := by
    apply CurveComplex.actual_chart_axis_baselines_inside_side_core B.secondSide B.second_embedded
      (bankPatchF p) (bankPatchδ p) (hBankPatchδ p) (contactParam p).val
      (hContactParam p |>.symm ▸ hBankPatchPoint p)
      (by rw [hContactParam p,hBankPatchCenter p])
      (hBankPatchWholeAxis p) (hBankPatchSideAxis p)
      (coreLeft (contactParam p)) (coreRight (contactParam p))
      (hBankPatchSourceParameter p)
  choose bankU bankV hBankULower hBankUContact hBankVContact hBankVUpper hBankOrientation
    using hOrderedBankPatchBaselines
  choose bankL bankR hBankLFormula hBankRFormula hBankFamilySource hBankFamilyCoords
    hBankLZero hBankRZero using
      fun p : P => hActualOffsetEndpointFamilies (bankPatchF p) (bankPatchδ p) (bankPatchH p)
        (hBankPatchH p) (hBankPatchLeft0 p) (hBankPatchRight0 p) (hBankPatchSegments p)
  let flip : P → Bool := fun p => if B.secondSide (bankU p)=(bankPatchF p).symm (Plane.mk (-bankPatchδ p) 0)
    then false else true
  let orientedLeft : P → C(Interval,S) := fun p => if flip p then bankR p else bankL p
  let orientedRight : P → C(Interval,S) := fun p => if flip p then bankL p else bankR p
  have hOrientedZero (p : P) :
      orientedLeft p 0=B.secondSide (bankU p) ∧ orientedRight p 0=B.secondSide (bankV p) := by
    by_cases h : B.secondSide (bankU p)=(bankPatchF p).symm (Plane.mk (-bankPatchδ p) 0)
    · have hflip : flip p=false := by simp [flip,h]
      simp only [orientedLeft,orientedRight,hflip,Bool.false_eq_true,↓reduceIte]
      rw [hBankLZero,hBankRZero]
      rcases hBankOrientation p with ⟨hu,hv⟩|⟨hu,hv⟩
      · exact ⟨hu.symm,hv.symm⟩
      · have hh : (bankPatchF p).symm (Plane.mk (-bankPatchδ p) 0)=
            (bankPatchF p).symm (Plane.mk (bankPatchδ p) 0) := h.symm.trans hu
        have he := (bankPatchF p).symm.injOn (hBankPatchLeft0 p) (hBankPatchRight0 p) hh
        have hx := congrArg (fun z : Plane => z 0) he
        change -bankPatchδ p=bankPatchδ p at hx
        linarith [hBankPatchδ p]
    · have hflip : flip p=true := by simp [flip,h]
      simp only [orientedLeft,orientedRight,hflip,↓reduceIte]
      rw [hBankRZero,hBankLZero]
      rcases hBankOrientation p with ⟨hu,hv⟩|⟨hu,hv⟩
      · exact False.elim (h hu)
      · exact ⟨hu.symm,hv.symm⟩
  have hOrientedFamilySource (p : P) (t : Interval) :
      orientedLeft p t ∈ Ebank.source ∧ orientedRight p t ∈ Ebank.source := by
    have hs := hBankFamilySource p t
    have hl := (hBankPatchSource p hs.1).2.1
    have hr := (hBankPatchSource p hs.2).2.1
    dsimp [orientedLeft,orientedRight]
    split_ifs <;> first | exact ⟨hr,hl⟩ | exact ⟨hl,hr⟩
  have hOrientedInside (p : P) (t : Interval) (ht : 0 < t.val) :
      orientedLeft p t ∈ B.openInterior ∧ orientedRight p t ∈ B.openInterior := by
    let h : ℝ := (bankPatchH p/2)*t.val
    have hh : 0 < h := mul_pos (half_pos (hBankPatchH p)) ht
    have hhH : h < bankPatchH p := by dsimp [h]; nlinarith [t.property.2,hBankPatchH p]
    obtain ⟨f,hf,hfs,hfr,hf0,hf1,hinside,hm,hbfree,hcounts⟩ := hBankPatchInside p h hh hhH
    have hl : bankL p t=f 0 := (hBankLFormula p t).trans hf0.symm
    have hr : bankR p t=f 1 := (hBankRFormula p t).trans hf1.symm
    have hlI : bankL p t ∈ B.openInterior := hl.symm ▸ hinside (Set.mem_range_self 0)
    have hrI : bankR p t ∈ B.openInterior := hr.symm ▸ hinside (Set.mem_range_self 1)
    dsimp [orientedLeft,orientedRight]
    split_ifs <;> first | exact ⟨hrI,hlI⟩ | exact ⟨hlI,hrI⟩
  have hFiniteArcChain : ∀ n : ℕ, ∀ pieces : Fin (n+1) → C(Interval,S),
      (∀ i, IsEmbedding (pieces i)) →
      (∀ i, range (pieces i) ⊆ range B.disk) →
      (∀ i : Fin n, pieces i.castSucc 1=pieces i.succ 0) →
      (∀ i, pieces 0 0 ≠ pieces i 1) →
      ∃ f : C(Interval,S), IsEmbedding f ∧ f 0=pieces 0 0 ∧
        f 1=pieces (Fin.last n) 1 ∧ range f ⊆ ⋃ i, range (pieces i) := by
    intro n
    induction n with
    | zero =>
      intro pieces he hd hc hn
      refine ⟨pieces 0,he 0,rfl,rfl,?_⟩
      intro x hx
      exact Set.mem_iUnion.mpr ⟨0,hx⟩
    | succ n ih =>
      intro pieces he hd hc hn
      let prefixArc : Fin (n+1) → C(Interval,S) := fun i => pieces i.castSucc
      obtain ⟨f,hf,hf0,hf1,hfs⟩ := ih prefixArc
        (fun i => he i.castSucc) (fun i => hd i.castSucc)
        (fun i => hc i.castSucc) (fun i => hn i.castSucc)
      have hfD : range f ⊆ range B.disk := by
        intro x hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hfs hx)
        exact hd i.castSucc hi
      have hjoint : f 1=pieces (Fin.last (n+1)) 0 := by
        rw [hf1]
        exact hc (Fin.last n)
      have hne : f 0 ≠ pieces (Fin.last (n+1)) 1 := by rw [hf0]; exact hn _
      obtain ⟨g,hg,hg0,hg1,hgs⟩ := CurveComplex.actual_arc_join_inside_embedded_disk B.disk B.disk_embedded
        f (pieces (Fin.last (n+1))) hf (he _) hjoint hne hfD (hd _)
      refine ⟨g,hg,hg0.trans hf0,hg1,?_⟩
      intro x hx
      rcases hgs hx with hx|hx
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hfs hx)
        exact Set.mem_iUnion.mpr ⟨i.castSucc,hi⟩
      · exact Set.mem_iUnion.mpr ⟨Fin.last (n+1),hx⟩
  let sideX : ℝ → ℝ := fun θ => χ (Set.projIcc 0 1 zero_le_one ((θ-α)/(β-α)))
  have hSideXContinuous : Continuous sideX := χ.continuous.comp (continuous_projIcc.comp (by fun_prop))
  have hSideXStrict : StrictMonoOn sideX (Icc α β) := by
    intro θ hθ ϕ hϕ hlt
    apply hχ
    change Set.projIcc 0 1 zero_le_one ((θ-α)/(β-α)) < Set.projIcc 0 1 zero_le_one ((ϕ-α)/(β-α))
    have hθ01 : (θ-α)/(β-α) ∈ Icc (0:ℝ) 1 := ⟨div_nonneg (sub_nonneg.mpr hθ.1) (sub_pos.mpr hαβ).le,
      (div_le_one (sub_pos.mpr hαβ)).mpr (by linarith [hθ.2])⟩
    have hϕ01 : (ϕ-α)/(β-α) ∈ Icc (0:ℝ) 1 := ⟨div_nonneg (sub_nonneg.mpr hϕ.1) (sub_pos.mpr hαβ).le,
      (div_le_one (sub_pos.mpr hαβ)).mpr (by linarith [hϕ.2])⟩
    change (Set.projIcc 0 1 zero_le_one ((θ-α)/(β-α))).val <
      (Set.projIcc 0 1 zero_le_one ((ϕ-α)/(β-α))).val
    rw [Set.projIcc_of_mem zero_le_one hθ01,Set.projIcc_of_mem zero_le_one hϕ01]
    exact (div_lt_div_iff_of_pos_right (sub_pos.mpr hαβ)).mpr (by linarith)
  have hSideXCoordinate (θ : ℝ) (hθα : α < θ) (hθβ : θ < β) :
      Ebank (ψ θ)=Plane.mk (sideX θ) 0 := by
    let t : Interval := Set.projIcc 0 1 zero_le_one ((θ-α)/(β-α))
    have htval : t.val=(θ-α)/(β-α) := congrArg Subtype.val (Set.projIcc_of_mem zero_le_one
      ⟨(div_pos (sub_pos.mpr hθα) (sub_pos.mpr hαβ)).le,
        ((div_lt_one (sub_pos.mpr hαβ)).mpr (by linarith)).le⟩)
    have hct : core t=ψ θ := by
      change ψ (α+t.val*(β-α))=ψ θ
      rw [htval,div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hαβ))]
      congr 1
      ring
    have h0 : globalF1 (ψ θ) 1=0 := by rw [← hct,hGlobalF1Value,hCoreCoords]; rfl
    have h1 : globalE (ψ θ) 1=0 := by
      rcases hGlobalEY (ψ θ) with h|h <;> rw [h,h0] <;> norm_num
    ext i
    fin_cases i
    · change globalE (ψ θ) 0=sideX θ
      rw [hGlobalEX,← hct,hGlobalF1Value,hCoreCoords]
      rfl
    · exact h1
  have hSideOldContactCoordinate (θ : ℝ) (hθα : α < θ) (hθβ : θ < β)
      (j : J) (hj : ψ θ ∈ (old j).val.image) : θ ∈ contactCoordinates := by
    have hθ01 : θ ∈ Icc (0:ℝ) 1 := ⟨(hα.trans hθα).le,(hθβ.trans hβ).le⟩
    let t : Interval := ⟨θ,hθ01⟩
    have hψt : ψ θ=B.secondSide t := by
      dsimp [ψ,Function.comp_def]
      rw [Set.projIcc_of_mem zero_le_one hθ01]
    have hmark : ψ θ ∉ M.cover.branch := by
      have hs : ψ θ ∈ globalF0.source := (hGlobalF1Source ▸
        (hGlobalESource ▸ (hEbankSource ▸ hGlobalParameterBank θ hθα hθβ).1)).1
      exact fun hm => Set.disjoint_left.mp hGlobalMarks hs hm
    have htT : t ∈ T := by
      change B.secondSide t ∈ P
      apply Set.mem_iUnion.mpr
      refine ⟨j,⟨⟨⟨B.second_on_curve (Set.mem_range_self t),hψt ▸ hmark⟩,
        hψt ▸ hj,hψt ▸ hmark⟩,Set.mem_range_self t⟩⟩
    exact (hCoordinateMembership θ).mpr ⟨⟨t,htT⟩,rfl⟩
  let contactAt : Fin contactCoordinates.card → P := fun i =>
    ⟨B.secondSide (orderedLabel i).val,(orderedLabel i).property⟩
  have hContactAtParameter (i : Fin contactCoordinates.card) :
      contactParam (contactAt i)=orderedLabel i := by
    apply Subtype.ext
    apply B.second_embedded.injective
    exact hContactParam (contactAt i)
  have hContactAtOnto : Function.Surjective contactAt := by
    intro p
    have hmem : (contactParam p).val.val ∈ contactCoordinates :=
      (hCoordinateMembership _).mpr ⟨contactParam p,rfl⟩
    have hrange : (contactParam p).val.val ∈ range (contactCoordinates.orderEmbOfFin rfl) :=
      (contactCoordinates.range_orderEmbOfFin rfl).symm ▸ hmem
    obtain ⟨i,hi⟩ := hrange
    refine ⟨i,?_⟩
    apply Subtype.ext
    have ht : (orderedLabel i).val=(contactParam p).val :=
      Subtype.ext ((hOrderedLabelCoord i).trans hi)
    change B.secondSide (orderedLabel i).val=p.val
    rw [ht,hContactParam]
  have hBankPatchMiddleParameter (p : P) (u : Interval)
      (hu : B.secondSide u ∈ (bankPatchF p).source) :
      commonδ/2 < u.val ∧ u.val < 1-commonδ/2 := by
    have hnot := (hBankPatchSource p hu).2.2.2
    have hψu : ψ u.val=B.secondSide u := by
      dsimp [ψ,Function.comp_def]
      rw [Set.projIcc_of_mem zero_le_one u.property]
    constructor
    · by_contra hn
      exact hnot (Or.inl ⟨u.val,⟨u.property.1,le_of_not_gt hn⟩,hψu⟩)
    · by_contra hn
      exact hnot (Or.inr ⟨u.val,⟨le_of_not_gt hn,u.property.2⟩,hψu⟩)
  have hBankBaselineSources (p : P) :
      B.secondSide (bankU p) ∈ (bankPatchF p).source ∧
      B.secondSide (bankV p) ∈ (bankPatchF p).source := by
    rcases hBankOrientation p with ⟨hu,hv⟩|⟨hu,hv⟩
    · rw [hu,hv]
      exact ⟨(bankPatchF p).map_target (hBankPatchLeft0 p),(bankPatchF p).map_target (hBankPatchRight0 p)⟩
    · rw [hu,hv]
      exact ⟨(bankPatchF p).map_target (hBankPatchRight0 p),(bankPatchF p).map_target (hBankPatchLeft0 p)⟩
  have hBankUMiddle (p : P) : commonδ/2 < (bankU p).val ∧ (bankU p).val < 1-commonδ/2 :=
    hBankPatchMiddleParameter p (bankU p) (hBankBaselineSources p).1
  have hBankVMiddle (p : P) : commonδ/2 < (bankV p).val ∧ (bankV p).val < 1-commonδ/2 :=
    hBankPatchMiddleParameter p (bankV p) (hBankBaselineSources p).2
  let n := contactCoordinates.card
  let gapLeftθ : Fin (n+1) → ℝ := fun g =>
    if hg : g.val=0 then (cornerParam false).val
    else (bankV (contactAt ⟨g.val-1,by change g.val-1<n; omega⟩)).val
  let gapRightθ : Fin (n+1) → ℝ := fun g =>
    if hg : g.val<n then (bankU (contactAt ⟨g.val,hg⟩)).val else (cornerParam true).val
  let gapLeftCenter : Fin (n+1) → ℝ := fun g =>
    if hg : g.val=0 then α else (orderedLabel ⟨g.val-1,by change g.val-1<n; omega⟩).val.val
  let gapRightCenter : Fin (n+1) → ℝ := fun g =>
    if hg : g.val<n then (orderedLabel ⟨g.val,hg⟩).val.val else β
  have hGapParameterOrder (g : Fin (n+1)) :
      gapLeftCenter g < gapLeftθ g ∧ gapLeftθ g < gapRightθ g ∧ gapRightθ g < gapRightCenter g := by
    by_cases hg0 : g.val=0
    · by_cases hgn : g.val<n
      · simp only [gapLeftCenter,gapLeftθ,gapRightθ,gapRightCenter,dif_pos hg0,dif_pos hgn]
        have hu := hBankUContact (contactAt ⟨g.val,hgn⟩)
        rw [hContactAtParameter] at hu
        exact ⟨by dsimp [α]; linarith [hCornerParamOrder.1],
          hCornerParamOrder.2.1.trans (hBankUMiddle _).1,hu⟩
      · simp only [gapLeftCenter,gapLeftθ,gapRightθ,gapRightCenter,dif_pos hg0,dif_neg hgn]
        refine ⟨?_,?_,?_⟩
        · dsimp [α]; linarith [hCornerParamOrder.1]
        · linarith [hCornerParamOrder.2.1,hCornerParamOrder.2.2.1,hCommonδhalf]
        · dsimp [β]; linarith [hCornerParamOrder.2.2.2]
    · by_cases hgn : g.val<n
      · simp only [gapLeftCenter,gapLeftθ,gapRightθ,gapRightCenter,dif_neg hg0,dif_pos hgn]
        let i : Fin n := ⟨g.val-1,by omega⟩
        let j : Fin n := ⟨g.val,hgn⟩
        have hiOrder : i < j := by change g.val-1<g.val; omega
        have hcoord : (orderedLabel i).val.val < (orderedLabel j).val.val := by
          rw [hOrderedLabelCoord,hOrderedLabelCoord]
          exact (contactCoordinates.orderEmbOfFin rfl).strictMono hiOrder
        have hcore := hCoreOrder (orderedLabel i) (orderedLabel j) hcoord
        have hv := hBankVContact (contactAt i)
        have hu := hBankUContact (contactAt j)
        rw [hContactAtParameter] at hv hu
        refine ⟨hv,?_,hu⟩
        exact (hBankVUpper (contactAt i)).trans (by
          rw [hContactAtParameter]
          exact hcore.trans (by rw [← hContactAtParameter j]; exact hBankULower (contactAt j)))
      · simp only [gapLeftCenter,gapLeftθ,gapRightθ,gapRightCenter,dif_neg hg0,dif_neg hgn]
        have hv := hBankVContact (contactAt ⟨g.val-1,by change g.val-1<n; omega⟩)
        rw [hContactAtParameter] at hv
        exact ⟨hv,(hBankVMiddle _).2.trans hCornerParamOrder.2.2.1,
          by dsimp [β]; linarith [hCornerParamOrder.2.2.2]⟩
  have hGapCenterBounds (g : Fin (n+1)) : α ≤ gapLeftCenter g ∧ gapRightCenter g ≤ β := by
    constructor
    · dsimp [gapLeftCenter]
      split_ifs
      · exact le_rfl
      · have hbds := hCommonContactCore (orderedLabel ⟨g.val-1,by change g.val-1<n; omega⟩).val
          (orderedLabel ⟨g.val-1,by change g.val-1<n; omega⟩).property
        dsimp [α]
        linarith [hbds.1,hCornerParamOrder.2.1]
    · dsimp [gapRightCenter]
      split_ifs with hgn
      · have hbds := hCommonContactCore (orderedLabel ⟨g.val,hgn⟩).val (orderedLabel ⟨g.val,hgn⟩).property
        dsimp [β]
        linarith [hbds.2,hCornerParamOrder.2.2.1]
      · exact le_rfl
  let gapAθ : Fin (n+1) → ℝ := fun g => (gapLeftCenter g+gapLeftθ g)/2
  let gapBθ : Fin (n+1) → ℝ := fun g => (gapRightθ g+gapRightCenter g)/2
  have hGapθBounds (g : Fin (n+1)) :
      α < gapAθ g ∧ gapAθ g < gapLeftθ g ∧ gapLeftθ g < gapRightθ g ∧
      gapRightθ g < gapBθ g ∧ gapBθ g < β := by
    obtain ⟨hl,hlr,hr⟩ := hGapParameterOrder g
    obtain ⟨hαg,hgβ⟩ := hGapCenterBounds g
    dsimp [gapAθ,gapBθ]
    constructor; linarith
    constructor; linarith
    refine ⟨hlr,?_,?_⟩ <;> linarith
  have hGapNoContactCoordinate (g : Fin (n+1)) (θ : ℝ)
      (hθ : θ ∈ Icc (gapAθ g) (gapBθ g)) : θ ∉ contactCoordinates := by
    intro hm
    have hrange : θ ∈ range (contactCoordinates.orderEmbOfFin rfl) :=
      (contactCoordinates.range_orderEmbOfFin rfl).symm ▸ hm
    obtain ⟨i,hi⟩ := hrange
    have hleft : gapLeftCenter g < gapAθ g := by
      dsimp [gapAθ]
      linarith [(hGapParameterOrder g).1]
    have hright : gapBθ g < gapRightCenter g := by
      dsimp [gapBθ]
      linarith [(hGapParameterOrder g).2.2]
    by_cases hig : i.val < g.val
    · have hg0 : g.val ≠ 0 := by omega
      let j : Fin contactCoordinates.card := ⟨g.val-1,by change g.val-1<n; omega⟩
      have hij : i ≤ j := by change i.val≤g.val-1; omega
      have hh := (contactCoordinates.orderEmbOfFin rfl).monotone hij
      rw [hi,← hOrderedLabelCoord j] at hh
      have hc : gapLeftCenter g=(orderedLabel j).val.val := by simp only [gapLeftCenter,dif_neg hg0]; rfl
      rw [← hc] at hh
      linarith [hθ.1]
    · have hgn : g.val<n := by omega
      let j : Fin contactCoordinates.card := ⟨g.val,hgn⟩
      have hij : j ≤ i := by change g.val ≤ i.val; omega
      have hh := (contactCoordinates.orderEmbOfFin rfl).monotone hij
      rw [hi,← hOrderedLabelCoord j] at hh
      have hc : gapRightCenter g=(orderedLabel j).val.val := by simp only [gapRightCenter,dif_pos hgn]; rfl
      rw [← hc] at hh
      linarith [hθ.2]
  have hGapOldFree (g : Fin (n+1)) (θ : ℝ)
      (hθ : θ ∈ Icc (gapAθ g) (gapBθ g)) (j : J) : ψ θ ∉ (old j).val.image := by
    intro hj
    exact hGapNoContactCoordinate g θ hθ (hSideOldContactCoordinate θ
      ((hGapθBounds g).1.trans_le hθ.1) (hθ.2.trans_lt (hGapθBounds g).2.2.2.2) j hj)
  have hGapWholeAxis (g : Fin (n+1)) (x : ℝ)
      (hx : x ∈ Icc (sideX (gapAθ g)) (sideX (gapBθ g))) :
      ∃ y : S, y ∈ Ebank.source ∧ Ebank y=Plane.mk x 0 ∧ ∀ j, y ∉ (old j).val.image := by
    have hAB : gapAθ g ≤ gapBθ g := by
      obtain ⟨hαA,hAl,hlr,hrB,hBβ⟩ := hGapθBounds g
      exact (hAl.trans (hlr.trans hrB)).le
    obtain ⟨θ,hθ,hθx⟩ := intermediate_value_Icc hAB hSideXContinuous.continuousOn hx
    have hθα : α < θ := (hGapθBounds g).1.trans_le hθ.1
    have hθβ : θ < β := hθ.2.trans_lt (hGapθBounds g).2.2.2.2
    refine ⟨ψ θ,hGlobalParameterBank θ hθα hθβ,?_,hGapOldFree g θ hθ⟩
    rw [hSideXCoordinate θ hθα hθβ,hθx]
  let planePair : Plane ≃ₜ ℝ × ℝ := {
    toFun := fun z => (z 0,z 1)
    invFun := fun z => Plane.mk z.1 z.2
    left_inv := by intro z; ext i; fin_cases i <;> rfl
    right_inv := by intro z; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let bankPair := Ebank.trans planePair.toOpenPartialHomeomorph
  have hBankPairSource : bankPair.source=Ebank.source := by simp [bankPair]
  have hBankPairValue (x : S) : bankPair x=(Ebank x 0,Ebank x 1) := rfl
  let Ubank := bankPair.source
  let Vbank := bankPair.target
  let ebank : Ubank ≃ₜ Vbank := bankPair.toHomeomorphSourceTarget
  have hEbankPairAxis (u : Ubank) : (u : S) ∈ b.val.image ↔ (ebank u : ℝ × ℝ).2=0 :=
    hEbankAxis u.val (hBankPairSource ▸ u.property)
  have hGapPairWholeAxis (g : Fin (n+1)) (x : ℝ)
      (hx : x ∈ Icc (sideX (gapAθ g)) (sideX (gapBθ g))) :
      ∃ y : Vbank, y.val=(x,0) ∧ ∀ j, (ebank.symm y : S) ∉ (old j).val.image := by
    obtain ⟨z,hz,hcoord,hOldFree⟩ := hGapWholeAxis g x hx
    let u : Ubank := ⟨z,by change z ∈ bankPair.source; exact hBankPairSource.symm ▸ hz⟩
    refine ⟨ebank u,?_,?_⟩
    · change (Ebank z 0,Ebank z 1)=(x,0)
      rw [hcoord]
      rfl
    · simpa only [Homeomorph.symm_apply_apply] using hOldFree
  let cornerU : Bool → C(Interval,Ubank) := fun i =>
    ⟨fun t => ⟨(bankCornerL i t : S),by change (bankCornerL i t : S) ∈ bankPair.source; exact hBankPairSource.symm ▸ (bankCornerL i t).property⟩,
      (continuous_subtype_val.comp (bankCornerL i).continuous).subtype_mk (fun t => by change (bankCornerL i t : S) ∈ bankPair.source; exact hBankPairSource.symm ▸ (bankCornerL i t).property)⟩
  let patchLeftU : P → C(Interval,Ubank) := fun p =>
    ⟨fun t => ⟨orientedLeft p t,by change orientedLeft p t ∈ bankPair.source; exact hBankPairSource.symm ▸ (hOrientedFamilySource p t).1⟩,
      (orientedLeft p).continuous.subtype_mk (fun t => by change orientedLeft p t ∈ bankPair.source; exact hBankPairSource.symm ▸ (hOrientedFamilySource p t).1)⟩
  let patchRightU : P → C(Interval,Ubank) := fun p =>
    ⟨fun t => ⟨orientedRight p t,by change orientedRight p t ∈ bankPair.source; exact hBankPairSource.symm ▸ (hOrientedFamilySource p t).2⟩,
      (orientedRight p).continuous.subtype_mk (fun t => by change orientedRight p t ∈ bankPair.source; exact hBankPairSource.symm ▸ (hOrientedFamilySource p t).2)⟩
  let gapL : Fin (n+1) → C(Interval,Ubank) := fun g =>
    if hg : g.val=0 then cornerU false else patchRightU (contactAt ⟨g.val-1,by change g.val-1<n; omega⟩)
  let gapR : Fin (n+1) → C(Interval,Ubank) := fun g =>
    if hg : g.val<n then patchLeftU (contactAt ⟨g.val,hg⟩) else cornerU true
  have hGapBaselineSurface (g : Fin (n+1)) :
      (gapL g 0 : S)=ψ (gapLeftθ g) ∧ (gapR g 0 : S)=ψ (gapRightθ g) := by
    constructor
    · dsimp [gapL,gapLeftθ]
      split_ifs with hg
      · change (bankCornerL false 0 : S)=ψ (cornerParam false).val
        rw [hBankCornerBaseline]
        have hh := hCornerParam false
        change cornerL false 0=B.secondSide (Set.projIcc 0 1 zero_le_one (cornerParam false).val)
        rw [Set.projIcc_of_mem zero_le_one (cornerParam false).property]
        exact hh.symm
      · change orientedRight _ 0=ψ (bankV _).val
        rw [(hOrientedZero _).2]
        dsimp [ψ,Function.comp_def]
        rw [Set.projIcc_of_mem zero_le_one (bankV _).property]
    · dsimp [gapR,gapRightθ]
      split_ifs with hg
      · change orientedLeft _ 0=ψ (bankU _).val
        rw [(hOrientedZero _).1]
        dsimp [ψ,Function.comp_def]
        rw [Set.projIcc_of_mem zero_le_one (bankU _).property]
      · change (bankCornerL true 0 : S)=ψ (cornerParam true).val
        rw [hBankCornerBaseline]
        have hh := hCornerParam true
        change cornerL true 0=B.secondSide (Set.projIcc 0 1 zero_le_one (cornerParam true).val)
        rw [Set.projIcc_of_mem zero_le_one (cornerParam true).property]
        exact hh.symm
  have hGapLCoordinate (g : Fin (n+1)) : (ebank (gapL g 0) : ℝ × ℝ)=(sideX (gapLeftθ g),0) := by
    change (Ebank (gapL g 0 : S) 0,Ebank (gapL g 0 : S) 1)=_
    rw [(hGapBaselineSurface g).1,hSideXCoordinate _
      ((hGapθBounds g).1.trans (hGapθBounds g).2.1)
      ((hGapθBounds g).2.2.1.trans ((hGapθBounds g).2.2.2.1.trans (hGapθBounds g).2.2.2.2))]
    rfl
  have hGapRCoordinate (g : Fin (n+1)) : (ebank (gapR g 0) : ℝ × ℝ)=(sideX (gapRightθ g),0) := by
    change (Ebank (gapR g 0 : S) 0,Ebank (gapR g 0 : S) 1)=_
    rw [(hGapBaselineSurface g).2,hSideXCoordinate _
      ((hGapθBounds g).1.trans ((hGapθBounds g).2.1.trans (hGapθBounds g).2.2.1))
      ((hGapθBounds g).2.2.2.1.trans (hGapθBounds g).2.2.2.2)]
    rfl
  have hPatchPairPositive (p : P) (t : Interval) (ht : t ≠ 0) :
      0 < (ebank (patchLeftU p t) : ℝ × ℝ).2 ∧ 0 < (ebank (patchRightU p t) : ℝ × ℝ).2 := by
    have htp : 0 < t.val := lt_of_le_of_ne t.property.1 (by intro he; exact ht (Subtype.ext he.symm))
    obtain ⟨hl,hr⟩ := hOrientedInside p t htp
    exact ⟨(hEbankInside _ (hOrientedFamilySource p t).1).mp hl,
      (hEbankInside _ (hOrientedFamilySource p t).2).mp hr⟩
  have hGapPairPositive (g : Fin (n+1)) (t : Interval) (ht : t ≠ 0) :
      0 < (ebank (gapL g t) : ℝ × ℝ).2 ∧ 0 < (ebank (gapR g t) : ℝ × ℝ).2 := by
    constructor
    · dsimp [gapL]
      split_ifs
      · exact hBankCornerPositive false t ht
      · exact (hPatchPairPositive _ t ht).2
    · dsimp [gapR]
      split_ifs
      · exact (hPatchPairPositive _ t ht).1
      · exact hBankCornerPositive true t ht
  have hGapRealOrder (g : Fin (n+1)) :
      sideX (gapAθ g) < sideX (gapLeftθ g) ∧
      sideX (gapLeftθ g) < sideX (gapRightθ g) ∧
      sideX (gapRightθ g) < sideX (gapBθ g) := by
    obtain ⟨hαA,hAl,hlr,hrB,hBβ⟩ := hGapθBounds g
    have hA : gapAθ g ∈ Icc α β := ⟨hαA.le,(hAl.trans (hlr.trans (hrB.trans hBβ))).le⟩
    have hl : gapLeftθ g ∈ Icc α β := ⟨(hαA.trans hAl).le,(hlr.trans (hrB.trans hBβ)).le⟩
    have hr : gapRightθ g ∈ Icc α β := ⟨(hαA.trans (hAl.trans hlr)).le,(hrB.trans hBβ).le⟩
    have hB : gapBθ g ∈ Icc α β := ⟨(hαA.trans (hAl.trans (hlr.trans hrB))).le,hBβ.le⟩
    exact ⟨hSideXStrict hA hl hAl,hSideXStrict hl hr hlr,hSideXStrict hr hB hrB⟩
  obtain ⟨matchedT,hMatchedT,hMatchedT1,hMatchedPaths⟩ :=
    actual_marked_simultaneous_gap_matching M old b Ubank Vbank bankPair.open_target ebank
      (fun g => sideX (gapAθ g)) (fun g => sideX (gapLeftθ g))
      (fun g => sideX (gapRightθ g)) (fun g => sideX (gapBθ g))
      (fun g => (hGapRealOrder g).1) (fun g => (hGapRealOrder g).2.1) (fun g => (hGapRealOrder g).2.2)
      hGapPairWholeAxis hEbankPairAxis gapL gapR hGapLCoordinate hGapRCoordinate hGapPairPositive
  choose matchedGap hMatchedGapEmbedded hMatchedGapBFree hMatchedGapOldFree hMatchedGapFormula using hMatchedPaths
  have hMatchedGapInside (g : Fin (n+1)) : range (matchedGap g) ⊆ B.openInterior := by
    rintro x ⟨s,rfl⟩
    obtain ⟨u,hu,hcoord⟩ := hMatchedGapFormula g s
    have hpos := hGapPairPositive g matchedT (by intro he; subst matchedT; norm_num at hMatchedT)
    have hy : 0 < (ebank u : ℝ × ℝ).2 := by
      rw [hcoord]
      change 0 < (1-s.val)*(ebank (gapL g matchedT) : ℝ × ℝ).2+s.val*(ebank (gapR g matchedT) : ℝ × ℝ).2
      rcases eq_or_lt_of_le s.property.1 with hs|hs
      · have hs0 : s.val=0 := hs.symm
        simpa [hs0] using hpos.1
      · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr s.property.2) hpos.1.le) (mul_pos hs hpos.2)
    rw [← hu]
    exact (hEbankInside _ (hBankPairSource ▸ u.property)).mpr hy
  let cornerT : Interval := ⟨cornerη*matchedT.val,mul_nonneg hCornerη.le matchedT.property.1,
    (mul_le_of_le_one_right hCornerη.le matchedT.property.2).trans hCornerη1.le⟩
  have hCornerT : 0 < cornerT.val := mul_pos hCornerη hMatchedT
  choose fixedCorner hFixedCornerEmbedded hFixedCornerZero hFixedCornerOne hFixedCornerSource
    hFixedCornerInside hFixedCornerA hFixedCornerB hFixedCornerMarks hFixedCornerOld using
      fun i => hCornerPaths i cornerT hCornerT
  have hFixedCornerBankEnd (i : Bool) : fixedCorner i 1=(bankCornerL i matchedT : S) := by
    rw [hFixedCornerOne,hBankCornerFormula]
  obtain ⟨fixedRight,hFixedRightEmbedded,hFixedRightRange,hFixedRightZero,hFixedRightOne⟩ :=
    actual_reverse_embedded_continuous_arc (fixedCorner true) (hFixedCornerEmbedded true)
  have hFirstCornerA : B.firstCorner ∈ a.val.image :=
    B.first_on_curve (B.first_zero ▸ Set.mem_range_self 0)
  have hSecondCornerA : B.secondCorner ∈ a.val.image :=
    B.first_on_curve (B.first_one ▸ Set.mem_range_self 1)
  have hInteriorNoCorners : Disjoint B.openInterior ({B.firstCorner,B.secondCorner} : Set S) := by
    apply Set.disjoint_left.mpr
    intro p hp hc
    rcases hc with hc|hc
    · exact Set.disjoint_left.mp hempty hp (Or.inl (hc ▸ hFirstCornerA))
    · exact Set.disjoint_left.mp hempty hp (Or.inl (hc ▸ hSecondCornerA))
  have hFirstNotInterior : B.firstCorner ∉ B.openInterior :=
    fun hp => Set.disjoint_left.mp hInteriorNoCorners hp (Set.mem_insert _ _)
  have hSecondNotInterior : B.secondCorner ∉ B.openInterior :=
    fun hp => Set.disjoint_left.mp hInteriorNoCorners hp (by simp)
  have hCornerDistinct : B.firstCorner ≠ B.secondCorner := by
    intro he
    have h01 := B.first_embedded.injective (B.first_zero.trans (he.trans B.first_one.symm))
    exact zero_ne_one h01
  have hCornersInDisk : ({B.firstCorner,B.secondCorner} : Set S) ⊆ range B.disk := by
    intro p hp
    have hs : p ∈ range B.firstSide := by
      rcases hp with hp|hp
      · exact ⟨0,B.first_zero.trans hp.symm⟩
      · exact ⟨1,B.first_one.trans hp.symm⟩
    exact image_subset_range _ _ (B.boundary_eq.symm ▸ (show p ∈ range B.firstSide ∪ range B.secondSide from Or.inl hs))
  have hInteriorInDisk : B.openInterior ⊆ range B.disk := image_subset_range _ _
  have hFixedCornerCarrier (i : Bool) : range (fixedCorner i) ⊆ B.openInterior ∪ {corner i} := by
    intro p hp
    by_cases he : p=corner i
    · exact Or.inr he
    · exact Or.inl (hFixedCornerInside i ⟨hp,he⟩)
  have hFixedCornerDisk (i : Bool) : range (fixedCorner i) ⊆ range B.disk := by
    intro p hp
    rcases hFixedCornerCarrier i hp with hp|hp
    · exact hInteriorInDisk hp
    · exact hCornersInDisk (hp ▸ hCornerMember i)
  have hRightCarrier : range fixedRight ⊆ B.openInterior ∪ {B.secondCorner} := by
    rw [hFixedRightRange]
    exact hFixedCornerCarrier true
  have hRightDisk : range fixedRight ⊆ range B.disk := by
    rw [hFixedRightRange]
    exact hFixedCornerDisk true
  have hFinalCarrierGeometry (f : C(Interval,S)) (hf : IsEmbedding f)
      (hf0 : f 0=B.firstCorner) (hf1 : f 1=B.secondCorner)
      (hsub : range f ⊆ B.openInterior ∪ ({B.firstCorner,B.secondCorner} : Set S)) :
      range f ∩ b.val.image=({B.firstCorner,B.secondCorner} : Set S) ∧
      range B.firstSide ∩ range f=({B.firstCorner,B.secondCorner} : Set S) ∧
      range f ∩ Kraw=({B.firstCorner,B.secondCorner} : Set S) ∧
      (∀ p ∈ range f, p ∈ M.cover.branch → p ∈ ({B.firstCorner,B.secondCorner} : Set S)) ∧
      ∃ Q : C(Metric.closedBall (0 : Plane) 1,S), IsEmbedding Q ∧
        Q '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=range B.firstSide ∪ range f ∧
        (∀ p ∈ range Q, p ∈ M.cover.branch → p ∈ ({B.firstCorner,B.secondCorner} : Set S)) ∧
        Disjoint (Q '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) Kraw := by
    have hcornF : ({B.firstCorner,B.secondCorner} : Set S) ⊆ range f := by
      rintro p (he|he)
      · exact ⟨0,hf0.trans he.symm⟩
      · exact ⟨1,hf1.trans he.symm⟩
    have hFD : range f ⊆ range B.disk := fun p hp =>
      (hsub hp).elim (fun hi => hInteriorInDisk hi) (fun hc => hCornersInDisk hc)
    have hmeet (X : Set S) (hcornX : ({B.firstCorner,B.secondCorner} : Set S) ⊆ X)
        (hfree : Disjoint B.openInterior X) :
        range f ∩ X=({B.firstCorner,B.secondCorner} : Set S) := by
      apply Set.Subset.antisymm
      · intro p hp
        rcases hsub hp.1 with hi|hc
        · exact False.elim (Set.disjoint_left.mp hfree hi hp.2)
        · exact hc
      · intro p hp
        exact ⟨hcornF hp,hcornX hp⟩
    have hcornB : ({B.firstCorner,B.secondCorner} : Set S) ⊆ b.val.image := by
      rintro p (he|he)
      · exact he ▸ B.second_on_curve (B.second_zero ▸ Set.mem_range_self 0)
      · exact he ▸ B.second_on_curve (B.second_one ▸ Set.mem_range_self 1)
    have hfb := hmeet b.val.image hcornB (hempty.mono_right Set.subset_union_right)
    have hcornFirst : ({B.firstCorner,B.secondCorner} : Set S) ⊆ range B.firstSide := by
      rintro p (he|he)
      · exact ⟨0,B.first_zero.trans he.symm⟩
      · exact ⟨1,B.first_one.trans he.symm⟩
    have hfirstfree : Disjoint B.openInterior (range B.firstSide) :=
      (hempty.mono_right Set.subset_union_left).mono_right B.first_on_curve
    have hfirst := hmeet (range B.firstSide) hcornFirst hfirstfree
    have hfirst' : range B.firstSide ∩ range f=({B.firstCorner,B.secondCorner} : Set S) := by
      rw [Set.inter_comm,hfirst]
    have hcornK : ({B.firstCorner,B.secondCorner} : Set S) ⊆ Kraw :=
      fun p hp => (hOriginalRemainderSupport.symm ▸ hp).2
    have hKfree : Disjoint B.openInterior Kraw := by
      apply Set.disjoint_left.mpr
      intro p hp hpK
      have hc : p ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hOriginalRemainderSupport ▸ (show p ∈ range B.disk ∩ Kraw from ⟨hInteriorInDisk hp,hpK⟩)
      exact Set.disjoint_left.mp hInteriorNoCorners hp hc
    have hfK := hmeet Kraw hcornK hKfree
    obtain ⟨Q,hQ,hQboundary,hQdisk,hQmarks,hQK⟩ :=
      actual_marked_joined_path_cap_inside_original_disk M a b B Kraw hOriginalRemainderSupport f hf hf0 hf1 hfirst' hFD
    exact ⟨hfb,hfirst',hfK,(fun p hp hm => B.marks_are_corners p (hFD hp) hm),Q,hQ,hQboundary,hQmarks,hQK⟩
  let chosenHeight : P → ℝ := fun p => (bankPatchH p/2)*matchedT.val
  have hChosenHeight (p : P) : 0 < chosenHeight p ∧ chosenHeight p < bankPatchH p := by
    constructor
    · exact mul_pos (half_pos (hBankPatchH p)) hMatchedT
    · dsimp [chosenHeight]; nlinarith [matchedT.property.2,hBankPatchH p]
  choose rawPiece hRawPieceEmbedded hRawPieceSource hRawPieceRange hRawPieceZero hRawPieceOne
    hRawPieceInside hRawPieceMarks hRawPieceB hRawPieceCounts using
      fun p => hBankPatchInside p (chosenHeight p) (hChosenHeight p).1 (hChosenHeight p).2
  choose reversePiece hReversePieceEmbedded hReversePieceRange hReversePieceZero hReversePieceOne using
    fun p => actual_reverse_embedded_continuous_arc (rawPiece p) (hRawPieceEmbedded p)
  let fixedPatch : P → C(Interval,S) := fun p => if flip p then reversePiece p else rawPiece p
  have hFixedPatchRange (p : P) : range (fixedPatch p)=range (rawPiece p) := by
    dsimp [fixedPatch]
    split_ifs
    · exact hReversePieceRange p
    · rfl
  have hFixedPatchEmbedded (p : P) : IsEmbedding (fixedPatch p) := by
    dsimp [fixedPatch]
    split_ifs
    · exact hReversePieceEmbedded p
    · exact hRawPieceEmbedded p
  have hFixedPatchZero (p : P) : fixedPatch p 0=orientedLeft p matchedT := by
    have hl : rawPiece p 0=bankL p matchedT := (hRawPieceZero p).trans (hBankLFormula p matchedT).symm
    have hr : rawPiece p 1=bankR p matchedT := (hRawPieceOne p).trans (hBankRFormula p matchedT).symm
    dsimp [fixedPatch,orientedLeft]
    split_ifs
    · exact (hReversePieceZero p).trans hr
    · exact hl
  have hFixedPatchOne (p : P) : fixedPatch p 1=orientedRight p matchedT := by
    have hl : rawPiece p 0=bankL p matchedT := (hRawPieceZero p).trans (hBankLFormula p matchedT).symm
    have hr : rawPiece p 1=bankR p matchedT := (hRawPieceOne p).trans (hBankRFormula p matchedT).symm
    dsimp [fixedPatch,orientedRight]
    split_ifs
    · exact (hReversePieceOne p).trans hl
    · exact hr
  have hFixedPatchInside (p : P) : range (fixedPatch p) ⊆ B.openInterior := by
    rw [hFixedPatchRange]
    exact hRawPieceInside p
  have hFixedPatchSource (p : P) : range (fixedPatch p) ⊆ (bankPatchF p).source := by
    rw [hFixedPatchRange]
    exact hRawPieceSource p
  have hFixedPatchMarks (p : P) : Disjoint (range (fixedPatch p)) (M.cover.branch : Set S) := by
    rw [hFixedPatchRange]
    exact hRawPieceMarks p
  have hFixedPatchB (p : P) : Disjoint (range (fixedPatch p)) b.val.image := by
    rw [hFixedPatchRange]
    exact hRawPieceB p
  have hFixedPatchCounts (p : P) (j : J) :
      (range (fixedPatch p) ∩ (old j).val.image).Finite ∧
      (range (fixedPatch p) ∩ (old j).val.image).ncard ≤ if p.val ∈ (old j).val.image then 1 else 0 := by
    rw [hFixedPatchRange]
    exact ⟨(hRawPieceCounts p j).2.2.1,(hRawPieceCounts p j).2.2.2⟩
  have hFixedPatchesDisjoint (p q : P) (hpq : p ≠ q) :
      Disjoint (range (fixedPatch p)) (range (fixedPatch q)) :=
    (hContactUDisjoint p q hpq).mono
      (fun x hx => (hBankPatchSource p (hFixedPatchSource p hx)).1)
      (fun x hx => (hBankPatchSource q (hFixedPatchSource q hx)).1)
  let pieces : Fin (2*n+3) → C(Interval,S) := fun k =>
    if hk : k.val=2*n+2 then fixedRight
    else if hk0 : k.val=0 then fixedCorner false
    else if hkodd : k.val%2=1 then (matchedGap ⟨k.val/2,by omega⟩).toContinuousMap
    else fixedPatch (contactAt ⟨(k.val-2)/2,by omega⟩)
  have hPieceZero : pieces 0=fixedCorner false := by
    have hn : (0:ℕ) ≠ 2*n+2 := by omega
    simp [pieces,hn]
  have hPieceLast : pieces (Fin.last (2*n+2))=fixedRight := by simp [pieces]
  have hPieceGap (g : Fin (n+1)) : pieces ⟨2*g.val+1,by omega⟩=(matchedGap g).toContinuousMap := by
    have hlast : 2*g.val+1 ≠ 2*n+2 := by omega
    have hzero : 2*g.val+1 ≠ 0 := by omega
    have hodd : (2*g.val+1)%2=1 := by omega
    dsimp only [pieces]
    rw [dif_neg hlast,dif_neg hzero,dif_pos hodd]
    exact congrArg (fun j : Fin (n+1) => (matchedGap j).toContinuousMap)
      (show (⟨(2*g.val+1)/2,by omega⟩ : Fin (n+1))=g from Fin.ext (by change (2*g.val+1)/2=g.val; omega))
  have hPiecePatch (i : Fin n) : pieces ⟨2*i.val+2,by omega⟩=fixedPatch (contactAt i) := by
    have hlast : 2*i.val+2 ≠ 2*n+2 := by omega
    have hzero : 2*i.val+2 ≠ 0 := by omega
    have heven : (2*i.val+2)%2 ≠ 1 := by omega
    dsimp only [pieces]
    rw [dif_neg hlast,dif_neg hzero,dif_neg heven]
    simp only [show (2*i.val+2-2)/2=i.val by omega]
    rfl
  have hPiecesEmbedded (k : Fin (2*n+3)) : IsEmbedding (pieces k) := by
    dsimp only [pieces]
    split_ifs
    · exact hFixedRightEmbedded
    · exact hFixedCornerEmbedded false
    · exact hMatchedGapEmbedded _
    · exact hFixedPatchEmbedded _
  have hPiecesCarrier (k : Fin (2*n+3)) :
      range (pieces k) ⊆ B.openInterior ∪ ({B.firstCorner,B.secondCorner} : Set S) := by
    dsimp only [pieces]
    split_ifs
    · intro p hp
      rcases hRightCarrier hp with hp|hp
      · exact Or.inl hp
      · exact Or.inr (Set.mem_insert_iff.mpr (Or.inr hp))
    · intro p hp
      rcases hFixedCornerCarrier false hp with hp|hp
      · exact Or.inl hp
      · exact Or.inr (Set.mem_insert_iff.mpr (Or.inl hp))
    · exact (hMatchedGapInside _).trans Set.subset_union_left
    · exact (hFixedPatchInside _).trans Set.subset_union_left
  have hPiecesDisk (k : Fin (2*n+3)) : range (pieces k) ⊆ range B.disk :=
    (hPiecesCarrier k).trans (Set.union_subset hInteriorInDisk hCornersInDisk)
  have hPiecesEnd (k : Fin (2*n+3)) : pieces k 1 ∈ B.openInterior ∪ {B.secondCorner} := by
    dsimp only [pieces]
    split_ifs
    · exact Or.inr (hFixedRightOne.trans (hFixedCornerZero true))
    · exact Or.inl ((hFixedCornerOne false).symm ▸ hCornerFamiliesInside false cornerT hCornerT)
    · exact Or.inl (hMatchedGapInside _ (Set.mem_range_self 1))
    · exact Or.inl (hFixedPatchInside _ (Set.mem_range_self 1))
  have hPiecesStartAvoid (k : Fin (2*n+3)) : pieces 0 0 ≠ pieces k 1 := by
    rw [hPieceZero,hFixedCornerZero]
    intro he
    change B.firstCorner=pieces k 1 at he
    rcases hPiecesEnd k with hi|hi
    · exact hFirstNotInterior (he.symm ▸ hi)
    · exact hCornerDistinct (he.trans hi)
  have hGapStartFirst : (gapL (0 : Fin (n+1)) matchedT : S)=(bankCornerL false matchedT : S) := by
    rfl
  have hGapEndLast : (gapR (Fin.last n) matchedT : S)=(bankCornerL true matchedT : S) := by
    dsimp only [gapR, Fin.val_last]
    rw [dif_neg (Nat.lt_irrefl n)]
    rfl
  have hGapEndBefore (i : Fin n) :
      (gapR ⟨i.val,by omega⟩ matchedT : S)=orientedLeft (contactAt i) matchedT := by
    dsimp only [gapR]
    rw [dif_pos i.isLt]
    rfl
  have hGapStartAfter (i : Fin n) :
      (gapL ⟨i.val+1,by omega⟩ matchedT : S)=orientedRight (contactAt i) matchedT := by
    change orientedRight (contactAt ⟨i.val+1-1,by omega⟩) matchedT =
      orientedRight (contactAt i) matchedT
    have he : (⟨i.val+1-1,by omega⟩ : Fin n) = i := by
      apply Fin.ext
      change i.val+1-1=i.val
      omega
    rw [he]
  have hPiecesJoin (i : Fin (2*n+2)) : pieces i.castSucc 1=pieces i.succ 0 := by
    by_cases hi0 : i.val=0
    · have hleft : i.castSucc=(0 : Fin (2*n+3)) := Fin.ext hi0
      have hright : i.succ=(⟨2*(0:Fin (n+1)).val+1,by omega⟩ : Fin (2*n+3)) := by apply Fin.ext; simp [hi0]
      rw [hleft,hright,hPieceZero,hPieceGap,hFixedCornerBankEnd]
      exact ((matchedGap 0).source.trans hGapStartFirst).symm
    · by_cases hilast : i.val=2*n+1
      · have hleft : i.castSucc=(⟨2*(Fin.last n).val+1,by omega⟩ : Fin (2*n+3)) := Fin.ext hilast
        have hright : i.succ=Fin.last (2*n+2) := by apply Fin.ext; simp [hilast]
        rw [hleft,hright,hPieceGap,hPieceLast,hFixedRightZero,hFixedCornerBankEnd]
        exact (matchedGap (Fin.last n)).target.trans hGapEndLast
      · by_cases hiodd : i.val%2=1
        · let j : Fin n := ⟨i.val/2,by omega⟩
          let g : Fin (n+1) := ⟨j.val,by omega⟩
          have hleft : i.castSucc=(⟨2*g.val+1,by omega⟩ : Fin (2*n+3)) := by apply Fin.ext; dsimp [g,j]; omega
          have hright : i.succ=(⟨2*j.val+2,by omega⟩ : Fin (2*n+3)) := by apply Fin.ext; dsimp [j]; omega
          rw [hleft,hright,hPieceGap,hPiecePatch,hFixedPatchZero]
          exact (matchedGap g).target.trans (hGapEndBefore j)
        · let j : Fin n := ⟨(i.val-2)/2,by omega⟩
          let g : Fin (n+1) := ⟨j.val+1,by omega⟩
          have hleft : i.castSucc=(⟨2*j.val+2,by omega⟩ : Fin (2*n+3)) := by apply Fin.ext; dsimp [j]; omega
          have hright : i.succ=(⟨2*g.val+1,by omega⟩ : Fin (2*n+3)) := by apply Fin.ext; dsimp [g,j]; omega
          rw [hleft,hright,hPiecePatch,hPieceGap,hFixedPatchOne]
          exact ((matchedGap g).source.trans (hGapStartAfter j)).symm
  obtain ⟨joinedF,hJoinedEmbedded,hJoinedZero,hJoinedOne,hJoinedPieces⟩ :=
    hFiniteArcChain (2*n+2) pieces hPiecesEmbedded hPiecesDisk hPiecesJoin hPiecesStartAvoid
  have hJoinedFirst : joinedF 0=B.firstCorner := by rw [hJoinedZero,hPieceZero,hFixedCornerZero]; rfl
  have hJoinedSecond : joinedF 1=B.secondCorner := by
    rw [hJoinedOne,hPieceLast,hFixedRightOne,hFixedCornerZero]
    rfl
  have hJoinedCarrier : range joinedF ⊆ B.openInterior ∪ ({B.firstCorner,B.secondCorner} : Set S) := by
    intro p hp
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (hJoinedPieces hp)
    exact hPiecesCarrier k hk
  obtain ⟨hJoinedB,hJoinedFirstSide,hJoinedK,hJoinedMarks,joinedQ,hJoinedQEmbedded,
    hJoinedQBoundary,hJoinedQMarks,hJoinedQK⟩ :=
    hFinalCarrierGeometry joinedF hJoinedEmbedded hJoinedFirst hJoinedSecond hJoinedCarrier
  have hJoinedOldInPatches (j : J) :
      range joinedF ∩ arcInterior M (old j) ⊆ ⋃ p : P, range (fixedPatch p) ∩ (old j).val.image := by
    intro x hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (hJoinedPieces hx.1)
    dsimp only [pieces] at hk
    split_ifs at hk
    · rw [hFixedRightRange] at hk
      exact False.elim (Set.disjoint_left.mp (hFixedCornerOld true j) hk hx.2)
    · exact False.elim (Set.disjoint_left.mp (hFixedCornerOld false j) hk hx.2)
    · exact False.elim (Set.disjoint_left.mp (hMatchedGapOldFree _ j) hk hx.2.1)
    · exact Set.mem_iUnion.mpr ⟨_,hk,hx.2.1⟩
  have hJoinedOldBudget (j : J) :
      (range joinedF ∩ arcInterior M (old j)).Finite ∧
      (range joinedF ∩ arcInterior M (old j)).ncard ≤
        (crossings M b (old j) ∩ range B.secondSide).ncard := by
    obtain ⟨hUnionFinite,hUnionBound⟩ := CurveComplex.actual_finite_union_card_bound
      (fun p : P => range (fixedPatch p) ∩ (old j).val.image)
      (fun p => (hFixedPatchCounts p j).1)
    refine ⟨hUnionFinite.subset (hJoinedOldInPatches j),?_⟩
    calc
      (range joinedF ∩ arcInterior M (old j)).ncard ≤
          (⋃ p : P, range (fixedPatch p) ∩ (old j).val.image).ncard :=
        Set.ncard_le_ncard (hJoinedOldInPatches j) hUnionFinite
      _ ≤ ∑ p : P, (range (fixedPatch p) ∩ (old j).val.image).ncard := hUnionBound
      _ ≤ ∑ p : P, if p.val ∈ (old j).val.image then 1 else 0 :=
        Finset.sum_le_sum (fun p hp => (hFixedPatchCounts p j).2)
      _ = (crossings M b (old j) ∩ range B.secondSide).ncard := hActualSideIncidenceBudget j
  have hPositiveRayAffineCrossing := actual_marked_positive_radial_horizontal_crossing_chart M
  have hFixedPatchHeight (p : P) (x : S) (hx : x ∈ range (fixedPatch p)) :
      (bankPatchF p) x 1=chosenHeight p := by
    have hr : x ∈ range (rawPiece p) := hFixedPatchRange p ▸ hx
    obtain ⟨z,hz,hzx⟩ := hRawPieceRange p ▸ hr
    have hzT := hBankPatchSegments p (chosenHeight p) (hChosenHeight p).1 (hChosenHeight p).2 hz
    have hy : z 1=chosenHeight p := by
      rw [segment_eq_image'] at hz
      obtain ⟨u,hu,he⟩ := hz
      have hh := congrArg (fun z : Plane => z 1) he
      change chosenHeight p+u*(chosenHeight p-chosenHeight p)=z 1 at hh
      simpa using hh.symm
    rw [← hzx,(bankPatchF p).right_inv hzT,hy]
  let otherPieces : P → Set S := fun p =>
    ((range (fixedCorner false) ∪ range fixedRight) ∪ ⋃ g, range (matchedGap g)) ∪
      ⋃ q : P, if q=p then ∅ else range (fixedPatch q)
  have hOtherPiecesCompact (p : P) : IsCompact (otherPieces p) := by
    apply IsCompact.union
    · exact ((isCompact_range (fixedCorner false).continuous).union
        (isCompact_range fixedRight.continuous)).union
        (isCompact_iUnion (fun g => isCompact_range (matchedGap g).continuous))
    · apply isCompact_iUnion
      intro q
      split_ifs
      · exact isCompact_empty
      · exact isCompact_range (fixedPatch q).continuous
  have hJoinedCoverForPatch (p : P) : range joinedF ⊆ range (fixedPatch p) ∪ otherPieces p := by
    intro x hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (hJoinedPieces hx)
    dsimp only [pieces] at hk
    split_ifs at hk
    · exact Or.inr (Or.inl (Or.inl (Or.inr hk)))
    · exact Or.inr (Or.inl (Or.inl (Or.inl hk)))
    · exact Or.inr (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨_,hk⟩)))
    · rename_i hlast hzero hodd
      let q : P := contactAt ⟨(k.val-2)/2,by omega⟩
      change x ∈ range (fixedPatch q) at hk
      by_cases hqp : q=p
      · exact Or.inl (hqp ▸ hk)
      · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨q,by simpa [hqp] using hk⟩))
  have hPatchOldPointNotOthers (p : P) (j : J) (x : S)
      (hx : x ∈ range (fixedPatch p)) (hold : x ∈ arcInterior M (old j)) : x ∉ otherPieces p := by
    rintro ((hcorner|hgap)|hpatch)
    · rcases hcorner with hl|hr
      · exact Set.disjoint_left.mp (hFixedCornerOld false j) hl hold
      · rw [hFixedRightRange] at hr
        exact Set.disjoint_left.mp (hFixedCornerOld true j) hr hold
    · obtain ⟨g,hg⟩ := Set.mem_iUnion.mp hgap
      exact Set.disjoint_left.mp (hMatchedGapOldFree g j) hg hold.1
    · obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hpatch
      by_cases hqp : q=p
      · simp [hqp] at hq
      · have hq' : x ∈ range (fixedPatch q) := by simpa [hqp] using hq
        exact Set.disjoint_left.mp (hFixedPatchesDisjoint p q (Ne.symm hqp)) hx hq'
  have hJoinedPointNotCorner (j : J) (x : S) (hx : x ∈ arcInterior M (old j)) :
      x ∉ ({B.firstCorner,B.secondCorner} : Set S) :=
    fun hc => hcorners j x hc hx.2 hx.1
  have hJoinedWholeTraceCharts (j : J) (x : S)
      (hx : x ∈ range joinedF ∩ arcInterior M (old j)) :
      ∃ F : OpenPartialHomeomorph S Plane, x ∈ F.source ∧ F x=0 ∧
        Disjoint F.source (M.cover.branch : Set S) ∧ Disjoint F.source Kraw ∧
        ∀ y ∈ F.source, (y ∈ range joinedF ↔ F y 1=0) ∧
          (y ∈ (old j).val.image ↔ F y 0=0) := by
    obtain ⟨p,hpPiece,hpOld⟩ := Set.mem_iUnion.mp (hJoinedOldInPatches j hx)
    have hIncident : p.val ∈ (old j).val.image := by
      by_contra hn
      exact Set.disjoint_left.mp (hContactUNonincident p j hn)
        (hBankPatchSource p (hFixedPatchSource p hpPiece)).1 hpOld
    let j' : {k : J // p.val ∈ (old k).val.image} := ⟨j,hIncident⟩
    obtain ⟨v,w,hv,hw,hmodel⟩ := hBankPatchModel p
    have hmarkPatch : Disjoint (bankPatchF p).source (M.cover.branch : Set S) :=
      (hContactUMarks p).mono_left (fun y hy => (hBankPatchSource p hy).1)
    obtain ⟨F0,hxF0,hF0x,hF0Patch,hF0Mark,hF0Old,hF0Line⟩ :=
      hPositiveRayAffineCrossing (old j) x hx.2 (bankPatchF p) (hFixedPatchSource p hpPiece)
        hmarkPatch (v j') (w j') (hv j') (hw j') (hmodel j')
        (chosenHeight p) (hChosenHeight p).1 (hFixedPatchHeight p x hpPiece)
    have hxOthers : x ∉ otherPieces p := hPatchOldPointNotOthers p j x hpPiece hx.2
    have hxK : x ∉ Kraw := by
      intro hk
      exact hJoinedPointNotCorner j x hx.2 (hJoinedK ▸ (show x ∈ range joinedF ∩ Kraw from ⟨hx.1,hk⟩))
    have hx0 : x ≠ joinedF 0 := by
      intro he
      have hc : x=B.firstCorner := he.trans hJoinedFirst
      exact hJoinedPointNotCorner j x hx.2 (Set.mem_insert_iff.mpr (Or.inl hc))
    have hx1 : x ≠ joinedF 1 := by
      intro he
      have hc : x=B.secondCorner := he.trans hJoinedSecond
      exact hJoinedPointNotCorner j x hx.2 (by simp [hc])
    exact actual_joined_carrier_local_axis_chart joinedF hJoinedEmbedded
      (range (fixedPatch p)) (otherPieces p) Kraw (M.cover.branch : Set S) (old j).val.image
      (hOtherPiecesCompact p).isClosed hKraw.isClosed (hJoinedCoverForPatch p)
      x hx.1 hxOthers hxK hx0 hx1 F0 hxF0 hF0x hF0Mark
      (fun y hy => hF0Line y (hFixedPatchHeight p y hy.1)) hF0Old
  exact ⟨joinedF,hJoinedEmbedded,hJoinedFirst,hJoinedSecond,hJoinedB,hJoinedFirstSide,
    hJoinedK,hJoinedMarks,hJoinedOldBudget,hJoinedWholeTraceCharts,
    joinedQ,hJoinedQEmbedded,hJoinedQBoundary,hJoinedQMarks,hJoinedQK⟩
end CurveComplex.HyperellipticModel
