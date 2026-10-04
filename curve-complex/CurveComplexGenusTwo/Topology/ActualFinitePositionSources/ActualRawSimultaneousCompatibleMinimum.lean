import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingSymmetry
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualSingleContactSlide
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualRawMutualFiniteTransverseFamily
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualMarkedCrossingTransport
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import CurveComplexGenusTwo.Topology.GeometricPosition.IntervalSubdivision
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualCountControlledProperCrosscutCandidate
import Mathlib.Data.Set.Card.Arithmetic
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteSurfaceReplacement
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedAffineCrossingDisk
import CurveComplexGenusTwo.Topology.GeometricPosition.ProperAffineCrosscut
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedEndpointSourceFanChart
import CurveComplexGenusTwo.Topology.Smoothing.JordanSectorCrosscutExtensionHeader
import CurveComplexGenusTwo.Topology.Smoothing.ConvexSectorChartHeader
import CurveComplexGenusTwo.Topology.Smoothing.JordanRegionIdentificationHeader
import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.Smoothing.PointedCrosscutHeader
import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
import CurveComplexGenusTwo.Topology.WeightedSurgery.SupportedEndpointRotation
import CurveComplexGenusTwo.Topology.Smoothing.FiniteActualStarRadialization
import Schoenflies.MatchedArc
import Schoenflies.BoundaryContinuity2
import CurveComplexGenusTwo.Topology.Smoothing.PointedPlaneIsotopyProof
import CurveComplexGenusTwo.Topology.ChartLift
import CurveComplexGenusTwo.Topology.Smoothing.ActualStarIntersection
import CurveComplexGenusTwo.Topology.Smoothing.ActualGermArcs
import CurveComplexGenusTwo.Topology.Smoothing.UniformActualGerms
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualFiniteContactNormalizationScaffold
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.GapMatchingTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.CornerGeometryTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualChartArcTools
import ActualRawCompatiblePairMarkedBigonSelector_DIRECT_IMPORT_RECOVERY_CANDIDATE
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.TripleContactLocalIsolation
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.TwoDirectionCountBridge
import CurveComplexGenusTwo.Topology.ActualNoTriplePosition.NoTriplePositionProof
import CurveComplexGenusTwo.Topology.ActualRoundedSideReplacement.ActualOriginalRoundedCompleteSupportCandidate4
import CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualCountControlledMutualFiniteTransversePosition

namespace CurveComplex.HyperellipticModel.ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

open Set Topology Metric Schoenflies
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
theorem actual_raw_simultaneous_compatible_minimum_family
(M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
(F : Finset (EssentialArcClass M)) :
  ∃ r : {v // v ∈ F} → EssentialMarkedArc M,
    (∀ v, vertex M (r v) = v.val) ∧
    (∀ v, (crossings M anchor (r v)).Finite) ∧
    (∀ v p, p ∈ crossings M anchor (r v) →
      CrossesInDisk M anchor (r v) p) ∧
    (∀ v w, v ≠ w → IsArcSimplex M {v.val,w.val} →
      Disjoint (arcInterior M (r v)) (arcInterior M (r w))) ∧
    (∀ v (b : EssentialMarkedArc M), vertex M b = v.val →
      (crossings M anchor b).Finite →
      (crossings M anchor (r v)).ncard ≤ (crossings M anchor b).ncard) := by
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
      ∃ δ H : ℝ, 0 < δ ∧ 0 < H ∧ ∀ h : ℝ, 0 < h → h < H →
        ∃ f : C(Interval,S), IsEmbedding f ∧
          range f=F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          f 0=F.symm (Plane.mk (-δ) h) ∧ f 1=F.symm (Plane.mk δ h) ∧
          range f ⊆ F.source ∧ Disjoint (range f) (M.cover.branch : Set S) ∧
          Disjoint (range f) side.val.image ∧ ∀ j,
            f 0 ∉ (old j).val.image ∧ f 1 ∉ (old j).val.image ∧
            (range f ∩ (old j).val.image).Finite ∧
            (range f ∩ (old j).val.image).ncard ≤ 1 := by
    obtain ⟨δ,H,hδ,hH,_,_,hpatch⟩ := CurveComplex.actual_uniform_radial_contact_patch a b ha hb η hη
    refine ⟨δ,H,hδ,hH,?_⟩
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
    refine ⟨f,hfi,hf,hf0,hf1,hsub,hmark.mono_left hsub,?_,?_⟩
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
  let I := {v // v ∈ F}
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨seed,hSeedClass,hSeedAnchor,hSeedMutual⟩ := actual_raw_mutual_finite_transverse_family M anchor F
  have hActualIndividualAnchorMinimum (v : I) :
      ∃ c : EssentialMarkedArc M, vertex M c=v.val ∧
        (crossings M anchor c).Finite ∧
        (∀ p ∈ crossings M anchor c, CrossesInDisk M anchor c p) ∧
        ∀ b : EssentialMarkedArc M, vertex M b=v.val → (crossings M anchor b).Finite →
          (crossings M anchor c).ncard ≤ (crossings M anchor b).ncard := by
    let P : ℕ → Prop := fun n => ∃ b : EssentialMarkedArc M,
      vertex M b=v.val ∧ (crossings M anchor b).Finite ∧ (crossings M anchor b).ncard=n
    have hP : ∃ n, P n := ⟨_,seed v,hSeedClass v,(hSeedAnchor v).1,rfl⟩
    obtain ⟨b,hb,hbf,hbn⟩ := Nat.find_spec hP
    obtain ⟨c,hcb,hcf,hct,hcount⟩ := actual_finite_contact_transverse_normalization M anchor b hbf
    have hcv : vertex M c=v.val := hcb.trans hb
    refine ⟨c,hcv,hcf,hct,?_⟩
    intro d hd hdf
    have hdmin : Nat.find hP ≤ (crossings M anchor d).ncard :=
      Nat.find_min' hP ⟨d,hd,hdf,rfl⟩
    exact hcount.trans (hbn ▸ hdmin)
  choose minimumArc hMinimumClass hMinimumFinite hMinimumTransverse hMinimumComparison
    using hActualIndividualAnchorMinimum
  let GeometricFamily : (I → EssentialMarkedArc M) → Prop := fun r =>
    (∀ v, vertex M (r v)=v.val) ∧
    (∀ v, (crossings M anchor (r v)).Finite ∧
      ∀ p ∈ crossings M anchor (r v), CrossesInDisk M anchor (r v) p) ∧
    ∀ v w, v ≠ w → (crossings M (r v) (r w)).Finite ∧
      ∀ p ∈ crossings M (r v) (r w), CrossesInDisk M (r v) (r w) p
  let anchorEnergy : (I → EssentialMarkedArc M) → ℕ := fun r =>
    ∑ v : I, (crossings M anchor (r v)).ncard
  let pairEnergy : (I → EssentialMarkedArc M) → ℕ := fun r =>
    ∑ v : I, ∑ w : I, if v=w then 0 else (crossings M (r v) (r w)).ncard
  have hActualLexicographicFiniteFamilyMinimum :
      ∃ r : I → EssentialMarkedArc M, GeometricFamily r ∧
        (∀ s, GeometricFamily s → anchorEnergy r ≤ anchorEnergy s) ∧
        ∀ s, GeometricFamily s → anchorEnergy s=anchorEnergy r → pairEnergy r ≤ pairEnergy s := by
    let P : ℕ → Prop := fun n => ∃ r, GeometricFamily r ∧ anchorEnergy r=n
    have hP : ∃ n, P n := ⟨_,seed,⟨hSeedClass,hSeedAnchor,hSeedMutual⟩,rfl⟩
    let Q : ℕ → Prop := fun n => ∃ r, GeometricFamily r ∧
      anchorEnergy r=Nat.find hP ∧ pairEnergy r=n
    have hQ : ∃ n, Q n := by
      obtain ⟨r,hr,ha⟩ := Nat.find_spec hP
      exact ⟨_,r,hr,ha,rfl⟩
    obtain ⟨r,hr,ha,hpair⟩ := Nat.find_spec hQ
    refine ⟨r,hr,?_,?_⟩
    · intro s hs
      rw [ha]
      exact Nat.find_min' hP ⟨s,hs,rfl⟩
    · intro s hs has
      rw [hpair]
      exact Nat.find_min' hQ ⟨s,hs,has.trans ha,rfl⟩
  have hActualAnchorMinimumPreservation
      (r : I → EssentialMarkedArc M)
      (hminimum : ∀ v b, vertex M b=v.val → (crossings M anchor b).Finite →
        (crossings M anchor (r v)).ncard ≤ (crossings M anchor b).ncard)
      (v : I) (c : EssentialMarkedArc M) (hc : vertex M c=v.val)
      (hcf : (crossings M anchor c).Finite)
      (hcost : (crossings M anchor c).ncard ≤ (crossings M anchor (r v)).ncard) :
      (crossings M anchor c).ncard=(crossings M anchor (r v)).ncard ∧
      ∀ b, vertex M b=v.val → (crossings M anchor b).Finite →
        (crossings M anchor c).ncard ≤ (crossings M anchor b).ncard := by
    refine ⟨Nat.le_antisymm hcost (hminimum v c hc hcf),?_⟩
    intro b hb hbf
    exact hcost.trans (hminimum v b hb hbf)
  have hActualPairEnergySplit (r : I → EssentialMarkedArc M) (v : I) :
      pairEnergy r=
        (∑ i ∈ Finset.univ.erase v, ∑ j ∈ Finset.univ.erase v,
          if i=j then 0 else (crossings M (r i) (r j)).ncard) +
        2*(∑ j ∈ Finset.univ.erase v, (crossings M (r v) (r j)).ncard) := by
    let C : I → I → ℕ := fun i j => if i=j then 0 else (crossings M (r i) (r j)).ncard
    have hSym (i j : I) : C i j=C j i := by
      by_cases hij : i=j
      · subst j; rfl
      · simp only [C,if_neg hij,if_neg (Ne.symm hij)]
        change (arcInterior M (r i) ∩ arcInterior M (r j)).ncard=
          (arcInterior M (r j) ∩ arcInterior M (r i)).ncard
        rw [Set.inter_comm]
    have hRow (i : I) : (∑ j : I, C i j)=(∑ j ∈ Finset.univ.erase v, C i j)+C i v :=
      (Finset.sum_erase_add Finset.univ (C i) (Finset.mem_univ v)).symm
    have hAll : (∑ i : I, ∑ j : I, C i j)=
        (∑ i ∈ Finset.univ.erase v, ∑ j : I, C i j)+(∑ j : I, C v j) :=
      (Finset.sum_erase_add Finset.univ (fun i => ∑ j : I, C i j) (Finset.mem_univ v)).symm
    have hV : (∑ j : I, C v j)=∑ j ∈ Finset.univ.erase v, C v j := by
      rw [hRow]
      simp [C]
    have hIncoming : (∑ i ∈ Finset.univ.erase v, C i v)=∑ i ∈ Finset.univ.erase v, C v i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hSym i v
    have hVR : (∑ j ∈ Finset.univ.erase v, C v j)=
        ∑ j ∈ Finset.univ.erase v, (crossings M (r v) (r j)).ncard := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [C,if_neg (Ne.symm (Finset.mem_erase.mp hj).1)]
    change (∑ i : I, ∑ j : I, C i j)=_
    rw [hAll,hV]
    simp_rw [hRow]
    rw [Finset.sum_add_distrib,hIncoming,hVR]
    dsimp [C]
    ring
  have hActualPairEnergyStrictSubstitution
      (r : I → EssentialMarkedArc M) (v : I) (c : EssentialMarkedArc M)
      (hrow : (∑ j ∈ Finset.univ.erase v, (crossings M c (r j)).ncard) <
        ∑ j ∈ Finset.univ.erase v, (crossings M (r v) (r j)).ncard) :
      pairEnergy (fun i => if i=v then c else r i) < pairEnergy r := by
    let r' : I → EssentialMarkedArc M := fun i => if i=v then c else r i
    have hBulk : (∑ i ∈ Finset.univ.erase v, ∑ j ∈ Finset.univ.erase v,
        if i=j then 0 else (crossings M (r' i) (r' j)).ncard)=
        ∑ i ∈ Finset.univ.erase v, ∑ j ∈ Finset.univ.erase v,
          if i=j then 0 else (crossings M (r i) (r j)).ncard := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp [r',(Finset.mem_erase.mp hi).1,(Finset.mem_erase.mp hj).1]
    have hNewRow : (∑ j ∈ Finset.univ.erase v, (crossings M (r' v) (r' j)).ncard)=
        ∑ j ∈ Finset.univ.erase v, (crossings M c (r j)).ncard := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [r',(Finset.mem_erase.mp hj).1]
    change pairEnergy r' < pairEnergy r
    rw [hActualPairEnergySplit r' v,hActualPairEnergySplit r v,hBulk,hNewRow]
    omega
  have hActualAnchorEnergySelectedComparison
      (r : I → EssentialMarkedArc M)
      (hleast : ∀ s, GeometricFamily s → anchorEnergy r ≤ anchorEnergy s)
      (v : I) (c : EssentialMarkedArc M)
      (hnew : GeometricFamily (fun i => if i=v then c else r i)) :
      (crossings M anchor (r v)).ncard ≤ (crossings M anchor c).ncard := by
    have hle := hleast (fun i => if i=v then c else r i) hnew
    let S : ℕ := ∑ i ∈ Finset.univ.erase v, (crossings M anchor (r i)).ncard
    have hOld : anchorEnergy r=S+(crossings M anchor (r v)).ncard :=
      (Finset.sum_erase_add Finset.univ (fun i => (crossings M anchor (r i)).ncard) (Finset.mem_univ v)).symm
    have hNew : anchorEnergy (fun i => if i=v then c else r i)=S+(crossings M anchor c).ncard := by
      change (∑ i : I, (crossings M anchor (if i=v then c else r i)).ncard)=_
      rw [← Finset.sum_erase_add Finset.univ (fun i => (crossings M anchor (if i=v then c else r i)).ncard) (Finset.mem_univ v)]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        simp [(Finset.mem_erase.mp hi).1]
      · simp
    rw [hOld,hNew] at hle
    omega
  let AnchorMinimumFamily : (I → EssentialMarkedArc M) → Prop := fun r =>
    ∀ v b, vertex M b=v.val → (crossings M anchor b).Finite →
      (crossings M anchor (r v)).ncard ≤ (crossings M anchor b).ncard
  have hActualMinimumCoherenceFromCountPreservingPosition
      (q : I → EssentialMarkedArc M)
      (hcounts : ∀ v, (crossings M anchor (q v)).ncard ≤
        (crossings M anchor (minimumArc v)).ncard) : AnchorMinimumFamily q := by
    intro v b hb hbf
    exact (hcounts v).trans (hMinimumComparison v b hb hbf)
  have hActualMinimumFamilyPairEnergyChoice
      (hfeasible : ∃ q : I → EssentialMarkedArc M, GeometricFamily q ∧ AnchorMinimumFamily q) :
      ∃ r : I → EssentialMarkedArc M, GeometricFamily r ∧ AnchorMinimumFamily r ∧
        ∀ q, GeometricFamily q → AnchorMinimumFamily q → pairEnergy r ≤ pairEnergy q := by
    let P : ℕ → Prop := fun n => ∃ r, GeometricFamily r ∧ AnchorMinimumFamily r ∧ pairEnergy r=n
    have hP : ∃ n, P n := by
      obtain ⟨q,hq,hqm⟩ := hfeasible
      exact ⟨_,q,hq,hqm,rfl⟩
    obtain ⟨r,hr,hm,he⟩ := Nat.find_spec hP
    refine ⟨r,hr,hm,?_⟩
    intro q hq hqm
    rw [he]
    exact Nat.find_min' hP ⟨q,hq,hqm,rfl⟩
  have hActualMinimumEnergyRejectsStrictIncidentDrop
      (r : I → EssentialMarkedArc M)
      (hleast : ∀ q, GeometricFamily q → AnchorMinimumFamily q → pairEnergy r ≤ pairEnergy q)
      (v : I) (c : EssentialMarkedArc M)
      (hnew : GeometricFamily (fun i => if i=v then c else r i))
      (hnewMinimum : AnchorMinimumFamily (fun i => if i=v then c else r i)) :
      ¬ (∑ j ∈ Finset.univ.erase v, (crossings M c (r j)).ncard) <
        ∑ j ∈ Finset.univ.erase v, (crossings M (r v) (r j)).ncard := by
    intro hdrop
    exact (not_lt_of_ge (hleast _ hnew hnewMinimum))
      (hActualPairEnergyStrictSubstitution r v c hdrop)
  have hActualReplacementPreservesGeometricFamily
      (r : I → EssentialMarkedArc M) (hr : GeometricFamily r)
      (v : I) (c : EssentialMarkedArc M) (hc : vertex M c=v.val)
      (ha : (crossings M anchor c).Finite ∧
        ∀ p ∈ crossings M anchor c, CrossesInDisk M anchor c p)
      (hold : ∀ j, j≠v → (crossings M c (r j)).Finite ∧
        ∀ p ∈ crossings M c (r j), CrossesInDisk M c (r j) p) :
      GeometricFamily (fun i => if i=v then c else r i) := by
    refine ⟨?_,?_,?_⟩
    · intro i
      by_cases hi : i=v
      · subst i; simpa using hc
      · simpa [hi] using hr.1 i
    · intro i
      by_cases hi : i=v
      · subst i; simpa using ha
      · simpa [hi] using hr.2.1 i
    · intro i j hij
      by_cases hi : i=v
      · subst i
        simpa [Ne.symm hij] using hold j (Ne.symm hij)
      · by_cases hj : j=v
        · subst j
          obtain ⟨hf,ht⟩ := hold i hi
          have he : crossings M (r i) c=crossings M c (r i) := Set.inter_comm _ _
          refine ⟨?_,?_⟩
          · simpa [hi,he] using hf
          · intro p hp
            have hp' : p ∈ crossings M c (r i) := by simpa [hi,he] using hp
            simpa [hi] using actual_marked_crossesInDisk_symm M c (r i) p (ht p hp')
        · simpa [hi,hj] using hr.2.2 i j hij
  have hActualReplacementPreservesEveryAnchorMinimum
      (r : I → EssentialMarkedArc M) (hm : AnchorMinimumFamily r)
      (v : I) (c : EssentialMarkedArc M)
      (hcost : (crossings M anchor c).ncard ≤ (crossings M anchor (r v)).ncard) :
      AnchorMinimumFamily (fun i => if i=v then c else r i) := by
    intro i b hb hbf
    by_cases hi : i=v
    · subst i
      simpa using hcost.trans (hm v b hb hbf)
    · simpa [hi] using hm i b hb hbf
  have hActualControlledReplacementCannotStrictlyDropIncidentCost
      (r : I → EssentialMarkedArc M) (hr : GeometricFamily r)
      (hm : AnchorMinimumFamily r)
      (hleast : ∀ q, GeometricFamily q → AnchorMinimumFamily q → pairEnergy r ≤ pairEnergy q)
      (v : I) (c : EssentialMarkedArc M) (hc : vertex M c=v.val)
      (ha : (crossings M anchor c).Finite ∧
        ∀ p ∈ crossings M anchor c, CrossesInDisk M anchor c p)
      (hold : ∀ j, j≠v → (crossings M c (r j)).Finite ∧
        ∀ p ∈ crossings M c (r j), CrossesInDisk M c (r j) p)
      (hcost : (crossings M anchor c).ncard ≤ (crossings M anchor (r v)).ncard) :
      ¬ (∑ j ∈ Finset.univ.erase v, (crossings M c (r j)).ncard) <
        ∑ j ∈ Finset.univ.erase v, (crossings M (r v) (r j)).ncard := by
    exact hActualMinimumEnergyRejectsStrictIncidentDrop r hleast v c
      (hActualReplacementPreservesGeometricFamily r hr v c hc ha hold)
      (hActualReplacementPreservesEveryAnchorMinimum r hm v c hcost)
  obtain ⟨q,hqclass,hqanchor,hqmutual⟩ :=
    CurveComplex.HyperellipticModel.actual_count_controlled_mutual_finite_transverse_position
      M anchor minimumArc hMinimumFinite hMinimumTransverse
  have hqGeometric : GeometricFamily q :=
    ⟨fun v => (hqclass v).trans (hMinimumClass v),
      fun v => ⟨(hqanchor v).1,(hqanchor v).2.1⟩,hqmutual⟩
  have hqMinimum : AnchorMinimumFamily q :=
    hActualMinimumCoherenceFromCountPreservingPosition q (fun v => (hqanchor v).2.2)
  obtain ⟨r,hr,hm,hleast⟩ := hActualMinimumFamilyPairEnergyChoice ⟨q,hqGeometric,hqMinimum⟩
  have hNoTriplePositionPreservesMinimumChoice
      (s : I → EssentialMarkedArc M)
      (hsClass : ∀ i, vertex M (s i) = vertex M (r i))
      (hsAnchor : ∀ i, (crossings M anchor (s i)).Finite ∧
        (∀ p ∈ crossings M anchor (s i), CrossesInDisk M anchor (s i) p) ∧
        (crossings M anchor (s i)).ncard =
          (crossings M anchor (r i)).ncard)
      (hsPair : ∀ i j, i ≠ j → (crossings M (s i) (s j)).Finite ∧
        (∀ p ∈ crossings M (s i) (s j), CrossesInDisk M (s i) (s j) p) ∧
        (crossings M (s i) (s j)).ncard =
          (crossings M (r i) (r j)).ncard) :
      GeometricFamily s ∧ AnchorMinimumFamily s ∧
        (∀ t, GeometricFamily t → AnchorMinimumFamily t → pairEnergy s ≤ pairEnergy t) := by
    have hsGeometric : GeometricFamily s := by
      refine ⟨?_,?_,?_⟩
      · intro i; exact (hsClass i).trans (hr.1 i)
      · intro i; exact ⟨(hsAnchor i).1,(hsAnchor i).2.1⟩
      · intro i j hij; exact ⟨(hsPair i j hij).1,(hsPair i j hij).2.1⟩
    have hsMinimum : AnchorMinimumFamily s := by
      intro i b hb hbf
      exact (hsAnchor i).2.2.le.trans (hm i b hb hbf)
    have hEnergy : pairEnergy s = pairEnergy r := by
      dsimp [pairEnergy]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · simp [hij]
      · simpa only [if_neg hij] using (hsPair i j hij).2.2
    exact ⟨hsGeometric,hsMinimum,fun t ht htm => hEnergy ▸ hleast t ht htm⟩
  obtain ⟨s,hsClass,hsAnchor,hsPair,hsTriple,hsAnchorTriple⟩ :=
    actual_raw_count_preserving_no_triple_family M anchor r hr.2.1 hr.2.2
  obtain ⟨hsGeo,hsMin,hsLeast⟩ :=
    hNoTriplePositionPreservesMinimumChoice s hsClass hsAnchor hsPair
  let r := s
  have hr : GeometricFamily r := hsGeo
  have hm : AnchorMinimumFamily r := hsMin
  have hleast : ∀ q, GeometricFamily q → AnchorMinimumFamily q →
      pairEnergy r ≤ pairEnergy q := hsLeast
  refine ⟨r,hr.1,(fun v => (hr.2.1 v).1),(fun v p hp => (hr.2.1 v).2 p hp),?_,hm⟩
  -- Remaining actual compatible-pair cancellation and weighted rounded-side
  -- replacement must contradict the computed least pair energy, while
  -- preserving the literal anchor minima. No empty arbitrary-family disk assumed.
  intro v w hvw hcompatible
  by_cases hcontact : (crossings M (r v) (r w)).Nonempty
  · have hclasses : vertex M (r v)≠vertex M (r w) := by
      rw [hr.1 v,hr.1 w]
      exact fun h => hvw (Subtype.ext h)
    have hfinite := (hr.2.2 v w hvw).1
    have htransverse := (hr.2.2 v w hvw).2
    have hcompatible' : IsArcSimplex M {vertex M (r v), vertex M (r w)} := by
      simpa [hr.1 v, hr.1 w] using hcompatible
    obtain ⟨B,hBfree,hhit⟩ :=
      CurveComplex.HyperellipticModel.actual_raw_compatible_pair_marked_bigon_selector
        M (r v) (r w) hclasses hcompatible' hfinite htransverse hcontact
    have hcornerCross (p : S) (hp : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
        (hpm : p ∉ M.cover.branch) : p ∈ crossings M (r v) (r w) := by
      have hp' : p = B.firstCorner ∨ p = B.secondCorner := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp
      have hpa : p ∈ (r v).val.image := by
        rcases hp' with h | h
        · rw [h]
          exact B.first_on_curve ⟨0, B.first_zero⟩
        · rw [h]
          exact B.first_on_curve ⟨1, B.first_one⟩
      have hpb : p ∈ (r w).val.image := by
        rcases hp' with h | h
        · rw [h]
          exact B.second_on_curve ⟨0, B.second_zero⟩
        · rw [h]
          exact B.second_on_curve ⟨1, B.second_one⟩
      exact ⟨⟨hpa,hpm⟩,⟨hpb,hpm⟩⟩
    have hselectedNotCornerAvoidance :
        ¬ (∀ p, p ∈ ({B.firstCorner,B.secondCorner} : Set S) →
          p ∉ M.cover.branch → p ∉ (r v).val.image) := by
      intro havoid
      rcases hhit with hfirst | hsecond
      · exact havoid B.firstCorner (by simp) hfirst.1.2 hfirst.1.1
      · exact havoid B.secondCorner (by simp) hsecond.1.2 hsecond.1.1
    let J := {j : I // j ≠ v ∧ j ≠ w}
    let old : Option J → EssentialMarkedArc M := fun j =>
      match j with
      | none => anchor
      | some j => r j.val
    have hOldPair : ∀ i j : Option J, i ≠ j →
        (crossings M (old i) (old j)).Finite ∧
        ∀ p ∈ crossings M (old i) (old j), CrossesInDisk M (old i) (old j) p := by
      intro i j hij
      cases i with
      | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some j => exact hr.2.1 j.val
      | some i =>
        cases j with
        | none =>
          have h := hr.2.1 i.val
          have he : crossings M (r i.val) anchor = crossings M anchor (r i.val) :=
            Set.inter_comm _ _
          refine ⟨he ▸ h.1, ?_⟩
          intro p hp
          have hp' : p ∈ crossings M anchor (r i.val) := he ▸ hp
          exact actual_marked_crossesInDisk_symm M anchor (r i.val) p (h.2 p hp')
        | some j =>
          have hne : i.val ≠ j.val := by
            intro he
            exact hij (congrArg Option.some (Subtype.ext he))
          exact hr.2.2 i.val j.val hne
    have hOldA : ∀ j : Option J,
        (crossings M (r v) (old j)).Finite ∧
        ∀ p ∈ crossings M (r v) (old j), CrossesInDisk M (r v) (old j) p := by
      intro j
      cases j with
      | none =>
        have h := hr.2.1 v
        have he : crossings M (r v) anchor = crossings M anchor (r v) :=
          Set.inter_comm _ _
        refine ⟨he ▸ h.1, ?_⟩
        intro p hp
        have hp' : p ∈ crossings M anchor (r v) := he ▸ hp
        exact actual_marked_crossesInDisk_symm M anchor (r v) p (h.2 p hp')
      | some j => exact hr.2.2 v j.val j.property.1.symm
    have hOldB : ∀ j : Option J,
        (crossings M (r w) (old j)).Finite ∧
        ∀ p ∈ crossings M (r w) (old j), CrossesInDisk M (r w) (old j) p := by
      intro j
      cases j with
      | none =>
        have h := hr.2.1 w
        have he : crossings M (r w) anchor = crossings M anchor (r w) :=
          Set.inter_comm _ _
        refine ⟨he ▸ h.1, ?_⟩
        intro p hp
        have hp' : p ∈ crossings M anchor (r w) := he ▸ hp
        exact actual_marked_crossesInDisk_symm M anchor (r w) p (h.2 p hp')
      | some j => exact hr.2.2 w j.val j.property.2.symm
    have hCornersFromNoTriple
        (hTriple : ∀ i j k : I, i ≠ j → i ≠ k → j ≠ k →
          Disjoint (crossings M (r i) (r j)) (arcInterior M (r k)))
        (hAnchor : ∀ i j : I, i ≠ j →
          Disjoint (crossings M (r i) (r j)) (arcInterior M anchor)) :
        ∀ j : Option J, ∀ p,
          p ∈ ({B.firstCorner,B.secondCorner} : Set S) →
          p ∉ M.cover.branch → p ∉ (old j).val.image := by
      intro j p hpCorner hpmark hpOld
      have hpCross := hcornerCross p hpCorner hpmark
      cases j with
      | none =>
        exact Set.disjoint_left.mp (hAnchor v w hvw) hpCross ⟨hpOld,hpmark⟩
      | some j =>
        exact Set.disjoint_left.mp
          (hTriple v w j.val hvw j.property.1.symm j.property.2.symm)
          hpCross ⟨hpOld,hpmark⟩
    let Bswap : ActualMarkedTwoSideDisk M (r w) (r v) := {
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
    have hBswapFree : Disjoint Bswap.openInterior
        ((r w).val.image ∪ (r v).val.image) := by
      simpa only [Bswap, ActualMarkedTwoSideDisk.openInterior, Set.union_comm]
        using hBfree
    have hBswapHit : Bswap.firstCorner ∈ crossings M (r w) (r v) ∨
        Bswap.secondCorner ∈ crossings M (r w) (r v) := by
      simpa only [Bswap, crossings, Set.inter_comm] using hhit
    have hBswapCorners (j : Option J) (p : S)
        (hTriple : ∀ i j k : I, i ≠ j → i ≠ k → j ≠ k →
          Disjoint (crossings M (r i) (r j)) (arcInterior M (r k)))
        (hAnchor : ∀ i j : I, i ≠ j →
          Disjoint (crossings M (r i) (r j)) (arcInterior M anchor))
        (hpCorner : p ∈ ({Bswap.firstCorner,Bswap.secondCorner} : Set S))
        (hpmark : p ∉ M.cover.branch) :
        p ∉ (old j).val.image := by
      exact hCornersFromNoTriple hTriple hAnchor j p
        (by simpa only [Bswap] using hpCorner) hpmark
    have hForwardRow :
        (∑ j ∈ Finset.univ.erase v, (crossings M (r v) (r j)).ncard) =
          (crossings M (r v) (r w)).ncard +
          ∑ j ∈ (Finset.univ.erase v).erase w,
            (crossings M (r v) (r j)).ncard := by
      exact incident_row_split_at_selected_pair v w hvw _
    have hBackwardRow :
        (∑ j ∈ Finset.univ.erase w, (crossings M (r w) (r j)).ncard) =
          (crossings M (r w) (r v)).ncard +
          ∑ j ∈ (Finset.univ.erase w).erase v,
            (crossings M (r w) (r j)).ncard := by
      exact incident_row_split_at_selected_pair w v hvw.symm _
    have hConditionalTwoOrientationCountDrop
        (ca cb : EssentialMarkedArc M)
        (hcaClass : vertex M ca = v.val)
        (hcbClass : vertex M cb = w.val)
        (hcaPair : (crossings M ca (r w)).ncard <
          (crossings M (r v) (r w)).ncard)
        (hcbPair : (crossings M cb (r v)).ncard <
          (crossings M (r v) (r w)).ncard)
        (hcaBound : ∀ j : Option J,
          (crossings M ca (old j)).Finite ∧
          (crossings M ca (old j)).ncard ≤
            (crossings M (r v) (old j) \ Set.range B.firstSide).ncard +
            (crossings M (r w) (old j) ∩ Set.range B.secondSide).ncard)
        (hcbBound : ∀ j : Option J,
          (crossings M cb (old j)).Finite ∧
          (crossings M cb (old j)).ncard ≤
            (crossings M (r w) (old j) \ Set.range B.secondSide).ncard +
            (crossings M (r v) (old j) ∩ Set.range B.firstSide).ncard) :
        (crossings M anchor ca).ncard ≤ (crossings M anchor (r v)).ncard ∧
        (crossings M anchor cb).ncard ≤ (crossings M anchor (r w)).ncard ∧
        ((∑ j ∈ Finset.univ.erase v, (crossings M ca (r j)).ncard) <
            ∑ j ∈ Finset.univ.erase v, (crossings M (r v) (r j)).ncard ∨
        (∑ j ∈ Finset.univ.erase w, (crossings M cb (r j)).ncard) <
            ∑ j ∈ Finset.univ.erase w, (crossings M (r w) (r j)).ncard) := by
      have hcaAnchorFinite : (crossings M anchor ca).Finite := by
        have he : crossings M anchor ca = crossings M ca anchor := Set.inter_comm _ _
        exact he ▸ (hcaBound none).1
      have hcbAnchorFinite : (crossings M anchor cb).Finite := by
        have he : crossings M anchor cb = crossings M cb anchor := Set.inter_comm _ _
        exact he ▸ (hcbBound none).1
      have hcaAnchorMin : (crossings M (r v) anchor).ncard ≤
          (crossings M ca anchor).ncard := by
        have h := hm v ca hcaClass hcaAnchorFinite
        simpa only [crossings, arcInterior, Set.inter_comm] using h
      have hcbAnchorMin : (crossings M (r w) anchor).ncard ≤
          (crossings M cb anchor).ncard := by
        have h := hm w cb hcbClass hcbAnchorFinite
        simpa only [crossings, arcInterior, Set.inter_comm] using h
      have haAnchorPartition := Set.ncard_inter_add_ncard_sdiff_eq_ncard
        (crossings M (r v) anchor) (Set.range B.firstSide) (hOldA none).1
      have hbAnchorPartition := Set.ncard_inter_add_ncard_sdiff_eq_ncard
        (crossings M (r w) anchor) (Set.range B.secondSide) (hOldB none).1
      have hcaAnchorBudget : (crossings M ca anchor).ncard ≤
          (crossings M (r v) anchor).ncard := by
        have ha := (hcaBound none).2
        have hb := (hcbBound none).2
        dsimp [old] at ha hb
        omega
      have hcbAnchorBudget : (crossings M cb anchor).ncard ≤
          (crossings M (r w) anchor).ncard := by
        have ha := (hcaBound none).2
        have hb := (hcbBound none).2
        dsimp [old] at ha hb
        omega
      have hcaAnchorCostLe : (crossings M anchor ca).ncard ≤
          (crossings M anchor (r v)).ncard := by
        simpa only [crossings, arcInterior, Set.inter_comm] using hcaAnchorBudget
      have hcbAnchorCostLe : (crossings M anchor cb).ncard ≤
          (crossings M anchor (r w)).ncard := by
        simpa only [crossings, arcInterior, Set.inter_comm] using hcbAnchorBudget
      have hDrop := two_direction_finite_family_count_drop
        (none : Option J)
        (fun j => crossings M (r v) (old j))
        (fun j => crossings M (r w) (old j))
        (fun j => crossings M ca (old j))
        (fun j => crossings M cb (old j))
        (fun _ => Set.range B.firstSide)
        (fun _ => Set.range B.secondSide)
        (fun j => (hOldA j).1) (fun j => (hOldB j).1)
        (fun j => (hcaBound j).2) (fun j => (hcbBound j).2)
        hcaAnchorMin hcbAnchorMin _ _ _ hcaPair (by
          simpa only [crossings, arcInterior, Set.inter_comm] using hcbPair)
      have hcaThird :
          (∑ j ∈ (Finset.univ : Finset (Option J)).erase none,
            (crossings M ca (old j)).ncard) =
          ∑ j : J, (crossings M ca (r j.val)).ncard := by
        rw [sum_option_erase_none]
      have hcbThird :
          (∑ j ∈ (Finset.univ : Finset (Option J)).erase none,
            (crossings M cb (old j)).ncard) =
          ∑ j : J, (crossings M cb (r j.val)).ncard := by
        rw [sum_option_erase_none]
      have haThird :
          (∑ j ∈ (Finset.univ : Finset (Option J)).erase none,
            (crossings M (r v) (old j)).ncard) =
          ∑ j : J, (crossings M (r v) (r j.val)).ncard := by
        rw [sum_option_erase_none]
      have hbThird :
          (∑ j ∈ (Finset.univ : Finset (Option J)).erase none,
            (crossings M (r w) (old j)).ncard) =
          ∑ j : J, (crossings M (r w) (r j.val)).ncard := by
        rw [sum_option_erase_none]
      refine ⟨hcaAnchorCostLe,hcbAnchorCostLe,?_⟩
      rcases hDrop with hDrop | hDrop
      · left
        rw [hcaThird, haThird] at hDrop
        have hcaRow := incident_row_split_at_selected_pair v w hvw
          (fun j => (crossings M ca (r j)).ncard)
        rw [sum_except_two_eq_sum_remaining_subtype v w] at hcaRow
        have haRow := hForwardRow
        rw [sum_except_two_eq_sum_remaining_subtype v w] at haRow
        rw [hcaRow, haRow]
        simpa only [Nat.add_comm] using hDrop
      · right
        rw [hcbThird, hbThird] at hDrop
        have hEraseComm :
            ((Finset.univ : Finset I).erase w).erase v =
              ((Finset.univ : Finset I).erase v).erase w := by
          ext j
          simp only [Finset.mem_erase]
          tauto
        have hcbRow := incident_row_split_at_selected_pair w v hvw.symm
          (fun j => (crossings M cb (r j)).ncard)
        rw [hEraseComm, sum_except_two_eq_sum_remaining_subtype v w] at hcbRow
        have hbRow := hBackwardRow
        rw [hEraseComm, sum_except_two_eq_sum_remaining_subtype v w] at hbRow
        rw [hcbRow, hbRow]
        simpa only [crossings, arcInterior, Set.inter_comm, Nat.add_comm] using hDrop
    have hConditionalRoundedOutputsContradictMinimality
        (ca cb : EssentialMarkedArc M)
        (hcaClass : vertex M ca = v.val)
        (hcbClass : vertex M cb = w.val)
        (hcaPair : (crossings M ca (r w)).Finite ∧
          (crossings M ca (r w)).ncard < (crossings M (r v) (r w)).ncard ∧
          ∀ p ∈ crossings M ca (r w), CrossesInDisk M ca (r w) p)
        (hcbPair : (crossings M cb (r v)).Finite ∧
          (crossings M cb (r v)).ncard < (crossings M (r v) (r w)).ncard ∧
          ∀ p ∈ crossings M cb (r v), CrossesInDisk M cb (r v) p)
        (hcaOld : ∀ j : Option J, (crossings M ca (old j)).Finite ∧
          (∀ p ∈ crossings M ca (old j), CrossesInDisk M ca (old j) p) ∧
          (crossings M ca (old j)).ncard ≤
            (crossings M (r v) (old j) \ Set.range B.firstSide).ncard +
            (crossings M (r w) (old j) ∩ Set.range B.secondSide).ncard)
        (hcbOld : ∀ j : Option J, (crossings M cb (old j)).Finite ∧
          (∀ p ∈ crossings M cb (old j), CrossesInDisk M cb (old j) p) ∧
          (crossings M cb (old j)).ncard ≤
            (crossings M (r w) (old j) \ Set.range B.secondSide).ncard +
            (crossings M (r v) (old j) ∩ Set.range B.firstSide).ncard) : False := by
      obtain ⟨hcaCost,hcbCost,hdrop⟩ :=
        hConditionalTwoOrientationCountDrop ca cb hcaClass hcbClass
          hcaPair.2.1 hcbPair.2.1
          (fun j => ⟨(hcaOld j).1,(hcaOld j).2.2⟩)
          (fun j => ⟨(hcbOld j).1,(hcbOld j).2.2⟩)
      have hcaAnchor : (crossings M anchor ca).Finite ∧
          ∀ p ∈ crossings M anchor ca, CrossesInDisk M anchor ca p := by
        have he : crossings M anchor ca = crossings M ca anchor := Set.inter_comm _ _
        refine ⟨he ▸ (hcaOld none).1,?_⟩
        intro p hp
        exact actual_marked_crossesInDisk_symm M ca anchor p
          ((hcaOld none).2.1 p (he ▸ hp))
      have hcbAnchor : (crossings M anchor cb).Finite ∧
          ∀ p ∈ crossings M anchor cb, CrossesInDisk M anchor cb p := by
        have he : crossings M anchor cb = crossings M cb anchor := Set.inter_comm _ _
        refine ⟨he ▸ (hcbOld none).1,?_⟩
        intro p hp
        exact actual_marked_crossesInDisk_symm M cb anchor p
          ((hcbOld none).2.1 p (he ▸ hp))
      have hcaContacts : ∀ j, j ≠ v → (crossings M ca (r j)).Finite ∧
          ∀ p ∈ crossings M ca (r j), CrossesInDisk M ca (r j) p := by
        intro j hjv
        by_cases hjw : j = w
        · subst j; exact ⟨hcaPair.1,hcaPair.2.2⟩
        · exact ⟨(hcaOld (some ⟨j,⟨hjv,hjw⟩⟩)).1,
            (hcaOld (some ⟨j,⟨hjv,hjw⟩⟩)).2.1⟩
      have hcbContacts : ∀ j, j ≠ w → (crossings M cb (r j)).Finite ∧
          ∀ p ∈ crossings M cb (r j), CrossesInDisk M cb (r j) p := by
        intro j hjw
        by_cases hjv : j = v
        · subst j; exact ⟨hcbPair.1,hcbPair.2.2⟩
        · exact ⟨(hcbOld (some ⟨j,⟨hjv,hjw⟩⟩)).1,
            (hcbOld (some ⟨j,⟨hjv,hjw⟩⟩)).2.1⟩
      rcases hdrop with hdrop | hdrop
      · exact (hActualControlledReplacementCannotStrictlyDropIncidentCost
          r hr hm hleast v ca hcaClass hcaAnchor hcaContacts hcaCost) hdrop
      · exact (hActualControlledReplacementCannotStrictlyDropIncidentCost
          r hr hm hleast w cb hcbClass hcbAnchor hcbContacts hcbCost) hdrop
    have hthirdLocalIsolation (j : I) (hvj : v ≠ j) (hwj : w ≠ j)
        (p : S) :
        ∃ U : Set S, IsOpen U ∧ p ∈ U ∧
          (U ∩ (r v).val.image ∩ (r w).val.image ⊆ {p}) ∧
          (U ∩ (r v).val.image ∩ (r j).val.image ⊆ {p}) ∧
          (U ∩ (r w).val.image ∩ (r j).val.image ⊆ {p}) := by
      letI : T2Space S := M.sphere.symm.t2Space
      have hAB : ((r v).val.image ∩ (r w).val.image).Finite := by
        exact ((hfinite.union (M.cover.branch.finite_toSet)).subset (by
          intro x hx
          by_cases hm : x ∈ M.cover.branch
          · exact Or.inr hm
          · exact Or.inl ⟨⟨hx.1,hm⟩,⟨hx.2,hm⟩⟩))
      have hAC : ((r v).val.image ∩ (r j).val.image).Finite := by
        exact (((hr.2.2 v j hvj).1.union M.cover.branch.finite_toSet).subset (by
          intro x hx
          by_cases hm : x ∈ M.cover.branch
          · exact Or.inr hm
          · exact Or.inl ⟨⟨hx.1,hm⟩,⟨hx.2,hm⟩⟩))
      have hBC : ((r w).val.image ∩ (r j).val.image).Finite := by
        exact (((hr.2.2 w j hwj).1.union M.cover.branch.finite_toSet).subset (by
          intro x hx
          by_cases hm : x ∈ M.cover.branch
          · exact Or.inr hm
          · exact Or.inl ⟨⟨hx.1,hm⟩,⟨hx.2,hm⟩⟩))
      exact finite_three_trace_contact_isolation _ _ _ hAB hAC hBC p
    have hcorners := hCornersFromNoTriple hsTriple hsAnchorTriple
    have hswapcorners : ∀ j : Option J, ∀ p,
        p ∈ ({Bswap.firstCorner,Bswap.secondCorner} : Set S) →
        p ∉ M.cover.branch → p ∉ (old j).val.image := by
      intro j p hp hpmark
      exact hBswapCorners j p hsTriple hsAnchorTriple hp hpmark
    obtain ⟨ca,hcaClass,hcaFinite,hcaDrop,hcaTransverse,hcaOld⟩ :=
      CurveComplex.HyperellipticModel.actual_marked_rounded_side_replacement
        M old (r v) (r w) hOldPair hfinite htransverse hOldA hOldB
        B hBfree hhit hcorners
    have hcaPair := And.intro hcaFinite (And.intro hcaDrop hcaTransverse)
    have hswapFinite : (crossings M (r w) (r v)).Finite := by
      simpa only [crossings, arcInterior, Set.inter_comm] using hfinite
    have hswapTransverse : ∀ p ∈ crossings M (r w) (r v),
        CrossesInDisk M (r w) (r v) p := by
      intro p hp
      apply actual_marked_crossesInDisk_symm M (r v) (r w) p
      apply htransverse p
      simpa only [crossings, arcInterior, Set.inter_comm] using hp
    obtain ⟨cb,hcbClass,hcbFinite,hcbDrop,hcbTransverse,hcbOld⟩ :=
      CurveComplex.HyperellipticModel.actual_marked_rounded_side_replacement
        M old (r w) (r v) hOldPair hswapFinite hswapTransverse hOldB hOldA
        Bswap hBswapFree hBswapHit hswapcorners
    have hcbPair := And.intro hcbFinite (And.intro hcbDrop hcbTransverse)
    exfalso
    apply hConditionalRoundedOutputsContradictMinimality ca cb
      (hcaClass.trans (hr.1 v)) (hcbClass.trans (hr.1 w))
      hcaPair
    · refine ⟨hcbPair.1,?_,hcbPair.2.2⟩
      simpa only [crossings, arcInterior, Set.inter_comm] using hcbPair.2.1
    · exact hcaOld
    · simpa only [Bswap] using hcbOld
  · exact Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hcontact)

end CurveComplex.HyperellipticModel.ArcSurgery
