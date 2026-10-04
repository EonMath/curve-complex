import CurveComplexGenusTwo.Filtration.Geometry.ActualEndpointBigonEnlargement
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedJoinedOffsetCarrier
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
import CurveComplexGenusTwo.Topology.FrontierCircle.FrontierGeometry
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualEmbeddedArcConcatenation
import CurveComplexGenusTwo.Topology.CapBandGeometry.LocalCapSeam
import Mathlib.Topology.LocalAtTarget
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualRawTailBigonReplacement
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkFreeBigonLoopExclusion
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance actualRoundedSideReplacementDecidableEqEssentialArcClass (M : HyperellipticModel E S) : DecidableEq (EssentialArcClass M) := Classical.decEq _
open ArcSurgery Set Topology Metric Schoenflies CurveComplex.ActualCrossingSlide
open scoped BigOperators
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
private theorem actual_unmarked_attached_wide_cap_geometry
(M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
(B : ActualMarkedTwoSideDisk M a b)
(F : OpenPartialHomeomorph S (ℝ × ℝ)) (δ : ℝ) (hδ : 0 < δ)
(A p L : S) (hAS : A ∈ F.source) (hpS : p ∈ F.source) (hLS : L ∈ F.source)
(hAcoord : F A=(-δ,0)) (hpcoord : F p=(0,0)) (hLcoord : F L=(0,δ))
(H : C(Interval × Interval,S))
(hHS : ∀ t u : Interval, H (t,u) ∈ F.source)
(hHC : ∀ t u : Interval, F (H (t,u))=(-(δ*(1-u.val)+(δ/2*t.val)*u.val),δ*u.val))
(hBox : ∀ x y : ℝ, 0≤x → x≤δ → 0≤y → y≤δ → (-x,y) ∈ F.target)
(hAxis : ∀ x ∈ F.source, x ∈ a.val.image ↔ (F x).2=0)
(hBAxis : ∀ x ∈ F.source, x ∈ b.val.image ↔ (F x).1=0)
(hMarks : Disjoint F.source (M.cover.branch : Set S))
(T : Set S)
(hTImage : T=F.symm '' {z : ℝ × ℝ | -δ≤z.1 ∧ z.1≤0 ∧ 0≤z.2 ∧ z.2≤z.1+δ})
(hTContact : T ∩ range B.disk ⊆ range B.secondSide)
(hVerticalSelected : ∀ y : ℝ, 0≤y → y≤δ → F.symm (0,y) ∈ range B.secondSide)
(hSharedInterior : ∀ y : ℝ, 0<y → y<δ → F.symm (0,y) ∈ interior (range B.disk ∪ T))
(hFrontier : frontier (range B.disk)=range B.firstSide ∪ range B.secondSide) :
∃ W : Set S, IsCompact W ∧ W ⊆ F.source ∧ T ⊆ W ∧
  Disjoint W (M.cover.branch : Set S) ∧ W ∩ a.val.image ⊆ T ∧
  (∀ t u : Interval, H (t,u) ∈ W) ∧
  (∀ t u : Interval, 0<t.val → t.val<1 → 0<u.val → u.val<1 → H (t,u) ∈ interior W) ∧
  ∃ g outer : C(Interval,S), IsEmbedding g ∧ IsEmbedding outer ∧
    g 0=p ∧ g 1=L ∧ outer 0=A ∧ outer 1=L ∧
    range g ⊆ range B.secondSide ∧ range g ⊆ W ∧ range outer ⊆ W ∧
    range g=W ∩ range B.disk ∧ range outer ∩ range B.secondSide={L} ∧
    range outer ∩ a.val.image ⊆ {A} ∧
    (∀ u : Interval, 0<u.val → u.val<1 → g u ∈ interior (range B.disk ∪ W)) ∧
    frontier W ⊆ (T ∩ a.val.image) ∪ range g ∪ range outer := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let V : Set (ℝ × ℝ) := {z | -δ≤z.1 ∧ z.1≤0 ∧ 0≤z.2 ∧ z.2≤2*(z.1+δ) ∧ z.2≤δ}
  let P : Set (ℝ × ℝ) := {z | -δ<z.1 ∧ z.1<0 ∧ 0<z.2 ∧ z.2<2*(z.1+δ) ∧ z.2<δ}
  have hTarget (z : ℝ × ℝ) (hz : z ∈ V) : z ∈ F.target := by
    simpa only [neg_neg] using hBox (-z.1) z.2 (by linarith [hz.2.1])
      (by linarith [hz.1]) hz.2.2.1 hz.2.2.2.2
  have hVc : IsClosed V := (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le continuous_const continuous_snd).inter
        ((isClosed_le continuous_snd (show Continuous (fun z : ℝ × ℝ => 2*(z.1+δ)) by fun_prop)).inter
          (isClosed_le continuous_snd continuous_const))))
  have hVk : IsCompact V := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hVc
    (fun z hz => ⟨⟨hz.1,hz.2.1⟩,⟨hz.2.2.1,hz.2.2.2.2⟩⟩)
  let W : Set S := F.symm '' V
  have hWsource : W ⊆ F.source := by rintro x ⟨z,hz,rfl⟩; exact F.map_target (hTarget z hz)
  have hWcompact : IsCompact W := hVk.image_of_continuousOn (F.symm.continuousOn.mono hTarget)
  have hTW : T ⊆ W := by
    rw [hTImage]
    rintro x ⟨z,hz,rfl⟩
    exact ⟨z,⟨hz.1,hz.2.1,hz.2.2.1,by linarith [hz.1,hz.2.2.2],by linarith [hz.2.1,hz.2.2.2]⟩,rfl⟩
  have hWA : W ∩ a.val.image ⊆ T := by
    rintro x ⟨⟨z,hz,he⟩,haX⟩
    have hxS : x ∈ F.source := he ▸ F.map_target (hTarget z hz)
    have hy : z.2=0 := by
      have hh := (hAxis x hxS).mp haX
      rw [← he,F.right_inv (hTarget z hz)] at hh
      exact hh
    rw [hTImage]
    exact ⟨z,⟨hz.1,hz.2.1,by rw [hy],by rw [hy]; linarith [hz.1]⟩,he⟩
  have hPo : IsOpen P := (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        ((isOpen_lt continuous_snd (show Continuous (fun z : ℝ × ℝ => 2*(z.1+δ)) by fun_prop)).inter
          (isOpen_lt continuous_snd continuous_const))))
  have hPsub : P ⊆ V := fun z hz => ⟨hz.1.le,hz.2.1.le,hz.2.2.1.le,hz.2.2.2.1.le,hz.2.2.2.2.le⟩
  have hOpenP : IsOpen (F.symm '' P) := F.symm.isOpen_image_of_subset_source hPo (hPsub.trans hTarget)
  have hJointV (t u : Interval) : (-(δ*(1-u.val)+(δ/2*t.val)*u.val),δ*u.val) ∈ V := by
    have hu0 := u.property.1
    have hu1 := u.property.2
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hy := mul_nonneg hδ.le hu0
    have ha := mul_nonneg hy (show 0≤1-t.val/2 by linarith)
    have hb := add_nonneg (mul_nonneg hδ.le (sub_nonneg.mpr hu1))
      (mul_nonneg (mul_nonneg (half_pos hδ).le ht0) hu0)
    exact ⟨by nlinarith,by nlinarith,hy,
      by nlinarith [mul_nonneg hy (sub_nonneg.mpr ht1)],by nlinarith⟩
  have hJointP (t u : Interval) (ht : 0<t.val) (ht1 : t.val<1) (hu : 0<u.val) (hu1 : u.val<1) :
      (-(δ*(1-u.val)+(δ/2*t.val)*u.val),δ*u.val) ∈ P := by
    have hy := mul_pos hδ hu
    have ha := mul_pos hy (show 0<1-t.val/2 by linarith)
    have hb := add_pos_of_pos_of_nonneg (mul_pos hδ (sub_pos.mpr hu1))
      (mul_nonneg (mul_nonneg (half_pos hδ).le ht.le) hu.le)
    exact ⟨by nlinarith,by nlinarith,hy,
      by nlinarith [mul_pos hy (sub_pos.mpr ht1)],by nlinarith⟩
  have hJointBack (t u : Interval) : F.symm (-(δ*(1-u.val)+(δ/2*t.val)*u.val),δ*u.val)=H (t,u) := by
    rw [← hHC t u,F.left_inv (hHS t u)]
  have hAoffD : A ∉ range B.disk := by
    intro haD
    have haT : A ∈ T := by
      rw [hTImage]
      refine ⟨(-δ,0),?_,?_⟩
      · exact ⟨le_rfl,by linarith,le_rfl,by ring_nf; exact le_rfl⟩
      · rw [← hAcoord,F.left_inv hAS]
    have hbX := B.second_on_curve (hTContact ⟨haT,haD⟩)
    have hh := (hBAxis A hAS).mp hbX
    rw [hAcoord] at hh
    linarith
  have hPathOutside (f : C(Interval,S))
      (hBoundary : Disjoint (range f) (range B.firstSide ∪ range B.secondSide))
      (hStart : f 0 ∉ range B.disk) : Disjoint (range f) (range B.disk) := by
    have hClosed : IsClosed (range B.disk) := (isCompact_range B.disk.continuous).isClosed
    have hFront : Disjoint (range f) (frontier (range B.disk)) := hFrontier.symm ▸ hBoundary
    have hCover : range f ⊆ interior (range B.disk) ∪ (range B.disk)ᶜ := by
      intro x hx
      by_cases hxD : x ∈ range B.disk
      · apply Or.inl
        by_contra hn
        exact Set.disjoint_left.mp hFront hx (hClosed.frontier_eq ▸ ⟨hxD,hn⟩)
      · exact Or.inr hxD
    rcases (isPreconnected_range f.continuous).subset_or_subset isOpen_interior hClosed.isOpen_compl
      (Set.disjoint_left.mpr (fun x hx hn => hn (interior_subset hx))) hCover with hi|ho
    · exact False.elim (hStart (interior_subset (hi (Set.mem_range_self 0))))
    · exact Set.disjoint_left.mpr (fun x hx hD => ho hx hD)
  have hNegativeOutside (z : ℝ × ℝ) (hz : z ∈ V) (hx : z.1<0) : F.symm z ∉ range B.disk := by
    by_cases hy0 : z.2=0
    · intro hD
      have hzT : F.symm z ∈ T := by
        rw [hTImage]
        exact ⟨z,⟨hz.1,hz.2.1,by rw [hy0],by rw [hy0]; linarith [hz.1]⟩,rfl⟩
      have hbX := B.second_on_curve (hTContact ⟨hzT,hD⟩)
      have hh := (hBAxis _ (F.map_target (hTarget z hz))).mp hbX
      rw [F.right_inv (hTarget z hz)] at hh
      linarith
    · have hypos : 0<z.2 := lt_of_le_of_ne hz.2.2.1 (Ne.symm hy0)
      let q : Interval → ℝ × ℝ := fun u => (-δ*(1-u.val)+z.1*u.val,z.2*u.val)
      have hqx (u : Interval) : (q u).1<0 := by
        by_cases hu : u.val=0
        · simp [q,hu,hδ]
        · have hup : 0<u.val := lt_of_le_of_ne u.property.1 (Ne.symm hu)
          have h0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) (sub_nonneg.mpr u.property.2)
          have h1 := mul_neg_of_neg_of_pos hx hup
          dsimp [q]
          linarith
      have hqt (u : Interval) : q u ∈ F.target := by
        have hxlow : -δ≤(q u).1 := by
          dsimp [q]
          nlinarith [mul_nonneg u.property.1 (show 0≤z.1+δ by linarith [hz.1])]
        have hyup : (q u).2≤δ := by
          change z.2*u.val≤δ
          exact (mul_le_of_le_one_right hz.2.2.1 u.property.2).trans hz.2.2.2.2
        simpa only [neg_neg] using hBox (-(q u).1) (q u).2 (by linarith [hqx u])
          (by linarith) (mul_nonneg hz.2.2.1 u.property.1) hyup
      let f : C(Interval,S) := ⟨fun u => F.symm (q u),
        F.symm.continuousOn.comp_continuous (by dsimp [q]; fun_prop) hqt⟩
      have hfc (u : Interval) : F (f u)=q u := F.right_inv (hqt u)
      have hf0 : f 0=A := by
        change F.symm (q 0)=A
        have hh : q 0=F A := by simp [q,hAcoord]
        rw [hh,F.left_inv hAS]
      have hf1 : f 1=F.symm z := by simp [f,q]
      have hBoundary : Disjoint (range f) (range B.firstSide ∪ range B.secondSide) := by
        apply Set.disjoint_left.mpr
        rintro x ⟨u,rfl⟩ (hfirst|hsecond)
        · have hh := (hAxis _ (F.map_target (hqt u))).mp (B.first_on_curve hfirst)
          change (F (f u)).2 = 0 at hh
          rw [hfc] at hh
          have hu0 : u=0 := Subtype.ext ((mul_eq_zero.mp hh).resolve_left (ne_of_gt hypos))
          subst u
          exact hAoffD (hf0 ▸ image_subset_range _ _ (B.boundary_eq.symm ▸
            (show f 0 ∈ range B.firstSide ∪ range B.secondSide from Or.inl hfirst)))
        · have hh := (hBAxis _ (F.map_target (hqt u))).mp (B.second_on_curve hsecond)
          change (F (f u)).1 = 0 at hh
          rw [hfc] at hh
          exact (ne_of_lt (hqx u)) hh
      exact fun hD => Set.disjoint_left.mp (hPathOutside f hBoundary (hf0 ▸ hAoffD))
        (hf1 ▸ Set.mem_range_self 1) hD
  let qb : Interval → ℝ × ℝ := fun u => (0,δ*u.val)
  have hqb (u : Interval) : qb u ∈ V := by
    change -δ≤0 ∧ 0≤0 ∧ 0≤δ*u.val ∧ δ*u.val≤2*(0+δ) ∧ δ*u.val≤δ
    have hx := mul_nonneg hδ.le u.property.1
    have hupper := mul_le_of_le_one_right hδ.le u.property.2
    exact ⟨by linarith,le_rfl,hx,by linarith,hupper⟩
  let g : C(Interval,S) := ⟨fun u => F.symm (qb u),
    F.symm.continuousOn.comp_continuous (by dsimp [qb]; fun_prop) (fun u => hTarget _ (hqb u))⟩
  have hgc (u : Interval) : F (g u)=qb u := F.right_inv (hTarget _ (hqb u))
  have hgi : Function.Injective g := by
    intro u v he
    have hh := congrArg Prod.snd (congrArg F he)
    rw [hgc,hgc] at hh
    exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hδ) hh)
  have hg0 : g 0=p := by
    change F.symm (qb 0)=p
    have hh : qb 0=F p := by simp [qb,hpcoord]
    rw [hh,F.left_inv hpS]
  have hg1 : g 1=L := by
    change F.symm (qb 1)=L
    have hh : qb 1=F L := by simp [qb,hLcoord]
    rw [hh,F.left_inv hLS]
  have hgside : range g ⊆ range B.secondSide := by
    rintro x ⟨u,rfl⟩
    exact hVerticalSelected (δ*u.val) (mul_nonneg hδ.le u.property.1)
      (mul_le_of_le_one_right hδ.le u.property.2)
  have hgW : range g ⊆ W := by rintro x ⟨u,rfl⟩; exact ⟨qb u,hqb u,rfl⟩
  have hAxisImage (z : ℝ × ℝ) (hz : z ∈ V) (hx : z.1=0) : F.symm z ∈ range g := by
    let u : Interval := ⟨z.2/δ,div_nonneg hz.2.2.1 hδ.le,(div_le_one hδ).mpr hz.2.2.2.2⟩
    have hh : qb u=z := by
      apply Prod.ext
      · exact hx.symm
      · change δ*(z.2/δ)=z.2
        field_simp [ne_of_gt hδ]
    exact ⟨u,by change F.symm (qb u)=F.symm z; rw [hh]⟩
  have hgContact : range g=W ∩ range B.disk := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hgW hx,image_subset_range _ _ (B.boundary_eq.symm ▸
        (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inr (hgside hx)))⟩
    · rintro x ⟨⟨z,hz,rfl⟩,hxD⟩
      have hx0 : z.1=0 := le_antisymm hz.2.1
        (le_of_not_gt (fun hn => hNegativeOutside z hz hn hxD))
      exact hAxisImage z hz hx0
  let d : C(Interval,S) := ⟨fun u => H (1,u),H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hdc (u : Interval) : F (d u)=(-δ+(δ/2)*u.val,δ*u.val) := by
    have hh := hHC 1 u
    change F (d u)=_ at hh
    convert hh using 1 <;> dsimp <;> congr 1 <;> ring
  have hdi : Function.Injective d := by
    intro u v he
    have hh := congrArg Prod.snd (congrArg F he)
    rw [hdc,hdc] at hh
    exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hδ) hh)
  have hd0 : d 0=A := F.injOn (hHS 1 0) hAS (by change F (d 0) = F A; rw [hdc,hAcoord]; simp)
  let qv : Interval → ℝ × ℝ := fun u => (-(δ/2)*(1-u.val),δ)
  have hqv (u : Interval) : qv u ∈ V := by
    change -δ≤-(δ/2)*(1-u.val) ∧ -(δ/2)*(1-u.val)≤0 ∧ 0≤δ ∧
      δ≤2*(-(δ/2)*(1-u.val)+δ) ∧ δ≤δ
    exact ⟨by nlinarith [u.property.1,u.property.2],
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr u.property.2),hδ.le,
      by nlinarith [u.property.1],le_rfl⟩
  let v : C(Interval,S) := ⟨fun u => F.symm (qv u),
    F.symm.continuousOn.comp_continuous (by dsimp [qv]; fun_prop) (fun u => hTarget _ (hqv u))⟩
  have hvc (u : Interval) : F (v u)=qv u := F.right_inv (hTarget _ (hqv u))
  have hvi : Function.Injective v := by
    intro u w he
    have hh := congrArg Prod.fst (congrArg F he)
    rw [hvc,hvc] at hh
    have hh' : -(δ/2)*(1-u.val)=-(δ/2)*(1-w.val) := hh
    have hEq := mul_left_cancel₀ (show -(δ/2)≠0 by linarith) hh'
    exact Subtype.ext (by linarith)
  have hdv : d 1=v 0 := F.injOn (hHS 1 1) (F.map_target (hTarget _ (hqv 0)))
    (by change F (d 1) = F (v 0); rw [hdc,hvc]; simp [qv]; ring)
  have hv1 : v 1=L := F.injOn (F.map_target (hTarget _ (hqv 1))) hLS
    (by change F (v 1) = F L; rw [hvc,hLcoord]; simp [qv])
  have hdW : range d ⊆ W := by
    rintro x ⟨u,rfl⟩
    exact ⟨_,hJointV 1 u,hJointBack 1 u⟩
  have hvW : range v ⊆ W := by rintro x ⟨u,rfl⟩; exact ⟨qv u,hqv u,rfl⟩
  have hMeet : range d ∩ range v={d 1} := by
    ext x
    constructor
    · rintro ⟨⟨u,rfl⟩,⟨w,he⟩⟩
      have hh := congrArg Prod.snd (congrArg F he)
      rw [hvc,hdc] at hh
      have hu : u=1 := Subtype.ext (by change u.val=1; dsimp [qv] at hh; nlinarith)
      subst u
      rfl
    · rintro rfl
      exact ⟨⟨1,rfl⟩,⟨0,hdv.symm⟩⟩
  obtain ⟨outer,ho,ho0,ho1,hoRange⟩ := CurveComplex.source_embedded_arc_concatenation d v
    (d.continuous.isClosedEmbedding hdi).isEmbedding (v.continuous.isClosedEmbedding hvi).isEmbedding hdv hMeet
  have hoW : range outer ⊆ W := by rw [hoRange]; exact Set.union_subset hdW hvW
  have hOuterB : range outer ∩ range B.secondSide={L} := by
    ext x
    constructor
    · rintro ⟨hx,hB⟩
      have hxS := hWsource (hoW hx)
      have hx0 := (hBAxis x hxS).mp (B.second_on_curve hB)
      rw [hoRange] at hx
      rcases hx with ⟨u,hu⟩|⟨u,hu⟩
      · have hh : -δ+(δ/2)*u.val=0 := by rw [← hu,hdc] at hx0; exact hx0
        exfalso
        nlinarith [u.property.2]
      · have hh : -(δ/2)*(1-u.val)=0 := by rw [← hu,hvc] at hx0; exact hx0
        have hz : 1-u.val=0 := (mul_eq_zero.mp hh).resolve_left (by linarith)
        have hu1 : u=1 := Subtype.ext (by change u.val=1; linarith)
        exact Set.mem_singleton_iff.mpr (hu.symm.trans ((congrArg v hu1).trans hv1))
    · rintro rfl
      exact ⟨⟨1,ho1.trans hv1⟩,hg1 ▸ hgside (Set.mem_range_self 1)⟩
  have hOuterA : range outer ∩ a.val.image ⊆ {A} := by
    rintro x ⟨hx,hA⟩
    have hxS := hWsource (hoW hx)
    have hx0 := (hAxis x hxS).mp hA
    rw [hoRange] at hx
    rcases hx with ⟨u,hu⟩|⟨u,hu⟩
    · have hh : δ*u.val=0 := by rw [← hu,hdc] at hx0; exact hx0
      have hu0 : u=0 := Subtype.ext ((mul_eq_zero.mp hh).resolve_left (ne_of_gt hδ))
      exact Set.mem_singleton_iff.mpr (hu.symm.trans ((congrArg d hu0).trans hd0))
    · have hh : δ=0 := by rw [← hu,hvc] at hx0; exact hx0
      exact False.elim ((ne_of_gt hδ) hh)
  have hVerticalImage (z : ℝ × ℝ) (hz : z ∈ V) (hy : z.2=δ) : F.symm z ∈ range v := by
    have hxlow : -(δ/2)≤z.1 := by linarith [hz.2.2.2.1]
    have hlo : -1 ≤ 2*z.1/δ := (le_div_iff₀ hδ).mpr (by linarith)
    have hhi : 2*z.1/δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hz.2.1]) hδ.le
    let u : Interval := ⟨1+2*z.1/δ,(by linarith),(by linarith)⟩
    have hu : δ*u.val=δ+2*z.1 := by dsimp [u]; field_simp [ne_of_gt hδ]
    refine ⟨u, ?_⟩
    apply F.injOn (F.map_target (hTarget _ (hqv u))) (F.map_target (hTarget z hz))
    change F (v u) = F (F.symm z)
    rw [hvc,F.right_inv (hTarget z hz)]
    apply Prod.ext
    · change -(δ/2)*(1-u.val) = z.1
      nlinarith [hu]
    · exact hy.symm
  have hDiagonalImage (z : ℝ × ℝ) (hz : z ∈ V) (hy : z.2=2*(z.1+δ)) : F.symm z ∈ range d := by
    let u : Interval := ⟨z.2/δ,div_nonneg hz.2.2.1 hδ.le,(div_le_one hδ).mpr hz.2.2.2.2⟩
    have hu : δ*u.val=z.2 := by dsimp [u]; field_simp [ne_of_gt hδ]
    refine ⟨u,?_⟩
    apply F.injOn (hHS 1 u) (F.map_target (hTarget z hz))
    change F (d u) = F (F.symm z)
    rw [hdc,F.right_inv (hTarget z hz)]
    apply Prod.ext
    · have hh : (δ/2)*u.val=z.2/2 := by nlinarith [hu]
      rw [hh]; linarith
    · exact hu
  refine ⟨W,hWcompact,hWsource,hTW,hMarks.mono_left hWsource,hWA,?_,?_,g,outer,
    (g.continuous.isClosedEmbedding hgi).isEmbedding,ho,hg0,hg1,ho0.trans hd0,ho1.trans hv1,
    hgside,hgW,hoW,hgContact,hOuterB,hOuterA,?_,?_⟩
  · intro t u
    exact ⟨_,hJointV t u,hJointBack t u⟩
  · intro t u ht ht1 hu hu1
    exact interior_maximal (Set.image_mono hPsub) hOpenP ⟨_,hJointP t u ht ht1 hu hu1,hJointBack t u⟩
  · intro u hu0 hu1
    exact interior_mono (Set.union_subset_union_right _ hTW)
      (hSharedInterior (δ*u.val) (mul_pos hδ hu0) (mul_lt_of_lt_one_right hδ hu1))
  · intro x hx
    have hxW := hWcompact.isClosed.frontier_subset hx
    obtain ⟨z,hz,he⟩ := hxW
    have hxW : x ∈ W := ⟨z,hz,he⟩
    by_cases hy0 : z.2=0
    · have hxA : x ∈ a.val.image := (hAxis x (hWsource hxW)).mpr (by rw [← he,F.right_inv (hTarget z hz)]; exact hy0)
      exact Or.inl (Or.inl ⟨hWA ⟨hxW,hxA⟩,hxA⟩)
    by_cases hx0 : z.1=0
    · exact Or.inl (Or.inr (he ▸ hAxisImage z hz hx0))
    by_cases hyδ : z.2=δ
    · exact Or.inr (hoRange.symm ▸ Or.inr (he ▸ hVerticalImage z hz hyδ))
    by_cases hdiag : z.2=2*(z.1+δ)
    · exact Or.inr (hoRange.symm ▸ Or.inl (he ▸ hDiagonalImage z hz hdiag))
    · have hzP : z ∈ P := ⟨by have hh := lt_of_le_of_ne hz.2.2.1 (Ne.symm hy0); linarith [hz.2.2.2.1],
        lt_of_le_of_ne hz.2.1 hx0,lt_of_le_of_ne hz.2.2.1 (Ne.symm hy0),
        lt_of_le_of_ne hz.2.2.2.1 hdiag,lt_of_le_of_ne hz.2.2.2.2 hyδ⟩
      have hi : x ∈ interior W := interior_maximal (Set.image_mono hPsub) hOpenP ⟨z,hzP,he⟩
      exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hi hx)

private theorem actual_jordan_image (C : Set Plane) (hC : IsJordanCurve C)
    (e : Plane ≃ₜ Plane) : IsJordanCurve (e '' C) := by
  obtain ⟨f,hf,hfr⟩ := hC
  refine ⟨e ∘ f,⟨e.continuous.comp_continuousOn hf.continuousOn,
    congrArg e hf.closes,fun x hx y hy he => hf.injOn hx hy (e.injective he)⟩,?_⟩
  rw [Set.image_comp,hfr]
private theorem actual_normalized_jordan_open_enclosure
    (A B : Set Plane) (p q : Plane)
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hwhole : A ∪ B=modelCurve)
    (F : Set Plane) (hF : IsClosed F) (hpF : p ∈ F) (hqF : q ∈ F)
    (hboundary : ∀ z ∈ F, z ∈ modelCurve → z=p ∨ z=q)
    (hinside : Disjoint (Plane.openSquare 0 1) F) :
    ∃ U : Set Plane, IsOpen U ∧ Disjoint U F ∧
      (Plane.openSquare 0 1 ∪ modelCurve) \ {p,q} ⊆ U ∧
      ∃ e : Plane ≃ₜ Plane, U=e '' Plane.openSquare 0 1 := by
  obtain ⟨φ,hp,hq,hAA,hBB,hAI,hBI,hfree⟩ :=
    CurveComplex.actual_endpoint_preserving_bigon_enlargement A B p q hA hB hwhole F hF hpF hqF hboundary hinside
  have hCurve : φ.symm '' modelCurve ⊆ Plane.openSquare 0 1 ∪ modelCurve := by
    intro x hx
    by_cases he : x ∈ ({p,q} : Set Plane)
    · rcases he with he|he
      · exact Or.inr (he.symm ▸ (hwhole ▸ Or.inl hA.left_mem))
      · have heq : x=q := by simpa using he
        exact Or.inr (heq.symm ▸ (hwhole ▸ Or.inl hA.right_mem))
    · rw [← hwhole,Set.image_union] at hx
      rcases hx with ha|hb
      · exact Or.inl (hAI ⟨ha,he⟩)
      · exact Or.inl (hBI ⟨hb,he⟩)
  have hImageJordan := actual_jordan_image modelCurve isJordanCurve_modelCurve φ.symm
  have hInsideSub : φ.symm '' Plane.openSquare 0 1 ⊆ Plane.openSquare 0 1 := by
    rw [← inside_modelCurve,CurveComplex.jordan_inside_homeomorph_image]
    exact CurveComplex.jordan_inside_mono_of_boundary_subset_closed_inside
      (jordan_curve_theorem isJordanCurve_modelCurve) (jordan_curve_theorem hImageJordan)
      (by simpa only [inside_modelCurve] using hCurve)
  let U : Set Plane := φ '' Plane.openSquare 0 1
  refine ⟨U,φ.isOpenMap _ (Plane.isOpen_openSquare 0 1),?_,?_,φ,rfl⟩
  · apply Set.disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hx
    exact hfree z hz hx
  · rintro x ⟨hx,hn⟩
    refine ⟨φ.symm x,?_,φ.apply_symm_apply x⟩
    rcases hx with hi|hc
    · exact hInsideSub (Set.mem_image_of_mem φ.symm hi)
    · have hximage : φ.symm x ∈ φ.symm '' modelCurve := Set.mem_image_of_mem φ.symm hc
      have hnot : φ.symm x ∉ ({p,q} : Set Plane) := by
        rintro (he|he)
        · exact hn (Or.inl (by calc x=φ (φ.symm x) := (φ.apply_symm_apply x).symm
                                  _=p := by rw [he,hp]))
        · have heq : φ.symm x=q := by simpa using he
          exact hn (Or.inr (by calc x=φ (φ.symm x) := (φ.apply_symm_apply x).symm
                                   _=q := by rw [heq,hq]))
      rw [← hwhole,Set.image_union] at hximage
      exact hximage.elim (fun ha => hAI ⟨ha,hnot⟩) (fun hb => hBI ⟨hb,hnot⟩)
private theorem actual_jordan_relative_open_enclosure
    (A B : Set Plane) (p q : Plane)
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hC : IsJordanCurve (A ∪ B))
    (F : Set Plane) (hF : IsClosed F) (hpF : p ∈ F) (hqF : q ∈ F)
    (hboundary : ∀ z ∈ F, z ∈ A ∪ B → z=p ∨ z=q)
    (hinside : Disjoint (inside (A ∪ B)) F) :
    ∃ U : Set Plane, IsOpen U ∧ Disjoint U F ∧
      (inside (A ∪ B) ∪ (A ∪ B)) \ {p,q} ⊆ U ∧
      ∃ e : Plane ≃ₜ Plane, U=e '' Plane.openSquare 0 1 := by
  obtain ⟨bc⟩ := hC.homeomorph_modelCurve
  obtain ⟨e,he⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve bc
  have hImage : e '' (A ∪ B)=modelCurve := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [he ⟨x,hx⟩]
      exact (bc ⟨x,hx⟩).property
    · intro hz
      obtain ⟨x,hx⟩ := bc.surjective ⟨z,hz⟩
      exact ⟨x,x.property,(he x).trans (congrArg Subtype.val hx)⟩
  have hInsideImage : e '' inside (A ∪ B)=Plane.openSquare 0 1 := by
    rw [CurveComplex.jordan_inside_homeomorph_image,hImage,inside_modelCurve]
  have hNF : IsClosed (e '' F) := e.isClosedMap _ hF
  have hNB : ∀ z ∈ e '' F, z ∈ modelCurve → z=e p ∨ z=e q := by
    rintro z ⟨x,hx,rfl⟩ hz
    rw [← hImage] at hz
    obtain ⟨y,hy,hye⟩ := hz
    have hxy : y=x := e.injective hye
    exact (hboundary x hx (hxy ▸ hy)).elim
      (fun hp => Or.inl (congrArg e hp)) (fun hq => Or.inr (congrArg e hq))
  have hNI : Disjoint (Plane.openSquare 0 1) (e '' F) := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨x,hx,hxz⟩
    rw [← hInsideImage] at hz
    obtain ⟨y,hy,hyz⟩ := hz
    exact Set.disjoint_left.mp hinside ((e.injective (hyz.trans hxz.symm)) ▸ hy) hx
  obtain ⟨V,hVo,hVF,hVK,d,hd⟩ := actual_normalized_jordan_open_enclosure
    (e '' A) (e '' B) (e p) (e q)
    (hA.image_of_injOn (Set.subset_univ _) e.continuous.continuousOn e.injective.injOn)
    (hB.image_of_injOn (Set.subset_univ _) e.continuous.continuousOn e.injective.injOn)
    (by rw [← Set.image_union,hImage]) (e '' F) hNF
    (Set.mem_image_of_mem e hpF) (Set.mem_image_of_mem e hqF) hNB hNI
  refine ⟨e ⁻¹' V,hVo.preimage e.continuous,?_,?_,d.trans e.symm,?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hf
    exact Set.disjoint_left.mp hVF hx (Set.mem_image_of_mem e hf)
  · rintro x ⟨hx,hn⟩
    apply hVK
    refine ⟨?_,?_⟩
    · exact hx.elim (fun hi => Or.inl (hInsideImage ▸ Set.mem_image_of_mem e hi))
        (fun hc => Or.inr (hImage ▸ Set.mem_image_of_mem e hc))
    · rintro (hp|hq)
      · exact hn (Or.inl (e.injective hp))
      · have hq' : e x=e q := by simpa using hq
        exact hn (Or.inr (e.injective hq'))
  · rw [hd]
    ext x
    constructor
    · rintro ⟨y,hy,hye⟩
      refine ⟨y,hy,?_⟩
      change e.symm (d y)=x
      exact e.injective.eq_iff.mp (by rw [e.apply_symm_apply]; exact hye)
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,(e.apply_symm_apply _).symm⟩

private theorem actual_joint_compact_support_bound
    {Y : Type*} [TopologicalSpace Y]
    (H : unitInterval × Y → S) (hH : Continuous H)
    (K : Set Y) (hK : IsCompact K) (U : Set S) (hU : IsOpen U)
    (hzero : ∀ y ∈ K, H (0,y) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : unitInterval, t.val < δ → ∀ y ∈ K, H (t,y) ∈ U := by
  have he : ∀ᶠ t : unitInterval in 𝓝 0, ∀ y ∈ K, H (t,y) ∈ U :=
    hK.eventually_forall_of_forall_eventually (fun y hy =>
      (hU.preimage hH).mem_nhds (hzero y hy))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro t ht y hy
  have hd : dist t (0 : unitInterval) < δ := by
    rw [Subtype.dist_eq,Real.dist_eq]
    change |t.val - 0| < δ
    simpa [abs_of_nonneg t.property.1] using ht
  exact hball hd y hy


private theorem actual_marked_simultaneous_gap_matching_below
    (M : HyperellipticModel E S) [T2Space S]
    {J G : Type} [Fintype J] [Fintype G]
    (old : J → EssentialMarkedArc M) (b : EssentialMarkedArc M)
    (U : Set S) (V : Set (ℝ × ℝ)) (hV : IsOpen V) (e : U ≃ₜ V)
    (A l r B : G → ℝ)
    (hAl : ∀ g, A g < l g) (hlr : ∀ g, l g < r g) (hrB : ∀ g, r g < B g)
    (haxis : ∀ g x, x ∈ Icc (A g) (B g) → ∃ y : V, y.val=(x,0) ∧
      ∀ j, (e.symm y : S) ∉ (old j).val.image)
    (hbaxis : ∀ u : U, (u : S) ∈ b.val.image ↔ (e u : ℝ × ℝ).2=0)
    (L R : G → C(unitInterval,U))
    (hL : ∀ g, (e (L g 0) : ℝ × ℝ)=(l g,0))
    (hR : ∀ g, (e (R g 0) : ℝ × ℝ)=(r g,0))
    (δ : ℝ) (hδ : 0 < δ)
    (hside : ∀ g (t : unitInterval), t≠0 →
      0 < (e (L g t) : ℝ × ℝ).2 ∧ 0 < (e (R g t) : ℝ × ℝ).2) :
    ∃ t : unitInterval, 0 < t.val ∧ t.val < 1 ∧ t.val < δ ∧
      ∀ g, ∃ f : Path (L g t : S) (R g t : S), IsEmbedding f ∧
        Disjoint (range f) b.val.image ∧
        (∀ j, Disjoint (range f) (old j).val.image) ∧
        ∀ s, ∃ u : U, (u : S)=f s ∧
          (e u : ℝ × ℝ)=(1-s.val) • (e (L g t) : ℝ × ℝ)+s.val • (e (R g t) : ℝ × ℝ) := by
  classical
  have hMatch (g : G) := actual_marked_contact_gap_matching M old b U V hV e
    (A g) (l g) (r g) (B g) (hAl g) (hlr g) (hrB g) (haxis g)
    hbaxis (L g) (R g) (hL g) (hR g) (hside g)
  choose ρ hρ hPaths using hMatch
  let O : Set ℝ := (Iio 1 ∩ Iio δ) ∩ ⋂ g, Iio (ρ g)
  have hO : IsOpen O := (isOpen_Iio.inter isOpen_Iio).inter (isOpen_iInter_of_finite (fun _ => isOpen_Iio))
  have h0O : (0:ℝ) ∈ O := ⟨⟨by norm_num,hδ⟩,Set.mem_iInter.mpr hρ⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO 0 h0O
  have hμ : 0 < ε/2 := half_pos hε
  have hμO : ε/2 ∈ O := hball (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hμ]
    linarith)
  let t : unitInterval := ⟨ε/2,hμ.le,hμO.1.1.le⟩
  refine ⟨t,hμ,hμO.1.1,hμO.1.2,?_⟩
  intro g
  exact hPaths g t hμ (Set.mem_iInter.mp hμO.2 g)

private theorem actual_jordan_inside_open_disk_enclosure
    (C : Set Plane) (hC : IsJordanCurve C) (e : Plane ≃ₜ Plane)
    (hBoundary : C ⊆ closure (e '' Plane.openSquare 0 1)) :
    inside C ⊆ e '' Plane.openSquare 0 1 := by
  have hContainer := actual_jordan_image modelCurve isJordanCurve_modelCurve e
  have hClosure : closure (e '' Plane.openSquare 0 1)=inside (e '' modelCurve) ∪ e '' modelCurve := by
    rw [← e.image_closure,← inside_modelCurve,closure_eq_self_union_frontier,
      (jordan_curve_theorem isJordanCurve_modelCurve).frontier_inside,Set.image_union,
      CurveComplex.jordan_inside_homeomorph_image]
  have hSub := CurveComplex.jordan_inside_mono_of_boundary_subset_closed_inside
    (jordan_curve_theorem hContainer) (jordan_curve_theorem hC) (hClosure ▸ hBoundary)
  simpa only [← CurveComplex.jordan_inside_homeomorph_image,inside_modelCurve] using hSub

theorem actual_marked_rounded_side_replacement
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
  p ∉ M.cover.branch → p ∉ (old j).val.image) :
∃ c : EssentialMarkedArc M,
  ArcSurgery.vertex M c=ArcSurgery.vertex M a ∧
  (ArcSurgery.crossings M c b).Finite ∧
  (ArcSurgery.crossings M c b).ncard < (ArcSurgery.crossings M a b).ncard ∧
  (∀ p ∈ ArcSurgery.crossings M c b, ArcSurgery.CrossesInDisk M c b p) ∧
  ∀ j, (ArcSurgery.crossings M c (old j)).Finite ∧
    (∀ p ∈ ArcSurgery.crossings M c (old j),
      ArcSurgery.CrossesInDisk M c (old j) p) ∧
    (ArcSurgery.crossings M c (old j)).ncard ≤
      (ArcSurgery.crossings M a (old j) \ Set.range B.firstSide).ncard +
      (ArcSurgery.crossings M b (old j) ∩ Set.range B.secondSide).ncard := by
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
  obtain ⟨Graw,araw,Kraw,hKraw,hdecompRaw,hmeetRaw,hGrawMarks,hGrawK,hclassRaw,himageRaw⟩ :=
    hActualRawMarkedSideMove L R hL hLR hR hproper hSide
  have hRawRetainedCrossings (j : J) :
      Kraw ∩ arcInterior M (old j)=crossings M a (old j) \ range B.firstSide := by
    have hKa : Kraw ⊆ a.val.image := fun x hx => hdecompRaw.symm ▸ Or.inr hx
    ext x
    constructor
    · rintro ⟨hxK,hxo,hxm⟩
      refine ⟨⟨⟨hKa hxK,hxm⟩,hxo,hxm⟩,?_⟩
      intro hxf
      have hxcorner : x ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hmeetRaw ▸ (show x ∈ range B.firstSide ∩ Kraw from ⟨hxf,hxK⟩)
      exact hcorners j x hxcorner hxm hxo
    · rintro ⟨⟨⟨hxa,hxm⟩,hxo,hxom⟩,hxf⟩
      refine ⟨?_,hxo,hxm⟩
      rw [hdecompRaw] at hxa
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
    have hsplit : ((range B.secondSide ∪ Kraw) \ (M.cover.branch : Set S)) ∩
        arcInterior M (old j)=(range B.secondSide ∩ arcInterior M (old j)) ∪
          (Kraw ∩ arcInterior M (old j)) := by
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
      rw [himageRaw,hdecompRaw]
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
        Disjoint F.source (Kraw ∪ Kother) ∧
        (∀ x ∈ F.source, x ∈ araw.val.image ↔ (F x).2=0) ∧
        (∀ x ∈ F.source, x ∈ (old j).val.image ↔ (F x).1=0) := by
    have hpKraw : p ∉ Kraw := by
      intro hk
      have hpa : p ∈ a.val.image := hdecompRaw.symm ▸ Or.inr hk
      have hc : p ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hsecondclean ▸ (show p ∈ range B.secondSide ∩ a.val.image from ⟨hp.2,hpa⟩)
      exact hcorners j p hc hp.1.1.2 hp.1.2.1
    have hpKother : p ∉ Kother := by
      intro hk
      have hc : p ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hOtherMeet ▸ (show p ∈ range B.secondSide ∩ Kother from ⟨hp.2,hk⟩)
      exact hcorners j p hc hp.1.1.2 hp.1.2.1
    let W : Set S := (Kraw ∪ Kother)ᶜ
    have hW : IsOpen W := (hKraw.union hKother).isClosed.isOpen_compl
    have hpW : p ∈ W := fun h => h.elim hpKraw hpKother
    obtain ⟨F,hpF,hFW,hF0,hfree,hFb,hFo⟩ :=
      hMarkedLocalizedCrossingChart b (old j) p ((hb j).2 p hp.1) W hW hpW
    refine ⟨F,hpF,hF0,hfree,Set.disjoint_left.mpr (fun x hx hs => hFW hx hs),?_,hFo⟩
    intro x hx
    have hxK : x ∉ Kraw := fun hh => hFW hx (Or.inl hh)
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
        Disjoint U (M.cover.branch : Set S) ∧ Disjoint U (Kraw ∪ Kother) ∧
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
      have hxK : x ∉ Kraw ∪ Kother := fun hk => Set.disjoint_left.mp (hContactURemainders p) hxU hk
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
      have hnot : x ∉ Kraw ∪ Kother := fun hk => Set.disjoint_left.mp (hContactURemainders p) hx hk
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
      range B.disk ∩ Kraw=({B.firstCorner,B.secondCorner} : Set S) := by
    ext x
    constructor
    · rintro ⟨hxD,hxK⟩
      have hxa : x ∈ a.val.image := hdecompRaw.symm ▸ (show x ∈ range B.firstSide ∪ Kraw from Or.inr hxK)
      have hxs : x ∈ range B.firstSide := hDiskA ▸ ⟨hxD,hxa⟩
      exact hmeetRaw ▸ ⟨hxs,hxK⟩
    · intro hxc
      have hxs : x ∈ range B.firstSide ∩ Kraw := hmeetRaw.symm ▸ hxc
      refine ⟨?_,hxs.2⟩
      apply image_subset_range _ _
      exact B.boundary_eq.symm ▸ (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inl hxs.1)
  have hActualProducedDiskSupport
      (Q : C(Metric.closedBall (0:Plane) 1,S)) (hQ : range Q ⊆ range B.disk) :
      (∀ x ∈ range Q, x ∈ M.cover.branch → x ∈ ({B.firstCorner,B.secondCorner} : Set S)) ∧
      range Q ∩ Kraw ⊆ ({B.firstCorner,B.secondCorner} : Set S) := by
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
  obtain ⟨offset,hOffsetEmbedded,hOffsetFirst,hOffsetSecond,hOffsetB,
    hOffsetFirstSide,hOffsetK,hOffsetMarks,hOffsetOldBudget,hOffsetWholeCharts,
    cap,hCapEmbedded,hCapBoundary,hCapMarks,hCapK⟩ :=
    actual_marked_joined_offset_carrier M old a b hOld hab htab ha hb B hempty hhit
      hcorners Kraw hKraw hdecompRaw hmeetRaw
  let replacementTrace : Set S := Kraw ∪ range offset
  have hReplacementOldTrace (j : J) :
      replacementTrace ∩ arcInterior M (old j)=
        (crossings M a (old j) \ range B.firstSide) ∪
          (range offset ∩ arcInterior M (old j)) := by
    change (Kraw ∪ range offset) ∩ arcInterior M (old j)=_
    rw [Set.union_inter_distrib_right,hRawRetainedCrossings j]
  have hReplacementOldBudget (j : J) :
      (replacementTrace ∩ arcInterior M (old j)).Finite ∧
      (replacementTrace ∩ arcInterior M (old j)).ncard ≤
        (crossings M a (old j) \ range B.firstSide).ncard +
        (crossings M b (old j) ∩ range B.secondSide).ncard := by
    rw [hReplacementOldTrace j]
    have hRetainedFinite : (crossings M a (old j) \ range B.firstSide).Finite := (ha j).1.sdiff
    refine ⟨hRetainedFinite.union (hOffsetOldBudget j).1,?_⟩
    exact (Set.ncard_union_le _ _).trans
      (Nat.add_le_add_left (hOffsetOldBudget j).2 _)
  have hOffsetCapActual :
      IsEmbedding cap ∧
      cap '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=
        range B.firstSide ∪ range offset ∧
      Disjoint (cap '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) Kraw :=
    ⟨hCapEmbedded,hCapBoundary,hCapK⟩
  have hCapEmbeddedSideArc (f : C(Interval,Plane))
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
  have hActualOffsetCapChart :
      ∃ (F : Plane → S) (A C : Set Plane) (p q : Plane),
        IsOpenEmbedding F ∧ IsArcBetween A p q ∧ IsArcBetween C p q ∧
        A ∪ C=modelCurve ∧ F '' A=range B.firstSide ∧ F '' C=range offset ∧
        F p=B.firstCorner ∧ F q=B.secondCorner ∧
        F '' Plane.openSquare 0 1=cap '' {x | x.val ∈ Metric.ball (0 : Plane) 1} := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    have hex : ∃ p ∈ M.cover.branch, p ∉ ({B.firstCorner,B.secondCorner} : Finset S) := by
      by_contra hn
      have hsub : M.cover.branch ⊆ {B.firstCorner,B.secondCorner} := by
        intro p hp
        by_contra hc
        exact hn ⟨p,hp,hc⟩
      have hcard := Finset.card_le_card hsub
      rw [M.cover.branch_card] at hcard
      have htwo : ({B.firstCorner,B.secondCorner} : Finset S).card ≤ 2 := Finset.card_insert_le _ _
      omega
    obtain ⟨v,hvm,hvCorner⟩ := hex
    have hv : v ∉ range cap := by
      intro hvc
      exact hvCorner (by simpa using hCapMarks v hvc hvm)
    let e := M.puncturedPlane v
    let j : range cap → {z : S // z ≠ v} :=
      fun z => ⟨z.val,fun hz => hv (hz ▸ z.property)⟩
    let d : C(Metric.closedBall (0 : Plane) 1,Plane) :=
      ⟨fun x => e ⟨cap x,fun h => hv (h ▸ Set.mem_range_self x)⟩,by fun_prop⟩
    have firstDisk (t : Interval) : B.firstSide t ∈ range cap := by
      apply image_subset_range cap _
      rw [hCapBoundary]
      exact Or.inl (Set.mem_range_self t)
    have secondDisk (t : Interval) : offset t ∈ range cap := by
      apply image_subset_range cap _
      rw [hCapBoundary]
      exact Or.inr (Set.mem_range_self t)
    let g : C(Interval,Plane) :=
      ⟨fun t => e ⟨B.firstSide t,fun h => hv (h ▸ firstDisk t)⟩,by fun_prop⟩
    let h : C(Interval,Plane) :=
      ⟨fun t => e ⟨offset t,fun hh => hv (hh ▸ secondDisk t)⟩,by fun_prop⟩
    have hd : IsEmbedding d := (d.continuous.isClosedEmbedding (by
      intro x y hxy
      exact hCapEmbedded.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
    have hg : IsEmbedding g := (g.continuous.isClosedEmbedding (by
      intro x y hxy
      exact B.first_embedded.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
    have hh : IsEmbedding h := (h.continuous.isClosedEmbedding (by
      intro x y hxy
      exact hOffsetEmbedded.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
    have hg0 : g 0 = h 0 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact B.first_zero.trans hOffsetFirst.symm
    have hg1 : g 1 = h 1 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact B.first_one.trans hOffsetSecond.symm
    have hgA := hCapEmbeddedSideArc g hg
    have hhB : IsArcBetween (range h) (g 0) (g 1) := by rw [hg0,hg1]; exact hCapEmbeddedSideArc h hh
    have hc : IsJordanCurve (range g ∪ range h) := IsJordanCurve.of_two_arcs hgA hhB.reverse (by
      rintro z ⟨t,ht⟩ ⟨s,hs⟩
      have heq : B.firstSide t = offset s := congrArg Subtype.val (e.injective (ht.trans hs.symm))
      have hm : B.firstSide t ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hOffsetFirstSide ▸ ⟨Set.mem_range_self t,⟨s,heq.symm⟩⟩
      rcases mem_insert_iff.mp hm with hm | hm
      · left
        have ht0 : t=0 := B.first_embedded.injective (hm.trans B.first_zero.symm)
        exact ht.symm.trans (congrArg g ht0)
      · right
        have ht1 : t=1 := B.first_embedded.injective ((mem_singleton_iff.mp hm).trans B.first_one.symm)
        exact ht.symm.trans (congrArg g ht1))
    have hbd : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range g ∪ range h := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        have hxs : cap x ∈ range B.firstSide ∪ range offset := by
          rw [← hCapBoundary]
          exact mem_image_of_mem cap hx
        rcases hxs with ⟨t,ht⟩ | ⟨t,ht⟩
        · left; refine ⟨t,?_⟩; apply congrArg e; apply Subtype.ext; exact ht
        · right; refine ⟨t,?_⟩; apply congrArg e; apply Subtype.ext; exact ht
      · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
        · have htB : B.firstSide t ∈ cap '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
            rw [hCapBoundary]; exact Or.inl (Set.mem_range_self t)
          obtain ⟨x,hx,hxt⟩ := htB
          refine ⟨x,hx,?_⟩; apply congrArg e; apply Subtype.ext; exact hxt
        · have htB : offset t ∈ cap '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
            rw [hCapBoundary]; exact Or.inr (Set.mem_range_self t)
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
    let Cplane := φ.symm '' range h
    let p := φ.symm (g 0)
    let q := φ.symm (g 1)
    have hcancel (K : Set Plane) : φ '' (φ.symm '' K) = K := by
      ext z; simp
    have hgs (t) : M.planeToSphere v (g t) = B.firstSide t := congrArg Subtype.val (e.symm_apply_apply _)
    have hhs (t) : M.planeToSphere v (h t) = offset t := congrArg Subtype.val (e.symm_apply_apply _)
    refine ⟨f,A,Cplane,p,q,(M.planeToSphere_isOpenEmbedding v).comp φ.isOpenEmbedding,
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
      rw [φ.apply_symm_apply,hgs,B.first_zero]
    · change M.planeToSphere v (φ (φ.symm (g 1))) = _
      rw [φ.apply_symm_apply,hgs,B.first_one]
    · change (M.planeToSphere v ∘ φ) '' Plane.openSquare 0 1 = _
      rw [image_comp,hφI,← hi,image_image]
      apply Set.image_congr
      intro x hx
      exact congrArg Subtype.val (e.symm_apply_apply _)
  obtain ⟨capF,capA,capC,capP,capQ,hCapF,hCapA,hCapC,hCapAC,
    hCapFA,hCapFC,hCapFP,hCapFQ,hCapFInside⟩ := hActualOffsetCapChart
  have hOpenCapOffBoundary : Disjoint
      (cap '' {x | x.val ∈ Metric.ball (0 : Plane) 1})
      (cap '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hxy : x=y := hCapEmbedded.injective (hxz.trans hyz.symm)
    have hlt : dist y.val 0 < 1 := hxy ▸ hx
    have heq : dist y.val 0=1 := hy
    exact (ne_of_lt hlt) heq
  have hCornersCapBoundary : ({B.firstCorner,B.secondCorner} : Set S) ⊆
      cap '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
    intro x hx
    rw [hCapBoundary]
    rcases hx with hx|hx
    · exact Or.inl ⟨0,B.first_zero.trans hx.symm⟩
    · exact Or.inl ⟨1,B.first_one.trans hx.symm⟩
  have hOpenCapMarks : Disjoint
      (cap '' {x | x.val ∈ Metric.ball (0 : Plane) 1})
      (M.cover.branch : Set S) := by
    apply Set.disjoint_left.mpr
    intro x hx hm
    exact Set.disjoint_left.mp hOpenCapOffBoundary hx
      (hCornersCapBoundary (hCapMarks x (Set.image_subset_range _ _ hx) hm))
  let protectedObstacle : Set S := (M.cover.branch : Set S) ∪ Kraw
  have hObstacleClosed : IsClosed protectedObstacle :=
    M.cover.branch.finite_toSet.isClosed.union hKraw.isClosed
  have hObstacleInside : Disjoint
      (cap '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) protectedObstacle := by
    apply Set.disjoint_left.mpr
    intro x hx ho
    rcases ho with hm|hk
    · exact Set.disjoint_left.mp hOpenCapMarks hx hm
    · exact Set.disjoint_left.mp hCapK hx hk
  have hObstacleBoundary : ∀ z ∈ modelCurve, capF z ∈ protectedObstacle →
      z=capP ∨ z=capQ := by
    intro z hz ho
    have htrace : capF z ∈ range B.firstSide ∪ range offset := by
      rw [← hCapFA,← hCapFC,← Set.image_union,hCapAC]
      exact Set.mem_image_of_mem capF hz
    have hcorner : capF z ∈ ({B.firstCorner,B.secondCorner} : Set S) := by
      rcases ho with hm|hk
      · rcases htrace with hf|hf
        · exact B.marks_are_corners _ (Set.image_subset_range _ _
            (B.boundary_eq.symm ▸ (show capF z ∈ range B.firstSide ∪ range B.secondSide from Or.inl hf))) hm
        · exact hOffsetMarks _ hf hm
      · rcases htrace with hf|hf
        · exact hmeetRaw ▸ (show capF z ∈ range B.firstSide ∩ Kraw from ⟨hf,hk⟩)
        · exact hOffsetK ▸ (show capF z ∈ range offset ∩ Kraw from ⟨hf,hk⟩)
    rcases hcorner with hc|hc
    · exact Or.inl (hCapF.injective (hc.trans hCapFP.symm))
    · exact Or.inr (hCapF.injective (hc.trans hCapFQ.symm))
  letI : CompactSpace S := M.sphere.symm.compactSpace
  obtain ⟨offsetMove,hOffsetMoveFix,hOffsetMoveSide⟩ :=
    CurveComplex.actual_raw_bigon_supported_replacement capF hCapF capA capC capP capQ
      hCapA hCapC hCapAC protectedObstacle hObstacleClosed hObstacleBoundary
      (by rwa [hCapFInside])
  have hOffsetMoveMarks : ∀ t x, x ∈ M.cover.branch → offsetMove.map (t,x)=x :=
    fun t x hx => hOffsetMoveFix t x (Or.inl hx)
  have hOffsetMoveK : offsetMove.finalMap '' Kraw=Kraw := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [AmbientIsotopy.finalMap,hOffsetMoveFix _ _ (Or.inr hy)] using hy
    · intro hx
      exact ⟨x,hx,hOffsetMoveFix 1 x (Or.inr hx)⟩
  have hOffsetMoveActualSide : offsetMove.finalMap '' range B.firstSide=range offset := by
    simpa only [hCapFA,hCapFC] using hOffsetMoveSide
  obtain ⟨offsetHomeomorph,hOffsetHomeomorph⟩ := offsetMove.homeomorphism_at (1 : Interval)
  have hOffsetHomeomorphMarks : ∀ x, x ∈ M.cover.branch → offsetHomeomorph x=x :=
    fun x hx => (hOffsetHomeomorph x).trans (hOffsetMoveMarks 1 x hx)
  let carrierArc := a.transport offsetHomeomorph hOffsetHomeomorphMarks
  have hOffsetFinalHomeomorph : offsetMove.finalMap=offsetHomeomorph :=
    funext (fun x => (hOffsetHomeomorph x).symm)
  have hCarrierClass : vertex M carrierArc=vertex M a := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨offsetMove,hOffsetMoveMarks,?_⟩
    change offsetMove.finalMap '' a.val.image=
      (a.val.transport offsetHomeomorph hOffsetHomeomorphMarks).image
    rw [MarkedArc.transport_image,hOffsetFinalHomeomorph]
  have hCarrierImage : carrierArc.val.image=replacementTrace := by
    change (a.val.transport offsetHomeomorph hOffsetHomeomorphMarks).image=Kraw ∪ range offset
    rw [MarkedArc.transport_image,← hOffsetFinalHomeomorph,hdecompRaw,Set.image_union,
      hOffsetMoveActualSide,hOffsetMoveK,Set.union_comm]
  have hCarrierOldTrace (j : J) :
      crossings M carrierArc (old j)=replacementTrace ∩ arcInterior M (old j) := by
    change (carrierArc.val.image \ (M.cover.branch : Set S)) ∩ arcInterior M (old j)=_
    rw [hCarrierImage]
    ext x
    constructor
    · rintro ⟨⟨hx,hxm⟩,hxo⟩
      exact ⟨hx,hxo⟩
    · rintro ⟨hx,hxo⟩
      exact ⟨⟨hx,hxo.2⟩,hxo⟩
  have hCarrierOldBudget (j : J) :
      (crossings M carrierArc (old j)).Finite ∧
      (crossings M carrierArc (old j)).ncard ≤
        (crossings M a (old j) \ range B.firstSide).ncard +
        (crossings M b (old j) ∩ range B.secondSide).ncard := by
    rw [hCarrierOldTrace j]
    exact hReplacementOldBudget j
  have hCarrierOffsetTransverse (j : J) (p : S)
      (hp : p ∈ range offset ∩ arcInterior M (old j)) :
      CrossesInDisk M carrierArc (old j) p := by
    obtain ⟨F,hpF,hF0,hMarks,hK,hAxes⟩ := hOffsetWholeCharts j p hp
    have hCarrierAxis (x : S) (hx : x ∈ F.source) :
        x ∈ carrierArc.val.image ↔ F x 1=0 := by
      rw [hCarrierImage]
      change x ∈ Kraw ∪ range offset ↔ F x 1=0
      have hxK : x ∉ Kraw := fun hk => Set.disjoint_left.mp hK hx hk
      simp only [Set.mem_union,hxK,false_or]
      exact (hAxes x hx).1
    apply hSymm
    apply actual_affine_graph_crosses_in_disk M (old j) carrierArc F p hpF hMarks
      (by rw [hF0]; rfl) 0
    · intro x hx
      exact (hAxes x hx).2
    · intro x hx
      rw [hF0,zero_mul,add_zero]
      exact hCarrierAxis x hx
  have hCarrierRetainedChart (j : J) (p : S)
      (hp : p ∈ crossings M a (old j) \ range B.firstSide) :
      ∃ F : OpenPartialHomeomorph S (ℝ × ℝ), p ∈ F.source ∧ F p=(0,0) ∧
        Disjoint F.source (M.cover.branch : Set S) ∧
        (∀ x ∈ F.source, x ∈ carrierArc.val.image ↔ (F x).2=0) ∧
        (∀ x ∈ F.source, x ∈ (old j).val.image ↔ (F x).1=0) := by
    have hpKO : p ∈ Kraw ∩ arcInterior M (old j) := (hRawRetainedCrossings j).symm ▸ hp
    have hpK : p ∈ Kraw := hpKO.1
    have hpOffset : p ∉ range offset := by
      intro hf
      have hc : p ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hOffsetK ▸ (show p ∈ range offset ∩ Kraw from ⟨hf,hpK⟩)
      exact hcorners j p hc hp.1.1.2 hp.1.2.1
    let W : Set S := (range B.firstSide ∪ range offset)ᶜ
    have hW : IsOpen W :=
      ((isCompact_range B.firstSide.continuous).union
        (isCompact_range offset.continuous)).isClosed.isOpen_compl
    have hpW : p ∈ W := by
      rintro (hfirst|hoffset)
      · exact hp.2 hfirst
      · exact hpOffset hoffset
    obtain ⟨F,hpF,hFW,hF0,hMarks,hFirst,hOld⟩ :=
      hMarkedLocalizedCrossingChart a (old j) p ((ha j).2 p hp.1) W hW hpW
    refine ⟨F,hpF,hF0,hMarks,?_,hOld⟩
    intro x hx
    have hxf : x ∉ range B.firstSide := fun hh => hFW hx (Or.inl hh)
    have hxg : x ∉ range offset := fun hh => hFW hx (Or.inr hh)
    have he : x ∈ carrierArc.val.image ↔ x ∈ a.val.image := by
      rw [hCarrierImage,hdecompRaw]
      change x ∈ Kraw ∪ range offset ↔ x ∈ range B.firstSide ∪ Kraw
      simp only [Set.mem_union,hxf,hxg,false_or,or_false]
    exact he.trans (hFirst x hx)
  have hCarrierRetainedTransverse (j : J) (p : S)
      (hp : p ∈ crossings M a (old j) \ range B.firstSide) :
      CrossesInDisk M carrierArc (old j) p := by
    obtain ⟨F,hpF,hF0,hMarks,hFirst,hOld⟩ := hCarrierRetainedChart j p hp
    let L : Plane ≃ₜ ℝ × ℝ :=
      ((EuclideanSpace.equiv (Fin 2) ℝ).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
    let F0 := F.trans L.symm.toOpenPartialHomeomorph
    have hs : F0.source=F.source := by simp [F0,OpenPartialHomeomorph.trans_source]
    have hc0 (x : S) : F0 x 0=(F x).1 := rfl
    have hc1 (x : S) : F0 x 1=(F x).2 := rfl
    apply hSymm
    apply actual_affine_graph_crosses_in_disk M (old j) carrierArc F0 p
      (hs.symm ▸ hpF) (hs.symm ▸ hMarks) (by rw [hc0,hF0]) 0
    · intro x hx
      rw [hc0]
      exact hOld x (hs ▸ hx)
    · intro x hx
      rw [hc1,hc1,hF0,zero_mul,add_zero]
      exact hFirst x (hs ▸ hx)
  have hCarrierOldTransverse (j : J) :
      ∀ p ∈ crossings M carrierArc (old j), CrossesInDisk M carrierArc (old j) p := by
    intro p hp
    rw [hCarrierOldTrace j,hReplacementOldTrace j] at hp
    rcases hp with hRetained|hOffset
    · exact hCarrierRetainedTransverse j p hRetained
    · exact hCarrierOffsetTransverse j p hOffset
  have hCarrierPreservesAnchorMinimum (j : J)
      (hmin : ∀ d : EssentialMarkedArc M, vertex M d=vertex M a →
        (crossings M d (old j)).Finite →
        (crossings M a (old j)).ncard ≤ (crossings M d (old j)).ncard)
      (hsideCost : (crossings M b (old j) ∩ range B.secondSide).ncard ≤
        (crossings M a (old j) ∩ range B.firstSide).ncard) :
      (crossings M carrierArc (old j)).ncard=(crossings M a (old j)).ncard := by
    apply Nat.le_antisymm
    · calc
        (crossings M carrierArc (old j)).ncard ≤
          (crossings M a (old j) \ range B.firstSide).ncard +
          (crossings M b (old j) ∩ range B.secondSide).ncard := (hCarrierOldBudget j).2
        _ ≤ (crossings M a (old j) \ range B.firstSide).ncard +
          (crossings M a (old j) ∩ range B.firstSide).ncard := Nat.add_le_add_left hsideCost _
        _ = (crossings M a (old j)).ncard := by
          rw [Nat.add_comm]
          exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (ha j).1
    · exact hmin carrierArc hCarrierClass (hCarrierOldBudget j).1
  have hCarrierPairTrace : carrierArc.val.image ∩ b.val.image=a.val.image ∩ b.val.image := by
    rw [hCarrierImage]
    change (Kraw ∪ range offset) ∩ b.val.image=a.val.image ∩ b.val.image
    ext x
    constructor
    · rintro ⟨hx,hxb⟩
      rcases hx with hxK|hxf
      · exact ⟨hdecompRaw.symm ▸ (show x ∈ range B.firstSide ∪ Kraw from Or.inr hxK),hxb⟩
      · have hc : x ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
          hOffsetB ▸ (show x ∈ range offset ∩ b.val.image from ⟨hxf,hxb⟩)
        have hfirst : x ∈ range B.firstSide := by
          rcases hc with hc|hc
          · exact ⟨0,B.first_zero.trans hc.symm⟩
          · exact ⟨1,B.first_one.trans hc.symm⟩
        exact ⟨B.first_on_curve hfirst,hxb⟩
    · rintro ⟨hxa,hxb⟩
      have hxSplit : x ∈ range B.firstSide ∪ Kraw := hdecompRaw ▸ hxa
      refine ⟨?_,hxb⟩
      rcases hxSplit with hfirst|hK
      · have hc : x ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
          hfirstclean ▸ (show x ∈ range B.firstSide ∩ b.val.image from ⟨hfirst,hxb⟩)
        right
        rcases hc with hc|hc
        · exact ⟨0,hOffsetFirst.trans hc.symm⟩
        · exact ⟨1,hOffsetSecond.trans hc.symm⟩
      · exact Or.inl hK
  have hCarrierSelectedCrossingsEquality :
      crossings M carrierArc b=crossings M a b := by
    ext x
    constructor
    · rintro ⟨⟨hxc,hxm⟩,hxb,hxbm⟩
      have hxPair : x ∈ a.val.image ∩ b.val.image := hCarrierPairTrace ▸ (show x ∈ carrierArc.val.image ∩ b.val.image from ⟨hxc,hxb⟩)
      exact ⟨⟨hxPair.1,hxm⟩,hxPair.2,hxbm⟩
    · rintro ⟨⟨hxa,hxm⟩,hxb,hxbm⟩
      have hxPair : x ∈ carrierArc.val.image ∩ b.val.image := hCarrierPairTrace.symm ▸ (show x ∈ a.val.image ∩ b.val.image from ⟨hxa,hxb⟩)
      exact ⟨⟨hxPair.1,hxm⟩,hxPair.2,hxbm⟩
  have hCarrierSelectedFinite : (crossings M carrierArc b).Finite :=
    hCarrierSelectedCrossingsEquality.symm ▸ hab
  have hActualUnmarkedRoundChart (p : S)
      (hpCorner : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
      (hpCross : p ∈ crossings M a b) :
      ∃ F : OpenPartialHomeomorph S (ℝ × ℝ), p ∈ F.source ∧ F p=(0,0) ∧
        Disjoint F.source (M.cover.branch : Set S) ∧
        (∀ j, Disjoint F.source (old j).val.image) ∧
        Disjoint F.source (crossings M a b \ {p}) ∧
        Disjoint F.source (({B.firstCorner,B.secondCorner} : Set S) \ {p}) ∧
        (∀ x ∈ F.source, x ∈ a.val.image ↔ (F x).2=0) ∧
        (∀ x ∈ F.source, x ∈ b.val.image ↔ (F x).1=0) := by
    let O : Set S := (⋃ j, (old j).val.image) ∪
      (crossings M a b \ {p}) ∪ (({B.firstCorner,B.secondCorner} : Set S) \ {p})
    have hO : IsClosed O := by
      apply IsClosed.union
      · apply IsClosed.union
        · exact isClosed_iUnion_of_finite (fun j =>
            (isCompact_range (old j).val.continuous).isClosed)
        · exact hab.sdiff.isClosed
      · exact (Set.toFinite _).isClosed
    have hpO : p ∉ O := by
      rintro ((hOld|hRetained)|hOther)
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hOld
        exact hcorners j p hpCorner hpCross.1.2 hj
      · exact hRetained.2 (Set.mem_singleton p)
      · exact hOther.2 (Set.mem_singleton p)
    obtain ⟨F,hpF,hFO,hF0,hMarks,hA,hB⟩ :=
      hMarkedLocalizedCrossingChart a b p (htab p hpCross) Oᶜ hO.isOpen_compl hpO
    refine ⟨F,hpF,hF0,hMarks,?_,?_,?_,hA,hB⟩
    · intro j
      exact Set.disjoint_left.mpr (fun x hx hj =>
        hFO hx (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨j,hj⟩))))
    · exact Set.disjoint_left.mpr (fun x hx hj => hFO hx (Or.inl (Or.inr hj)))
    · exact Set.disjoint_left.mpr (fun x hx hj => hFO hx (Or.inr hj))
  have hActualUnmarkedRoundCrossing :
      ∃ p ∈ ({B.firstCorner,B.secondCorner} : Set S), p ∈ crossings M a b := by
    rcases hhit with hp|hp
    · exact ⟨B.firstCorner,by simp,hp⟩
    · exact ⟨B.secondCorner,by simp,hp⟩
  obtain ⟨roundCorner,hRoundCorner,hRoundCross⟩ := hActualUnmarkedRoundCrossing
  obtain ⟨roundChart,hRoundChart,hRoundZero,hRoundMarks,hRoundOld,
    hRoundRetained,hRoundOther,hRoundA,hRoundB⟩ :=
    hActualUnmarkedRoundChart roundCorner hRoundCorner hRoundCross
  have hActualSignedRoundBypass (σ τ : Bool) :
      ∃ f : C(unitInterval,S), IsEmbedding f ∧
        range f ⊆ roundChart.source ∧
        range f ∩ a.val.image={f 0} ∧
        range f ∩ b.val.image={f 1} ∧
        roundCorner ∉ range f ∧
        Disjoint (range f) (M.cover.branch : Set S) ∧
        (∀ j, Disjoint (range f) (old j).val.image) ∧
        Disjoint (range f) (crossings M a b \ {roundCorner}) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ t,
          roundChart (f t)=
            ((if σ then 1 else -1)*ε*(1-(t:ℝ)),
             (if τ then 1 else -1)*ε*(t:ℝ)) := by
    have hzero : (0 : ℝ × ℝ) ∈ roundChart.target := by
      change (0,0) ∈ roundChart.target
      rw [← hRoundZero]
      exact roundChart.map_source hRoundChart
    obtain ⟨r,hr,hrTarget⟩ := Metric.isOpen_iff.mp roundChart.open_target 0 hzero
    let ε : ℝ := r/2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hεr : ε < r := by dsimp [ε]; linarith
    let sx : ℝ := if σ then 1 else -1
    let sy : ℝ := if τ then 1 else -1
    have hsx : sx ≠ 0 := by cases σ <;> norm_num [sx]
    have hsy : sy ≠ 0 := by cases τ <;> norm_num [sy]
    have hsxa : |sx|=1 := by cases σ <;> norm_num [sx]
    have hsya : |sy|=1 := by cases τ <;> norm_num [sy]
    let z : unitInterval → ℝ × ℝ := fun t =>
      (sx*ε*(1-(t:ℝ)),sy*ε*(t:ℝ))
    have hzTarget (t : unitInterval) : z t ∈ roundChart.target := by
      apply hrTarget
      rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      simp only [Prod.fst_zero,Prod.snd_zero,sub_zero]
      dsimp [z]
      rw [abs_mul,abs_mul,abs_mul,abs_mul,hsxa,hsya,
        abs_of_pos hε,abs_of_nonneg (sub_nonneg.mpr t.property.2),
        abs_of_nonneg t.property.1]
      simp only [one_mul]
      exact max_lt (by nlinarith [t.property.1]) (by nlinarith [t.property.2])
    let f : C(unitInterval,S) := ⟨fun t => roundChart.symm (z t),
      roundChart.symm.continuousOn.comp_continuous (by dsimp [z]; fun_prop) hzTarget⟩
    have hfSource (t : unitInterval) : f t ∈ roundChart.source :=
      roundChart.symm.map_source (hzTarget t)
    have hfCoord (t : unitInterval) : roundChart (f t)=z t :=
      roundChart.right_inv (hzTarget t)
    have hinj : Function.Injective f := by
      intro t u he
      have hy := congrArg Prod.snd (congrArg roundChart he)
      rw [hfCoord,hfCoord] at hy
      change sy*ε*(t:ℝ)=sy*ε*(u:ℝ) at hy
      exact Subtype.ext (mul_left_cancel₀ (mul_ne_zero hsy (ne_of_gt hε)) hy)
    have hfa (t : unitInterval) : f t ∈ a.val.image ↔ t=0 := by
      rw [hRoundA (f t) (hfSource t),hfCoord]
      change sy*ε*(t:ℝ)=0 ↔ t=0
      constructor
      · intro ht
        exact Subtype.ext ((mul_eq_zero.mp ht).resolve_left (mul_ne_zero hsy (ne_of_gt hε)))
      · rintro rfl; norm_num
    have hfb (t : unitInterval) : f t ∈ b.val.image ↔ t=1 := by
      rw [hRoundB (f t) (hfSource t),hfCoord]
      change sx*ε*(1-(t:ℝ))=0 ↔ t=1
      constructor
      · intro ht
        have ht1 := (mul_eq_zero.mp ht).resolve_left (mul_ne_zero hsx (ne_of_gt hε))
        apply Subtype.ext
        change (t:ℝ)=1
        linarith
      · rintro rfl; norm_num
    have hsub : range f ⊆ roundChart.source := by
      rintro x ⟨t,rfl⟩; exact hfSource t
    refine ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,hsub,?_,?_,?_,
      hRoundMarks.mono_left hsub,(fun j => (hRoundOld j).mono_left hsub),
      hRoundRetained.mono_left hsub,ε,hε,?_⟩
    · ext x
      constructor
      · rintro ⟨⟨t,rfl⟩,ht⟩; rw [hfa] at ht; simp [ht]
      · rintro rfl; exact ⟨Set.mem_range_self _,(hfa 0).mpr rfl⟩
    · ext x
      constructor
      · rintro ⟨⟨t,rfl⟩,ht⟩; rw [hfb] at ht; simp [ht]
      · rintro rfl; exact ⟨Set.mem_range_self _,(hfb 1).mpr rfl⟩
    · rintro ⟨t,ht⟩
      have hc : z t=(0,0) := by rw [← hfCoord,ht,hRoundZero]
      have ht0 : t=0 := (hfa t).mp (ht.symm ▸ hRoundCross.1.1)
      have ht1 : t=1 := (hfb t).mp (ht.symm ▸ hRoundCross.2.1)
      have := congrArg Subtype.val (ht0.symm.trans ht1)
      norm_num at this
    · exact hfCoord
  have hRoundedStrictOriginalConsumer (d : EssentialMarkedArc M)
      (hRetained : crossings M d b ⊆ crossings M a b)
      (hRemoved : roundCorner ∉ crossings M d b) :
      (crossings M d b).Finite ∧
        (crossings M d b).ncard < (crossings M a b).ncard := by
    have hsub : crossings M d b ⊆ crossings M a b \ {roundCorner} := by
      intro x hx
      refine ⟨hRetained hx,?_⟩
      rintro rfl
      exact hRemoved hx
    exact ⟨hab.subset hRetained,
      lt_of_le_of_lt (Set.ncard_le_ncard hsub hab.sdiff)
        (Set.ncard_sdiff_singleton_lt_of_mem hRoundCross hab)⟩
  let α : ℝ := commonδ/2
  let β : ℝ := 1-commonδ/2
  have hα : 0 < α := half_pos hCommonδ
  have hβ : β < 1 := by dsimp [β]; linarith [hCommonδ]
  have hαβ : α < β := by dsimp [α,β]; linarith [hCommonδhalf]
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
  have hContactsInGlobalCore : P ⊆ range core := by
    intro p hp
    obtain ⟨j,hj⟩ := hPold p hp
    obtain ⟨t,ht⟩ := hj.2
    have htT : t ∈ T := by
      change B.secondSide t ∈ P
      exact ht.symm ▸ hp
    rw [hCoreRange]
    refine ⟨t.val,?_,?_⟩
    · have hbds := hCommonContactCore t htT
      dsimp [α,β]
      constructor <;> linarith [hbds.1,hbds.2,hCommonδ]
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
  have hActualGlobalExteriorBank (x : S) (hx : x ∈ globalE.source ∩ bankO) :
      x ∉ range B.disk ↔ globalE x 1 < 0 := by
    constructor
    · intro hxD
      by_contra hn
      have hy : 0 ≤ globalE x 1 := le_of_not_gt hn
      by_cases hz : globalE x 1=0
      · have hxb : x ∈ b.val.image := (hGlobalEAxis x hx.1).mpr hz
        have hxSide : x ∈ range B.secondSide :=
          (hF1SideLocal x (hGlobalESource ▸ hx.1)).mp hxb
        apply hxD
        apply image_subset_range _ _
        exact B.boundary_eq.symm ▸ (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inr hxSide)
      · have hxOpen : x ∈ B.openInterior := (hRealBank x hx).mpr (lt_of_le_of_ne hy (Ne.symm hz))
        obtain ⟨z,hz,rfl⟩ := hxOpen
        exact hxD (Set.mem_range_self z)
    · intro hy hxD
      have hxOpen : x ∉ B.openInterior := by
        intro hh
        have hp := (hRealBank x hx).mp hh
        linarith
      obtain ⟨z,rfl⟩ := hxD
      have hzSphere : dist z.val (0:Plane)=1 := by
        apply le_antisymm z.property
        by_contra hn
        exact hxOpen ⟨z,lt_of_not_ge hn,rfl⟩
      have hzBoundary : B.disk z ∈ range B.firstSide ∪ range B.secondSide :=
        B.boundary_eq ▸ (show B.disk z ∈ B.disk '' {w | w.val ∈ Metric.sphere (0:Plane) 1} from
          ⟨z,hzSphere,rfl⟩)
      rcases hzBoundary with hzFirst|hzSecond
      · exact Set.disjoint_left.mp hF1FirstFree (hGlobalESource ▸ hx.1) hzFirst
      · have hzAxis : globalE (B.disk z) 1=0 :=
          (hGlobalEAxis _ hx.1).mp (B.second_on_curve hzSecond)
        linarith
  have hContactInBankO (p : P) : p.val ∈ globalE.source ∩ bankO := by
    obtain ⟨u,hu⟩ := hContactsInGlobalCore p.property
    obtain ⟨j,hj⟩ := hPold p.val p.property
    obtain ⟨t,ht⟩ := hj.2
    have htT : t ∈ T := by
      change B.secondSide t ∈ P
      exact ht.symm ▸ p.property
    have hθt : α+u.val*(β-α)=t.val := by
      apply hψInjective _ _ ⟨(hCoreθ01 u).1.le,(hCoreθ01 u).2.le⟩ t.property
      exact hu.trans (by simpa [ψ,Function.comp_def,Set.projIcc_of_mem zero_le_one t.property] using ht.symm)
    have hu0 : (0:Interval)<u := by
      change 0<u.val
      have hh := (hCommonContactCore t htT).1
      dsimp [α] at hθt
      nlinarith [hCommonδ,sub_pos.mpr hαβ]
    have hu1 : u<(1:Interval) := by
      change u.val<1
      have hh := (hCommonContactCore t htT).2
      dsimp [β] at hθt
      nlinarith [hCommonδ,sub_pos.mpr hαβ]
    have hpS : p.val ∈ globalF1.source := hu ▸ hCoreF1Source (Set.mem_range_self u)
    have hpx : globalF1 p.val 0=χ u := by
      rw [← hu,hGlobalF1Value,hCoreCoords]
      rfl
    have hpy : globalF1 p.val 1=0 :=
      (hF1Axis p.val hpS).mp (B.second_on_curve ⟨t,ht⟩)
    refine ⟨hGlobalESource.symm ▸ hpS,?_⟩
    change χ 0<globalF1 p.val 0 ∧ globalF1 p.val 0<χ 1 ∧
      -globalε<globalF1 p.val 1 ∧ globalF1 p.val 1<globalε
    rw [hpx,hpy]
    exact ⟨hχ hu0,hχ hu1,neg_neg_of_pos hGlobalε,hGlobalε⟩
  let mirrorY : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk (z 0) (-z 1)
    invFun := fun z => Plane.mk (z 0) (-z 1)
    left_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk]
    right_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let negativeBase := globalE.restrOpen (globalE.source ∩ bankO) hBankOOpen
  let negativeE := negativeBase.trans mirrorY.toOpenPartialHomeomorph
  have hNegativeSource : negativeE.source=globalE.source ∩ bankO := by
    simp [negativeE,negativeBase,OpenPartialHomeomorph.trans_source]
  have hNegativeY (x : S) : negativeE x 1= -globalE x 1 := rfl
  have hNegativeAxis (x : S) (hx : x ∈ negativeE.source) :
      x ∈ b.val.image ↔ negativeE x 1=0 := by
    rw [hNegativeY,neg_eq_zero]
    exact hGlobalEAxis x (hNegativeSource ▸ hx).1
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
      have hnot : x ∉ Kraw ∪ Kother := fun hk => Set.disjoint_left.mp (hContactURemainders p) hx hk
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
  have hActualOppositeBankPatch (p : P) :
      ∃ F : OpenPartialHomeomorph S Plane, ∃ δ H : ℝ,
        p.val ∈ F.source ∧ F p.val=0 ∧
        (∀ x ∈ F.source, x ∈ b.val.image ↔ F x 1=0) ∧
        (∃ v w : {j : J // p.val ∈ (old j).val.image} → Plane,
          (∀ j, 0<v j 1) ∧ (∀ j, w j 1<0) ∧
          ∀ j x, x ∈ F.source →
            (x ∈ (old j.val).val.image ↔ F x ∈ segment ℝ (0:Plane) (v j) ∪ segment ℝ (0:Plane) (w j))) ∧
        F.source ⊆ contactU p ∩ negativeE.source ∧ 0<δ ∧ 0<H ∧
        Plane.mk (-δ) 0 ∈ F.target ∧ Plane.mk δ 0 ∈ F.target ∧
        (∀ h : ℝ, 0<h → h<H → segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ F.target) ∧
        ∀ h : ℝ, 0<h → h<H → ∃ f : C(Interval,S),
          IsEmbedding f ∧ range f ⊆ F.source ∧
          range f=F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          f 0=F.symm (Plane.mk (-δ) h) ∧ f 1=F.symm (Plane.mk δ h) ∧
          Disjoint (range f) (range B.disk) ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧ Disjoint (range f) b.val.image ∧
          ∀ j, f 0 ∉ (old j).val.image ∧ f 1 ∉ (old j).val.image ∧
            (range f ∩ (old j).val.image).Finite ∧
            (range f ∩ (old j).val.image).ncard ≤ if p.val ∈ (old j).val.image then 1 else 0 := by
    obtain ⟨F,δ,H,hpF,hFp,hAxis,hModel,hFS,hδ,hH,hl,hr,hFullAxis,hsegments,hpaths⟩ :=
      hRetainedBankedSourceContactPatch negativeE hNegativeAxis p (hNegativeSource.symm ▸ hContactInBankO p)
    refine ⟨F,δ,H,hpF,hFp,hAxis,hModel,hFS,hδ,hH,hl,hr,hsegments,?_⟩
    intro h hh hhH
    obtain ⟨f,hfi,hfS,hfr,hf0,hf1,hBank,hMarks,hB,hCounts⟩ := hpaths h hh hhH
    refine ⟨f,hfi,hfS,hfr,hf0,hf1,?_,hMarks,hB,hCounts⟩
    apply Set.disjoint_left.mpr
    intro x hx hxD
    have hxBank : x ∈ globalE.source ∩ bankO := hNegativeSource ▸ (hFS (hfS hx)).2
    have hxy : globalE x 1<0 := by
      have hh := hBank x hx
      rw [hNegativeY] at hh
      linarith
    exact (hActualGlobalExteriorBank x hxBank).mpr hxy hxD
  choose oppositePatchF oppositePatchδ oppositePatchH hOppositePatchPoint hOppositePatchCenter
    hOppositePatchAxis hOppositePatchModel hOppositePatchSource
    hOppositePatchδ hOppositePatchH hOppositeLeft hOppositeRight
    hOppositeSegments hOppositeFamily using hActualOppositeBankPatch
  have hUniformOppositeHeight : ∃ H : ℝ, 0<H ∧ ∀ p : P, H<oppositePatchH p := by
    let O : Set ℝ := {h | ∀ p : P, h<oppositePatchH p}
    have hO : IsOpen O := by
      have hh : O=⋂ p : P, Set.Iio (oppositePatchH p) := by ext h; simp [O]
      rw [hh]
      exact isOpen_iInter_of_finite (fun p => isOpen_Iio)
    have hz : (0:ℝ) ∈ O := hOppositePatchH
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO 0 hz
    refine ⟨ε/2,half_pos hε,?_⟩
    exact hball (by rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hε)]; linarith)
  obtain ⟨oppositeH,hOppositeH,hOppositeHlt⟩ := hUniformOppositeHeight
  have hActualUniformOppositePatchUnion (h : ℝ) (hh : 0<h) (hhH : h<oppositeH) :
      ∃ f : P → C(Interval,S),
        (∀ p, IsEmbedding (f p) ∧ range (f p) ⊆ (oppositePatchF p).source ∧
          (f p) 0=(oppositePatchF p).symm (Plane.mk (-oppositePatchδ p) h) ∧
          (f p) 1=(oppositePatchF p).symm (Plane.mk (oppositePatchδ p) h) ∧
          Disjoint (range (f p)) (range B.disk) ∧
          Disjoint (range (f p)) (M.cover.branch : Set S) ∧
          Disjoint (range (f p)) b.val.image) ∧
        (∀ p q, p≠q → Disjoint (range (f p)) (range (f q))) ∧
        ∀ j, (⋃ p, range (f p) ∩ (old j).val.image).Finite ∧
          (⋃ p, range (f p) ∩ (old j).val.image).ncard ≤
            (crossings M b (old j) ∩ range B.secondSide).ncard := by
    have hFamilies (p : P) := hOppositeFamily p h hh (hhH.trans (hOppositeHlt p))
    choose f hfembed hfsource hfrange hfleft hfright hfdisk hfmarks hfb hfcount
      using hFamilies
    refine ⟨f,?_,?_,?_⟩
    · intro p
      exact ⟨hfembed p,hfsource p,hfleft p,hfright p,hfdisk p,hfmarks p,hfb p⟩
    · intro p q hpq
      exact (hContactUDisjoint p q hpq).mono
        (fun x hx => (hOppositePatchSource p (hfsource p hx)).1)
        (fun x hx => (hOppositePatchSource q (hfsource q hx)).1)
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
  choose oppositeLeft oppositeRight hOppositeLeftFormula hOppositeRightFormula
    hOppositeEndpointsSource hOppositeEndpointsCoords hOppositeLeftBaseline
    hOppositeRightBaseline using
      (fun p : P => hActualOffsetEndpointFamilies (oppositePatchF p) (oppositePatchδ p)
        oppositeH hOppositeH (hOppositeLeft p) (hOppositeRight p)
        (fun h hh hhH => hOppositeSegments p h hh (hhH.trans (hOppositeHlt p))))
  have hActualMovingUnmarkedRoundFamily (σ τ : Bool) :
      ∃ A : S, ∃ L : C(Interval,S), A ∈ a.val.image ∧ A ∉ b.val.image ∧
        L 0 ∈ b.val.image ∧ L 0 ∉ a.val.image ∧
        (∀ t, L t ∈ roundChart.source) ∧
        ∀ t : Interval, 0<t.val → ∃ f : C(Interval,S),
          IsEmbedding f ∧ f 0=A ∧ f 1=L t ∧ range f ⊆ roundChart.source ∧
          range f ∩ a.val.image={A} ∧ Disjoint (range f) b.val.image ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧
          (∀ j, Disjoint (range f) (old j).val.image) ∧
          Disjoint (range f) (crossings M a b \ {roundCorner}) := by
    have hzero : (0 : ℝ × ℝ) ∈ roundChart.target := by
      change (0,0) ∈ roundChart.target
      rw [← hRoundZero]
      exact roundChart.map_source hRoundChart
    obtain ⟨r,hr,hrTarget⟩ := Metric.isOpen_iff.mp roundChart.open_target 0 hzero
    let ε : ℝ := r/2
    have hε : 0<ε := by dsimp [ε]; linarith
    have hεr : ε<r := by dsimp [ε]; linarith
    let sx : ℝ := if σ then 1 else -1
    let sy : ℝ := if τ then 1 else -1
    have hsx : sx≠0 := by cases σ <;> norm_num [sx]
    have hsy : sy≠0 := by cases τ <;> norm_num [sy]
    have hsxa : |sx|=1 := by cases σ <;> norm_num [sx]
    have hsya : |sy|=1 := by cases τ <;> norm_num [sy]
    have hbox (x y : ℝ) (hx : 0≤x ∧ x≤ε) (hy : 0≤y ∧ y≤ε) :
        (sx*x,sy*y) ∈ roundChart.target := by
      apply hrTarget
      rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      simp only [Prod.fst_zero,Prod.snd_zero,sub_zero]
      rw [abs_mul,abs_mul,hsxa,hsya,abs_of_nonneg hx.1,abs_of_nonneg hy.1]
      simp only [one_mul]
      exact max_lt (hx.2.trans_lt hεr) (hy.2.trans_lt hεr)
    let A : S := roundChart.symm (sx*ε,0)
    have hAt : (sx*ε,0) ∈ roundChart.target := by
      simpa using hbox ε 0 ⟨hε.le,le_rfl⟩ ⟨le_rfl,hε.le⟩
    have hAS : A ∈ roundChart.source := roundChart.map_target hAt
    have hAC : roundChart A=(sx*ε,0) := roundChart.right_inv hAt
    let lz : Interval → ℝ × ℝ := fun t => (sx*(ε/2)*t.val,sy*ε)
    have hlz (t : Interval) : lz t ∈ roundChart.target := by
      have hx : 0≤ε/2*t.val ∧ ε/2*t.val≤ε := by
        constructor <;> nlinarith [t.property.1,t.property.2]
      simpa [lz,mul_assoc] using hbox (ε/2*t.val) ε hx ⟨hε.le,le_rfl⟩
    let L : C(Interval,S) := ⟨fun t => roundChart.symm (lz t),
      roundChart.symm.continuousOn.comp_continuous (by dsimp [lz]; fun_prop) hlz⟩
    have hLS (t : Interval) : L t ∈ roundChart.source := roundChart.map_target (hlz t)
    have hLC (t : Interval) : roundChart (L t)=lz t := roundChart.right_inv (hlz t)
    refine ⟨A,L,?_,?_,?_,?_,hLS,?_⟩
    · exact (hRoundA A hAS).mpr (by rw [hAC])
    · intro hh
      have hzero := (hRoundB A hAS).mp hh
      rw [hAC] at hzero
      exact mul_ne_zero hsx (ne_of_gt hε) hzero
    · exact (hRoundB (L 0) (hLS 0)).mpr (by rw [hLC]; simp [lz])
    · intro hh
      have hzero := (hRoundA (L 0) (hLS 0)).mp hh
      rw [hLC] at hzero
      exact mul_ne_zero hsy (ne_of_gt hε) hzero
    · intro t ht
      let c : ℝ := ε/2*t.val
      have hc : 0<c := mul_pos (half_pos hε) ht
      have hcε : c≤ε := by dsimp [c]; nlinarith [t.property.2]
      let z : Interval → ℝ × ℝ := fun u =>
        (sx*(ε*(1-u.val)+c*u.val),sy*ε*u.val)
      have hz (u : Interval) : z u ∈ roundChart.target := by
        have hx : 0≤ε*(1-u.val)+c*u.val ∧ ε*(1-u.val)+c*u.val≤ε := by
          constructor <;> nlinarith [u.property.1,u.property.2,
            mul_nonneg hc.le u.property.1,mul_nonneg hε.le (sub_nonneg.mpr u.property.2),
            mul_nonneg (sub_nonneg.mpr hcε) u.property.1]
        have hy : 0≤ε*u.val ∧ ε*u.val≤ε := by
          constructor <;> nlinarith [u.property.1,u.property.2]
        simpa [z,mul_assoc] using hbox _ _ hx hy
      let f : C(Interval,S) := ⟨fun u => roundChart.symm (z u),
        roundChart.symm.continuousOn.comp_continuous (by dsimp [z]; fun_prop) hz⟩
      have hfS (u : Interval) : f u ∈ roundChart.source := roundChart.map_target (hz u)
      have hfC (u : Interval) : roundChart (f u)=z u := roundChart.right_inv (hz u)
      have hinj : Function.Injective f := by
        intro u v he
        have hh := congrArg Prod.snd (congrArg roundChart he)
        rw [hfC,hfC] at hh
        exact Subtype.ext (mul_left_cancel₀ (mul_ne_zero hsy (ne_of_gt hε)) hh)
      have hsub : range f ⊆ roundChart.source := by rintro x ⟨u,rfl⟩; exact hfS u
      have hf0 : f 0=A := by
        change roundChart.symm (z 0)=roundChart.symm (sx*ε,0)
        congr 1
        simp [z]
      have hf1 : f 1=L t := by
        change roundChart.symm (z 1)=roundChart.symm (lz t)
        congr 1
        simp [z,lz,c,mul_assoc]
      refine ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,hf0,hf1,hsub,?_,?_,
        hRoundMarks.mono_left hsub,(fun j => (hRoundOld j).mono_left hsub),
        hRoundRetained.mono_left hsub⟩
      · ext x
        constructor
        · rintro ⟨⟨u,rfl⟩,hu⟩
          have hy := (hRoundA (f u) (hfS u)).mp hu
          rw [hfC] at hy
          have hu0 : u=0 := Subtype.ext ((mul_eq_zero.mp hy).resolve_left (mul_ne_zero hsy (ne_of_gt hε)))
          simp [hu0,hf0]
        · rintro rfl
          exact ⟨⟨0,hf0⟩,(hRoundA A hAS).mpr (by rw [hAC])⟩
      · apply Set.disjoint_left.mpr
        rintro x ⟨u,rfl⟩ hu
        have hx := (hRoundB (f u) (hfS u)).mp hu
        rw [hfC] at hx
        have hx0 : ε*(1-u.val)+c*u.val=0 := (mul_eq_zero.mp hx).resolve_left hsx
        have hpos : 0<ε*(1-u.val)+c*u.val := by
          by_cases hu0 : u.val=0
          · simp [hu0,hε]
          · have hup : 0<u.val := lt_of_le_of_ne u.property.1 (Ne.symm hu0)
            have := mul_pos hc hup
            nlinarith [mul_nonneg hε.le (sub_nonneg.mpr u.property.2)]
        linarith
  have hActualOppositePatchWholeCrossingChart (p : P) (j : J) (x : S)
      (h : ℝ) (hh : 0<h) (hxF : x ∈ (oppositePatchF p).source)
      (hxOld : x ∈ arcInterior M (old j)) (hxHeight : oppositePatchF p x 1=h) :
      ∃ G : OpenPartialHomeomorph S Plane, x ∈ G.source ∧ G x=0 ∧
        G.source ⊆ (oppositePatchF p).source ∧
        Disjoint G.source (M.cover.branch : Set S) ∧
        (∀ y ∈ G.source, y ∈ (old j).val.image ↔ G y 0=0) ∧
        ∀ y, oppositePatchF p y 1=h → G y 1=0 := by
    have hxU : x ∈ contactU p := (hOppositePatchSource p hxF).1
    have hj : p.val ∈ (old j).val.image := by
      by_contra hn
      exact Set.disjoint_left.mp (hContactUNonincident p j hn) hxU hxOld.1
    obtain ⟨v,w,hv,hw,hmodel⟩ := hOppositePatchModel p
    have hFMarks : Disjoint (oppositePatchF p).source (M.cover.branch : Set S) :=
      (hContactUMarks p).mono_left (fun y hy => (hOppositePatchSource p hy).1)
    exact actual_marked_positive_radial_horizontal_crossing_chart M (old j) x hxOld
      (oppositePatchF p) hxF hFMarks (v ⟨j,hj⟩) (w ⟨j,hj⟩)
      (hv ⟨j,hj⟩) (hw ⟨j,hj⟩) (hmodel ⟨j,hj⟩) h hh hxHeight
  have hActualSelectedSideWholeRay (side : C(Interval,S)) (hside : IsEmbedding side)
      (F : OpenPartialHomeomorph S (ℝ × ℝ)) (h0 : side 0 ∈ F.source)
      (hF0 : F (side 0)=(0,0))
      (hAxis : ∀ t : Interval, side t ∈ F.source → (F (side t)).2=0) :
      ∃ G : OpenPartialHomeomorph S (ℝ × ℝ), ∃ σ ell : ℝ,
        G.source ⊆ F.source ∧ (∀ x, G x=F x) ∧ side 0 ∈ G.source ∧
        (σ=-1 ∨ σ=1) ∧ 0<ell ∧
        (∀ x ∈ G.source, x ∈ range side → 0≤σ*(G x).1) ∧
        ∀ x ∈ Icc (0:ℝ) ell, (σ*x,0) ∈ G.target ∧ G.symm (σ*x,0) ∈ range side := by
    have hOpen : IsOpen (side ⁻¹' F.source) := F.open_source.preimage side.continuous
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hOpen 0 h0
    let r : ℝ := min ε 1/2
    have hr : 0<r := half_pos (lt_min hε zero_lt_one)
    have hrε : r<ε := by dsimp [r]; linarith [min_le_left ε 1]
    have hr1 : r<1 := by dsimp [r]; linarith [min_le_right ε 1]
    let k : Interval → Interval := fun t => ⟨r*t.val,
      mul_nonneg hr.le t.property.1,
      (mul_le_of_le_one_right hr.le t.property.2).trans hr1.le⟩
    have hk : Continuous k := by dsimp [k]; fun_prop
    have hS (t : Interval) : side (k t) ∈ F.source := hball (by
      change dist (k t) (0:Interval)<ε
      rw [Subtype.dist_eq,Real.dist_eq]
      change |r*t.val-0|<ε
      rw [sub_zero,abs_of_nonneg (mul_nonneg hr.le t.property.1)]
      exact (mul_le_of_le_one_right hr.le t.property.2).trans_lt hrε)
    let β : Interval → ℝ := fun t => (F (side (k t))).1
    have hβ : Continuous β := continuous_fst.comp
      (F.continuousOn.comp_continuous (side.continuous.comp hk) hS)
    have hk0 : k 0=0 := by apply Subtype.ext; simp [k]
    have hβ0 : β 0=0 := by dsimp [β]; rw [hk0,hF0]
    have hβinj : Function.Injective β := by
      intro u v he
      have hcoord : F (side (k u))=F (side (k v)) :=
        Prod.ext he ((hAxis (k u) (hS u)).trans (hAxis (k v) (hS v)).symm)
      have hku := hside.injective (F.injOn (hS u) (hS v) hcoord)
      have hh := congrArg Subtype.val hku
      exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hr) hh)
    let tail : Set S := side '' {t : Interval | r≤t.val}
    have htail : IsCompact tail :=
      (isClosed_le continuous_const continuous_subtype_val).isCompact.image side.continuous
    have hpTail : side 0 ∉ tail := by
      rintro ⟨t,ht,he⟩
      have ht0 := hside.injective he
      subst t
      exact not_le_of_gt hr ht
    let G := F.restrOpen tailᶜ htail.isClosed.isOpen_compl
    have hGs : G.source=F.source ∩ tailᶜ := rfl
    have hGvalue (x : S) : G x=F x := rfl
    have hG0 : side 0 ∈ G.source := ⟨h0,hpTail⟩
    have hsideLocal (x : S) (hx : x ∈ G.source) (hxs : x ∈ range side) :
        ∃ t : Interval, side (k t)=x := by
      obtain ⟨u,rfl⟩ := hxs
      have hur : u.val<r := by
        by_contra hn
        exact hx.2 ⟨u,le_of_not_gt hn,rfl⟩
      let t : Interval := ⟨u.val/r,div_nonneg u.property.1 hr.le,
        ((div_lt_one hr).mpr hur).le⟩
      refine ⟨t,?_⟩
      congr 1
      apply Subtype.ext
      change r*(u.val/r)=u.val
      field_simp
    let half : Interval := ⟨1/2,by norm_num,by norm_num⟩
    have hhalf0 : (0:Interval)<half := by change (0:ℝ)<1/2; norm_num
    have hhalf1 : half<(1:Interval) := by change (1/2:ℝ)<1; norm_num
    obtain hm|hm := hβ.strictMono_of_inj_boundedOrder' hβinj
    · have hhalf : 0<β half := hβ0 ▸ hm hhalf0
      refine ⟨G,1,β half,fun x hx => hx.1,hGvalue,hG0,Or.inr rfl,hhalf,?_,?_⟩
      · intro x hx hxs
        obtain ⟨t,ht⟩ := hsideLocal x hx hxs
        simp only [one_mul,hGvalue]
        change 0≤(F x).1
        rw [← ht]
        exact hβ0 ▸ hm.monotone (show (0:Interval)≤t from t.property.1)
      · intro x hx
        simp only [one_mul]
        have hRange := (isPreconnected_range hβ).ordConnected
        obtain ⟨t,ht⟩ := hRange.uIcc_subset (Set.mem_range_self 0) (Set.mem_range_self half)
          (show x ∈ uIcc (β 0) (β half) by simpa [hβ0,uIcc_of_le hhalf.le] using hx)
        have hthalf : t≤half := hm.le_iff_le.mp (ht ▸ hx.2)
        have hkt : (k t).val<r := by
          change r*t.val<r
          change t.val≤1/2 at hthalf
          nlinarith
        have hnot : side (k t) ∉ tail := by
          rintro ⟨u,hu,he⟩
          have hh := congrArg Subtype.val (hside.injective he)
          change r≤u.val at hu
          linarith
        have hsrc : side (k t) ∈ G.source := ⟨hS t,hnot⟩
        have he : G (side (k t))=(x,0) := Prod.ext ht (hAxis (k t) (hS t))
        refine ⟨by rw [← he]; exact G.map_source hsrc,?_⟩
        rw [← he,G.left_inv hsrc]
        exact Set.mem_range_self _
    · have hhalf : β half<0 := hβ0 ▸ hm hhalf0
      refine ⟨G,-1,-β half,fun x hx => hx.1,hGvalue,hG0,Or.inl rfl,neg_pos.mpr hhalf,?_,?_⟩
      · intro x hx hxs
        obtain ⟨t,ht⟩ := hsideLocal x hx hxs
        simp only [neg_one_mul,hGvalue]
        change 0≤ -(F x).1
        rw [← ht]
        exact neg_nonneg.mpr (hβ0 ▸ hm.antitone (show (0:Interval)≤t from t.property.1))
      · intro x hx
        have hRange := (isPreconnected_range hβ).ordConnected
        obtain ⟨t,ht⟩ := hRange.uIcc_subset (Set.mem_range_self 0) (Set.mem_range_self half)
          (show -x ∈ uIcc (β 0) (β half) by rw [hβ0,uIcc_of_ge hhalf.le]; constructor <;> linarith [hx.1,hx.2])
        have hthalf : t≤half := hm.le_iff_ge.mp (show β half≤β t by rw [ht]; linarith [hx.2])
        have hkt : (k t).val<r := by
          change r*t.val<r
          change t.val≤1/2 at hthalf
          nlinarith
        have hnot : side (k t) ∉ tail := by
          rintro ⟨u,hu,he⟩
          have hh := congrArg Subtype.val (hside.injective he)
          change r≤u.val at hu
          linarith
        have hsrc : side (k t) ∈ G.source := ⟨hS t,hnot⟩
        have he : G (side (k t))=(-1*x,0) := by
          apply Prod.ext
          · change β t= -1*x
            rw [ht]; ring
          · exact hAxis (k t) (hS t)
        refine ⟨by rw [← he]; exact G.map_source hsrc,?_⟩
        rw [← he,G.left_inv hsrc]
        exact Set.mem_range_self _
  have hActualUnmarkedCornerWholeAxes (p : S)
      (hpCorner : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
      (hpCross : p ∈ crossings M a b)
      (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
      ∃ F : OpenPartialHomeomorph S (ℝ × ℝ), ∃ ell : ℝ,
        p ∈ F.source ∧ F p=(0,0) ∧ F.source ⊆ W ∧ 0<ell ∧
        Disjoint F.source (M.cover.branch : Set S) ∧
        (∀ j, Disjoint F.source (old j).val.image) ∧
        Disjoint F.source (crossings M a b \ {p}) ∧
        Disjoint F.source (({B.firstCorner,B.secondCorner} : Set S) \ {p}) ∧
        (∀ x ∈ F.source, x ∈ a.val.image ↔ (F x).2=0) ∧
        (∀ x ∈ F.source, x ∈ b.val.image ↔ (F x).1=0) ∧
        (∀ x ∈ F.source, x ∈ range B.firstSide → 0≤(F x).1) ∧
        ∀ y ∈ Icc (0:ℝ) ell, (0,y) ∈ F.target ∧ F.symm (0,y) ∈ range B.secondSide := by
    obtain ⟨G0,hpG0,hG0p,hMarks0,hOld0,hRetained0,hOther0,hA0,hB0⟩ :=
      hActualUnmarkedRoundChart p hpCorner hpCross
    let G := G0.restrOpen W hW
    have hGs : G.source=G0.source ∩ W := rfl
    have hpG : p ∈ G.source := ⟨hpG0,hpW⟩
    have hGp : G p=(0,0) := hG0p
    have hMarks : Disjoint G.source (M.cover.branch : Set S) := hMarks0.mono_left Set.inter_subset_left
    have hOld (j : J) : Disjoint G.source (old j).val.image := (hOld0 j).mono_left Set.inter_subset_left
    have hRetained : Disjoint G.source (crossings M a b \ {p}) := hRetained0.mono_left Set.inter_subset_left
    have hOther : Disjoint G.source (({B.firstCorner,B.secondCorner} : Set S) \ {p}) := hOther0.mono_left Set.inter_subset_left
    have hA (x : S) (hx : x ∈ G.source) : x ∈ a.val.image ↔ (G x).2=0 := hA0 x hx.1
    have hB (x : S) (hx : x ∈ G.source) : x ∈ b.val.image ↔ (G x).1=0 := hB0 x hx.1
    have hOrientedSide (side : C(Interval,S)) (hSide : IsEmbedding side)
        (hz : side 0=B.firstCorner) (ho : side 1=B.secondCorner) :
        ∃ f : C(Interval,S), IsEmbedding f ∧ f 0=p ∧ range f=range side := by
      rcases hpCorner with he|he
      · exact ⟨side,hSide,hz.trans he.symm,rfl⟩
      · let q : C(Interval,S) := ⟨side ∘ unitInterval.symmHomeomorph,
          side.continuous.comp unitInterval.symmHomeomorph.continuous⟩
        refine ⟨q,hSide.comp unitInterval.symmHomeomorph.isEmbedding,?_,?_⟩
        · change side (unitInterval.symmHomeomorph 0)=p
          simpa using ho.trans he.symm
        · ext x
          constructor
          · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symmHomeomorph t,rfl⟩
          · rintro ⟨t,rfl⟩
            refine ⟨unitInterval.symmHomeomorph.symm t,?_⟩
            exact congrArg side (unitInterval.symmHomeomorph.apply_symm_apply t)
    obtain ⟨sideA,hSideA,hSideA0,hSideARange⟩ :=
      hOrientedSide B.firstSide B.first_embedded B.first_zero B.first_one
    obtain ⟨sideB,hSideB,hSideB0,hSideBRange⟩ :=
      hOrientedSide B.secondSide B.second_embedded B.second_zero B.second_one
    obtain ⟨GA,σa,ellA,hGAG,hGAValue,hSideAGA,hσa,hEllA,hAWhole,hARay⟩ :=
      hActualSelectedSideWholeRay sideA hSideA G (hSideA0.symm ▸ hpG)
        (hSideA0.symm ▸ hGp)
        (fun t ht => (hA _ ht).mp (B.first_on_curve (hSideARange ▸ Set.mem_range_self t)))
    have hpGA : p ∈ GA.source := hSideA0 ▸ hSideAGA
    let swapGA := GA.transHomeomorph (Homeomorph.prodComm ℝ ℝ)
    have hSwapSource : swapGA.source=GA.source := rfl
    have hSwapValue (x : S) : swapGA x=((GA x).2,(GA x).1) := rfl
    obtain ⟨GB,σb,ell,hGBSwap,hGBValue,hSideBGB,hσb,hEll,hBWhole,hBRay⟩ :=
      hActualSelectedSideWholeRay sideB hSideB swapGA
        (hSideB0.symm ▸ (hSwapSource.symm ▸ hpGA))
        (by rw [hSideB0,hSwapValue,hGAValue,hGp])
        (by
          intro t ht
          rw [hSwapValue,hGAValue]
          exact (hB _ (hGAG (hSwapSource ▸ ht))).mp
            (B.second_on_curve (hSideBRange ▸ Set.mem_range_self t)))
    have hpGB : p ∈ GB.source := hSideB0 ▸ hSideBGB
    let N : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
      toFun := fun z => (σa*z.2,σb*z.1)
      invFun := fun z => (σb*z.2,σa*z.1)
      left_inv := by intro z; rcases hσa with rfl|rfl <;> rcases hσb with rfl|rfl <;> simp
      right_inv := by intro z; rcases hσa with rfl|rfl <;> rcases hσb with rfl|rfl <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let F := GB.transHomeomorph N
    have hFs : F.source=GB.source := rfl
    have hFG (x : S) : F x=(σa*(G x).1,σb*(G x).2) := by
      change (σa*(GB x).2,σb*(GB x).1)=_
      rw [hGBValue,hSwapValue,hGAValue]
    have hFGSource : F.source ⊆ G.source := fun x hx =>
      hGAG (hSwapSource ▸ hGBSwap (hFs ▸ hx))
    have hσane : σa≠0 := by rcases hσa with rfl|rfl <;> norm_num
    have hσbne : σb≠0 := by rcases hσb with rfl|rfl <;> norm_num
    refine ⟨F,ell,hFs.symm ▸ hpGB,?_,(fun x hx => (hGs ▸ hFGSource hx).2),hEll,hMarks.mono_left hFGSource,
      (fun j => (hOld j).mono_left hFGSource),hRetained.mono_left hFGSource,
      hOther.mono_left hFGSource,?_,?_,?_,?_⟩
    · rw [hFG,hGp]; simp
    · intro x hx
      rw [hFG,mul_eq_zero]
      simp only [hσbne,false_or]
      exact hA x (hFGSource hx)
    · intro x hx
      rw [hFG,mul_eq_zero]
      simp only [hσane,false_or]
      exact hB x (hFGSource hx)
    · intro x hx hxSide
      rw [hFG]
      have hh := hAWhole x (hSwapSource ▸ hGBSwap (hFs ▸ hx)) (hSideARange.symm ▸ hxSide)
      simpa [hGAValue] using hh
    · intro y hy
      obtain ⟨hyT,hySide⟩ := hBRay y hy
      have hN : N (σb*y,0)=(0,y) := by
        change (σa*0,σb*(σb*y))=(0,y)
        rcases hσb with rfl|rfl <;> simp
      have hyFT : (0,y) ∈ F.target := by
        change N.symm (0,y) ∈ GB.target
        rw [← hN,N.symm_apply_apply]
        exact hyT
      refine ⟨hyFT,?_⟩
      change GB.symm (N.symm (0,y)) ∈ range B.secondSide
      rw [← hN,N.symm_apply_apply]
      exact hSideBRange ▸ hySide
  have hActualJointUnmarkedCornerFamily
      (F : OpenPartialHomeomorph S (ℝ × ℝ)) (ε : ℝ) (hε : 0 < ε)
      (hbox : ∀ x y : ℝ, 0 ≤ x → x ≤ ε → 0 ≤ y → y ≤ ε → (-x,y) ∈ F.target) :
      ∃ H : C(Interval × Interval,S),
        (∀ t u : Interval, H (t,u) ∈ F.source) ∧
        (∀ t u : Interval,
          F (H (t,u)) = (-(ε*(1-u.val)+(ε/2*t.val)*u.val),ε*u.val)) ∧
        (∀ t : Interval, IsEmbedding (fun u : Interval => H (t,u))) ∧
        (∀ t : Interval, H (t,0)=F.symm (-ε,0)) ∧
        (∀ t : Interval, H (t,1)=F.symm (-(ε/2)*t.val,ε)) ∧
        (∀ u : Interval, F (H (0,u))=(-ε*(1-u.val),ε*u.val)) := by
    let z : Interval × Interval → ℝ × ℝ := fun v =>
      (-(ε*(1-v.2.val)+(ε/2*v.1.val)*v.2.val),ε*v.2.val)
    have hz (v : Interval × Interval) : z v ∈ F.target := by
      apply hbox
      · exact add_nonneg (mul_nonneg hε.le (sub_nonneg.mpr v.2.property.2))
          (mul_nonneg (mul_nonneg (half_pos hε).le v.1.property.1) v.2.property.1)
      · nlinarith [v.1.property.1,v.1.property.2,v.2.property.1,v.2.property.2,
          mul_nonneg hε.le (sub_nonneg.mpr v.2.property.2),
          mul_nonneg (mul_nonneg (half_pos hε).le v.1.property.1) v.2.property.1]
      · nlinarith [v.2.property.1]
      · nlinarith [v.2.property.2]
    let H : C(Interval × Interval,S) := ⟨fun v => F.symm (z v),
      F.symm.continuousOn.comp_continuous (by dsimp [z]; fun_prop) hz⟩
    have hcoord (t u : Interval) : F (H (t,u))=z (t,u) := F.right_inv (hz (t,u))
    refine ⟨H,(fun t u => F.map_target (hz (t,u))),hcoord,?_,?_,?_,?_⟩
    · intro t
      have hc : Continuous (fun u : Interval => H (t,u)) :=
        H.continuous.comp (continuous_const.prodMk continuous_id)
      apply (hc.isClosedEmbedding ?_).isEmbedding
      intro u v huv
      have hy := congrArg Prod.snd (congrArg F huv)
      rw [hcoord,hcoord] at hy
      exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hε) hy)
    · intro t
      change F.symm (z (t,0))=F.symm (-ε,0)
      congr 1
      simp [z]
    · intro t
      change F.symm (z (t,1))=F.symm (-(ε/2)*t.val,ε)
      congr 1
      simp [z]
    · intro u
      rw [hcoord]
      simp [z,neg_mul]
  have hActualBaselineTriangleDisk
      (F : OpenPartialHomeomorph S (ℝ × ℝ)) (ε : ℝ) (hε : 0 < ε)
      (hbox : ∀ x y : ℝ, 0 ≤ x → x ≤ ε → 0 ≤ y → y ≤ ε → (-x,y) ∈ F.target) :
      ∃ d : C(closedBall (0 : ℝ × ℝ) 1,S), IsEmbedding d ∧
        range d=F.symm '' {z : ℝ × ℝ | -ε ≤ z.1 ∧ z.1 ≤ 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1+ε} := by
    let T : Set (ℝ × ℝ) := {z | -ε ≤ z.1 ∧ z.1 ≤ 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1+ε}
    have hclosed : IsClosed T :=
      (isClosed_le continuous_const continuous_fst).inter
        ((isClosed_le continuous_fst continuous_const).inter
          ((isClosed_le continuous_const continuous_snd).inter
            (isClosed_le continuous_snd (continuous_fst.add continuous_const))))
    have hconvex : Convex ℝ T := by
      intro x hx y hy a b ha hb hab
      change -ε ≤ a*x.1+b*y.1 ∧ a*x.1+b*y.1 ≤ 0 ∧
        0 ≤ a*x.2+b*y.2 ∧ a*x.2+b*y.2 ≤ a*x.1+b*y.1+ε
      constructor
      · nlinarith [mul_nonneg ha (show 0 ≤ x.1+ε by linarith [hx.1]),
          mul_nonneg hb (show 0 ≤ y.1+ε by linarith [hy.1])]
      constructor
      · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx.2.1)
          (mul_nonpos_of_nonneg_of_nonpos hb hy.2.1)
      constructor
      · exact add_nonneg (mul_nonneg ha hx.2.2.1) (mul_nonneg hb hy.2.2.1)
      · nlinarith [mul_nonneg ha (show 0 ≤ x.1+ε-x.2 by linarith [hx.2.2.2]),
          mul_nonneg hb (show 0 ≤ y.1+ε-y.2 by linarith [hy.2.2.2])]
    let O : Set (ℝ × ℝ) := {z | -ε < z.1 ∧ z.1 < 0 ∧ 0 < z.2 ∧ z.2 < z.1+ε}
    have hO : IsOpen O :=
      (isOpen_lt continuous_const continuous_fst).inter
        ((isOpen_lt continuous_fst continuous_const).inter
          ((isOpen_lt continuous_const continuous_snd).inter
            (isOpen_lt continuous_snd (continuous_fst.add continuous_const))))
    have hOT : O ⊆ T := fun z hz => ⟨hz.1.le,hz.2.1.le,hz.2.2.1.le,hz.2.2.2.le⟩
    have hne : (interior T).Nonempty := by
      refine ⟨(-ε/2,ε/4),mem_interior_iff_mem_nhds.mpr ?_⟩
      apply Filter.mem_of_superset (hO.mem_nhds ?_) hOT
      change -ε < -ε/2 ∧ -ε/2 < 0 ∧ 0 < ε/4 ∧ ε/4 < -ε/2+ε
      constructor <;> [linarith; skip]
      constructor <;> [linarith; skip]
      constructor <;> linarith
    have hb : Bornology.IsBounded T :=
      (show Bornology.IsBounded (closedBall (0 : ℝ × ℝ) ε) from isBounded_closedBall).subset (by
      intro z hz
      rw [mem_closedBall,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      simp only [Prod.fst_zero,Prod.snd_zero,sub_zero]
      apply max_le
      · rw [abs_of_nonpos hz.2.1]; linarith [hz.1]
      · rw [abs_of_nonneg hz.2.2.1]; linarith [hz.2.1,hz.2.2.2])
    obtain ⟨h,hi,hcl,hfr⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconvex hne hb
    rw [hclosed.closure_eq] at hcl
    have hs (x : closedBall (0 : ℝ × ℝ) 1) : h.symm x.val ∈ T := by
      have hx : x.val ∈ h '' T := hcl.symm ▸ x.property
      obtain ⟨z,hz,he⟩ := hx
      rw [← he,h.symm_apply_apply]
      exact hz
    have htarget (z : ℝ × ℝ) (hz : z ∈ T) : z ∈ F.target := by
      simpa using hbox (-z.1) z.2 (by linarith [hz.2.1]) (by linarith [hz.1])
        hz.2.2.1 (by linarith [hz.2.1,hz.2.2.2])
    let d : C(closedBall (0 : ℝ × ℝ) 1,S) := ⟨fun x => F.symm (h.symm x.val),
      F.symm.continuousOn.comp_continuous (h.symm.continuous.comp continuous_subtype_val)
        (fun x => htarget _ (hs x))⟩
    have hd : IsEmbedding d := (d.continuous.isClosedEmbedding (by
      intro x y he
      have hh := congrArg F he
      change F (F.symm (h.symm x.val))=F (F.symm (h.symm y.val)) at hh
      rw [F.right_inv (htarget _ (hs x)),F.right_inv (htarget _ (hs y))] at hh
      exact Subtype.ext (h.symm.injective hh))).isEmbedding
    refine ⟨d,hd,?_⟩
    ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨h.symm u.val,hs u,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      have hh : h z ∈ closedBall (0 : ℝ × ℝ) 1 := hcl ▸ mem_image_of_mem h hz
      refine ⟨⟨h z,hh⟩,?_⟩
      change F.symm (h.symm (h z))=F.symm z
      rw [h.symm_apply_apply]
  have hActualTriangleLiteralBaselinePorts
      (G : OpenPartialHomeomorph S (ℝ × ℝ)) (δ : ℝ) (hδ : 0 < δ)
      (A p : S) (L : C(Interval,S)) (H : C(Interval × Interval,S))
      (hA : A ∈ G.source) (hp : p ∈ G.source)
      (hL : L 0 ∈ G.source) (hH : ∀ u : Interval, H (0,u) ∈ G.source)
      (hAc : G A=(-δ,0)) (hpc : G p=(0,0)) (hLc : G (L 0)=(0,δ))
      (hHc : ∀ u : Interval, G (H (0,u))=(-δ*(1-u.val),δ*u.val))
      (T : Set S) (hT : T=G.symm '' {z : ℝ × ℝ | -δ ≤ z.1 ∧ z.1 ≤ 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1+δ}) :
      A ∈ T ∧ p ∈ T ∧ L 0 ∈ T ∧ range (fun u : Interval => H (0,u)) ⊆ T := by
    have hmem (x : S) (hx : x ∈ G.source)
        (hcoord : -δ ≤ (G x).1 ∧ (G x).1 ≤ 0 ∧ 0 ≤ (G x).2 ∧ (G x).2 ≤ (G x).1+δ) : x ∈ T := by
      rw [hT]
      exact ⟨G x,hcoord,G.left_inv hx⟩
    refine ⟨hmem A hA ?_,hmem p hp ?_,hmem (L 0) hL ?_,?_⟩
    · rw [hAc]; constructor
      · exact le_rfl
      constructor
      · linarith
      constructor
      · exact le_rfl
      · simp
    · rw [hpc]; constructor
      · linarith
      constructor
      · exact le_rfl
      constructor
      · exact le_rfl
      · linarith
    · rw [hLc]; constructor
      · linarith
      constructor
      · exact le_rfl
      constructor
      · exact hδ.le
      · simp
    · rintro x ⟨u,rfl⟩
      apply hmem _ (hH u)
      rw [hHc]
      constructor
      · nlinarith [u.property.1]
      constructor
      · simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hδ.le (sub_nonneg.mpr u.property.2))
      constructor
      · exact mul_nonneg hδ.le u.property.1
      · linarith
  have hActualUnmarkedArcLiteralParameterTraceEq
      (c : EssentialMarkedArc M)
      (f : C(Interval,S)) (hf : IsEmbedding f) (hfc : range f ⊆ c.val.image)
      (h0 : c.val.map 0 ∉ range f) (h1 : c.val.map 1 ∉ range f)
      (u v : Interval) (hf0 : f 0=c.val.map u) (hf1 : f 1=c.val.map v) :
      range f = (c.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Icc (min u.val v.val) (max u.val v.val) := by
    classical
    obtain ⟨l,r,hl,hlr,hr,hImage⟩ := hActualUnmarkedSideParameters c f hf hfc h0 h1
    let g : Icc l r → S := fun t => c.val.map ⟨t.val,hl.le.trans t.property.1,t.property.2.trans hr.le⟩
    have hgc : Continuous g := c.val.continuous.comp (by fun_prop)
    have hgi : Function.Injective g := by
      intro x y he
      rcases c.val.injective_except_loop_closure _ _ he with he|he|he
      · exact Subtype.ext (congrArg (fun z : Interval => z.val) he)
      · have hh := congrArg Subtype.val he.1
        change x.val=0 at hh
        linarith [x.property.1]
      · have hh := congrArg Subtype.val he.1
        change x.val=1 at hh
        linarith [x.property.2]
    let e : Icc l r ≃ₜ range g := (hgc.isClosedEmbedding hgi).isEmbedding.toHomeomorph
    have hfr (t : Interval) : f t ∈ range g := by
      obtain ⟨θ,hθ,he⟩ := hImage ▸ Set.mem_range_self t
      refine ⟨⟨θ,hθ⟩,?_⟩
      simpa only [g,Function.comp_apply,Set.projIcc_of_mem zero_le_one
        (show θ ∈ Icc (0:ℝ) 1 from ⟨hl.le.trans hθ.1,hθ.2.trans hr.le⟩)] using he
    let α : Interval → ℝ := fun t => (e.symm ⟨f t,hfr t⟩).val
    have hαc : Continuous α := continuous_subtype_val.comp
      (e.symm.continuous.comp (f.continuous.subtype_mk _))
    have hαf (t : Interval) : g (e.symm ⟨f t,hfr t⟩)=f t :=
      congrArg Subtype.val (e.apply_symm_apply _)
    have hαi : Function.Injective α := by
      intro t w he
      apply hf.injective
      rw [← hαf t,← hαf w]
      congr 1
      exact Subtype.ext he
    have hEndpoint (t w : Interval) (he : f t=c.val.map w) : α t=w.val := by
      rcases c.val.injective_except_loop_closure _ w ((hαf t).trans he) with hh|hh|hh
      · exact congrArg Subtype.val hh
      · have hzero := congrArg Subtype.val hh.1
        change α t=0 at hzero
        have := (e.symm ⟨f t,hfr t⟩).property.1
        change l ≤ α t at this
        linarith
      · have hone := congrArg Subtype.val hh.1
        change α t=1 at hone
        have := (e.symm ⟨f t,hfr t⟩).property.2
        change α t ≤ r at this
        linarith
    have hα0 : α 0=u.val := hEndpoint 0 u hf0
    have hα1 : α 1=v.val := hEndpoint 1 v hf1
    have hαbound (t : Interval) : α t ∈ Icc (min u.val v.val) (max u.val v.val) := by
      rcases hαc.strictMono_of_inj_boundedOrder' hαi with hm|hm
      · have hleft := hm.monotone (show (0:Interval) ≤ t from bot_le)
        have hright := hm.monotone (show t ≤ (1:Interval) from le_top)
        rw [hα0] at hleft
        rw [hα1] at hright
        exact ⟨(min_le_left _ _).trans hleft,hright.trans (le_max_right _ _)⟩
      · have hleft := hm.antitone (show t ≤ (1:Interval) from le_top)
        have hright := hm.antitone (show (0:Interval) ≤ t from bot_le)
        rw [hα1] at hleft
        rw [hα0] at hright
        exact ⟨(min_le_right _ _).trans hleft,hright.trans (le_max_left _ _)⟩
    have hαfull : Icc (min u.val v.val) (max u.val v.val) ⊆ range α :=
      (isPreconnected_range hαc).ordConnected.uIcc_subset ⟨0,hα0⟩ ⟨1,hα1⟩
    apply Set.Subset.antisymm
    · rintro x ⟨t,rfl⟩
      refine ⟨α t,hαbound t,?_⟩
      have ht : α t ∈ Icc (0:ℝ) 1 :=
        ⟨hl.le.trans (e.symm ⟨f t,hfr t⟩).property.1,
          (e.symm ⟨f t,hfr t⟩).property.2.trans hr.le⟩
      simp only [Function.comp_apply,Set.projIcc_of_mem zero_le_one ht]
      exact hαf t
    · rintro x ⟨θ,hθ,rfl⟩
      obtain ⟨t,ht⟩ := hαfull hθ
      refine ⟨t,?_⟩
      have hα01 : α t ∈ Icc (0:ℝ) 1 :=
        ⟨hl.le.trans (e.symm ⟨f t,hfr t⟩).property.1,
          (e.symm ⟨f t,hfr t⟩).property.2.trans hr.le⟩
      rw [← ht]
      simp only [Function.comp_apply,Set.projIcc_of_mem zero_le_one hα01]
      exact (hαf t).symm
  have hActualUnmarkedArcLiteralParameterInterval
      (c : EssentialMarkedArc M)
      (f : C(Interval,S)) (hf : IsEmbedding f) (hfc : range f ⊆ c.val.image)
      (h0 : c.val.map 0 ∉ range f) (h1 : c.val.map 1 ∉ range f)
      (u v : Interval) (hf0 : f 0=c.val.map u) (hf1 : f 1=c.val.map v) :
      range f ⊆ (c.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Icc (min u.val v.val) (max u.val v.val) := by
    classical
    obtain ⟨l,r,hl,hlr,hr,hImage⟩ := hActualUnmarkedSideParameters c f hf hfc h0 h1
    let g : Icc l r → S := fun t => c.val.map ⟨t.val,hl.le.trans t.property.1,t.property.2.trans hr.le⟩
    have hgc : Continuous g := c.val.continuous.comp (by fun_prop)
    have hgi : Function.Injective g := by
      intro x y he
      rcases c.val.injective_except_loop_closure _ _ he with he|he|he
      · exact Subtype.ext (congrArg (fun z : Interval => z.val) he)
      · have hh := congrArg Subtype.val he.1
        change x.val=0 at hh
        linarith [x.property.1]
      · have hh := congrArg Subtype.val he.1
        change x.val=1 at hh
        linarith [x.property.2]
    let e : Icc l r ≃ₜ range g := (hgc.isClosedEmbedding hgi).isEmbedding.toHomeomorph
    have hfr (t : Interval) : f t ∈ range g := by
      obtain ⟨θ,hθ,he⟩ := hImage ▸ Set.mem_range_self t
      refine ⟨⟨θ,hθ⟩,?_⟩
      simpa only [g,Function.comp_apply,Set.projIcc_of_mem zero_le_one
        (show θ ∈ Icc (0:ℝ) 1 from ⟨hl.le.trans hθ.1,hθ.2.trans hr.le⟩)] using he
    let α : Interval → ℝ := fun t => (e.symm ⟨f t,hfr t⟩).val
    have hαc : Continuous α := continuous_subtype_val.comp
      (e.symm.continuous.comp (f.continuous.subtype_mk _))
    have hαf (t : Interval) : g (e.symm ⟨f t,hfr t⟩)=f t :=
      congrArg Subtype.val (e.apply_symm_apply _)
    have hαi : Function.Injective α := by
      intro t w he
      apply hf.injective
      rw [← hαf t,← hαf w]
      congr 1
      exact Subtype.ext he
    have hEndpoint (t w : Interval) (he : f t=c.val.map w) : α t=w.val := by
      rcases c.val.injective_except_loop_closure _ w ((hαf t).trans he) with hh|hh|hh
      · exact congrArg Subtype.val hh
      · have hzero := congrArg Subtype.val hh.1
        change α t=0 at hzero
        have := (e.symm ⟨f t,hfr t⟩).property.1
        change l ≤ α t at this
        linarith
      · have hone := congrArg Subtype.val hh.1
        change α t=1 at hone
        have := (e.symm ⟨f t,hfr t⟩).property.2
        change α t ≤ r at this
        linarith
    have hα0 : α 0=u.val := hEndpoint 0 u hf0
    have hα1 : α 1=v.val := hEndpoint 1 v hf1
    have hαbound (t : Interval) : α t ∈ Icc (min u.val v.val) (max u.val v.val) := by
      rcases hαc.strictMono_of_inj_boundedOrder' hαi with hm|hm
      · have hleft := hm.monotone (show (0:Interval) ≤ t from bot_le)
        have hright := hm.monotone (show t ≤ (1:Interval) from le_top)
        rw [hα0] at hleft
        rw [hα1] at hright
        exact ⟨(min_le_left _ _).trans hleft,hright.trans (le_max_right _ _)⟩
      · have hleft := hm.antitone (show t ≤ (1:Interval) from le_top)
        have hright := hm.antitone (show (0:Interval) ≤ t from bot_le)
        rw [hα1] at hleft
        rw [hα0] at hright
        exact ⟨(min_le_right _ _).trans hleft,hright.trans (le_max_left _ _)⟩
    rintro x ⟨t,rfl⟩
    refine ⟨α t,hαbound t,?_⟩
    have ht : α t ∈ Icc (0:ℝ) 1 :=
      ⟨hl.le.trans (e.symm ⟨f t,hfr t⟩).property.1,
        (e.symm ⟨f t,hfr t⟩).property.2.trans hr.le⟩
    simp only [Function.comp_apply,Set.projIcc_of_mem zero_le_one ht]
    exact hαf t
  have hActualTriangleHorizontalArc
      (G : OpenPartialHomeomorph S (ℝ × ℝ)) (δ : ℝ) (hδ : 0 < δ)
      (hBox : ∀ x y : ℝ, 0 ≤ x → x ≤ δ → 0 ≤ y → y ≤ δ → (-x,y) ∈ G.target)
      (A p : S) (hA : A ∈ G.source) (hp : p ∈ G.source)
      (hAc : G A=(-δ,0)) (hpc : G p=(0,0)) :
      ∃ g : C(Interval,S), IsEmbedding g ∧ g 0=A ∧ g 1=p ∧
        range g ⊆ G.source ∧
        range g=G.symm '' {z : ℝ × ℝ | -δ ≤ z.1 ∧ z.1 ≤ 0 ∧ z.2=0} := by
    let z : Interval → ℝ × ℝ := fun u => (-δ+δ*u.val,0)
    have hz (u : Interval) : z u ∈ G.target := by
      have hh := hBox (δ-δ*u.val) 0
        (by nlinarith [u.property.2]) (by nlinarith [u.property.1]) le_rfl hδ.le
      convert hh using 1
      dsimp [z]; congr 1; ring
    let g : C(Interval,S) := ⟨fun u => G.symm (z u),
      G.symm.continuousOn.comp_continuous (by dsimp [z]; fun_prop) hz⟩
    have hgs (u : Interval) : g u ∈ G.source := G.map_target (hz u)
    have hgc (u : Interval) : G (g u)=z u := G.right_inv (hz u)
    have hgi : Function.Injective g := by
      intro u v he
      have hh := congrArg Prod.fst (congrArg G he)
      rw [hgc,hgc] at hh
      have hv : u.val=v.val := by dsimp [z] at hh; nlinarith
      exact Subtype.ext hv
    refine ⟨g,(g.continuous.isClosedEmbedding hgi).isEmbedding,?_,?_,?_,?_⟩
    · change G.symm (z 0)=A
      have he : z 0=G A := by simp [z,hAc]
      rw [he,G.left_inv hA]
    · change G.symm (z 1)=p
      have he : z 1=G p := by simp [z,hpc]
      rw [he,G.left_inv hp]
    · rintro x ⟨u,rfl⟩; exact hgs u
    · ext x
      constructor
      · rintro ⟨u,rfl⟩
        refine ⟨z u,?_,rfl⟩
        change -δ ≤ -δ+δ*u.val ∧ -δ+δ*u.val ≤ 0 ∧ (0:ℝ)=0
        exact ⟨by nlinarith [u.property.1],by nlinarith [u.property.2],rfl⟩
      · rintro ⟨q,hq,rfl⟩
        let u : Interval := ⟨(q.1+δ)/δ,
          (div_nonneg (by linarith [hq.1]) hδ.le),
          (div_le_one hδ).mpr (by linarith [hq.2.1])⟩
        refine ⟨u,?_⟩
        change G.symm (z u)=G.symm q
        congr 1
        apply Prod.ext
        · change -δ+δ*((q.1+δ)/δ)=q.1
          field_simp
          ring
        · exact hq.2.2.symm
  have hActualTruncatedWideCornerSupport
      (ε : ℝ) (hε : 0 < ε) (t u : Interval) :
      let z : ℝ × ℝ := (-(ε*(1-u.val)+(ε/2*t.val)*u.val),ε*u.val)
      (-ε ≤ z.1 ∧ z.1 ≤ 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ 2*(z.1+ε) ∧ z.2 ≤ ε) ∧
      (0 < t.val → t.val < 1 → 0 < u.val → u.val < 1 →
        -ε < z.1 ∧ z.1 < 0 ∧ 0 < z.2 ∧ z.2 < 2*(z.1+ε) ∧ z.2 < ε) := by
    dsimp only
    have hu0 := u.property.1
    have hu1 := u.property.2
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hy : 0 ≤ ε*u.val := mul_nonneg hε.le hu0
    have hleft : 0 ≤ ε*u.val*(1-t.val/2) :=
      mul_nonneg hy (by linarith)
    have hright : 0 ≤ ε*(1-u.val)+ε/2*t.val*u.val :=
      add_nonneg (mul_nonneg hε.le (sub_nonneg.mpr hu1))
        (mul_nonneg (mul_nonneg (half_pos hε).le ht0) hu0)
    have hgap : 0 ≤ ε*u.val*(1-t.val) := mul_nonneg hy (sub_nonneg.mpr ht1)
    constructor
    · constructor
      · nlinarith
      constructor
      · nlinarith
      constructor
      · exact hy
      · exact ⟨by nlinarith,mul_le_of_le_one_right hε.le hu1⟩
    · intro ht htlt hu hult
      have hypos := mul_pos hε hu
      have hleftpos := mul_pos hypos (show 0 < 1-t.val/2 by linarith)
      have hrightpos := mul_pos (mul_pos (half_pos hε) ht) hu
      have hnonneg := mul_nonneg hε.le (sub_nonneg.mpr hu1)
      have hgappos := mul_pos hypos (sub_pos.mpr htlt)
      constructor
      · nlinarith
      constructor
      · nlinarith
      constructor
      · exact hypos
      · exact ⟨by nlinarith,by simpa only [mul_one] using mul_lt_mul_of_pos_left hult hε⟩
  have hActualEmbeddedArcLiteralIntervalTrace
      (g f : C(Interval,S)) (hg : IsEmbedding g) (hf : IsEmbedding f)
      (hfg : range f ⊆ range g) (u v : Interval)
      (hf0 : f 0=g u) (hf1 : f 1=g v) :
      range f=g '' Icc (min u v) (max u v) := by
    let e := hg.toHomeomorph
    let α : Interval → Interval := fun t => e.symm ⟨f t,hfg (Set.mem_range_self t)⟩
    have hαc : Continuous α := e.symm.continuous.comp (f.continuous.subtype_mk _)
    have hαf (t : Interval) : g (α t)=f t := congrArg Subtype.val (e.apply_symm_apply _)
    have hαi : Function.Injective α := by
      intro t w he
      exact hf.injective ((hαf t).symm.trans ((congrArg g he).trans (hαf w)))
    have hα0 : α 0=u := hg.injective ((hαf 0).trans hf0)
    have hα1 : α 1=v := hg.injective ((hαf 1).trans hf1)
    have hαrange : range α ⊆ Icc (min u v) (max u v) := by
      rintro θ ⟨t,rfl⟩
      rcases hαc.strictMono_of_inj_boundedOrder' hαi with hm|hm
      · have hlo := hm.monotone (show (0:Interval)≤t from bot_le)
        have hhi := hm.monotone (show t≤(1:Interval) from le_top)
        rw [hα0] at hlo
        rw [hα1] at hhi
        exact ⟨(min_le_left u v).trans hlo,hhi.trans (le_max_right u v)⟩
      · have hlo := hm.antitone (show t≤(1:Interval) from le_top)
        have hhi := hm.antitone (show (0:Interval)≤t from bot_le)
        rw [hα1] at hlo
        rw [hα0] at hhi
        exact ⟨(min_le_right u v).trans hlo,hhi.trans (le_max_left u v)⟩
    have hfull : Icc (min u v) (max u v) ⊆ range α :=
      (isPreconnected_range hαc).ordConnected.uIcc_subset ⟨0,hα0⟩ ⟨1,hα1⟩
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨α t,hαrange (Set.mem_range_self t),hαf t⟩
    · rintro ⟨θ,hθ,rfl⟩
      obtain ⟨t,ht⟩ := hfull hθ
      exact ⟨t,(hαf t).symm.trans (congrArg g ht)⟩
  have hActualMovingCornerFamilyKernel
      (roundCorner : S) (roundChart : OpenPartialHomeomorph S (ℝ × ℝ))
      (hRoundChart : roundCorner ∈ roundChart.source)
      (hRoundZero : roundChart roundCorner=(0,0))
      (hRoundMarks : Disjoint roundChart.source (M.cover.branch : Set S))
      (hRoundOld : ∀ j, Disjoint roundChart.source (old j).val.image)
      (hRoundRetained : Disjoint roundChart.source (crossings M a b \ {roundCorner}))
      (hRoundA : ∀ x ∈ roundChart.source, x ∈ a.val.image ↔ (roundChart x).2=0)
      (hRoundB : ∀ x ∈ roundChart.source, x ∈ b.val.image ↔ (roundChart x).1=0)
      (ell : ℝ) (hell : 0<ell) :
      ∃ A : S, ∃ L : C(Interval,S), ∃ eps : ℝ,
        0<eps ∧ eps<ell ∧ roundChart A=(-eps,0) ∧
        (∀ t, roundChart (L t)=(-(eps/2)*t.val,eps)) ∧ A ∈ a.val.image ∧ A ∉ b.val.image ∧
        L 0 ∈ b.val.image ∧ L 0 ∉ a.val.image ∧
        (∀ t, L t ∈ roundChart.source) ∧
        (∀ x y : ℝ, 0 ≤ x → x ≤ eps → 0 ≤ y → y ≤ eps → (-x,y) ∈ roundChart.target) ∧
        ∀ t : Interval, 0<t.val → ∃ f : C(Interval,S),
          (∀ u : Interval, roundChart (f u)=(-(eps*(1-u.val)+(eps/2*t.val)*u.val),eps*u.val)) ∧
          IsEmbedding f ∧ f 0=A ∧ f 1=L t ∧ range f ⊆ roundChart.source ∧
          range f ∩ a.val.image={A} ∧ Disjoint (range f) b.val.image ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧
          (∀ j, Disjoint (range f) (old j).val.image) ∧
          Disjoint (range f) (crossings M a b \ {roundCorner}) := by
    have hzero : (0 : ℝ × ℝ) ∈ roundChart.target := by
      change (0,0) ∈ roundChart.target
      rw [← hRoundZero]
      exact roundChart.map_source hRoundChart
    obtain ⟨r,hr,hrTarget⟩ := Metric.isOpen_iff.mp roundChart.open_target 0 hzero
    let ε : ℝ := min r ell/2
    have hε : 0<ε := half_pos (lt_min hr hell)
    have hεr : ε<r := by dsimp [ε]; linarith [min_le_left r ell]
    have hεell : ε<ell := by dsimp [ε]; linarith [min_le_right r ell]
    let sx : ℝ := -1
    let sy : ℝ := 1
    have hsx : sx≠0 := by norm_num [sx]
    have hsy : sy≠0 := by norm_num [sy]
    have hsxa : |sx|=1 := by norm_num [sx]
    have hsya : |sy|=1 := by norm_num [sy]
    have hbox (x y : ℝ) (hx : 0≤x ∧ x≤ε) (hy : 0≤y ∧ y≤ε) :
        (sx*x,sy*y) ∈ roundChart.target := by
      apply hrTarget
      rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      simp only [Prod.fst_zero,Prod.snd_zero,sub_zero]
      rw [abs_mul,abs_mul,hsxa,hsya,abs_of_nonneg hx.1,abs_of_nonneg hy.1]
      simp only [one_mul]
      exact max_lt (hx.2.trans_lt hεr) (hy.2.trans_lt hεr)
    let A : S := roundChart.symm (sx*ε,0)
    have hAt : (sx*ε,0) ∈ roundChart.target := by
      simpa using hbox ε 0 ⟨hε.le,le_rfl⟩ ⟨le_rfl,hε.le⟩
    have hAS : A ∈ roundChart.source := roundChart.map_target hAt
    have hAC : roundChart A=(sx*ε,0) := roundChart.right_inv hAt
    let lz : Interval → ℝ × ℝ := fun t => (sx*(ε/2)*t.val,sy*ε)
    have hlz (t : Interval) : lz t ∈ roundChart.target := by
      have hx : 0≤ε/2*t.val ∧ ε/2*t.val≤ε := by
        constructor <;> nlinarith [t.property.1,t.property.2]
      simpa [lz,mul_assoc] using hbox (ε/2*t.val) ε hx ⟨hε.le,le_rfl⟩
    let L : C(Interval,S) := ⟨fun t => roundChart.symm (lz t),
      roundChart.symm.continuousOn.comp_continuous (by dsimp [lz]; fun_prop) hlz⟩
    have hLS (t : Interval) : L t ∈ roundChart.source := roundChart.map_target (hlz t)
    have hLC (t : Interval) : roundChart (L t)=lz t := roundChart.right_inv (hlz t)
    refine ⟨A,L,ε,hε,hεell,?_,?_,?_,?_,?_,?_,hLS,?_,?_⟩
    · simpa [sx] using hAC
    · intro t
      simpa [lz,sx,sy] using hLC t
    · exact (hRoundA A hAS).mpr (by rw [hAC])
    · intro hh
      have hzero := (hRoundB A hAS).mp hh
      rw [hAC] at hzero
      exact mul_ne_zero hsx (ne_of_gt hε) hzero
    · exact (hRoundB (L 0) (hLS 0)).mpr (by rw [hLC]; simp [lz])
    · intro hh
      have hzero := (hRoundA (L 0) (hLS 0)).mp hh
      rw [hLC] at hzero
      exact mul_ne_zero hsy (ne_of_gt hε) hzero
    · intro x y hx0 hxε hy0 hyε
      simpa [sx,sy] using hbox x y ⟨hx0,hxε⟩ ⟨hy0,hyε⟩
    · intro t ht
      let c : ℝ := ε/2*t.val
      have hc : 0<c := mul_pos (half_pos hε) ht
      have hcε : c≤ε := by dsimp [c]; nlinarith [t.property.2]
      let z : Interval → ℝ × ℝ := fun u =>
        (sx*(ε*(1-u.val)+c*u.val),sy*ε*u.val)
      have hz (u : Interval) : z u ∈ roundChart.target := by
        have hx : 0≤ε*(1-u.val)+c*u.val ∧ ε*(1-u.val)+c*u.val≤ε := by
          constructor <;> nlinarith [u.property.1,u.property.2,
            mul_nonneg hc.le u.property.1,mul_nonneg hε.le (sub_nonneg.mpr u.property.2),
            mul_nonneg (sub_nonneg.mpr hcε) u.property.1]
        have hy : 0≤ε*u.val ∧ ε*u.val≤ε := by
          constructor <;> nlinarith [u.property.1,u.property.2]
        simpa [z,mul_assoc] using hbox _ _ hx hy
      let f : C(Interval,S) := ⟨fun u => roundChart.symm (z u),
        roundChart.symm.continuousOn.comp_continuous (by dsimp [z]; fun_prop) hz⟩
      have hfS (u : Interval) : f u ∈ roundChart.source := roundChart.map_target (hz u)
      have hfC (u : Interval) : roundChart (f u)=z u := roundChart.right_inv (hz u)
      have hinj : Function.Injective f := by
        intro u v he
        have hh := congrArg Prod.snd (congrArg roundChart he)
        rw [hfC,hfC] at hh
        exact Subtype.ext (mul_left_cancel₀ (mul_ne_zero hsy (ne_of_gt hε)) hh)
      have hsub : range f ⊆ roundChart.source := by rintro x ⟨u,rfl⟩; exact hfS u
      have hf0 : f 0=A := by
        change roundChart.symm (z 0)=roundChart.symm (sx*ε,0)
        congr 1
        simp [z]
      have hf1 : f 1=L t := by
        change roundChart.symm (z 1)=roundChart.symm (lz t)
        congr 1
        simp [z,lz,c,mul_assoc]
      have hfFormula (u : Interval) : roundChart (f u)=(-(ε*(1-u.val)+(ε/2*t.val)*u.val),ε*u.val) := by
        simpa [z,sx,sy,c,mul_assoc] using hfC u
      refine ⟨f,hfFormula,(f.continuous.isClosedEmbedding hinj).isEmbedding,hf0,hf1,hsub,?_,?_,
        hRoundMarks.mono_left hsub,(fun j => (hRoundOld j).mono_left hsub),
        hRoundRetained.mono_left hsub⟩
      · ext x
        constructor
        · rintro ⟨⟨u,rfl⟩,hu⟩
          have hy := (hRoundA (f u) (hfS u)).mp hu
          rw [hfC] at hy
          have hu0 : u=0 := Subtype.ext ((mul_eq_zero.mp hy).resolve_left (mul_ne_zero hsy (ne_of_gt hε)))
          simp [hu0,hf0]
        · rintro rfl
          exact ⟨⟨0,hf0⟩,(hRoundA A hAS).mpr (by rw [hAC])⟩
      · apply Set.disjoint_left.mpr
        rintro x ⟨u,rfl⟩ hu
        have hx := (hRoundB (f u) (hfS u)).mp hu
        rw [hfC] at hx
        have hx0 : ε*(1-u.val)+c*u.val=0 := (mul_eq_zero.mp hx).resolve_left hsx
        have hpos : 0<ε*(1-u.val)+c*u.val := by
          by_cases hu0 : u.val=0
          · simp [hu0,hε]
          · have hup : 0<u.val := lt_of_le_of_ne u.property.1 (Ne.symm hu0)
            have := mul_pos hc hup
            nlinarith [mul_nonneg hε.le (sub_nonneg.mpr u.property.2)]
        linarith
  have hOriginalDiskFrontier : frontier (range B.disk)=range B.firstSide ∪ range B.secondSide := by
    letI : CompactSpace S := M.sphere.symm.compactSpace
    letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      Subtype.connectedSpace (isConnected_sphere
        (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
        0 (by norm_num))
    letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
    letI := (actualSphereSmoothAtlas M).charts
    letI := (actualSphereSmoothAtlas M).manifold
    letI : ClosedSurface S := {}
    have hclosed : IsClosed (range B.disk) := (isCompact_range B.disk.continuous).isClosed
    rw [hclosed.frontier_eq,CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq B.disk B.disk_embedded,← B.boundary_eq]
    ext x
    constructor
    · rintro ⟨⟨z,rfl⟩,hnot⟩
      refine ⟨z,?_,rfl⟩
      apply le_antisymm z.property
      by_contra hn
      exact hnot ⟨z,lt_of_not_ge hn,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      refine ⟨⟨z,rfl⟩,?_⟩
      rintro ⟨w,hw,he⟩
      have hzw := B.disk_embedded.injective he
      subst w
      change dist z.val (0:Plane)<1 at hw
      change dist z.val (0:Plane)=1 at hz
      linarith
  have hActualClosedDiskPathOutsideBoundary (f : C(Interval,S))
      (hBoundary : Disjoint (range f) (range B.firstSide ∪ range B.secondSide))
      (hStart : f 0 ∉ range B.disk) : Disjoint (range f) (range B.disk) := by
    have hClosed : IsClosed (range B.disk) := (isCompact_range B.disk.continuous).isClosed
    have hFront : Disjoint (range f) (frontier (range B.disk)) := hOriginalDiskFrontier.symm ▸ hBoundary
    have hCover : range f ⊆ interior (range B.disk) ∪ (range B.disk)ᶜ := by
      intro x hx
      by_cases hxD : x ∈ range B.disk
      · left
        by_contra hn
        exact Set.disjoint_left.mp hFront hx (hClosed.frontier_eq ▸ ⟨hxD,hn⟩)
      · exact Or.inr hxD
    have hClass := (isPreconnected_range f.continuous).subset_or_subset
      isOpen_interior hClosed.isOpen_compl
      (Set.disjoint_left.mpr (fun x hx hn => hn (interior_subset hx))) hCover
    rcases hClass with hInside|hOutside
    · exact False.elim (hStart (interior_subset (hInside (Set.mem_range_self 0))))
    · exact Set.disjoint_left.mpr (fun x hx hxD => hOutside hx hxD)
  have hActualUnmarkedRoundedExteriorFamily (p : S)
      (hpCorner : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
      (hpCross : p ∈ crossings M a b)
      (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
      ∃ F : OpenPartialHomeomorph S (ℝ × ℝ), ∃ A : S, ∃ L : C(Interval,S),
        p ∈ F.source ∧ F p=(0,0) ∧ F.source ⊆ W ∧ A ∈ F.source ∧
        Disjoint F.source (M.cover.branch : Set S) ∧
        (∀ j, Disjoint F.source (old j).val.image) ∧
        A ∈ Kraw ∧ A ∉ range B.firstSide ∧
        L 0 ∈ F.source ∧ L 0 ∈ range B.secondSide ∧ L 0 ∉ a.val.image ∧
        (∀ j, L 0 ∉ (old j).val.image) ∧
        ∃ H : C(Interval × Interval,S),
        (∀ t u : Interval, H (t,u) ∈ F.source) ∧
        (∀ t : Interval, IsEmbedding (fun u : Interval => H (t,u))) ∧
        (∀ t : Interval, H (t,0)=A) ∧ (∀ t : Interval, H (t,1)=L t) ∧
        (∃ delta : ℝ, 0 < delta ∧ F p=(0,0) ∧ F A=(-delta,0) ∧ F (L 0)=(0,delta) ∧
          (∀ t u : Interval, F (H (t,u))=(-(delta*(1-u.val)+(delta/2*t.val)*u.val),delta*u.val)) ∧
          (∀ x y : ℝ, 0 ≤ x → x ≤ delta → 0 ≤ y → y ≤ delta → (-x,y) ∈ F.target) ∧
          (∀ x ∈ F.source, x ∈ a.val.image ↔ (F x).2=0) ∧
          (∀ x ∈ F.source, x ∈ b.val.image ↔ (F x).1=0) ∧
          (∀ x ∈ F.source, x ∈ range B.firstSide → 0 ≤ (F x).1) ∧
          ∃ d : C(closedBall (0 : ℝ × ℝ) 1,S), IsEmbedding d ∧
            range d=F.symm '' {z : ℝ × ℝ | -delta ≤ z.1 ∧ z.1 ≤ 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1+delta} ∧
            range d ⊆ F.source ∧
            Disjoint (range d) (M.cover.branch : Set S) ∧
            (∀ j, Disjoint (range d) (old j).val.image) ∧
            range d ∩ range B.disk=F.symm '' {z : ℝ × ℝ | z.1=0 ∧ 0 ≤ z.2 ∧ z.2 ≤ delta} ∧
            (∀ y : ℝ, 0<y → y<delta → F.symm (0,y) ∈ interior (range B.disk ∪ range d))) ∧
        ∀ t : Interval, 0<t.val → ∃ f : C(Interval,S),
          IsEmbedding f ∧ f 0=A ∧ f 1=L t ∧ range f ⊆ F.source ∧
          Disjoint (range f) (range B.disk) ∧
          range f ∩ a.val.image={A} ∧ range f ∩ Kraw={A} ∧
          Disjoint (range f) b.val.image ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧
          (∀ j, Disjoint (range f) (old j).val.image) ∧
          Disjoint (range f) (crossings M a b \ {p}) ∧
          (∀ u : Interval, f u=H (t,u)) := by
    obtain ⟨F,ell,hpF,hFp,hFW,hell,hMarks,hOld,hRetained,hOther,hAaxis,hBaxis,hFirstPositive,hSecondRay⟩ :=
      hActualUnmarkedCornerWholeAxes p hpCorner hpCross W hW hpW
    obtain ⟨A,L,eps,heps,hepsell,hAcoord,hLcoord,hA,hAnotB,hL0B,hL0notA,hLS,hFamilyBox,hPaths⟩ :=
      hActualMovingCornerFamilyKernel p F hpF hFp hMarks hOld hRetained hAaxis hBaxis ell hell
    obtain ⟨jointCorner,hJointSource,hJointCoordinates,hJointEmbedded,hJointStart,hJointEnd,hActualBaselineDiagonal⟩ :=
      hActualJointUnmarkedCornerFamily F eps heps hFamilyBox
    have hAS : A ∈ F.source := by
      obtain ⟨f,hfc,hf,hf0,hf1,hfS,hfa,hfb,hfm,hfo,hfr⟩ := hPaths 1 (by norm_num)
      rw [← hf0]
      exact hfS (Set.mem_range_self 0)
    have hAfirst : A ∉ range B.firstSide := by
      intro hh
      have hnonneg := hFirstPositive A hAS hh
      rw [hAcoord] at hnonneg
      linarith
    have hAK : A ∈ Kraw := by
      have hh : A ∈ range B.firstSide ∪ Kraw := hdecompRaw ▸ hA
      exact hh.resolve_left hAfirst
    have hAoffDisk : A ∉ range B.disk := by
      intro hh
      exact hAfirst (hDiskA ▸ (show A ∈ range B.disk ∩ a.val.image from ⟨hh,hA⟩))
    let baselineTriangle : Set (ℝ × ℝ) :=
      {z | -eps ≤ z.1 ∧ z.1 ≤ 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1+eps}
    have hTriangleTarget (z : ℝ × ℝ) (hz : z ∈ baselineTriangle) : z ∈ F.target := by
      have hh := hFamilyBox (-z.1) z.2 (by linarith [hz.2.1])
        (by linarith [hz.1]) hz.2.2.1 (by linarith [hz.2.1,hz.2.2.2])
      simpa using hh
    have hTriangleSource : F.symm '' baselineTriangle ⊆ F.source := by
      rintro x ⟨z,hz,rfl⟩
      exact F.map_target (hTriangleTarget z hz)
    have hTriangleMarks : Disjoint (F.symm '' baselineTriangle) (M.cover.branch : Set S) :=
      hMarks.mono_left hTriangleSource
    have hTriangleOld (j) : Disjoint (F.symm '' baselineTriangle) (old j).val.image :=
      (hOld j).mono_left hTriangleSource
    obtain ⟨actualTriangleDisk,hActualTriangleEmbedded,hActualTriangleRange⟩ :=
      hActualBaselineTriangleDisk F eps heps hFamilyBox
    have hActualTriangleCompact : IsCompact (F.symm '' baselineTriangle) := by
      rw [← hActualTriangleRange]
      exact isCompact_range actualTriangleDisk.continuous
    have hTriangleOutside (z : ℝ × ℝ) (hz : z ∈ baselineTriangle) (hx : z.1 < 0) :
        F.symm z ∉ range B.disk := by
      let v : Interval → ℝ × ℝ := fun u =>
        ((1-u.val)*(-eps)+u.val*z.1,u.val*z.2)
      have hvx (u : Interval) : (v u).1 < 0 := by
        dsimp [v]
        by_cases hu : u.val=0
        · simp [hu,heps]
        · have hup : 0 < u.val := lt_of_le_of_ne u.property.1 (Ne.symm hu)
          have hn := mul_neg_of_pos_of_neg hup hx
          have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr u.property.2) (neg_nonpos.mpr heps.le)
          linarith
      have hv (u : Interval) : v u ∈ F.target := by
        have hh := hFamilyBox (-(v u).1) (v u).2 (le_of_lt (neg_pos.mpr (hvx u)))
          (by dsimp [v]; nlinarith [u.property.1,u.property.2,hz.1,
            mul_nonneg u.property.1 (show 0 ≤ z.1+eps by linarith [hz.1])])
          (by dsimp [v]; exact mul_nonneg u.property.1 hz.2.2.1)
          (by dsimp [v]; nlinarith [u.property.1,u.property.2,hz.2.1,hz.2.2.2,
            mul_nonneg (sub_nonneg.mpr u.property.2) (show 0 ≤ eps-z.2 by linarith [hz.2.1,hz.2.2.2])])
        simpa using hh
      let f : C(Interval,S) := ⟨fun u => F.symm (v u),
        F.symm.continuousOn.comp_continuous (by dsimp [v]; fun_prop) hv⟩
      have hfSource (u : Interval) : f u ∈ F.source := F.map_target (hv u)
      have hfCoord (u : Interval) : F (f u)=v u := F.right_inv (hv u)
      have hfBoundary : Disjoint (range f) (range B.firstSide ∪ range B.secondSide) := by
        apply Set.disjoint_left.mpr
        rintro x ⟨u,rfl⟩ (hfirst|hsecond)
        · have hh := hFirstPositive (f u) (hfSource u) hfirst
          rw [hfCoord] at hh
          linarith [hvx u]
        · have hh := (hBaxis (f u) (hfSource u)).mp (B.second_on_curve hsecond)
          rw [hfCoord] at hh
          linarith [hvx u]
      have hf0 : f 0=A := by
        change F.symm (v 0)=A
        have hh : v 0=F A := by simp [v,hAcoord]
        rw [hh,F.left_inv hAS]
      have hfree := hActualClosedDiskPathOutsideBoundary f hfBoundary (hf0 ▸ hAoffDisk)
      have hf1 : f 1=F.symm z := by change F.symm (v 1)=F.symm z; congr 1; simp [v]
      exact fun hh => Set.disjoint_left.mp hfree ⟨1,hf1⟩ hh
    have hTriangleDiskContact :
        (F.symm '' baselineTriangle) ∩ range B.disk =
          F.symm '' ({z : ℝ × ℝ | z.1=0 ∧ 0 ≤ z.2 ∧ z.2 ≤ eps}) := by
      ext x
      constructor
      · rintro ⟨⟨z,hz,rfl⟩,hD⟩
        have hx : z.1=0 := by
          by_contra hn
          exact hTriangleOutside z hz (lt_of_le_of_ne hz.2.1 hn) hD
        exact ⟨z,⟨hx,hz.2.2.1,by linarith [hz.2.2.2]⟩,rfl⟩
      · rintro ⟨z,⟨hx,hy0,hyε⟩,rfl⟩
        have hz : z ∈ baselineTriangle := by change -eps ≤ z.1 ∧ z.1 ≤ 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1+eps; simp only [hx,zero_add]; exact ⟨by linarith,le_rfl,hy0,hyε⟩
        refine ⟨⟨z,hz,rfl⟩,?_⟩
        have hside := (hSecondRay z.2 ⟨hy0,hyε.trans hepsell.le⟩).2
        have he : z=(0,z.2) := by ext <;> simp [hx]
        rw [← he] at hside
        exact image_subset_range _ _ (B.boundary_eq.symm ▸
          (show F.symm z ∈ range B.firstSide ∪ range B.secondSide from Or.inr hside))
    have hTriangleVerticalSeam (y : ℝ) (hy0 : 0<y) (hy1 : y<eps) :
        F.symm (0,y) ∈ interior (range B.disk ∪ F.symm '' baselineTriangle) := by
      letI := (actualSphereSmoothAtlas M).charts
      let r : ℝ := min y (eps-y)/4
      have hr : 0<r := div_pos (lt_min hy0 (sub_pos.mpr hy1)) (by norm_num)
      have hry : r<y := by dsimp [r]; linarith [min_le_left y (eps-y)]
      have hrε : 2*r<eps-y := by dsimp [r]; linarith [min_le_right y (eps-y)]
      let cy : BandWidth → ℝ := fun t => y+r*t.val
      have hcy (t : BandWidth) : 0<cy t ∧ cy t<eps := by
        dsimp [cy]
        have hlo := mul_le_mul_of_nonneg_left t.property.1 hr.le
        have hhi := mul_le_mul_of_nonneg_left t.property.2 hr.le
        norm_num at hlo hhi
        constructor <;> linarith
      let c : C(BandWidth,S) := ⟨fun t => F.symm (0,cy t),
        F.symm.continuousOn.comp_continuous (by dsimp [cy]; fun_prop)
          (fun t => by simpa using hFamilyBox 0 (cy t) le_rfl heps.le (hcy t).1.le (hcy t).2.le)⟩
      have hcF (t : BandWidth) : F (c t)=(0,cy t) :=
        F.right_inv (by simpa using hFamilyBox 0 (cy t) le_rfl heps.le (hcy t).1.le (hcy t).2.le)
      have hcb (t : BandWidth) : c t ∈ range B.secondSide :=
        (hSecondRay (cy t) ⟨(hcy t).1.le,(hcy t).2.le.trans hepsell.le⟩).2
      have hcBound (t : BandWidth) : c t ∈ B.disk ''
          {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
        B.boundary_eq.symm ▸ Or.inr (hcb t)
      let v : BandWidth → Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
        fun t => B.disk_embedded.toHomeomorph.symm ⟨c t,image_subset_range _ _ (hcBound t)⟩
      have hvimage (t : BandWidth) : B.disk (v t)=c t :=
        congrArg Subtype.val (B.disk_embedded.toHomeomorph.apply_symm_apply _)
      have hvnorm (t : BandWidth) : ‖(v t).val‖=1 := by
        obtain ⟨z,hz,he⟩ := hcBound t
        have hzv : v t=z := B.disk_embedded.injective ((hvimage t).trans he.symm)
        rw [hzv]
        simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hz
      have hvc : Continuous v := B.disk_embedded.toHomeomorph.symm.continuous.comp
        (c.continuous.subtype_mk _)
      have hvi : Function.Injective v := by
        intro t w he
        have hh := congrArg F ((hvimage t).symm.trans ((congrArg B.disk he).trans (hvimage w)))
        rw [hcF,hcF] at hh
        have hh1 := congrArg Prod.snd hh
        apply Subtype.ext
        dsimp [cy] at hh1
        exact mul_left_cancel₀ (ne_of_gt hr) (add_left_cancel hh1)
      let Ls : BandWidth × Interval → S := B.disk ∘ CapBandGeometry.diskRadialStrip v hvnorm
      have hLs : IsEmbedding Ls := B.disk_embedded.comp
        (CapBandGeometry.diskRadialStrip_embedded v hvnorm hvc hvi)
      have hLs0 (t : BandWidth) : Ls (t,0)=c t := by
        simp only [Ls,Function.comp_apply,CapBandGeometry.diskRadialStrip_zero,hvimage]
      have hLsD : range Ls ⊆ range B.disk := by rintro x ⟨p,rfl⟩; exact Set.mem_range_self _
      let z : BandWidth × Interval → ℝ × ℝ := fun p => (-(r/2)*p.2.val,cy p.1)
      have hz (p : BandWidth × Interval) : z p ∈ baselineTriangle := by
        change -eps ≤ -(r/2)*p.2.val ∧ -(r/2)*p.2.val ≤ 0 ∧ 0 ≤ cy p.1 ∧
          cy p.1 ≤ -(r/2)*p.2.val+eps
        have hulo : 0≤(r/2)*p.2.val := mul_nonneg (half_pos hr).le p.2.property.1
        have huhi : (r/2)*p.2.val≤r/2 := mul_le_of_le_one_right (half_pos hr).le p.2.property.2
        have hthi : r*p.1.val≤r := mul_le_of_le_one_right hr.le p.1.property.2
        dsimp [cy]
        constructor
        · linarith
        constructor
        · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) p.2.property.1
        constructor
        · exact (hcy p.1).1.le
        · linarith
      let Rs : BandWidth × Interval → S := fun p => F.symm (z p)
      have hRc : Continuous Rs := F.symm.continuousOn.comp_continuous
        (by dsimp [z,cy]; fun_prop) (fun p => hTriangleTarget (z p) (hz p))
      have hRF (p : BandWidth × Interval) : F (Rs p)=z p := F.right_inv (hTriangleTarget (z p) (hz p))
      have hRi : Function.Injective Rs := by
        intro p q he
        have hh := congrArg F he
        rw [hRF,hRF] at hh
        apply Prod.ext
        · apply Subtype.ext
          have hh1 := congrArg Prod.snd hh
          dsimp [z,cy] at hh1
          exact mul_left_cancel₀ (ne_of_gt hr) (add_left_cancel hh1)
        · apply Subtype.ext
          have hh0 := congrArg Prod.fst hh
          dsimp [z] at hh0
          exact mul_left_cancel₀ (show -(r/2)≠0 by linarith) hh0
      have hRs : IsEmbedding Rs := (hRc.isClosedEmbedding hRi).isEmbedding
      have hRsT : range Rs ⊆ F.symm '' baselineTriangle := by
        rintro x ⟨p,rfl⟩; exact ⟨z p,hz p,rfl⟩
      have hRs0 (t : BandWidth) : Rs (t,0)=c t := by simp [Rs,z,c]
      have hmeet : range Ls ∩ range Rs=range (fun t => Ls (t,0)) := by
        ext x
        constructor
        · rintro ⟨hxL,p,rfl⟩
          have hp0 : p.2=0 := by
            by_contra hn
            have hu : 0<p.2.val := lt_of_le_of_ne p.2.property.1
              (by intro he; exact hn (Subtype.ext he.symm))
            exact hTriangleOutside (z p) (hz p)
              (by change -(r/2)*p.2.val<0; nlinarith [mul_pos (half_pos hr) hu]) (hLsD hxL)
          refine ⟨p.1,?_⟩
          change Ls (p.1,0)=Rs p
          rw [hLs0,← hRs0]
          exact congrArg Rs (Prod.ext rfl hp0.symm)
        · rintro ⟨t,rfl⟩
          exact ⟨Set.mem_range_self _,⟨(t,0),(hRs0 t).trans (hLs0 t).symm⟩⟩
      have hsub : range Ls ∪ range Rs ⊆ range B.disk ∪ F.symm '' baselineTriangle :=
        Set.union_subset_union hLsD hRsT
      have hseam := CurveComplex.glued_half_rectangles_seam_interior_probe Ls Rs hLs hRs
        (fun t => (hLs0 t).trans (hRs0 t).symm) hmeet ⟨0,by norm_num⟩ (by norm_num) (by norm_num)
      have hcenter : Ls (⟨0,by norm_num⟩,0)=F.symm (0,y) := by simp [hLs0,c,cy]
      exact hcenter ▸ interior_mono hsub hseam
    have hL0side : L 0 ∈ range B.secondSide := by
      have hc : F (L 0)=(0,eps) := by rw [hLcoord]; simp
      have hray := (hSecondRay eps ⟨heps.le,hepsell.le⟩).2
      rw [← hc,F.left_inv (hLS 0)] at hray
      exact hray
    refine ⟨F,A,L,hpF,hFp,hFW,hAS,hMarks,hOld,hAK,hAfirst,hLS 0,hL0side,hL0notA,?_,jointCorner,hJointSource,hJointEmbedded,?_,?_,?_,?_⟩
    · intro j hh
      exact Set.disjoint_left.mp (hOld j) (hLS 0) hh
    · intro t
      rw [hJointStart]
      exact (congrArg F.symm hAcoord.symm).trans (F.left_inv hAS)
    · intro t
      rw [hJointEnd]
      exact (congrArg F.symm (hLcoord t).symm).trans (F.left_inv (hLS t))
    · refine ⟨eps,heps,hFp,hAcoord,?_,hJointCoordinates,hFamilyBox,hAaxis,hBaxis,hFirstPositive,actualTriangleDisk,
        hActualTriangleEmbedded,hActualTriangleRange,?_,?_,?_,?_,?_⟩
      · rw [hLcoord]; simp
      · rw [hActualTriangleRange]; exact hTriangleSource
      · rw [hActualTriangleRange]; exact hTriangleMarks
      · intro j; rw [hActualTriangleRange]; exact hTriangleOld j
      · rw [hActualTriangleRange]; exact hTriangleDiskContact
      · intro y hy0 hy1
        rw [hActualTriangleRange]
        exact hTriangleVerticalSeam y hy0 hy1
    · intro t ht
      obtain ⟨f,hfc,hf,hf0,hf1,hfS,hfa,hfb,hfm,hfo,hfr⟩ := hPaths t ht
      have hfFirst : Disjoint (range f) (range B.firstSide) := by
        apply Set.disjoint_left.mpr
        intro x hx hxFirst
        have hxA : x ∈ a.val.image := B.first_on_curve hxFirst
        have hxEq : x=A := Set.mem_singleton_iff.mp (hfa ▸ ⟨hx,hxA⟩)
        exact hAfirst (hxEq ▸ hxFirst)
      have hfSecond : Disjoint (range f) (range B.secondSide) :=
        hfb.mono_right B.second_on_curve
      have hfDisk := hActualClosedDiskPathOutsideBoundary f
        (Set.disjoint_union_right.mpr ⟨hfFirst,hfSecond⟩) (hf0.symm ▸ hAoffDisk)
      have hfK : range f ∩ Kraw={A} := by
        ext x
        constructor
        · intro hx
          have hxA : x ∈ a.val.image := hdecompRaw.symm ▸ Or.inr hx.2
          exact hfa ▸ ⟨hx.1,hxA⟩
        · rintro rfl
          exact ⟨⟨0,hf0⟩,hAK⟩
      refine ⟨f,hf,hf0,hf1,hfS,hfDisk,hfa,hfK,hfb,hfm,hfo,hfr,?_⟩
      intro u
      exact F.injOn (hfS (Set.mem_range_self u)) (hJointSource t u)
        ((hfc u).trans (hJointCoordinates t u).symm)
  have hActualJointMarkedCornerFamily
      (F : OpenPartialHomeomorph S Plane) (p : S)
      (hpF : p ∈ F.source) (hFp : F p=0)
      (R κ ell τ : ℝ) (hR : 0 < R) (hκ : 0 < κ)
      (hell : 0 < ell) (hellR : ell < R) (hτ : τ= -1 ∨ τ=1)
      (hTarget : ∀ z : Plane, 0 < z 0 → z 0 < R →
        -κ*z 0 < z 1 → z 1 < κ*z 0 → z ∈ F.target) :
      ∃ H : C(Interval × Interval,S),
        (∀ t u : Interval, H (t,u) ∈ F.source) ∧
        (∀ t u : Interval, F (H (t,u))=Plane.mk (ell*u.val)
          ((ell*u.val)*(τ*((κ/4)*t.val)))) ∧
        (∀ t : Interval, IsEmbedding (fun u : Interval => H (t,u))) ∧
        (∀ t : Interval, H (t,0)=p) ∧
        (∀ t : Interval, H (t,1)=F.symm (Plane.mk ell (ell*(τ*((κ/4)*t.val))))) := by
    let q (t s : Interval) : Plane :=
      Plane.mk (ell*s.val) ((ell*s.val)*(τ*((κ/4)*t.val)))
    have hcone (t s : Interval) (hs : 0 < s.val) :
        0 < (q t s) 0 ∧ (q t s) 0 < R ∧
        -κ*(q t s) 0 < (q t s) 1 ∧ (q t s) 1 < κ*(q t s) 0 := by
      have hx : 0 < ell*s.val := mul_pos hell hs
      have hxR : ell*s.val < R := lt_of_le_of_lt
        (mul_le_of_le_one_right hell.le s.property.2) hellR
      have hh : 0 ≤ (κ/4)*t.val ∧ (κ/4)*t.val < κ := by
        constructor
        · exact mul_nonneg (by positivity) t.property.1
        · nlinarith [t.property.2]
      have hhl : -κ < τ*((κ/4)*t.val) ∧ τ*((κ/4)*t.val) < κ := by
        rcases hτ with rfl|rfl <;> simp only [neg_one_mul,one_mul] <;> constructor <;> linarith
      change 0 < ell*s.val ∧ ell*s.val < R ∧
        -κ*(ell*s.val) < (ell*s.val)*(τ*((κ/4)*t.val)) ∧
        (ell*s.val)*(τ*((κ/4)*t.val)) < κ*(ell*s.val)
      exact ⟨hx,hxR,by nlinarith [mul_pos hx (sub_pos.mpr hhl.1)],
        by nlinarith [mul_pos hx (sub_pos.mpr hhl.2)]⟩
    have hq0 (t : Interval) : q t 0 = (0:Plane) := by
      ext i
      fin_cases i <;> simp [q]
    have htarget (t s : Interval) : q t s ∈ F.target := by
      by_cases hs : s.val = 0
      · have hs0 : s = 0 := Subtype.ext hs
        rw [hs0,hq0,← hFp]
        exact F.map_source hpF
      · have hh := hcone t s (lt_of_le_of_ne s.property.1 (Ne.symm hs))
        exact hTarget (q t s) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
    let H : C(Interval × Interval,S) := ⟨fun v => F.symm (q v.1 v.2),
      F.symm.continuousOn.comp_continuous (by dsimp [q]; fun_prop)
        (fun v => htarget v.1 v.2)⟩
    have hcoord (t u : Interval) : F (H (t,u))=q t u := F.right_inv (htarget t u)
    refine ⟨H,(fun t u => F.map_target (htarget t u)),hcoord,?_,?_,?_⟩
    · intro t
      have hc : Continuous (fun u : Interval => H (t,u)) :=
        H.continuous.comp (continuous_const.prodMk continuous_id)
      apply (hc.isClosedEmbedding ?_).isEmbedding
      intro u v huv
      have hh := congrArg (fun x : S => F x 0) huv
      rw [hcoord,hcoord] at hh
      exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hell) hh)
    · intro t
      change F.symm (q t 0)=p
      rw [hq0,← hFp,F.left_inv hpF]
    · intro t
      change F.symm (q t 1)=_
      simp [q]
  have hActualMarkedRoundedExteriorFamily (p : S)
      (hpmark : p ∈ M.cover.branch)
      (hpCorner : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
      (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
      ∃ F : OpenPartialHomeomorph S Plane, ∃ L : C(Interval,S),
        p ∈ F.source ∧ F p=0 ∧ F.source ⊆ W ∧
        F.source ∩ (M.cover.branch : Set S)={p} ∧
        L 0 ∈ F.source ∧ L 0 ∈ range B.secondSide ∧ L 0 ∉ a.val.image ∧
        (∀ j, L 0 ∉ (old j).val.image) ∧
        ∃ H : C(Interval × Interval,S),
        (∀ t u : Interval, H (t,u) ∈ F.source) ∧
        (∀ t : Interval, IsEmbedding (fun u : Interval => H (t,u))) ∧
        (∀ t : Interval, H (t,0)=p) ∧ (∀ t : Interval, H (t,1)=L t) ∧
        (∀ u : Interval, H (0,u) ∈ range B.secondSide) ∧
        (∃ Wwide : Set S, IsCompact Wwide ∧ Wwide ⊆ F.source ∧
          Wwide ∩ (M.cover.branch : Set S) ⊆ {p} ∧ Wwide ∩ a.val.image ⊆ {p} ∧
          Wwide ∩ range B.disk ⊆ range B.secondSide ∧
          (∀ t u : Interval, H (t,u) ∈ Wwide) ∧
          (∀ t u : Interval, 0<t.val → 0<u.val → H (t,u) ∈ interior Wwide) ∧
          ∃ g : C(Interval,S), IsEmbedding g ∧ g 0=p ∧ range g ⊆ range B.secondSide ∧
            range g ⊆ Wwide ∧ range g=Wwide ∩ range B.disk ∧
            (∀ u : Interval, 0<u.val → u.val<1 → g u ∈ interior (range B.disk ∪ Wwide)) ∧
            ∃ outer : C(Interval,S), IsEmbedding outer ∧ outer 0=p ∧ outer 1=g 1 ∧
              range outer ⊆ Wwide ∧ range outer ∩ range B.secondSide={p,g 1} ∧
              range outer ∩ a.val.image ⊆ {p} ∧ frontier Wwide ⊆ range g ∪ range outer) ∧
        ∀ t : Interval, 0<t.val → ∃ f : C(Interval,S),
          IsEmbedding f ∧ f 0=p ∧ f 1=L t ∧ range f ⊆ F.source ∧
          range f \ {p} ⊆ (range B.disk)ᶜ ∧
          range f ∩ a.val.image={p} ∧ range f ∩ b.val.image={p} ∧
          range f ∩ Kraw={p} ∧ range f ∩ (M.cover.branch : Set S)={p} ∧
          (∀ j, Disjoint (range f) (arcInterior M (old j))) ∧
          (∀ u : Interval, f u=H (t,u)) := by
    letI : CompactSpace S := M.sphere.symm.compactSpace
    letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      Subtype.connectedSpace (isConnected_sphere
        (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
        0 (by norm_num))
    letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
    letI := (actualSphereSmoothAtlas M).charts
    letI := (actualSphereSmoothAtlas M).manifold
    letI : ClosedSurface S := {}
    obtain ⟨terminal,s,hs,hshalf,hend,hSideGerm⟩ := hActualSelectedSideEndpointLabel p hpmark hpCorner
    obtain ⟨F,hpF,hFp,hFW,hmarks,R,κ,hR,hR1,hκ,hκ1,hCone⟩ :=
      actual_marked_corner_cone_from_selected_side_germ M old a b
        (fun i j hij => (hOld i j hij).1) hab (fun j => (ha j).1) (fun j => (hb j).1) B
        p hpmark W hW hpW terminal hend s hs hshalf hSideGerm
    have hclosed : IsClosed (range B.disk) := (isCompact_range B.disk.continuous).isClosed
    have hregular : range B.disk ⊆ closure (interior (range B.disk)) := by
      rw [CurveComplex.actual_embedded_disk_closure_interior B.disk B.disk_embedded]
    have hFrontier (z : Plane) (hx : 0<z 0) (hxr : z 0<R)
        (hlo : -κ*z 0<z 1) (hhi : z 1<κ*z 0) :
        F.symm z ∈ frontier (range B.disk) ↔ z 1=0 := by
      obtain ⟨hzT,haFree,hOldFree,hBaxis,hSideAxis⟩ := hCone z hx hxr hlo hhi
      rw [hOriginalDiskFrontier]
      constructor
      · rintro (hfirst|hsecond)
        · exact False.elim (haFree (B.first_on_curve hfirst))
        · exact hBaxis.mp (B.second_on_curve hsecond)
      · intro hz
        exact Or.inr (hSideAxis hz)
    obtain ⟨τ,hτ,hSector⟩ := CurveComplex.actual_chart_cone_interior_sector F (range B.disk)
      hclosed hregular R κ hR hκ
      (fun z hx hxr hlo hhi => (hCone z hx hxr hlo hhi).1) hFrontier
    have hOutsideSector (z : Plane) (hx : 0<z 0) (hxr : z 0<R)
        (hlo : -κ*z 0<z 1) (hhi : z 1<κ*z 0) :
        F.symm z ∈ interior (range B.disk)ᶜ ↔ 0<(-τ)*z 1 := by
      rw [hclosed.isOpen_compl.interior_eq]
      have hτne : τ≠0 := by rcases hτ with rfl|rfl <;> norm_num
      constructor
      · intro hnot
        have hy : z 1≠0 := by
          intro hz
          exact hnot (hclosed.frontier_subset ((hFrontier z hx hxr hlo hhi).mpr hz))
        have hnotInside : F.symm z ∉ interior (range B.disk) := fun hh => hnot (interior_subset hh)
        have hnonpos : τ*z 1≤0 := le_of_not_gt (fun hh =>
          hnotInside ((hSector z hx hxr hlo hhi).mpr hh))
        have hnegative : τ*z 1<0 := lt_of_le_of_ne hnonpos (mul_ne_zero hτne hy)
        nlinarith
      · intro hnegative hDisk
        have hy : z 1≠0 := by intro hz; rw [hz,mul_zero] at hnegative; linarith
        have hnotFront : F.symm z ∉ frontier (range B.disk) :=
          fun hh => hy ((hFrontier z hx hxr hlo hhi).mp hh)
        have hInside : F.symm z ∈ interior (range B.disk) := by
          by_contra hn
          exact hnotFront (hclosed.frontier_eq ▸ ⟨hDisk,hn⟩)
        have hpos := (hSector z hx hxr hlo hhi).mp hInside
        nlinarith
    have hnegτ : -τ= -1 ∨ -τ=1 := by rcases hτ with rfl|rfl <;> simp
    obtain ⟨L,hL,hL0,hLS,hPaths⟩ := CurveComplex.actual_interior_corner_endpoint_family
      F (range B.disk)ᶜ p hpF hFp R κ (R/2) (-τ) hR hκ (half_pos hR)
      (by linarith) hnegτ
      (fun z hx hxr hlo hhi => (hCone z hx hxr hlo hhi).1) hOutsideSector
    obtain ⟨jointMarked,hJointMarkedSource,hJointMarkedCoord,hJointMarkedEmbedded,hJointMarkedStart,hJointMarkedEnd⟩ :=
      hActualJointMarkedCornerFamily F p hpF hFp R κ (R/2) (-τ) hR hκ (half_pos hR)
        (by linarith) hnegτ (fun z hx hxr hlo hhi => (hCone z hx hxr hlo hhi).1)
    have hActualMarkedWideEnvelope :
    ∃ Wwide : Set S, IsCompact Wwide ∧ Wwide ⊆ F.source ∧
              Wwide ∩ (M.cover.branch : Set S) ⊆ {p} ∧
              Wwide ∩ a.val.image ⊆ {p} ∧
              Wwide ∩ range B.disk ⊆ range B.secondSide ∧
              (∀ t u : Interval, jointMarked (t,u) ∈ Wwide) ∧
              (∀ t u : Interval, 0<t.val → 0<u.val → jointMarked (t,u) ∈ interior Wwide) ∧
              ∃ g : C(Interval,S), IsEmbedding g ∧ g 0=p ∧ range g ⊆ range B.secondSide ∧
                range g ⊆ Wwide ∧ range g=Wwide ∩ range B.disk ∧ (∀ u : Interval, 0<u.val → u.val<1 →
                  g u ∈ interior (range B.disk ∪ Wwide)) ∧
                ∃ outer : C(Interval,S), IsEmbedding outer ∧ outer 0=p ∧ outer 1=g 1 ∧
                  range outer ⊆ Wwide ∧ range outer ∩ range B.secondSide={p,g 1} ∧
                  range outer ∩ a.val.image ⊆ {p} ∧ frontier Wwide ⊆ range g ∪ range outer := by
      classical
      letI : T2Space S := M.sphere.symm.t2Space
      
      let σ : ℝ := -τ
      have hσ : σ= -1 ∨ σ=1 := hnegτ
      have hσsq : σ*σ=1 := by rcases hσ with hh|hh <;> rw [hh] <;> norm_num
      let V : Set (ℝ × ℝ) := {z | 0≤z.1 ∧ z.1≤3*R/4 ∧ 0≤σ*z.2 ∧ σ*z.2≤(κ/2)*z.1}
      let P : Set (ℝ × ℝ) := {z | 0<z.1 ∧ z.1<3*R/4 ∧ 0<σ*z.2 ∧ σ*z.2<(κ/2)*z.1}
      let toPlane : (ℝ × ℝ) → Plane := fun z => Plane.mk z.1 z.2
      have hTarget (z : ℝ × ℝ) (hz : z ∈ V) : toPlane z ∈ F.target := by
        by_cases hx : z.1=0
        · have hy : z.2=0 := by
            have hh : σ*z.2=0 := le_antisymm (by simpa [hx] using hz.2.2.2) hz.2.2.1
            rcases hσ with hs|hs <;> rw [hs] at hh <;> linarith
          have he : toPlane z=0 := by ext i; fin_cases i <;> simp [toPlane,hx,hy]
          rw [he,← hFp]; exact F.map_source hpF
        · have hxpos : 0<z.1 := lt_of_le_of_ne hz.1 (Ne.symm hx)
          have hxr : z.1<R := by linarith [hz.2.1]
          have hlow : -κ*z.1<z.2 := by
            rcases hσ with hs|hs <;> dsimp only [V] at hz <;> rw [hs] at hz <;>
              nlinarith [hz.2.2.1,hz.2.2.2,mul_pos hκ hxpos]
          have hhigh : z.2<κ*z.1 := by
            rcases hσ with hs|hs <;> dsimp only [V] at hz <;> rw [hs] at hz <;>
              nlinarith [hz.2.2.1,hz.2.2.2,mul_pos hκ hxpos]
          exact (hCone (toPlane z) hxpos hxr hlow hhigh).1
      have hVc : IsClosed V :=
        (isClosed_le continuous_const continuous_fst).inter
          ((isClosed_le continuous_fst continuous_const).inter
            ((isClosed_le continuous_const (show Continuous (fun z : ℝ × ℝ => σ*z.2) by fun_prop)).inter
              (isClosed_le (show Continuous (fun z : ℝ × ℝ => σ*z.2) by fun_prop) (show Continuous (fun z : ℝ × ℝ => (κ/2)*z.1) by fun_prop))))
      have hVbound : V ⊆ (Icc 0 (3*R/4)) ×ˢ Icc (-κ*R) (κ*R) := by
        intro z hz
        have hx := hz.2.1
        have h0 := hz.2.2.1
        have h1 := hz.2.2.2
        rcases hσ with hs|hs <;> rw [hs] at h0 h1 <;> refine ⟨⟨hz.1,hx⟩,?_,?_⟩ <;>
          nlinarith [mul_pos hκ hR,mul_nonneg hκ.le hz.1,
            mul_nonneg hκ.le (show 0≤3*R/4-z.1 by linarith)]
      have hVk : IsCompact V := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hVc hVbound
      have hToPlane : Continuous toPlane := by dsimp [toPlane]; fun_prop
      let Wwide : Set S := F.symm '' (toPlane '' V)
      have hWsource : Wwide ⊆ F.source := by
        rintro x ⟨q,⟨z,hz,rfl⟩,rfl⟩
        exact F.map_target (hTarget z hz)
      have hWcompact : IsCompact Wwide := (hVk.image hToPlane).image_of_continuousOn
        (F.symm.continuousOn.mono (by rintro q ⟨z,hz,rfl⟩; exact hTarget z hz))
      have hWpoint (z : ℝ × ℝ) (hz : z ∈ V) (hx : z.1=0) : F.symm (toPlane z)=p := by
        have hy : z.2=0 := by
          have hh : σ*z.2=0 := le_antisymm (by simpa [hx] using hz.2.2.2) hz.2.2.1
          rcases hσ with hs|hs <;> rw [hs] at hh <;> linarith
        have he : toPlane z=F p := by rw [hFp]; ext i; fin_cases i <;> simp [toPlane,hx,hy]
        rw [he,F.left_inv hpF]
      have hConeBounds (z : ℝ × ℝ) (hz : z ∈ V) (hx : 0<z.1) :
          z.1<R ∧ -κ*z.1<z.2 ∧ z.2<κ*z.1 := by
        have hxr : z.1<R := by linarith [hz.2.1]
        refine ⟨hxr,?_,?_⟩
        all_goals rcases hσ with hs|hs <;> dsimp only [V] at hz <;> rw [hs] at hz <;>
          nlinarith [hz.2.2.1,hz.2.2.2,mul_pos hκ hx]
      have hCoordinates (t u : Interval) :
          σ*((R/2*u.val)*(σ*((κ/4)*t.val)))=(R/2*u.val)*((κ/4)*t.val) := by
        calc
          _ = (σ*σ)*(R/2*u.val)*((κ/4)*t.val) := by ring
          _ = _ := by rw [hσsq]; ring
      have hJointV (t u : Interval) :
          ((R/2)*u.val,((R/2)*u.val)*(σ*((κ/4)*t.val))) ∈ V := by
        have hx0 := mul_nonneg (half_pos hR).le u.property.1
        have hx1 : (R/2)*u.val≤R/2 := mul_le_of_le_one_right (half_pos hR).le u.property.2
        have ht0 := mul_nonneg (show 0≤κ/4 by positivity) t.property.1
        have ht1 : (κ/4)*t.val≤κ/4 := mul_le_of_le_one_right (by positivity) t.property.2
        change 0≤(R/2)*u.val ∧ (R/2)*u.val≤3*R/4 ∧ _
        rw [hCoordinates]
        exact ⟨hx0,by linarith,mul_nonneg hx0 ht0,
          by nlinarith [mul_nonneg hx0 (show 0≤κ/2-(κ/4)*t.val by linarith)]⟩
      refine ⟨Wwide,hWcompact,hWsource,?_,?_,?_,?_,?_,?_⟩
      · intro x hx
        exact hmarks ▸ (show x ∈ F.source ∩ (M.cover.branch : Set S) from ⟨hWsource hx.1,hx.2⟩)
      · rintro x ⟨⟨q,⟨z,hz,rfl⟩,rfl⟩,haX⟩
        by_cases hx : z.1=0
        · exact Set.mem_singleton_iff.mpr (hWpoint z hz hx)
        · have hb := hConeBounds z hz (lt_of_le_of_ne hz.1 (Ne.symm hx))
          exact False.elim ((hCone _ (lt_of_le_of_ne hz.1 (Ne.symm hx)) hb.1 hb.2.1 hb.2.2).2.1 haX)
      · rintro x ⟨⟨q,⟨z,hz,rfl⟩,rfl⟩,hxD⟩
        by_cases hx : z.1=0
        · rw [hWpoint z hz hx]
          rcases hpCorner with he|he
          · exact ⟨0,B.second_zero.trans he.symm⟩
          · have he1 : p=B.secondCorner := by simpa using he
            exact ⟨1,B.second_one.trans he1.symm⟩
        · have hxp := lt_of_le_of_ne hz.1 (Ne.symm hx)
          have hb := hConeBounds z hz hxp
          have hy0 : z.2=0 := by
            by_contra hn
            have hy : 0<σ*z.2 := lt_of_le_of_ne hz.2.2.1
              (by rcases hσ with hs|hs <;> rw [hs] <;> simpa [eq_comm] using hn)
            have hh := (hOutsideSector (toPlane z) hxp hb.1 hb.2.1 hb.2.2).mpr hy
            rw [hclosed.isOpen_compl.interior_eq] at hh
            exact hh hxD
          exact (hCone _ hxp hb.1 hb.2.1 hb.2.2).2.2.2.2 hy0
      · intro t u
        refine ⟨toPlane ((R/2*u.val),(R/2*u.val)*(σ*((κ/4)*t.val))),?_,?_⟩
        · exact ⟨_,hJointV t u,rfl⟩
        · dsimp only [toPlane,σ]
          rw [← hJointMarkedCoord t u,F.left_inv (hJointMarkedSource t u)]
      · intro t u ht hu
        have hPo : IsOpen P := (isOpen_lt continuous_const continuous_fst).inter
          ((isOpen_lt continuous_fst continuous_const).inter
            ((isOpen_lt continuous_const (show Continuous (fun z : ℝ × ℝ => σ*z.2) by fun_prop)).inter
              (isOpen_lt (show Continuous (fun z : ℝ × ℝ => σ*z.2) by fun_prop) (show Continuous (fun z : ℝ × ℝ => (κ/2)*z.1) by fun_prop))))
        have hPsub : P ⊆ V := fun _ hz => ⟨hz.1.le,hz.2.1.le,hz.2.2.1.le,hz.2.2.2.le⟩
        have hzP : ((R/2)*u.val,((R/2)*u.val)*(σ*((κ/4)*t.val))) ∈ P := by
          have hx := mul_pos (half_pos hR) hu
          have hx1 : (R/2)*u.val≤R/2 := mul_le_of_le_one_right (half_pos hR).le u.property.2
          have htpos := mul_pos (show 0<κ/4 by positivity) ht
          have ht1 : (κ/4)*t.val≤κ/4 := mul_le_of_le_one_right (by positivity) t.property.2
          change 0<(R/2)*u.val ∧ (R/2)*u.val<3*R/4 ∧ _
          rw [hCoordinates]
          exact ⟨hx,by linarith,mul_pos hx htpos,
            by nlinarith [mul_pos hx (show 0<κ/2-(κ/4)*t.val by linarith)]⟩
        -- Use the coordinate homeomorphism for openness of the whole wedge image.
        let e : (ℝ × ℝ) ≃ₜ Plane := {
          toFun := toPlane
          invFun := fun z => (z 0,z 1)
          left_inv := by intro z; rfl
          right_inv := by intro z; ext i; fin_cases i <;> rfl
          continuous_toFun := hToPlane
          continuous_invFun := by fun_prop }
        have hOpenPlane : IsOpen (toPlane '' P) := e.isOpenMap _ hPo
        have hOpenS : IsOpen (F.symm '' (toPlane '' P)) :=
          F.symm.isOpen_image_of_subset_source hOpenPlane
            (by rintro q ⟨z,hz,rfl⟩; exact hTarget z (hPsub hz))
        apply interior_maximal (Set.image_mono (Set.image_mono hPsub)) hOpenS
        refine ⟨toPlane ((R/2*u.val),(R/2*u.val)*(σ*((κ/4)*t.val))),⟨_,hzP,rfl⟩,?_⟩
        dsimp only [toPlane,σ]
        rw [← hJointMarkedCoord t u,F.left_inv (hJointMarkedSource t u)]
      · let qb : Interval → ℝ × ℝ := fun u => ((3*R/4)*u.val,0)
        have hqV (u : Interval) : qb u ∈ V := by
          have hx : 0≤(3*R/4)*u.val := mul_nonneg (by positivity) u.property.1
          change 0≤(3*R/4)*u.val ∧ (3*R/4)*u.val≤3*R/4 ∧ 0≤σ*0 ∧ σ*0≤(κ/2)*((3*R/4)*u.val)
          simp only [mul_zero]
          exact ⟨hx,mul_le_of_le_one_right (by positivity) u.property.2,le_rfl,
            mul_nonneg (by positivity) hx⟩
        let g : C(Interval,S) := ⟨fun u => F.symm (toPlane (qb u)),
          F.symm.continuousOn.comp_continuous (hToPlane.comp (by dsimp [qb]; fun_prop))
            (fun u => hTarget _ (hqV u))⟩
        have hgsource (u : Interval) : g u ∈ F.source := F.map_target (hTarget _ (hqV u))
        have hgcoord (u : Interval) : F (g u)=toPlane (qb u) := F.right_inv (hTarget _ (hqV u))
        have hgi : Function.Injective g := by
          intro u v he
          have hh := congrArg (fun q : Plane => q 0) (congrArg F he)
          rw [hgcoord,hgcoord] at hh
          change (3*R/4)*u.val=(3*R/4)*v.val at hh
          exact Subtype.ext (mul_left_cancel₀ (by positivity : (3*R/4)≠0) hh)
        have hg0 : g 0=p := by
          exact hWpoint _ (hqV 0) (by simp [qb])
        have hgside : range g ⊆ range B.secondSide := by
          rintro x ⟨u,rfl⟩
          by_cases hu : u=0
          · rw [hu,hg0]
            rcases hpCorner with he|he
            · exact ⟨0,B.second_zero.trans he.symm⟩
            · have he1 : p=B.secondCorner := by simpa using he
              exact ⟨1,B.second_one.trans he1.symm⟩
          · have hx : 0<(qb u).1 := mul_pos (by positivity)
              (lt_of_le_of_ne u.property.1 (fun he => hu (Subtype.ext he.symm)))
            have hb := hConeBounds _ (hqV u) hx
            exact (hCone (toPlane (qb u)) hx hb.1 hb.2.1 hb.2.2).2.2.2.2 rfl
        have hgW : range g ⊆ Wwide := by
          rintro x ⟨u,rfl⟩
          exact ⟨toPlane (qb u),⟨qb u,hqV u,rfl⟩,rfl⟩
        have hgContact : range g=Wwide ∩ range B.disk := by
          apply Set.Subset.antisymm
          · intro x hx
            exact ⟨hgW hx,image_subset_range _ _ (B.boundary_eq.symm ▸
              (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inr (hgside hx)))⟩
          · rintro x ⟨⟨q,⟨z,hz,rfl⟩,rfl⟩,hxD⟩
            have hy0 : z.2=0 := by
              by_cases hx : z.1=0
              · have hh : σ*z.2=0 := le_antisymm (by simpa [hx] using hz.2.2.2) hz.2.2.1
                rcases hσ with hs|hs <;> rw [hs] at hh <;> linarith
              · have hxp := lt_of_le_of_ne hz.1 (Ne.symm hx)
                have hb := hConeBounds z hz hxp
                by_contra hn
                have hy : 0<σ*z.2 := lt_of_le_of_ne hz.2.2.1
                  (by rcases hσ with hs|hs <;> rw [hs] <;> simpa [eq_comm] using hn)
                have hh := (hOutsideSector (toPlane z) hxp hb.1 hb.2.1 hb.2.2).mpr hy
                rw [hclosed.isOpen_compl.interior_eq] at hh
                exact hh hxD
            have hmpos : 0<3*R/4 := by positivity
            let u : Interval := ⟨z.1/(3*R/4),div_nonneg hz.1 hmpos.le,
              (div_le_one hmpos).mpr hz.2.1⟩
            have hqeq : qb u=z := by
              apply Prod.ext
              · change (3*R/4)*(z.1/(3*R/4))=z.1
                field_simp [ne_of_gt hmpos]
              · exact hy0.symm
            refine ⟨u,?_⟩
            change F.symm (toPlane (qb u))=F.symm (toPlane z)
            rw [hqeq]
        refine ⟨g,(g.continuous.isClosedEmbedding hgi).isEmbedding,hg0,hgside,hgW,hgContact,?_,?_⟩
        · intro u hu0 hu1
          let O : Set (ℝ × ℝ) := {z | 0<z.1 ∧ z.1<3*R/4 ∧
            -(κ/2)*z.1<σ*z.2 ∧ σ*z.2<(κ/2)*z.1}
          have hOo : IsOpen O := (isOpen_lt continuous_const continuous_fst).inter
            ((isOpen_lt continuous_fst continuous_const).inter
              ((isOpen_lt (show Continuous (fun z : ℝ × ℝ => -(κ/2)*z.1) by fun_prop)
                (show Continuous (fun z : ℝ × ℝ => σ*z.2) by fun_prop)).inter
                (isOpen_lt (show Continuous (fun z : ℝ × ℝ => σ*z.2) by fun_prop)
                  (show Continuous (fun z : ℝ × ℝ => (κ/2)*z.1) by fun_prop))))
          have hObounds (z : ℝ × ℝ) (hz : z ∈ O) :
              z.1<R ∧ -κ*z.1<z.2 ∧ z.2<κ*z.1 := by
            have hxr : z.1<R := by linarith [hz.2.1]
            refine ⟨hxr,?_,?_⟩
            all_goals rcases hσ with hs|hs <;> dsimp only [O] at hz <;> rw [hs] at hz <;>
              nlinarith [hz.2.2.1,hz.2.2.2,mul_pos hκ hz.1]
          have hOt : toPlane '' O ⊆ F.target := by
            rintro q ⟨z,hz,rfl⟩
            have hb := hObounds z hz
            exact (hCone _ hz.1 hb.1 hb.2.1 hb.2.2).1
          let e : (ℝ × ℝ) ≃ₜ Plane := {
            toFun := toPlane
            invFun := fun z => (z 0,z 1)
            left_inv := by intro z; rfl
            right_inv := by intro z; ext i; fin_cases i <;> rfl
            continuous_toFun := hToPlane
            continuous_invFun := by fun_prop }
          have hOpenS : IsOpen (F.symm '' (toPlane '' O)) :=
            F.symm.isOpen_image_of_subset_source (e.isOpenMap _ hOo) hOt
          have hImageSub : F.symm '' (toPlane '' O) ⊆ range B.disk ∪ Wwide := by
            rintro x ⟨q,⟨z,hz,rfl⟩,rfl⟩
            by_cases hy : 0≤σ*z.2
            · exact Or.inr ⟨toPlane z,⟨z,⟨hz.1.le,hz.2.1.le,hy,hz.2.2.2.le⟩,rfl⟩,rfl⟩
            · apply Or.inl
              by_contra hD
              have hb := hObounds z hz
              have hc : F.symm (toPlane z) ∈ interior (range B.disk)ᶜ := by
                rw [hclosed.isOpen_compl.interior_eq]
                exact hD
              have hh := (hOutsideSector (toPlane z) hz.1 hb.1 hb.2.1 hb.2.2).mp hc
              exact hy hh.le
          have hqO : qb u ∈ O := by
            have hx := mul_pos (show 0<3*R/4 by positivity) hu0
            have hupper := mul_lt_of_lt_one_right (show 0<3*R/4 by positivity) hu1
            have hκx := mul_pos (half_pos hκ) hx
            change 0<(3*R/4)*u.val ∧ (3*R/4)*u.val<3*R/4 ∧ -(κ/2)*((3*R/4)*u.val)<σ*0 ∧ σ*0<(κ/2)*((3*R/4)*u.val)
            simp only [mul_zero]
            exact ⟨hx,hupper,by linarith,by linarith⟩
          exact interior_maximal hImageSub hOpenS ⟨toPlane (qb u),⟨qb u,hqO,rfl⟩,rfl⟩
        · let m : ℝ := 3*R/4
          let K : ℝ := (κ/2)*m
          have hm : 0< m := by dsimp [m]; positivity
          have hK : 0< K := mul_pos (half_pos hκ) hm
          have hσcancel (y : ℝ) : σ*(σ*y)=y := by
            rcases hσ with hs|hs <;> rw [hs] <;> ring
          let qd : Interval → ℝ × ℝ := fun u => (m*u.val,σ*((κ/2)*(m*u.val)))
          let qv : Interval → ℝ × ℝ := fun u => (m,σ*(K*(1-u.val)))
          have hqd (u : Interval) : qd u ∈ V := by
            have hx : 0≤ m*u.val := mul_nonneg hm.le u.property.1
            change 0≤ m*u.val ∧ m*u.val≤ m ∧ 0≤σ*(σ*((κ/2)*(m*u.val))) ∧
              σ*(σ*((κ/2)*(m*u.val)))≤(κ/2)*(m*u.val)
            rw [hσcancel]
            exact ⟨hx,mul_le_of_le_one_right hm.le u.property.2,mul_nonneg (half_pos hκ).le hx,le_rfl⟩
          have hqv (u : Interval) : qv u ∈ V := by
            change 0≤ m ∧ m≤ m ∧ 0≤σ*(σ*(K*(1-u.val))) ∧ σ*(σ*(K*(1-u.val)))≤(κ/2)*m
            rw [hσcancel]
            exact ⟨hm.le,le_rfl,mul_nonneg hK.le (sub_nonneg.mpr u.property.2),by dsimp [K] at *; nlinarith [u.property.1]⟩
          let d : C(Interval,S) := ⟨fun u => F.symm (toPlane (qd u)),
            F.symm.continuousOn.comp_continuous (hToPlane.comp (by dsimp [qd]; fun_prop))
              (fun u => hTarget _ (hqd u))⟩
          let v : C(Interval,S) := ⟨fun u => F.symm (toPlane (qv u)),
            F.symm.continuousOn.comp_continuous (hToPlane.comp (by dsimp [qv]; fun_prop))
              (fun u => hTarget _ (hqv u))⟩
          have hdc (u : Interval) : F (d u)=toPlane (qd u) := F.right_inv (hTarget _ (hqd u))
          have hvc (u : Interval) : F (v u)=toPlane (qv u) := F.right_inv (hTarget _ (hqv u))
          have hdW : range d ⊆ Wwide := by rintro x ⟨u,rfl⟩; exact ⟨_,⟨qd u,hqd u,rfl⟩,rfl⟩
          have hvW : range v ⊆ Wwide := by rintro x ⟨u,rfl⟩; exact ⟨_,⟨qv u,hqv u,rfl⟩,rfl⟩
          have hdn (u : Interval) : σ*(F (d u) 1)=K*u.val := by
            rw [hdc]
            change σ*(σ*((κ/2)*(m*u.val)))=K*u.val
            rw [hσcancel]; dsimp [K]; ring
          have hvn (u : Interval) : σ*(F (v u) 1)=K*(1-u.val) := by
            rw [hvc]
            exact hσcancel _
          have hgn (u : Interval) : σ*(F (g u) 1)=0 := by
            rw [hgcoord]
            change σ*0=0
            ring
          have hdi : Function.Injective d := by
            intro u w he
            have hh := congrArg (fun q : Plane => q 0) (congrArg F he)
            rw [hdc,hdc] at hh
            change m*u.val=m*w.val at hh
            exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hm) hh)
          have hvi : Function.Injective v := by
            intro u w he
            have hh := congrArg (fun q : Plane => σ*q 1) (congrArg F he)
            rw [hvn,hvn] at hh
            have hh' := mul_left_cancel₀ (ne_of_gt hK) hh
            exact Subtype.ext (by linarith)
          have hd0 : d 0=p := hWpoint _ (hqd 0) (by simp [qd])
          have hdv : d 1=v 0 := by
            change F.symm (toPlane (qd 1))=F.symm (toPlane (qv 0))
            have hh : qd 1=qv 0 := by simp [qd,qv,K]
            rw [hh]
          have hv1 : v 1=g 1 := by
            change F.symm (toPlane (qv 1))=F.symm (toPlane (qb 1))
            have hh : qv 1=qb 1 := by simp [qv,qb,m]
            rw [hh]
          have hMeet : range d ∩ range v={d 1} := by
            ext x
            constructor
            · rintro ⟨⟨u,rfl⟩,⟨w,he⟩⟩
              have hh := congrArg (fun q : Plane => q 0) (congrArg F he)
              rw [hvc,hdc] at hh
              change m=m*u.val at hh
              have hu : u=1 := Subtype.ext (by change u.val=1; nlinarith)
              subst u
              rfl
            · rintro rfl
              exact ⟨⟨1,rfl⟩,⟨0,hdv.symm⟩⟩
          obtain ⟨outer,ho,ho0,ho1,hoRange⟩ := CurveComplex.source_embedded_arc_concatenation d v
            (d.continuous.isClosedEmbedding hdi).isEmbedding (v.continuous.isClosedEmbedding hvi).isEmbedding
            hdv hMeet
          have hoW : range outer ⊆ Wwide := by
            rw [hoRange]
            exact Set.union_subset hdW hvW
          have hBdisk (x : S) (hx : x ∈ range B.secondSide) : x ∈ range B.disk :=
            image_subset_range _ _ (B.boundary_eq.symm ▸
              (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inr hx))
          have hOuterB : range outer ∩ range B.secondSide={p,g 1} := by
            ext x
            constructor
            · rintro ⟨hx,hxb⟩
              have hxg : x ∈ range g := hgContact.symm ▸ ⟨hoW hx,hBdisk x hxb⟩
              obtain ⟨w,hw⟩ := hxg
              rw [hoRange] at hx
              rcases hx with ⟨u,hu⟩|⟨u,hu⟩
              · have hh : K*u.val=0 := by
                  rw [← hdn u,hu,← hw,hgn w]
                have hu0 : u=0 := Subtype.ext ((mul_eq_zero.mp hh).resolve_left (ne_of_gt hK))
                exact Or.inl (hu.symm.trans ((congrArg d hu0).trans hd0))
              · have hh : K*(1-u.val)=0 := by
                  rw [← hvn u,hu,← hw,hgn w]
                have hz : 1-u.val=0 := (mul_eq_zero.mp hh).resolve_left (ne_of_gt hK)
                have hu1 : u=1 := Subtype.ext (by change u.val=1; linarith)
                exact Or.inr (hu.symm.trans ((congrArg v hu1).trans hv1))
            · rintro (he|he)
              · have hx : x=p := he
                rw [hx]
                exact ⟨⟨0,ho0.trans hd0⟩,hg0 ▸ hgside (Set.mem_range_self 0)⟩
              · have hx : x=g 1 := by simpa using he
                rw [hx]
                exact ⟨⟨1,ho1.trans hv1⟩,hgside (Set.mem_range_self 1)⟩
          have hOuterA : range outer ∩ a.val.image ⊆ {p} := by
            rintro x ⟨hx,hxa⟩
            rw [hoRange] at hx
            rcases hx with ⟨u,rfl⟩|⟨u,rfl⟩
            · by_cases hu : u=0
              · rw [hu,hd0]; exact Set.mem_singleton p
              · have hxpos : 0<(qd u).1 := mul_pos hm
                  (lt_of_le_of_ne u.property.1 (fun he => hu (Subtype.ext he.symm)))
                have hb := hConeBounds _ (hqd u) hxpos
                exact False.elim ((hCone (toPlane (qd u)) hxpos hb.1 hb.2.1 hb.2.2).2.1 hxa)
            · have hb := hConeBounds _ (hqv u) hm
              exact False.elim ((hCone (toPlane (qv u)) hm hb.1 hb.2.1 hb.2.2).2.1 hxa)
          have hAxisImage (z : ℝ × ℝ) (hz : z ∈ V) (hy : z.2=0) :
              F.symm (toPlane z) ∈ range g := by
            let u : Interval := ⟨z.1/m,div_nonneg hz.1 hm.le,(div_le_one hm).mpr hz.2.1⟩
            have hh : qb u=z := by
              apply Prod.ext
              · change m*(z.1/m)=z.1
                field_simp [ne_of_gt hm]
              · exact hy.symm
            exact ⟨u,by change F.symm (toPlane (qb u))=F.symm (toPlane z); rw [hh]⟩
          have hVerticalImage (z : ℝ × ℝ) (hz : z ∈ V) (hx : z.1=m) :
              F.symm (toPlane z) ∈ range v := by
            have hratio0 : 0≤(σ*z.2)/K := div_nonneg hz.2.2.1 hK.le
            have hratio1 : (σ*z.2)/K≤1 := (div_le_one hK).mpr (by simpa [K,hx] using hz.2.2.2)
            let u : Interval := ⟨1-(σ*z.2)/K,sub_nonneg.mpr hratio1,by linarith⟩
            have hn : K*(1-u.val)=σ*z.2 := by dsimp [u]; field_simp [ne_of_gt hK]; ring
            have hh : qv u=z := by
              apply Prod.ext
              · exact hx.symm
              · change σ*(K*(1-u.val))=z.2
                rw [hn,hσcancel]
            exact ⟨u,by change F.symm (toPlane (qv u))=F.symm (toPlane z); rw [hh]⟩
          have hDiagonalImage (z : ℝ × ℝ) (hz : z ∈ V) (hy : σ*z.2=(κ/2)*z.1) :
              F.symm (toPlane z) ∈ range d := by
            let u : Interval := ⟨z.1/m,div_nonneg hz.1 hm.le,(div_le_one hm).mpr hz.2.1⟩
            have hu : m*u.val=z.1 := by dsimp [u]; field_simp [ne_of_gt hm]
            have hh : qd u=z := by
              apply Prod.ext
              · exact hu
              · change σ*((κ/2)*(m*u.val))=z.2
                rw [hu,← hy,hσcancel]
            exact ⟨u,by change F.symm (toPlane (qd u))=F.symm (toPlane z); rw [hh]⟩
          refine ⟨outer,ho,ho0.trans hd0,ho1.trans hv1,hoW,hOuterB,hOuterA,?_⟩
          intro x hx
          have hxW := hWcompact.isClosed.frontier_subset hx
          obtain ⟨q,⟨z,hz,rfl⟩,he⟩ := hxW
          by_cases hy0 : σ*z.2=0
          · have hy : z.2=0 := by rcases hσ with hs|hs <;> rw [hs] at hy0 <;> linarith
            exact Or.inl (he ▸ hAxisImage z hz hy)
          by_cases hxmax : z.1=m
          · exact Or.inr (hoRange.symm ▸ Or.inr (he ▸ hVerticalImage z hz hxmax))
          by_cases hdiag : σ*z.2=(κ/2)*z.1
          · exact Or.inr (hoRange.symm ▸ Or.inl (he ▸ hDiagonalImage z hz hdiag))
          · have hxpos : 0<z.1 := by
              have hypos := lt_of_le_of_ne hz.2.2.1 (Ne.symm hy0)
              nlinarith [hz.2.2.2]
            have hzP : z ∈ P := ⟨hxpos,lt_of_le_of_ne hz.2.1 hxmax,
              lt_of_le_of_ne hz.2.2.1 (Ne.symm hy0),lt_of_le_of_ne hz.2.2.2 hdiag⟩
            have hPo : IsOpen P := (isOpen_lt continuous_const continuous_fst).inter
              ((isOpen_lt continuous_fst continuous_const).inter
                ((isOpen_lt continuous_const (show Continuous (fun z : ℝ × ℝ => σ*z.2) by fun_prop)).inter
                  (isOpen_lt (show Continuous (fun z : ℝ × ℝ => σ*z.2) by fun_prop)
                    (show Continuous (fun z : ℝ × ℝ => (κ/2)*z.1) by fun_prop))))
            have hPsub : P ⊆ V := fun _ hq => ⟨hq.1.le,hq.2.1.le,hq.2.2.1.le,hq.2.2.2.le⟩
            let e : (ℝ × ℝ) ≃ₜ Plane := {
              toFun := toPlane
              invFun := fun z => (z 0,z 1)
              left_inv := by intro z; rfl
              right_inv := by intro z; ext i; fin_cases i <;> rfl
              continuous_toFun := hToPlane
              continuous_invFun := by fun_prop }
            have hOpen : IsOpen (F.symm '' (toPlane '' P)) :=
              F.symm.isOpen_image_of_subset_source (e.isOpenMap _ hPo)
                (by rintro q ⟨w,hw,rfl⟩; exact hTarget w (hPsub hw))
            have hi : x ∈ interior Wwide := interior_maximal
              (Set.image_mono (Set.image_mono hPsub)) hOpen ⟨toPlane z,⟨z,hzP,rfl⟩,he⟩
            exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hi hx)
    have hBase := hCone (Plane.mk (R/2) 0) (by change 0<R/2; linarith)
      (by change R/2<R; linarith)
      (by change -κ*(R/2)<0; nlinarith [mul_pos hκ hR])
      (by change 0<κ*(R/2); positivity)
    have hpA : p ∈ a.val.image := by
      rcases hpCorner with he|he
      · exact B.first_on_curve ⟨0,B.first_zero.trans he.symm⟩
      · exact B.first_on_curve ⟨1,B.first_one.trans he.symm⟩
    have hpB : p ∈ b.val.image := by
      cases terminal
      · exact ⟨0,hend⟩
      · exact ⟨1,hend⟩
    have hpK : p ∈ Kraw := (hmeetRaw.symm ▸ hpCorner).2
    refine ⟨F,L,hpF,hFp,hFW,hmarks,hLS 0,?_,?_,?_,jointMarked,hJointMarkedSource,hJointMarkedEmbedded,hJointMarkedStart,?_,?_,?_,?_⟩
    · rw [hL0]; exact hBase.2.2.2.2 rfl
    · rw [hL0]; exact hBase.2.1
    · intro j; rw [hL0]; exact hBase.2.2.1 j
    · intro t
      rw [hJointMarkedEnd,hL]
    · intro u
      by_cases hu : u=0
      · rw [hu,hJointMarkedStart]
        rcases hpCorner with he|he
        · exact ⟨0,B.second_zero.trans he.symm⟩
        · have he1 : p=B.secondCorner := by simpa using he
          exact ⟨1,B.second_one.trans he1.symm⟩
      · have hup : 0<u.val := lt_of_le_of_ne u.property.1
          (by intro he; exact hu (Subtype.ext he.symm))
        have hx : 0<(R/2)*u.val := mul_pos (half_pos hR) hup
        have hxr : (R/2)*u.val<R := by nlinarith [u.property.2]
        have hz : Plane.mk ((R/2)*u.val) 0 ∈ F.target :=
          (hCone _ hx hxr (by change -κ*((R/2)*u.val)<0; nlinarith [mul_pos hκ hx])
            (by change 0<κ*((R/2)*u.val); positivity)).1
        have hcoord : F (jointMarked (0,u))=Plane.mk ((R/2)*u.val) 0 := by
          simpa using hJointMarkedCoord (0:Interval) u
        have he : jointMarked (0,u)=F.symm (Plane.mk ((R/2)*u.val) 0) := by
          rw [← hcoord,F.left_inv (hJointMarkedSource 0 u)]
        rw [he]
        exact (hCone _ hx hxr (by change -κ*((R/2)*u.val)<0; nlinarith [mul_pos hκ hx])
          (by change 0<κ*((R/2)*u.val); positivity)).2.2.2.2 rfl
    · exact hActualMarkedWideEnvelope
    · intro t ht
      obtain ⟨f,hf,hf0,hf1,hfS,hfOutside,hfCone,hfCoord⟩ := hPaths t ht
      have hOutside : range f \ {p} ⊆ (range B.disk)ᶜ := hfOutside.trans interior_subset
      have hFree (u : Interval) (hu : 0<u.val) : f u ∉ a.val.image ∧ f u ∉ b.val.image ∧
          ∀ j, f u ∉ (old j).val.image := by
        have hc := hfCone u hu
        have hd := hCone (F (f u)) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
        rw [F.left_inv (hfS (Set.mem_range_self u))] at hd
        refine ⟨hd.2.1,?_,hd.2.2.1⟩
        intro hb
        have hy0 := hd.2.2.2.1.mp hb
        rw [hfCoord] at hy0
        change (R/2*u.val)*((-τ)*((κ/4)*t.val))=0 at hy0
        have hτne : -τ≠0 := by rcases hτ with rfl|rfl <;> norm_num
        exact mul_ne_zero (ne_of_gt (mul_pos (half_pos hR) hu))
          (mul_ne_zero hτne (ne_of_gt (mul_pos (by positivity : 0<κ/4) ht))) hy0
      have hIntersection (A : Set S) (hpA : p ∈ A)
          (hFreeA : ∀ u : Interval, 0<u.val → f u ∉ A) : range f ∩ A={p} := by
        ext x
        constructor
        · rintro ⟨⟨u,rfl⟩,huA⟩
          have hu0 : u=0 := by
            by_contra hn
            have hup : 0<u.val := lt_of_le_of_ne u.property.1
              (by intro he; exact hn (Subtype.ext he.symm))
            exact hFreeA u hup huA
          simp [hu0,hf0]
        · rintro rfl
          exact ⟨⟨0,hf0⟩,hpA⟩
      have hfa : range f ∩ a.val.image={p} := hIntersection _ hpA (fun u hu => (hFree u hu).1)
      have hfb : range f ∩ b.val.image={p} := hIntersection _ hpB (fun u hu => (hFree u hu).2.1)
      have hfK : range f ∩ Kraw={p} := hIntersection _ hpK (fun u hu hk =>
        (hFree u hu).1 (hdecompRaw.symm ▸ Or.inr hk))
      refine ⟨f,hf,hf0,hf1,hfS,hOutside,hfa,hfb,hfK,?_,?_,?_⟩
      · ext x
        constructor
        · rintro ⟨hx,hm⟩; exact hmarks ▸ ⟨hfS hx,hm⟩
        · rintro rfl; exact ⟨⟨0,hf0⟩,hpmark⟩
      · intro j
        apply Set.disjoint_left.mpr
        rintro x ⟨u,rfl⟩ huOld
        by_cases hu0 : u=0
        · subst u; rw [hf0] at huOld; exact huOld.2 hpmark
        · have hu : 0<u.val := lt_of_le_of_ne u.property.1
            (by intro he; exact hu0 (Subtype.ext he.symm))
          exact (hFree u hu).2.2 j huOld.1
      · intro u
        exact F.injOn (hfS (Set.mem_range_self u)) (hJointMarkedSource t u)
          ((hfCoord u).trans (hJointMarkedCoord t u).symm)
  have hActualUnifiedRoundedCornerFamily (p : S)
      (hpCorner : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
      (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
      ∃ F : OpenPartialHomeomorph S Plane, ∃ A : S, ∃ L : C(Interval,S),
        p ∈ F.source ∧ F p=0 ∧ F.source ⊆ W ∧ A ∈ F.source ∧ A ∈ Kraw ∧
        (p ∈ M.cover.branch → A=p) ∧ (p ∉ M.cover.branch → A ∉ range B.firstSide) ∧
        F.source ∩ (M.cover.branch : Set S) ⊆ {p} ∧
        L 0 ∈ F.source ∧ L 0 ∈ range B.secondSide ∧ L 0 ∉ a.val.image ∧
        (∀ j, L 0 ∉ (old j).val.image) ∧
        ∃ H : C(Interval × Interval,S),
        (∀ t u : Interval, H (t,u) ∈ F.source) ∧
        (∀ t : Interval, IsEmbedding (fun u : Interval => H (t,u))) ∧
        (∀ t : Interval, H (t,0)=A) ∧ (∀ t : Interval, H (t,1)=L t) ∧
        (p ∈ M.cover.branch → ∀ u : Interval, H (0,u) ∈ range B.secondSide) ∧
        (p ∈ M.cover.branch → ∃ Wwide : Set S, IsCompact Wwide ∧ Wwide ⊆ F.source ∧
          Wwide ∩ (M.cover.branch : Set S) ⊆ {p} ∧ Wwide ∩ a.val.image ⊆ {p} ∧
          Wwide ∩ range B.disk ⊆ range B.secondSide ∧
          (∀ t u : Interval, H (t,u) ∈ Wwide) ∧
          (∀ t u : Interval, 0<t.val → 0<u.val → H (t,u) ∈ interior Wwide) ∧
          ∃ g : C(Interval,S), IsEmbedding g ∧ g 0=p ∧ range g ⊆ range B.secondSide ∧
            range g ⊆ Wwide ∧ range g=Wwide ∩ range B.disk ∧
            (∀ u : Interval, 0<u.val → u.val<1 → g u ∈ interior (range B.disk ∪ Wwide)) ∧
            ∃ outer : C(Interval,S), IsEmbedding outer ∧ outer 0=p ∧ outer 1=g 1 ∧
              range outer ⊆ Wwide ∧ range outer ∩ range B.secondSide={p,g 1} ∧
              range outer ∩ a.val.image ⊆ {p} ∧ frontier Wwide ⊆ range g ∪ range outer) ∧
        (p ∉ M.cover.branch → ∃ G : OpenPartialHomeomorph S (ℝ × ℝ), G.source=F.source ∧
          ∃ delta : ℝ, 0 < delta ∧ G p=(0,0) ∧ G A=(-delta,0) ∧ G (L 0)=(0,delta) ∧
          (∀ t u : Interval, G (H (t,u))=(-(delta*(1-u.val)+(delta/2*t.val)*u.val),delta*u.val)) ∧
          (∀ x y : ℝ, 0 ≤ x → x ≤ delta → 0 ≤ y → y ≤ delta → (-x,y) ∈ G.target) ∧
          (∀ x ∈ G.source, x ∈ a.val.image ↔ (G x).2=0) ∧
          (∀ x ∈ G.source, x ∈ b.val.image ↔ (G x).1=0) ∧
          (∀ x ∈ G.source, x ∈ range B.firstSide → 0 ≤ (G x).1) ∧
          ∃ d : C(closedBall (0 : ℝ × ℝ) 1,S), IsEmbedding d ∧
            range d=G.symm '' {z : ℝ × ℝ | -delta ≤ z.1 ∧ z.1 ≤ 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1+delta} ∧
            range d ⊆ G.source ∧
            Disjoint (range d) (M.cover.branch : Set S) ∧
            (∀ j, Disjoint (range d) (old j).val.image) ∧
            range d ∩ range B.disk=G.symm '' {z : ℝ × ℝ | z.1=0 ∧ 0 ≤ z.2 ∧ z.2 ≤ delta} ∧
            (∀ y : ℝ, 0<y → y<delta → G.symm (0,y) ∈ interior (range B.disk ∪ range d))) ∧
        ∀ t : Interval, 0<t.val → ∃ f : C(Interval,S),
          IsEmbedding f ∧ f 0=A ∧ f 1=L t ∧ range f ⊆ F.source ∧
          range f \ {A} ⊆ (range B.disk)ᶜ ∧
          range f ∩ a.val.image={A} ∧ range f ∩ Kraw={A} ∧
          range f ∩ b.val.image=(if p ∈ M.cover.branch then {p} else ∅) ∧
          range f ∩ (M.cover.branch : Set S) ⊆ {p} ∧
          (∀ j, Disjoint (range f) (arcInterior M (old j))) ∧
          (∀ u : Interval, f u=H (t,u)) := by
    by_cases hpmark : p ∈ M.cover.branch
    · obtain ⟨F,L,hpF,hFp,hFW,hmarks,hLsource,hLside,hLa,hLo,H,hHS,hHEmbedded,hH0,hH1,hHBase,hHWide,hpaths⟩ :=
        hActualMarkedRoundedExteriorFamily p hpmark hpCorner W hW hpW
      have hpK : p ∈ Kraw := (hmeetRaw.symm ▸ hpCorner).2
      refine ⟨F,p,L,hpF,hFp,hFW,hpF,hpK,(fun _ => rfl),
        (fun hn => False.elim (hn hpmark)),hmarks.le,hLsource,hLside,hLa,hLo,H,hHS,hHEmbedded,hH0,hH1,(fun _ => hHBase),(fun _ => hHWide),(fun hn => False.elim (hn hpmark)),?_⟩
      intro t ht
      obtain ⟨f,hf,hf0,hf1,hfs,hfo,hfa,hfb,hfK,hfm,hfold,hJoint⟩ := hpaths t ht
      exact ⟨f,hf,hf0,hf1,hfs,hfo,hfa,hfK,by simpa [hpmark] using hfb,hfm.le,hfold,hJoint⟩
    · have hpA : p ∈ a.val.image := by
        rcases hpCorner with he|he
        · exact B.first_on_curve ⟨0,B.first_zero.trans he.symm⟩
        · exact B.first_on_curve ⟨1,B.first_one.trans he.symm⟩
      have hpB : p ∈ b.val.image := by
        rcases hpCorner with he|he
        · exact B.second_on_curve ⟨0,B.second_zero.trans he.symm⟩
        · exact B.second_on_curve ⟨1,B.second_one.trans he.symm⟩
      have hpCross : p ∈ crossings M a b := ⟨⟨hpA,hpmark⟩,hpB,hpmark⟩
      obtain ⟨G,A,L,hpG,hGp,hGW,hAG,hmarks,hOld,hAK,hAfirst,hLsource,hLside,hLa,hLo,H,hHS,hHEmbedded,hH0,hH1,hTriData,hpaths⟩ :=
        hActualUnmarkedRoundedExteriorFamily p hpCorner hpCross W hW hpW
      let xy : (ℝ × ℝ) ≃ₜ Plane := {
        toFun := fun z => Plane.mk z.1 z.2
        invFun := fun z => (z 0,z 1)
        left_inv := by intro z; rfl
        right_inv := by intro z; ext i; fin_cases i <;> rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      let F := G.transHomeomorph xy
      have hFs : F.source=G.source := rfl
      have hFp : F p=0 := by
        change Plane.mk (G p).1 (G p).2=0
        rw [hGp]
        ext i; fin_cases i <;> rfl
      have hEmptyMarks : F.source ∩ (M.cover.branch : Set S) ⊆ {p} := by
        intro x hx
        exact False.elim (Set.disjoint_left.mp hmarks hx.1 hx.2)
      refine ⟨F,A,L,hpG,hFp,hGW,hAG,hAK,(fun hh => False.elim (hpmark hh)),
        (fun _ => hAfirst),hEmptyMarks,hLsource,hLside,hLa,hLo,H,hHS,hHEmbedded,hH0,hH1,(fun hh => False.elim (hpmark hh)),(fun hh => False.elim (hpmark hh)),(fun _ => ⟨G,rfl,hTriData⟩),?_⟩
      intro t ht
      obtain ⟨f,hf,hf0,hf1,hfs,hfd,hfa,hfK,hfb,hfm,hfold,hfr,hJoint⟩ := hpaths t ht
      refine ⟨f,hf,hf0,hf1,hfs,?_,hfa,hfK,?_,?_,?_,hJoint⟩
      · intro x hx; exact fun hxD => Set.disjoint_left.mp hfd hx.1 hxD
      · simpa [hpmark] using Set.disjoint_iff_inter_eq_empty.mp hfb
      · intro x hx; exact False.elim (Set.disjoint_left.mp hfm hx.1 hx.2)
      · intro j; exact (hfold j).mono_right (fun x hx => hx.1)
  have hActualUnmarkedParameterNeighborhood (c : EssentialMarkedArc M)
      (t₀ : Interval) (ht₀ : 0<t₀.val ∧ t₀.val<1)
      (α β : ℝ) (hα : α<t₀.val) (hβ : t₀.val<β) :
      ∃ W : Set S, IsOpen W ∧ c.val.map t₀ ∈ W ∧
        ∀ t : Interval, c.val.map t ∈ W → α<t.val ∧ t.val<β := by
    let leftTail : Set Interval := {t | t.val≤α}
    let rightTail : Set Interval := {t | β≤t.val}
    have hleft : IsCompact leftTail := (isClosed_le continuous_subtype_val continuous_const).isCompact
    have hright : IsCompact rightTail := (isClosed_le continuous_const continuous_subtype_val).isCompact
    let W : Set S := (c.val.map '' leftTail ∪ c.val.map '' rightTail)ᶜ
    refine ⟨W,((hleft.image c.val.continuous).union (hright.image c.val.continuous)).isClosed.isOpen_compl,?_,?_⟩
    · rintro (⟨t,ht,he⟩|⟨t,ht,he⟩)
      all_goals
        rcases c.val.injective_except_loop_closure t t₀ he with he|he|he
        · subst t
          dsimp [leftTail,rightTail] at ht
          linarith
        · have hh := congrArg Subtype.val he.2
          change t₀.val=1 at hh
          linarith [ht₀.2]
        · have hh := congrArg Subtype.val he.2
          change t₀.val=0 at hh
          linarith [ht₀.1]
    · intro t ht
      constructor
      · by_contra hn
        exact ht (Or.inl ⟨t,le_of_not_gt hn,rfl⟩)
      · by_contra hn
        exact ht (Or.inr ⟨t,le_of_not_gt hn,rfl⟩)
  have hOriginalSelectedPorts : {(a.val.map ∘ Set.projIcc 0 1 zero_le_one) L,
        (a.val.map ∘ Set.projIcc 0 1 zero_le_one) R}=({B.firstCorner,B.secondCorner} : Set S) := by
    obtain ⟨f,hfi,hf0,hf1,hf,K,hK,hfull,hmeet⟩ :=
      hActualMarkedSubarcRemainder a L R hL hLR hR hproper
    have hfSide : range f=range B.firstSide := hf.trans hSide.symm
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
  let corner : Bool → S := fun i => if i then B.secondCorner else B.firstCorner
  let tail : Bool → Set Interval := fun i =>
    if i then {t | t.val ≤ 1-commonδ/2} else {t | commonδ/2 ≤ t.val}
  have hTailCompact (i : Bool) : IsCompact (tail i) := by
    dsimp [tail]
    split_ifs
    · exact (isClosed_le continuous_subtype_val continuous_const).isCompact
    · exact (isClosed_le continuous_const continuous_subtype_val).isCompact
  have hActualUnmarkedPortParameterNeighborhood (p : S)
      (hp : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
      (hpm : p ∉ M.cover.branch) :
      ∃ W : Set S, IsOpen W ∧ p ∈ W ∧
        ∀ t : Interval, a.val.map t ∈ W → a.val.map t ∉ range B.firstSide →
          0<t.val ∧ t.val<1 ∧
          ((p=(a.val.map ∘ Set.projIcc 0 1 zero_le_one) L ∧ t.val<L) ∨
           (p=(a.val.map ∘ Set.projIcc 0 1 zero_le_one) R ∧ R<t.val)) := by
    let γ := a.val.map ∘ Set.projIcc 0 1 zero_le_one
    have hpPorts : p ∈ ({γ L,γ R} : Set S) := hOriginalSelectedPorts.symm ▸ hp
    have hSelected (t : Interval) (ht : L≤t.val ∧ t.val≤R) : a.val.map t ∈ range B.firstSide := by
      rw [hSide]
      refine ⟨t.val,ht,?_⟩
      change a.val.map (Set.projIcc 0 1 zero_le_one t.val)=a.val.map t
      congr 1
      simpa using Set.projIcc_of_mem zero_le_one t.property
    rcases hpPorts with hpL|hpR
    · let t₀ := Set.projIcc 0 1 zero_le_one L
      have ht₀L : t₀.val=L := congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hL,hLR.le.trans hR⟩)
      have hp₀ : a.val.map t₀=p := hpL.symm
      have ht₀ : 0<t₀.val ∧ t₀.val<1 := by
        constructor
        · by_contra hn
          have he : t₀=(0 : Interval) := Subtype.ext (le_antisymm (le_of_not_gt hn) t₀.property.1)
          exact hpm (hp₀ ▸ (he.symm ▸ a.val.start_marked))
        · by_contra hn
          have he : t₀=(1 : Interval) := Subtype.ext (le_antisymm t₀.property.2 (le_of_not_gt hn))
          exact hpm (hp₀ ▸ (he.symm ▸ a.val.end_marked))
      obtain ⟨W,hW,hpW,hwindow⟩ := hActualUnmarkedParameterNeighborhood a t₀ ht₀
        (L/2) ((L+R)/2) (by rw [ht₀L] at *; linarith [ht₀.1]) (by rw [ht₀L]; linarith)
      refine ⟨W,hW,hp₀ ▸ hpW,?_⟩
      intro t ht hoff
      obtain ⟨hlo,hhi⟩ := hwindow t ht
      have hleft : t.val<L := by
        by_contra hn
        exact hoff (hSelected t ⟨le_of_not_gt hn,by linarith⟩)
      exact ⟨by linarith,by linarith,Or.inl ⟨hpL,hleft⟩⟩
    · let t₀ := Set.projIcc 0 1 zero_le_one R
      have ht₀R : t₀.val=R := congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hL.trans hLR.le,hR⟩)
      have hp₀ : a.val.map t₀=p := hpR.symm
      have ht₀ : 0<t₀.val ∧ t₀.val<1 := by
        constructor
        · by_contra hn
          have he : t₀=(0 : Interval) := Subtype.ext (le_antisymm (le_of_not_gt hn) t₀.property.1)
          exact hpm (hp₀ ▸ (he.symm ▸ a.val.start_marked))
        · by_contra hn
          have he : t₀=(1 : Interval) := Subtype.ext (le_antisymm t₀.property.2 (le_of_not_gt hn))
          exact hpm (hp₀ ▸ (he.symm ▸ a.val.end_marked))
      obtain ⟨W,hW,hpW,hwindow⟩ := hActualUnmarkedParameterNeighborhood a t₀ ht₀
        ((L+R)/2) ((R+1)/2) (by rw [ht₀R]; linarith) (by rw [ht₀R] at *; linarith [ht₀.2])
      refine ⟨W,hW,hp₀ ▸ hpW,?_⟩
      intro t ht hoff
      obtain ⟨hlo,hhi⟩ := hwindow t ht
      have hright : R<t.val := by
        by_contra hn
        exact hoff (hSelected t ⟨by linarith,le_of_not_gt hn⟩)
      exact ⟨by linarith,by linarith,Or.inr ⟨hpR,hright⟩⟩
  let baseCornerW : Bool → Set S := fun i => (B.secondSide '' tail i)ᶜ
  have hBaseCornerWOpen (i : Bool) : IsOpen (baseCornerW i) :=
    ((hTailCompact i).image B.secondSide.continuous).isClosed.isOpen_compl
  have hBaseCornerInW (i : Bool) : corner i ∈ baseCornerW i := by
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
  obtain ⟨sep0,sep1,hSep0,hSep1,hInSep0,hInSep1,hSepDisjoint⟩ := t2_separation hcornersNe
  let cornerSep : Bool → Set S := fun i => if i then sep1 else sep0
  have hCornerSepOpen (i : Bool) : IsOpen (cornerSep i) := by cases i <;> assumption
  have hCornerInSep (i : Bool) : corner i ∈ cornerSep i := by cases i <;> assumption
  have hCornerMember (i : Bool) : corner i ∈ ({B.firstCorner,B.secondCorner} : Set S) := by
    cases i <;> simp [corner]
  have hCornerParameterNeighborhood (i : Bool) :
      ∃ W : Set S, IsOpen W ∧ corner i ∈ W ∧
        ∀ t : Interval, a.val.map t ∈ W → a.val.map t ∉ range B.firstSide →
          corner i ∉ M.cover.branch →
          0<t.val ∧ t.val<1 ∧
          ((corner i=(a.val.map ∘ Set.projIcc 0 1 zero_le_one) L ∧ t.val<L) ∨
           (corner i=(a.val.map ∘ Set.projIcc 0 1 zero_le_one) R ∧ R<t.val)) := by
    by_cases hm : corner i ∈ M.cover.branch
    · exact ⟨univ,isOpen_univ,Set.mem_univ _,fun t ht hf hn => False.elim (hn hm)⟩
    · obtain ⟨W,hW,hpW,hlabels⟩ := hActualUnmarkedPortParameterNeighborhood (corner i) (hCornerMember i) hm
      exact ⟨W,hW,hpW,fun t ht hf _ => hlabels t ht hf⟩
  choose cornerParamW hCornerParamWOpen hCornerParamWPoint hCornerParamWLabels using hCornerParameterNeighborhood
  let cornerW : Bool → Set S := fun i => (baseCornerW i ∩ cornerParamW i) ∩ cornerSep i
  have hCornerWOpen (i : Bool) : IsOpen (cornerW i) :=
    ((hBaseCornerWOpen i).inter (hCornerParamWOpen i)).inter (hCornerSepOpen i)
  have hCornerInW (i : Bool) : corner i ∈ cornerW i :=
    ⟨⟨hBaseCornerInW i,hCornerParamWPoint i⟩,hCornerInSep i⟩
  choose cornerF cornerA cornerL hCornerPoint hCornerCenter hCornerSource
    hCornerASource hCornerAK hCornerAMarked hCornerAUnmarked hCornerMarks
    hCornerBaselineSource hCornerBaselineSide hCornerBaselineA hCornerBaselineOld cornerH hCornerJointSource hCornerJointEmbedded hCornerJointStart hCornerJointEnd hCornerMarkedBaselineWholeSide hCornerMarkedWideEnvelope hCornerBaselineTriangleData hCornerPaths using
      fun i => hActualUnifiedRoundedCornerFamily (corner i) (hCornerMember i)
        (cornerW i) (hCornerWOpen i) (hCornerInW i)
  have hCornerActualBaselineTriangle (i : Bool) :
      ∃ T : Set S, IsCompact T ∧ T ⊆ (cornerF i).source ∧
        Disjoint T (M.cover.branch : Set S) ∧
        (∀ j, Disjoint T (old j).val.image) ∧
        T ∩ range B.disk ⊆ range B.secondSide ∧
        (corner i ∈ M.cover.branch → T=∅) ∧
        (corner i ∉ M.cover.branch → cornerA i ∈ T ∧ corner i ∈ T ∧
          cornerL i 0 ∈ T ∧ range (fun u : Interval => cornerH i (0,u)) ⊆ T) ∧
        (corner i ∉ M.cover.branch → ∃ G : OpenPartialHomeomorph S (ℝ × ℝ), ∃ δ : ℝ,
          G.source=(cornerF i).source ∧ 0 < δ ∧ G (corner i)=(0,0) ∧ G (cornerA i)=(-δ,0) ∧
          G (cornerL i 0)=(0,δ) ∧
          (∀ t u : Interval, G (cornerH i (t,u))=(-(δ*(1-u.val)+(δ/2*t.val)*u.val),δ*u.val)) ∧
          (∀ x y : ℝ, 0 ≤ x → x ≤ δ → 0 ≤ y → y ≤ δ → (-x,y) ∈ G.target) ∧
          (∀ x ∈ G.source, x ∈ a.val.image ↔ (G x).2=0) ∧
          (∀ x ∈ G.source, x ∈ b.val.image ↔ (G x).1=0) ∧
          T=G.symm '' {z : ℝ × ℝ | -δ ≤ z.1 ∧ z.1 ≤ 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1+δ} ∧
          (∀ y : ℝ, 0<y → y<δ → G.symm (0,y) ∈ interior (range B.disk ∪ T)) ∧
          (∀ y : ℝ, 0 ≤ y → y ≤ δ → G.symm (0,y) ∈ range B.secondSide)) := by
    by_cases hm : corner i ∈ M.cover.branch
    · refine ⟨∅,isCompact_empty,empty_subset _,by simp,?_,?_,fun _ => rfl,?_,?_⟩
      · intro j; simp
      · simp
      · intro hn; exact False.elim (hn hm)
      · intro hn; exact False.elim (hn hm)
    · obtain ⟨G,hGS,δ,hδ,hGp,hGA,hGL,hJoint,hBox,hAAxis,hBAxis,hFirstPositive,
        d,hd,hRange,hSource,hMarks,hOld,hContact,hSharedInterior⟩ := hCornerBaselineTriangleData i hm
      have hVerticalSelected (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ δ) :
          G.symm (0,y) ∈ range B.secondSide := by
        have hzT : (0,y) ∈ G.target := by
          simpa only [neg_zero] using hBox 0 y (le_refl 0) hδ.le hy0 hy1
        have hxS := G.map_target hzT
        have hPair : G.symm (0,y) ∈ range d ∩ range B.disk := by
          rw [hContact]
          exact ⟨(0,y),⟨rfl,hy0,hy1⟩,rfl⟩
        have hxB : G.symm (0,y) ∈ b.val.image := (hBAxis _ hxS).mpr (by
          rw [G.right_inv hzT])
        exact hDiskB ▸ (show G.symm (0,y) ∈ range B.disk ∩ b.val.image from ⟨hPair.2,hxB⟩)
      have hLiteralPorts := hActualTriangleLiteralBaselinePorts G δ hδ (cornerA i) (corner i)
        (cornerL i) (cornerH i)
        (hGS.symm ▸ hCornerASource i) (hGS.symm ▸ hCornerPoint i)
        (hGS.symm ▸ hCornerBaselineSource i)
        (fun u => hGS.symm ▸ hCornerJointSource i 0 u) hGA hGp hGL
        (fun u => by simpa [neg_mul] using hJoint 0 u)
        (range d) hRange
      refine ⟨range d,isCompact_range d.continuous,(hGS ▸ hSource),hMarks,hOld,?_,
        (fun hh => False.elim (hm hh)),fun _ => hLiteralPorts,fun _ => ⟨G,δ,hGS,hδ,hGp,hGA,hGL,hJoint,hBox,hAAxis,hBAxis,hRange,hSharedInterior,hVerticalSelected⟩⟩
      intro x hx
      obtain ⟨z,hz,he⟩ := hContact ▸ hx
      have hzT : z ∈ G.target := by
        have hh := hBox 0 z.2 (le_refl 0) hδ.le hz.2.1 hz.2.2
        have hez : z=(0,z.2) := Prod.ext hz.1 rfl
        simpa only [neg_zero,← hez] using hh
      have hxG : x ∈ G.source := hSource hx.1
      have hxB : x ∈ b.val.image := (hBAxis x hxG).mpr (by
        rw [← he,G.right_inv hzT]
        exact hz.1)
      exact hDiskB ▸ (show x ∈ range B.disk ∩ b.val.image from ⟨hx.2,hxB⟩)
  choose baselineCornerTriangle hBaselineTriangleCompact hBaselineTriangleSource
    hBaselineTriangleMarks hBaselineTriangleOld hBaselineTriangleContact
    hBaselineMarkedTriangleEmpty hBaselineTriangleLiteralPorts hBaselineTriangleLiteralChart using hCornerActualBaselineTriangle
  let actualBaselineCapSet : Set S := range B.disk ∪ ⋃ i : Bool, baselineCornerTriangle i
  have hActualBaselineCapCompact : IsCompact actualBaselineCapSet :=
    (isCompact_range B.disk.continuous).union (isCompact_iUnion hBaselineTriangleCompact)
  have hActualBaselineCapMarks : actualBaselineCapSet ∩ (M.cover.branch : Set S) ⊆
      ({cornerA false,cornerA true} : Set S) := by
    rintro x ⟨(hxD|hxT),hm⟩
    · rcases B.marks_are_corners x hxD hm with h0|h1
      · have hmark : corner false ∈ M.cover.branch := by
          change B.firstCorner ∈ M.cover.branch
          exact h0 ▸ hm
        have hc : cornerA false=B.firstCorner := hCornerAMarked false hmark
        exact Or.inl (h0.trans hc.symm)
      · have he1 : x=B.secondCorner := by simpa using h1
        have hmark : corner true ∈ M.cover.branch := by
          change B.secondCorner ∈ M.cover.branch
          exact he1 ▸ hm
        have hc : cornerA true=B.secondCorner := hCornerAMarked true hmark
        exact Or.inr (he1.trans hc.symm)
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hxT
      exact False.elim (Set.disjoint_left.mp (hBaselineTriangleMarks i) hi hm)
  have hCornerActualRetainedParameters (i : Bool) (hm : corner i ∉ M.cover.branch)
      (t : Interval) (ht : a.val.map t=cornerA i) :
      0<t.val ∧ t.val<1 ∧
        ((corner i=(a.val.map ∘ Set.projIcc 0 1 zero_le_one) L ∧ t.val<L) ∨
         (corner i=(a.val.map ∘ Set.projIcc 0 1 zero_le_one) R ∧ R<t.val)) := by
    apply hCornerParamWLabels i t
    · exact ht.symm ▸ (hCornerSource i (hCornerASource i)).1.2
    · exact ht.symm ▸ hCornerAUnmarked i hm
    · exact hm
  have hCornerADistinct : cornerA false ≠ cornerA true := by
    intro he
    have h0 : cornerA false ∈ sep0 := (hCornerSource false (hCornerASource false)).2
    have h1 : cornerA true ∈ sep1 := (hCornerSource true (hCornerASource true)).2
    exact Set.disjoint_left.mp hSepDisjoint h0 (he.symm ▸ h1)
  choose cornerParam hCornerParam using hCornerBaselineSide
  have hCornerParamOrder :
      0 < (cornerParam false).val ∧ (cornerParam false).val < commonδ/2 ∧
      1-commonδ/2 < (cornerParam true).val ∧ (cornerParam true).val < 1 := by
    have h0W : cornerL false 0 ∈ baseCornerW false :=
      (hCornerSource false (hCornerBaselineSource false)).1.1
    have h1W : cornerL true 0 ∈ baseCornerW true :=
      (hCornerSource true (hCornerBaselineSource true)).1.1
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
  obtain ⟨insideGlobalE,hInsideGlobalSource,hInsideGlobalX,hInsideGlobalY,hInsideGlobalAxis,hInsideGlobalBank⟩ :=
    actual_marked_two_side_disk_interior_bank M a b B globalF1 (χ 0) (χ 1) globalε hχ01 hGlobalε
      (fun z hz => hGlobalStrip z ⟨hz.1.le,hz.2.1.le⟩ (abs_lt.mpr ⟨hz.2.2.1,hz.2.2.2⟩))
      hF1FirstFree hF1SideLocal hF1Axis
  let globalE := insideGlobalE.transHomeomorph mirrorY
  have hGlobalESource : globalE.source=globalF1.source := hInsideGlobalSource
  have hGlobalEX (x : S) : globalE x 0=globalF1 x 0 := hInsideGlobalX x
  have hGlobalEY (x : S) : globalE x 1=globalF1 x 1 ∨ globalE x 1= -globalF1 x 1 := by
    have hh := hInsideGlobalY x
    change -(insideGlobalE x 1)=globalF1 x 1 ∨ -(insideGlobalE x 1)= -globalF1 x 1
    rcases hh with hh|hh
    · exact Or.inr (congrArg Neg.neg hh)
    · left; rw [hh,neg_neg]
  have hGlobalEAxis (x : S) (hx : x ∈ globalE.source) :
      x ∈ b.val.image ↔ globalE x 1=0 := by
    change x ∈ b.val.image ↔ -(insideGlobalE x 1)=0
    rw [neg_eq_zero]
    exact hInsideGlobalAxis x hx
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
      x ∈ (range B.disk)ᶜ ↔ 0 < globalE x 1 := by
    have hInsideRealBank : x ∈ B.openInterior ↔ 0 < (insideGlobalE x 1) :=
      hInsideGlobalBank x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2
    have hExterior : x ∉ range B.disk ↔ insideGlobalE x 1<0 := by
      constructor
      · intro hxD
        by_contra hn
        have hy : 0 ≤ insideGlobalE x 1 := le_of_not_gt hn
        by_cases hz : insideGlobalE x 1=0
        · have hxb : x ∈ b.val.image := (hInsideGlobalAxis x hx.1).mpr hz
          have hxSide : x ∈ range B.secondSide :=
            (hF1SideLocal x (hInsideGlobalSource ▸ hx.1)).mp hxb
          apply hxD
          apply image_subset_range _ _
          exact B.boundary_eq.symm ▸ (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inr hxSide)
        · have hxOpen : x ∈ B.openInterior := (hInsideRealBank).mpr (lt_of_le_of_ne hy (Ne.symm hz))
          obtain ⟨z,hz,rfl⟩ := hxOpen
          exact hxD (Set.mem_range_self z)
      · intro hy hxD
        have hxOpen : x ∉ B.openInterior := by
          intro hh
          have hp := (hInsideRealBank).mp hh
          linarith
        obtain ⟨z,rfl⟩ := hxD
        have hzSphere : dist z.val (0:Plane)=1 := by
          apply le_antisymm z.property
          by_contra hn
          exact hxOpen ⟨z,lt_of_not_ge hn,rfl⟩
        have hzBoundary : B.disk z ∈ range B.firstSide ∪ range B.secondSide :=
          B.boundary_eq ▸ (show B.disk z ∈ B.disk '' {w | w.val ∈ Metric.sphere (0:Plane) 1} from
            ⟨z,hzSphere,rfl⟩)
        rcases hzBoundary with hzFirst|hzSecond
        · exact Set.disjoint_left.mp hF1FirstFree (hInsideGlobalSource ▸ hx.1) hzFirst
        · have hzAxis : insideGlobalE (B.disk z) 1=0 :=
            (hInsideGlobalAxis _ hx.1).mp (B.second_on_curve hzSecond)
          linarith
    change x ∉ range B.disk ↔ 0< -(insideGlobalE x 1)
    exact hExterior.trans (by constructor <;> intro hh <;> linarith)
  let Ebank := globalE.restrOpen (globalE.source ∩ bankO) hBankOOpen
  have hEbankSource : Ebank.source=globalE.source ∩ bankO := by
    ext x
    simp [Ebank,OpenPartialHomeomorph.restrOpen_source,Set.inter_assoc]
  have hEbankValue (x : S) : Ebank x=globalE x := rfl
  have hEbankAxis (x : S) (hx : x ∈ Ebank.source) : x ∈ b.val.image ↔ Ebank x 1=0 :=
    hGlobalEAxis x ((hEbankSource ▸ hx).1)
  have hEbankInside (x : S) (hx : x ∈ Ebank.source) :
      x ∈ (range B.disk)ᶜ ↔ 0 < Ebank x 1 := hRealBank x (hEbankSource ▸ hx)
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
        range f ⊆ (range B.disk)ᶜ ∧
        Disjoint (range f) (M.cover.branch : Set S) ∧ Disjoint (range f) b.val.image ∧
        ∀ j, f 0 ∉ (old j).val.image ∧ f 1 ∉ (old j).val.image ∧
          (range f ∩ (old j).val.image).Finite ∧
          (range f ∩ (old j).val.image).ncard ≤ if p.val ∈ (old j).val.image then 1 else 0 := by
    obtain ⟨f,hf,hfs,hfr,hf0,hf1,hbank,hmarks,hbfree,hcounts⟩ := hBankPatchFamily p h hh hhH
    refine ⟨f,hf,hfs,hfr,hf0,hf1,?_,hmarks,hbfree,hcounts⟩
    intro x hx
    exact (hEbankInside x (hBankPatchSource p (hfs hx)).2.1).mpr (hbank x hx)
  have hCornerFamiliesInside (i : Bool) :
      ∀ t : Interval, 0 < t.val → cornerL i t ∈ (range B.disk)ᶜ := by
    apply CurveComplex.actual_corner_endpoint_family_attaches_inside (cornerA i) (range B.disk)ᶜ (cornerL i)
    intro t ht
    obtain ⟨f,hf,hf0,hf1,hfs,hfi,hfa,hfK,hfb,hfm,hfo,hJoint⟩ := hCornerPaths i t ht
    exact ⟨f,hf,hf0,hf1,hfi⟩
  obtain ⟨cornerη,hCornerη,hCornerη1,bankCornerL,hBankCornerFormula,hBankCornerBaseline,hBankCornerPositive⟩ :=
    CurveComplex.actual_finite_endpoint_families_common_bank Ebank (range B.disk)ᶜ cornerL
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
      orientedLeft p t ∈ (range B.disk)ᶜ ∧ orientedRight p t ∈ (range B.disk)ᶜ := by
    let h : ℝ := (bankPatchH p/2)*t.val
    have hh : 0 < h := mul_pos (half_pos (hBankPatchH p)) ht
    have hhH : h < bankPatchH p := by dsimp [h]; nlinarith [t.property.2,hBankPatchH p]
    obtain ⟨f,hf,hfs,hfr,hf0,hf1,hinside,hm,hbfree,hcounts⟩ := hBankPatchInside p h hh hhH
    have hl : bankL p t=f 0 := (hBankLFormula p t).trans hf0.symm
    have hr : bankR p t=f 1 := (hBankRFormula p t).trans hf1.symm
    have hlI : bankL p t ∈ (range B.disk)ᶜ := hl.symm ▸ hinside (Set.mem_range_self 0)
    have hrI : bankR p t ∈ (range B.disk)ᶜ := hr.symm ▸ hinside (Set.mem_range_self 1)
    dsimp [orientedLeft,orientedRight]
    split_ifs <;> first | exact ⟨hrI,hlI⟩ | exact ⟨hlI,hrI⟩
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
  have hActualChartArcJoin (F : OpenPartialHomeomorph S Plane)
      (f g : C(Interval,S)) (hf : IsEmbedding f) (hg : IsEmbedding g)
      (hfS : range f ⊆ F.source) (hgS : range g ⊆ F.source)
      (hfg : f 1=g 0) (hne : f 0≠g 1) :
      ∃ h : C(Interval,S), IsEmbedding h ∧ h 0=f 0 ∧ h 1=g 1 ∧
        range h ⊆ range f ∪ range g := by
    have hfa := CurveComplex.actual_chart_continuous_arc F f hf (fun t => hfS (Set.mem_range_self t))
    have hga := CurveComplex.actual_chart_continuous_arc F g hg (fun t => hgS (Set.mem_range_self t))
    have hjoin : F (f 1)=F (g 0) := congrArg F hfg
    have hdistinct : F (f 0)≠F (g 1) := fun he =>
      hne (F.injOn (hfS (Set.mem_range_self 0)) (hgS (Set.mem_range_self 1)) he)
    obtain ⟨A,hAU,hA⟩ := Schoenflies.exists_arc_in_union_of_arcs hfa (hjoin.symm ▸ hga) hdistinct
    have hAT : A ⊆ F.target := by
      intro x hx
      rcases hAU hx with ⟨y,hy,hye⟩|⟨y,hy,hye⟩
      · exact hye ▸ F.map_source (hfS hy)
      · exact hye ▸ F.map_source (hgS hy)
    obtain ⟨h,hh,hhR,hh0,hh1⟩ := CurveComplex.actual_pullback_chart_arc F (f 0) (g 1)
      (hfS (Set.mem_range_self 0)) (hgS (Set.mem_range_self 1)) A hA hAT
    refine ⟨h,hh,hh0,hh1,?_⟩
    intro x hx
    obtain ⟨z,hz,hzx⟩ := hhR ▸ hx
    rcases hAU hz with ⟨y,hy,hyz⟩|⟨y,hy,hyz⟩
    · left
      have he : y=x := by rw [← hzx,← hyz,F.left_inv (hfS hy)]
      exact he ▸ hy
    · right
      have he : y=x := by rw [← hzx,← hyz,F.left_inv (hgS hy)]
      exact he ▸ hy
  have hCornerAOnA (i : Bool) : cornerA i ∈ a.val.image := hdecompRaw.symm ▸ Or.inr (hCornerAK i)
  let originalγ := a.val.map ∘ Set.projIcc 0 1 zero_le_one
  have hOriginalPortsDistinct : originalγ L≠originalγ R := by
    intro he
    have h0 : B.firstCorner ∈ ({originalγ L,originalγ R} : Set S) :=
      hOriginalSelectedPorts.symm ▸ (by simp [originalγ])
    have h1 : B.secondCorner ∈ ({originalγ L,originalγ R} : Set S) :=
      hOriginalSelectedPorts.symm ▸ (by simp [originalγ])
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,← he,or_self] at h0 h1
    exact hcornersNe (h0.trans h1.symm)
  have hLeftPortExists : ∃ i : Bool, corner i=originalγ L := by
    have hh : originalγ L ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
      hOriginalSelectedPorts ▸ (by simp [originalγ])
    rcases hh with hh|hh
    · exact ⟨false,hh.symm⟩
    · exact ⟨true,hh.symm⟩
  have hRightPortExists : ∃ i : Bool, corner i=originalγ R := by
    have hh : originalγ R ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
      hOriginalSelectedPorts ▸ (by simp [originalγ])
    rcases hh with hh|hh
    · exact ⟨false,hh.symm⟩
    · exact ⟨true,hh.symm⟩
  obtain ⟨leftPort,hLeftPort⟩ := hLeftPortExists
  obtain ⟨rightPort,hRightPort⟩ := hRightPortExists
  have hPortsDifferent : leftPort≠rightPort := by
    intro he
    exact hOriginalPortsDistinct (hLeftPort.symm.trans (he ▸ hRightPort))
  have hActualExpandedLeftParameter :
      ∃ U : ℝ, 0≤U ∧ U≤L ∧ (0<L → 0<U) ∧ originalγ U=cornerA leftPort ∧
        (corner leftPort ∈ M.cover.branch → U=L) := by
    by_cases hm : corner leftPort ∈ M.cover.branch
    · refine ⟨L,hL,le_rfl,id,?_,fun _ => rfl⟩
      exact hLeftPort.symm.trans (hCornerAMarked leftPort hm).symm
    · obtain ⟨t,ht⟩ := hCornerAOnA leftPort
      obtain ⟨ht0,ht1,hlabels⟩ := hCornerActualRetainedParameters leftPort hm t ht
      have htL : t.val<L := by
        rcases hlabels with hlabels|hlabels
        · exact hlabels.2
        · exact False.elim (hOriginalPortsDistinct (hLeftPort.symm.trans hlabels.1))
      refine ⟨t.val,t.property.1,htL.le,fun _ => ht0,?_,fun hh => False.elim (hm hh)⟩
      change a.val.map (Set.projIcc 0 1 zero_le_one t.val)=cornerA leftPort
      simpa only [Set.projIcc_of_mem zero_le_one t.property] using ht
  have hActualExpandedRightParameter :
      ∃ V : ℝ, R≤V ∧ V≤1 ∧ (R<1 → V<1) ∧ originalγ V=cornerA rightPort ∧
        (corner rightPort ∈ M.cover.branch → V=R) := by
    by_cases hm : corner rightPort ∈ M.cover.branch
    · refine ⟨R,le_rfl,hR,id,?_,fun _ => rfl⟩
      exact hRightPort.symm.trans (hCornerAMarked rightPort hm).symm
    · obtain ⟨t,ht⟩ := hCornerAOnA rightPort
      obtain ⟨ht0,ht1,hlabels⟩ := hCornerActualRetainedParameters rightPort hm t ht
      have hRt : R<t.val := by
        rcases hlabels with hlabels|hlabels
        · exact False.elim (hOriginalPortsDistinct (hlabels.1.symm.trans hRightPort))
        · exact hlabels.2
      refine ⟨t.val,hRt.le,t.property.2,fun _ => ht1,?_,fun hh => False.elim (hm hh)⟩
      change a.val.map (Set.projIcc 0 1 zero_le_one t.val)=cornerA rightPort
      simpa only [Set.projIcc_of_mem zero_le_one t.property] using ht
  obtain ⟨expandedL,hExpandedL0,hExpandedL,hExpandedLPositive,hExpandedLeft,hExpandedLeftMarked⟩ := hActualExpandedLeftParameter
  obtain ⟨expandedR,hExpandedR,hExpandedR1,hExpandedRInterior,hExpandedRight,hExpandedRightMarked⟩ := hActualExpandedRightParameter
  have hExpandedLR : expandedL<expandedR := lt_of_le_of_lt hExpandedL (hLR.trans_le hExpandedR)
  have hExpandedProper : 0<expandedL ∨ expandedR<1 := hproper.imp hExpandedLPositive hExpandedRInterior
  obtain ⟨expandedFirst,hExpandedEmbedded,hExpandedFirstZero,hExpandedFirstOne,
    hExpandedFirstRange,expandedK,hExpandedKCompact,hExpandedDecomposition,hExpandedMeet⟩ :=
    hActualMarkedSubarcRemainder a expandedL expandedR hExpandedL0 hExpandedLR hExpandedR1 hExpandedProper
  have hFirstSideInExpanded : range B.firstSide ⊆ range expandedFirst := by
    rw [hSide,hExpandedFirstRange]
    apply Set.image_mono
    intro t ht
    exact ⟨hExpandedL.trans ht.1,ht.2.trans hExpandedR⟩
  have hExpandedKSubset : expandedK ⊆ Kraw := by
    intro x hx
    have hxa : x ∈ a.val.image := hExpandedDecomposition.symm ▸ Or.inr hx
    rcases hdecompRaw ▸ hxa with hfirst|hraw
    · have hm : x ∈ range expandedFirst ∩ expandedK := ⟨hFirstSideInExpanded hfirst,hx⟩
      rw [hExpandedMeet] at hm
      rcases hm with he|he
      · have hxA : x=cornerA leftPort := he.trans hExpandedLeft
        exact hxA.symm ▸ hCornerAK leftPort
      · have hxA : x=cornerA rightPort := he.trans hExpandedRight
        exact hxA.symm ▸ hCornerAK rightPort
    · exact hraw
  have hEbankOffA : Disjoint Ebank.source a.val.image := by
    apply Set.disjoint_left.mpr
    intro x hx hxA
    have hxF : x ∈ globalF1.source := hGlobalESource ▸ (hEbankSource ▸ hx).1
    exact (hGlobalF1Source ▸ hxF).2 (Or.inl hxA)
  have hEbankMarks : Disjoint Ebank.source (M.cover.branch : Set S) := by
    apply hGlobalMarks.mono_left
    intro x hx
    exact (hGlobalF1Source ▸ (hGlobalESource ▸ (hEbankSource ▸ hx).1)).1
  have hExteriorTracePuncture : ∃ v ∈ M.cover.branch,
      v ∉ ({B.firstCorner,B.secondCorner} : Finset S) := by
    by_contra hn
    have hsub : M.cover.branch ⊆ {B.firstCorner,B.secondCorner} := by
      intro v hv
      by_contra hc
      exact hn ⟨v,hv,hc⟩
    have hcard := Finset.card_le_card hsub
    rw [M.cover.branch_card] at hcard
    have htwo : ({B.firstCorner,B.secondCorner} : Finset S).card≤2 := Finset.card_insert_le _ _
    omega
  obtain ⟨exteriorPuncture,hExteriorPunctureMark,hExteriorPunctureCorner⟩ := hExteriorTracePuncture
  let exteriorChart : OpenPartialHomeomorph S Plane :=
    ((M.planeToSphere_isOpenEmbedding exteriorPuncture).toOpenPartialHomeomorph).symm
  have hExteriorChartCovers (x : S) (hx : x≠exteriorPuncture) : x ∈ exteriorChart.source := by
    simp only [exteriorChart,OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨M.puncturedPlane exteriorPuncture ⟨x,hx⟩,
      congrArg Subtype.val ((M.puncturedPlane exteriorPuncture).symm_apply_apply ⟨x,hx⟩)⟩
  have hPositiveRayAffineCrossing := actual_marked_positive_radial_horizontal_crossing_chart M
  have hUnmarkedCornerOffExpandedK (p : S)
      (hp : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
      (hpm : p ∉ M.cover.branch) : p ∉ expandedK := by
    intro hk
    have hpFirst : p ∈ range B.firstSide := by
      rcases hp with he|he
      · exact ⟨0,B.first_zero.trans he.symm⟩
      · exact ⟨1,B.first_one.trans he.symm⟩
    have hm : p ∈ ({originalγ expandedL,originalγ expandedR} : Set S) :=
      hExpandedMeet ▸ (show p ∈ range expandedFirst ∩ expandedK from
        ⟨hFirstSideInExpanded hpFirst,hk⟩)
    have hImpossible (i : Bool) (he : p=cornerA i) : False := by
      by_cases hi : corner i ∈ M.cover.branch
      · exact hpm (he.symm ▸ ((hCornerAMarked i hi).symm ▸ hi))
      · exact hCornerAUnmarked i hi (he ▸ hpFirst)
    rcases hm with he|he
    · exact hImpossible leftPort (he.trans hExpandedLeft)
    · exact hImpossible rightPort (he.trans hExpandedRight)
  let baselineCorner : Bool → C(Interval,S) := fun i =>
    ⟨fun u => cornerH i (0,u),(cornerH i).continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hBaselineCornerEmbedded (i : Bool) : IsEmbedding (baselineCorner i) := hCornerJointEmbedded i 0
  have hBaselineCornerZero (i : Bool) : baselineCorner i 0=cornerA i := hCornerJointStart i 0
  have hBaselineCornerOne (i : Bool) : baselineCorner i 1=cornerL i 0 := hCornerJointEnd i 0
  have hMarkedBaselineLiteralSideInterval (i : Bool) (hm : corner i ∈ M.cover.branch) :
      range (baselineCorner i)=B.secondSide ''
        Icc (min (if i then (1:Interval) else 0) (cornerParam i))
          (max (if i then (1:Interval) else 0) (cornerParam i)) := by
    have hp : B.secondSide (if i then (1:Interval) else 0)=corner i := by
      cases i
      · exact B.second_zero
      · exact B.second_one
    exact hActualEmbeddedArcLiteralIntervalTrace B.secondSide (baselineCorner i)
      B.second_embedded (hBaselineCornerEmbedded i)
      (by rintro x ⟨u,rfl⟩; exact hCornerMarkedBaselineWholeSide i hm u)
      (if i then (1:Interval) else 0) (cornerParam i)
      ((hBaselineCornerZero i).trans ((hCornerAMarked i hm).trans hp.symm))
      ((hBaselineCornerOne i).trans (hCornerParam i).symm)
  have hUnmarkedBaselineSideIntersection (i : Bool) (hn : corner i ∉ M.cover.branch) :
      range (baselineCorner i) ∩ range B.secondSide={cornerL i 0} := by
    obtain ⟨G,δ,hGS,hδ,hGp,hGA,hGL,hJoint,hBox,hAxis,hBAxis,hTImage,hSharedInterior,hVerticalSelected⟩ :=
      hBaselineTriangleLiteralChart i hn
    ext x
    constructor
    · rintro ⟨⟨u,rfl⟩,hxB⟩
      have hxS : baselineCorner i u ∈ G.source := hGS.symm ▸ hCornerJointSource i 0 u
      have hx0 := (hBAxis (baselineCorner i u) hxS).mp (B.second_on_curve hxB)
      have hc := hJoint 0 u
      have hh : (G (baselineCorner i u)).1= -(δ*(1-u.val)) := by
        simpa [baselineCorner] using congrArg Prod.fst hc
      rw [hx0] at hh
      have hz : δ*(1-u.val)=0 := by linarith
      have hu : 1-u.val=0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hδ)
      have hu1 : u=1 := Subtype.ext (by change u.val=1; linarith)
      subst u
      exact hBaselineCornerOne i
    · rintro rfl
      exact ⟨⟨1,hBaselineCornerOne i⟩,⟨cornerParam i,hCornerParam i⟩⟩
  have hActualUnmarkedBaselineVerticalArc (i : Bool) (hn : corner i ∉ M.cover.branch) :
      ∃ g : C(Interval,S), IsEmbedding g ∧ g 0=corner i ∧ g 1=cornerL i 0 ∧
        range g=B.secondSide '' Icc
          (min (if i then (1:Interval) else 0) (cornerParam i))
          (max (if i then (1:Interval) else 0) (cornerParam i)) ∧
        (∀ u : Interval, 0<u.val → u.val<1 → g u ∈ interior actualBaselineCapSet) := by
    obtain ⟨G,δ,hGS,hδ,hGp,hGA,hGL,hJoint,hBox,hAxis,hBAxis,hTImage,hSharedInterior,hVerticalSelected⟩ :=
      hBaselineTriangleLiteralChart i hn
    let z : Interval → ℝ × ℝ := fun u => (0,δ*u.val)
    have hz (u : Interval) : z u ∈ G.target := by
      simpa only [z,neg_zero] using hBox 0 (δ*u.val) (le_refl 0) hδ.le
        (mul_nonneg hδ.le u.property.1) (by nlinarith [u.property.2])
    let g : C(Interval,S) := ⟨fun u => G.symm (z u),
      G.symm.continuousOn.comp_continuous (by dsimp [z]; fun_prop) hz⟩
    have hgc (u : Interval) : G (g u)=z u := G.right_inv (hz u)
    have hgi : Function.Injective g := by
      intro u v he
      have hh := congrArg Prod.snd (congrArg G he)
      rw [hgc,hgc] at hh
      have hh' : δ*u.val=δ*v.val := hh
      exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hδ) hh')
    have hge : IsEmbedding g := (g.continuous.isClosedEmbedding hgi).isEmbedding
    have hg0 : g 0=corner i := by
      change G.symm (z 0)=corner i
      have he : z 0=G (corner i) := by simp [z,hGp]
      rw [he,G.left_inv (hGS.symm ▸ hCornerPoint i)]
    have hg1 : g 1=cornerL i 0 := by
      change G.symm (z 1)=cornerL i 0
      have he : z 1=G (cornerL i 0) := by simp [z,hGL]
      rw [he,G.left_inv (hGS.symm ▸ hCornerBaselineSource i)]
    have hgB : range g ⊆ range B.secondSide := by
      rintro x ⟨u,rfl⟩
      exact hVerticalSelected (δ*u.val) (mul_nonneg hδ.le u.property.1)
        (by nlinarith [u.property.2])
    have hp : B.secondSide (if i then (1:Interval) else 0)=corner i := by
      cases i
      · exact B.second_zero
      · exact B.second_one
    refine ⟨g,hge,hg0,hg1,?_,?_⟩
    · exact hActualEmbeddedArcLiteralIntervalTrace B.secondSide g B.second_embedded hge hgB
        (if i then (1:Interval) else 0) (cornerParam i) (hg0.trans hp.symm)
        (hg1.trans (hCornerParam i).symm)
    · intro u hu0 hu1
      have hh := hSharedInterior (δ*u.val) (mul_pos hδ hu0) (by nlinarith)
      exact interior_mono (show range B.disk ∪ baselineCornerTriangle i ⊆ actualBaselineCapSet from
        fun x hx => hx.elim Or.inl (fun ht => Or.inr (Set.mem_iUnion.mpr ⟨i,ht⟩))) hh
  have hBaselineCuts : (cornerParam false).val < (cornerParam true).val := by
    linarith [hCornerParamOrder.2.1,hCornerParamOrder.2.2.1,hCommonδhalf]
  let baselineMiddle : C(Interval,S) := ⟨fun u => ψ ((cornerParam false).val+
    u.val*((cornerParam true).val-(cornerParam false).val)),hψ.comp (by fun_prop)⟩
  have hBaselineMiddleθ (u : Interval) :
      (cornerParam false).val ≤ (cornerParam false).val+u.val*((cornerParam true).val-(cornerParam false).val) ∧
      (cornerParam false).val+u.val*((cornerParam true).val-(cornerParam false).val) ≤ (cornerParam true).val := by
    have h0 := mul_nonneg u.property.1 (sub_pos.mpr hBaselineCuts).le
    have h1 := mul_nonneg (sub_nonneg.mpr u.property.2) (sub_pos.mpr hBaselineCuts).le
    constructor <;> nlinarith
  have hBaselineMiddle01 (u : Interval) :
      (cornerParam false).val+u.val*((cornerParam true).val-(cornerParam false).val) ∈ Icc (0:ℝ) 1 :=
    ⟨(cornerParam false).property.1.trans (hBaselineMiddleθ u).1,
      (hBaselineMiddleθ u).2.trans (cornerParam true).property.2⟩
  have hBaselineMiddleEmbedded : IsEmbedding baselineMiddle := by
    apply (baselineMiddle.continuous.isClosedEmbedding ?_).isEmbedding
    intro u v he
    have hh := hψInjective _ _ (hBaselineMiddle01 u) (hBaselineMiddle01 v) he
    apply Subtype.ext
    exact mul_right_cancel₀ (ne_of_gt (sub_pos.mpr hBaselineCuts)) (add_left_cancel hh)
  have hBaselineMiddleZero : baselineMiddle 0=cornerL false 0 := by
    simpa [baselineMiddle,ψ,Set.projIcc_of_mem zero_le_one (cornerParam false).property]
      using hCornerParam false
  have hBaselineMiddleOne : baselineMiddle 1=cornerL true 0 := by
    have hθ1 : (cornerParam false).val+((cornerParam true).val-(cornerParam false).val)=
        (cornerParam true).val := by ring
    simpa [baselineMiddle,ψ,hθ1,Set.projIcc_of_mem zero_le_one (cornerParam true).property]
      using hCornerParam true
  have hBaselineMiddleSide : range baselineMiddle ⊆ range B.secondSide := by
    rintro x ⟨u,rfl⟩
    exact Set.mem_range_self _
  have hBaselineMiddleRange : range baselineMiddle=B.secondSide '' Icc (cornerParam false) (cornerParam true) := by
    have hh := hActualEmbeddedArcLiteralIntervalTrace B.secondSide baselineMiddle
      B.second_embedded hBaselineMiddleEmbedded hBaselineMiddleSide (cornerParam false) (cornerParam true)
      (hBaselineMiddleZero.trans (hCornerParam false).symm)
      (hBaselineMiddleOne.trans (hCornerParam true).symm)
    simpa only [min_eq_left (show cornerParam false ≤ cornerParam true from hBaselineCuts.le),max_eq_right (show cornerParam false ≤ cornerParam true from hBaselineCuts.le)] using hh
  have hBaselineLeftMiddleMeet : range (baselineCorner false) ∩ range baselineMiddle={cornerL false 0} := by
    ext x
    constructor
    · rintro ⟨hx,hmid⟩
      by_cases hm : corner false ∈ M.cover.branch
      · have hr : range (baselineCorner false)=B.secondSide '' Icc (0:Interval) (cornerParam false) := by
          simpa only [Bool.coe_false,ite_false,min_eq_left (show (0:Interval) ≤ cornerParam false from bot_le),max_eq_right (show (0:Interval) ≤ cornerParam false from bot_le)]
            using hMarkedBaselineLiteralSideInterval false hm
        obtain ⟨u,hu,heU⟩ := hr ▸ hx
        obtain ⟨v,hv,heV⟩ := hBaselineMiddleRange ▸ hmid
        have huv : u=v := B.second_embedded.injective (heU.trans heV.symm)
        subst v
        have huc : u=cornerParam false := le_antisymm hu.2 hv.1
        exact heU.symm.trans ((congrArg B.secondSide huc).trans (hCornerParam false))
      · exact hUnmarkedBaselineSideIntersection false hm ▸ ⟨hx,hBaselineMiddleSide hmid⟩
    · rintro rfl
      exact ⟨⟨1,hBaselineCornerOne false⟩,⟨0,hBaselineMiddleZero⟩⟩
  have hBaselineMiddleRightMeet : range baselineMiddle ∩ range (baselineCorner true)={cornerL true 0} := by
    ext x
    constructor
    · rintro ⟨hmid,hx⟩
      by_cases hm : corner true ∈ M.cover.branch
      · have hr : range (baselineCorner true)=B.secondSide '' Icc (cornerParam true) (1:Interval) := by
          simpa only [Bool.coe_true,ite_true,min_eq_right (show cornerParam true ≤ (1:Interval) from le_top),max_eq_left (show cornerParam true ≤ (1:Interval) from le_top)]
            using hMarkedBaselineLiteralSideInterval true hm
        obtain ⟨u,hu,heU⟩ := hBaselineMiddleRange ▸ hmid
        obtain ⟨v,hv,heV⟩ := hr ▸ hx
        have huv : u=v := B.second_embedded.injective (heU.trans heV.symm)
        subst v
        have huc : u=cornerParam true := le_antisymm hu.2 hv.1
        exact heU.symm.trans ((congrArg B.secondSide huc).trans (hCornerParam true))
      · exact hUnmarkedBaselineSideIntersection true hm ▸ ⟨hx,hBaselineMiddleSide hmid⟩
    · rintro rfl
      exact ⟨⟨1,hBaselineMiddleOne⟩,⟨1,hBaselineCornerOne true⟩⟩
  have hBaselineCornersDisjoint : Disjoint (range (baselineCorner false)) (range (baselineCorner true)) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨u,rfl⟩ ⟨v,he⟩
    exact Set.disjoint_left.mp hSepDisjoint
      (hCornerSource false (hCornerJointSource false 0 u)).2
      (he ▸ (hCornerSource true (hCornerJointSource true 0 v)).2)
  obtain ⟨baselineLeftMiddle,hBaselineLeftMiddleEmbedded,hBaselineLeftMiddleZero,
    hBaselineLeftMiddleOne,hBaselineLeftMiddleRange⟩ :=
    CurveComplex.source_embedded_arc_concatenation (baselineCorner false) baselineMiddle
      (hBaselineCornerEmbedded false) hBaselineMiddleEmbedded
      ((hBaselineCornerOne false).trans hBaselineMiddleZero.symm)
      (by rw [hBaselineCornerOne false]; exact hBaselineLeftMiddleMeet)
  obtain ⟨baselineRight,hBaselineRightEmbedded,hBaselineRightRange,hBaselineRightZero,hBaselineRightOne⟩ :=
    actual_reverse_embedded_continuous_arc (baselineCorner true) (hBaselineCornerEmbedded true)
  have hBaselineLastMeet : range baselineLeftMiddle ∩ range baselineRight={baselineLeftMiddle 1} := by
    rw [hBaselineLeftMiddleRange,hBaselineRightRange,hBaselineLeftMiddleOne,hBaselineMiddleOne]
    ext x
    constructor
    · rintro ⟨(hx|hx),hr⟩
      · exact False.elim (Set.disjoint_left.mp hBaselineCornersDisjoint hx hr)
      · exact hBaselineMiddleRightMeet ▸ ⟨hx,hr⟩
    · rintro rfl
      exact ⟨Or.inr ⟨1,hBaselineMiddleOne⟩,⟨1,hBaselineCornerOne true⟩⟩
  obtain ⟨baselineOpposite,hBaselineOppositeEmbedded,hBaselineOppositeZero,hBaselineOppositeOne,
    hBaselineOppositeRange⟩ := CurveComplex.source_embedded_arc_concatenation baselineLeftMiddle baselineRight
      hBaselineLeftMiddleEmbedded hBaselineRightEmbedded
      (hBaselineLeftMiddleOne.trans (hBaselineMiddleOne.trans ((hBaselineCornerOne true).symm.trans hBaselineRightZero.symm)))
      hBaselineLastMeet
  have hActualBaselineOppositePorts : baselineOpposite 0=cornerA false ∧ baselineOpposite 1=cornerA true :=
    ⟨hBaselineOppositeZero.trans (hBaselineLeftMiddleZero.trans (hBaselineCornerZero false)),
      hBaselineOppositeOne.trans (hBaselineRightOne.trans (hBaselineCornerZero true))⟩
  have hActualBaselineOppositeWholeTrace : range baselineOpposite=
      (range (baselineCorner false) ∪ range baselineMiddle) ∪ range (baselineCorner true) := by
    rw [hBaselineOppositeRange,hBaselineLeftMiddleRange,hBaselineRightRange]
  have hBaselineMiddleNoCorner (u : Interval) : baselineMiddle u ∉ ({B.firstCorner,B.secondCorner} : Set S) := by
    rintro (he|he)
    · have hh := congrArg Subtype.val (B.second_embedded.injective (he.trans B.second_zero.symm))
      rw [Set.projIcc_of_mem zero_le_one (hBaselineMiddle01 u)] at hh
      change (cornerParam false).val+u.val*((cornerParam true).val-(cornerParam false).val)=0 at hh
      linarith [(hBaselineMiddleθ u).1,hCornerParamOrder.1]
    · have he1 : baselineMiddle u=B.secondCorner := by simpa using he
      have hh := congrArg Subtype.val (B.second_embedded.injective (he1.trans B.second_one.symm))
      rw [Set.projIcc_of_mem zero_le_one (hBaselineMiddle01 u)] at hh
      change (cornerParam false).val+u.val*((cornerParam true).val-(cornerParam false).val)=1 at hh
      linarith [(hBaselineMiddleθ u).2,hCornerParamOrder.2.2.2]
  have hBaselineMiddleAFree : Disjoint (range baselineMiddle) a.val.image := by
    apply Set.disjoint_left.mpr
    rintro x ⟨u,rfl⟩ hxA
    exact hBaselineMiddleNoCorner u (hsecondclean ▸ ⟨hBaselineMiddleSide (Set.mem_range_self u),hxA⟩)
  have hBaselineCornerAIntersection (i : Bool) : range (baselineCorner i) ∩ a.val.image={cornerA i} := by
    have hAiA : cornerA i ∈ a.val.image := hdecompRaw.symm ▸ Or.inr (hCornerAK i)
    ext x
    constructor
    · rintro ⟨⟨u,rfl⟩,hxA⟩
      by_cases hm : corner i ∈ M.cover.branch
      · have hp : baselineCorner i u ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
          hsecondclean ▸ ⟨hCornerMarkedBaselineWholeSide i hm u,hxA⟩
        have hxSep := (hCornerSource i (hCornerJointSource i 0 u)).2
        cases i
        · rcases hp with he|he
          · exact he.trans (hCornerAMarked false hm).symm
          · have he1 : baselineCorner false u=B.secondCorner := by simpa using he
            exact False.elim (Set.disjoint_left.mp hSepDisjoint hxSep (he1.symm ▸ hInSep1))
        · rcases hp with he|he
          · exact False.elim (Set.disjoint_left.mp hSepDisjoint (he.symm ▸ hInSep0) hxSep)
          · have he1 : baselineCorner true u=B.secondCorner := by simpa using he
            exact he1.trans (hCornerAMarked true hm).symm
      · obtain ⟨G,δ,hGS,hδ,hGp,hGA,hGL,hJoint,hBox,hAxis,hBAxis,hTImage,hSharedInterior,hVerticalSelected⟩ :=
          hBaselineTriangleLiteralChart i hm
        have hxS : baselineCorner i u ∈ G.source := hGS.symm ▸ hCornerJointSource i 0 u
        have hx0 := (hAxis (baselineCorner i u) hxS).mp hxA
        have hh : (G (baselineCorner i u)).2=δ*u.val := congrArg Prod.snd (hJoint 0 u)
        rw [hx0] at hh
        have hu0 : u=0 := Subtype.ext ((mul_eq_zero.mp hh.symm).resolve_left (ne_of_gt hδ))
        subst u
        exact hBaselineCornerZero i
    · rintro rfl
      exact ⟨⟨0,hBaselineCornerZero i⟩,hAiA⟩
  have hActualBaselineOppositeAIntersection : range baselineOpposite ∩ a.val.image=
      ({cornerA false,cornerA true} : Set S) := by
    ext x
    constructor
    · rintro ⟨hx,hxA⟩
      rw [hActualBaselineOppositeWholeTrace] at hx
      rcases hx with (hl|hm)|hr
      · exact Or.inl (Set.mem_singleton_iff.mp ((hBaselineCornerAIntersection false) ▸ (show x ∈ range (baselineCorner false) ∩ a.val.image from ⟨hl,hxA⟩)))
      · exact False.elim (Set.disjoint_left.mp hBaselineMiddleAFree hm hxA)
      · exact Or.inr (Set.mem_singleton_iff.mp ((hBaselineCornerAIntersection true) ▸ (show x ∈ range (baselineCorner true) ∩ a.val.image from ⟨hr,hxA⟩)))
    · rintro (h0|h1)
      · exact ⟨⟨0,hActualBaselineOppositePorts.1.trans h0.symm⟩,
          h0.symm ▸ (hdecompRaw.symm ▸ Or.inr (hCornerAK false))⟩
      · have he1 : x=cornerA true := by simpa using h1
        exact ⟨⟨1,hActualBaselineOppositePorts.2.trans he1.symm⟩,
          he1.symm ▸ (hdecompRaw.symm ▸ Or.inr (hCornerAK true))⟩
  have hBaselineCornerInCap (i : Bool) : range (baselineCorner i) ⊆ actualBaselineCapSet := by
    intro x hx
    by_cases hm : corner i ∈ M.cover.branch
    · obtain ⟨u,rfl⟩ := hx
      have hs : baselineCorner i u ∈ range B.secondSide := hCornerMarkedBaselineWholeSide i hm u
      exact Or.inl (image_subset_range _ _ (B.boundary_eq.symm ▸ (show baselineCorner i u ∈ range B.firstSide ∪ range B.secondSide from Or.inr hs)))
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i,(hBaselineTriangleLiteralPorts i hm).2.2.2 hx⟩)
  have hActualBaselineOppositeInCap : range baselineOpposite ⊆ actualBaselineCapSet := by
    intro x hx
    rw [hActualBaselineOppositeWholeTrace] at hx
    rcases hx with (hl|hm)|hr
    · exact hBaselineCornerInCap false hl
    · exact Or.inl (image_subset_range _ _ (B.boundary_eq.symm ▸ (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inr (hBaselineMiddleSide hm))))
    · exact hBaselineCornerInCap true hr
  have hActualBaselinePrefixCovered (i : Bool) :
      B.secondSide '' Icc
        (min (if i then (1:Interval) else 0) (cornerParam i))
        (max (if i then (1:Interval) else 0) (cornerParam i)) ⊆
        range baselineOpposite ∪ interior actualBaselineCapSet ∪ range B.firstSide := by
    have hCornerOpposite : range (baselineCorner i) ⊆ range baselineOpposite := by
      intro x hx
      rw [hActualBaselineOppositeWholeTrace]
      cases i
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
    by_cases hm : corner i ∈ M.cover.branch
    · intro x hx
      exact Or.inl (Or.inl (hCornerOpposite ((hMarkedBaselineLiteralSideInterval i hm).symm ▸ hx)))
    · obtain ⟨g,hg,hg0,hg1,hRange,hInterior⟩ := hActualUnmarkedBaselineVerticalArc i hm
      intro x hx
      obtain ⟨u,rfl⟩ := hRange.symm ▸ hx
      by_cases hu0 : u=0
      · subst u
        apply Or.inr
        rw [hg0]
        cases i
        · exact ⟨0,B.first_zero⟩
        · exact ⟨1,B.first_one⟩
      by_cases hu1 : u=1
      · subst u
        apply Or.inl; apply Or.inl
        exact hCornerOpposite ⟨1,(hBaselineCornerOne i).trans hg1.symm⟩
      · exact Or.inl (Or.inr (hInterior u
          (lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm)))
          (lt_of_le_of_ne u.property.2 (fun he => hu1 (Subtype.ext he)))))
  have hActualBaselineSecondSideCovered : range B.secondSide ⊆
      range baselineOpposite ∪ interior actualBaselineCapSet ∪ range B.firstSide := by
    rintro x ⟨u,rfl⟩
    by_cases hl : u ≤ cornerParam false
    · apply hActualBaselinePrefixCovered false
      exact ⟨u,by simp only [Bool.coe_false,ite_false,min_eq_left (show (0:Interval) ≤ cornerParam false from bot_le),max_eq_right (show (0:Interval) ≤ cornerParam false from bot_le)]; exact ⟨bot_le,hl⟩,rfl⟩
    by_cases hr : cornerParam true ≤ u
    · apply hActualBaselinePrefixCovered true
      exact ⟨u,by simp only [Bool.coe_true,ite_true,min_eq_right (show cornerParam true ≤ (1:Interval) from le_top),max_eq_left (show cornerParam true ≤ (1:Interval) from le_top)]; exact ⟨hr,le_top⟩,rfl⟩
    · apply Or.inl; apply Or.inl
      rw [hActualBaselineOppositeWholeTrace]
      apply Or.inl; apply Or.inr
      rw [hBaselineMiddleRange]
      exact ⟨u,⟨le_of_not_ge hl,le_of_not_ge hr⟩,rfl⟩
  letI := (actualSphereSmoothAtlas M).charts
  have hActualBaselineOriginalDiskFrontier :
      frontier actualBaselineCapSet ∩ range B.disk ⊆
        range expandedFirst ∪ range baselineOpposite := by
    intro x hx
    have hxnot : x ∉ interior (range B.disk) := by
      intro hi
      have hCapInterior : x ∈ interior actualBaselineCapSet :=
        interior_mono (show range B.disk ⊆ actualBaselineCapSet from fun _ hh => Or.inl hh) hi
      exact Set.disjoint_left.mp disjoint_interior_frontier hCapInterior hx.1
    have hDiskFront : x ∈ frontier (range B.disk) := by
      rw [(isCompact_range B.disk.continuous).isClosed.frontier_eq]
      exact ⟨hx.2,hxnot⟩
    have hb := CurveComplex.embedded_disk_frontier_subset_boundary B.disk B.disk_embedded hDiskFront
    have hSides : x ∈ range B.firstSide ∪ range B.secondSide := B.boundary_eq ▸ hb
    rcases hSides with haSide|hbSide
    · exact Or.inl (hFirstSideInExpanded haSide)
    · rcases hActualBaselineSecondSideCovered hbSide with (hOpp|hInt)|hFirst
      · exact Or.inr hOpp
      · exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hInt hx.1)
      · exact Or.inl (hFirstSideInExpanded hFirst)
  have hCornerActualWideEnvelope (i : Bool) (hn : corner i ∉ M.cover.branch) :
      ∃ W : Set S, IsCompact W ∧ baselineCornerTriangle i ⊆ W ∧
        W ⊆ (cornerF i).source ∧ Disjoint W (M.cover.branch : Set S) ∧
        W ∩ a.val.image ⊆ baselineCornerTriangle i ∧
        (∀ t u : Interval, cornerH i (t,u) ∈ W) ∧
        (∀ t u : Interval, 0<t.val → t.val<1 → 0<u.val → u.val<1 →
          cornerH i (t,u) ∈ interior W) ∧
        ∃ g outer : C(Interval,S), IsEmbedding g ∧ IsEmbedding outer ∧
          g 0=corner i ∧ g 1=cornerL i 0 ∧ outer 0=cornerA i ∧ outer 1=cornerL i 0 ∧
          range g ⊆ range B.secondSide ∧ range g ⊆ W ∧ range outer ⊆ W ∧
          range g=W ∩ range B.disk ∧ range outer ∩ range B.secondSide={cornerL i 0} ∧
          range outer ∩ a.val.image ⊆ {cornerA i} ∧
          (∀ u : Interval, 0<u.val → u.val<1 → g u ∈ interior (range B.disk ∪ W)) ∧
          frontier W ⊆ (baselineCornerTriangle i ∩ a.val.image) ∪ range g ∪ range outer := by
    obtain ⟨G,δ,hGS,hδ,hGp,hGA,hGL,hJoint,hBox,hAxis,hBAxis,hTImage,hSharedInterior,hVerticalSelected⟩ :=
      hBaselineTriangleLiteralChart i hn
    have hMarks : Disjoint G.source (M.cover.branch : Set S) := by
      apply Set.disjoint_left.mpr
      intro x hx hm
      have he : x=corner i := hCornerMarks i ⟨hGS ▸ hx,hm⟩
      exact hn (he ▸ hm)
    obtain ⟨W,hWc,hWS,hTW,hWM,hWA,hWH,hWI,hcap⟩ :=
      actual_unmarked_attached_wide_cap_geometry M a b B G δ hδ
        (cornerA i) (corner i) (cornerL i 0)
        (hGS.symm ▸ hCornerASource i) (hGS.symm ▸ hCornerPoint i)
        (hGS.symm ▸ hCornerBaselineSource i) hGA hGp hGL (cornerH i)
        (fun t u => hGS.symm ▸ hCornerJointSource i t u) hJoint hBox hAxis hBAxis hMarks
        (baselineCornerTriangle i) hTImage (hBaselineTriangleContact i) hVerticalSelected hSharedInterior
        hOriginalDiskFrontier
    exact ⟨W,hWc,hTW,(fun x hx => hGS ▸ hWS hx),hWM,hWA,hWH,hWI,hcap⟩
  have hActualBaselineTriangleOnAIsExpanded (i : Bool) (hn : corner i ∉ M.cover.branch) :
      (baselineCornerTriangle i ∩ a.val.image ⊆ range expandedFirst) ∧
      (i=leftPort → originalγ '' Icc expandedL L ⊆ baselineCornerTriangle i) ∧
      (i=rightPort → originalγ '' Icc R expandedR ⊆ baselineCornerTriangle i) := by
    obtain ⟨G,δ,hGS,hδ,hGp,hGA,hGL,hJoint,hBox,hAxis,hBAxis,hTImage,hSharedInterior,hVerticalSelected⟩ := hBaselineTriangleLiteralChart i hn
    obtain ⟨g,hg,hg0,hg1,hgSource,hgRange⟩ := hActualTriangleHorizontalArc G δ hδ hBox
      (cornerA i) (corner i) (hGS.symm ▸ hCornerASource i)
      (hGS.symm ▸ hCornerPoint i) hGA hGp
    have hHorizontalTarget (z : ℝ × ℝ)
        (hz : -δ ≤ z.1 ∧ z.1 ≤ 0 ∧ z.2=0) : z ∈ G.target := by
      have hh := hBox (-z.1) 0 (by linarith [hz.2.1]) (by linarith [hz.1]) le_rfl hδ.le
      simpa only [neg_neg,← hz.2.2] using hh
    have hgT : range g ⊆ baselineCornerTriangle i := by
      intro x hx
      rw [hgRange] at hx
      obtain ⟨z,hz,he⟩ := hx
      rw [hTImage]
      refine ⟨z,⟨hz.1,hz.2.1,?_,?_⟩,he⟩
      · rw [hz.2.2]
      · rw [hz.2.2]; linarith [hz.1]
    have hgA : range g ⊆ a.val.image := by
      intro x hx
      have hxS := hgSource hx
      rw [hgRange] at hx
      obtain ⟨z,hz,he⟩ := hx
      apply (hAxis x hxS).mpr
      rw [← he,G.right_inv (hHorizontalTarget z hz)]
      exact hz.2.2
    have hNo0 : a.val.map 0 ∉ range g := by
      intro hh
      exact Set.disjoint_left.mp (hBaselineTriangleMarks i) (hgT hh) a.val.start_marked
    have hNo1 : a.val.map 1 ∉ range g := by
      intro hh
      exact Set.disjoint_left.mp (hBaselineTriangleMarks i) (hgT hh) a.val.end_marked
    have hEndpointParameters : ∃ u v : Interval, g 0=a.val.map u ∧ g 1=a.val.map v ∧
        expandedL ≤ u.val ∧ u.val ≤ expandedR ∧ expandedL ≤ v.val ∧ v.val ≤ expandedR ∧
        u.val=(if i=leftPort then expandedL else expandedR) ∧
        v.val=(if i=leftPort then L else R) := by
      have hCases : i=leftPort ∨ i=rightPort := by
        rcases Bool.eq_or_eq_not i leftPort with hh|hh
        · exact Or.inl hh
        · exact Or.inr (hh.trans (Bool.not_eq_iff.mpr hPortsDifferent))
      rcases hCases with hleft|hright
      · subst i
        have hU : expandedL ∈ Icc (0:ℝ) 1 := ⟨hExpandedL0,hExpandedLR.le.trans hExpandedR1⟩
        have hV : L ∈ Icc (0:ℝ) 1 := ⟨hL,hLR.le.trans hR⟩
        let u : Interval := ⟨expandedL,hU⟩
        let v : Interval := ⟨L,hV⟩
        have hγu : originalγ expandedL=a.val.map u := by
          dsimp [originalγ,u]
          rw [Set.projIcc_of_mem zero_le_one hU]
        have hγv : originalγ L=a.val.map v := by
          dsimp [originalγ,v]
          rw [Set.projIcc_of_mem zero_le_one hV]
        exact ⟨u,v,hg0.trans (hExpandedLeft.symm.trans hγu),hg1.trans (hLeftPort.trans hγv),
          le_rfl,hExpandedLR.le,hExpandedL,hLR.le.trans hExpandedR,by simp [u],by simp [v]⟩
      · subst i
        have hU : expandedR ∈ Icc (0:ℝ) 1 := ⟨hExpandedL0.trans hExpandedLR.le,hExpandedR1⟩
        have hV : R ∈ Icc (0:ℝ) 1 := ⟨hL.trans hLR.le,hR⟩
        let u : Interval := ⟨expandedR,hU⟩
        let v : Interval := ⟨R,hV⟩
        have hγu : originalγ expandedR=a.val.map u := by
          dsimp [originalγ,u]
          rw [Set.projIcc_of_mem zero_le_one hU]
        have hγv : originalγ R=a.val.map v := by
          dsimp [originalγ,v]
          rw [Set.projIcc_of_mem zero_le_one hV]
        exact ⟨u,v,hg0.trans (hExpandedRight.symm.trans hγu),hg1.trans (hRightPort.trans hγv),
          hExpandedLR.le,le_rfl,hExpandedL.trans hLR.le,hExpandedR,
          by simp [u,hPortsDifferent.symm],by simp [v,hPortsDifferent.symm]⟩
    obtain ⟨u,v,hgU,hgV,hUL,hUR,hVL,hVR,hu,hv⟩ := hEndpointParameters
    have hgExpanded : range g ⊆ range expandedFirst := by
      rw [hExpandedFirstRange]
      have hsub := hActualUnmarkedArcLiteralParameterInterval a g hg hgA hNo0 hNo1 u v hgU hgV
      apply hsub.trans
      apply Set.image_mono
      intro t ht
      exact ⟨(le_min hUL hVL).trans ht.1,ht.2.trans (max_le hUR hVR)⟩
    have hgExact : range g=originalγ '' Icc (min u.val v.val) (max u.val v.val) :=
      hActualUnmarkedArcLiteralParameterTraceEq a g hg hgA hNo0 hNo1 u v hgU hgV
    refine ⟨?_,?_,?_⟩
    · intro x hx
      have hxG : x ∈ G.source := hGS.symm ▸ hBaselineTriangleSource i hx.1
      obtain ⟨z,hz,he⟩ := hTImage ▸ hx.1
      have hzT : z ∈ G.target := by
        have hh := hBox (-z.1) z.2 (by linarith [hz.2.1]) (by linarith [hz.1])
          hz.2.2.1 (by linarith [hz.2.1,hz.2.2.2])
        simpa only [neg_neg] using hh
      have hz0 : z.2=0 := by
        have hh := (hAxis x hxG).mp hx.2
        rw [← he,G.right_inv hzT] at hh
        exact hh
      apply hgExpanded
      rw [hgRange]
      exact ⟨z,⟨hz.1,hz.2.1,hz0⟩,he⟩
    · intro hi
      subst i
      simp only [if_pos rfl] at hu hv
      rw [hu,hv] at hgExact
      simp only [ite_true,min_eq_left hExpandedL,max_eq_right hExpandedL] at hgExact
      exact hgExact ▸ hgT
    · intro hi
      subst i
      simp only [if_neg hPortsDifferent.symm] at hu hv
      rw [hu,hv] at hgExact
      simp only [if_neg hPortsDifferent.symm,ite_false,min_eq_right hExpandedR,max_eq_left hExpandedR] at hgExact
      exact hgExact ▸ hgT
  have hActualExpandedFirstInBaselineCap : range expandedFirst ⊆ actualBaselineCapSet := by
    rw [hExpandedFirstRange]
    rintro x ⟨t,ht,rfl⟩
    by_cases hleft : t<L
    · by_cases hm : corner leftPort ∈ M.cover.branch
      · exact False.elim (by have hh := hExpandedLeftMarked hm; linarith [ht.1])
      · exact Or.inr (Set.mem_iUnion.mpr ⟨leftPort,
          (hActualBaselineTriangleOnAIsExpanded leftPort hm).2.1 rfl
            (Set.mem_image_of_mem originalγ ⟨ht.1,hleft.le⟩)⟩)
    · by_cases hright : R<t
      · by_cases hm : corner rightPort ∈ M.cover.branch
        · exact False.elim (by have hh := hExpandedRightMarked hm; linarith [ht.2])
        · exact Or.inr (Set.mem_iUnion.mpr ⟨rightPort,
            (hActualBaselineTriangleOnAIsExpanded rightPort hm).2.2 rfl
              (Set.mem_image_of_mem originalγ ⟨hright.le,ht.2⟩)⟩)
      · apply Or.inl
        have hx : originalγ t ∈ range B.firstSide := hSide.symm ▸
          Set.mem_image_of_mem originalγ ⟨le_of_not_gt hleft,le_of_not_gt hright⟩
        exact (show originalγ t ∈ range B.disk ∩ a.val.image from hDiskA.symm ▸ hx).1
  have hActualBaselineCapExpandedRemainder : actualBaselineCapSet ∩ expandedK ⊆
      ({cornerA false,cornerA true} : Set S) := by
    have hAnyPort (i : Bool) : cornerA i ∈ ({cornerA false,cornerA true} : Set S) := by
      cases i <;> simp
    rintro x ⟨(hxD|hxT),hxK⟩
    · have hxA : x ∈ a.val.image := hdecompRaw.symm ▸ Or.inr (hExpandedKSubset hxK)
      have hxFirst : x ∈ range B.firstSide := hDiskA ▸ ⟨hxD,hxA⟩
      have hxc : x ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
        hmeetRaw ▸ ⟨hxFirst,hExpandedKSubset hxK⟩
      by_cases hm : x ∈ M.cover.branch
      · rcases hxc with h0|h1
        · have hmark : corner false ∈ M.cover.branch := by
            change B.firstCorner ∈ M.cover.branch
            exact h0 ▸ hm
          have he := hCornerAMarked false hmark
          exact (h0.trans he.symm).symm ▸ hAnyPort false
        · have he1 : x=B.secondCorner := by simpa using h1
          have hmark : corner true ∈ M.cover.branch := by
            change B.secondCorner ∈ M.cover.branch
            exact he1 ▸ hm
          have he := hCornerAMarked true hmark
          exact (he1.trans he.symm).symm ▸ hAnyPort true
      · exact False.elim (hUnmarkedCornerOffExpandedK x hxc hm hxK)
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hxT
      by_cases hm : corner i ∈ M.cover.branch
      · rw [hBaselineMarkedTriangleEmpty i hm] at hi
        exact False.elim hi
      · have hxA : x ∈ a.val.image := hdecompRaw.symm ▸ Or.inr (hExpandedKSubset hxK)
        have hxExpanded := (hActualBaselineTriangleOnAIsExpanded i hm).1 ⟨hi,hxA⟩
        have hports : x ∈ ({originalγ expandedL,originalγ expandedR} : Set S) :=
          hExpandedMeet ▸ ⟨hxExpanded,hxK⟩
        rcases hports with h0|h1
        · exact (h0.trans hExpandedLeft).symm ▸ hAnyPort leftPort
        · exact (h1.trans hExpandedRight).symm ▸ hAnyPort rightPort
  have hBaselineOtherTriangle (i : Bool) : Disjoint (cornerF i).source (baselineCornerTriangle (!i)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    cases i
    · exact Set.disjoint_left.mp hSepDisjoint (hCornerSource false hx).2
        (hCornerSource true (hBaselineTriangleSource true hy)).2
    · exact Set.disjoint_left.mp hSepDisjoint
        (hCornerSource false (hBaselineTriangleSource false hy)).2 (hCornerSource true hx).2
  have hBaselineTriangleVertexFrontier (i : Bool) (hn : corner i ∉ M.cover.branch) :
      cornerA i ∈ frontier (baselineCornerTriangle i) := by
    obtain ⟨G,δ,hGS,hδ,hGp,hGA,hGL,hJoint,hBox,hAxis,hBAxis,hTImage,hSharedInterior,hVerticalSelected⟩ := hBaselineTriangleLiteralChart i hn
    rw [(hBaselineTriangleCompact i).isClosed.frontier_eq]
    refine ⟨(hBaselineTriangleLiteralPorts i hn).1,?_⟩
    intro hi
    let U : Set S := G.source ∩ interior (baselineCornerTriangle i)
    have hU : IsOpen U := G.open_source.inter isOpen_interior
    have hUsub : U ⊆ G.source := inter_subset_left
    have hImageOpen : IsOpen (G '' U) := G.isOpen_image_of_subset_source hU hUsub
    have hAimage : (-δ,0) ∈ G '' U := ⟨cornerA i,⟨hGS.symm ▸ hCornerASource i,hi⟩,hGA⟩
    obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp hImageOpen (-δ,0) hAimage
    have hqBall : (-δ-r/2,(0:ℝ)) ∈ Metric.ball (-δ,0) r := by
      rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      have he : -δ-r/2-(-δ)= -(r/2) := by ring
      rw [he]
      simp only [sub_self,abs_zero,abs_neg,abs_of_pos (half_pos hr),max_eq_left (half_pos hr).le]
      exact half_lt_self hr
    obtain ⟨x,hxU,hxq⟩ := hBall hqBall
    have hxT : x ∈ baselineCornerTriangle i := interior_subset hxU.2
    obtain ⟨z,hz,he⟩ := hTImage ▸ hxT
    have hzTarget : z ∈ G.target := by
      have hh := hBox (-z.1) z.2 (by linarith [hz.2.1]) (by linarith [hz.1])
        hz.2.2.1 (by linarith [hz.2.1,hz.2.2.2])
      simpa only [neg_neg] using hh
    have hzCoord : G x=z := by rw [← he,G.right_inv hzTarget]
    have hzX := congrArg Prod.fst (hzCoord.symm.trans hxq)
    change z.1= -δ-r/2 at hzX
    linarith [hz.1]
  have hActualBaselinePortFrontier (i : Bool) : cornerA i ∈ frontier actualBaselineCapSet := by
    have hOther : cornerA i ∉ baselineCornerTriangle (!i) :=
      fun hh => Set.disjoint_left.mp (hBaselineOtherTriangle i) (hCornerASource i) hh
    have hCapDecomposition : actualBaselineCapSet=
        baselineCornerTriangle i ∪ (range B.disk ∪ baselineCornerTriangle (!i)) := by
      ext x
      simp only [actualBaselineCapSet,Set.mem_union,Set.mem_iUnion]
      cases i <;> constructor
      · rintro (hx|⟨j,hj⟩)
        · exact Or.inr (Or.inl hx)
        · cases j
          · exact Or.inl hj
          · exact Or.inr (Or.inr hj)
      · rintro (hx|hx|hx)
        · exact Or.inr ⟨false,hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨true,hx⟩
      · rintro (hx|⟨j,hj⟩)
        · exact Or.inr (Or.inl hx)
        · cases j
          · exact Or.inr (Or.inr hj)
          · exact Or.inl hj
      · rintro (hx|hx|hx)
        · exact Or.inr ⟨true,hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨false,hx⟩
    by_cases hm : corner i ∈ M.cover.branch
    · have hAi : cornerA i=corner i := hCornerAMarked i hm
      have hTEmpty := hBaselineMarkedTriangleEmpty i hm
      have hOriginalCornerFront : corner i ∈ frontier (range B.disk) := by
        rw [hOriginalDiskFrontier]
        cases i
        · exact Or.inl ⟨0,B.first_zero⟩
        · exact Or.inl ⟨1,B.first_one⟩
      have hf := CurveComplex.mem_frontier_union_of_not_mem_closed
        (hBaselineTriangleCompact (!i)).isClosed hOther (hAi.symm ▸ hOriginalCornerFront)
      rw [hCapDecomposition,hTEmpty,empty_union]
      exact hf
    · have hAiOffDisk : cornerA i ∉ range B.disk := by
        intro hh
        have hxA : cornerA i ∈ a.val.image := hdecompRaw.symm ▸ Or.inr (hCornerAK i)
        exact hCornerAUnmarked i hm (hDiskA ▸ ⟨hh,hxA⟩)
      rw [hCapDecomposition]
      exact CurveComplex.mem_frontier_union_of_not_mem_closed
        ((isCompact_range B.disk.continuous).isClosed.union (hBaselineTriangleCompact (!i)).isClosed)
        (fun hh => hh.elim hAiOffDisk hOther) (hBaselineTriangleVertexFrontier i hm)
  have hActualBaselineInteriorClearance : Disjoint (interior actualBaselineCapSet)
      ((M.cover.branch : Set S) ∪ expandedK) := by
    apply Set.disjoint_left.mpr
    rintro x hx (hm|hk)
    · have hp := hActualBaselineCapMarks ⟨interior_subset hx,hm⟩
      rcases hp with h0|h1
      · exact (hActualBaselinePortFrontier false).2 (h0 ▸ hx)
      · have he1 : x=cornerA true := by simpa using h1
        exact (hActualBaselinePortFrontier true).2 (he1 ▸ hx)
    · have hp := hActualBaselineCapExpandedRemainder ⟨interior_subset hx,hk⟩
      rcases hp with h0|h1
      · exact (hActualBaselinePortFrontier false).2 (h0 ▸ hx)
      · have he1 : x=cornerA true := by simpa using h1
        exact (hActualBaselinePortFrontier true).2 (he1 ▸ hx)
  have hActualBaselineTriangleFrontier (i : Bool) :
      frontier actualBaselineCapSet ∩ baselineCornerTriangle i ⊆
        range expandedFirst ∪ range baselineOpposite := by
    intro x hx
    by_cases hm : corner i ∈ M.cover.branch
    · exact False.elim (by simpa only [hBaselineMarkedTriangleEmpty i hm,Set.mem_empty_iff_false] using hx.2)
    · obtain ⟨G,δ,hGS,hδ,hGp,hGA,hGL,hJoint,hBox,hAxis,hBAxis,hTImage,hSharedInterior,hVerticalSelected⟩ :=
        hBaselineTriangleLiteralChart i hm
      obtain ⟨z,hz,he⟩ := hTImage ▸ hx.2
      have hzT : z ∈ G.target := by
        have hh := hBox (-z.1) z.2 (by linarith [hz.2.1]) (by linarith [hz.1])
          hz.2.2.1 (by linarith [hz.2.1,hz.2.2.2])
        simpa only [neg_neg] using hh
      have hxS : x ∈ G.source := he ▸ G.map_target hzT
      by_cases hy0 : z.2=0
      · apply Or.inl
        apply (hActualBaselineTriangleOnAIsExpanded i hm).1
        exact ⟨hx.2,(hAxis x hxS).mpr (by rw [← he,G.right_inv hzT]; exact hy0)⟩
      by_cases hdiag : z.2=z.1+δ
      · apply Or.inr
        let u : Interval := ⟨z.2/δ,div_nonneg hz.2.2.1 hδ.le,
          (div_le_one hδ).mpr (by linarith [hz.2.1,hz.2.2.2])⟩
        have hu : δ*u.val=z.2 := by dsimp [u]; field_simp [ne_of_gt hδ]
        have huDivision : δ*(z.2/δ)=z.2 := hu
        have hc : G (baselineCorner i u)=z := by
          have hh := hJoint 0 u
          change G (baselineCorner i u)=z
          apply Prod.ext
          · have hhx := congrArg Prod.fst hh
            change (G (cornerH i (0,u))).1= -(δ*(1-u.val)+(δ/2*0)*u.val) at hhx
            simp only [mul_zero,zero_mul,add_zero] at hhx
            change (G (cornerH i (0,u))).1=z.1
            rw [hhx]
            nlinarith [hu]
          · exact (congrArg Prod.snd hh).trans hu
        have heq : baselineCorner i u=x := G.injOn
          (hGS.symm ▸ hCornerJointSource i 0 u) hxS
          (hc.trans (by rw [← he,G.right_inv hzT]))
        rw [hActualBaselineOppositeWholeTrace]
        cases i
        · exact Or.inl (Or.inl ⟨u,heq⟩)
        · exact Or.inr ⟨u,heq⟩
      by_cases hx0 : z.1=0
      · have hypos : 0<z.2 := lt_of_le_of_ne hz.2.2.1 (Ne.symm hy0)
        have hylt : z.2<δ := by
          have hn : z.2≠δ := by intro hh; exact hdiag (by rw [hx0]; simpa using hh)
          exact lt_of_le_of_ne (by linarith [hz.2.2.2]) hn
        have hh := hSharedInterior z.2 hypos hylt
        have hi : x ∈ interior actualBaselineCapSet := by
          have hez : z=(0,z.2) := Prod.ext hx0 rfl
          rw [← he,hez]
          exact interior_mono (show range B.disk ∪ baselineCornerTriangle i ⊆ actualBaselineCapSet from
            fun _ hh => hh.elim Or.inl (fun ht => Or.inr (Set.mem_iUnion.mpr ⟨i,ht⟩))) hh
        exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hi hx.1)
      · let P : Set (ℝ × ℝ) := {q | -δ<q.1 ∧ q.1<0 ∧ 0<q.2 ∧ q.2<q.1+δ}
        have hPo : IsOpen P := (isOpen_lt continuous_const continuous_fst).inter
          ((isOpen_lt continuous_fst continuous_const).inter
            ((isOpen_lt continuous_const continuous_snd).inter
              (isOpen_lt continuous_snd (by fun_prop))))
        have hPsub : P ⊆ {q : ℝ × ℝ | -δ≤q.1 ∧ q.1≤0 ∧ 0≤q.2 ∧ q.2≤q.1+δ} :=
          fun _ hh => ⟨hh.1.le,hh.2.1.le,hh.2.2.1.le,hh.2.2.2.le⟩
        have hPt : P ⊆ G.target := by
          intro q hq
          have hh := hPsub hq
          have hh' := hBox (-q.1) q.2 (by linarith [hh.2.1]) (by linarith [hh.1])
            hh.2.2.1 (by linarith [hh.2.1,hh.2.2.2])
          simpa only [neg_neg] using hh'
        have hzP : z ∈ P := by
          exact ⟨by have hh := lt_of_le_of_ne hz.2.2.1 (Ne.symm hy0); linarith [hz.2.2.2],
            lt_of_le_of_ne hz.2.1 hx0,lt_of_le_of_ne hz.2.2.1 (Ne.symm hy0),
            lt_of_le_of_ne hz.2.2.2 hdiag⟩
        have hImageSub : G.symm '' P ⊆ actualBaselineCapSet := by
          intro y hy
          exact Or.inr (Set.mem_iUnion.mpr ⟨i,hTImage.symm ▸ Set.image_mono hPsub hy⟩)
        have hi : x ∈ interior actualBaselineCapSet := interior_maximal hImageSub
          (G.symm.isOpen_image_of_subset_source hPo hPt) ⟨z,hzP,he⟩
        exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hi hx.1)
  have hActualBaselineCapFrontier : frontier actualBaselineCapSet ⊆
      range expandedFirst ∪ range baselineOpposite := by
    intro x hx
    have hk := hActualBaselineCapCompact.isClosed.frontier_subset hx
    rcases hk with hD|hT
    · exact hActualBaselineOriginalDiskFrontier ⟨hx,hD⟩
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hT
      exact hActualBaselineTriangleFrontier i ⟨hx,hi⟩
  have hActualCornerSupportEnvelope (i : Bool) :
      ∃ W : Set S, IsCompact W ∧ W ⊆ (cornerF i).source ∧
        W ∩ ((M.cover.branch : Set S) ∪ expandedK) ⊆ {cornerA i} ∧
        (corner i ∈ M.cover.branch → W ∩ a.val.image ⊆ {corner i}) ∧
        (corner i ∉ M.cover.branch → W ∩ a.val.image ⊆ baselineCornerTriangle i) ∧
        (corner i ∉ M.cover.branch → baselineCornerTriangle i ⊆ W) ∧
        (corner i ∈ M.cover.branch → ∃ g : C(Interval,S), IsEmbedding g ∧ g 0=corner i ∧
          range g ⊆ range B.secondSide ∧ range g ⊆ W ∧ range g=W ∩ range B.disk ∧
          (∀ u : Interval, 0<u.val → u.val<1 → g u ∈ interior (range B.disk ∪ W)) ∧
          ∃ outer : C(Interval,S), IsEmbedding outer ∧ outer 0=corner i ∧ outer 1=g 1 ∧
            range outer ⊆ W ∧ range outer ∩ range B.secondSide={corner i,g 1} ∧
            range outer ∩ a.val.image ⊆ {corner i} ∧ frontier W ⊆ range g ∪ range outer) ∧
        (corner i ∉ M.cover.branch → ∃ g outer : C(Interval,S), IsEmbedding g ∧ IsEmbedding outer ∧
          g 0=corner i ∧ g 1=cornerL i 0 ∧ outer 0=cornerA i ∧ outer 1=cornerL i 0 ∧
          range g ⊆ range B.secondSide ∧ range g ⊆ W ∧ range outer ⊆ W ∧
          range g=W ∩ range B.disk ∧ range outer ∩ range B.secondSide={cornerL i 0} ∧
          range outer ∩ a.val.image ⊆ {cornerA i} ∧
          (∀ u : Interval, 0<u.val → u.val<1 → g u ∈ interior (range B.disk ∪ W)) ∧
          frontier W ⊆ (baselineCornerTriangle i ∩ a.val.image) ∪ range g ∪ range outer) ∧
        (∀ t u : Interval, cornerH i (t,u) ∈ W) ∧
        (∀ t u : Interval, 0<t.val → t.val<1 → 0<u.val → u.val<1 →
          cornerH i (t,u) ∈ interior W) := by
    by_cases hm : corner i ∈ M.cover.branch
    · obtain ⟨W,hWc,hWS,hWM,hWA,hWD,hWH,hWHInterior,hCapBase⟩ := hCornerMarkedWideEnvelope i hm
      refine ⟨W,hWc,hWS,?_,(fun _ => hWA),(fun hn => False.elim (hn hm)),(fun hn => False.elim (hn hm)),(fun _ => hCapBase),(fun hn => False.elim (hn hm)),hWH,?_⟩
      · intro x hx
        have hp : x=corner i := by
          rcases hx.2 with hmarks|hK
          · exact Set.mem_singleton_iff.mp (hWM ⟨hx.1,hmarks⟩)
          · exact Set.mem_singleton_iff.mp (hWA ⟨hx.1,hExpandedDecomposition.symm ▸ Or.inr hK⟩)
        exact Set.mem_singleton_iff.mpr (hp.trans (hCornerAMarked i hm).symm)
      · intro t u ht ht1 hu hu1
        exact hWHInterior t u ht hu
    · obtain ⟨W,hWc,hTW,hWS,hWM,hWA,hWH,hWHInterior,hCapUnmarked⟩ := hCornerActualWideEnvelope i hm
      refine ⟨W,hWc,hWS,?_,(fun hh => False.elim (hm hh)),(fun _ => hWA),(fun _ => hTW),(fun hh => False.elim (hm hh)),(fun _ => hCapUnmarked),hWH,hWHInterior⟩
      intro x hx
      rcases hx.2 with hmarks|hK
      · exact False.elim (Set.disjoint_left.mp hWM hx.1 hmarks)
      · have hT : x ∈ baselineCornerTriangle i := hWA ⟨hx.1,hExpandedDecomposition.symm ▸ Or.inr hK⟩
        have hp := hActualBaselineCapExpandedRemainder
          ⟨Or.inr (Set.mem_iUnion.mpr ⟨i,hT⟩),hK⟩
        have hxSep := (hCornerSource i (hWS hx.1)).2
        cases i
        · rcases hp with he|he
          · exact Set.mem_singleton_iff.mpr he
          · have he1 : x=cornerA true := by simpa using he
            have ho := (hCornerSource true (hCornerASource true)).2
            exact False.elim (Set.disjoint_left.mp hSepDisjoint hxSep (he1.symm ▸ ho))
        · rcases hp with he|he
          · have ho := (hCornerSource false (hCornerASource false)).2
            exact False.elim (Set.disjoint_left.mp hSepDisjoint (he.symm ▸ ho) hxSep)
          · exact Set.mem_singleton_iff.mpr (by simpa using he)
  choose cornerSupportEnvelope hCornerSupportCompact hCornerSupportSource hCornerSupportObstacles
    hCornerSupportMarkedA hCornerSupportUnmarkedA hCornerTriangleWide hCornerSupportMarkedBase hCornerSupportUnmarkedCap hCornerSupportWholeFamily hCornerSupportInterior using hActualCornerSupportEnvelope
  have hActualCornerAttachedWideCap (i : Bool) :
      ∃ g outer : C(Interval,S), IsEmbedding g ∧ IsEmbedding outer ∧
        g 0=corner i ∧ outer 0=cornerA i ∧ outer 1=g 1 ∧
        range g ⊆ range B.secondSide ∧ range g ⊆ cornerSupportEnvelope i ∧
        range outer ⊆ cornerSupportEnvelope i ∧
        range g=cornerSupportEnvelope i ∩ range B.disk ∧
        range outer ∩ range B.secondSide ⊆ {corner i,g 1} ∧
        range outer ∩ a.val.image ⊆ {cornerA i} ∧
        (∀ u : Interval, 0<u.val → u.val<1 → g u ∈ interior (range B.disk ∪ cornerSupportEnvelope i)) ∧
        frontier (cornerSupportEnvelope i) ⊆ range expandedFirst ∪ range g ∪ range outer := by
    by_cases hm : corner i ∈ M.cover.branch
    · obtain ⟨g,hg,hg0,hgb,hgW,hgContact,hgInt,outer,ho,ho0,ho1,hoW,hoB,hoA,hFront⟩ :=
        hCornerSupportMarkedBase i hm
      refine ⟨g,outer,hg,ho,hg0,ho0.trans (hCornerAMarked i hm).symm,ho1,hgb,hgW,hoW,hgContact,
        (fun _ hx => hoB ▸ hx),?_,hgInt,?_⟩
      · intro x hx
        have he : x=corner i := Set.mem_singleton_iff.mp (hoA hx)
        exact Set.mem_singleton_iff.mpr (he.trans (hCornerAMarked i hm).symm)
      · intro x hx
        rcases hFront hx with hgx|hox
        · exact Or.inl (Or.inr hgx)
        · exact Or.inr hox
    · obtain ⟨g,outer,hg,ho,hg0,hg1,ho0,ho1,hgb,hgW,hoW,hgContact,hoB,hoA,hgInt,hFront⟩ :=
        hCornerSupportUnmarkedCap i hm
      refine ⟨g,outer,hg,ho,hg0,ho0,ho1.trans hg1.symm,hgb,hgW,hoW,hgContact,?_,hoA,hgInt,?_⟩
      · intro x hx
        have he : x=cornerL i 0 := Set.mem_singleton_iff.mp (hoB ▸ hx)
        exact Or.inr (he.trans hg1.symm)
      · intro x hx
        rcases hFront hx with (haT|hgx)|hox
        · exact Or.inl (Or.inl ((hActualBaselineTriangleOnAIsExpanded i hm).1 haT))
        · exact Or.inl (Or.inr hgx)
        · exact Or.inr hox
  choose wideCornerBase wideCornerOuter hWideCornerBaseEmbedded hWideCornerOuterEmbedded
    hWideCornerBaseZero hWideCornerOuterZero hWideCornerOuterOne hWideCornerBaseSide
    hWideCornerBaseInEnvelope hWideCornerOuterInEnvelope hWideCornerBaseDiskContact
    hWideCornerOuterSideContact hWideCornerOuterAContact hWideCornerBaseSeamInterior
    hWideCornerEnvelopeFrontier using hActualCornerAttachedWideCap
  have hWideCornerEnvelopeDisjoint : Disjoint (cornerSupportEnvelope false) (cornerSupportEnvelope true) := by
    apply Set.disjoint_left.mpr
    intro x hx0 hx1
    exact Set.disjoint_left.mp hSepDisjoint
      ((hCornerSource false (hCornerSupportSource false hx0)).2)
      ((hCornerSource true (hCornerSupportSource true hx1)).2)
  have hWideCornerCutExists (i : Bool) : ∃ u : Interval, B.secondSide u=wideCornerBase i 1 :=
    hWideCornerBaseSide i (Set.mem_range_self 1)
  choose wideCornerCut hWideCornerCut using hWideCornerCutExists
  have hWideCornerBaseLiteralTrace (i : Bool) :
      range (wideCornerBase i)=B.secondSide ''
        Icc (min (if i then (1:Interval) else 0) (wideCornerCut i))
          (max (if i then (1:Interval) else 0) (wideCornerCut i)) := by
    have hp : B.secondSide (if i then (1:Interval) else 0)=corner i := by
      cases i
      · exact B.second_zero
      · exact B.second_one
    exact hActualEmbeddedArcLiteralIntervalTrace B.secondSide (wideCornerBase i)
      B.second_embedded (hWideCornerBaseEmbedded i) (hWideCornerBaseSide i)
      (if i then (1:Interval) else 0) (wideCornerCut i)
      ((hWideCornerBaseZero i).trans hp.symm) (hWideCornerCut i).symm
  have hWideCornerCuts : wideCornerCut false < wideCornerCut true := by
    by_contra hh
    have hle : wideCornerCut true ≤ wideCornerCut false := le_of_not_gt hh
    have hx0 : B.secondSide (wideCornerCut false) ∈ cornerSupportEnvelope false :=
      hWideCornerCut false ▸ hWideCornerBaseInEnvelope false (Set.mem_range_self 1)
    have hx1 : B.secondSide (wideCornerCut false) ∈ cornerSupportEnvelope true := by
      apply hWideCornerBaseInEnvelope true
      rw [hWideCornerBaseLiteralTrace]
      refine ⟨wideCornerCut false,?_,rfl⟩
      change min 1 (wideCornerCut true) ≤ wideCornerCut false ∧
        wideCornerCut false ≤ max 1 (wideCornerCut true)
      rw [min_eq_right (show wideCornerCut true ≤ 1 from le_top),
        max_eq_left (show wideCornerCut true ≤ 1 from le_top)]
      exact ⟨hle,le_top⟩
    exact Set.disjoint_left.mp hWideCornerEnvelopeDisjoint hx0 hx1
  let wideMiddle : C(Interval,S) := ⟨fun u => ψ ((wideCornerCut false).val+
    u.val*((wideCornerCut true).val-(wideCornerCut false).val)),hψ.comp (by fun_prop)⟩
  have hWideMiddleθ (u : Interval) :
      (wideCornerCut false).val ≤ (wideCornerCut false).val+u.val*((wideCornerCut true).val-(wideCornerCut false).val) ∧
      (wideCornerCut false).val+u.val*((wideCornerCut true).val-(wideCornerCut false).val) ≤ (wideCornerCut true).val := by
    have h0 := mul_nonneg u.property.1 (sub_pos.mpr (show (wideCornerCut false).val < (wideCornerCut true).val from hWideCornerCuts)).le
    have h1 := mul_nonneg (sub_nonneg.mpr u.property.2) (sub_pos.mpr (show (wideCornerCut false).val < (wideCornerCut true).val from hWideCornerCuts)).le
    constructor <;> nlinarith
  have hWideMiddle01 (u : Interval) :
      (wideCornerCut false).val+u.val*((wideCornerCut true).val-(wideCornerCut false).val) ∈ Icc (0:ℝ) 1 :=
    ⟨(wideCornerCut false).property.1.trans (hWideMiddleθ u).1,
      (hWideMiddleθ u).2.trans (wideCornerCut true).property.2⟩
  have hWideMiddleEmbedded : IsEmbedding wideMiddle := by
    apply (wideMiddle.continuous.isClosedEmbedding ?_).isEmbedding
    intro u v he
    have hh := hψInjective _ _ (hWideMiddle01 u) (hWideMiddle01 v) he
    apply Subtype.ext
    exact mul_right_cancel₀ (ne_of_gt (sub_pos.mpr (show (wideCornerCut false).val < (wideCornerCut true).val from hWideCornerCuts))) (add_left_cancel hh)
  have hWideMiddleZero : wideMiddle 0=wideCornerBase false 1 := by
    simpa [wideMiddle,ψ,Set.projIcc_of_mem zero_le_one (wideCornerCut false).property]
      using hWideCornerCut false
  have hWideMiddleOne : wideMiddle 1=wideCornerBase true 1 := by
    have hθ1 : (wideCornerCut false).val+((wideCornerCut true).val-(wideCornerCut false).val)=
        (wideCornerCut true).val := by ring
    simpa [wideMiddle,ψ,hθ1,Set.projIcc_of_mem zero_le_one (wideCornerCut true).property]
      using hWideCornerCut true
  have hWideMiddleSide : range wideMiddle ⊆ range B.secondSide := by
    rintro x ⟨u,rfl⟩
    exact Set.mem_range_self _
  have hWideMiddleRange : range wideMiddle=B.secondSide '' Icc (wideCornerCut false) (wideCornerCut true) := by
    have hh := hActualEmbeddedArcLiteralIntervalTrace B.secondSide wideMiddle
      B.second_embedded hWideMiddleEmbedded hWideMiddleSide (wideCornerCut false) (wideCornerCut true)
      (hWideMiddleZero.trans (hWideCornerCut false).symm)
      (hWideMiddleOne.trans (hWideCornerCut true).symm)
    simpa only [min_eq_left (show wideCornerCut false ≤ wideCornerCut true from hWideCornerCuts.le),max_eq_right (show wideCornerCut false ≤ wideCornerCut true from hWideCornerCuts.le)] using hh
  have hWideCornerCutFalsePositive : 0 < (wideCornerCut false).val := by
    apply lt_of_le_of_ne (wideCornerCut false).property.1
    intro he
    have hu : wideCornerCut false=0 := Subtype.ext he.symm
    have hg : wideCornerBase false 1=wideCornerBase false 0 :=
      (hWideCornerCut false).symm.trans ((congrArg B.secondSide hu).trans
        (B.second_zero.trans (hWideCornerBaseZero false).symm))
    exact one_ne_zero ((hWideCornerBaseEmbedded false).injective hg)
  have hWideCornerCutTrueBelowOne : (wideCornerCut true).val < 1 := by
    apply lt_of_le_of_ne (wideCornerCut true).property.2
    intro he
    have hu : wideCornerCut true=1 := Subtype.ext he
    have hg : wideCornerBase true 1=wideCornerBase true 0 :=
      (hWideCornerCut true).symm.trans ((congrArg B.secondSide hu).trans
        (B.second_one.trans (hWideCornerBaseZero true).symm))
    exact one_ne_zero ((hWideCornerBaseEmbedded true).injective hg)
  have hWideMiddleNoCorner (i : Bool) : corner i ∉ range wideMiddle := by
    rintro ⟨u,hu⟩
    have hparam := hWideMiddleθ u
    have h01 := hWideMiddle01 u
    have hh : B.secondSide (Set.projIcc 0 1 zero_le_one
        ((wideCornerCut false).val+u.val*((wideCornerCut true).val-(wideCornerCut false).val)))=corner i := hu
    have hp : B.secondSide (if i then (1:Interval) else 0)=corner i := by
      cases i
      · exact B.second_zero
      · exact B.second_one
    have he := congrArg Subtype.val (B.second_embedded.injective (hh.trans hp.symm))
    rw [Set.projIcc_of_mem zero_le_one h01] at he
    cases i
    · change (wideCornerCut false).val+u.val*((wideCornerCut true).val-(wideCornerCut false).val)=0 at he
      linarith [hWideCornerCutFalsePositive]
    · change (wideCornerCut false).val+u.val*((wideCornerCut true).val-(wideCornerCut false).val)=1 at he
      linarith [hWideCornerCutTrueBelowOne]
  have hWideOuterMiddleMeet (i : Bool) :
      range (wideCornerOuter i) ∩ range wideMiddle={wideCornerBase i 1} := by
    ext x
    constructor
    · rintro ⟨hx,hm⟩
      rcases hWideCornerOuterSideContact i ⟨hx,hWideMiddleSide hm⟩ with he|he
      · exact False.elim (hWideMiddleNoCorner i (he ▸ hm))
      · exact he
    · rintro rfl
      refine ⟨⟨1,hWideCornerOuterOne i⟩,?_⟩
      cases i
      · exact ⟨0,hWideMiddleZero⟩
      · exact ⟨1,hWideMiddleOne⟩
  obtain ⟨wideLeftMiddle,hWideLeftMiddleEmbedded,hWideLeftMiddleZero,
    hWideLeftMiddleOne,hWideLeftMiddleRange⟩ :=
    CurveComplex.source_embedded_arc_concatenation (wideCornerOuter false) wideMiddle
      (hWideCornerOuterEmbedded false) hWideMiddleEmbedded
      ((hWideCornerOuterOne false).trans hWideMiddleZero.symm)
      (by rw [hWideCornerOuterOne false]; exact hWideOuterMiddleMeet false)
  obtain ⟨wideRight,hWideRightEmbedded,hWideRightRange,hWideRightZero,hWideRightOne⟩ :=
    actual_reverse_embedded_continuous_arc (wideCornerOuter true) (hWideCornerOuterEmbedded true)
  have hWideLastMeet : range wideLeftMiddle ∩ range wideRight={wideLeftMiddle 1} := by
    rw [hWideLeftMiddleRange,hWideRightRange,hWideLeftMiddleOne,hWideMiddleOne]
    ext x
    constructor
    · rintro ⟨(hx|hx),hr⟩
      · exact False.elim (Set.disjoint_left.mp hWideCornerEnvelopeDisjoint
          (hWideCornerOuterInEnvelope false hx) (hWideCornerOuterInEnvelope true hr))
      · exact hWideOuterMiddleMeet true ▸ ⟨hr,hx⟩
    · rintro rfl
      exact ⟨Or.inr ⟨1,hWideMiddleOne⟩,⟨1,hWideCornerOuterOne true⟩⟩
  obtain ⟨wideOpposite,hWideOppositeEmbedded,hWideOppositeZero,hWideOppositeOne,
    hWideOppositeRange⟩ := CurveComplex.source_embedded_arc_concatenation wideLeftMiddle wideRight
      hWideLeftMiddleEmbedded hWideRightEmbedded
      (hWideLeftMiddleOne.trans (hWideMiddleOne.trans ((hWideCornerOuterOne true).symm.trans hWideRightZero.symm)))
      hWideLastMeet
  have hActualWideOppositePorts : wideOpposite 0=cornerA false ∧ wideOpposite 1=cornerA true :=
    ⟨hWideOppositeZero.trans (hWideLeftMiddleZero.trans (hWideCornerOuterZero false)),
      hWideOppositeOne.trans (hWideRightOne.trans (hWideCornerOuterZero true))⟩
  have hActualWideOppositeWholeTrace : range wideOpposite=
      (range (wideCornerOuter false) ∪ range wideMiddle) ∪ range (wideCornerOuter true) := by
    rw [hWideOppositeRange,hWideLeftMiddleRange,hWideRightRange]
  have hWideMiddleAFree : Disjoint (range wideMiddle) a.val.image := by
    apply Set.disjoint_left.mpr
    intro x hx haX
    have hp : x ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
      hsecondclean ▸ ⟨hWideMiddleSide hx,haX⟩
    rcases hp with hp|hp
    · have he : x=corner false := by simpa [corner] using hp
      exact hWideMiddleNoCorner false (he ▸ hx)
    · have he : x=corner true := by simpa [corner] using hp
      exact hWideMiddleNoCorner true (he ▸ hx)
  have hActualWideOppositeAIntersection : range wideOpposite ∩ a.val.image=
      ({cornerA false,cornerA true} : Set S) := by
    ext x
    constructor
    · rintro ⟨hx,haX⟩
      rw [hActualWideOppositeWholeTrace] at hx
      rcases hx with (hx|hx)|hx
      · exact Or.inl (hWideCornerOuterAContact false ⟨hx,haX⟩)
      · exact False.elim (Set.disjoint_left.mp hWideMiddleAFree hx haX)
      · exact Or.inr (hWideCornerOuterAContact true ⟨hx,haX⟩)
    · rintro (he|he)
      · exact ⟨⟨0,hActualWideOppositePorts.1.trans he.symm⟩,he.symm ▸ hCornerAOnA false⟩
      · have he1 : x=cornerA true := by simpa using he
        exact ⟨⟨1,hActualWideOppositePorts.2.trans he1.symm⟩,he1.symm ▸ hCornerAOnA true⟩
  let actualWideBaselineCapSet : Set S := range B.disk ∪ ⋃ i : Bool, cornerSupportEnvelope i
  have hActualWideBaselineCapCompact : IsCompact actualWideBaselineCapSet :=
    (isCompact_range B.disk.continuous).union (isCompact_iUnion hCornerSupportCompact)
  have hWideCornerBaseCovered (i : Bool) : range (wideCornerBase i) ⊆
      range expandedFirst ∪ range wideOpposite ∪ interior actualWideBaselineCapSet := by
    rintro x ⟨u,rfl⟩
    by_cases hu0 : u=0
    · subst u
      apply Or.inl ∘ Or.inl
      apply hFirstSideInExpanded
      rw [hWideCornerBaseZero]
      cases i
      · exact ⟨0,B.first_zero⟩
      · exact ⟨1,B.first_one⟩
    by_cases hu1 : u=1
    · subst u
      apply Or.inl ∘ Or.inr
      rw [hActualWideOppositeWholeTrace]
      cases i
      · exact Or.inl (Or.inl ⟨1,hWideCornerOuterOne false⟩)
      · exact Or.inr ⟨1,hWideCornerOuterOne true⟩
    · apply Or.inr
      have h0 : 0<u.val := lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm))
      have h1 : u.val<1 := lt_of_le_of_ne u.property.2 (fun he => hu1 (Subtype.ext he))
      exact interior_mono (show range B.disk ∪ cornerSupportEnvelope i ⊆ actualWideBaselineCapSet from
        fun x hx => hx.elim Or.inl (fun hw => Or.inr (Set.mem_iUnion.mpr ⟨i,hw⟩)))
        (hWideCornerBaseSeamInterior i u h0 h1)
  have hWideSecondSideCovered : range B.secondSide ⊆
      range expandedFirst ∪ range wideOpposite ∪ interior actualWideBaselineCapSet := by
    rintro x ⟨u,rfl⟩
    by_cases hl : u ≤ wideCornerCut false
    · apply hWideCornerBaseCovered false
      rw [hWideCornerBaseLiteralTrace]
      refine ⟨u,?_,rfl⟩
      change min 0 (wideCornerCut false) ≤ u ∧ u ≤ max 0 (wideCornerCut false)
      rw [min_eq_left (show 0 ≤ wideCornerCut false from bot_le),
        max_eq_right (show 0 ≤ wideCornerCut false from bot_le)]
      exact ⟨bot_le,hl⟩
    by_cases hr : wideCornerCut true ≤ u
    · apply hWideCornerBaseCovered true
      rw [hWideCornerBaseLiteralTrace]
      refine ⟨u,?_,rfl⟩
      change min 1 (wideCornerCut true) ≤ u ∧ u ≤ max 1 (wideCornerCut true)
      rw [min_eq_right (show wideCornerCut true ≤ 1 from le_top),
        max_eq_left (show wideCornerCut true ≤ 1 from le_top)]
      exact ⟨hr,le_top⟩
    · apply Or.inl ∘ Or.inr
      rw [hActualWideOppositeWholeTrace]
      apply Or.inl ∘ Or.inr
      rw [hWideMiddleRange]
      exact ⟨u,⟨(lt_of_not_ge hl).le,(lt_of_not_ge hr).le⟩,rfl⟩
  have hActualWideBaselineCapFrontier : frontier actualWideBaselineCapSet ⊆
      range expandedFirst ∪ range wideOpposite := by
    intro x hx
    have hNoInterior : x ∉ interior actualWideBaselineCapSet :=
      fun hi => Set.disjoint_left.mp disjoint_interior_frontier hi hx
    have hMembership := hActualWideBaselineCapCompact.isClosed.frontier_subset hx
    rcases hMembership with hd|hw
    · have hdFront : x ∈ frontier (range B.disk) := by
        rw [(isCompact_range B.disk.continuous).isClosed.frontier_eq]
        exact ⟨hd,fun hi => hNoInterior (interior_mono (fun _ hh => Or.inl hh) hi)⟩
      rcases hOriginalDiskFrontier ▸ hdFront with haSide|hbSide
      · exact Or.inl (hFirstSideInExpanded haSide)
      · rcases hWideSecondSideCovered hbSide with (ha|ho)|hi
        · exact Or.inl ha
        · exact Or.inr ho
        · exact False.elim (hNoInterior hi)
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hw
      have hiFront : x ∈ frontier (cornerSupportEnvelope i) := by
        rw [(hCornerSupportCompact i).isClosed.frontier_eq]
        exact ⟨hi,fun hh => hNoInterior (interior_mono
          (fun _ hw => Or.inr (Set.mem_iUnion.mpr ⟨i,hw⟩)) hh)⟩
      rcases hWideCornerEnvelopeFrontier i hiFront with (ha|hg)|ho
      · exact Or.inl ha
      · rcases hWideCornerBaseCovered i hg with (ha|ho)|hi
        · exact Or.inl ha
        · exact Or.inr ho
        · exact False.elim (hNoInterior hi)
      · apply Or.inr
        rw [hActualWideOppositeWholeTrace]
        cases i
        · exact Or.inl (Or.inl ho)
        · exact Or.inr ho
  have hActualWideOppositeInCap : range wideOpposite ⊆ actualWideBaselineCapSet := by
    intro x hx
    rw [hActualWideOppositeWholeTrace] at hx
    rcases hx with (hx|hx)|hx
    · exact Or.inr (Set.mem_iUnion.mpr ⟨false,hWideCornerOuterInEnvelope false hx⟩)
    · exact Or.inl (image_subset_range _ _ (B.boundary_eq.symm ▸
        (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inr (hWideMiddleSide hx))))
    · exact Or.inr (Set.mem_iUnion.mpr ⟨true,hWideCornerOuterInEnvelope true hx⟩)
  have hActualWideBaselineObstacleIncidence : actualWideBaselineCapSet ∩
      ((M.cover.branch : Set S) ∪ expandedK) ⊆ ({cornerA false,cornerA true} : Set S) := by
    rintro x ⟨(hxD|hxW),ho⟩
    · rcases ho with hm|hK
      · exact hActualBaselineCapMarks ⟨Or.inl hxD,hm⟩
      · exact hActualBaselineCapExpandedRemainder ⟨Or.inl hxD,hK⟩
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hxW
      have hp := Set.mem_singleton_iff.mp (hCornerSupportObstacles i ⟨hi,ho⟩)
      cases i
      · exact Or.inl hp
      · exact Or.inr hp
  have hActualCornerSupportFirstSide (i : Bool) :
      cornerSupportEnvelope i ∩ range B.firstSide ⊆ {corner i} := by
    intro x hx
    by_cases hm : corner i ∈ M.cover.branch
    · exact hCornerSupportMarkedA i hm ⟨hx.1,B.first_on_curve hx.2⟩
    · have hT := hCornerSupportUnmarkedA i hm ⟨hx.1,B.first_on_curve hx.2⟩
      have hxD : x ∈ range B.disk := image_subset_range _ _ (B.boundary_eq.symm ▸
        (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inl hx.2))
      have hSecond := hBaselineTriangleContact i ⟨hT,hxD⟩
      have hp : x ∈ ({B.firstCorner,B.secondCorner} : Set S) := B.sides_inter ▸ ⟨hx.2,hSecond⟩
      have hxSep := (hCornerSource i (hCornerSupportSource i hx.1)).2
      cases i
      · rcases hp with he|he
        · exact Set.mem_singleton_iff.mpr he
        · have he1 : x=B.secondCorner := by simpa using he
          exact False.elim (Set.disjoint_left.mp hSepDisjoint hxSep (he1.symm ▸ hInSep1))
      · rcases hp with he|he
        · exact False.elim (Set.disjoint_left.mp hSepDisjoint (he.symm ▸ hInSep0) hxSep)
        · exact Set.mem_singleton_iff.mpr (by simpa [corner] using he)
  have hActualWideFirstSideFrontier (t : Interval) (ht0 : 0<t) (ht1 : t<1) :
      B.firstSide t ∈ frontier actualWideBaselineCapSet := by
    have hNoW : B.firstSide t ∉ ⋃ i : Bool, cornerSupportEnvelope i := by
      intro hw
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hw
      have hp : B.firstSide t=corner i := Set.mem_singleton_iff.mp
        (hActualCornerSupportFirstSide i ⟨hi,Set.mem_range_self t⟩)
      cases i
      · have he : t=0 := B.first_embedded.injective (hp.trans B.first_zero.symm)
        exact (ne_of_gt ht0) he
      · have he : t=1 := B.first_embedded.injective (hp.trans B.first_one.symm)
        exact (ne_of_lt ht1) he
    exact CurveComplex.mem_frontier_union_of_not_mem_closed
      (isCompact_iUnion hCornerSupportCompact).isClosed hNoW
      (hOriginalDiskFrontier.symm ▸ (show B.firstSide t ∈ range B.firstSide ∪ range B.secondSide from
        Or.inl (Set.mem_range_self t)))
  have hActualWideMarkedPortFrontier (i : Bool) (hm : corner i ∈ M.cover.branch) :
      cornerA i ∈ frontier actualWideBaselineCapSet := by
    have hClosed : IsClosed ((B.firstSide) ⁻¹' frontier actualWideBaselineCapSet) :=
      isClosed_frontier.preimage B.firstSide.continuous
    have hSub : Ioo (0:Interval) 1 ⊆ (B.firstSide) ⁻¹' frontier actualWideBaselineCapSet :=
      fun t ht => hActualWideFirstSideFrontier t ht.1 ht.2
    have hClosure : closure (Ioo (0:Interval) 1) ⊆
        (B.firstSide) ⁻¹' frontier actualWideBaselineCapSet := hClosed.closure_subset_iff.mpr hSub
    have h01 : (0:Interval)<1 := by change (0:ℝ)<1; norm_num
    have h0 : B.firstSide 0 ∈ frontier actualWideBaselineCapSet :=
      hClosure (by rw [closure_Ioo (ne_of_lt h01)]; exact ⟨le_rfl,bot_le⟩)
    have h1 : B.firstSide 1 ∈ frontier actualWideBaselineCapSet :=
      hClosure (by rw [closure_Ioo (ne_of_lt h01)]; exact ⟨le_top,le_rfl⟩)
    rw [hCornerAMarked i hm]
    cases i
    · change B.firstCorner ∈ frontier actualWideBaselineCapSet
      exact B.first_zero ▸ h0
    · change B.secondCorner ∈ frontier actualWideBaselineCapSet
      exact B.first_one ▸ h1
  have hActualWideUnmarkedVertexFrontier (i : Bool) (hn : corner i ∉ M.cover.branch) :
      cornerA i ∈ frontier (cornerSupportEnvelope i) := by
    obtain ⟨G,δ,hGS,hδ,hGp,hGA,hGL,hJoint,hBox,hAxis,hBAxis,hTImage,hSharedInterior,hVerticalSelected⟩ :=
      hBaselineTriangleLiteralChart i hn
    rw [(hCornerSupportCompact i).isClosed.frontier_eq]
    refine ⟨by simpa only [hCornerJointStart] using hCornerSupportWholeFamily i 0 0,?_⟩
    intro hi
    let U : Set S := G.source ∩ interior (cornerSupportEnvelope i)
    have hU : IsOpen U := G.open_source.inter isOpen_interior
    have hImageOpen : IsOpen (G '' U) := G.isOpen_image_of_subset_source hU inter_subset_left
    have hAimage : (-δ,0) ∈ G '' U := ⟨cornerA i,⟨hGS.symm ▸ hCornerASource i,hi⟩,hGA⟩
    obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp hImageOpen (-δ,0) hAimage
    have hqBall : (-δ-r/2,(0:ℝ)) ∈ Metric.ball (-δ,0) r := by
      rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      have he : -δ-r/2-(-δ)= -(r/2) := by ring
      rw [he]
      simp only [sub_self,abs_zero,abs_neg,abs_of_pos (half_pos hr),max_eq_left (half_pos hr).le]
      exact half_lt_self hr
    obtain ⟨x,hxU,hxq⟩ := hBall hqBall
    have hxA : x ∈ a.val.image := (hAxis x hxU.1).mpr (by rw [hxq])
    have hxT := hCornerSupportUnmarkedA i hn ⟨interior_subset hxU.2,hxA⟩
    obtain ⟨z,hz,he⟩ := hTImage ▸ hxT
    have hzTarget : z ∈ G.target := by
      have hh := hBox (-z.1) z.2 (by linarith [hz.2.1]) (by linarith [hz.1])
        hz.2.2.1 (by linarith [hz.2.1,hz.2.2.2])
      simpa only [neg_neg] using hh
    have hzCoord : G x=z := by rw [← he,G.right_inv hzTarget]
    have hzX := congrArg Prod.fst (hzCoord.symm.trans hxq)
    change z.1= -δ-r/2 at hzX
    linarith [hz.1]
  have hActualWidePortFrontier (i : Bool) : cornerA i ∈ frontier actualWideBaselineCapSet := by
    by_cases hm : corner i ∈ M.cover.branch
    · exact hActualWideMarkedPortFrontier i hm
    · have hOther : cornerA i ∉ cornerSupportEnvelope (!i) := by
        intro hh
        have ho := (hCornerSource (!i) (hCornerSupportSource (!i) hh)).2
        have hi := (hCornerSource i (hCornerASource i)).2
        cases i
        · exact Set.disjoint_left.mp hSepDisjoint hi ho
        · exact Set.disjoint_left.mp hSepDisjoint ho hi
      have hOffD : cornerA i ∉ range B.disk := by
        intro hd
        have ha : cornerA i ∈ a.val.image := hdecompRaw.symm ▸ Or.inr (hCornerAK i)
        exact hCornerAUnmarked i hm (hDiskA ▸ (show cornerA i ∈ range B.disk ∩ a.val.image from ⟨hd,ha⟩))
      have hDecomp : actualWideBaselineCapSet=cornerSupportEnvelope i ∪
          (range B.disk ∪ cornerSupportEnvelope (!i)) := by
        ext x
        simp only [actualWideBaselineCapSet,Set.mem_union,Set.mem_iUnion]
        cases i <;> constructor
        · rintro (hx|⟨j,hj⟩)
          · exact Or.inr (Or.inl hx)
          · cases j
            · exact Or.inl hj
            · exact Or.inr (Or.inr hj)
        · rintro (hx|hx|hx)
          · exact Or.inr ⟨false,hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨true,hx⟩
        · rintro (hx|⟨j,hj⟩)
          · exact Or.inr (Or.inl hx)
          · cases j
            · exact Or.inr (Or.inr hj)
            · exact Or.inl hj
        · rintro (hx|hx|hx)
          · exact Or.inr ⟨true,hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨false,hx⟩
      rw [hDecomp]
      exact CurveComplex.mem_frontier_union_of_not_mem_closed
        ((isCompact_range B.disk.continuous).isClosed.union (hCornerSupportCompact (!i)).isClosed)
        (fun hh => hh.elim hOffD hOther) (hActualWideUnmarkedVertexFrontier i hm)
  have hActualWideBaselineInteriorClearance : Disjoint (interior actualWideBaselineCapSet)
      ((M.cover.branch : Set S) ∪ expandedK) := by
    apply Set.disjoint_left.mpr
    intro x hx ho
    have hp := hActualWideBaselineObstacleIncidence ⟨interior_subset hx,ho⟩
    rcases hp with he|he
    · exact Set.disjoint_left.mp disjoint_interior_frontier hx (he.symm ▸ hActualWidePortFrontier false)
    · have he1 : x=cornerA true := by simpa using he
      exact Set.disjoint_left.mp disjoint_interior_frontier hx (he1.symm ▸ hActualWidePortFrontier true)
  have hExpandedFirstOnA : range expandedFirst ⊆ a.val.image := by
    intro x hx
    exact hExpandedDecomposition.symm ▸ Or.inl hx
  have hExpandedFirstMarks : range expandedFirst ∩ (M.cover.branch : Set S) ⊆
      ({cornerA leftPort,cornerA rightPort} : Set S) := by
    intro x hx
    obtain ⟨θ,hθ,hθx⟩ := hExpandedFirstRange ▸ hx.1
    have hθ01 : θ ∈ Set.Icc (0:ℝ) 1 := ⟨hExpandedL0.trans hθ.1,hθ.2.trans hExpandedR1⟩
    change a.val.map (Set.projIcc 0 1 zero_le_one θ)=x at hθx
    have hm : a.val.map (Set.projIcc 0 1 zero_le_one θ) ∈ M.cover.branch := by
      rw [hθx]; exact hx.2
    rcases a.val.marked_only_at_ends _ hm with h0|h1
    · have hh := congrArg Subtype.val h0
      rw [Set.projIcc_of_mem zero_le_one hθ01] at hh
      change θ=0 at hh
      have hθL : θ=expandedL := by linarith [hθ.1]
      exact Or.inl (hθx.symm.trans ((congrArg originalγ hθL).trans hExpandedLeft))
    · have hh := congrArg Subtype.val h1
      rw [Set.projIcc_of_mem zero_le_one hθ01] at hh
      change θ=1 at hh
      have hθR : θ=expandedR := by linarith [hθ.2]
      exact Or.inr (hθx.symm.trans ((congrArg originalγ hθR).trans hExpandedRight))
  have hExpandedFirstPunctureFree (x : S) (hx : x ∈ range expandedFirst) : x≠exteriorPuncture := by
    intro he
    have hm := hExpandedFirstMarks ⟨hx,he.symm ▸ hExteriorPunctureMark⟩
    have hImpossible (i : Bool) (hi : x=cornerA i) : False := by
      have hxA : cornerA i ∈ (M.cover.branch : Set S) := hi ▸ (he.symm ▸ hExteriorPunctureMark)
      have hc : cornerA i=corner i := Set.mem_singleton_iff.mp
        (hCornerMarks i ⟨hCornerASource i,hxA⟩)
      have hv : exteriorPuncture=corner i := he.symm.trans (hi.trans hc)
      exact hExteriorPunctureCorner (by cases i <;> simp [hv,corner])
    rcases hm with hl|hr
    · exact hImpossible leftPort hl
    · exact hImpossible rightPort hr
  let capCoordinates := M.puncturedPlane exteriorPuncture
  let expandedPlane : C(Interval,Plane) := ⟨fun t => capCoordinates
      ⟨expandedFirst t,hExpandedFirstPunctureFree _ (Set.mem_range_self t)⟩,
    capCoordinates.continuous.comp (expandedFirst.continuous.subtype_mk _)⟩
  have hExpandedPlaneEmbedded : IsEmbedding expandedPlane :=
    (expandedPlane.continuous.isClosedEmbedding (by
      intro t u he
      exact hExpandedEmbedded.injective (congrArg Subtype.val (capCoordinates.injective he)))).isEmbedding
  obtain ⟨reverseBaselineOpposite,hReverseBaselineOppositeEmbedded,hReverseBaselineOppositeRange,hReverseBaselineOppositeZero,hReverseBaselineOppositeOne⟩ :=
    actual_reverse_embedded_continuous_arc baselineOpposite hBaselineOppositeEmbedded
  let orientedBaselineOpposite : C(Interval,S) := if leftPort then reverseBaselineOpposite else baselineOpposite
  have hOrientedBaselineOppositeRange : range orientedBaselineOpposite=range baselineOpposite := by
    cases leftPort <;> simp [orientedBaselineOpposite,hReverseBaselineOppositeRange]
  have hOrientedBaselineOppositeEmbedded : IsEmbedding orientedBaselineOpposite := by
    cases leftPort <;> simp only [orientedBaselineOpposite,Bool.false_eq_true,if_false,if_true]
    · exact hBaselineOppositeEmbedded
    · exact hReverseBaselineOppositeEmbedded
  have hOrientedBaselineOppositeZero : orientedBaselineOpposite 0=originalγ expandedL := by
    rw [hExpandedLeft]
    cases leftPort <;> simp [orientedBaselineOpposite,hReverseBaselineOppositeZero,hActualBaselineOppositePorts.1,hActualBaselineOppositePorts.2]
  have hOrientedBaselineOppositeOne : orientedBaselineOpposite 1=originalγ expandedR := by
    rw [hExpandedRight]
    cases leftPort <;> cases rightPort
    · exact False.elim (hPortsDifferent rfl)
    · exact hActualBaselineOppositePorts.2
    · exact hReverseBaselineOppositeOne.trans hActualBaselineOppositePorts.1
    · exact False.elim (hPortsDifferent rfl)
  have hExpandedBaselineBoundaryMeet : range expandedFirst ∩ range orientedBaselineOpposite=
      ({originalγ expandedL,originalγ expandedR} : Set S) := by
    rw [hOrientedBaselineOppositeRange]
    ext x
    constructor
    · intro hx
      have hm : x ∈ ({cornerA false,cornerA true} : Set S) :=
        hActualBaselineOppositeAIntersection ▸ (show x ∈ range baselineOpposite ∩ a.val.image from
          ⟨hx.2,hExpandedFirstOnA hx.1⟩)
      rw [hExpandedLeft,hExpandedRight]
      cases leftPort <;> cases rightPort
      · exact False.elim (hPortsDifferent rfl)
      · exact hm
      · simpa only [Set.pair_comm] using hm
      · exact False.elim (hPortsDifferent rfl)
    · rintro (he|he)
      · have hfirst : x ∈ range expandedFirst := ⟨0,hExpandedFirstZero.trans he.symm⟩
        have hround : x ∈ range orientedBaselineOpposite := ⟨0,hOrientedBaselineOppositeZero.trans he.symm⟩
        exact ⟨hfirst,hOrientedBaselineOppositeRange ▸ hround⟩
      · have hfirst : x ∈ range expandedFirst := ⟨1,hExpandedFirstOne.trans he.symm⟩
        have hround : x ∈ range orientedBaselineOpposite := ⟨1,hOrientedBaselineOppositeOne.trans he.symm⟩
        exact ⟨hfirst,hOrientedBaselineOppositeRange ▸ hround⟩
  have hBaselineOppositePunctureFree (x : S) (hx : x ∈ range orientedBaselineOpposite) : x≠exteriorPuncture := by
    intro he
    have hc := hActualBaselineCapMarks ⟨hActualBaselineOppositeInCap (hOrientedBaselineOppositeRange ▸ hx),
      he.symm ▸ hExteriorPunctureMark⟩
    have hImpossible (i : Bool) (hi : x=cornerA i) : False := by
      have hm : cornerA i ∈ M.cover.branch := hi ▸ (he.symm ▸ hExteriorPunctureMark)
      have hh : cornerA i=corner i := Set.mem_singleton_iff.mp (hCornerMarks i ⟨hCornerASource i,hm⟩)
      have hv : exteriorPuncture=corner i := he.symm.trans (hi.trans hh)
      exact hExteriorPunctureCorner (by cases i <;> simp [hv,corner])
    rcases hc with h0|h1
    · exact hImpossible false h0
    · exact hImpossible true (by simpa using h1)
  let baselinePlane : C(Interval,Plane) := ⟨fun t => capCoordinates
      ⟨orientedBaselineOpposite t,hBaselineOppositePunctureFree _ (Set.mem_range_self t)⟩,
    capCoordinates.continuous.comp (orientedBaselineOpposite.continuous.subtype_mk _)⟩
  have hBaselinePlaneEmbedded : IsEmbedding baselinePlane :=
    (baselinePlane.continuous.isClosedEmbedding (by
      intro t u he
      exact hOrientedBaselineOppositeEmbedded.injective (congrArg Subtype.val (capCoordinates.injective he)))).isEmbedding
  have hBaselinePlanePort0 : expandedPlane 0=baselinePlane 0 := by
    apply capCoordinates.injective.eq_iff.mpr
    apply Subtype.ext
    exact hExpandedFirstZero.trans hOrientedBaselineOppositeZero.symm
  have hBaselinePlanePort1 : expandedPlane 1=baselinePlane 1 := by
    apply capCoordinates.injective.eq_iff.mpr
    apply Subtype.ext
    exact hExpandedFirstOne.trans hOrientedBaselineOppositeOne.symm
  have hActualBaselineJordan : IsJordanCurve (range expandedPlane ∪ range baselinePlane) := by
    apply IsJordanCurve.of_two_arcs (hCapEmbeddedSideArc expandedPlane hExpandedPlaneEmbedded)
      (show IsArcBetween (range baselinePlane) (expandedPlane 1) (expandedPlane 0) from
        (by rw [hBaselinePlanePort0,hBaselinePlanePort1]; exact (hCapEmbeddedSideArc baselinePlane hBaselinePlaneEmbedded).reverse))
    rintro z ⟨t,ht⟩ ⟨u,hu⟩
    have he : expandedFirst t=orientedBaselineOpposite u := congrArg Subtype.val
      (capCoordinates.injective (ht.trans hu.symm))
    have hm : expandedFirst t ∈ ({originalγ expandedL,originalγ expandedR} : Set S) :=
      hExpandedBaselineBoundaryMeet ▸ (show expandedFirst t ∈ range expandedFirst ∩ range orientedBaselineOpposite from
        ⟨Set.mem_range_self t,⟨u,he.symm⟩⟩)
    rcases hm with h0|h1
    · have ht0 : t=0 := hExpandedEmbedded.injective (h0.trans hExpandedFirstZero.symm)
      exact Or.inl (ht.symm.trans (congrArg expandedPlane ht0))
    · have ht1 : t=1 := hExpandedEmbedded.injective (h1.trans hExpandedFirstOne.symm)
      exact Or.inr (ht.symm.trans (congrArg expandedPlane ht1))
  have hBaselineCapPunctureFree (x : S) (hx : x ∈ actualBaselineCapSet) : x≠exteriorPuncture := by
    intro he
    have hc := hActualBaselineCapMarks ⟨hx,he.symm ▸ hExteriorPunctureMark⟩
    have hImpossible (i : Bool) (hi : x=cornerA i) : False := by
      have hm : cornerA i ∈ M.cover.branch := hi ▸ (he.symm ▸ hExteriorPunctureMark)
      have hh : cornerA i=corner i := Set.mem_singleton_iff.mp (hCornerMarks i ⟨hCornerASource i,hm⟩)
      have hv : exteriorPuncture=corner i := he.symm.trans (hi.trans hh)
      exact hExteriorPunctureCorner (by cases i <;> simp [hv,corner])
    rcases hc with h0|h1
    · exact hImpossible false h0
    · exact hImpossible true (by simpa using h1)
  let baselinePlaneCap : Set Plane := (M.planeToSphere exteriorPuncture) ⁻¹' actualBaselineCapSet
  have hBaselineCapImage : (M.planeToSphere exteriorPuncture) '' baselinePlaneCap=actualBaselineCapSet := by
    apply Set.image_preimage_eq_of_subset
    intro x hx
    refine ⟨capCoordinates ⟨x,hBaselineCapPunctureFree x hx⟩,?_⟩
    exact congrArg Subtype.val (capCoordinates.symm_apply_apply _)
  have hBaselinePlaneCapCompact : IsCompact baselinePlaneCap :=
    (M.planeToSphere_isOpenEmbedding exteriorPuncture).isEmbedding.isInducing.isCompact_preimage'
      hActualBaselineCapCompact (by
        intro x hx
        exact ⟨capCoordinates ⟨x,hBaselineCapPunctureFree x hx⟩,
          congrArg Subtype.val (capCoordinates.symm_apply_apply _)⟩)
  have hExpandedPlaneBack (t : Interval) : M.planeToSphere exteriorPuncture (expandedPlane t)=expandedFirst t :=
    congrArg Subtype.val (capCoordinates.symm_apply_apply _)
  have hBaselinePlaneBack (t : Interval) : M.planeToSphere exteriorPuncture (baselinePlane t)=orientedBaselineOpposite t :=
    congrArg Subtype.val (capCoordinates.symm_apply_apply _)
  have hBaselinePlaneCapFrontier : frontier baselinePlaneCap ⊆ range expandedPlane ∪ range baselinePlane := by
    intro z hz
    have hh : M.planeToSphere exteriorPuncture z ∈ frontier actualBaselineCapSet := by
      rw [← hBaselineCapImage,← M.planeToSphere_image_frontier_of_compact exteriorPuncture hBaselinePlaneCapCompact]
      exact ⟨z,hz,rfl⟩
    rcases hActualBaselineCapFrontier hh with hf|hb
    · obtain ⟨t,ht⟩ := hf
      exact Or.inl ⟨t,(M.planeToSphere_injective exteriorPuncture) ((hExpandedPlaneBack t).trans ht)⟩
    · obtain ⟨t,ht⟩ := hOrientedBaselineOppositeRange.symm ▸ hb
      exact Or.inr ⟨t,(M.planeToSphere_injective exteriorPuncture) ((hBaselinePlaneBack t).trans ht)⟩
  have hBaselinePlaneCapInteriorNonempty : (interior baselinePlaneCap).Nonempty := by
    let v : Metric.closedBall (0 : Plane) 1 := ⟨0,by simp⟩
    have hv : v.val ∈ Metric.ball (0 : Plane) 1 := by simp [v]
    have hOpen : IsOpen (B.disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) :=
      CurveComplex.embedded_disk_interior_isOpen B.disk B.disk_embedded
    have hiD : B.disk v ∈ interior (range B.disk) :=
      interior_maximal (Set.image_subset_range _ _) hOpen ⟨v,hv,rfl⟩
    have hiK : B.disk v ∈ interior actualBaselineCapSet :=
      interior_mono (show range B.disk ⊆ actualBaselineCapSet from fun _ hh => Or.inl hh) hiD
    rw [← hBaselineCapImage,← M.planeToSphere_image_interior exteriorPuncture baselinePlaneCap] at hiK
    obtain ⟨z,hz,he⟩ := hiK
    exact ⟨z,hz⟩
  have hActualCompactBaselineCapRecognitionOfFrontierSubset
      (K C : Set Plane) (hK : IsCompact K) (hC : IsSeparating C)
      (hfront : frontier K ⊆ C) (hne : (interior K).Nonempty) :
      K=inside C ∪ C := by
    have hclosed : IsClosed K := hK.isClosed
    have hcover (R : Set Plane) (hR : R ⊆ Cᶜ) : R ⊆ interior K ∪ Kᶜ := by
      intro x hx
      by_cases hxK : x ∈ K
      · left
        by_contra hn
        exact hR hx (hfront (hclosed.frontier_eq ▸ ⟨hxK,hn⟩))
      · exact Or.inr hxK
    have houtside : outside C ⊆ Kᶜ := by
      rcases hC.isConnected_outside.isPreconnected.subset_or_subset
        isOpen_interior hclosed.isOpen_compl
        (Set.disjoint_left.mpr (fun x hx hn => hn (interior_subset hx)))
        (hcover _ outside_subset_compl) with h|h
      · exact False.elim (hC.not_isBounded_outside (hK.isBounded.subset (h.trans interior_subset)))
      · exact h
    have hpoint : (interior K ∩ inside C).Nonempty := by
      obtain ⟨p,hp⟩ := hne
      by_cases hpC : p ∈ C
      · have hpcl : p ∈ closure (inside C) :=
          frontier_subset_closure (hC.frontier_inside.symm ▸ hpC)
        exact Set.Nonempty.of_closure ⟨p,isOpen_interior.inter_closure ⟨hp,hpcl⟩⟩
      · rcases (show p ∈ inside C ∪ outside C by rw [inside_union_outside]; exact hpC) with h|h
        · exact ⟨p,hp,h⟩
        · exact False.elim (houtside h (interior_subset hp))
    obtain ⟨p,hp,hpInside⟩ := hpoint
    have hinside : inside C ⊆ interior K := by
      rcases hC.isConnected_inside.isPreconnected.subset_or_subset
        isOpen_interior hclosed.isOpen_compl
        (Set.disjoint_left.mpr (fun x hx hn => hn (interior_subset hx)))
        (hcover _ inside_subset_compl) with h|h
      · exact h
      · exact False.elim (h hpInside (interior_subset hp))
    ext x
    constructor
    · intro hx
      by_cases hxC : x ∈ C
      · exact Or.inr hxC
      · rcases (show x ∈ inside C ∪ outside C by rw [inside_union_outside]; exact hxC) with h|h
        · exact Or.inl h
        · exact False.elim (houtside h hx)
    · rintro (h|h)
      · exact interior_subset (hinside h)
      · have hh : x ∈ closure (inside C) := frontier_subset_closure (hC.frontier_inside.symm ▸ h)
        exact hclosed.closure_eq ▸ closure_mono (hinside.trans interior_subset) hh
  have hActualBaselineClosedJordanCap : baselinePlaneCap=
      inside (range expandedPlane ∪ range baselinePlane) ∪ (range expandedPlane ∪ range baselinePlane) :=
    hActualCompactBaselineCapRecognitionOfFrontierSubset baselinePlaneCap _ hBaselinePlaneCapCompact
      (Schoenflies.jordan_curve_theorem hActualBaselineJordan) hBaselinePlaneCapFrontier hBaselinePlaneCapInteriorNonempty
  have hActualWideCapMarks : actualWideBaselineCapSet ∩ (M.cover.branch : Set S) ⊆
      ({cornerA false,cornerA true} : Set S) := by
    intro x hx
    exact hActualWideBaselineObstacleIncidence ⟨hx.1,Or.inl hx.2⟩
  obtain ⟨reverseWideOpposite,hReverseWideOppositeEmbedded,hReverseWideOppositeRange,hReverseWideOppositeZero,hReverseWideOppositeOne⟩ :=
    actual_reverse_embedded_continuous_arc wideOpposite hWideOppositeEmbedded
  let orientedWideOpposite : C(Interval,S) := if leftPort then reverseWideOpposite else wideOpposite
  have hOrientedWideOppositeRange : range orientedWideOpposite=range wideOpposite := by
    cases leftPort <;> simp [orientedWideOpposite,hReverseWideOppositeRange]
  have hOrientedWideOppositeEmbedded : IsEmbedding orientedWideOpposite := by
    cases leftPort <;> simp only [orientedWideOpposite,Bool.false_eq_true,if_false,if_true]
    · exact hWideOppositeEmbedded
    · exact hReverseWideOppositeEmbedded
  have hOrientedWideOppositeZero : orientedWideOpposite 0=originalγ expandedL := by
    rw [hExpandedLeft]
    cases leftPort <;> simp [orientedWideOpposite,hReverseWideOppositeZero,hActualWideOppositePorts.1,hActualWideOppositePorts.2]
  have hOrientedWideOppositeOne : orientedWideOpposite 1=originalγ expandedR := by
    rw [hExpandedRight]
    cases leftPort <;> cases rightPort
    · exact False.elim (hPortsDifferent rfl)
    · exact hActualWideOppositePorts.2
    · exact hReverseWideOppositeOne.trans hActualWideOppositePorts.1
    · exact False.elim (hPortsDifferent rfl)
  have hExpandedWideBoundaryMeet : range expandedFirst ∩ range orientedWideOpposite=
      ({originalγ expandedL,originalγ expandedR} : Set S) := by
    rw [hOrientedWideOppositeRange]
    ext x
    constructor
    · intro hx
      have hm : x ∈ ({cornerA false,cornerA true} : Set S) :=
        hActualWideOppositeAIntersection ▸ (show x ∈ range wideOpposite ∩ a.val.image from
          ⟨hx.2,hExpandedFirstOnA hx.1⟩)
      rw [hExpandedLeft,hExpandedRight]
      cases leftPort <;> cases rightPort
      · exact False.elim (hPortsDifferent rfl)
      · exact hm
      · simpa only [Set.pair_comm] using hm
      · exact False.elim (hPortsDifferent rfl)
    · rintro (he|he)
      · have hfirst : x ∈ range expandedFirst := ⟨0,hExpandedFirstZero.trans he.symm⟩
        have hround : x ∈ range orientedWideOpposite := ⟨0,hOrientedWideOppositeZero.trans he.symm⟩
        exact ⟨hfirst,hOrientedWideOppositeRange ▸ hround⟩
      · have hfirst : x ∈ range expandedFirst := ⟨1,hExpandedFirstOne.trans he.symm⟩
        have hround : x ∈ range orientedWideOpposite := ⟨1,hOrientedWideOppositeOne.trans he.symm⟩
        exact ⟨hfirst,hOrientedWideOppositeRange ▸ hround⟩
  have hWideOppositePunctureFree (x : S) (hx : x ∈ range orientedWideOpposite) : x≠exteriorPuncture := by
    intro he
    have hc := hActualWideCapMarks ⟨hActualWideOppositeInCap (hOrientedWideOppositeRange ▸ hx),
      he.symm ▸ hExteriorPunctureMark⟩
    have hImpossible (i : Bool) (hi : x=cornerA i) : False := by
      have hm : cornerA i ∈ M.cover.branch := hi ▸ (he.symm ▸ hExteriorPunctureMark)
      have hh : cornerA i=corner i := Set.mem_singleton_iff.mp (hCornerMarks i ⟨hCornerASource i,hm⟩)
      have hv : exteriorPuncture=corner i := he.symm.trans (hi.trans hh)
      exact hExteriorPunctureCorner (by cases i <;> simp [hv,corner])
    rcases hc with h0|h1
    · exact hImpossible false h0
    · exact hImpossible true (by simpa using h1)
  let wideBaselinePlane : C(Interval,Plane) := ⟨fun t => capCoordinates
      ⟨orientedWideOpposite t,hWideOppositePunctureFree _ (Set.mem_range_self t)⟩,
    capCoordinates.continuous.comp (orientedWideOpposite.continuous.subtype_mk _)⟩
  have hWideBaselinePlaneEmbedded : IsEmbedding wideBaselinePlane :=
    (wideBaselinePlane.continuous.isClosedEmbedding (by
      intro t u he
      exact hOrientedWideOppositeEmbedded.injective (congrArg Subtype.val (capCoordinates.injective he)))).isEmbedding
  have hWideBaselinePlanePort0 : expandedPlane 0=wideBaselinePlane 0 := by
    apply capCoordinates.injective.eq_iff.mpr
    apply Subtype.ext
    exact hExpandedFirstZero.trans hOrientedWideOppositeZero.symm
  have hWideBaselinePlanePort1 : expandedPlane 1=wideBaselinePlane 1 := by
    apply capCoordinates.injective.eq_iff.mpr
    apply Subtype.ext
    exact hExpandedFirstOne.trans hOrientedWideOppositeOne.symm
  have hActualWideJordan : IsJordanCurve (range expandedPlane ∪ range wideBaselinePlane) := by
    apply IsJordanCurve.of_two_arcs (hCapEmbeddedSideArc expandedPlane hExpandedPlaneEmbedded)
      (show IsArcBetween (range wideBaselinePlane) (expandedPlane 1) (expandedPlane 0) from
        (by rw [hWideBaselinePlanePort0,hWideBaselinePlanePort1]; exact (hCapEmbeddedSideArc wideBaselinePlane hWideBaselinePlaneEmbedded).reverse))
    rintro z ⟨t,ht⟩ ⟨u,hu⟩
    have he : expandedFirst t=orientedWideOpposite u := congrArg Subtype.val
      (capCoordinates.injective (ht.trans hu.symm))
    have hm : expandedFirst t ∈ ({originalγ expandedL,originalγ expandedR} : Set S) :=
      hExpandedWideBoundaryMeet ▸ (show expandedFirst t ∈ range expandedFirst ∩ range orientedWideOpposite from
        ⟨Set.mem_range_self t,⟨u,he.symm⟩⟩)
    rcases hm with h0|h1
    · have ht0 : t=0 := hExpandedEmbedded.injective (h0.trans hExpandedFirstZero.symm)
      exact Or.inl (ht.symm.trans (congrArg expandedPlane ht0))
    · have ht1 : t=1 := hExpandedEmbedded.injective (h1.trans hExpandedFirstOne.symm)
      exact Or.inr (ht.symm.trans (congrArg expandedPlane ht1))
  have hWideCapPunctureFree (x : S) (hx : x ∈ actualWideBaselineCapSet) : x≠exteriorPuncture := by
    intro he
    have hc := hActualWideCapMarks ⟨hx,he.symm ▸ hExteriorPunctureMark⟩
    have hImpossible (i : Bool) (hi : x=cornerA i) : False := by
      have hm : cornerA i ∈ M.cover.branch := hi ▸ (he.symm ▸ hExteriorPunctureMark)
      have hh : cornerA i=corner i := Set.mem_singleton_iff.mp (hCornerMarks i ⟨hCornerASource i,hm⟩)
      have hv : exteriorPuncture=corner i := he.symm.trans (hi.trans hh)
      exact hExteriorPunctureCorner (by cases i <;> simp [hv,corner])
    rcases hc with h0|h1
    · exact hImpossible false h0
    · exact hImpossible true (by simpa using h1)
  let wideBaselinePlaneCap : Set Plane := (M.planeToSphere exteriorPuncture) ⁻¹' actualWideBaselineCapSet
  have hWideCapImage : (M.planeToSphere exteriorPuncture) '' wideBaselinePlaneCap=actualWideBaselineCapSet := by
    apply Set.image_preimage_eq_of_subset
    intro x hx
    refine ⟨capCoordinates ⟨x,hWideCapPunctureFree x hx⟩,?_⟩
    exact congrArg Subtype.val (capCoordinates.symm_apply_apply _)
  have hWideBaselinePlaneCapCompact : IsCompact wideBaselinePlaneCap :=
    (M.planeToSphere_isOpenEmbedding exteriorPuncture).isEmbedding.isInducing.isCompact_preimage'
      hActualWideBaselineCapCompact (by
        intro x hx
        exact ⟨capCoordinates ⟨x,hWideCapPunctureFree x hx⟩,
          congrArg Subtype.val (capCoordinates.symm_apply_apply _)⟩)
  have hWideBaselinePlaneBack (t : Interval) : M.planeToSphere exteriorPuncture (wideBaselinePlane t)=orientedWideOpposite t :=
    congrArg Subtype.val (capCoordinates.symm_apply_apply _)
  have hWideBaselinePlaneCapFrontier : frontier wideBaselinePlaneCap ⊆ range expandedPlane ∪ range wideBaselinePlane := by
    intro z hz
    have hh : M.planeToSphere exteriorPuncture z ∈ frontier actualWideBaselineCapSet := by
      rw [← hWideCapImage,← M.planeToSphere_image_frontier_of_compact exteriorPuncture hWideBaselinePlaneCapCompact]
      exact ⟨z,hz,rfl⟩
    rcases hActualWideBaselineCapFrontier hh with hf|hb
    · obtain ⟨t,ht⟩ := hf
      exact Or.inl ⟨t,(M.planeToSphere_injective exteriorPuncture) ((hExpandedPlaneBack t).trans ht)⟩
    · obtain ⟨t,ht⟩ := hOrientedWideOppositeRange.symm ▸ hb
      exact Or.inr ⟨t,(M.planeToSphere_injective exteriorPuncture) ((hWideBaselinePlaneBack t).trans ht)⟩
  have hWideBaselinePlaneCapInteriorNonempty : (interior wideBaselinePlaneCap).Nonempty := by
    let v : Metric.closedBall (0 : Plane) 1 := ⟨0,by simp⟩
    have hv : v.val ∈ Metric.ball (0 : Plane) 1 := by simp [v]
    have hOpen : IsOpen (B.disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) :=
      CurveComplex.embedded_disk_interior_isOpen B.disk B.disk_embedded
    have hiD : B.disk v ∈ interior (range B.disk) :=
      interior_maximal (Set.image_subset_range _ _) hOpen ⟨v,hv,rfl⟩
    have hiK : B.disk v ∈ interior actualWideBaselineCapSet :=
      interior_mono (show range B.disk ⊆ actualWideBaselineCapSet from fun _ hh => Or.inl hh) hiD
    rw [← hWideCapImage,← M.planeToSphere_image_interior exteriorPuncture wideBaselinePlaneCap] at hiK
    obtain ⟨z,hz,he⟩ := hiK
    exact ⟨z,hz⟩
  have hActualWideClosedJordanCap : wideBaselinePlaneCap=
      inside (range expandedPlane ∪ range wideBaselinePlane) ∪ (range expandedPlane ∪ range wideBaselinePlane) :=
    hActualCompactBaselineCapRecognitionOfFrontierSubset wideBaselinePlaneCap _ hWideBaselinePlaneCapCompact
      (Schoenflies.jordan_curve_theorem hActualWideJordan) hWideBaselinePlaneCapFrontier hWideBaselinePlaneCapInteriorNonempty
  have hActualJordanClosedDiskProducer (C : Set Plane) (hC : IsJordanCurve C) :
      ∃ d : C(Metric.closedBall (0 : Plane) 1,Plane), IsEmbedding d ∧
        d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=C := by
    classical
    obtain ⟨square,hSquare,hBoundary⟩ := exists_embedded_square_disc_of_jordan hC
    obtain ⟨h,hi,hcl,hfront⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (Plane.convex_closedSquare 0 1)
      (by rw [Plane.interior_closedSquare]; exact ⟨0,by simp [Plane.openSquare,Plane.supNorm]⟩)
      (Plane.isBounded_closedSquare 0 1)
    have hcl' : h '' Plane.closedSquare 0 1 = Metric.closedBall (0 : Plane) 1 := by
      simpa only [(Plane.isClosed_closedSquare 0 1).closure_eq] using hcl
    have hfront' : h '' Schoenflies.modelCurve = Metric.sphere (0 : Plane) 1 := by
      simpa only [← Schoenflies.modelCurve_eq_frontier] using hfront
    let e : Plane.closedSquare 0 1 ≃ₜ Metric.closedBall (0 : Plane) 1 :=
      (h.image (Plane.closedSquare 0 1)).trans (Homeomorph.setCongr hcl')
    have he (x : Plane.closedSquare 0 1) : (e x).val = h x.val := rfl
    have heB : e.symm '' {x : Metric.closedBall (0 : Plane) 1 | x.val ∈ Metric.sphere (0 : Plane) 1} =
        {x : Plane.closedSquare 0 1 | x.val ∈ Schoenflies.modelCurve} := by
      ext x
      constructor
      · rintro ⟨y,hy,hxy⟩
        have hy' : (e x).val ∈ Metric.sphere (0 : Plane) 1 := by
          rw [←hxy,e.apply_symm_apply]; exact hy
        rw [he,←hfront'] at hy'
        obtain ⟨z,hz,hzx⟩ := hy'
        change x.val ∈ Schoenflies.modelCurve
        rw [←h.injective hzx]
        exact hz
      · intro hx
        refine ⟨e x,?_,e.symm_apply_apply x⟩
        change (e x).val ∈ Metric.sphere (0 : Plane) 1
        rw [he,←hfront']
        exact Set.mem_image_of_mem h hx
    let d : C(Metric.closedBall (0 : Plane) 1,Plane) :=
      ⟨fun x => square (e.symm x),square.continuous.comp e.symm.continuous⟩
    have hd : Topology.IsEmbedding d := hSquare.comp e.symm.isEmbedding
    have hdB : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = C := by
      change (square ∘ e.symm) '' _ = C
      rw [Set.image_comp,heB]
      exact hBoundary
    exact ⟨d,hd,hdB⟩
  obtain ⟨actualBaselinePlaneDisk,hActualBaselinePlaneDiskEmbedded,hActualBaselinePlaneDiskBoundary⟩ :=
    hActualJordanClosedDiskProducer (range expandedPlane ∪ range baselinePlane) hActualBaselineJordan
  have hActualBaselinePlaneDiskInteriorNonempty : (interior (range actualBaselinePlaneDisk)).Nonempty := by
    let v : Metric.closedBall (0 : Plane) 1 := ⟨0,by simp⟩
    have hv : v.val ∈ Metric.ball (0 : Plane) 1 := by simp [v]
    have hOpen : IsOpen (actualBaselinePlaneDisk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) :=
      CurveComplex.embedded_disk_interior_isOpen actualBaselinePlaneDisk hActualBaselinePlaneDiskEmbedded
    exact ⟨actualBaselinePlaneDisk v,interior_maximal (Set.image_subset_range _ _) hOpen ⟨v,hv,rfl⟩⟩
  have hActualBaselinePlaneDiskRange : range actualBaselinePlaneDisk=baselinePlaneCap := by
    have hFront : frontier (range actualBaselinePlaneDisk) ⊆ range expandedPlane ∪ range baselinePlane := by
      rw [← hActualBaselinePlaneDiskBoundary]
      exact CurveComplex.embedded_disk_frontier_subset_boundary actualBaselinePlaneDisk hActualBaselinePlaneDiskEmbedded
    have hRecognized := hActualCompactBaselineCapRecognitionOfFrontierSubset
      (range actualBaselinePlaneDisk) (range expandedPlane ∪ range baselinePlane)
      (isCompact_range actualBaselinePlaneDisk.continuous) (Schoenflies.jordan_curve_theorem hActualBaselineJordan)
      hFront hActualBaselinePlaneDiskInteriorNonempty
    exact hRecognized.trans hActualBaselineClosedJordanCap.symm
  let actualBaselineCap : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨M.planeToSphere exteriorPuncture ∘ actualBaselinePlaneDisk,
      (M.planeToSphere_isOpenEmbedding exteriorPuncture).continuous.comp actualBaselinePlaneDisk.continuous⟩
  have hActualBaselineCapEmbedded : IsEmbedding actualBaselineCap :=
    (M.planeToSphere_isOpenEmbedding exteriorPuncture).isEmbedding.comp hActualBaselinePlaneDiskEmbedded
  have hActualBaselineCapRange : range actualBaselineCap=actualBaselineCapSet := by
    change range (M.planeToSphere exteriorPuncture ∘ actualBaselinePlaneDisk)=actualBaselineCapSet
    rw [Set.range_comp,hActualBaselinePlaneDiskRange,hBaselineCapImage]
  have hActualBaselineCapInteriorClearance : Disjoint
      (actualBaselineCap '' {x | x.val ∈ Metric.ball (0 : Plane) 1})
      ((M.cover.branch : Set S) ∪ expandedK) := by
    apply hActualBaselineInteriorClearance.mono_left
    rw [← hActualBaselineCapRange]
    exact interior_maximal (Set.image_subset_range _ _)
      (CurveComplex.embedded_disk_interior_isOpen actualBaselineCap hActualBaselineCapEmbedded)
  obtain ⟨actualWidePlaneDisk,hActualWidePlaneDiskEmbedded,hActualWidePlaneDiskBoundary⟩ :=
    hActualJordanClosedDiskProducer (range expandedPlane ∪ range wideBaselinePlane) hActualWideJordan
  have hActualWidePlaneDiskInteriorNonempty : (interior (range actualWidePlaneDisk)).Nonempty := by
    let v : Metric.closedBall (0 : Plane) 1 := ⟨0,by simp⟩
    have hv : v.val ∈ Metric.ball (0 : Plane) 1 := by simp [v]
    have hOpen : IsOpen (actualWidePlaneDisk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) :=
      CurveComplex.embedded_disk_interior_isOpen actualWidePlaneDisk hActualWidePlaneDiskEmbedded
    exact ⟨actualWidePlaneDisk v,interior_maximal (Set.image_subset_range _ _) hOpen ⟨v,hv,rfl⟩⟩
  have hActualWidePlaneDiskRange : range actualWidePlaneDisk=wideBaselinePlaneCap := by
    have hFront : frontier (range actualWidePlaneDisk) ⊆ range expandedPlane ∪ range wideBaselinePlane := by
      rw [← hActualWidePlaneDiskBoundary]
      exact CurveComplex.embedded_disk_frontier_subset_boundary actualWidePlaneDisk hActualWidePlaneDiskEmbedded
    have hRecognized := hActualCompactBaselineCapRecognitionOfFrontierSubset
      (range actualWidePlaneDisk) (range expandedPlane ∪ range wideBaselinePlane)
      (isCompact_range actualWidePlaneDisk.continuous) (Schoenflies.jordan_curve_theorem hActualWideJordan)
      hFront hActualWidePlaneDiskInteriorNonempty
    exact hRecognized.trans hActualWideClosedJordanCap.symm
  let actualWideCap : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨M.planeToSphere exteriorPuncture ∘ actualWidePlaneDisk,
      (M.planeToSphere_isOpenEmbedding exteriorPuncture).continuous.comp actualWidePlaneDisk.continuous⟩
  have hActualWideCapEmbedded : IsEmbedding actualWideCap :=
    (M.planeToSphere_isOpenEmbedding exteriorPuncture).isEmbedding.comp hActualWidePlaneDiskEmbedded
  have hActualWideCapRange : range actualWideCap=actualWideBaselineCapSet := by
    change range (M.planeToSphere exteriorPuncture ∘ actualWidePlaneDisk)=actualWideBaselineCapSet
    rw [Set.range_comp,hActualWidePlaneDiskRange,hWideCapImage]
  have hActualWideCapInteriorClearance : Disjoint
      (actualWideCap '' {x | x.val ∈ Metric.ball (0 : Plane) 1})
      ((M.cover.branch : Set S) ∪ expandedK) := by
    apply hActualWideBaselineInteriorClearance.mono_left
    rw [← hActualWideCapRange]
    exact interior_maximal (Set.image_subset_range _ _)
      (CurveComplex.embedded_disk_interior_isOpen actualWideCap hActualWideCapEmbedded)
  have hExpandedPlaneBack (t : Interval) :
      M.planeToSphere exteriorPuncture (expandedPlane t)=expandedFirst t :=
    congrArg Subtype.val (capCoordinates.symm_apply_apply _)
  let actualWidePlaneObstacle : Set Plane := (M.planeToSphere exteriorPuncture) ⁻¹'
    ((M.cover.branch : Set S) ∪ expandedK)
  have hActualWidePlaneObstacleClosed : IsClosed actualWidePlaneObstacle :=
    (M.cover.branch.finite_toSet.isClosed.union hExpandedKCompact.isClosed).preimage
      (M.planeToSphere_isOpenEmbedding exteriorPuncture).continuous
  have hActualWidePlaneObstaclePort0 : expandedPlane 0 ∈ actualWidePlaneObstacle := by
    change M.planeToSphere exteriorPuncture (expandedPlane 0) ∈ (M.cover.branch : Set S) ∪ expandedK
    rw [hExpandedPlaneBack,hExpandedFirstZero]
    exact Or.inr ((hExpandedMeet.symm ▸ (show originalγ expandedL ∈
      ({originalγ expandedL,originalγ expandedR} : Set S) from Or.inl rfl)).2)
  have hActualWidePlaneObstaclePort1 : expandedPlane 1 ∈ actualWidePlaneObstacle := by
    change M.planeToSphere exteriorPuncture (expandedPlane 1) ∈ (M.cover.branch : Set S) ∪ expandedK
    rw [hExpandedPlaneBack,hExpandedFirstOne]
    exact Or.inr ((hExpandedMeet.symm ▸ (show originalγ expandedR ∈
      ({originalγ expandedL,originalγ expandedR} : Set S) from Or.inr rfl)).2)
  have hActualWidePlaneObstacleBoundary : ∀ z ∈ actualWidePlaneObstacle,
      z ∈ range expandedPlane ∪ range wideBaselinePlane → z=expandedPlane 0 ∨ z=expandedPlane 1 := by
    intro z hz hc
    have hs : M.planeToSphere exteriorPuncture z ∈ actualWideBaselineCapSet := by
      have hzK : z ∈ wideBaselinePlaneCap := hActualWideClosedJordanCap.symm ▸ Or.inr hc
      exact hzK
    have hp := hActualWideBaselineObstacleIncidence ⟨hs,hz⟩
    have hports : M.planeToSphere exteriorPuncture z ∈
        ({originalγ expandedL,originalγ expandedR} : Set S) := by
      rw [hExpandedLeft,hExpandedRight]
      cases leftPort <;> cases rightPort
      · exact False.elim (hPortsDifferent rfl)
      · exact hp
      · simpa only [Set.pair_comm] using hp
      · exact False.elim (hPortsDifferent rfl)
    rcases hports with h0|h1
    · exact Or.inl ((M.planeToSphere_injective exteriorPuncture)
        (h0.trans (hExpandedFirstZero.symm.trans (hExpandedPlaneBack 0).symm)))
    · have h1' : M.planeToSphere exteriorPuncture z=originalγ expandedR := by simpa using h1
      exact Or.inr ((M.planeToSphere_injective exteriorPuncture)
        (h1'.trans (hExpandedFirstOne.symm.trans (hExpandedPlaneBack 1).symm)))
  have hActualWidePlaneInsideClearance : Disjoint
      (inside (range expandedPlane ∪ range wideBaselinePlane)) actualWidePlaneObstacle := by
    apply Set.disjoint_left.mpr
    intro z hz ho
    have hOpen : IsOpen ((M.planeToSphere exteriorPuncture) ''
        inside (range expandedPlane ∪ range wideBaselinePlane)) :=
      (M.planeToSphere_isOpenEmbedding exteriorPuncture).isOpenMap _
        (jordan_curve_theorem hActualWideJordan).isOpen_inside
    have hSub : (M.planeToSphere exteriorPuncture) ''
        inside (range expandedPlane ∪ range wideBaselinePlane) ⊆ actualWideBaselineCapSet := by
      rintro x ⟨w,hw,rfl⟩
      have hwK : w ∈ wideBaselinePlaneCap := hActualWideClosedJordanCap.symm ▸ Or.inl hw
      exact hwK
    exact Set.disjoint_left.mp hActualWideBaselineInteriorClearance
      (interior_maximal hSub hOpen ⟨z,hz,rfl⟩) ho
  obtain ⟨widePlaneSupport,hWidePlaneSupportOpen,hWidePlaneSupportFree,
    hWidePlaneSupportContains,wideSupportHomeomorph,hWidePlaneSupportImage⟩ :=
    actual_jordan_relative_open_enclosure (range expandedPlane) (range wideBaselinePlane)
      (expandedPlane 0) (expandedPlane 1)
      (hCapEmbeddedSideArc expandedPlane hExpandedPlaneEmbedded)
      (by rw [hWideBaselinePlanePort0,hWideBaselinePlanePort1];
          exact hCapEmbeddedSideArc wideBaselinePlane hWideBaselinePlaneEmbedded)
      hActualWideJordan actualWidePlaneObstacle hActualWidePlaneObstacleClosed
      hActualWidePlaneObstaclePort0 hActualWidePlaneObstaclePort1
      hActualWidePlaneObstacleBoundary hActualWidePlaneInsideClearance
  let actualWideSupport : Set S := (M.planeToSphere exteriorPuncture) '' widePlaneSupport
  have hActualWideSupportOpen : IsOpen actualWideSupport :=
    (M.planeToSphere_isOpenEmbedding exteriorPuncture).isOpenMap _ hWidePlaneSupportOpen
  have hActualWideSupportFree : Disjoint actualWideSupport ((M.cover.branch : Set S) ∪ expandedK) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hx
    exact Set.disjoint_left.mp hWidePlaneSupportFree hz hx
  have hActualWideCapExceptPortsSupport : actualWideBaselineCapSet \
      ({originalγ expandedL,originalγ expandedR} : Set S) ⊆ actualWideSupport := by
    rintro x ⟨hx,hn⟩
    let z : Plane := capCoordinates ⟨x,hWideCapPunctureFree x hx⟩
    have hzback : M.planeToSphere exteriorPuncture z=x :=
      congrArg Subtype.val (capCoordinates.symm_apply_apply _)
    have hzK : z ∈ wideBaselinePlaneCap := by
      change M.planeToSphere exteriorPuncture z ∈ actualWideBaselineCapSet
      rw [hzback]
      exact hx
    refine ⟨z,hWidePlaneSupportContains ⟨hActualWideClosedJordanCap ▸ hzK,?_⟩,hzback⟩
    rintro (he|he)
    · exact hn (Or.inl (hzback.symm.trans
        ((congrArg (M.planeToSphere exteriorPuncture) he).trans
          ((hExpandedPlaneBack 0).trans hExpandedFirstZero))))
    · have he1 : z=expandedPlane 1 := by simpa using he
      exact hn (Or.inr (hzback.symm.trans
        ((congrArg (M.planeToSphere exteriorPuncture) he1).trans
          ((hExpandedPlaneBack 1).trans hExpandedFirstOne))))
  have hActualWideCornerFamilySupport (i : Bool) (t u : Interval) (hu : 0<u.val) :
      cornerH i (t,u) ∈ actualWideSupport := by
    apply hActualWideCapExceptPortsSupport
    refine ⟨Or.inr (Set.mem_iUnion.mpr ⟨i,hCornerSupportWholeFamily i t u⟩),?_⟩
    have hAi : cornerH i (t,u) ≠ cornerA i := by
      intro he
      have hu0 := (hCornerJointEmbedded i t).injective (he.trans (hCornerJointStart i t).symm)
      have hh := congrArg Subtype.val hu0
      change u.val=0 at hh
      linarith
    have hOther : cornerH i (t,u) ≠ cornerA (!i) := by
      intro he
      have hs := (hCornerSource i (hCornerJointSource i t u)).2
      have ho := (hCornerSource (!i) (hCornerASource (!i))).2
      cases i
      · exact Set.disjoint_left.mp hSepDisjoint hs (he.symm ▸ ho)
      · exact Set.disjoint_left.mp hSepDisjoint (he.symm ▸ ho) hs
    have hBoth : cornerH i (t,u) ∉ ({cornerA false,cornerA true} : Set S) := by
      cases i
      · rintro (he|he)
        · exact hAi he
        · exact hOther (by simpa using he)
      · rintro (he|he)
        · exact hOther he
        · exact hAi (by simpa using he)
    rw [hExpandedLeft,hExpandedRight]
    cases leftPort <;> cases rightPort
    · exact False.elim (hPortsDifferent rfl)
    · exact hBoth
    · simpa only [Set.pair_comm] using hBoth
    · exact False.elim (hPortsDifferent rfl)
  have hActualWideSecondInteriorSupport (v : Interval) (hv0 : 0<v.val) (hv1 : v.val<1) :
      B.secondSide v ∈ actualWideSupport := by
    apply hActualWideCapExceptPortsSupport
    refine ⟨Or.inl (image_subset_range _ _ (B.boundary_eq.symm ▸
      (show B.secondSide v ∈ range B.firstSide ∪ range B.secondSide from Or.inr (Set.mem_range_self v)))),?_⟩
    have hNotA : B.secondSide v ∉ a.val.image := by
      intro haV
      have hc := hsecondclean ▸ (show B.secondSide v ∈ range B.secondSide ∩ a.val.image from
        ⟨Set.mem_range_self v,haV⟩)
      rcases hc with he|he
      · have hh := congrArg Subtype.val (B.second_embedded.injective (he.trans B.second_zero.symm))
        change v.val=0 at hh
        linarith
      · have he1 : B.secondSide v=B.secondCorner := by simpa using he
        have hh := congrArg Subtype.val (B.second_embedded.injective (he1.trans B.second_one.symm))
        change v.val=1 at hh
        linarith
    rintro (he|he)
    · exact hNotA (he.symm ▸ hExpandedFirstOnA ⟨0,hExpandedFirstZero⟩)
    · have he1 : B.secondSide v=originalγ expandedR := by simpa using he
      exact hNotA (he1.symm ▸ hExpandedFirstOnA ⟨1,hExpandedFirstOne⟩)
  have hActualBankAxisSupport (x : S) (hxS : x ∈ Ebank.source) (hSide : x ∈ range B.secondSide) :
      x ∈ actualWideSupport := by
    apply hActualWideCapExceptPortsSupport
    refine ⟨Or.inl (image_subset_range _ _ (B.boundary_eq.symm ▸
      (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inr hSide))),?_⟩
    rintro (he|he)
    · exact Set.disjoint_left.mp hEbankOffA hxS (he.symm ▸ hExpandedFirstOnA ⟨0,hExpandedFirstZero⟩)
    · have he1 : x=originalγ expandedR := by simpa using he
      exact Set.disjoint_left.mp hEbankOffA hxS (he1.symm ▸ hExpandedFirstOnA ⟨1,hExpandedFirstOne⟩)
  let jointPatchCoordinate (p : P) (z : Interval × Interval) : Plane :=
    AffineMap.lineMap (Plane.mk (-bankPatchδ p) ((bankPatchH p/2)*z.1.val))
      (Plane.mk (bankPatchδ p) ((bankPatchH p/2)*z.1.val)) z.2.val
  have hJointPatchTarget (p : P) (z : Interval × Interval) :
      jointPatchCoordinate p z ∈ (bankPatchF p).target := by
    have hs : jointPatchCoordinate p z ∈ segment ℝ
      (Plane.mk (-bankPatchδ p) ((bankPatchH p/2)*z.1.val))
      (Plane.mk (bankPatchδ p) ((bankPatchH p/2)*z.1.val)) :=
      lineMap_mem_segment ℝ _ _ z.2.property
    by_cases ht : z.1.val=0
    · have hc : jointPatchCoordinate p z=Plane.mk
          (-bankPatchδ p+z.2.val*(2*bankPatchδ p)) 0 := by
        ext i
        fin_cases i <;> simp [jointPatchCoordinate,AffineMap.lineMap_apply,ht] <;> ring
      rw [hc]
      apply hBankPatchWholeAxis
      constructor <;> nlinarith [z.2.property.1,z.2.property.2,hBankPatchδ p]
    · have htpos : 0<z.1.val := lt_of_le_of_ne z.1.property.1 (Ne.symm ht)
      exact hBankPatchSegments p _ (mul_pos (half_pos (hBankPatchH p)) htpos)
        (by nlinarith [z.1.property.2,hBankPatchH p]) hs
  let jointPatchFamily (p : P) : Interval × Interval → S :=
    fun z => (bankPatchF p).symm (jointPatchCoordinate p z)
  have hJointPatchContinuous (p : P) : Continuous (jointPatchFamily p) :=
    (bankPatchF p).symm.continuousOn.comp_continuous
      (by dsimp [jointPatchCoordinate]; fun_prop) (hJointPatchTarget p)
  have hJointPatchBaselineSupport (p : P) (u : Interval) : jointPatchFamily p (0,u) ∈ actualWideSupport := by
    have hc : jointPatchCoordinate p (0,u)=Plane.mk (-bankPatchδ p+u.val*(2*bankPatchδ p)) 0 := by
      ext i
      fin_cases i <;> simp [jointPatchCoordinate,AffineMap.lineMap_apply] <;> ring
    have hu : -bankPatchδ p+u.val*(2*bankPatchδ p) ∈ Icc (-bankPatchδ p) (bankPatchδ p) := by
      constructor <;> nlinarith [u.property.1,u.property.2,hBankPatchδ p]
    apply hActualBankAxisSupport
    · exact (hBankPatchSource p ((bankPatchF p).map_target (hJointPatchTarget p (0,u)))).2.1
    · change (bankPatchF p).symm (jointPatchCoordinate p (0,u)) ∈ range B.secondSide
      rw [hc]
      exact hBankPatchSideAxis p _ hu
  have hActualPatchSupportBound (p : P) : ∃ δ : ℝ, 0<δ ∧ ∀ t u : Interval,
      t.val<δ → jointPatchFamily p (t,u) ∈ actualWideSupport := by
    obtain ⟨δ,hδ,hbound⟩ := actual_joint_compact_support_bound (jointPatchFamily p)
      (hJointPatchContinuous p) (Set.univ : Set Interval) isCompact_univ actualWideSupport
      hActualWideSupportOpen (fun u _ => hJointPatchBaselineSupport p u)
    exact ⟨δ,hδ,fun t u ht => hbound t ht u (Set.mem_univ u)⟩
  let jointGapCoordinate (g : Fin (n+1)) (z : Interval × Interval) : ℝ × ℝ :=
    (1-z.2.val) • (ebank (gapL g z.1) : ℝ × ℝ)+z.2.val • (ebank (gapR g z.1) : ℝ × ℝ)
  have hJointGapContinuous (g : Fin (n+1)) : Continuous (jointGapCoordinate g) := by
    dsimp [jointGapCoordinate]
    fun_prop
  let actualWideBankSupport : Set (ℝ × ℝ) := bankPair '' (actualWideSupport ∩ bankPair.source)
  have hActualWideBankSupportOpen : IsOpen actualWideBankSupport :=
    bankPair.isOpen_image_of_subset_source (hActualWideSupportOpen.inter bankPair.open_source)
      Set.inter_subset_right
  have hJointGapBaselineSupport (g : Fin (n+1)) (u : Interval) :
      jointGapCoordinate g (0,u) ∈ actualWideBankSupport := by
    let x : ℝ := (1-u.val)*sideX (gapLeftθ g)+u.val*sideX (gapRightθ g)
    have hx : x ∈ Icc (sideX (gapAθ g)) (sideX (gapBθ g)) := by
      obtain ⟨hAl,hlr,hrB⟩ := hGapRealOrder g
      dsimp [x]
      constructor <;> nlinarith [u.property.1,u.property.2]
    obtain ⟨y,hy,hcoord,hOld⟩ := hGapWholeAxis g x hx
    have hya : y ∈ b.val.image := (hEbankAxis y hy).mpr (by rw [hcoord]; rfl)
    have hyGlobal : y ∈ globalF1.source := hGlobalESource ▸ (hEbankSource ▸ hy).1
    have hySide : y ∈ range B.secondSide := (hF1SideLocal y hyGlobal).mp hya
    refine ⟨y,⟨hActualBankAxisSupport y hy hySide,hBankPairSource.symm ▸ hy⟩,?_⟩
    rw [hBankPairValue,hcoord]
    change (x,0)=jointGapCoordinate g (0,u)
    dsimp [jointGapCoordinate]
    rw [hGapLCoordinate,hGapRCoordinate]
    exact Prod.ext rfl (by simp)
  have hActualGapSupportBound (g : Fin (n+1)) : ∃ δ : ℝ, 0<δ ∧ ∀ t u : Interval,
      t.val<δ → jointGapCoordinate g (t,u) ∈ actualWideBankSupport := by
    obtain ⟨δ,hδ,hbound⟩ := actual_joint_compact_support_bound (jointGapCoordinate g)
      (hJointGapContinuous g) (Set.univ : Set Interval) isCompact_univ actualWideBankSupport
      hActualWideBankSupportOpen (fun u _ => hJointGapBaselineSupport g u)
    exact ⟨δ,hδ,fun t u ht => hbound t ht u (Set.mem_univ u)⟩
  choose patchSupportRadius hPatchSupportRadius hPatchSupportContains using hActualPatchSupportBound
  choose gapSupportRadius hGapSupportRadius hGapSupportContains using hActualGapSupportBound
  let OSupport : Set ℝ := (Iio 1 ∩ ⋂ p : P, Iio (patchSupportRadius p)) ∩
    ⋂ g : Fin (n+1), Iio (gapSupportRadius g)
  have hOSupportOpen : IsOpen OSupport :=
    (isOpen_Iio.inter (isOpen_iInter_of_finite (fun _ => isOpen_Iio))).inter
      (isOpen_iInter_of_finite (fun _ => isOpen_Iio))
  have h0OSupport : (0 : ℝ) ∈ OSupport :=
    ⟨⟨by norm_num,Set.mem_iInter.mpr hPatchSupportRadius⟩,Set.mem_iInter.mpr hGapSupportRadius⟩
  obtain ⟨actualSupportRadius,hActualSupportRadius,hSupportBall⟩ :=
    Metric.isOpen_iff.mp hOSupportOpen 0 h0OSupport
  have hActualSupportParameterBounds (t : Interval) (ht : t.val<actualSupportRadius) :
      (∀ p : P, t.val<patchSupportRadius p) ∧ (∀ g : Fin (n+1), t.val<gapSupportRadius g) := by
    have hmem := hSupportBall (show t.val ∈ Metric.ball (0:ℝ) actualSupportRadius from by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg t.property.1]
      exact ht)
    exact ⟨Set.mem_iInter.mp hmem.1.2,Set.mem_iInter.mp hmem.2⟩
  have hActualExpandedFirstInWideCap : range expandedFirst ⊆ actualWideBaselineCapSet := by
    intro x hx
    rcases hActualExpandedFirstInBaselineCap hx with hD|hT
    · exact Or.inl hD
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hT
      by_cases hm : corner i ∈ M.cover.branch
      · exact False.elim (by simpa [hBaselineMarkedTriangleEmpty i hm] using hi)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨i,hCornerTriangleWide i hm hi⟩)
  have hActualExpandedPortSet : ({originalγ expandedL,originalγ expandedR} : Set S)=
      ({cornerA false,cornerA true} : Set S) := by
    rw [hExpandedLeft,hExpandedRight]
    cases leftPort <;> cases rightPort
    · exact False.elim (hPortsDifferent rfl)
    · rfl
    · exact Set.pair_comm _ _
    · exact False.elim (hPortsDifferent rfl)
  obtain ⟨matchedT,hMatchedT,hMatchedT1,hMatchedSupport,hMatchedPaths⟩ :=
    actual_marked_simultaneous_gap_matching_below M old b Ubank Vbank bankPair.open_target ebank
      (fun g => sideX (gapAθ g)) (fun g => sideX (gapLeftθ g))
      (fun g => sideX (gapRightθ g)) (fun g => sideX (gapBθ g))
      (fun g => (hGapRealOrder g).1) (fun g => (hGapRealOrder g).2.1) (fun g => (hGapRealOrder g).2.2)
      hGapPairWholeAxis hEbankPairAxis gapL gapR hGapLCoordinate hGapRCoordinate
      actualSupportRadius hActualSupportRadius hGapPairPositive
  choose matchedGap hMatchedGapEmbedded hMatchedGapBFree hMatchedGapOldFree hMatchedGapFormula using hMatchedPaths
  have hMatchedGapSupport (g : Fin (n+1)) : range (matchedGap g) ⊆ actualWideSupport := by
    rintro x ⟨u,rfl⟩
    obtain ⟨y,hy,hcoord⟩ := hMatchedGapFormula g u
    have hsup := hGapSupportContains g matchedT u
      ((hActualSupportParameterBounds matchedT hMatchedSupport).2 g)
    obtain ⟨z,⟨hzU,hzS⟩,hzcoord⟩ := hsup
    have hYS : (y : S) ∈ bankPair.source := y.property
    have he : z=(y : S) := bankPair.injOn hzS hYS (hzcoord.trans hcoord.symm)
    exact hy ▸ (he ▸ hzU)
  have hMatchedGapInside (g : Fin (n+1)) : range (matchedGap g) ⊆ (range B.disk)ᶜ := by
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
    hFixedCornerInside hFixedCornerA hFixedCornerK hFixedCornerB hFixedCornerMarks hFixedCornerOld hFixedCornerJoint using
      fun i => hCornerPaths i cornerT hCornerT
  have hFixedCornerSupport (i : Bool) : range (fixedCorner i) \ {cornerA i} ⊆ actualWideSupport := by
    rintro x ⟨⟨u,rfl⟩,hn⟩
    have hu0 : u≠0 := by
      intro he
      exact hn (Set.mem_singleton_iff.mpr ((congrArg (fixedCorner i) he).trans (hFixedCornerZero i)))
    have hu : 0<u.val := lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm))
    rw [hFixedCornerJoint i u]
    exact hActualWideCornerFamilySupport i cornerT u hu
  have hFixedCornerBankEnd (i : Bool) : fixedCorner i 1=(bankCornerL i matchedT : S) := by
    rw [hFixedCornerOne,hBankCornerFormula]
  obtain ⟨fixedRight,hFixedRightEmbedded,hFixedRightRange,hFixedRightZero,hFixedRightOne⟩ :=
    actual_reverse_embedded_continuous_arc (fixedCorner true) (hFixedCornerEmbedded true)
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
  have hFixedPatchInside (p : P) : range (fixedPatch p) ⊆ (range B.disk)ᶜ := by
    rw [hFixedPatchRange]
    exact hRawPieceInside p
  have hFixedPatchSource (p : P) : range (fixedPatch p) ⊆ (bankPatchF p).source := by
    rw [hFixedPatchRange]
    exact hRawPieceSource p
  have hFixedPatchSupport (p : P) : range (fixedPatch p) ⊆ actualWideSupport := by
    intro x hx
    rw [hFixedPatchRange,hRawPieceRange] at hx
    obtain ⟨z,hz,hzx⟩ := hx
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨u,hu,huZ⟩ := hz
    have hs := hPatchSupportContains p matchedT ⟨u,hu⟩
      ((hActualSupportParameterBounds matchedT hMatchedSupport).1 p)
    change (bankPatchF p).symm (jointPatchCoordinate p (matchedT,⟨u,hu⟩)) ∈ actualWideSupport at hs
    have he : jointPatchCoordinate p (matchedT,⟨u,hu⟩)=z := huZ
    exact hzx ▸ (he ▸ hs)
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
  have hPiecesSupport (k : Fin (2*n+3)) : range (pieces k) \
      ({cornerA false,cornerA true} : Set S) ⊆ actualWideSupport := by
    dsimp only [pieces]
    split_ifs
    · rintro x ⟨hx,hn⟩
      exact hFixedCornerSupport true ⟨hFixedRightRange ▸ hx,fun he => hn (Or.inr he)⟩
    · rintro x ⟨hx,hn⟩
      exact hFixedCornerSupport false ⟨hx,fun he => hn (Or.inl he)⟩
    · intro x hx
      exact hMatchedGapSupport _ hx.1
    · intro x hx
      exact hFixedPatchSupport _ hx.1
  have hPiecesEmbedded (k : Fin (2*n+3)) : IsEmbedding (pieces k) := by
    dsimp only [pieces]
    split_ifs
    · exact hFixedRightEmbedded
    · exact hFixedCornerEmbedded false
    · exact hMatchedGapEmbedded _
    · exact hFixedPatchEmbedded _
  have hActualFiniteArcChainInChart (F : OpenPartialHomeomorph S Plane) :
      ∀ n : ℕ, ∀ pieces : Fin (n+1) → C(Interval,S),
        (∀ i, IsEmbedding (pieces i)) → (∀ i, range (pieces i) ⊆ F.source) →
        (∀ i : Fin n, pieces i.castSucc 1=pieces i.succ 0) →
        (∀ i, pieces 0 0≠pieces i 1) →
        ∃ f : C(Interval,S), IsEmbedding f ∧ f 0=pieces 0 0 ∧
          f 1=pieces (Fin.last n) 1 ∧ range f ⊆ ⋃ i, range (pieces i) := by
    intro n
    induction n with
    | zero =>
      intro pieces he hs hc hn
      exact ⟨pieces 0,he 0,rfl,rfl,fun x hx => Set.mem_iUnion.mpr ⟨0,hx⟩⟩
    | succ n ih =>
      intro pieces he hs hc hn
      let prefixArc : Fin (n+1) → C(Interval,S) := fun i => pieces i.castSucc
      obtain ⟨f,hf,hf0,hf1,hfs⟩ := ih prefixArc
        (fun i => he i.castSucc) (fun i => hs i.castSucc)
        (fun i => hc i.castSucc) (fun i => hn i.castSucc)
      have hfS : range f ⊆ F.source := by
        intro x hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hfs hx)
        exact hs i.castSucc hi
      have hjoint : f 1=pieces (Fin.last (n+1)) 0 := by rw [hf1]; exact hc (Fin.last n)
      have hne : f 0≠pieces (Fin.last (n+1)) 1 := by rw [hf0]; exact hn _
      obtain ⟨g,hg,hg0,hg1,hgs⟩ := hActualChartArcJoin F f (pieces (Fin.last (n+1)))
        hf (he _) hfS (hs _) hjoint hne
      refine ⟨g,hg,hg0.trans hf0,hg1,?_⟩
      intro x hx
      rcases hgs hx with hx|hx
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hfs hx)
        exact Set.mem_iUnion.mpr ⟨i.castSucc,hi⟩
      · exact Set.mem_iUnion.mpr ⟨Fin.last (n+1),hx⟩
  have hMatchedGapSource (g : Fin (n+1)) : range (matchedGap g) ⊆ Ebank.source := by
    rintro x ⟨t,rfl⟩
    obtain ⟨u,hu,hcoord⟩ := hMatchedGapFormula g t
    rw [← hu]
    exact hBankPairSource ▸ u.property
  have hMatchedGapAFree (g : Fin (n+1)) : Disjoint (range (matchedGap g)) a.val.image :=
    hEbankOffA.mono_left (hMatchedGapSource g)
  have hFixedPatchAFree (p : P) : Disjoint (range (fixedPatch p)) a.val.image :=
    hEbankOffA.mono_left (fun x hx => (hBankPatchSource p (hFixedPatchSource p hx)).2.1)
  have hPiecesMeetA (k : Fin (2*n+3)) :
      range (pieces k) ∩ a.val.image ⊆ ({cornerA false,cornerA true} : Set S) := by
    dsimp only [pieces]
    split_ifs
    · intro x hx
      have hxa : x ∈ range (fixedCorner true) ∩ a.val.image := ⟨hFixedRightRange ▸ hx.1,hx.2⟩
      have he : x=cornerA true := Set.mem_singleton_iff.mp (hFixedCornerA true ▸ hxa)
      simp [he]
    · intro x hx
      have he : x=cornerA false := Set.mem_singleton_iff.mp (hFixedCornerA false ▸ hx)
      simp [he]
    · intro x hx
      exact False.elim (Set.disjoint_left.mp (hMatchedGapAFree _) hx.1 hx.2)
    · intro x hx
      exact False.elim (Set.disjoint_left.mp (hFixedPatchAFree _) hx.1 hx.2)
  have hPiecesMarks (k : Fin (2*n+3)) :
      range (pieces k) ∩ (M.cover.branch : Set S) ⊆ ({B.firstCorner,B.secondCorner} : Set S) := by
    dsimp only [pieces]
    split_ifs
    · intro x hx
      have hxm : x ∈ range (fixedCorner true) ∩ (M.cover.branch : Set S) := ⟨hFixedRightRange ▸ hx.1,hx.2⟩
      have he : x=corner true := Set.mem_singleton_iff.mp (hFixedCornerMarks true hxm)
      simp [he,corner]
    · intro x hx
      have he : x=corner false := Set.mem_singleton_iff.mp (hFixedCornerMarks false hx)
      simp [he,corner]
    · intro x hx
      exact False.elim (Set.disjoint_left.mp hEbankMarks (hMatchedGapSource _ hx.1) hx.2)
    · intro x hx
      exact False.elim (Set.disjoint_left.mp (hFixedPatchMarks _) hx.1 hx.2)
  have hPiecesStartsAvoid (k : Fin (2*n+3)) : pieces 0 0≠pieces k 1 := by
    rw [hPieceZero,hFixedCornerZero]
    dsimp only [pieces]
    split_ifs
    · rw [hFixedRightOne,hFixedCornerZero]
      exact hCornerADistinct
    · intro he
      have hh := congrArg Subtype.val ((hFixedCornerEmbedded false).injective
        ((hFixedCornerZero false).trans he))
      norm_num at hh
    · intro he
      exact Set.disjoint_left.mp (hMatchedGapAFree _) (Set.mem_range_self 1) (he ▸ hCornerAOnA false)
    · intro he
      exact Set.disjoint_left.mp (hFixedPatchAFree _) (Set.mem_range_self 1) (he ▸ hCornerAOnA false)
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
  have hPiecesInExteriorChart (k : Fin (2*n+3)) : range (pieces k) ⊆ exteriorChart.source := by
    intro x hx
    apply hExteriorChartCovers
    intro he
    have hh : exteriorPuncture ∈ ({B.firstCorner,B.secondCorner} : Set S) :=
      hPiecesMarks k ⟨he ▸ hx,hExteriorPunctureMark⟩
    exact hExteriorPunctureCorner (by simpa using hh)
  obtain ⟨roundedTrace,hRoundedEmbedded,hRoundedZero,hRoundedOne,hRoundedPieces⟩ :=
    hActualFiniteArcChainInChart exteriorChart (2*n+2) pieces hPiecesEmbedded
      hPiecesInExteriorChart hPiecesJoin hPiecesStartsAvoid
  have hRoundedTraceSupport : range roundedTrace \
      ({originalγ expandedL,originalγ expandedR} : Set S) ⊆ actualWideSupport := by
    rintro x ⟨hx,hn⟩
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (hRoundedPieces hx)
    exact hPiecesSupport k ⟨hk,hActualExpandedPortSet ▸ hn⟩
  have hRoundedStart : roundedTrace 0=cornerA false := by rw [hRoundedZero,hPieceZero,hFixedCornerZero]
  have hRoundedEnd : roundedTrace 1=cornerA true := by
    rw [hRoundedOne,hPieceLast,hFixedRightOne,hFixedCornerZero]
  have hRoundedMeetsA : range roundedTrace ∩ a.val.image=({cornerA false,cornerA true} : Set S) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (hRoundedPieces hx.1)
      exact hPiecesMeetA k ⟨hk,hx.2⟩
    · rintro (he|he)
      · subst x; exact ⟨⟨0,hRoundedStart⟩,hCornerAOnA false⟩
      · subst x; exact ⟨⟨1,hRoundedEnd⟩,hCornerAOnA true⟩
  have hRoundedOldInPatches (j : J) :
      range roundedTrace ∩ arcInterior M (old j) ⊆ ⋃ p : P, range (fixedPatch p) ∩ (old j).val.image := by
    intro x hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (hRoundedPieces hx.1)
    dsimp only [pieces] at hk
    split_ifs at hk
    · rw [hFixedRightRange] at hk
      exact False.elim (Set.disjoint_left.mp (hFixedCornerOld true j) hk hx.2)
    · exact False.elim (Set.disjoint_left.mp (hFixedCornerOld false j) hk hx.2)
    · exact False.elim (Set.disjoint_left.mp (hMatchedGapOldFree _ j) hk hx.2.1)
    · exact Set.mem_iUnion.mpr ⟨_,hk,hx.2.1⟩
  have hRoundedOldBudget (j : J) :
      (range roundedTrace ∩ arcInterior M (old j)).Finite ∧
      (range roundedTrace ∩ arcInterior M (old j)).ncard ≤
        (crossings M b (old j) ∩ range B.secondSide).ncard := by
    obtain ⟨hUnionFinite,hUnionBound⟩ := CurveComplex.actual_finite_union_card_bound
      (fun p : P => range (fixedPatch p) ∩ (old j).val.image)
      (fun p => (hFixedPatchCounts p j).1)
    refine ⟨hUnionFinite.subset (hRoundedOldInPatches j),?_⟩
    calc
      (range roundedTrace ∩ arcInterior M (old j)).ncard ≤
          (⋃ p : P, range (fixedPatch p) ∩ (old j).val.image).ncard :=
        Set.ncard_le_ncard (hRoundedOldInPatches j) hUnionFinite
      _ ≤ ∑ p : P, (range (fixedPatch p) ∩ (old j).val.image).ncard := hUnionBound
      _ ≤ ∑ p : P, if p.val ∈ (old j).val.image then 1 else 0 :=
        Finset.sum_le_sum (fun p hp => (hFixedPatchCounts p j).2)
      _ = (crossings M b (old j) ∩ range B.secondSide).ncard := hActualSideIncidenceBudget j
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
  have hRoundedCoverForPatch (p : P) : range roundedTrace ⊆ range (fixedPatch p) ∪ otherPieces p := by
    intro x hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (hRoundedPieces hx)
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
  have hRoundedPointNotEndpoint (i : Bool) (j : J) (x : S)
      (hx : x ∈ arcInterior M (old j)) : x≠cornerA i := by
    intro he
    exact Set.disjoint_left.mp (hFixedCornerOld i j)
      (he.symm ▸ (show cornerA i ∈ range (fixedCorner i) from ⟨0,hFixedCornerZero i⟩)) hx
  have hRoundedWholeTraceCharts (j : J) (x : S)
      (hx : x ∈ range roundedTrace ∩ arcInterior M (old j)) :
      ∃ F : OpenPartialHomeomorph S Plane, x ∈ F.source ∧ F x=0 ∧
        Disjoint F.source (M.cover.branch : Set S) ∧ Disjoint F.source Kraw ∧
        ∀ y ∈ F.source, (y ∈ range roundedTrace ↔ F y 1=0) ∧
          (y ∈ (old j).val.image ↔ F y 0=0) := by
    obtain ⟨p,hpPiece,hpOld⟩ := Set.mem_iUnion.mp (hRoundedOldInPatches j hx)
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
      have hm : x ∈ ({cornerA false,cornerA true} : Set S) :=
        hRoundedMeetsA ▸ (show x ∈ range roundedTrace ∩ a.val.image from
          ⟨hx.1,hdecompRaw.symm ▸ Or.inr hk⟩)
      rcases hm with he|he
      · exact hRoundedPointNotEndpoint false j x hx.2 he
      · exact hRoundedPointNotEndpoint true j x hx.2 he
    have hx0 : x ≠ roundedTrace 0 := by
      intro he
      exact hRoundedPointNotEndpoint false j x hx.2 (he.trans hRoundedStart)
    have hx1 : x ≠ roundedTrace 1 := by
      intro he
      exact hRoundedPointNotEndpoint true j x hx.2 (he.trans hRoundedEnd)
    exact actual_joined_carrier_local_axis_chart roundedTrace hRoundedEmbedded
      (range (fixedPatch p)) (otherPieces p) Kraw (M.cover.branch : Set S) (old j).val.image
      (hOtherPiecesCompact p).isClosed hKraw.isClosed (hRoundedCoverForPatch p)
      x hx.1 hxOthers hxK hx0 hx1 F0 hxF0 hF0x hF0Mark
      (fun y hy => hF0Line y (hFixedPatchHeight p y hy.1)) hF0Old
  have hFixedCornerBInteriorFree (i : Bool) :
      Disjoint (range (fixedCorner i)) (arcInterior M b) := by
    apply Set.disjoint_left.mpr
    intro x hx hb
    have hh : x ∈ (if corner i ∈ M.cover.branch then {corner i} else ∅ : Set S) :=
      hFixedCornerB i ▸ (show x ∈ range (fixedCorner i) ∩ b.val.image from ⟨hx,hb.1⟩)
    split_ifs at hh with hm
    · have he : x=corner i := Set.mem_singleton_iff.mp hh
      exact hb.2 (he.symm ▸ hm)
    · exact hh
  have hRoundedBInteriorFree : Disjoint (range roundedTrace) (arcInterior M b) := by
    apply Set.disjoint_left.mpr
    intro x hx hb
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (hRoundedPieces hx)
    dsimp only [pieces] at hk
    split_ifs at hk
    · rw [hFixedRightRange] at hk
      exact Set.disjoint_left.mp (hFixedCornerBInteriorFree true) hk hb
    · exact Set.disjoint_left.mp (hFixedCornerBInteriorFree false) hk hb
    · exact Set.disjoint_left.mp (hMatchedGapBFree _) hk hb.1
    · exact Set.disjoint_left.mp (hFixedPatchB _) hk hb.1
  have hExpandedEndpointsOldFree (i : Bool) (j : J) : cornerA i ∉ arcInterior M (old j) := by
    exact fun hx => Set.disjoint_left.mp (hFixedCornerOld i j) ⟨0,hFixedCornerZero i⟩ hx
  have hExpandedEndpointsBFree (i : Bool) : cornerA i ∉ arcInterior M b := by
    exact fun hx => Set.disjoint_left.mp (hFixedCornerBInteriorFree i) ⟨0,hFixedCornerZero i⟩ hx
  have hActualRoundedRetainedTransverse (d e : EssentialMarkedArc M)
      (hImage : d.val.image=expandedK ∪ range roundedTrace)
      (p : S) (hp : p ∈ expandedK ∩ arcInterior M e)
      (hCross : CrossesInDisk M a e p)
      (hEndpoint : ∀ i : Bool, cornerA i ∉ arcInterior M e) : CrossesInDisk M d e p := by
    have hpRemoved : p ∉ range expandedFirst := by
      intro hh
      have hm : p ∈ ({originalγ expandedL,originalγ expandedR} : Set S) :=
        hExpandedMeet ▸ (show p ∈ range expandedFirst ∩ expandedK from ⟨hh,hp.1⟩)
      rcases hm with he|he
      · exact hEndpoint leftPort (he.trans hExpandedLeft ▸ hp.2)
      · exact hEndpoint rightPort (he.trans hExpandedRight ▸ hp.2)
    have hpRounded : p ∉ range roundedTrace := by
      intro hh
      have hm : p ∈ ({cornerA false,cornerA true} : Set S) :=
        hRoundedMeetsA ▸ (show p ∈ range roundedTrace ∩ a.val.image from
          ⟨hh,hdecompRaw.symm ▸ Or.inr (hExpandedKSubset hp.1)⟩)
      rcases hm with he|he
      · exact hEndpoint false (he ▸ hp.2)
      · exact hEndpoint true (he ▸ hp.2)
    let W : Set S := (range expandedFirst ∪ range roundedTrace)ᶜ
    have hW : IsOpen W := ((isCompact_range expandedFirst.continuous).union
      (isCompact_range roundedTrace.continuous)).isClosed.isOpen_compl
    obtain ⟨F,hpF,hFW,hF0,hMarks,hA,hE⟩ := hMarkedLocalizedCrossingChart a e p hCross W hW
      (by rintro (hf|hr); exact hpRemoved hf; exact hpRounded hr)
    have hDAxis (x : S) (hx : x ∈ F.source) : x ∈ d.val.image ↔ (F x).2=0 := by
      have hxF : x ∉ range expandedFirst := fun hh => hFW hx (Or.inl hh)
      have hxR : x ∉ range roundedTrace := fun hh => hFW hx (Or.inr hh)
      have he : x ∈ d.val.image ↔ x ∈ a.val.image := by
        rw [hImage,hExpandedDecomposition]
        simp only [Set.mem_union,hxF,hxR,false_or,or_false]
      exact he.trans (hA x hx)
    let xy : Plane ≃ₜ ℝ × ℝ := ((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
    let F0 := F.trans xy.symm.toOpenPartialHomeomorph
    have hs : F0.source=F.source := by simp [F0,OpenPartialHomeomorph.trans_source]
    have h0 (x : S) : F0 x 0=(F x).1 := rfl
    have h1 (x : S) : F0 x 1=(F x).2 := rfl
    apply hSymm
    apply actual_affine_graph_crosses_in_disk M e d F0 p (hs.symm ▸ hpF)
      (hs.symm ▸ hMarks) (by rw [h0,hF0]) 0
    · intro x hx; rw [h0]; exact hE x (hs ▸ hx)
    · intro x hx; rw [h1,h1,hF0,zero_mul,add_zero]; exact hDAxis x (hs ▸ hx)
  have hActualRoundedOldConsumer (d : EssentialMarkedArc M)
      (hImage : d.val.image=expandedK ∪ range roundedTrace) (j : J) :
      (crossings M d (old j)).Finite ∧
      (∀ p ∈ crossings M d (old j), CrossesInDisk M d (old j) p) ∧
      (crossings M d (old j)).ncard ≤
        (crossings M a (old j) \ range B.firstSide).ncard+
        (crossings M b (old j) ∩ range B.secondSide).ncard := by
    have hTrace : crossings M d (old j)=(expandedK ∩ arcInterior M (old j)) ∪
        (range roundedTrace ∩ arcInterior M (old j)) := by
      ext x
      constructor
      · rintro ⟨⟨hx,hm⟩,he⟩
        rcases hImage ▸ hx with hk|hr
        · exact Or.inl ⟨hk,he⟩
        · exact Or.inr ⟨hr,he⟩
      · rintro (⟨hk,he⟩|⟨hr,he⟩)
        · exact ⟨⟨hImage.symm ▸ Or.inl hk,he.2⟩,he⟩
        · exact ⟨⟨hImage.symm ▸ Or.inr hr,he.2⟩,he⟩
    have hRetainedSubset : expandedK ∩ arcInterior M (old j) ⊆
        crossings M a (old j) \ range B.firstSide := by
      intro x hx
      exact hRawRetainedCrossings j ▸ (show x ∈ Kraw ∩ arcInterior M (old j) from
        ⟨hExpandedKSubset hx.1,hx.2⟩)
    have hRetainedFinite := ((ha j).1.sdiff).subset hRetainedSubset
    refine ⟨hTrace.symm ▸ hRetainedFinite.union (hRoundedOldBudget j).1,?_,?_⟩
    · intro x hx
      rcases hTrace ▸ hx with hk|hr
      · apply hActualRoundedRetainedTransverse d (old j) hImage x hk
          ((ha j).2 x (hRetainedSubset hk).1)
        exact fun i => hExpandedEndpointsOldFree i j
      · obtain ⟨F,hxF,hF0,hMarks,hK,hAxes⟩ := hRoundedWholeTraceCharts j x hr
        have hDAxis (y : S) (hy : y ∈ F.source) : y ∈ d.val.image ↔ F y 1=0 := by
          have hyK : y ∉ expandedK := fun hk => Set.disjoint_left.mp hK hy (hExpandedKSubset hk)
          rw [hImage]
          simp only [Set.mem_union,hyK,false_or]
          exact (hAxes y hy).1
        apply hSymm
        apply actual_affine_graph_crosses_in_disk M (old j) d F x hxF hMarks (by rw [hF0]; rfl) 0
        · intro y hy; exact (hAxes y hy).2
        · intro y hy; rw [hF0,zero_mul,add_zero]; exact hDAxis y hy
    · rw [hTrace]
      exact (Set.ncard_union_le _ _).trans (Nat.add_le_add
        (Set.ncard_le_ncard hRetainedSubset ((ha j).1.sdiff)) (hRoundedOldBudget j).2)
  have hActualRoundedSelectedConsumer (d : EssentialMarkedArc M)
      (hImage : d.val.image=expandedK ∪ range roundedTrace) :
      (crossings M d b).Finite ∧
      (crossings M d b).ncard < (crossings M a b).ncard ∧
      ∀ p ∈ crossings M d b, CrossesInDisk M d b p := by
    have hRetained (p : S) (hp : p ∈ crossings M d b) : p ∈ expandedK ∩ arcInterior M b := by
      rcases hImage ▸ hp.1.1 with hk|hr
      · exact ⟨hk,hp.2⟩
      · exact False.elim (Set.disjoint_left.mp hRoundedBInteriorFree hr hp.2)
    have hSubset : crossings M d b ⊆ crossings M a b := by
      intro p hp
      exact ⟨⟨hdecompRaw.symm ▸ Or.inr (hExpandedKSubset (hRetained p hp).1),hp.1.2⟩,hp.2⟩
    have hRemoved : roundCorner ∉ crossings M d b := by
      intro hp
      exact hUnmarkedCornerOffExpandedK roundCorner hRoundCorner hRoundCross.1.2 (hRetained roundCorner hp).1
    obtain ⟨hf,hd⟩ := hRoundedStrictOriginalConsumer d hSubset hRemoved
    refine ⟨hf,hd,?_⟩
    intro p hp
    exact hActualRoundedRetainedTransverse d b hImage p (hRetained p hp)
      (htab p (hSubset hp)) hExpandedEndpointsBFree
  have hActualOriginalRoundedConclusion
      (d : EssentialMarkedArc M) (hClass : vertex M d=vertex M a)
      (hImage : d.val.image=expandedK ∪ range roundedTrace) :
      vertex M d=vertex M a ∧ (crossings M d b).Finite ∧
      (crossings M d b).ncard<(crossings M a b).ncard ∧
      (∀ p ∈ crossings M d b,CrossesInDisk M d b p) ∧
      ∀ j, (crossings M d (old j)).Finite ∧
        (∀ p ∈ crossings M d (old j),CrossesInDisk M d (old j) p) ∧
        (crossings M d (old j)).ncard≤
          (crossings M a (old j) \ range B.firstSide).ncard+
          (crossings M b (old j) ∩ range B.secondSide).ncard := by
    obtain ⟨hf,hd,ht⟩ := hActualRoundedSelectedConsumer d hImage
    exact ⟨hClass,hf,hd,ht,hActualRoundedOldConsumer d hImage⟩
  obtain ⟨reverseRounded,hReverseRoundedEmbedded,hReverseRoundedRange,hReverseRoundedZero,hReverseRoundedOne⟩ :=
    actual_reverse_embedded_continuous_arc roundedTrace hRoundedEmbedded
  let orientedRounded : C(Interval,S) := if leftPort then reverseRounded else roundedTrace
  have hOrientedRoundedRange : range orientedRounded=range roundedTrace := by
    cases leftPort <;> simp [orientedRounded,hReverseRoundedRange]
  have hOrientedRoundedEmbedded : IsEmbedding orientedRounded := by
    cases leftPort <;> simp only [orientedRounded,Bool.false_eq_true,if_false,if_true]
    · exact hRoundedEmbedded
    · exact hReverseRoundedEmbedded
  have hOrientedRoundedZero : orientedRounded 0=originalγ expandedL := by
    rw [hExpandedLeft]
    cases leftPort <;> simp [orientedRounded,hReverseRoundedZero,hRoundedStart,hRoundedEnd]
  have hOrientedRoundedOne : orientedRounded 1=originalγ expandedR := by
    rw [hExpandedRight]
    cases leftPort <;> cases rightPort
    · exact False.elim (hPortsDifferent rfl)
    · exact hRoundedEnd
    · exact hReverseRoundedOne.trans hRoundedStart
    · exact False.elim (hPortsDifferent rfl)
  have hExpandedRoundedBoundaryMeet : range expandedFirst ∩ range orientedRounded=
      ({originalγ expandedL,originalγ expandedR} : Set S) := by
    rw [hOrientedRoundedRange]
    ext x
    constructor
    · intro hx
      have hm : x ∈ ({cornerA false,cornerA true} : Set S) :=
        hRoundedMeetsA ▸ (show x ∈ range roundedTrace ∩ a.val.image from
          ⟨hx.2,hExpandedFirstOnA hx.1⟩)
      rw [hExpandedLeft,hExpandedRight]
      cases leftPort <;> cases rightPort
      · exact False.elim (hPortsDifferent rfl)
      · exact hm
      · simpa only [Set.pair_comm] using hm
      · exact False.elim (hPortsDifferent rfl)
    · rintro (he|he)
      · have hfirst : x ∈ range expandedFirst := ⟨0,hExpandedFirstZero.trans he.symm⟩
        have hround : x ∈ range orientedRounded := ⟨0,hOrientedRoundedZero.trans he.symm⟩
        exact ⟨hfirst,hOrientedRoundedRange ▸ hround⟩
      · have hfirst : x ∈ range expandedFirst := ⟨1,hExpandedFirstOne.trans he.symm⟩
        have hround : x ∈ range orientedRounded := ⟨1,hOrientedRoundedOne.trans he.symm⟩
        exact ⟨hfirst,hOrientedRoundedRange ▸ hround⟩
  have hOrientedRoundedPunctureFree (x : S) (hx : x ∈ range orientedRounded) : x≠exteriorPuncture := by
    intro he
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (hRoundedPieces (hOrientedRoundedRange ▸ hx))
    have hh := hPiecesMarks k ⟨he ▸ hk,hExteriorPunctureMark⟩
    exact hExteriorPunctureCorner (by simpa using hh)
  let roundedPlane : C(Interval,Plane) := ⟨fun t => capCoordinates
      ⟨orientedRounded t,hOrientedRoundedPunctureFree _ (Set.mem_range_self t)⟩,
    capCoordinates.continuous.comp (orientedRounded.continuous.subtype_mk _)⟩
  have hRoundedPlaneEmbedded : IsEmbedding roundedPlane :=
    (roundedPlane.continuous.isClosedEmbedding (by
      intro t u he
      exact hOrientedRoundedEmbedded.injective (congrArg Subtype.val (capCoordinates.injective he)))).isEmbedding
  have hPlanePort0 : expandedPlane 0=roundedPlane 0 := by
    apply capCoordinates.injective.eq_iff.mpr
    apply Subtype.ext
    exact hExpandedFirstZero.trans hOrientedRoundedZero.symm
  have hPlanePort1 : expandedPlane 1=roundedPlane 1 := by
    apply capCoordinates.injective.eq_iff.mpr
    apply Subtype.ext
    exact hExpandedFirstOne.trans hOrientedRoundedOne.symm
  have hExpandedPlaneInteriorSupport (t : Interval) (ht0 : 0<t.val) (ht1 : t.val<1) :
      expandedPlane t ∈ widePlaneSupport := by
    have hS : expandedFirst t ∈ actualWideSupport := by
      apply hActualWideCapExceptPortsSupport
      refine ⟨hActualExpandedFirstInWideCap (Set.mem_range_self t),?_⟩
      rintro (he|he)
      · have ht := congrArg Subtype.val (hExpandedEmbedded.injective (he.trans hExpandedFirstZero.symm))
        change t.val=0 at ht
        linarith
      · have he1 : expandedFirst t=originalγ expandedR := by simpa using he
        have ht := congrArg Subtype.val (hExpandedEmbedded.injective (he1.trans hExpandedFirstOne.symm))
        change t.val=1 at ht
        linarith
    obtain ⟨z,hz,hzs⟩ := hS
    have he : z=expandedPlane t := (M.planeToSphere_injective exteriorPuncture)
      (hzs.trans (hExpandedPlaneBack t).symm)
    exact he ▸ hz
  have hExpandedPlaneClosureSupport : range expandedPlane ⊆ closure widePlaneSupport := by
    let f : ℝ → Plane := expandedPlane ∘ Set.projIcc 0 1 zero_le_one
    have hf : Continuous f := expandedPlane.continuous.comp continuous_projIcc
    have hImage : f '' Ioo (0:ℝ) 1 ⊆ widePlaneSupport := by
      rintro x ⟨u,hu,rfl⟩
      have h01 : u ∈ Icc (0:ℝ) 1 := ⟨hu.1.le,hu.2.le⟩
      have hh := hExpandedPlaneInteriorSupport ⟨u,h01⟩ hu.1 hu.2
      simpa only [f,Function.comp_def,Set.projIcc_of_mem zero_le_one h01] using hh
    have hAll : f '' Icc (0:ℝ) 1 ⊆ closure widePlaneSupport := by
      rw [← closure_Ioo (show (0:ℝ)≠1 by norm_num)]
      exact (image_closure_subset_closure_image hf).trans (closure_mono hImage)
    rintro x ⟨t,rfl⟩
    exact hAll ⟨t.val,t.property,by simp [f,Set.projIcc_of_mem zero_le_one t.property]⟩
  have hRoundedPlaneClosureSupport : range roundedPlane ⊆ closure widePlaneSupport := by
    rintro x ⟨t,rfl⟩
    have hb : M.planeToSphere exteriorPuncture (roundedPlane t)=orientedRounded t :=
      congrArg Subtype.val (capCoordinates.symm_apply_apply _)
    by_cases hp : orientedRounded t ∈ ({originalγ expandedL,originalγ expandedR} : Set S)
    · rcases hp with he|he
      · have he0 : roundedPlane t=expandedPlane 0 := (M.planeToSphere_injective exteriorPuncture)
          (hb.trans (he.trans (hExpandedFirstZero.symm.trans (hExpandedPlaneBack 0).symm)))
        exact he0.symm ▸ hExpandedPlaneClosureSupport (Set.mem_range_self 0)
      · have he1 : orientedRounded t=originalγ expandedR := by simpa using he
        have he0 : roundedPlane t=expandedPlane 1 := (M.planeToSphere_injective exteriorPuncture)
          (hb.trans (he1.trans (hExpandedFirstOne.symm.trans (hExpandedPlaneBack 1).symm)))
        exact he0.symm ▸ hExpandedPlaneClosureSupport (Set.mem_range_self 1)
    · have hS := hRoundedTraceSupport ⟨hOrientedRoundedRange ▸ Set.mem_range_self t,hp⟩
      obtain ⟨z,hz,hzs⟩ := hS
      have he : z=roundedPlane t := (M.planeToSphere_injective exteriorPuncture) (hzs.trans hb.symm)
      exact subset_closure (he ▸ hz)
  have hActualRoundedJordan : IsJordanCurve (range expandedPlane ∪ range roundedPlane) := by
    apply IsJordanCurve.of_two_arcs (hCapEmbeddedSideArc expandedPlane hExpandedPlaneEmbedded)
      (show IsArcBetween (range roundedPlane) (expandedPlane 1) (expandedPlane 0) from
        (by rw [hPlanePort0,hPlanePort1]; exact (hCapEmbeddedSideArc roundedPlane hRoundedPlaneEmbedded).reverse))
    rintro z ⟨t,ht⟩ ⟨u,hu⟩
    have he : expandedFirst t=orientedRounded u := congrArg Subtype.val
      (capCoordinates.injective (ht.trans hu.symm))
    have hm : expandedFirst t ∈ ({originalγ expandedL,originalγ expandedR} : Set S) :=
      hExpandedRoundedBoundaryMeet ▸ (show expandedFirst t ∈ range expandedFirst ∩ range orientedRounded from
        ⟨Set.mem_range_self t,⟨u,he.symm⟩⟩)
    rcases hm with h0|h1
    · have ht0 : t=0 := hExpandedEmbedded.injective (h0.trans hExpandedFirstZero.symm)
      exact Or.inl (ht.symm.trans (congrArg expandedPlane ht0))
    · have ht1 : t=1 := hExpandedEmbedded.injective (h1.trans hExpandedFirstOne.symm)
      exact Or.inr (ht.symm.trans (congrArg expandedPlane ht1))
  have hActualRoundedJordanInsideSupport : inside (range expandedPlane ∪ range roundedPlane) ⊆ widePlaneSupport := by
    rw [hWidePlaneSupportImage]
    apply actual_jordan_inside_open_disk_enclosure _ hActualRoundedJordan wideSupportHomeomorph
    rw [← hWidePlaneSupportImage]
    exact fun x hx => hx.elim (fun hf => hExpandedPlaneClosureSupport hf) (fun hr => hRoundedPlaneClosureSupport hr)
  obtain ⟨roundedPlaneDisk,hRoundedPlaneDiskEmbedded,hRoundedPlaneDiskBoundary⟩ :=
    hActualJordanClosedDiskProducer (range expandedPlane ∪ range roundedPlane) hActualRoundedJordan
  have hActualRoundedPlaneDiskInteriorNonempty : (interior (range roundedPlaneDisk)).Nonempty := by
    let v : Metric.closedBall (0 : Plane) 1 := ⟨0,by simp⟩
    have hv : v.val ∈ Metric.ball (0 : Plane) 1 := by simp [v]
    have hOpen : IsOpen (roundedPlaneDisk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) :=
      CurveComplex.embedded_disk_interior_isOpen roundedPlaneDisk hRoundedPlaneDiskEmbedded
    exact ⟨roundedPlaneDisk v,interior_maximal (Set.image_subset_range _ _) hOpen ⟨v,hv,rfl⟩⟩
  have hActualRoundedPlaneDiskClosedRegion : range roundedPlaneDisk=
      inside (range expandedPlane ∪ range roundedPlane) ∪ (range expandedPlane ∪ range roundedPlane) := by
    apply hActualCompactBaselineCapRecognitionOfFrontierSubset _ _
      (isCompact_range roundedPlaneDisk.continuous) (jordan_curve_theorem hActualRoundedJordan)
      _ hActualRoundedPlaneDiskInteriorNonempty
    rw [← hRoundedPlaneDiskBoundary]
    exact CurveComplex.embedded_disk_frontier_subset_boundary roundedPlaneDisk hRoundedPlaneDiskEmbedded
  have hActualRoundedPlaneDiskOpenInside (z : Metric.closedBall (0 : Plane) 1)
      (hz : z.val ∈ Metric.ball (0 : Plane) 1) :
      roundedPlaneDisk z ∈ inside (range expandedPlane ∪ range roundedPlane) := by
    rcases hActualRoundedPlaneDiskClosedRegion ▸ Set.mem_range_self z with hi|hc
    · exact hi
    · rw [← hRoundedPlaneDiskBoundary] at hc
      obtain ⟨w,hw,he⟩ := hc
      have hwz := hRoundedPlaneDiskEmbedded.injective he
      exact False.elim (not_lt_of_ge (show 1 ≤ dist z.val (0:Plane) from by
        rw [← hwz]
        exact hw.ge) hz)
  let roundedCap : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨M.planeToSphere exteriorPuncture ∘ roundedPlaneDisk,
      (M.planeToSphere_isOpenEmbedding exteriorPuncture).continuous.comp roundedPlaneDisk.continuous⟩
  have hRoundedCapEmbedded : IsEmbedding roundedCap :=
    (M.planeToSphere_isOpenEmbedding exteriorPuncture).isEmbedding.comp hRoundedPlaneDiskEmbedded
  have hRoundedPlaneBack (t : Interval) :
      M.planeToSphere exteriorPuncture (roundedPlane t)=orientedRounded t :=
    congrArg Subtype.val (capCoordinates.symm_apply_apply _)
  have hRoundedCapBoundary : roundedCap '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=
      range expandedFirst ∪ range roundedTrace := by
    change (M.planeToSphere exteriorPuncture ∘ roundedPlaneDisk) '' _ = _
    rw [Set.image_comp,hRoundedPlaneDiskBoundary,Set.image_union,← Set.range_comp,← Set.range_comp]
    have hfirst : M.planeToSphere exteriorPuncture ∘ expandedPlane=expandedFirst := funext hExpandedPlaneBack
    have hround : M.planeToSphere exteriorPuncture ∘ roundedPlane=orientedRounded := funext hRoundedPlaneBack
    rw [hfirst,hround,hOrientedRoundedRange]
  have hActualRoundedCapChart :
      ∃ (F : Plane → S) (A Cplane : Set Plane) (p q : Plane),
        IsOpenEmbedding F ∧ IsArcBetween A p q ∧ IsArcBetween Cplane p q ∧
        A ∪ Cplane=modelCurve ∧ F '' A=range expandedFirst ∧ F '' Cplane=range orientedRounded ∧
        F p=originalγ expandedL ∧ F q=originalγ expandedR ∧
        F '' Plane.openSquare 0 1=roundedCap '' {x | x.val ∈ Metric.ball (0 : Plane) 1} := by
    let v := exteriorPuncture
    let e := capCoordinates
    let g := expandedPlane
    let h := roundedPlane
    let d := roundedPlaneDisk
    have hd : IsEmbedding d := hRoundedPlaneDiskEmbedded
    have hg : IsEmbedding g := hExpandedPlaneEmbedded
    have hh : IsEmbedding h := hRoundedPlaneEmbedded
    have hg0 : g 0=h 0 := hPlanePort0
    have hg1 : g 1=h 1 := hPlanePort1
    have hgA := hCapEmbeddedSideArc g hg
    have hhB : IsArcBetween (range h) (g 0) (g 1) := by
      rw [hg0,hg1]; exact hCapEmbeddedSideArc h hh
    have hc : IsJordanCurve (range g ∪ range h) := hActualRoundedJordan
    have hbd : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=range g ∪ range h :=
      hRoundedPlaneDiskBoundary
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
    let Cplane := φ.symm '' range h
    let p := φ.symm (g 0)
    let q := φ.symm (g 1)
    have hcancel (K : Set Plane) : φ '' (φ.symm '' K) = K := by
      ext z; simp
    have hgs (t) : M.planeToSphere v (g t) = expandedFirst t := congrArg Subtype.val (e.symm_apply_apply _)
    have hhs (t) : M.planeToSphere v (h t) = orientedRounded t := congrArg Subtype.val (e.symm_apply_apply _)
    refine ⟨f,A,Cplane,p,q,(M.planeToSphere_isOpenEmbedding v).comp φ.isOpenEmbedding,
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
      rw [φ.apply_symm_apply,hgs,hExpandedFirstZero]
    · change M.planeToSphere v (φ (φ.symm (g 1))) = _
      rw [φ.apply_symm_apply,hgs,hExpandedFirstOne]
    · change (M.planeToSphere v ∘ φ) '' Plane.openSquare 0 1 = _
      rw [image_comp,hφI,← hi,image_image]
      apply Set.image_congr
      intro x hx
      rfl
  have hActualSupportedRoundedFinal
      (hMarks : ∀ x ∈ range roundedCap, x ∈ M.cover.branch →
        x ∈ ({originalγ expandedL,originalγ expandedR} : Set S))
      (hK : range roundedCap ∩ expandedK ⊆
        ({originalγ expandedL,originalγ expandedR} : Set S)) :
      ∃ d : EssentialMarkedArc M, vertex M d=vertex M a ∧
        d.val.image=expandedK ∪ range roundedTrace := by
    obtain ⟨capF,capA,capC,capP,capQ,hCapF,hCapA,hCapC,hCapAC,
      hCapFA,hCapFC,hCapFP,hCapFQ,hCapFInside⟩ := hActualRoundedCapChart
    have hOpenOffBoundary : Disjoint
        (roundedCap '' {x | x.val ∈ Metric.ball (0 : Plane) 1})
        (roundedCap '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
      have hxy : x=y := hRoundedCapEmbedded.injective (hxz.trans hyz.symm)
      have hlt : dist y.val 0<1 := hxy ▸ hx
      exact (ne_of_lt hlt) hy
    have hEndpointsBoundary : ({originalγ expandedL,originalγ expandedR} : Set S) ⊆
        roundedCap '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
      rw [hRoundedCapBoundary]
      rintro x (he|he)
      · exact Or.inl ⟨0,hExpandedFirstZero.trans he.symm⟩
      · exact Or.inl ⟨1,hExpandedFirstOne.trans he.symm⟩
    let protectedObstacle : Set S := (M.cover.branch : Set S) ∪ expandedK
    have hObstacleClosed : IsClosed protectedObstacle :=
      M.cover.branch.finite_toSet.isClosed.union hExpandedKCompact.isClosed
    have hObstacleInside : Disjoint
        (roundedCap '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) protectedObstacle := by
      apply Set.disjoint_left.mpr
      intro x hx ho
      have hxD : x ∈ range roundedCap := Set.image_subset_range _ _ hx
      apply Set.disjoint_left.mp hOpenOffBoundary hx
      apply hEndpointsBoundary
      rcases ho with hm|hk
      · exact hMarks x hxD hm
      · exact hK ⟨hxD,hk⟩
    have hObstacleBoundary : ∀ z ∈ modelCurve,capF z ∈ protectedObstacle → z=capP ∨ z=capQ := by
      intro z hz ho
      have htrace : capF z ∈ range expandedFirst ∪ range orientedRounded := by
        rw [← hCapFA,← hCapFC,← Set.image_union,hCapAC]
        exact Set.mem_image_of_mem capF hz
      have hxD : capF z ∈ range roundedCap := by
        apply Set.image_subset_range _ _
        rw [hRoundedCapBoundary]
        simpa only [hOrientedRoundedRange] using htrace
      have he : capF z ∈ ({originalγ expandedL,originalγ expandedR} : Set S) := by
        rcases ho with hm|hk
        · exact hMarks _ hxD hm
        · exact hK ⟨hxD,hk⟩
      rcases he with he|he
      · exact Or.inl (hCapF.injective (he.trans hCapFP.symm))
      · exact Or.inr (hCapF.injective (he.trans hCapFQ.symm))
    letI : CompactSpace S := M.sphere.symm.compactSpace
    obtain ⟨orientedRoundedMove,hRoundedMoveFix,hRoundedMoveSide⟩ :=
      CurveComplex.actual_raw_bigon_supported_replacement capF hCapF capA capC capP capQ
        hCapA hCapC hCapAC protectedObstacle hObstacleClosed hObstacleBoundary
        (by rwa [hCapFInside])
    have hRoundedMoveMarks : ∀ t x, x ∈ M.cover.branch → orientedRoundedMove.map (t,x)=x :=
      fun t x hx => hRoundedMoveFix t x (Or.inl hx)
    have hRoundedMoveK : orientedRoundedMove.finalMap '' expandedK=expandedK := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        simpa only [AmbientIsotopy.finalMap,hRoundedMoveFix _ _ (Or.inr hy)] using hy
      · intro hx
        exact ⟨x,hx,hRoundedMoveFix 1 x (Or.inr hx)⟩
    have hRoundedMoveActualSide : orientedRoundedMove.finalMap '' range expandedFirst=range orientedRounded := by
      simpa only [hCapFA,hCapFC] using hRoundedMoveSide
    obtain ⟨orientedRoundedHomeomorph,hRoundedHomeomorph⟩ := orientedRoundedMove.homeomorphism_at (1 : Interval)
    have hRoundedHomeomorphMarks : ∀ x, x ∈ M.cover.branch → orientedRoundedHomeomorph x=x :=
      fun x hx => (hRoundedHomeomorph x).trans (hRoundedMoveMarks 1 x hx)
    let carrierArc := a.transport orientedRoundedHomeomorph hRoundedHomeomorphMarks
    have hRoundedFinalHomeomorph : orientedRoundedMove.finalMap=orientedRoundedHomeomorph :=
      funext (fun x => (hRoundedHomeomorph x).symm)
    have hCarrierClass : vertex M carrierArc=vertex M a := by
      apply Eq.symm
      apply Quotient.sound
      refine ⟨orientedRoundedMove,hRoundedMoveMarks,?_⟩
      change orientedRoundedMove.finalMap '' a.val.image=
        (a.val.transport orientedRoundedHomeomorph hRoundedHomeomorphMarks).image
      rw [MarkedArc.transport_image,hRoundedFinalHomeomorph]
    have hCarrierImage : carrierArc.val.image=expandedK ∪ range orientedRounded := by
      change (a.val.transport orientedRoundedHomeomorph hRoundedHomeomorphMarks).image=expandedK ∪ range orientedRounded
      rw [MarkedArc.transport_image,← hRoundedFinalHomeomorph,hExpandedDecomposition,Set.image_union,
        hRoundedMoveActualSide,hRoundedMoveK,Set.union_comm]
    exact ⟨carrierArc,hCarrierClass,by simpa only [hOrientedRoundedRange] using hCarrierImage⟩
  have hRoundedCapBoundaryObstacle :
      (range expandedFirst ∪ range roundedTrace) ∩
        ((M.cover.branch : Set S) ∪ expandedK) ⊆
          ({originalγ expandedL,originalγ expandedR} : Set S) := by
    have hAllPorts : ({cornerA false,cornerA true} : Set S)=
        ({originalγ expandedL,originalγ expandedR} : Set S) := by
      rw [hExpandedLeft,hExpandedRight]
      cases leftPort <;> cases rightPort
      · exact False.elim (hPortsDifferent rfl)
      · rfl
      · exact Set.pair_comm _ _
      · exact False.elim (hPortsDifferent rfl)
    intro x hx
    rcases hx.1 with hfirst|hround
    · rcases hx.2 with hm|hk
      · have he := hExpandedFirstMarks ⟨hfirst,hm⟩
        simpa only [hExpandedLeft,hExpandedRight] using he
      · exact hExpandedMeet ▸ (show x ∈ range expandedFirst ∩ expandedK from ⟨hfirst,hk⟩)
    · rw [← hAllPorts]
      rcases hx.2 with hm|hk
      · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (hRoundedPieces hround)
        have hc := hPiecesMarks k ⟨hk,hm⟩
        rcases hc with hc|hc
        · have hxCorner : x=corner false := hc
          have hcMark : corner false ∈ M.cover.branch := hxCorner ▸ hm
          exact Or.inl (hxCorner.trans (hCornerAMarked false hcMark).symm)
        · have hxCorner : x=corner true := hc
          have hcMark : corner true ∈ M.cover.branch := hxCorner ▸ hm
          exact Or.inr (hxCorner.trans (hCornerAMarked true hcMark).symm)
      · exact hRoundedMeetsA ▸ (show x ∈ range roundedTrace ∩ a.val.image from
          ⟨hround,hExpandedDecomposition.symm ▸ Or.inr hk⟩)
  have hActualCapSupportOfInteriorClearance
      (hInterior : Disjoint
        (roundedCap '' {x | x.val ∈ Metric.ball (0 : Plane) 1})
        ((M.cover.branch : Set S) ∪ expandedK)) :
      (∀ x ∈ range roundedCap,x ∈ M.cover.branch →
        x ∈ ({originalγ expandedL,originalγ expandedR} : Set S)) ∧
      range roundedCap ∩ expandedK ⊆
        ({originalγ expandedL,originalγ expandedR} : Set S) := by
    have hCover : range roundedCap ⊆
        (roundedCap '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) ∪
        (range expandedFirst ∪ range roundedTrace) := by
      rintro x ⟨z,rfl⟩
      by_cases hz : dist z.val (0:Plane)<1
      · exact Or.inl ⟨z,hz,rfl⟩
      · apply Or.inr
        rw [← hRoundedCapBoundary]
        exact ⟨z,le_antisymm z.property (le_of_not_gt hz),rfl⟩
    have hObstacle (x : S) (hx : x ∈ range roundedCap)
        (ho : x ∈ (M.cover.branch : Set S) ∪ expandedK) :
        x ∈ ({originalγ expandedL,originalγ expandedR} : Set S) := by
      rcases hCover hx with hi|hb
      · exact False.elim (Set.disjoint_left.mp hInterior hi ho)
      · exact hRoundedCapBoundaryObstacle ⟨hb,ho⟩
    exact ⟨fun x hx hm => hObstacle x hx (Or.inl hm),
      fun x hx => hObstacle x hx.1 (Or.inr hx.2)⟩
  suffices hActualCapInterior : Disjoint
      (roundedCap '' {x | x.val ∈ Metric.ball (0 : Plane) 1})
      ((M.cover.branch : Set S) ∪ expandedK) by
    obtain ⟨hMarks,hK⟩ := hActualCapSupportOfInteriorClearance hActualCapInterior
    obtain ⟨d,hClass,hImage⟩ := hActualSupportedRoundedFinal hMarks hK
    exact ⟨d,hActualOriginalRoundedConclusion d hClass hImage⟩
  apply Set.disjoint_left.mpr
  rintro x ⟨z,hz,rfl⟩ ho
  have hi := hActualRoundedPlaneDiskOpenInside z hz
  have hs := hActualRoundedJordanInsideSupport hi
  exact Set.disjoint_left.mp hWidePlaneSupportFree hs ho
end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.actual_marked_rounded_side_replacement
