import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteSurfaceReplacement
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.GapMatchingTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualChartArcTools
import Mathlib.Topology.Order.IntermediateValue
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.DiskExteriorHalfTools
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000
theorem actual_marked_contact_free_gap_connector
    (M : HyperellipticModel E S) [T2Space S] {J : Type} [Fintype J]
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

theorem actual_marked_contact_gap_matching
    (M : HyperellipticModel E S) [T2Space S] {J : Type} [Fintype J]
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

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
theorem hMarkedUniformContactPatch (M : HyperellipticModel E S) [T2Space S] {J : Type} [Fintype J]
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
    (∀ u ∈ Icc (-δ) δ, Plane.mk u 0 ∈ F.target) ∧
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
  have hAxisTarget (u : ℝ) (hu : u ∈ Icc (-δ) δ) : Plane.mk u 0 ∈ F.target := by
    apply hball
    apply (convex_ball (0 : Plane) η).segment_subset hleft0 hright0
    rw [segment_eq_image']
    refine ⟨(u+δ)/(2*δ),⟨?_,?_⟩,?_⟩
    · exact div_nonneg (by linarith [hu.1]) (by positivity)
    · apply (div_le_one (by positivity : 0 < 2*δ)).mpr
      linarith [hu.2]
    · ext i
      fin_cases i
      · change -δ+(u+δ)/(2*δ)*(δ- -δ) = u
        field_simp
        ring
      · simp
  refine ⟨δ,H,hδ,hH,hball hleft0,hball hright0,hAxisTarget,?_,?_⟩
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

theorem hMarkedPositiveHalfChoice (M : HyperellipticModel E S) [T2Space S]
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

theorem hMarkedMirrorPositiveCore (M : HyperellipticModel E S) [T2Space S] {J : Type}
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

theorem hMarkedCommonBankUniformPatch (M : HyperellipticModel E S) [T2Space S] {D : Type} [Fintype D]
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
      p ∈ G.source ∧ G p = 0 ∧
      (∀ x ∈ G.source, x ∈ c.val.image ↔ G x 1 = 0) ∧
      (∃ a' b' : D → Plane, (∀ j, 0 < a' j 1) ∧ (∀ j, b' j 1 < 0) ∧
        ∀ j x, x ∈ G.source →
          (x ∈ (d j).val.image ↔ G x ∈ segment ℝ (0:Plane) (a' j) ∪ segment ℝ (0:Plane) (b' j))) ∧
      G.source ⊆ F.source ∧ 0 < δ ∧ 0 < H ∧
      Plane.mk (-δ) 0 ∈ G.target ∧ Plane.mk δ 0 ∈ G.target ∧
    (∀ u ∈ Icc (-δ) δ, Plane.mk u 0 ∈ G.target) ∧
      (∀ h : ℝ, 0 < h → h < H → segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ G.target) ∧
      ∀ h : ℝ, 0 < h → h < H → ∃ f : C(Interval,S),
        IsEmbedding f ∧ range f ⊆ G.source ∧
        range f=G.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
        f 0=G.symm (Plane.mk (-δ) h) ∧ f 1=G.symm (Plane.mk δ h) ∧
        (∀ x ∈ range f, 0 < E x 1) ∧
        Disjoint (range f) (M.cover.branch : Set S) ∧ Disjoint (range f) c.val.image ∧
        ∀ j, f 0 ∉ (d j).val.image ∧ f 1 ∉ (d j).val.image ∧
          (range f ∩ (d j).val.image).Finite ∧ (range f ∩ (d j).val.image).ncard ≤ 1 := by
  obtain ⟨σ,hσ,hpos⟩ := hMarkedPositiveHalfChoice M c p E F hFE hp hFp hEp ρ η hη hball hEaxis haxis
  obtain ⟨F',a',b',hs,hp',hball',haxis',ha',hb',hmodel',hpos'⟩ :=
    hMarkedMirrorPositiveCore M E F c p hFp ρ η a b hball haxis ha hb d hmodel σ hσ hpos
  let G := F'.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0:Plane) η) isOpen_ball)
  have hGs : G.source=F'.source ∩ F' ⁻¹' Metric.ball (0:Plane) η := by
    simp [G]
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
  obtain ⟨δ,H,hδ,hH,hleft0,hright0,hAxisTarget,hsegments,hpatch⟩ := hMarkedUniformContactPatch M d c G hGmark ζ hζ hζball
    hGaxis a' b' ha' hb' hGmodel
  have hTotalModel (j : D) (x : S) (hx : x ∈ G.source) :
      x ∈ (d j).val.image ↔ G x ∈ segment ℝ (0:Plane) (a' j) ∪ segment ℝ (0:Plane) (b' j) := by
    have hh := hGs ▸ hx
    exact hmodel' j x hh.1 (by simpa [Metric.mem_ball,dist_zero_right] using (hball' hh.2).2)
  refine ⟨G,δ,H,hpG,?_,hGaxis,⟨a',b',ha',hb',hTotalModel⟩,
    hGsub,hδ,hH,hleft0,hright0,hAxisTarget,hsegments,?_⟩
  · rw [hGval,hp']
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
end CurveComplex.HyperellipticModel


namespace CurveComplex
open Set Topology Schoenflies LocalSurgery
set_option maxHeartbeats 5000000

/-- Embedded disk density, extracted from the existing actual bigon proof. -/
theorem actual_embedded_disk_closure_interior
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (d : C(Metric.closedBall (0 : Plane) 1,S)) (hd : IsEmbedding d) :
    closure (interior (Set.range d)) = Set.range d := by
  let A : Set (Metric.closedBall (0 : Plane) 1) :=
    {x | x.val ∈ Metric.ball (0 : Plane) 1}
  have himage : Subtype.val '' A = Metric.ball (0 : Plane) 1 := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx; exact ⟨⟨x,Metric.ball_subset_closedBall hx⟩,hx,rfl⟩
  have hclosure : closure A = Set.univ := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, himage,
      closure_ball (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)]
    ext x
    simp only [Set.mem_preimage,Set.mem_univ,iff_true]
    exact x.property
  have hrange : Set.range d ⊆ closure (d '' A) := by
    rw [← Set.image_univ,← hclosure]
    exact image_closure_subset_closure_image d.continuous
  have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
  rw [embedded_surface_disk_interior_eq d hd]
  apply Set.Subset.antisymm
  · exact closure_minimal (Set.image_subset_range _ _) hclosed
  · exact hrange

/-- The actual disk, rather than an arbitrary chart orientation, selects the interior bank. -/
theorem actual_embedded_disk_chart_strip_interior_half
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (d : C(Metric.closedBall (0 : Plane) 1,S)) (hd : IsEmbedding d)
    (E : OpenPartialHomeomorph S Plane) (L R ε : ℝ) (hLR : L < R) (hε : 0 < ε)
    (hTarget : {z : Plane | L < z 0 ∧ z 0 < R ∧ -ε < z 1 ∧ z 1 < ε} ⊆ E.target)
    (hFrontier : ∀ z : Plane, L < z 0 → z 0 < R → -ε < z 1 → z 1 < ε →
      (E.symm z ∈ frontier (Set.range d) ↔ z 1 = 0)) :
    ∃ τ : ℝ, (τ = -1 ∨ τ = 1) ∧ ∀ z : Plane,
      L < z 0 → z 0 < R → -ε < z 1 → z 1 < ε → z 1 ≠ 0 →
      (E.symm z ∈ interior (Set.range d) ↔ 0 < τ*z 1) := by
  have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
  have hregular : Set.range d ⊆ closure (interior (Set.range d)) := by
    rw [actual_embedded_disk_closure_interior d hd]
  obtain ⟨σ,hσ,hside⟩ := actual_chart_strip_exterior_half E (Set.range d)
    hclosed hregular L R ε hLR hε hTarget hFrontier
  refine ⟨-σ,?_,?_⟩
  · rcases hσ with rfl | rfl <;> norm_num
  · intro z hL hR hlo hhi hy
    have hfront : E.symm z ∉ frontier (Set.range d) := by
      intro hf
      exact hy ((hFrontier z hL hR hlo hhi).mp hf)
    have hinside : E.symm z ∈ interior (Set.range d) ↔ E.symm z ∈ Set.range d := by
      constructor
      · intro hx; exact interior_subset hx
      · intro hz
        by_contra hn
        exact hfront (hclosed.frontier_eq ▸ ⟨hz,hn⟩)
    rw [hinside]
    have hsidez := hside z hL hR hlo hhi hy
    rcases hσ with rfl | rfl <;> simp only [neg_neg,neg_one_mul,one_mul] at *
    all_goals constructor
    · intro hz
      have hn : ¬ 0 < -z 1 := fun hn => (hsidez.mpr hn) hz
      have hle : 0 ≤ z 1 := by linarith
      exact lt_of_le_of_ne hle (Ne.symm hy)
    · intro hz
      by_contra hn
      have hs := hsidez.mp hn
      linarith
    · intro hz
      have hn : ¬ 0 < z 1 := fun hn => (hsidez.mpr hn) hz
      have hle : z 1 ≤ 0 := le_of_not_gt hn
      have hlt : z 1 < 0 := lt_of_le_of_ne hle hy
      linarith
    · intro hz
      by_contra hn
      have hs := hsidez.mp hn
      linarith

/-- Normalize the chart bank to the actual disk interior, preserving its horizontal coordinate. -/
theorem actual_embedded_disk_signed_interior_chart
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (d : C(Metric.closedBall (0 : Plane) 1,S)) (hd : IsEmbedding d)
    (E : OpenPartialHomeomorph S Plane) (L R ε : ℝ) (hLR : L < R) (hε : 0 < ε)
    (hTarget : {z : Plane | L < z 0 ∧ z 0 < R ∧ -ε < z 1 ∧ z 1 < ε} ⊆ E.target)
    (hFrontier : ∀ z : Plane, L < z 0 → z 0 < R → -ε < z 1 → z 1 < ε →
      (E.symm z ∈ frontier (Set.range d) ↔ z 1 = 0)) :
    ∃ F : OpenPartialHomeomorph S Plane, F.source = E.source ∧
      (∀ x, F x 0 = E x 0) ∧
      (∀ x, F x 1 = E x 1 ∨ F x 1 = -E x 1) ∧
      ∀ x ∈ F.source, L < E x 0 → E x 0 < R → -ε < E x 1 → E x 1 < ε →
        (x ∈ interior (Set.range d) ↔ 0 < F x 1) := by
  obtain ⟨τ,hτ,hinside⟩ := actual_embedded_disk_chart_strip_interior_half
    d hd E L R ε hLR hε hTarget hFrontier
  let N : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk (z 0) (-z 1)
    invFun := fun z => Plane.mk (z 0) (-z 1)
    left_inv := by intro z; ext i; fin_cases i <;> simp
    right_inv := by intro z; ext i; fin_cases i <;> simp
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hzero (x : S) (hx : x ∈ E.source)
      (hL : L < E x 0) (hR : E x 0 < R) (hlo : -ε < E x 1) (hhi : E x 1 < ε)
      (hy : E x 1 = 0) : x ∉ interior (Set.range d) := by
    have hf := (hFrontier (E x) hL hR hlo hhi).mpr hy
    rw [E.left_inv hx] at hf
    intro hi
    have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
    exact (hclosed.frontier_eq ▸ hf).2 hi
  rcases hτ with rfl | rfl
  · let F := E.transHomeomorph N
    have hs : F.source = E.source := rfl
    have hval (x : S) : F x 1 = -E x 1 := rfl
    refine ⟨F,hs,fun x => rfl,fun x => Or.inr (hval x),?_⟩
    intro x hx hL hR hlo hhi
    rw [hval]
    by_cases hy : E x 1 = 0
    · have hn := hzero x (hs ▸ hx) hL hR hlo hhi hy
      simp [hy,hn]
    · have hi := hinside (E x) hL hR hlo hhi hy
      rw [E.left_inv (hs ▸ hx)] at hi
      simpa only [neg_one_mul] using hi
  · refine ⟨E,rfl,fun x => rfl,fun x => Or.inl rfl,?_⟩
    intro x hx hL hR hlo hhi
    by_cases hy : E x 1 = 0
    · have hn := hzero x hx hL hR hlo hhi hy
      simp [hy,hn]
    · have hi := hinside (E x) hL hR hlo hhi hy
      rw [E.left_inv hx] at hi
      simpa only [one_mul] using hi

end CurveComplex

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies CurveComplex.LocalSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_marked_two_side_disk_interior_bank
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (B : ActualMarkedTwoSideDisk M a b)
    (F0 : OpenPartialHomeomorph S Plane) (L R ε : ℝ) (hLR : L < R) (hε : 0 < ε)
    (hTarget : {z : Plane | L < z 0 ∧ z 0 < R ∧ -ε < z 1 ∧ z 1 < ε} ⊆ F0.target)
    (hFirstFree : Disjoint F0.source (range B.firstSide))
    (hSideLocal : ∀ x ∈ F0.source, x ∈ b.val.image ↔ x ∈ range B.secondSide)
    (hAxis : ∀ x ∈ F0.source, x ∈ b.val.image ↔ F0 x 1 = 0) :
    ∃ F : OpenPartialHomeomorph S Plane, F.source = F0.source ∧
      (∀ x, F x 0 = F0 x 0) ∧
      (∀ x, F x 1 = F0 x 1 ∨ F x 1 = -F0 x 1) ∧
      (∀ x ∈ F.source, x ∈ b.val.image ↔ F x 1 = 0) ∧
      ∀ x ∈ F.source, L < F0 x 0 → F0 x 0 < R → -ε < F0 x 1 → F0 x 1 < ε →
        (x ∈ B.openInterior ↔ 0 < F x 1) := by
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
  have hfront : frontier (range B.disk) = range B.firstSide ∪ range B.secondSide := by
    have hclosed : IsClosed (range B.disk) := (isCompact_range B.disk.continuous).isClosed
    rw [hclosed.frontier_eq,embedded_surface_disk_interior_eq B.disk B.disk_embedded,← B.boundary_eq]
    ext p
    constructor
    · rintro ⟨⟨x,rfl⟩,hxnot⟩
      refine ⟨x,?_,rfl⟩
      have hxle : dist x.val (0 : Plane) ≤ 1 := x.property
      have hxge : 1 ≤ dist x.val (0 : Plane) := by
        by_contra hn
        exact hxnot ⟨x,lt_of_not_ge hn,rfl⟩
      exact le_antisymm hxle hxge
    · rintro ⟨x,hx,rfl⟩
      refine ⟨⟨x,rfl⟩,?_⟩
      rintro ⟨y,hy,he⟩
      have hxy := B.disk_embedded.injective he
      subst y
      change dist x.val (0 : Plane) < 1 at hy
      change dist x.val (0 : Plane) = 1 at hx
      linarith
  have hFrontier (z : Plane) (hL : L < z 0) (hR : z 0 < R)
      (hlo : -ε < z 1) (hhi : z 1 < ε) :
      F0.symm z ∈ frontier (range B.disk) ↔ z 1 = 0 := by
    have hzT := hTarget ⟨hL,hR,hlo,hhi⟩
    have hzS := F0.map_target hzT
    rw [hfront]
    constructor
    · rintro (hfirst|hsecond)
      · exact False.elim (Set.disjoint_left.mp hFirstFree hzS hfirst)
      · have hy := (hAxis _ hzS).mp ((hSideLocal _ hzS).mpr hsecond)
        rwa [F0.right_inv hzT] at hy
    · intro hy
      right
      apply (hSideLocal _ hzS).mp
      apply (hAxis _ hzS).mpr
      rw [F0.right_inv hzT]
      exact hy
  obtain ⟨F,hs,hx,hy,hi⟩ := CurveComplex.actual_embedded_disk_signed_interior_chart
    B.disk B.disk_embedded F0 L R ε hLR hε hTarget hFrontier
  refine ⟨F,hs,hx,hy,?_,?_⟩
  · intro x hxS
    rw [hAxis x (hs ▸ hxS)]
    rcases hy x with he|he <;> rw [he] <;> simp
  · intro x hxS hL hR hlo hhi
    have hh := hi x hxS hL hR hlo hhi
    rw [embedded_surface_disk_interior_eq B.disk B.disk_embedded] at hh
    exact hh
end CurveComplex.HyperellipticModel

namespace CurveComplex
open Set Topology Schoenflies
set_option maxHeartbeats 5000000

theorem actual_chart_axis_baselines_bracket_side_parameter
    {S : Type} [TopologicalSpace S]
    (side : C(Interval,S)) (hside : IsEmbedding side)
    (F : OpenPartialHomeomorph S Plane) (δ : ℝ) (hδ : 0 < δ)
    (t0 : Interval) (ht0 : side t0 ∈ F.source) (hF0 : F (side t0) = 0)
    (hTarget : ∀ u ∈ Icc (-δ) δ, Plane.mk u 0 ∈ F.target)
    (hAxisSide : ∀ u ∈ Icc (-δ) δ, F.symm (Plane.mk u 0) ∈ range side) :
    ∃ u v : Interval, u < t0 ∧ t0 < v ∧
      ((side u = F.symm (Plane.mk (-δ) 0) ∧ side v = F.symm (Plane.mk δ 0)) ∨
       (side u = F.symm (Plane.mk δ 0) ∧ side v = F.symm (Plane.mk (-δ) 0))) := by
  classical
  letI : Fact ((-δ : ℝ) ≤ δ) := ⟨by linarith⟩
  let A := Icc (-δ) δ
  let q : A → Plane := fun u => Plane.mk u.val 0
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hInv : Continuous (fun u : A => F.symm (q u)) :=
    F.symm.continuousOn.comp_continuous hq (fun u => hTarget u.val u.property)
  let lift : A → range side := fun u => ⟨F.symm (q u),hAxisSide u.val u.property⟩
  have hLift : Continuous lift := hInv.subtype_mk _
  let β : A → Interval := fun u => hside.toHomeomorph.symm (lift u)
  have hβ : Continuous β := hside.toHomeomorph.symm.continuous.comp hLift
  have hβSide (u : A) : side (β u) = F.symm (q u) :=
    congrArg Subtype.val (hside.toHomeomorph.apply_symm_apply (lift u))
  have hβinj : Function.Injective β := by
    intro u v he
    have he' : F.symm (q u) = F.symm (q v) := (hβSide u).symm.trans ((congrArg side he).trans (hβSide v))
    have heq := F.symm.injOn (hTarget u.val u.property) (hTarget v.val v.property) he'
    apply Subtype.ext
    exact congrArg (fun z : Plane => z 0) heq
  let l : A := ⟨-δ,le_rfl,by linarith⟩
  let z : A := ⟨0,by constructor <;> linarith⟩
  let r : A := ⟨δ,by linarith,le_rfl⟩
  have hβ0 : β z = t0 := by
    apply hside.injective
    rw [hβSide]
    change F.symm (Plane.mk 0 0) = side t0
    have hz : Plane.mk (0:ℝ) 0 = (0:Plane) := by ext i; fin_cases i <;> rfl
    rw [hz,← hF0,F.left_inv ht0]
  have hlz : l < z := by change -δ < 0; linarith
  have hzr : z < r := hδ
  rcases hβ.strictMono_of_inj_boundedOrder' hβinj with hm | ha
  · refine ⟨β l,β r,?_,?_,Or.inl ⟨hβSide l,hβSide r⟩⟩
    · rw [← hβ0]; exact hm hlz
    · rw [← hβ0]; exact hm hzr
  · refine ⟨β r,β l,?_,?_,Or.inr ⟨hβSide r,hβSide l⟩⟩
    · rw [← hβ0]; exact ha hzr
    · rw [← hβ0]; exact ha hlz

theorem actual_chart_axis_baselines_inside_side_core
    {S : Type} [TopologicalSpace S]
    (side : C(Interval,S)) (hside : IsEmbedding side)
    (F : OpenPartialHomeomorph S Plane) (δ : ℝ) (hδ : 0 < δ)
    (t0 : Interval) (ht0 : side t0 ∈ F.source) (hF0 : F (side t0) = 0)
    (hTarget : ∀ u ∈ Icc (-δ) δ, Plane.mk u 0 ∈ F.target)
    (hAxisSide : ∀ u ∈ Icc (-δ) δ, F.symm (Plane.mk u 0) ∈ range side)
    (coreLeft coreRight : ℝ)
    (hLocal : ∀ t : Interval, side t ∈ F.source → coreLeft < t.val ∧ t.val < coreRight) :
    ∃ u v : Interval, coreLeft < u.val ∧ u < t0 ∧ t0 < v ∧ v.val < coreRight ∧
      ((side u = F.symm (Plane.mk (-δ) 0) ∧ side v = F.symm (Plane.mk δ 0)) ∨
       (side u = F.symm (Plane.mk δ 0) ∧ side v = F.symm (Plane.mk (-δ) 0))) := by
  obtain ⟨u,v,hu,hv,he⟩ := actual_chart_axis_baselines_bracket_side_parameter
    side hside F δ hδ t0 ht0 hF0 hTarget hAxisSide
  have hleft := F.map_target (hTarget (-δ) ⟨le_rfl,by linarith⟩)
  have hright := F.map_target (hTarget δ ⟨by linarith,le_rfl⟩)
  have hSources : side u ∈ F.source ∧ side v ∈ F.source := by
    rcases he with ⟨heU,heV⟩|⟨heU,heV⟩
    · rw [heU,heV]; exact ⟨hleft,hright⟩
    · rw [heU,heV]; exact ⟨hright,hleft⟩
  exact ⟨u,v,(hLocal u hSources.1).1,hu,hv,(hLocal v hSources.2).2,he⟩
end CurveComplex
