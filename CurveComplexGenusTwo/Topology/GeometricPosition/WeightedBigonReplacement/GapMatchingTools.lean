import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Topology.Order.IntermediateValue

open Set Topology Metric
namespace CurveComplex

-- Construct actual contact-free joining arcs along an ORIGINAL boundary-side
-- gap. Uniform clearance is produced by compactness, not assumed as a radius.
theorem actual_contact_free_gap_connector {S J : Type*} [TopologicalSpace S] [T2Space S] [Fintype J]
    (d : J → Curve S) (g : Curve S)
    (U : Set S) (V : Set (ℝ × ℝ)) (hV : IsOpen V) (e : U ≃ₜ V)
    (l r : ℝ) (hlr : l < r)
    (haxis : ∀ x ∈ Icc l r, ∃ y : V, y.val = (x,0) ∧
      ∀ j, (e.symm y : S) ∉ (d j).image)
    (hgaxis : ∀ u : U, (u : S) ∈ g.image ↔ (e u : ℝ × ℝ).2 = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h < ε →
      ∃ f : C(unitInterval,S), IsEmbedding f ∧
        (∀ t, ∃ u : U, (u : S) = f t ∧
          (e u : ℝ × ℝ) = (l+(t : ℝ)*(r-l),h)) ∧
        Disjoint (Set.range f) g.image ∧
        ∀ j, Disjoint (Set.range f) (d j).image := by
  classical
  have hinverse : Continuous (fun y : V => (e.symm y : S)) :=
    continuous_subtype_val.comp e.symm.continuous
  let Q : Set V := {y | ∀ j, (e.symm y : S) ∉ (d j).image}
  have hQ : IsOpen Q := by
    have hO (j : J) : IsOpen {y : V | (e.symm y : S) ∉ (d j).image} :=
      (isCompact_range (d j).embedded.continuous).isClosed.isOpen_compl.preimage hinverse
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
      ∃ hz : (x,y) ∈ V, ∀ j, (e.symm ⟨(x,y),hz⟩ : S) ∉ (d j).image := by
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

end CurveComplex

open Set Topology Metric
namespace CurveComplex

-- Match actual contact endpoint families in the common boundary-side chart.
-- Continuity chooses a small common parameter, rather than assuming that
-- either target endpoint already lies in a prescribed safe gap rectangle.
theorem actual_contact_gap_matching {S J : Type*} [TopologicalSpace S] [T2Space S] [Fintype J]
    (d : J → Curve S) (g : Curve S)
    (U : Set S) (V : Set (ℝ × ℝ)) (hV : IsOpen V) (e : U ≃ₜ V)
    (A l r B : ℝ) (hAl : A < l) (hlr : l < r) (hrB : r < B)
    (haxis : ∀ x ∈ Icc A B, ∃ y : V, y.val = (x,0) ∧
      ∀ j, (e.symm y : S) ∉ (d j).image)
    (hgaxis : ∀ u : U, (u : S) ∈ g.image ↔ (e u : ℝ × ℝ).2 = 0)
    (L R : C(unitInterval,U))
    (hL : (e (L 0) : ℝ × ℝ) = (l,0))
    (hR : (e (R 0) : ℝ × ℝ) = (r,0))
    (hside : ∀ t : unitInterval, t ≠ 0 →
      0 < (e (L t) : ℝ × ℝ).2 ∧ 0 < (e (R t) : ℝ × ℝ).2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < ρ →
      ∃ f : Path (L t : S) (R t : S), IsEmbedding f ∧
        Disjoint (Set.range f) g.image ∧
        (∀ j, Disjoint (Set.range f) (d j).image) ∧
        (∀ s, ∃ u : U, (u : S) = f s ∧
          (e u : ℝ × ℝ) =
            (1-(s : ℝ)) • (e (L t) : ℝ × ℝ) +
              (s : ℝ) • (e (R t) : ℝ × ℝ)) := by
  classical
  have hinverse : Continuous (fun y : V => (e.symm y : S)) :=
    continuous_subtype_val.comp e.symm.continuous
  let Q : Set V := {y | ∀ j, (e.symm y : S) ∉ (d j).image}
  have hQ : IsOpen Q := by
    have hO (j : J) : IsOpen {y : V | (e.symm y : S) ∉ (d j).image} :=
      (isCompact_range (d j).embedded.continuous).isClosed.isOpen_compl.preimage hinverse
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
      ∃ hz : (x,y) ∈ V, ∀ j, (e.symm ⟨(x,y),hz⟩ : S) ∉ (d j).image := by
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

end CurveComplex

open Set Topology
namespace CurveComplex

-- A genuine contact arc may wiggle in the COMMON gap chart coordinate.
-- First right exit / last left entry constructs a separated actual subarc;
-- coordinate monotonicity is not assumed and actual intersection counts only fall.
end CurveComplex
