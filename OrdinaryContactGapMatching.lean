import RegionalWeightedMovieDefinitions
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.GapMatchingTools
import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.CornerGeometryTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.DiskExteriorHalfTools

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open CurveComplex.BranchedDoubleCover
open scoped BigOperators
set_option autoImplicit false
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- G0: the existing contact-gap argument with compact obstacles and an explicit side. -/
theorem actual_compact_family_contact_gap_matching
    {X J : Type*} [TopologicalSpace X] [T2Space X] [Fintype J]
    (K : J → Set X) (hK : ∀ j, IsCompact (K j)) (G U : Set X)
    (W : Set (ℝ × ℝ)) (hW : IsOpen W) (e : ↥U ≃ₜ ↥W)
    (A l r B : ℝ) (hAl : A < l) (hlr : l < r) (hrB : r < B)
    (haxis : ∀ x ∈ Icc A B, ∃ y : ↥W, y.val = (x,0) ∧
      ∀ j, (e.symm y).val ∉ K j)
    (hgaxis : ∀ q : ↥U, q.val ∈ G ↔ (e q).val.2 = 0)
    (L R : C(Interval,↥U)) (hL : (e (L 0)).val = (l,0))
    (hR : (e (R 0)).val = (r,0))
    (σ : ℝ) (hσ : σ = -1 ∨ σ = 1)
    (hside : ∀ t : Interval, 0 < t.val →
      0 < σ * (e (L t)).val.2 ∧ 0 < σ * (e (R t)).val.2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : Interval, 0 < t.val → t.val < ρ →
      ∃ q : Path (L t).val (R t).val,
        IsEmbedding q ∧ Disjoint (range q) G ∧
        (∀ j, Disjoint (range q) (K j)) ∧
        ∀ s : Interval, ∃ y : ↥U, y.val = q s ∧
          (e y).val = (1-s.val) • (e (L t)).val + s.val • (e (R t)).val := by
  classical
  have hinverse : Continuous (fun y : ↥W => (e.symm y).val) :=
    continuous_subtype_val.comp e.symm.continuous
  let Q : Set ↥W := {y | ∀ j, (e.symm y).val ∉ K j}
  have hQ : IsOpen Q := by
    have hO (j : J) : IsOpen {y : ↥W | (e.symm y).val ∉ K j} :=
      (hK j).isClosed.isOpen_compl.preimage hinverse
    convert isOpen_iInter_of_finite hO using 1
    ext y
    simp [Q]
  let O : Set (ℝ × ℝ) := Subtype.val '' Q
  have hO : IsOpen O := hW.isOpenMap_subtype_val Q hQ
  let C : Set (ℝ × ℝ) := (fun x : ℝ => (x,0)) '' Icc A B
  have hC : IsCompact C := isCompact_Icc.image (by fun_prop)
  have hCO : C ⊆ O := by
    rintro z ⟨x,hx,rfl⟩
    obtain ⟨y,hy,havoid⟩ := haxis x hx
    exact ⟨y,havoid,hy⟩
  obtain ⟨ε,hε,hclear⟩ := hC.exists_thickening_subset_open hO hCO
  have hsafe (x y : ℝ) (hx : x ∈ Icc A B) (hy : |y| < ε) :
      ∃ hz : (x,y) ∈ W, ∀ j, (e.symm ⟨(x,y),hz⟩).val ∉ K j := by
    have hxy : (x,y) ∈ O := by
      apply hclear
      apply Metric.mem_thickening_iff.mpr
      refine ⟨(x,0),⟨x,hx,rfl⟩,?_⟩
      simpa [Prod.dist_eq,Real.dist_eq] using hy
    obtain ⟨v,hv,hve⟩ := hxy
    have hz : (x,y) ∈ W := hve ▸ v.property
    refine ⟨hz,?_⟩
    have heq : v = ⟨(x,y),hz⟩ := Subtype.ext hve
    rwa [← heq]
  let qL : Interval → ℝ × ℝ := fun t => (e (L t)).val
  let qR : Interval → ℝ × ℝ := fun t => (e (R t)).val
  have hqL : Continuous qL := by dsimp [qL]; fun_prop
  have hqR : Continuous qR := by dsimp [qR]; fun_prop
  let N : Set Interval := {t | A < (qL t).1 ∧ (qL t).1 < (l+r)/2 ∧
      (l+r)/2 < (qR t).1 ∧ (qR t).1 < B ∧
      |(qL t).2| < ε ∧ |(qR t).2| < ε}
  have hN : IsOpen N := by
    exact (isOpen_lt continuous_const hqL.fst).inter
      ((isOpen_lt hqL.fst continuous_const).inter
      ((isOpen_lt continuous_const hqR.fst).inter
      ((isOpen_lt hqR.fst continuous_const).inter
      ((isOpen_lt hqL.snd.abs continuous_const).inter
        (isOpen_lt hqR.snd.abs continuous_const)))))
  have h0N : (0 : Interval) ∈ N := by
    dsimp [N,qL,qR]
    rw [hL,hR]
    simp only [abs_zero]
    exact ⟨hAl,by linarith,by linarith,hrB,hε,hε⟩
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hN 0 h0N
  refine ⟨ρ,hρ,?_⟩
  intro t ht htρ
  have htN : t ∈ N := hball (by
    change dist t (0 : Interval) < ρ
    simpa [Subtype.dist_eq,Real.dist_eq,abs_of_pos ht] using htρ)
  obtain ⟨hAx,hxm,hmy,hyB,hLy,hRy⟩ := htN
  obtain ⟨hLp,hRp⟩ := hside t ht
  let q (s : Interval) : ℝ × ℝ :=
    (1-s.val) • qL t + s.val • qR t
  have hcoord (s : Interval) :
      (q s).1 ∈ Icc A B ∧ 0 < σ * (q s).2 ∧ |(q s).2| < ε := by
    change 0 < σ * (qL t).2 at hLp
    change 0 < σ * (qR t).2 at hRp
    constructor
    · change A ≤ (1-s.val)*(qL t).1+s.val*(qR t).1 ∧
        (1-s.val)*(qL t).1+s.val*(qR t).1 ≤ B
      constructor <;> nlinarith [s.property.1,s.property.2,
        mul_nonneg (sub_nonneg.mpr s.property.2) (show 0 ≤ (qL t).1-A by linarith),
        mul_nonneg s.property.1 (show 0 ≤ (qR t).1-A by linarith),
        mul_nonneg (sub_nonneg.mpr s.property.2) (show 0 ≤ B-(qL t).1 by linarith),
        mul_nonneg s.property.1 (show 0 ≤ B-(qR t).1 by linarith)]
    · constructor
      · change 0 < σ * ((1-s.val)*(qL t).2+s.val*(qR t).2)
        nlinarith [s.property.1,s.property.2,
          mul_nonneg (sub_nonneg.mpr s.property.2) hLp.le,
          mul_nonneg s.property.1 hRp.le]
      · have hLbounds := abs_lt.mp hLy
        have hRbounds := abs_lt.mp hRy
        apply abs_lt.mpr
        change -ε < (1-s.val)*(qL t).2+s.val*(qR t).2 ∧
          (1-s.val)*(qL t).2+s.val*(qR t).2 < ε
        constructor <;> nlinarith [s.property.1,s.property.2,
          mul_nonneg (sub_nonneg.mpr s.property.2) (show 0 ≤ ε-(qL t).2 by linarith),
          mul_nonneg s.property.1 (show 0 ≤ ε-(qR t).2 by linarith),
          mul_nonneg (sub_nonneg.mpr s.property.2) (show 0 ≤ (qL t).2+ε by linarith),
          mul_nonneg s.property.1 (show 0 ≤ (qR t).2+ε by linarith)]
  have hpoint (s : Interval) := hsafe (q s).1 (q s).2 (hcoord s).1 (hcoord s).2.2
  let v : Interval → ↥W := fun s => ⟨q s,(hpoint s).choose⟩
  have hv : Continuous v := (by dsimp [q]; fun_prop : Continuous q).subtype_mk _
  have hv0 : v 0 = e (L t) := by apply Subtype.ext; simp [v,q,qL]
  have hv1 : v 1 = e (R t) := by apply Subtype.ext; simp [v,q,qR]
  let f : Path (L t).val (R t).val := {
    toFun := fun s => (e.symm (v s)).val
    continuous_toFun := hinverse.comp hv
    source' := by simp [hv0]
    target' := by simp [hv1] }
  have hinj : Function.Injective f := by
    intro s u he
    have hev := e.symm.injective (Subtype.ext he)
    have hx := congrArg (fun z : ↥W => z.val.1) hev
    change (1-s.val)*(qL t).1+s.val*(qR t).1 =
      (1-u.val)*(qL t).1+u.val*(qR t).1 at hx
    apply Subtype.ext
    nlinarith
  refine ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro y ⟨s,rfl⟩ hy
    have hz := (hgaxis (e.symm (v s))).mp hy
    rw [e.apply_symm_apply] at hz
    change (q s).2 = 0 at hz
    have hpos := (hcoord s).2.1
    rw [hz,mul_zero] at hpos
    exact lt_irrefl 0 hpos
  · intro j
    apply Set.disjoint_left.mpr
    rintro y ⟨s,rfl⟩ hy
    exact (hpoint s).choose_spec j hy
  · intro s
    exact ⟨e.symm (v s),rfl,congrArg Subtype.val (e.apply_symm_apply (v s))⟩
