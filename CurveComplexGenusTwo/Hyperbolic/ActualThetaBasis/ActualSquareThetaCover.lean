import Mathlib
open Set Topology
namespace CurveComplex.Hyperbolic.PantsTheta
abbrev ActualSquareTheta := {z : ℝ × ℝ //
  ((-1 ≤ z.1 ∧ z.1 ≤ 1) ∧ (z.2 = -1 ∨ z.2 = 1)) ∨
  ((z.1 = -1 ∨ z.1 = 0 ∨ z.1 = 1) ∧ (-1 ≤ z.2 ∧ z.2 ≤ 1))}
noncomputable def thetaBase : ActualSquareTheta := ⟨(-1,0),by norm_num⟩
noncomputable def thetaVertex (outer : Bool) (i : Fin 6) : ActualSquareTheta :=
  ⟨match i.val with
    | 0 => (-1,0)
    | 1 => (-1,-1)
    | 2 => (if outer then 1 else 0,-1)
    | 3 => (if outer then 1 else 0,1)
    | 4 => (-1,1)
    | _ => (-1,0),by fin_cases i <;> cases outer <;> norm_num⟩
noncomputable def thetaLeg (outer : Bool) (i : Fin 5) :
    Path (thetaVertex outer i.castSucc) (thetaVertex outer i.succ) where
  toFun t := ⟨((1-t.val)*(thetaVertex outer i.castSucc).val.1 +
      t.val*(thetaVertex outer i.succ).val.1,
    (1-t.val)*(thetaVertex outer i.castSucc).val.2 +
      t.val*(thetaVertex outer i.succ).val.2),by
    have h0 := t.property.1
    have h1 := t.property.2
    fin_cases i <;> cases outer <;> simp [thetaVertex] <;> ring_nf <;>
      aesop (add safe tactic (by linarith))⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext;ext <;> simp
  target' := by apply Subtype.ext;ext <;> simp
noncomputable def thetaLoop (outer : Bool) : Path thetaBase thetaBase :=
  (Path.concat (thetaVertex outer) (thetaLeg outer)).cast (by rfl) (by rfl)

abbrev ThetaLowerStar := {z : ActualSquareTheta // z.val.2 < (1/2 : ℝ)}
abbrev ThetaUpperStar := {z : ActualSquareTheta // -(1/2 : ℝ) < z.val.2}

theorem actualTheta_bounds (z : ActualSquareTheta) :
    (-1 ≤ z.val.1 ∧ z.val.1 ≤ 1) ∧ (-1 ≤ z.val.2 ∧ z.val.2 ≤ 1) := by
  rcases z.property with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨hx, by rcases hy with h | h <;> rw [h] <;> norm_num⟩
  · exact ⟨by rcases hx with h | h | h <;> rw [h] <;> norm_num, hy⟩

theorem thetaLowerStar_move_mem (z : ThetaLowerStar) (u v : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (hphase : u = 1 ∨ v = 0) :
    (((-1 ≤ (1-v)*z.val.val.1 ∧ (1-v)*z.val.val.1 ≤ 1) ∧
      ((1-u)*z.val.val.2-u = -1 ∨ (1-u)*z.val.val.2-u = 1)) ∨
      (((1-v)*z.val.val.1 = -1 ∨ (1-v)*z.val.val.1 = 0 ∨
          (1-v)*z.val.val.1 = 1) ∧
        (-1 ≤ (1-u)*z.val.val.2-u ∧ (1-u)*z.val.val.2-u ≤ 1))) ∧
      (1-u)*z.val.val.2-u < (1/2 : ℝ) := by
  have hb := actualTheta_bounds z.val
  have hylo : -1 ≤ (1-u)*z.val.val.2-u := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-u) (by linarith : 0 ≤ z.val.val.2+1)]
  have hyhi : (1-u)*z.val.val.2-u ≤ z.val.val.2 := by nlinarith [mul_nonneg hu.1 (by linarith : 0 ≤ z.val.val.2+1)]
  refine ⟨?_, lt_of_le_of_lt hyhi z.property⟩
  rcases hphase with rfl | rfl
  · left
    constructor
    · constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ 1-v) (by linarith : 0 ≤ z.val.val.1+1),
        mul_nonneg (by linarith : 0 ≤ 1-v) (by linarith : 0 ≤ 1-z.val.val.1)]
    · left; ring
  · simp only [sub_zero, one_mul]
    rcases z.val.property with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · left
      refine ⟨hx, Or.inl ?_⟩
      rcases hy with hy | hy
      · rw [hy]; ring
      · have hz := z.property; rw [hy] at hz; norm_num at hz
    · exact Or.inr ⟨hx, hylo, hyhi.trans hy.2⟩

noncomputable def thetaLowerCenter : ThetaLowerStar :=
  ⟨⟨(0,-1), by norm_num⟩, by norm_num⟩

noncomputable def thetaLowerContraction :
    ContinuousMap.Homotopy (ContinuousMap.id ThetaLowerStar)
      (ContinuousMap.const ThetaLowerStar thetaLowerCenter) where
  toFun p :=
    let u := min (2*p.1.val) 1
    let v := max (2*p.1.val-1) 0
    let h := thetaLowerStar_move_mem p.2 u v
      ⟨le_min (by linarith [p.1.property.1]) (by norm_num), min_le_right _ _⟩
      ⟨le_max_right _ _, max_le (by linarith [p.1.property.2]) (by norm_num)⟩
      (by
        by_cases hp : 2*p.1.val ≤ 1
        · right; exact max_eq_right (by linarith)
        · left; exact min_eq_right (by linarith))
    ⟨⟨((1-v)*p.2.val.val.1, (1-u)*p.2.val.val.2-u), h.1⟩, h.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous (fun p : unitInterval × ThetaLowerStar =>
      ((1-max (2*p.1.val-1) 0)*p.2.val.val.1,
        (1-min (2*p.1.val) 1)*p.2.val.val.2-min (2*p.1.val) 1))
    fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Subtype.ext
    ext <;> simp
  map_one_left z := by
    apply Subtype.ext
    apply Subtype.ext
    ext <;> norm_num [thetaLowerCenter]

theorem thetaLowerStar_contractible : ContractibleSpace ThetaLowerStar := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  exact ⟨thetaLowerCenter, ⟨thetaLowerContraction⟩⟩

noncomputable def thetaVerticalReflection : ActualSquareTheta ≃ₜ ActualSquareTheta where
  toFun z := ⟨(z.val.1, -z.val.2), by
    rcases z.property with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · left; refine ⟨hx, ?_⟩
      rcases hy with h | h
      · right; norm_num [h]
      · left; norm_num [h]
    · right; exact ⟨hx, by constructor <;> linarith⟩⟩
  invFun z := ⟨(z.val.1, -z.val.2), by
    rcases z.property with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · left; refine ⟨hx, ?_⟩
      rcases hy with h | h
      · right; norm_num [h]
      · left; norm_num [h]
    · right; exact ⟨hx, by constructor <;> linarith⟩⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def thetaStarsReflection : ThetaUpperStar ≃ₜ ThetaLowerStar where
  toFun z := ⟨thetaVerticalReflection z.val, by change -z.val.val.2 < (1/2 : ℝ); linarith [z.property]⟩
  invFun z := ⟨thetaVerticalReflection.symm z.val, by change -(1/2 : ℝ) < -z.val.val.2; linarith [z.property]⟩
  left_inv z := by apply Subtype.ext; exact thetaVerticalReflection.symm_apply_apply _
  right_inv z := by apply Subtype.ext; exact thetaVerticalReflection.apply_symm_apply _
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem thetaUpperStar_contractible : ContractibleSpace ThetaUpperStar := by
  let := thetaLowerStar_contractible
  exact thetaStarsReflection.contractibleSpace

def thetaStarOpen (upper : Bool) : Set ActualSquareTheta :=
  if upper then {z | -(1/2 : ℝ) < z.val.2} else {z | z.val.2 < (1/2 : ℝ)}

theorem thetaStarOpen_isOpen (upper : Bool) : IsOpen (thetaStarOpen upper) := by
  cases upper
  · exact isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const
  · exact isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)

theorem thetaStarOpen_cover : (⋃ upper : Bool, thetaStarOpen upper) = univ := by
  apply eq_univ_of_forall
  intro z
  by_cases hz : z.val.2 < (1/2 : ℝ)
  · exact mem_iUnion.mpr ⟨false, hz⟩
  · exact mem_iUnion.mpr ⟨true, by change -(1/2 : ℝ) < z.val.2; linarith⟩

abbrev ThetaStar (upper : Bool) := {z : ActualSquareTheta // z ∈ thetaStarOpen upper}

theorem thetaStar_contractible (upper : Bool) : ContractibleSpace (ThetaStar upper) := by
  cases upper
  · exact thetaLowerStar_contractible
  · exact thetaUpperStar_contractible

noncomputable def thetaStarLiftPath (upper : Bool) {a b : ActualSquareTheta}
    (ha : a ∈ thetaStarOpen upper) (hb : b ∈ thetaStarOpen upper)
    (p : Path a b) (hp : ∀ t, p t ∈ thetaStarOpen upper) :
    Path (⟨a,ha⟩ : ThetaStar upper) (⟨b,hb⟩ : ThetaStar upper) where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk hp
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

theorem thetaStar_paths_homotopic (upper : Bool) {a b : ActualSquareTheta}
    (ha : a ∈ thetaStarOpen upper) (hb : b ∈ thetaStarOpen upper)
    (p q : Path a b) (hp : ∀ t, p t ∈ thetaStarOpen upper)
    (hq : ∀ t, q t ∈ thetaStarOpen upper) : p.Homotopic q := by
  let := thetaStar_contractible upper
  have h := SimplyConnectedSpace.paths_homotopic
    (thetaStarLiftPath upper ha hb p hp) (thetaStarLiftPath upper ha hb q hq)
  exact h.map ⟨Subtype.val, continuous_subtype_val⟩

abbrev ThetaOverlap :=
  {z : ActualSquareTheta // -(1/2 : ℝ) < z.val.2 ∧ z.val.2 < (1/2 : ℝ)}
abbrev ThetaBranchCoordinate := {x : ℝ // x = -1 ∨ x = 0 ∨ x = 1}

theorem thetaOverlap_branch (z : ThetaOverlap) :
    z.val.val.1 = -1 ∨ z.val.val.1 = 0 ∨ z.val.val.1 = 1 := by
  rcases z.val.property with ⟨_, hy⟩ | ⟨hx, _⟩
  · rcases hy with hy | hy <;> have hz := z.property <;> rw [hy] at hz <;> linarith
  · exact hx

noncomputable def thetaOverlapProduct :
    ThetaOverlap ≃ₜ ThetaBranchCoordinate × Ioo (-(1/2 : ℝ)) (1/2) where
  toFun z := (⟨z.val.val.1, thetaOverlap_branch z⟩, ⟨z.val.val.2, z.property⟩)
  invFun p := ⟨⟨(p.1.val,p.2.val), Or.inr ⟨p.1.property,
    by
      have h0 := p.2.property.1
      have h1 := p.2.property.2
      constructor <;> dsimp <;> linarith⟩⟩, p.2.property⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv p := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem thetaBranchCoordinate_finite : Finite ThetaBranchCoordinate := by
  have h : Set.Finite {x : ℝ | x = -1 ∨ x = 0 ∨ x = 1} := by
    convert (Set.finite_singleton (1 : ℝ)).insert 0 |>.insert (-1) using 1
    ext x
    simp
  exact h.to_subtype

noncomputable def thetaOverlapVerticalPath (a b : ThetaOverlap)
    (hx : a.val.val.1 = b.val.val.1) : Path a b where
  toFun t := ⟨⟨(a.val.val.1,(1-t.val)*a.val.val.2+t.val*b.val.val.2),
    Or.inr ⟨thetaOverlap_branch a, by
      simpa only [smul_eq_mul, mem_Icc] using
        (convex_Icc (-1 : ℝ) 1) (actualTheta_bounds a.val).2
          (actualTheta_bounds b.val).2 (sub_nonneg.mpr t.property.2)
          t.property.1 (by ring : (1-t.val)+t.val=1)⟩⟩, by
      simpa only [smul_eq_mul, mem_Ioo] using
        (convex_Ioo (-(1/2 : ℝ)) (1/2)) a.property b.property
          (sub_nonneg.mpr t.property.2) t.property.1
          (by ring : (1-t.val)+t.val=1)⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; apply Subtype.ext; ext <;> simp
  target' := by apply Subtype.ext; apply Subtype.ext; ext <;> simp [hx]

theorem thetaPath_star_subdivision {a b : ActualSquareTheta} (p : Path a b) :
    ∃ t : ℕ → unitInterval, t 0 = 0 ∧ Monotone t ∧
      (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n, ∃ upper : Bool,
        ∀ s ∈ Icc (t n) (t (n+1)), p s ∈ thetaStarOpen upper := by
  apply exists_monotone_Icc_subset_open_cover_unitInterval
    (c := fun upper => p ⁻¹' thetaStarOpen upper)
  · intro upper
    exact (thetaStarOpen_isOpen upper).preimage p.continuous
  · intro s _
    have hs : p s ∈ ⋃ upper : Bool, thetaStarOpen upper := by rw [thetaStarOpen_cover]; trivial
    simpa only [mem_iUnion, mem_preimage] using hs

theorem thetaHomotopy_star_grid (H : C(unitInterval × unitInterval, ActualSquareTheta)) :
    ∃ t : ℕ → unitInterval, t 0 = 0 ∧ Monotone t ∧
      (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n m, ∃ upper : Bool,
        ∀ s ∈ Icc (t n) (t (n+1)) ×ˢ Icc (t m) (t (m+1)),
          H s ∈ thetaStarOpen upper := by
  apply exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
    (c := fun upper => H ⁻¹' thetaStarOpen upper)
  · intro upper
    exact (thetaStarOpen_isOpen upper).preimage H.continuous
  · intro s _
    have hs : H s ∈ ⋃ upper : Bool, thetaStarOpen upper := by rw [thetaStarOpen_cover]; trivial
    simpa only [mem_iUnion, mem_preimage] using hs

noncomputable def actualThetaGenerator (i : Fin 2) :
    FundamentalGroup ActualSquareTheta thetaBase :=
  if i = 0 then FundamentalGroup.fromPath ⟦thetaLoop false⟧
  else FundamentalGroup.fromPath ⟦thetaLoop true⟧

noncomputable def actualThetaWordMap :
    FreeGroup (Fin 2) →* FundamentalGroup ActualSquareTheta thetaBase :=
  FreeGroup.lift actualThetaGenerator

@[simp]
theorem actualThetaWordMap_zero :
    actualThetaWordMap (FreeGroup.of 0) =
      FundamentalGroup.fromPath ⟦thetaLoop false⟧ := by
  simp [actualThetaWordMap, actualThetaGenerator]

@[simp]
theorem actualThetaWordMap_one :
    actualThetaWordMap (FreeGroup.of 1) =
      FundamentalGroup.fromPath ⟦thetaLoop true⟧ := by
  simp [actualThetaWordMap, actualThetaGenerator]

theorem actualThetaWordMap_unique
    (h : FreeGroup (Fin 2) →* FundamentalGroup ActualSquareTheta thetaBase)
    (hzero : h (FreeGroup.of 0) = FundamentalGroup.fromPath ⟦thetaLoop false⟧)
    (hone : h (FreeGroup.of 1) = FundamentalGroup.fromPath ⟦thetaLoop true⟧) :
    h = actualThetaWordMap := by
  ext w
  apply FreeGroup.lift_unique
  intro i
  fin_cases i <;> simp [actualThetaGenerator, hzero, hone]

theorem actualThetaWordMap_free_basis_iff_bijective :
    (∃ e : FreeGroup (Fin 2) ≃* FundamentalGroup ActualSquareTheta thetaBase,
      e (FreeGroup.of 0) = FundamentalGroup.fromPath ⟦thetaLoop false⟧ ∧
      e (FreeGroup.of 1) = FundamentalGroup.fromPath ⟦thetaLoop true⟧) ↔
    Function.Bijective actualThetaWordMap := by
  constructor
  · rintro ⟨e, hzero, hone⟩
    have he : e.toMonoidHom = actualThetaWordMap :=
      actualThetaWordMap_unique e.toMonoidHom hzero hone
    rw [← he]
    exact e.bijective
  · intro h
    refine ⟨MulEquiv.ofBijective actualThetaWordMap h, ?_, ?_⟩
    · exact actualThetaWordMap_zero
    · exact actualThetaWordMap_one

theorem actualThetaWordMap_word_eval (w : List (Fin 2 × Bool)) :
    actualThetaWordMap (FreeGroup.mk w) =
      (w.map fun a => if a.2 then actualThetaGenerator a.1
        else (actualThetaGenerator a.1)⁻¹).prod := by
  simp [actualThetaWordMap, FreeGroup.lift_mk, Bool.cond_eq_ite]

theorem actualThetaWordMap_injective_iff_trivial_kernel :
    Function.Injective actualThetaWordMap ↔
      ∀ w : FreeGroup (Fin 2), actualThetaWordMap w = 1 → w = 1 := by
  constructor
  · intro h w hw
    apply h
    simpa using hw
  · intro h a b hab
    have hw : actualThetaWordMap (a * b⁻¹) = 1 := by
      simp [hab]
    exact mul_inv_eq_one.mp (h _ hw)

theorem actualThetaWordMap_surjective_iff_path_words :
    Function.Surjective actualThetaWordMap ↔
      ∀ p : Path thetaBase thetaBase,
        ∃ w : FreeGroup (Fin 2),
          actualThetaWordMap w = FundamentalGroup.fromPath ⟦p⟧ := by
  constructor
  · intro h p
    exact h _
  · intro h q
    change ∃ w, actualThetaWordMap w =
      FundamentalGroup.fromPath (FundamentalGroup.toPath q)
    induction FundamentalGroup.toPath q using Quotient.inductionOn with
    | h p => exact h p

theorem actualThetaWordMap_free_basis_iff_classification :
    (∃ e : FreeGroup (Fin 2) ≃* FundamentalGroup ActualSquareTheta thetaBase,
      e (FreeGroup.of 0) = FundamentalGroup.fromPath ⟦thetaLoop false⟧ ∧
      e (FreeGroup.of 1) = FundamentalGroup.fromPath ⟦thetaLoop true⟧) ↔
    (∀ w : FreeGroup (Fin 2), actualThetaWordMap w = 1 → w = 1) ∧
      (∀ p : Path thetaBase thetaBase,
        ∃ w : FreeGroup (Fin 2),
          actualThetaWordMap w = FundamentalGroup.fromPath ⟦p⟧) := by
  rw [actualThetaWordMap_free_basis_iff_bijective]
  exact and_congr actualThetaWordMap_injective_iff_trivial_kernel
    actualThetaWordMap_surjective_iff_path_words

@[instance_reducible]
def thetaSheetTopology : TopologicalSpace (FreeGroup (Fin 2)) := ⊥
local instance : TopologicalSpace (FreeGroup (Fin 2)) := thetaSheetTopology
local instance : DiscreteTopology (FreeGroup (Fin 2)) := ⟨rfl⟩

noncomputable def thetaBranchWeight (z : ActualSquareTheta) : FreeGroup (Fin 2) :=
  if z.val.1 = -1 then 1 else if z.val.1 = 0 then FreeGroup.of 0 else FreeGroup.of 1

theorem thetaBranchWeight_continuous_overlap :
    Continuous (fun z : ThetaOverlap => thetaBranchWeight z.val) := by
  let : Finite ThetaBranchCoordinate := thetaBranchCoordinate_finite
  let f : ThetaBranchCoordinate → FreeGroup (Fin 2) := fun x =>
    if x.val = -1 then 1 else if x.val = 0 then FreeGroup.of 0 else FreeGroup.of 1
  have hf : Continuous f := continuous_of_discreteTopology
  exact hf.comp (continuous_fst.comp thetaOverlapProduct.continuous)

theorem thetaBranchWeight_continuousOn_overlap :
    ContinuousOn thetaBranchWeight (thetaStarOpen false ∩ thetaStarOpen true) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let f : ↑(thetaStarOpen false ∩ thetaStarOpen true) → ThetaOverlap :=
    fun z => ⟨z.val, z.property.2, z.property.1⟩
  have hf : Continuous f := by fun_prop
  exact thetaBranchWeight_continuous_overlap.comp hf

noncomputable def thetaCoordChange (i j : Bool) (z : ActualSquareTheta)
    (v : FreeGroup (Fin 2)) : FreeGroup (Fin 2) :=
  if i = j then v else if i then v * thetaBranchWeight z else v * (thetaBranchWeight z)⁻¹

set_option backward.isDefEq.respectTransparency false in
noncomputable def thetaCoverCore :
    FiberBundleCore Bool ActualSquareTheta (FreeGroup (Fin 2)) where
  baseSet := thetaStarOpen
  isOpen_baseSet := thetaStarOpen_isOpen
  indexAt z := if 0 < z.val.2 then true else false
  mem_baseSet_at z := by
    by_cases hz : 0 < z.val.2
    · simp only [ite_eq_left hz]
      change -(1/2 : ℝ) < z.val.2
      linarith
    · simp only [ite_eq_right hz]
      change z.val.2 < (1/2 : ℝ)
      linarith
  coordChange := thetaCoordChange
  coordChange_self i z hz v := by simp [thetaCoordChange]
  continuousOn_coordChange i j := by
    cases i <;> cases j
    · simpa [thetaCoordChange] using
        (continuous_snd : Continuous (fun p : ActualSquareTheta × FreeGroup (Fin 2) => p.2)).continuousOn
    · have h := thetaBranchWeight_continuousOn_overlap.comp
        (continuous_fst : Continuous (fun p : ActualSquareTheta × FreeGroup (Fin 2) => p.1)).continuousOn
        (s := (thetaStarOpen false ∩ thetaStarOpen true) ×ˢ univ)
        (fun _ h => h.1)
      simp only [thetaCoordChange, Bool.false_eq_true, ↓reduceIte]
      convert continuous_snd.continuousOn.mul h.inv using 1
      ext p
      rfl
    · have h := thetaBranchWeight_continuousOn_overlap.comp
        (continuous_fst : Continuous (fun p : ActualSquareTheta × FreeGroup (Fin 2) => p.1)).continuousOn
        (s := (thetaStarOpen true ∩ thetaStarOpen false) ×ˢ univ)
        (fun _ h => ⟨h.1.2,h.1.1⟩)
      simp only [thetaCoordChange, Bool.true_eq_false, ↓reduceIte]
      convert continuous_snd.continuousOn.mul h using 1
      ext p
      rfl
    · simpa [thetaCoordChange] using
        (continuous_snd : Continuous (fun p : ActualSquareTheta × FreeGroup (Fin 2) => p.2)).continuousOn
  coordChange_comp i j k z hz v := by
    cases i <;> cases j <;> cases k <;>
      simp [thetaCoordChange, mul_assoc]

abbrev ThetaCover := thetaCoverCore.TotalSpace

theorem thetaCover_isCoveringMap : IsCoveringMap thetaCoverCore.proj :=
  FiberBundle.isCoveringMap

noncomputable def thetaCoverBase (v : FreeGroup (Fin 2)) : ThetaCover := ⟨thetaBase,v⟩

theorem thetaCoverBase_proj (v : FreeGroup (Fin 2)) :
    thetaCoverCore.proj (thetaCoverBase v) = thetaBase := rfl

noncomputable def thetaChartIn (upper : Bool) (z : ActualSquareTheta)
    (v : FreeGroup (Fin 2)) : ThetaCover :=
  (thetaCoverCore.localTriv upper).invFun (z,v)

theorem thetaChartIn_proj (upper : Bool) (z : ActualSquareTheta)
    (v : FreeGroup (Fin 2)) : thetaCoverCore.proj (thetaChartIn upper z v) = z := rfl

noncomputable def thetaChartLiftPath (upper : Bool) {a b : ActualSquareTheta}
    (p : Path a b) (hp : ∀ t, p t ∈ thetaStarOpen upper) (v : FreeGroup (Fin 2)) :
    Path (thetaChartIn upper a v) (thetaChartIn upper b v) where
  toFun t := thetaChartIn upper (p t) v
  continuous_toFun := by
    apply (thetaCoverCore.localTriv upper).continuousOn_invFun.comp_continuous
      (p.continuous.prodMk continuous_const)
    intro t
    exact (thetaCoverCore.localTriv upper).mem_target.mpr (hp t)
  source' := by rw [p.source]
  target' := by rw [p.target]

set_option backward.isDefEq.respectTransparency false in
theorem thetaChart_monodromy (upper : Bool) {a b : ActualSquareTheta}
    (p : Path a b) (hp : ∀ t, p t ∈ thetaStarOpen upper) (v : FreeGroup (Fin 2)) :
    thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk p) ⟨thetaChartIn upper a v, rfl⟩ =
      ⟨thetaChartIn upper b v, rfl⟩ := by
  apply thetaCover_isCoveringMap.monodromy_eq_of_map_eq
    ⟦thetaChartLiftPath upper p hp v⟧
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  change thetaCoverCore.proj (thetaChartIn upper (p t) v) = p t
  rfl

theorem thetaLeg_lower_mem (outer : Bool) (i : Fin 5) (hi : i.val ≤ 1)
    (t : unitInterval) : thetaLeg outer i t ∈ thetaStarOpen false := by
  have ht0 := t.property.1
  have ht1 := t.property.2
  fin_cases i <;> cases outer <;>
    norm_num [thetaStarOpen, thetaLeg, thetaVertex] at * <;> linarith

theorem thetaLeg_upper_mem (outer : Bool) (i : Fin 5) (hi : 3 ≤ i.val)
    (t : unitInterval) : thetaLeg outer i t ∈ thetaStarOpen true := by
  have ht0 := t.property.1
  have ht1 := t.property.2
  fin_cases i <;> cases outer <;>
    norm_num [thetaStarOpen, thetaLeg, thetaVertex] at * <;> linarith

noncomputable def thetaHalf : unitInterval := ⟨1/2,by norm_num⟩

theorem thetaMiddle_lower_mem (outer : Bool) (t : unitInterval) :
    (thetaLeg outer 2).subpath 0 thetaHalf t ∈ thetaStarOpen false := by
  have ht0 := t.property.1
  have ht1 := t.property.2
  cases outer <;>
    norm_num [thetaStarOpen, Path.subpath, thetaLeg, thetaVertex,
      Set.Icc.coe_convexComb, thetaHalf] <;> nlinarith

theorem thetaMiddle_upper_mem (outer : Bool) (t : unitInterval) :
    (thetaLeg outer 2).subpath thetaHalf 1 t ∈ thetaStarOpen true := by
  have ht0 := t.property.1
  have ht1 := t.property.2
  cases outer <;>
    norm_num [thetaStarOpen, Path.subpath, thetaLeg, thetaVertex,
      Set.Icc.coe_convexComb, thetaHalf] <;> nlinarith

noncomputable def thetaMiddlePoint (outer : Bool) : ActualSquareTheta :=
  thetaLeg outer 2 thetaHalf

noncomputable def thetaMiddleLowerPath (outer : Bool) :
    Path (thetaVertex outer 2) (thetaMiddlePoint outer) :=
  ((thetaLeg outer 2).subpath 0 thetaHalf).cast (thetaLeg outer 2).source.symm rfl

noncomputable def thetaMiddleUpperPath (outer : Bool) :
    Path (thetaMiddlePoint outer) (thetaVertex outer 3) :=
  ((thetaLeg outer 2).subpath thetaHalf 1).cast rfl (thetaLeg outer 2).target.symm

theorem thetaMiddleLowerPath_mem (outer : Bool) (t : unitInterval) :
    thetaMiddleLowerPath outer t ∈ thetaStarOpen false := thetaMiddle_lower_mem outer t

theorem thetaMiddleUpperPath_mem (outer : Bool) (t : unitInterval) :
    thetaMiddleUpperPath outer t ∈ thetaStarOpen true := thetaMiddle_upper_mem outer t

theorem thetaMiddle_split (outer : Bool) :
    ((thetaMiddleLowerPath outer).trans (thetaMiddleUpperPath outer)).Homotopic
      (thetaLeg outer 2) := by
  have h := (Path.Homotopic.subpath_trans_subpath (thetaLeg outer 2) 0 thetaHalf 1).pathCast
    (thetaLeg outer 2).source.symm (thetaLeg outer 2).target.symm
  have hr : ((thetaLeg outer 2).subpath 0 1).cast
      (thetaLeg outer 2).source.symm (thetaLeg outer 2).target.symm =
      thetaLeg outer 2 := by
    apply Path.ext
    funext t
    simp [Path.cast, Path.subpath]
  rw [hr] at h
  exact h

theorem thetaChartIn_eq (upper : Bool) (z : ActualSquareTheta) (v : FreeGroup (Fin 2)) :
    thetaChartIn upper z v =
      ⟨z, thetaCoordChange upper (if 0 < z.val.2 then true else false) z v⟩ := rfl

theorem thetaChartIn_midpoint (outer : Bool) (v : FreeGroup (Fin 2)) :
    thetaChartIn false (thetaMiddlePoint outer) v =
      thetaChartIn true (thetaMiddlePoint outer)
        (v * (FreeGroup.of (if outer then 1 else 0 : Fin 2))⁻¹) := by
  cases outer <;>
    norm_num [thetaChartIn_eq, thetaCoordChange, thetaMiddlePoint,
      thetaLeg, thetaVertex, thetaHalf, thetaBranchWeight, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem thetaMiddle_monodromy (outer : Bool) (v : FreeGroup (Fin 2)) :
    thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (thetaLeg outer 2))
      ⟨thetaChartIn false (thetaVertex outer 2) v, rfl⟩ =
      ⟨thetaChartIn true (thetaVertex outer 3)
        (v * (FreeGroup.of (if outer then 1 else 0 : Fin 2))⁻¹), rfl⟩ := by
  erw [← Path.Homotopic.Quotient.eq.mpr (thetaMiddle_split outer),
    Path.Homotopic.Quotient.mk_trans,
    IsCoveringMap.monodromy_trans_apply,
    thetaChart_monodromy false (thetaMiddleLowerPath outer)
      (thetaMiddleLowerPath_mem outer) v]
  have he := thetaChartIn_midpoint outer v
  have hef : (⟨thetaChartIn false (thetaMiddlePoint outer) v, rfl⟩ :
      thetaCoverCore.proj ⁻¹' {thetaMiddlePoint outer}) =
      ⟨thetaChartIn true (thetaMiddlePoint outer)
        (v * (FreeGroup.of (if outer then 1 else 0 : Fin 2))⁻¹), rfl⟩ :=
    Subtype.ext he
  erw [hef]
  exact thetaChart_monodromy true (thetaMiddleUpperPath outer)
    (thetaMiddleUpperPath_mem outer) _

theorem thetaChartIn_lower_vertices (outer : Bool) (i : Fin 6) (hi : i.val ≤ 2)
    (v : FreeGroup (Fin 2)) :
    thetaChartIn false (thetaVertex outer i) v = ⟨thetaVertex outer i,v⟩ := by
  fin_cases i <;> cases outer <;>
    norm_num [thetaChartIn_eq, thetaCoordChange, thetaVertex, thetaBranchWeight] at * <;> rfl

theorem thetaChartIn_upper_vertices (outer : Bool) (i : Fin 6) (hi : 3 ≤ i.val)
    (v : FreeGroup (Fin 2)) :
    thetaChartIn true (thetaVertex outer i) v = ⟨thetaVertex outer i,v⟩ := by
  fin_cases i <;> cases outer <;>
    norm_num [thetaChartIn_eq, thetaCoordChange, thetaVertex, thetaBranchWeight] at * <;> rfl

theorem thetaLeg_lower_monodromy (outer : Bool) (i : Fin 5) (hi : i.val ≤ 1)
    (v : FreeGroup (Fin 2)) :
    thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (thetaLeg outer i))
      ⟨⟨thetaVertex outer i.castSucc,v⟩,rfl⟩ =
      ⟨⟨thetaVertex outer i.succ,v⟩,rfl⟩ := by
  have h := thetaChart_monodromy false (thetaLeg outer i)
    (thetaLeg_lower_mem outer i hi) v
  simp only [thetaChartIn_lower_vertices outer i.castSucc (by simpa using hi.trans (by norm_num)),
    thetaChartIn_lower_vertices outer i.succ (by simpa using Nat.succ_le_succ hi)] at h
  exact h

theorem thetaLeg_upper_monodromy (outer : Bool) (i : Fin 5) (hi : 3 ≤ i.val)
    (v : FreeGroup (Fin 2)) :
    thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (thetaLeg outer i))
      ⟨⟨thetaVertex outer i.castSucc,v⟩,rfl⟩ =
      ⟨⟨thetaVertex outer i.succ,v⟩,rfl⟩ := by
  have h := thetaChart_monodromy true (thetaLeg outer i)
    (thetaLeg_upper_mem outer i hi) v
  simp only [thetaChartIn_upper_vertices outer i.castSucc hi,
    thetaChartIn_upper_vertices outer i.succ (by simpa using hi.trans (Nat.le_succ i.val))] at h
  exact h

theorem thetaMiddle_raw_monodromy (outer : Bool) (v : FreeGroup (Fin 2)) :
    thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (thetaLeg outer 2))
      ⟨⟨thetaVertex outer 2,v⟩,rfl⟩ =
      ⟨⟨thetaVertex outer 3,v * (FreeGroup.of (if outer then 1 else 0 : Fin 2))⁻¹⟩,rfl⟩ := by
  have h := thetaMiddle_monodromy outer v
  simp only [thetaChartIn_lower_vertices outer 2 (by decide),
    thetaChartIn_upper_vertices outer 3 (by decide)] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem thetaCover_loop_monodromy (outer : Bool) (v : FreeGroup (Fin 2)) :
    thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (thetaLoop outer))
      ⟨thetaCoverBase v,rfl⟩ =
      ⟨thetaCoverBase (v * (FreeGroup.of (if outer then 1 else 0 : Fin 2))⁻¹),rfl⟩ := by
  simp only [thetaLoop, Path.cast_rfl_rfl, Path.concat_succ, Path.concat_zero,
    Path.Homotopic.Quotient.mk_trans, IsCoveringMap.monodromy_trans_apply,
    Function.comp_apply]
  change thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (thetaLeg outer 4))
    (thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (thetaLeg outer 3))
      (thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (thetaLeg outer 2))
        (thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (thetaLeg outer 1))
          (thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (thetaLeg outer 0))
            (thetaCover_isCoveringMap.monodromy (Path.Homotopic.Quotient.refl thetaBase)
              ⟨thetaCoverBase v,rfl⟩))))) = _
  erw [IsCoveringMap.monodromy_refl]
  erw [thetaLeg_lower_monodromy outer 0 (by decide),
    thetaLeg_lower_monodromy outer 1 (by decide), thetaMiddle_raw_monodromy,
    thetaLeg_upper_monodromy outer 3 (by decide),
    thetaLeg_upper_monodromy outer 4 (by decide)]
  rfl

abbrev ThetaBasedFiber := thetaCoverCore.proj ⁻¹' {thetaBase}

noncomputable def thetaFiberCoordinate (e : ThetaBasedFiber) : FreeGroup (Fin 2) := e.val.2

theorem thetaBasedFiber_eta (e : ThetaBasedFiber) :
    e = ⟨thetaCoverBase e.val.2,rfl⟩ := by
  rcases e with ⟨⟨x,v⟩,hx⟩
  change x = thetaBase at hx
  subst x
  rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def thetaRightRegular :
    FreeGroup (Fin 2) →* Equiv.Perm ThetaBasedFiber where
  toFun g := {
    toFun e := ⟨thetaCoverBase (thetaFiberCoordinate e * g⁻¹),rfl⟩
    invFun e := ⟨thetaCoverBase (thetaFiberCoordinate e * g),rfl⟩
    left_inv e := by
      rcases e with ⟨⟨x,v⟩,hx⟩
      change x = thetaBase at hx
      subst x
      change FreeGroup (Fin 2) at v
      apply Subtype.ext
      change thetaCoverBase ((v*g⁻¹)*g) = thetaCoverBase v
      simp [mul_assoc]
    right_inv e := by
      rcases e with ⟨⟨x,v⟩,hx⟩
      change x = thetaBase at hx
      subst x
      change FreeGroup (Fin 2) at v
      apply Subtype.ext
      change thetaCoverBase ((v*g)*g⁻¹) = thetaCoverBase v
      simp [mul_assoc] }
  map_one' := by
    apply Equiv.ext
    intro e
    change (⟨thetaCoverBase (thetaFiberCoordinate e * (1 : FreeGroup (Fin 2))⁻¹),rfl⟩ : ThetaBasedFiber) = e
    simpa [thetaFiberCoordinate] using (thetaBasedFiber_eta e).symm
  map_mul' a b := by
    apply Equiv.ext
    intro e
    apply Subtype.ext
    change thetaCoverBase (thetaFiberCoordinate e * (a*b)⁻¹) =
      thetaCoverBase ((thetaFiberCoordinate e * b⁻¹) * a⁻¹)
    simp [mul_assoc]

theorem thetaRightRegular_injective : Function.Injective thetaRightRegular := by
  intro a b hab
  have h := congrArg (fun f : Equiv.Perm ThetaBasedFiber =>
    (f ⟨thetaCoverBase 1,rfl⟩).val.2) hab
  change 1*a⁻¹ = 1*b⁻¹ at h
  simpa using h

set_option backward.isDefEq.respectTransparency false in
theorem thetaMonodromy_wordMap :
    (thetaCover_isCoveringMap.monodromyPerm thetaBase).comp actualThetaWordMap =
      thetaRightRegular := by
  apply FreeGroup.lift.symm.injective
  funext i
  change thetaCover_isCoveringMap.monodromyPerm thetaBase
      (actualThetaWordMap (FreeGroup.of i)) = thetaRightRegular (FreeGroup.of i)
  fin_cases i
  · erw [actualThetaWordMap_zero]
    apply Equiv.ext
    intro e
    rw [thetaBasedFiber_eta e]
    exact thetaCover_loop_monodromy false _
  · erw [actualThetaWordMap_one]
    apply Equiv.ext
    intro e
    rw [thetaBasedFiber_eta e]
    exact thetaCover_loop_monodromy true _

theorem actualThetaWordMap_injective : Function.Injective actualThetaWordMap := by
  intro a b hab
  apply thetaRightRegular_injective
  rw [← thetaMonodromy_wordMap]
  exact congrArg (thetaCover_isCoveringMap.monodromyPerm thetaBase) hab

theorem actualThetaWordMap_kernel_trivial (w : FreeGroup (Fin 2))
    (h : actualThetaWordMap w = 1) : w = 1 :=
  actualThetaWordMap_injective (by simpa using h)

theorem thetaBase_mem_star (upper : Bool) : thetaBase ∈ thetaStarOpen upper := by
  cases upper <;> norm_num [thetaStarOpen,thetaBase]

noncomputable def thetaStarStem (upper : Bool) (z : ActualSquareTheta)
    (hz : z ∈ thetaStarOpen upper) : Path thetaBase z := by
  let := thetaStar_contractible upper
  exact (PathConnectedSpace.somePath (⟨thetaBase,thetaBase_mem_star upper⟩ : ThetaStar upper)
    ⟨z,hz⟩).map continuous_subtype_val

theorem thetaStarStem_mem (upper : Bool) (z : ActualSquareTheta)
    (hz : z ∈ thetaStarOpen upper) (t : unitInterval) :
    thetaStarStem upper z hz t ∈ thetaStarOpen upper := by
  let := thetaStar_contractible upper
  unfold thetaStarStem
  exact (PathConnectedSpace.somePath (⟨thetaBase,thetaBase_mem_star upper⟩ : ThetaStar upper)
    ⟨z,hz⟩ t).property

theorem thetaTrans_mem {a b c : ActualSquareTheta} (upper : Bool)
    (p : Path a b) (q : Path b c)
    (hp : ∀ t, p t ∈ thetaStarOpen upper) (hq : ∀ t, q t ∈ thetaStarOpen upper)
    (t : unitInterval) : p.trans q t ∈ thetaStarOpen upper := by
  rw [Path.trans_apply]
  split_ifs <;> first | exact hp _ | exact hq _

noncomputable def thetaLowerLoopHalf (outer : Bool) : Path thetaBase (thetaMiddlePoint outer) :=
  ((thetaLeg outer 0).trans (thetaLeg outer 1)).trans (thetaMiddleLowerPath outer)

noncomputable def thetaUpperLoopHalf (outer : Bool) : Path (thetaMiddlePoint outer) thetaBase :=
  ((thetaMiddleUpperPath outer).trans (thetaLeg outer 3)).trans (thetaLeg outer 4)

theorem thetaLowerLoopHalf_mem (outer : Bool) (t : unitInterval) :
    thetaLowerLoopHalf outer t ∈ thetaStarOpen false := by
  exact thetaTrans_mem false _ _
    (thetaTrans_mem false _ _ (thetaLeg_lower_mem outer 0 (by decide))
      (thetaLeg_lower_mem outer 1 (by decide))) (thetaMiddleLowerPath_mem outer) t

theorem thetaUpperLoopHalf_mem (outer : Bool) (t : unitInterval) :
    thetaUpperLoopHalf outer t ∈ thetaStarOpen true := by
  exact thetaTrans_mem true _ _
    (thetaTrans_mem true _ _ (thetaMiddleUpperPath_mem outer)
      (thetaLeg_upper_mem outer 3 (by decide))) (thetaLeg_upper_mem outer 4 (by decide)) t

set_option backward.isDefEq.respectTransparency false in
theorem thetaLoop_split_halves (outer : Bool) :
    (thetaLowerLoopHalf outer).trans (thetaUpperLoopHalf outer) |>.Homotopic
      (thetaLoop outer) := by
  apply Path.Homotopic.Quotient.eq.mp
  change (Path.Homotopic.Quotient.mk (thetaLowerLoopHalf outer)).trans
      (Path.Homotopic.Quotient.mk (thetaUpperLoopHalf outer)) =
    Path.Homotopic.Quotient.mk (thetaLoop outer)
  simp only [thetaLoop, Path.cast_rfl_rfl, Path.concat_succ, Path.concat_zero,
    Function.comp_apply, thetaLowerLoopHalf,thetaUpperLoopHalf,
    Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_refl]
  change (((Path.Homotopic.Quotient.mk (thetaLeg outer 0)).trans
    (Path.Homotopic.Quotient.mk (thetaLeg outer 1))).trans
      (Path.Homotopic.Quotient.mk (thetaMiddleLowerPath outer))).trans
      (((Path.Homotopic.Quotient.mk (thetaMiddleUpperPath outer)).trans
        (Path.Homotopic.Quotient.mk (thetaLeg outer 3))).trans
        (Path.Homotopic.Quotient.mk (thetaLeg outer 4))) =
    (((((Path.Homotopic.Quotient.refl thetaBase).trans
      (Path.Homotopic.Quotient.mk (thetaLeg outer 0))).trans
      (Path.Homotopic.Quotient.mk (thetaLeg outer 1))).trans
      (Path.Homotopic.Quotient.mk (thetaLeg outer 2))).trans
      (Path.Homotopic.Quotient.mk (thetaLeg outer 3))).trans
      (Path.Homotopic.Quotient.mk (thetaLeg outer 4))
  have h := Path.Homotopic.Quotient.eq.mpr (thetaMiddle_split outer)
  rw [Path.Homotopic.Quotient.mk_trans] at h
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.refl_trans]
  erw [← h]
  simp only [Path.Homotopic.Quotient.trans_assoc]

theorem thetaMiddlePoint_mem_overlap (outer : Bool) :
    -(1/2 : ℝ) < (thetaMiddlePoint outer).val.2 ∧
      (thetaMiddlePoint outer).val.2 < (1/2 : ℝ) := by
  cases outer <;> norm_num [thetaMiddlePoint,thetaLeg,thetaVertex,thetaHalf]

noncomputable def thetaSwitchClass (i j : Bool) (z : ActualSquareTheta)
    (hi : z ∈ thetaStarOpen i) (hj : z ∈ thetaStarOpen j) :
    FundamentalGroup ActualSquareTheta thetaBase :=
  FundamentalGroup.fromPath ((Path.Homotopic.Quotient.mk (thetaStarStem i z hi)).trans
    (Path.Homotopic.Quotient.mk (thetaStarStem j z hj)).symm)

theorem thetaSwitchClass_middle (outer : Bool) :
    thetaSwitchClass false true (thetaMiddlePoint outer)
      (thetaMiddlePoint_mem_overlap outer).2 (thetaMiddlePoint_mem_overlap outer).1 =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (thetaLoop outer)) := by
  apply Path.Homotopic.Quotient.eq.mpr
  have hlow := thetaStar_paths_homotopic false (thetaBase_mem_star false)
    (thetaMiddlePoint_mem_overlap outer).2
    (thetaStarStem false (thetaMiddlePoint outer) (thetaMiddlePoint_mem_overlap outer).2)
    (thetaLowerLoopHalf outer) (thetaStarStem_mem _ _ _) (thetaLowerLoopHalf_mem outer)
  have hupp := thetaStar_paths_homotopic true (thetaMiddlePoint_mem_overlap outer).1
    (thetaBase_mem_star true)
    (thetaStarStem true (thetaMiddlePoint outer) (thetaMiddlePoint_mem_overlap outer).1).symm
    (thetaUpperLoopHalf outer) (fun t => thetaStarStem_mem _ _ _ _)
    (thetaUpperLoopHalf_mem outer)
  exact (hlow.hcomp hupp).trans (thetaLoop_split_halves outer)

theorem thetaQuotient_symm_trans {a b c : ActualSquareTheta}
    (p : Path.Homotopic.Quotient a b) (q : Path.Homotopic.Quotient b c) :
    (p.trans q).symm = q.symm.trans p.symm := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction q using Path.Homotopic.Quotient.ind with
    | mk q =>
      simp only [← Path.Homotopic.Quotient.mk_trans,
        ← Path.Homotopic.Quotient.mk_symm, Path.trans_symm]

theorem thetaQuotient_cancel_middle {a b c d : ActualSquareTheta}
    (p : Path.Homotopic.Quotient a b) (q : Path.Homotopic.Quotient b c)
    (r : Path.Homotopic.Quotient b d) :
    (p.trans q).trans (q.symm.trans r) = p.trans r := by
  rw [Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.trans_assoc q q.symm r,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]

set_option backward.isDefEq.respectTransparency false in
theorem thetaSwitchClass_overlap_constant (z w : ThetaOverlap)
    (hx : z.val.val.1 = w.val.val.1) :
    thetaSwitchClass false true z.val z.property.2 z.property.1 =
      thetaSwitchClass false true w.val w.property.2 w.property.1 := by
  let r : Path z.val w.val := (thetaOverlapVerticalPath z w hx).map continuous_subtype_val
  have hrlo : ∀ t, r t ∈ thetaStarOpen false := fun t =>
    (thetaOverlapVerticalPath z w hx t).property.2
  have hrup : ∀ t, r t ∈ thetaStarOpen true := fun t =>
    (thetaOverlapVerticalPath z w hx t).property.1
  have hlo := thetaStar_paths_homotopic false (thetaBase_mem_star false) w.property.2
    (thetaStarStem false w.val w.property.2)
    ((thetaStarStem false z.val z.property.2).trans r)
    (thetaStarStem_mem _ _ _)
    (thetaTrans_mem false _ _ (thetaStarStem_mem _ _ _) hrlo)
  have hup := thetaStar_paths_homotopic true (thetaBase_mem_star true) w.property.1
    (thetaStarStem true w.val w.property.1)
    ((thetaStarStem true z.val z.property.1).trans r)
    (thetaStarStem_mem _ _ _)
    (thetaTrans_mem true _ _ (thetaStarStem_mem _ _ _) hrup)
  change (Path.Homotopic.Quotient.mk (thetaStarStem false z.val z.property.2)).trans
      (Path.Homotopic.Quotient.mk (thetaStarStem true z.val z.property.1)).symm =
    (Path.Homotopic.Quotient.mk (thetaStarStem false w.val w.property.2)).trans
      (Path.Homotopic.Quotient.mk (thetaStarStem true w.val w.property.1)).symm
  rw [Path.Homotopic.Quotient.eq.mpr hlo, Path.Homotopic.Quotient.eq.mpr hup]
  simp only [Path.Homotopic.Quotient.mk_trans, thetaQuotient_symm_trans]
  rw [Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.trans_assoc _ _
      (Path.Homotopic.Quotient.mk (thetaStarStem true z.val z.property.1)).symm,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]

theorem thetaSwitchClass_base :
    thetaSwitchClass false true thetaBase (thetaBase_mem_star false)
      (thetaBase_mem_star true) = 1 := by
  have h0 := thetaStar_paths_homotopic false (thetaBase_mem_star false) (thetaBase_mem_star false)
    (thetaStarStem false thetaBase (thetaBase_mem_star false)) (Path.refl thetaBase)
    (thetaStarStem_mem _ _ _) (fun _ => thetaBase_mem_star false)
  have h1 := thetaStar_paths_homotopic true (thetaBase_mem_star true) (thetaBase_mem_star true)
    (thetaStarStem true thetaBase (thetaBase_mem_star true)) (Path.refl thetaBase)
    (thetaStarStem_mem _ _ _) (fun _ => thetaBase_mem_star true)
  change (Path.Homotopic.Quotient.mk (thetaStarStem false thetaBase (thetaBase_mem_star false))).trans
      (Path.Homotopic.Quotient.mk (thetaStarStem true thetaBase (thetaBase_mem_star true))).symm =
    Path.Homotopic.Quotient.refl thetaBase
  rw [Path.Homotopic.Quotient.eq.mpr h0, Path.Homotopic.Quotient.eq.mpr h1]
  simp only [Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_symm]

theorem thetaSwitchClass_forward_range (z : ThetaOverlap) :
    thetaSwitchClass false true z.val z.property.2 z.property.1 ∈
      Set.range actualThetaWordMap := by
  rcases thetaOverlap_branch z with hx | hx | hx
  · have he := thetaSwitchClass_overlap_constant z
      ⟨thetaBase, ⟨thetaBase_mem_star true, thetaBase_mem_star false⟩⟩ hx
    rw [he, thetaSwitchClass_base]
    exact ⟨1, map_one _⟩
  · have he := thetaSwitchClass_overlap_constant z
      ⟨thetaMiddlePoint false, thetaMiddlePoint_mem_overlap false⟩ (by
        norm_num [thetaMiddlePoint,thetaLeg,thetaVertex,thetaHalf]
        exact hx)
    rw [he, thetaSwitchClass_middle]
    exact ⟨FreeGroup.of 0, actualThetaWordMap_zero⟩
  · have he := thetaSwitchClass_overlap_constant z
      ⟨thetaMiddlePoint true, thetaMiddlePoint_mem_overlap true⟩ (by
        norm_num [thetaMiddlePoint,thetaLeg,thetaVertex,thetaHalf]
        exact hx)
    rw [he, thetaSwitchClass_middle]
    exact ⟨FreeGroup.of 1, actualThetaWordMap_one⟩

theorem thetaSwitchClass_range (i j : Bool) (z : ActualSquareTheta)
    (hi : z ∈ thetaStarOpen i) (hj : z ∈ thetaStarOpen j) :
    thetaSwitchClass i j z hi hj ∈ Set.range actualThetaWordMap := by
  cases i <;> cases j
  · refine ⟨1, ?_⟩
    rw [map_one]
    change Path.Homotopic.Quotient.refl thetaBase = _
    exact (Path.Homotopic.Quotient.trans_symm _).symm
  · exact thetaSwitchClass_forward_range ⟨z,⟨hj,hi⟩⟩
  · obtain ⟨w, hw⟩ := thetaSwitchClass_forward_range ⟨z,⟨hi,hj⟩⟩
    refine ⟨w⁻¹, ?_⟩
    rw [map_inv, hw]
    change ((Path.Homotopic.Quotient.mk (thetaStarStem false z hj)).trans
      (Path.Homotopic.Quotient.mk (thetaStarStem true z hi)).symm).symm = _
    rw [thetaQuotient_symm_trans, ← Path.Homotopic.Quotient.mk_symm,
      ← Path.Homotopic.Quotient.mk_symm, Path.symm_symm]
    rfl
  · refine ⟨1, ?_⟩
    rw [map_one]
    change Path.Homotopic.Quotient.refl thetaBase = _
    exact (Path.Homotopic.Quotient.trans_symm _).symm

noncomputable def thetaAnchorStar (z : ActualSquareTheta) : Bool :=
  if z.val.2 < (1/2 : ℝ) then false else true

theorem thetaAnchorStar_mem (z : ActualSquareTheta) : z ∈ thetaStarOpen (thetaAnchorStar z) := by
  unfold thetaAnchorStar
  split_ifs with h
  · exact h
  · change -(1/2 : ℝ) < z.val.2
    push_neg at h
    linarith

noncomputable def thetaAnchor (z : ActualSquareTheta) : Path thetaBase z :=
  thetaStarStem (thetaAnchorStar z) z (thetaAnchorStar_mem z)

noncomputable def thetaAnchoredClass {a b : ActualSquareTheta} (p : Path a b) :
    FundamentalGroup ActualSquareTheta thetaBase :=
  FundamentalGroup.fromPath (((Path.Homotopic.Quotient.mk (thetaAnchor a)).trans
    (Path.Homotopic.Quotient.mk p)).trans (Path.Homotopic.Quotient.mk (thetaAnchor b)).symm)

theorem thetaAnchoredClass_trans {a b c : ActualSquareTheta} (p : Path a b) (q : Path b c) :
    thetaAnchoredClass (p.trans q) = thetaAnchoredClass q * thetaAnchoredClass p := by
  change _ = ((Path.Homotopic.Quotient.mk (thetaAnchor a)).trans
    (Path.Homotopic.Quotient.mk p) |>.trans (Path.Homotopic.Quotient.mk (thetaAnchor b)).symm).trans
      (((Path.Homotopic.Quotient.mk (thetaAnchor b)).trans
        (Path.Homotopic.Quotient.mk q)).trans (Path.Homotopic.Quotient.mk (thetaAnchor c)).symm)
  simp only [thetaAnchoredClass, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.mk (thetaAnchor b)).symm
    (Path.Homotopic.Quotient.mk (thetaAnchor b)),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

set_option backward.isDefEq.respectTransparency false in
theorem thetaAnchoredClass_star {a b : ActualSquareTheta} (p : Path a b)
    (i : Bool) (hp : ∀ t, p t ∈ thetaStarOpen i) :
    thetaAnchoredClass p ∈ Set.range actualThetaWordMap := by
  have ha : a ∈ thetaStarOpen i := by simpa using hp 0
  have hb : b ∈ thetaStarOpen i := by simpa using hp 1
  obtain ⟨u,hu⟩ := thetaSwitchClass_range (thetaAnchorStar a) i a (thetaAnchorStar_mem a) ha
  obtain ⟨v,hv⟩ := thetaSwitchClass_range i (thetaAnchorStar b) b hb (thetaAnchorStar_mem b)
  refine ⟨v*u, ?_⟩
  rw [map_mul, hu, hv]
  have h := thetaStar_paths_homotopic i (thetaBase_mem_star i) hb
    ((thetaStarStem i a ha).trans p) (thetaStarStem i b hb)
    (thetaTrans_mem i _ _ (thetaStarStem_mem _ _ _) hp) (thetaStarStem_mem _ _ _)
  have hq := Path.Homotopic.Quotient.eq.mpr h
  rw [Path.Homotopic.Quotient.mk_trans] at hq
  change ((Path.Homotopic.Quotient.mk (thetaAnchor a)).trans
    (Path.Homotopic.Quotient.mk (thetaStarStem i a ha)).symm).trans
      ((Path.Homotopic.Quotient.mk (thetaStarStem i b hb)).trans
        (Path.Homotopic.Quotient.mk (thetaAnchor b)).symm) = _
  rw [← hq]
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.mk (thetaStarStem i a ha)).symm
    (Path.Homotopic.Quotient.mk (thetaStarStem i a ha)),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  simp only [thetaAnchoredClass, Path.Homotopic.Quotient.trans_assoc]

theorem thetaAnchoredClass_homotopic {a b : ActualSquareTheta} {p q : Path a b}
    (h : p.Homotopic q) : thetaAnchoredClass p = thetaAnchoredClass q := by
  unfold thetaAnchoredClass
  rw [Path.Homotopic.Quotient.eq.mpr h]

theorem thetaAnchoredClass_cast {a b c d : ActualSquareTheta} (p : Path a b)
    (hc : c = a) (hd : d = b) : thetaAnchoredClass (p.cast hc hd) = thetaAnchoredClass p := by
  cases hc
  cases hd
  rw [Path.cast_rfl_rfl]

theorem thetaAnchoredClass_range (a b : ActualSquareTheta) (p : Path a b) :
    thetaAnchoredClass p ∈ Set.range actualThetaWordMap := by
  obtain ⟨t,ht0,hmono,⟨N,hN⟩,hstar⟩ := thetaPath_star_subdivision p
  have hpiece (n : ℕ) : thetaAnchoredClass (p.subpath (t n) (t (n+1))) ∈
      Set.range actualThetaWordMap := by
    obtain ⟨i,hi⟩ := hstar n
    apply thetaAnchoredClass_star _ i
    intro u
    have hu : p.subpath (t n) (t (n+1)) u ∈ Set.range (p.subpath (t n) (t (n+1))) :=
      ⟨u,rfl⟩
    rw [Path.range_subpath_of_le _ _ _ (hmono (Nat.le_succ n))] at hu
    obtain ⟨v,hv,hev⟩ := hu
    rw [← hev]
    exact hi v hv
  have hind (n : ℕ) : thetaAnchoredClass (p.subpath (t 0) (t n)) ∈
      Set.range actualThetaWordMap := by
    induction n with
    | zero =>
      refine ⟨1, ?_⟩
      rw [map_one, Path.subpath_self]
      change Path.Homotopic.Quotient.refl thetaBase = _
      simp only [thetaAnchoredClass, Path.Homotopic.Quotient.mk_refl,
        Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.trans_symm]
    | succ n ih =>
      obtain ⟨u,hu⟩ := ih
      obtain ⟨v,hv⟩ := hpiece n
      refine ⟨v*u, ?_⟩
      rw [map_mul, hu, hv, ← thetaAnchoredClass_trans]
      exact thetaAnchoredClass_homotopic ⟨Path.Homotopy.subpathTransSubpath p _ _ _⟩
  have h := hind N
  rw [ht0, hN N le_rfl, Path.subpath_zero_one, thetaAnchoredClass_cast] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem thetaAnchoredClass_based (p : Path thetaBase thetaBase) :
    thetaAnchoredClass p = FundamentalGroup.fromPath ⟦p⟧ := by
  have h := thetaStar_paths_homotopic false (thetaBase_mem_star false)
    (thetaBase_mem_star false)
    (thetaStarStem false thetaBase (thetaBase_mem_star false)) (Path.refl thetaBase)
    (thetaStarStem_mem _ _ _) (fun _ => thetaBase_mem_star false)
  have ha : thetaAnchor thetaBase = thetaStarStem false thetaBase (thetaBase_mem_star false) := by
    simp only [thetaAnchor, thetaAnchorStar]
    norm_num [thetaBase]
  unfold thetaAnchoredClass
  rw [ha, Path.Homotopic.Quotient.eq.mpr h]
  simp only [Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans]
  change (Path.Homotopic.Quotient.mk p).trans
    (Path.Homotopic.Quotient.mk (Path.refl thetaBase)).symm = _
  rw [← Path.Homotopic.Quotient.mk_symm, Path.refl_symm,
    Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl]
  rfl

theorem actualThetaWordMap_path_words (p : Path thetaBase thetaBase) :
    ∃ w : FreeGroup (Fin 2), actualThetaWordMap w = FundamentalGroup.fromPath ⟦p⟧ := by
  have h := thetaAnchoredClass_range thetaBase thetaBase p
  rw [thetaAnchoredClass_based] at h
  exact h

theorem actualThetaWordMap_surjective : Function.Surjective actualThetaWordMap :=
  actualThetaWordMap_surjective_iff_path_words.mpr actualThetaWordMap_path_words

/-- Literal square theta graph. The left cell loop and whole outer boundary
loop, with this common left midpoint base and these exact affine legs,
form a free basis of the actual based fundamental group. -/
theorem actual_square_theta_boundary_loops_fundamental_group_free_basis :
    ∃ e : FreeGroup (Fin 2) ≃* FundamentalGroup ActualSquareTheta thetaBase,
      e (FreeGroup.of 0) = FundamentalGroup.fromPath ⟦thetaLoop false⟧ ∧
      e (FreeGroup.of 1) = FundamentalGroup.fromPath ⟦thetaLoop true⟧ := by
  exact actualThetaWordMap_free_basis_iff_bijective.mpr
    ⟨actualThetaWordMap_injective, actualThetaWordMap_surjective⟩

end CurveComplex.Hyperbolic.PantsTheta
