import CurveComplexGenusTwo.Topology.ActualBoundaryModels.ZeroHandleClosedDisc
import ClassificationOfSurfaces.DiskSquare
import Mathlib
namespace CurveComplex.Hyperbolic
open Set Topology
open LeanEval.Topology.ClassificationOfSurfaces
private theorem complex_mk_continuous (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun u => (⟨f u,g u⟩ : ℂ)) :=
  Complex.equivRealProdCLM.symm.continuous.comp (hf.prodMk hg)

private noncomputable def rectPerimeter (u : ℝ) : ℂ :=
  if u≤1 then ⟨-1,-u⟩ else
  if u≤2 then ⟨2*u-3,-1⟩ else
  if u≤4 then ⟨1,u-3⟩ else
  if u≤5 then ⟨9-2*u,1⟩ else ⟨-1,6-u⟩

private theorem rectPerimeter_continuous : Continuous rectPerimeter := by
  unfold rectPerimeter
  apply Continuous.if_le (by exact complex_mk_continuous _ _ (by fun_prop) (by fun_prop)) _ continuous_id continuous_const
  · intro u hu
    simp only [id_eq] at hu
    subst u
    norm_num
  apply Continuous.if_le (by exact complex_mk_continuous _ _ (by fun_prop) (by fun_prop)) _ continuous_id continuous_const
  · intro u hu
    simp only [id_eq] at hu
    subst u
    norm_num
  apply Continuous.if_le (by exact complex_mk_continuous _ _ (by fun_prop) (by fun_prop)) _ continuous_id continuous_const
  · intro u hu
    simp only [id_eq] at hu
    subst u
    norm_num
  apply Continuous.if_le (by exact complex_mk_continuous _ _ (by fun_prop) (by fun_prop)) (by exact complex_mk_continuous _ _ (by fun_prop) (by fun_prop)) continuous_id continuous_const
  intro u hu
  simp only [id_eq] at hu
  subst u
  norm_num

private theorem rectPerimeter_mem_boundary (u : ℝ) (hu : u ∈ Icc (0:ℝ) 6) :
    rectPerimeter u ∈ DiskSquare.boundary := by
  change max |(rectPerimeter u).re| |(rectPerimeter u).im|=1
  unfold rectPerimeter
  split_ifs <;> simp only [abs_neg,abs_one]
  all_goals first
    | apply max_eq_left; rw [abs_le]; constructor <;> linarith [hu.1,hu.2]
    | apply max_eq_right; rw [abs_le]; constructor <;> linarith [hu.1,hu.2]

private theorem rectPerimeter_injective_mod_endpoints
    (u v : ℝ) (hu : u ∈ Icc (0:ℝ) 6) (hv : v ∈ Icc (0:ℝ) 6)
    (he : rectPerimeter u=rectPerimeter v) :
    u=v ∨ (u=0 ∧ v=6) ∨ (u=6 ∧ v=0) := by
  unfold rectPerimeter at he
  split_ifs at he
  all_goals
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    dsimp at hre him
    first
    | left; linarith [hu.1,hu.2,hv.1,hv.2]
    | right; left; constructor <;> linarith [hu.1,hu.2,hv.1,hv.2]
    | right; right; constructor <;> linarith [hu.1,hu.2,hv.1,hv.2]

private theorem rectPerimeter_surjective (z : DiskSquare.boundary) :
    ∃ u : ℝ, u ∈ Icc (0:ℝ) 6 ∧ rectPerimeter u=z.val := by
  have hb : max |z.val.re| |z.val.im|=1 := z.property
  have hbounds : |z.val.re|≤1 ∧ |z.val.im|≤1 := by
    constructor
    · exact (le_max_left _ _).trans hb.le
    · exact (le_max_right _ _).trans hb.le
  rw [abs_le,abs_le] at hbounds
  have hcase : z.val.re = -1 ∨ z.val.re=1 ∨ z.val.im = -1 ∨ z.val.im=1 := by
    rcases max_eq_iff.mp hb with h | h
    · rcases eq_or_eq_neg_of_abs_eq h.1 with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · rcases eq_or_eq_neg_of_abs_eq h.1 with h | h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
  rcases hcase with h | h | h | h
  · by_cases him : z.val.im≤0
    · refine ⟨-z.val.im,⟨by linarith,by linarith [hbounds.2.1]⟩,?_⟩
      have hle : -z.val.im≤1 := by linarith [hbounds.2.1]
      simp only [rectPerimeter,if_pos hle]
      apply Complex.ext <;> dsimp <;> linarith
    · refine ⟨6-z.val.im,⟨by linarith [hbounds.2.2],by linarith⟩,?_⟩
      unfold rectPerimeter
      split_ifs <;> apply Complex.ext <;> dsimp <;> linarith [hbounds.2.1,hbounds.2.2]
  · refine ⟨3+z.val.im,⟨by linarith [hbounds.2.1],by linarith [hbounds.2.2]⟩,?_⟩
    unfold rectPerimeter
    split_ifs <;> apply Complex.ext <;> dsimp <;> linarith [hbounds.2.1,hbounds.2.2]
  · refine ⟨(z.val.re+3)/2,⟨by linarith [hbounds.1.1],by linarith [hbounds.1.2]⟩,?_⟩
    unfold rectPerimeter
    split_ifs <;> apply Complex.ext <;> dsimp <;> linarith [hbounds.1.1,hbounds.1.2]
  · refine ⟨(9-z.val.re)/2,⟨by linarith [hbounds.1.2],by linarith [hbounds.1.1]⟩,?_⟩
    unfold rectPerimeter
    split_ifs <;> apply Complex.ext <;> dsimp <;> linarith [hbounds.1.1,hbounds.1.2]

private instance : Fact (0 < (6:ℝ)) := ⟨by norm_num⟩

private noncomputable def rectArc : C(Icc (0:ℝ) (0+6),DiskSquare.boundary) where
  toFun u := ⟨rectPerimeter u.val,rectPerimeter_mem_boundary u.val (by simpa using u.property)⟩
  continuous_toFun := (rectPerimeter_continuous.comp continuous_subtype_val).subtype_mk _

private theorem rectArc_endpoints :
    rectArc ⟨0,by norm_num⟩=rectArc ⟨0+6,by norm_num⟩ := by
  apply Subtype.ext
  norm_num [rectArc,rectPerimeter]

private theorem rectArc_respects (u v : Icc (0:ℝ) (0+6))
    (h : AddCircle.EndpointIdent 6 0 u v) : rectArc u=rectArc v := by
  cases h
  exact rectArc_endpoints

private noncomputable def rectQuotMap : C(Quot (AddCircle.EndpointIdent (6:ℝ) 0),DiskSquare.boundary) where
  toFun := Quot.lift rectArc rectArc_respects
  continuous_toFun := continuous_quot_lift rectArc_respects rectArc.continuous

private theorem rectQuotMap_injective : Function.Injective rectQuotMap := by
  intro q₁ q₂ he
  induction q₁ using Quot.inductionOn with
  | _ u =>
    induction q₂ using Quot.inductionOn with
    | _ v =>
      have hv : rectPerimeter u.val=rectPerimeter v.val := congrArg Subtype.val he
      rcases rectPerimeter_injective_mod_endpoints u.val v.val
        (by simpa using u.property) (by simpa using v.property) hv with h | h | h
      · have he : u=v := Subtype.ext h
        subst v
        rfl
      · have hu : u=(⟨0,by norm_num⟩ : Icc (0:ℝ) (0+6)) := Subtype.ext h.1
        have hv : v=(⟨0+6,by norm_num⟩ : Icc (0:ℝ) (0+6)) := Subtype.ext (by simpa using h.2)
        rw [hu,hv]
        exact Quot.sound AddCircle.EndpointIdent.mk
      · have hu : u=(⟨0+6,by norm_num⟩ : Icc (0:ℝ) (0+6)) := Subtype.ext (by simpa using h.1)
        have hv : v=(⟨0,by norm_num⟩ : Icc (0:ℝ) (0+6)) := Subtype.ext h.2
        rw [hu,hv]
        exact (Quot.sound (AddCircle.EndpointIdent.mk : AddCircle.EndpointIdent (6:ℝ) 0 _ _)).symm

private theorem rectQuotMap_surjective : Function.Surjective rectQuotMap := by
  intro z
  obtain ⟨u,hu,he⟩ := rectPerimeter_surjective z
  refine ⟨Quot.mk _ (⟨u,by simpa using hu⟩ : Icc (0:ℝ) (0+6)),?_⟩
  exact Subtype.ext he

private noncomputable def rectQuotHomeomorph :
    Quot (AddCircle.EndpointIdent (6:ℝ) 0) ≃ₜ DiskSquare.boundary :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective rectQuotMap ⟨rectQuotMap_injective,rectQuotMap_surjective⟩)
    rectQuotMap.continuous

private noncomputable def rectAddCircleHomeomorph : AddCircle (6:ℝ) ≃ₜ DiskSquare.boundary := by
  letI : Fact (0<(6:ℝ)) := ⟨by norm_num⟩
  exact (AddCircle.homeoIccQuot (6:ℝ) 0).trans rectQuotHomeomorph

private noncomputable def rectCircleHomeomorph : Circle ≃ₜ DiskSquare.boundary :=
  (AddCircle.homeomorphCircle (by norm_num : (6:ℝ)≠0)).symm.trans rectAddCircleHomeomorph

private theorem rectAddCircleHomeomorph_apply (u : ℝ) (hu : u ∈ Ico (0:ℝ) 6) :
    rectAddCircleHomeomorph (u : AddCircle (6:ℝ))=
      rectArc ⟨u,by simpa using ⟨hu.1,hu.2.le⟩⟩ := by
  letI : Fact (0<(6:ℝ)) := ⟨by norm_num⟩
  unfold rectAddCircleHomeomorph
  simp only [Homeomorph.trans_apply]
  have hsource : (AddCircle.homeoIccQuot (6:ℝ) 0) (u : AddCircle (6:ℝ))=
      Quot.mk _ (⟨u,by simpa using ⟨hu.1,hu.2.le⟩⟩ : Icc (0:ℝ) (0+6)) := by
    change Quot.mk _ (Set.inclusion Set.Ico_subset_Icc_self
      (AddCircle.equivIco (6:ℝ) 0 (u : AddCircle (6:ℝ))))=_
    rw [AddCircle.equivIco,QuotientAddGroup.equivIcoMod_coe]
    apply congrArg (Quot.mk _)
    apply Subtype.ext
    exact (toIcoMod_eq_self (by norm_num : 0<(6:ℝ))).2 (by simpa using hu)
  rw [hsource]
  rfl

private theorem rectCircleHomeomorph_exp (u : ℝ) (hu : u ∈ Icc (0:ℝ) 6) :
    (rectCircleHomeomorph (Circle.exp (2*Real.pi/6*u))).val=rectPerimeter u := by
  have hico (u : ℝ) (hu : u ∈ Ico (0:ℝ) 6) :
      (rectCircleHomeomorph (Circle.exp (2*Real.pi/6*u))).val=rectPerimeter u := by
    rw [show Circle.exp (2*Real.pi/6*u)=AddCircle.homeomorphCircle
      (by norm_num : (6:ℝ)≠0) (u : AddCircle (6:ℝ)) by
        rw [AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk]]
    unfold rectCircleHomeomorph
    rw [Homeomorph.trans_apply,Homeomorph.symm_apply_apply,rectAddCircleHomeomorph_apply u hu]
    rfl
  by_cases he : u=6
  · subst u
    have hexp : Circle.exp (2*Real.pi/6*6)=Circle.exp (2*Real.pi/6*0) := by
      apply Circle.exp_eq_exp.mpr
      refine ⟨1,?_⟩
      norm_num <;> ring
    rw [hexp,hico 0 (by norm_num)]
    norm_num [rectPerimeter]
  · exact hico u ⟨hu.1,lt_of_le_of_ne hu.2 he⟩

private noncomputable def rectSquareProdHomeomorph : DiskSquare.square ≃ₜ Metric.closedBall ((0,0):ℝ×ℝ) 1 :=
  Complex.equivRealProdCLM.toHomeomorph.subtype (fun z => by
    change DiskSquare.maxAbs z≤1 ↔ (z.re,z.im) ∈ Metric.closedBall ((0,0):ℝ×ℝ) 1
    simp [DiskSquare.maxAbs,Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq])

/-- Boundary-matched rectangle for the actual six-edge annulus cut. This is
an internal geometric construction for the n=2 branch, not an input premise. -/
theorem actual_zero_handle_two_boundary_cut_rectangle :
    ∃ d : Complex.ClosedUnitDisc ≃ₜ Metric.closedBall ((0,0):ℝ×ℝ) 1,
      ∀ t : unitInterval,
        (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(t:ℝ)/6))).val = (-1,-(t:ℝ)) ∧
        (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(3-(t:ℝ))/6))).val = (1,-(t:ℝ)) ∧
        (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(3+(t:ℝ))/6))).val = (1,(t:ℝ)) ∧
        (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(6-(t:ℝ))/6))).val = (-1,(t:ℝ)) := by
  classical
  let conjD : Complex.ClosedUnitDisc ≃ₜ Complex.ClosedUnitDisc :=
    Complex.conjCLE.toHomeomorph.subtype (fun z => by
      change z ∈ Metric.closedBall 0 1 ↔ (starRingEnd ℂ) z ∈ Metric.closedBall 0 1
      simp only [Metric.mem_closedBall,dist_zero_right,Complex.norm_conj])
  have hconjbdy (u : ℝ) : conjD (Complex.ClosedUnitDisc.bdyPtOfReal (-u))=
      Complex.ClosedUnitDisc.bdyPtOfReal u := by
    apply Subtype.ext
    change (starRingEnd ℂ) ((Real.fourierChar (-u) : Circle) : ℂ)=
      (Real.fourierChar u : ℂ)
    change (starRingEnd ℂ) (Complex.exp ((2*Real.pi*(-u) : ℝ)*Complex.I))=
      Complex.exp ((2*Real.pi*u : ℝ)*Complex.I)
    rw [←Complex.exp_conj]
    congr 1
    simp
    left
    exact Complex.conj_ofReal 2
  let d₀ : Complex.ClosedUnitDisc ≃ₜ DiskSquare.square := conjD.trans
    ((PolygonCell.closedUnitDiscHomeomorph 6).symm.trans
      (DiskSquare.cellSquareHomeomorph rectCircleHomeomorph))
  let d := d₀.trans rectSquareProdHomeomorph
  have hd₀ (u : ℝ) (hu : u ∈ Icc (0:ℝ) 6) :
      (d₀ (Complex.ClosedUnitDisc.bdyPtOfReal (-u/6))).val=rectPerimeter u := by
    change (DiskSquare.cellSquareHomeomorph rectCircleHomeomorph
      ((PolygonCell.closedUnitDiscHomeomorph 6).symm
        (conjD (Complex.ClosedUnitDisc.bdyPtOfReal (-u/6))))).val=_
    rw [show -u/6=-(u/6) by ring,hconjbdy]
    have hsource : (PolygonCell.closedUnitDiscHomeomorph 6).symm
        (Complex.ClosedUnitDisc.bdyPtOfReal (u/6))=
        PolygonCell.ofCircle 6 (Circle.exp (2*Real.pi/6*u)) := by
      apply PolygonCell.ext
      change (Circle.exp (2*Real.pi*(u/6)) : ℂ)=(Circle.exp (2*Real.pi/6*u) : ℂ)
      congr 2
      ring
    rw [hsource,DiskSquare.cellSquareHomeomorph_ofCircle]
    exact rectCircleHomeomorph_exp u hu
  have hd (u : ℝ) (hu : u ∈ Icc (0:ℝ) 6) :
      (d (Complex.ClosedUnitDisc.bdyPtOfReal (-u/6))).val=
        ((rectPerimeter u).re,(rectPerimeter u).im) := by
    change ((d₀ (Complex.ClosedUnitDisc.bdyPtOfReal (-u/6))).val.re,
      (d₀ (Complex.ClosedUnitDisc.bdyPtOfReal (-u/6))).val.im)=_
    rw [hd₀ u hu]
  refine ⟨d,?_⟩
  intro t
  have ht0 : 0≤(t:ℝ) := t.property.1
  have ht1 : (t:ℝ)≤1 := t.property.2
  constructor
  · rw [hd t ⟨ht0,by linarith⟩]
    simp only [rectPerimeter,if_pos ht1]
  constructor
  · rw [hd (3-(t:ℝ)) ⟨by linarith,by linarith⟩]
    unfold rectPerimeter
    split_ifs <;> apply Prod.ext <;> dsimp <;> linarith
  constructor
  · rw [hd (3+(t:ℝ)) ⟨by linarith,by linarith⟩]
    unfold rectPerimeter
    split_ifs <;> apply Prod.ext <;> dsimp <;> linarith
  · rw [hd (6-(t:ℝ)) ⟨by linarith,by linarith⟩]
    unfold rectPerimeter
    split_ifs <;> apply Prod.ext <;> dsimp <;> linarith

end CurveComplex.Hyperbolic
