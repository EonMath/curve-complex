import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualLoopTransportDefinitions

namespace CurveComplex.Hyperbolic.PantsTheta
open Set Topology
open scoped unitInterval

theorem literal_meridian_witnesses (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    let b := thetaRealEmbedding (thetaVertex false 2)
    ∃ a : ActualPuncturedRealPlane, a.val = (1+ρ,0) ∧
    ∃ γ : Path a a, ∃ stem : Path b a,
      (∀ t : unitInterval, (γ t).val =
        (1+ρ*(Circle.exp (2*Real.pi*(t:ℝ)) : ℂ).re,
          ρ*(Circle.exp (2*Real.pi*(t:ℝ)) : ℂ).im)) ∧
      (∀ t : unitInterval, (stem t).val =
        ((1-(t:ℝ))*(1/2)+(t:ℝ)*(1+ρ),-1+(t:ℝ))) := by
  let a : ActualPuncturedRealPlane := ⟨(1+ρ,0), by
    constructor <;> intro h <;> have hx := congrArg Prod.fst h <;> dsimp at hx <;> linarith⟩
  have hc (t : unitInterval) :
      (1+ρ*(Circle.exp (2*Real.pi*(t:ℝ)) : ℂ).re,
          ρ*(Circle.exp (2*Real.pi*(t:ℝ)) : ℂ).im) ≠ ((0:ℝ),0) ∧
      (1+ρ*(Circle.exp (2*Real.pi*(t:ℝ)) : ℂ).re,
          ρ*(Circle.exp (2*Real.pi*(t:ℝ)) : ℂ).im) ≠ ((1:ℝ),0) := by
    let z : ℂ := Circle.exp (2*Real.pi*(t:ℝ))
    have hn : ‖z‖ = 1 := Circle.norm_coe _
    have hr : -1 ≤ z.re := by
      have := Complex.abs_re_le_norm z
      rw [hn] at this
      exact (abs_le.mp this).1
    have hz : z.re ^ 2 + z.im ^ 2 = 1 := by
      have := Complex.sq_norm z
      rw [hn] at this
      simpa [Complex.normSq_apply, pow_two] using this.symm
    constructor
    · intro h
      have hx := congrArg Prod.fst h
      change 1+ρ*z.re=0 at hx
      nlinarith
    · intro h
      have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      change 1+ρ*z.re=1 at hx
      change ρ*z.im=0 at hy
      have hre : z.re=0 := by nlinarith
      have him := (mul_eq_zero.mp hy).resolve_left hρ.ne'
      rw [hre,him] at hz
      norm_num at hz
  let γ : Path a a := {
    toFun t := ⟨_,hc t⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      have hz : Continuous (fun t : unitInterval => (Circle.exp (2*Real.pi*(t:ℝ)) : ℂ)) :=
        continuous_subtype_val.comp (Circle.exp.continuous.comp (by fun_prop))
      exact (continuous_const.add (continuous_const.mul (Complex.continuous_re.comp hz))).prodMk
        (continuous_const.mul (Complex.continuous_im.comp hz))
    source' := by apply Subtype.ext; simp [a]
    target' := by apply Subtype.ext; simp [a] }
  let stem : Path (thetaRealEmbedding (thetaVertex false 2)) a := {
    toFun t := ⟨((1-(t:ℝ))*(1/2)+(t:ℝ)*(1+ρ),-1+(t:ℝ)),by
      constructor <;> intro h
      · have hx := congrArg Prod.fst h
        have hy := congrArg Prod.snd h
        dsimp at hx hy
        have ht : (t:ℝ)=1 := by linarith
        rw [ht] at hx
        nlinarith
      · have hx := congrArg Prod.fst h
        have hy := congrArg Prod.snd h
        dsimp at hx hy
        have ht : (t:ℝ)=1 := by linarith
        rw [ht] at hx
        nlinarith⟩
    continuous_toFun := by fun_prop
    source' := by apply Subtype.ext; norm_num [thetaRealEmbedding,thetaVertex]
    target' := by apply Subtype.ext; simp [a] }
  exact ⟨a,rfl,γ,stem,fun _ => rfl,fun _ => rfl⟩
end CurveComplex.Hyperbolic.PantsTheta

namespace CurveComplex.Hyperbolic.PantsTheta
open Set Topology
open scoped unitInterval

theorem homotopic_of_convex_avoiding (S : Set (ℝ × ℝ)) (hS : Convex ℝ S)
    (havoid : ∀ z ∈ S, z ≠ ((0:ℝ),0) ∧ z ≠ ((1:ℝ),0))
    {a b : ActualPuncturedRealPlane} (p q : Path a b)
    (hp : ∀ t, (p t).val ∈ S) (hq : ∀ t, (q t).val ∈ S) :
    Path.Homotopic p q := by
  let v (s : unitInterval × unitInterval) : ℝ × ℝ :=
    (1-s.1.val) • (p s.2).val + s.1.val • (q s.2).val
  have hv (s : unitInterval × unitInterval) : v s ∈ S :=
    hS (hp s.2) (hq s.2) (sub_nonneg.mpr s.1.property.2)
      s.1.property.1 (by ring)
  refine ⟨{
    toFun := fun s => ⟨v s,havoid _ (hv s)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      have ht : Continuous (fun s : unitInterval × unitInterval => s.1.val) :=
        continuous_subtype_val.comp continuous_fst
      exact ((continuous_const.sub ht).smul
        (continuous_subtype_val.comp (p.continuous.comp continuous_snd))).add
        (ht.smul (continuous_subtype_val.comp (q.continuous.comp continuous_snd)))
    map_zero_left := by intro t; apply Subtype.ext; simp [v]
    map_one_left := by intro t; apply Subtype.ext; simp [v]
    prop' := by
      intro t s hs
      rcases hs with hs | hs
      · subst s
        apply Subtype.ext
        simp [v, ← add_smul]
      · rw [Set.mem_singleton_iff] at hs
        subst s
        apply Subtype.ext
        simp [v, ← add_smul] }⟩

theorem path_trans_mem {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (S : Set X)
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) : ∀ t, (p.trans q) t ∈ S := by
  intro t
  rw [Path.trans_apply]
  split_ifs <;> first | exact hp _ | exact hq _

end CurveComplex.Hyperbolic.PantsTheta

namespace CurveComplex.Hyperbolic.PantsTheta
open Set Topology
open scoped unitInterval

theorem literal_rectangle_enclosure
    (D : Path (thetaVertex false 2) (thetaVertex true 2))
    (T : Path (thetaVertex true 3) (thetaVertex false 3))
    (hD : ∀ t : unitInterval, (D t).val = ((t:ℝ),-1))
    (hT : ∀ t : unitInterval, (T t).val = (1-(t:ℝ),1)) :
    let b := thetaRealEmbedding (thetaVertex false 2)
    let R := (thetaLeg false 2).trans
      (T.symm.trans ((thetaLeg true 2).symm.trans D.symm))
    b.val = ((1/2:ℝ),-1) ∧
    (∀ t : unitInterval, ((R.map thetaRealEmbedding.continuous) t).val ∈
      Icc (1/2:ℝ) (3/2) ×ˢ Icc (-1:ℝ) 1) := by
  dsimp only
  refine ⟨by norm_num [thetaRealEmbedding,thetaVertex],?_⟩
  have hleg (outer : Bool) (t : unitInterval) :
      (thetaLeg outer 2 t).val.1 ∈ Icc (0:ℝ) 1 ∧
      (thetaLeg outer 2 t).val.2 ∈ Icc (-1:ℝ) 1 := by
    have h0 := t.property.1
    have h1 := t.property.2
    cases outer <;> norm_num [thetaLeg,thetaVertex,Set.mem_Icc] <;> constructor <;> linarith
  have htrans {a b c : ActualSquareTheta} (p : Path a b) (q : Path b c)
      (hp : ∀ t, (p t).val.1 ∈ Icc (0:ℝ) 1 ∧ (p t).val.2 ∈ Icc (-1:ℝ) 1)
      (hq : ∀ t, (q t).val.1 ∈ Icc (0:ℝ) 1 ∧ (q t).val.2 ∈ Icc (-1:ℝ) 1) :
      ∀ t, ((p.trans q) t).val.1 ∈ Icc (0:ℝ) 1 ∧
        ((p.trans q) t).val.2 ∈ Icc (-1:ℝ) 1 := by
    intro t
    rw [Path.trans_apply]
    split_ifs <;> first | exact hp _ | exact hq _
  have hD' (t : unitInterval) :
      (D.symm t).val.1 ∈ Icc (0:ℝ) 1 ∧ (D.symm t).val.2 ∈ Icc (-1:ℝ) 1 := by
    simp only [Path.symm_apply,Function.comp_apply,hD]
    exact ⟨(unitInterval.symm t).property,by norm_num⟩
  have hT' (t : unitInterval) :
      (T.symm t).val.1 ∈ Icc (0:ℝ) 1 ∧ (T.symm t).val.2 ∈ Icc (-1:ℝ) 1 := by
    simp only [Path.symm_apply,Function.comp_apply,hT]
    have h0 := t.property.1
    have h1 := t.property.2
    constructor
    · constructor <;> simp only [unitInterval.coe_symm_eq] <;> linarith
    · norm_num
  have hL' (t : unitInterval) :
      ((thetaLeg true 2).symm t).val.1 ∈ Icc (0:ℝ) 1 ∧
      ((thetaLeg true 2).symm t).val.2 ∈ Icc (-1:ℝ) 1 := by
    rw [Path.symm_apply]
    exact hleg true _
  intro t
  have hb := htrans _ _ (hleg false) (htrans _ _ hT' (htrans _ _ hL' hD')) t
  change (((((thetaLeg false 2).trans (T.symm.trans ((thetaLeg true 2).symm.trans D.symm))) t).val.1+1/2), ((((thetaLeg false 2).trans (T.symm.trans ((thetaLeg true 2).symm.trans D.symm))) t).val.2)) ∈ _ ×ˢ _
  simp only [Set.mem_prod,Set.mem_Icc]
  rcases hb with ⟨⟨hxl,hxu⟩,hy⟩
  exact ⟨⟨by linarith,by linarith⟩,hy⟩
end CurveComplex.Hyperbolic.PantsTheta

namespace CurveComplex.Hyperbolic.PantsTheta
open Set Topology
open scoped unitInterval

noncomputable def literalSmallCircleMap (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    C(ℝ,ActualPuncturedRealPlane) where
  toFun θ := ⟨(1+ρ*(Circle.exp θ : ℂ).re,ρ*(Circle.exp θ : ℂ).im),by
    let z : ℂ := Circle.exp θ
    have hn : ‖z‖=1 := Circle.norm_coe _
    have hr : -1 ≤ z.re := by
      have h := Complex.abs_re_le_norm z
      rw [hn] at h
      exact (abs_le.mp h).1
    have hz : z.re ^ 2 + z.im ^ 2 = 1 := by
      have h := Complex.sq_norm z
      rw [hn] at h
      simpa [Complex.normSq_apply,pow_two] using h.symm
    constructor
    · intro h
      have hx := congrArg Prod.fst h
      change 1+ρ*z.re=0 at hx
      nlinarith
    · intro h
      have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      change 1+ρ*z.re=1 at hx
      change ρ*z.im=0 at hy
      have hre : z.re=0 := by nlinarith
      have him := (mul_eq_zero.mp hy).resolve_left hρ.ne'
      rw [hre,him] at hz
      norm_num at hz⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hz : Continuous (fun θ : ℝ => (Circle.exp θ : ℂ)) :=
      continuous_subtype_val.comp Circle.exp.continuous
    exact (continuous_const.add (continuous_const.mul (Complex.continuous_re.comp hz))).prodMk
      (continuous_const.mul (Complex.continuous_im.comp hz))

@[simp]
theorem literalSmallCircleMap_val (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (θ : ℝ) : (literalSmallCircleMap ρ hρ hρhalf θ).val =
      (1+ρ*Real.cos θ,ρ*Real.sin θ) := by
  simp [literalSmallCircleMap,Circle.coe_exp,Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem literalSmallCircleMap_periodic (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    Function.Periodic (literalSmallCircleMap ρ hρ hρhalf) (2*Real.pi) := by
  intro θ
  apply Subtype.ext
  simp [literalSmallCircleMap_val,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem literalSmallCircleMap_positive_x (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (θ : ℝ) : 0 < (literalSmallCircleMap ρ hρ hρhalf θ).val.1 := by
  rw [literalSmallCircleMap_val]
  have := Real.neg_one_le_cos θ
  dsimp
  nlinarith

noncomputable def literalSmallCircleArc (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (u v : ℝ) :
    Path (literalSmallCircleMap ρ hρ hρhalf u) (literalSmallCircleMap ρ hρ hρhalf v) :=
  (Path.segment u v).map (literalSmallCircleMap ρ hρ hρhalf).continuous

@[simp]
theorem literalSmallCircleArc_val (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (u v : ℝ) (t : unitInterval) :
    (literalSmallCircleArc ρ hρ hρhalf u v t).val =
      (1+ρ*Real.cos ((1-(t:ℝ))*u+(t:ℝ)*v),
        ρ*Real.sin ((1-(t:ℝ))*u+(t:ℝ)*v)) := by
  simp [literalSmallCircleArc,Path.segment,AffineMap.lineMap_apply_module]

 theorem literalSmallCircleArc_left (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (t : unitInterval) :
    (literalSmallCircleArc ρ hρ hρhalf (5*Real.pi/4) (3*Real.pi/4) t).val.1 < 1 := by
  rw [literalSmallCircleArc_val]
  have h0 := t.property.1
  have h1 := t.property.2
  have hpi := Real.pi_pos
  have h := Real.cos_neg_of_pi_div_two_lt_of_lt
    (x := (1-(t:ℝ))*(5*Real.pi/4)+(t:ℝ)*(3*Real.pi/4))
    (by nlinarith) (by nlinarith)
  dsimp
  nlinarith

 theorem literalSmallCircleArc_top (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (t : unitInterval) :
    0 < (literalSmallCircleArc ρ hρ hρhalf (3*Real.pi/4) (Real.pi/4) t).val.2 := by
  rw [literalSmallCircleArc_val]
  have h0 := t.property.1
  have h1 := t.property.2
  have hpi := Real.pi_pos
  apply mul_pos hρ
  apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith

 theorem literalSmallCircleArc_right (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (t : unitInterval) :
    1 < (literalSmallCircleArc ρ hρ hρhalf (Real.pi/4) (-Real.pi/4) t).val.1 := by
  rw [literalSmallCircleArc_val]
  have h0 := t.property.1
  have h1 := t.property.2
  have hpi := Real.pi_pos
  have h := Real.cos_pos_of_mem_Ioo
    (x := (1-(t:ℝ))*(Real.pi/4)+(t:ℝ)*(-Real.pi/4))
    ⟨by nlinarith,by nlinarith⟩
  dsimp
  nlinarith

 theorem literalSmallCircleArc_bottom (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (t : unitInterval) :
    (literalSmallCircleArc ρ hρ hρhalf (-Real.pi/4) (-3*Real.pi/4) t).val.2 < 0 := by
  rw [literalSmallCircleArc_val]
  have h0 := t.property.1
  have h1 := t.property.2
  have hpi := Real.pi_pos
  apply mul_neg_of_pos_of_neg hρ
  apply Real.sin_neg_of_neg_of_neg_pi_lt <;> nlinarith
end CurveComplex.Hyperbolic.PantsTheta

namespace CurveComplex.Hyperbolic.PantsTheta
open scoped unitInterval

theorem quadrilateral_connector_telescope {X : Type*} [TopologicalSpace X]
    {p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : X}
    (e₀ : Path p₀ p₁) (e₁ : Path p₁ p₂) (e₂ : Path p₂ p₃) (e₃ : Path p₃ p₀)
    (a₀ : Path q₀ q₁) (a₁ : Path q₁ q₂) (a₂ : Path q₂ q₃) (a₃ : Path q₃ q₀)
    (c₀ : Path p₀ q₀) (c₁ : Path p₁ q₁) (c₂ : Path p₂ q₂) (c₃ : Path p₃ q₃)
    (h₀ : Path.Homotopic e₀ (c₀.trans (a₀.trans c₁.symm)))
    (h₁ : Path.Homotopic e₁ (c₁.trans (a₁.trans c₂.symm)))
    (h₂ : Path.Homotopic e₂ (c₂.trans (a₂.trans c₃.symm)))
    (h₃ : Path.Homotopic e₃ (c₃.trans (a₃.trans c₀.symm))) :
    Path.Homotopic (e₀.trans (e₁.trans (e₂.trans e₃)))
      (c₀.trans ((a₀.trans (a₁.trans (a₂.trans a₃))).trans c₀.symm)) := by
  apply Path.Homotopic.Quotient.exact
  have he₀ := Path.Homotopic.Quotient.eq.mpr h₀
  have he₁ := Path.Homotopic.Quotient.eq.mpr h₁
  have he₂ := Path.Homotopic.Quotient.eq.mpr h₂
  have he₃ := Path.Homotopic.Quotient.eq.mpr h₃
  simp only [Path.Homotopic.Quotient.mk_trans] at he₀ he₁ he₂ he₃ ⊢
  rw [he₀,he₁,he₂,he₃]
  simp only [Path.Homotopic.Quotient.trans_assoc]
  simp only [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.mk_symm,Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]
end CurveComplex.Hyperbolic.PantsTheta

namespace CurveComplex.Hyperbolic.PantsTheta
open scoped unitInterval

theorem periodic_angle_based_conjugacy {X : Type*} [TopologicalSpace X]
    (f : C(ℝ,X)) (L u v : ℝ) (hf : Function.Periodic f L)
    (p : Path u (u-L)) (q : Path u v) (r : Path v (v-L)) :
    Path.Homotopic ((p.map f.continuous).cast rfl (hf.sub_eq u).symm)
      ((q.map f.continuous).trans
        (((r.map f.continuous).cast rfl (hf.sub_eq v).symm).trans
          (q.map f.continuous).symm)) := by
  let shift : ℝ → ℝ := fun x => x-L
  let q' : Path (v-L) (u-L) := q.symm.map (show Continuous shift by fun_prop)
  have h := (SimplyConnectedSpace.paths_homotopic p (q.trans (r.trans q'))).map f
  have hc := h.pathCast rfl (hf.sub_eq u).symm
  convert hc using 1
  ext t
  simp only [Path.cast_coe,Path.map_trans,Path.trans_apply,Path.symm_apply,
    Path.map_coe,Function.comp_apply]
  split_ifs <;> try rfl
  simp only [q',Path.map_coe,Path.symm_apply,Function.comp_apply,shift]
  exact (hf.sub_eq _).symm
end CurveComplex.Hyperbolic.PantsTheta

namespace CurveComplex.Hyperbolic.PantsTheta
open Set Topology
open scoped unitInterval

def meridianHalfPlane (a b : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 < z.1 ∧ 0 < a*(z.1-1)+b*z.2}

theorem meridianHalfPlane_convex (a b : ℝ) : Convex ℝ (meridianHalfPlane a b) := by
  intro x hx y hy u v hu hv huv
  rcases hx with ⟨hx,hx'⟩
  rcases hy with ⟨hy,hy'⟩
  change 0 < u*x.1+v*y.1 ∧ 0 < a*(u*x.1+v*y.1-1)+b*(u*x.2+v*y.2)
  have h := mul_nonneg hu hx.le
  have h' := mul_nonneg hv hy.le
  have hlt : 0 < u*x.1+v*y.1 := by
    by_cases hu' : 0 < u
    · exact add_pos_of_pos_of_nonneg (mul_pos hu' hx) h'
    · have hv' : 0 < v := by linarith
      exact add_pos_of_nonneg_of_pos h (mul_pos hv' hy)
  refine ⟨hlt,?_⟩
  have he : a*(u*x.1+v*y.1-1)+b*(u*x.2+v*y.2) =
      u*(a*(x.1-1)+b*x.2)+v*(a*(y.1-1)+b*y.2) := by
    nlinarith [congrArg (fun t : ℝ => a*t) huv]
  rw [he]
  by_cases hu' : 0 < u
  · exact add_pos_of_pos_of_nonneg (mul_pos hu' hx') (mul_nonneg hv hy'.le)
  · have hv' : 0 < v := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg hu hx'.le) (mul_pos hv' hy')

theorem meridianHalfPlane_avoids (a b : ℝ) (z : ℝ × ℝ)
    (hz : z ∈ meridianHalfPlane a b) : z ≠ ((0:ℝ),0) ∧ z ≠ ((1:ℝ),0) := by
  constructor <;> intro h <;> rw [h] at hz <;> norm_num [meridianHalfPlane] at hz

noncomputable def convexAvoidingSegment (S : Set (ℝ × ℝ)) (hS : Convex ℝ S)
    (havoid : ∀ z ∈ S, z ≠ ((0:ℝ),0) ∧ z ≠ ((1:ℝ),0))
    (a b : ActualPuncturedRealPlane) (ha : a.val ∈ S) (hb : b.val ∈ S) : Path a b where
  toFun t := ⟨(1-(t:ℝ)) • a.val+(t:ℝ) • b.val,
    havoid _ (hS ha hb (sub_nonneg.mpr t.property.2) t.property.1 (by ring))⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

@[simp]
theorem convexAvoidingSegment_mem (S : Set (ℝ × ℝ)) (hS : Convex ℝ S)
    (havoid : ∀ z ∈ S, z ≠ ((0:ℝ),0) ∧ z ≠ ((1:ℝ),0))
    (a b : ActualPuncturedRealPlane) (ha : a.val ∈ S) (hb : b.val ∈ S)
    (t : unitInterval) : (convexAvoidingSegment S hS havoid a b ha hb t).val ∈ S :=
  hS ha hb (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

def lowerStemRegion : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ z.2 ≤ 0 ∧ (z.2=0 → 1 < z.1)}

theorem lowerStemRegion_avoids (z : ℝ × ℝ) (hz : z ∈ lowerStemRegion) :
    z ≠ ((0:ℝ),0) ∧ z ≠ ((1:ℝ),0) := by
  constructor <;> intro h <;> rw [h] at hz <;> norm_num [lowerStemRegion] at hz

theorem lowerStemRegion_convex : Convex ℝ lowerStemRegion := by
  intro x hx y hy u v hu hv huv
  rcases hx with ⟨hx,hx0,hx1⟩
  rcases hy with ⟨hy,hy0,hy1⟩
  change 0 < u*x.1+v*y.1 ∧ u*x.2+v*y.2 ≤ 0 ∧
    (u*x.2+v*y.2=0 → 1 < u*x.1+v*y.1)
  have hux := mul_nonneg hu hx.le
  have hvy := mul_nonneg hv hy.le
  refine ⟨?_,add_nonpos (mul_nonpos_of_nonneg_of_nonpos hu hx0)
    (mul_nonpos_of_nonneg_of_nonpos hv hy0),?_⟩
  · by_cases hu' : 0 < u
    · exact add_pos_of_pos_of_nonneg (mul_pos hu' hx) hvy
    · have hv' : 0 < v := by linarith
      exact add_pos_of_nonneg_of_pos hux (mul_pos hv' hy)
  · intro h
    have hux0 : u*x.2=0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hv hy0]
    have hvy0 : v*y.2=0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hu hx0]
    by_cases hu' : u=0
    · have hv' : v=1 := by linarith
      simp only [hu',hv',zero_mul,one_mul,zero_add] at h ⊢
      exact hy1 h
    · by_cases hv' : v=0
      · have hu'' : u=1 := by linarith
        simp only [hv',hu'',zero_mul,one_mul,add_zero] at h ⊢
        exact hx1 h
      · have hx' := hx1 ((mul_eq_zero.mp hux0).resolve_left hu')
        have hy' := hy1 ((mul_eq_zero.mp hvy0).resolve_left hv')
        have hu'' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu')
        have hv'' : 0 < v := lt_of_le_of_ne hv (Ne.symm hv')
        nlinarith [mul_pos hu'' (sub_pos.mpr hx'),mul_pos hv'' (sub_pos.mpr hy')]
end CurveComplex.Hyperbolic.PantsTheta

namespace CurveComplex.Hyperbolic.PantsTheta
open Set Topology
open scoped unitInterval

-- This file is concatenated after CircleGeometry and SafeConvexRegions in the package.
theorem literalSmallCircleArc_lower_stem_region (ρ : ℝ) (hρ : 0 < ρ)
    (hρhalf : ρ < 1/2) (t : unitInterval) :
    (literalSmallCircleArc ρ hρ hρhalf (5*Real.pi/4) (2*Real.pi) t).val ∈ lowerStemRegion := by
  have hp : 0 < (literalSmallCircleArc ρ hρ hρhalf (5*Real.pi/4) (2*Real.pi) t).val.1 :=
    literalSmallCircleMap_positive_x ρ hρ hρhalf _
  rw [literalSmallCircleArc_val] at hp ⊢
  refine ⟨hp,?_,?_⟩
  · dsimp
    apply mul_nonpos_of_nonneg_of_nonpos hρ.le
    let θ : ℝ := (1-(t:ℝ))*(5*Real.pi/4)+(t:ℝ)*(2*Real.pi)
    have h0 := t.property.1
    have h1 := t.property.2
    have hpi := Real.pi_pos
    have ht : Real.sin θ = Real.sin (θ-2*Real.pi) := (Real.sin_sub_two_pi θ).symm
    rw [ht]
    apply Real.sin_nonpos_of_nonpos_of_neg_pi_le <;> dsimp [θ] <;> nlinarith
  · intro hy
    dsimp at hy ⊢
    by_cases ht : (t:ℝ)=1
    · simp only [ht,sub_self,zero_mul,one_mul,zero_add,Real.cos_two_pi]
      linarith
    · have h0 := t.property.1
      have h1 : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 ht
      have hpi := Real.pi_pos
      let θ : ℝ := (1-(t:ℝ))*(5*Real.pi/4)+(t:ℝ)*(2*Real.pi)
      have hs : Real.sin θ < 0 := by
        rw [← Real.sin_sub_two_pi θ]
        apply Real.sin_neg_of_neg_of_neg_pi_lt <;> dsimp [θ] <;> nlinarith
      have he : Real.sin θ=0 := (mul_eq_zero.mp hy).resolve_left hρ.ne'
      exact False.elim (hs.ne he)

theorem literal_stem_lower_region (ρ : ℝ) (hρ : 0 < ρ)
    {a : ActualPuncturedRealPlane}
    (stem : Path (thetaRealEmbedding (thetaVertex false 2)) a)
    (hs : ∀ t : unitInterval, (stem t).val =
      ((1-(t:ℝ))*(1/2)+(t:ℝ)*(1+ρ),-1+(t:ℝ))) :
    ∀ t, (stem t).val ∈ lowerStemRegion := by
  intro t
  rw [hs]
  have h0 := t.property.1
  have h1 := t.property.2
  change 0 < (1-(t:ℝ))*(1/2)+(t:ℝ)*(1+ρ) ∧
    -1+(t:ℝ) ≤ 0 ∧ (-1+(t:ℝ)=0 → 1 < (1-(t:ℝ))*(1/2)+(t:ℝ)*(1+ρ))
  refine ⟨?_,by linarith,?_⟩
  · nlinarith [mul_nonneg h0 hρ.le]
  · intro h
    have ht : (t:ℝ)=1 := by linarith
    rw [ht]
    nlinarith
end CurveComplex.Hyperbolic.PantsTheta

namespace CurveComplex.Hyperbolic.PantsTheta
open Set Topology
open scoped unitInterval

theorem four_sector_rectangle_reduction
    (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    {p₀ p₁ p₂ p₃ : ActualPuncturedRealPlane}
    (e₀ : Path p₀ p₁) (e₁ : Path p₁ p₂) (e₂ : Path p₂ p₃) (e₃ : Path p₃ p₀)
    (he₀ : ∀ t, (e₀ t).val ∈ meridianHalfPlane (-1) 0)
    (he₁ : ∀ t, (e₁ t).val ∈ meridianHalfPlane 0 1)
    (he₂ : ∀ t, (e₂ t).val ∈ meridianHalfPlane 1 0)
    (he₃ : ∀ t, (e₃ t).val ∈ meridianHalfPlane 0 (-1)) :
    let f := literalSmallCircleMap ρ hρ hρhalf
    let a₀ := literalSmallCircleArc ρ hρ hρhalf (5*Real.pi/4) (3*Real.pi/4)
    let a₁ := literalSmallCircleArc ρ hρ hρhalf (3*Real.pi/4) (Real.pi/4)
    let a₂ := literalSmallCircleArc ρ hρ hρhalf (Real.pi/4) (-Real.pi/4)
    ∃ h : f (5*Real.pi/4) = f (-3*Real.pi/4),
    let a₃ := (literalSmallCircleArc ρ hρ hρhalf (-Real.pi/4) (-3*Real.pi/4)).cast rfl h
    ∃ c : Path p₀ (f (5*Real.pi/4)),
      (∀ t, (c t).val ∈ meridianHalfPlane (-1) 0 ∩ meridianHalfPlane 0 (-1)) ∧
      Path.Homotopic (e₀.trans (e₁.trans (e₂.trans e₃)))
        (c.trans ((a₀.trans (a₁.trans (a₂.trans a₃))).trans c.symm)) := by
  dsimp only
  let f := literalSmallCircleMap ρ hρ hρhalf
  let L := meridianHalfPlane (-1) 0
  let U := meridianHalfPlane 0 1
  let R := meridianHalfPlane 1 0
  let B := meridianHalfPlane 0 (-1)
  have hh : f (5*Real.pi/4) = f (-3*Real.pi/4) := by
    have h := (literalSmallCircleMap_periodic ρ hρ hρhalf).sub_eq (5*Real.pi/4)
    convert h.symm using 1 <;> congr 1 <;> ring
  refine ⟨hh,?_⟩
  let a₀ := literalSmallCircleArc ρ hρ hρhalf (5*Real.pi/4) (3*Real.pi/4)
  let a₁ := literalSmallCircleArc ρ hρ hρhalf (3*Real.pi/4) (Real.pi/4)
  let a₂ := literalSmallCircleArc ρ hρ hρhalf (Real.pi/4) (-Real.pi/4)
  let a₃ := (literalSmallCircleArc ρ hρ hρhalf (-Real.pi/4) (-3*Real.pi/4)).cast rfl hh
  have ha₀ : ∀ t, (a₀ t).val ∈ L := by
    intro t
    have hp : 0 < (a₀ t).val.1 := literalSmallCircleMap_positive_x ρ hρ hρhalf _
    have hs := literalSmallCircleArc_left ρ hρ hρhalf t
    exact ⟨hp,by change 0 < -1*((a₀ t).val.1-1)+0*(a₀ t).val.2;dsimp [a₀] at hs ⊢;linarith⟩
  have ha₁ : ∀ t, (a₁ t).val ∈ U := by
    intro t
    have hp : 0 < (a₁ t).val.1 := literalSmallCircleMap_positive_x ρ hρ hρhalf _
    have hs := literalSmallCircleArc_top ρ hρ hρhalf t
    exact ⟨hp,by change 0 < 0*((a₁ t).val.1-1)+1*(a₁ t).val.2;dsimp [a₁] at hs ⊢;linarith⟩
  have ha₂ : ∀ t, (a₂ t).val ∈ R := by
    intro t
    have hp : 0 < (a₂ t).val.1 := literalSmallCircleMap_positive_x ρ hρ hρhalf _
    have hs := literalSmallCircleArc_right ρ hρ hρhalf t
    exact ⟨hp,by change 0 < 1*((a₂ t).val.1-1)+0*(a₂ t).val.2;dsimp [a₂] at hs ⊢;linarith⟩
  have ha₃ : ∀ t, (a₃ t).val ∈ B := by
    intro t
    have hp : 0 < (a₃ t).val.1 := literalSmallCircleMap_positive_x ρ hρ hρhalf _
    have hs := literalSmallCircleArc_bottom ρ hρ hρhalf t
    exact ⟨hp,by change 0 < 0*((a₃ t).val.1-1)+(-1)*(a₃ t).val.2;dsimp [a₃] at hs ⊢;linarith⟩
  have hc₀ : p₀.val ∈ L ∩ B := ⟨by simpa using he₀ 0,by simpa using he₃ 1⟩
  have hc₁ : p₁.val ∈ L ∩ U := ⟨by simpa using he₀ 1,by simpa using he₁ 0⟩
  have hc₂ : p₂.val ∈ U ∩ R := ⟨by simpa using he₁ 1,by simpa using he₂ 0⟩
  have hc₃ : p₃.val ∈ R ∩ B := ⟨by simpa using he₂ 1,by simpa using he₃ 0⟩
  have hq₀ : (f (5*Real.pi/4)).val ∈ L ∩ B :=
    ⟨by simpa [a₀,f] using ha₀ 0,by simpa [a₃,f] using ha₃ 1⟩
  have hq₁ : (f (3*Real.pi/4)).val ∈ L ∩ U :=
    ⟨by simpa [a₀,f] using ha₀ 1,by simpa [a₁,f] using ha₁ 0⟩
  have hq₂ : (f (Real.pi/4)).val ∈ U ∩ R :=
    ⟨by simpa [a₁,f] using ha₁ 1,by simpa [a₂,f] using ha₂ 0⟩
  have hq₃ : (f (-Real.pi/4)).val ∈ R ∩ B :=
    ⟨by simpa [a₂,f] using ha₂ 1,by simpa [a₃,f] using ha₃ 0⟩
  let c₀ := convexAvoidingSegment (L ∩ B)
    ((meridianHalfPlane_convex (-1) 0).inter (meridianHalfPlane_convex 0 (-1)))
    (fun z hz => meridianHalfPlane_avoids (-1) 0 z hz.1) p₀ (f (5*Real.pi/4)) hc₀ hq₀
  let c₁ := convexAvoidingSegment (L ∩ U)
    ((meridianHalfPlane_convex (-1) 0).inter (meridianHalfPlane_convex 0 1))
    (fun z hz => meridianHalfPlane_avoids (-1) 0 z hz.1) p₁ (f (3*Real.pi/4)) hc₁ hq₁
  let c₂ := convexAvoidingSegment (U ∩ R)
    ((meridianHalfPlane_convex 0 1).inter (meridianHalfPlane_convex 1 0))
    (fun z hz => meridianHalfPlane_avoids 0 1 z hz.1) p₂ (f (Real.pi/4)) hc₂ hq₂
  let c₃ := convexAvoidingSegment (R ∩ B)
    ((meridianHalfPlane_convex 1 0).inter (meridianHalfPlane_convex 0 (-1)))
    (fun z hz => meridianHalfPlane_avoids 1 0 z hz.1) p₃ (f (-Real.pi/4)) hc₃ hq₃
  have hm₀ : ∀ t, (c₀ t).val ∈ L ∩ B := fun t => convexAvoidingSegment_mem _ _ _ _ _ _ _ t
  have hm₁ : ∀ t, (c₁ t).val ∈ L ∩ U := fun t => convexAvoidingSegment_mem _ _ _ _ _ _ _ t
  have hm₂ : ∀ t, (c₂ t).val ∈ U ∩ R := fun t => convexAvoidingSegment_mem _ _ _ _ _ _ _ t
  have hm₃ : ∀ t, (c₃ t).val ∈ R ∩ B := fun t => convexAvoidingSegment_mem _ _ _ _ _ _ _ t
  have htrans {x y z : ActualPuncturedRealPlane} (p : Path x y) (q : Path y z)
      (S : Set (ℝ × ℝ)) (hp : ∀ t, (p t).val ∈ S) (hq : ∀ t, (q t).val ∈ S) :
      ∀ t, ((p.trans q) t).val ∈ S :=
    path_trans_mem p q {z | z.val ∈ S} hp hq
  have hsymm {x y : ActualPuncturedRealPlane} (p : Path x y)
      (S : Set (ℝ × ℝ)) (hp : ∀ t, (p t).val ∈ S) : ∀ t, (p.symm t).val ∈ S := by
    intro t
    exact hp (unitInterval.symm t)
  refine ⟨c₀,hm₀,?_⟩
  apply quadrilateral_connector_telescope e₀ e₁ e₂ e₃ a₀ a₁ a₂ a₃ c₀ c₁ c₂ c₃
  · exact homotopic_of_convex_avoiding L (meridianHalfPlane_convex _ _)
      (meridianHalfPlane_avoids _ _) _ _ he₀
      (htrans _ _ L (fun t => (hm₀ t).1)
        (htrans _ _ L ha₀ (hsymm _ L (fun t => (hm₁ t).1))))
  · exact homotopic_of_convex_avoiding U (meridianHalfPlane_convex _ _)
      (meridianHalfPlane_avoids _ _) _ _ he₁
      (htrans _ _ U (fun t => (hm₁ t).2)
        (htrans _ _ U ha₁ (hsymm _ U (fun t => (hm₂ t).1))))
  · exact homotopic_of_convex_avoiding R (meridianHalfPlane_convex _ _)
      (meridianHalfPlane_avoids _ _) _ _ he₂
      (htrans _ _ R (fun t => (hm₂ t).2)
        (htrans _ _ R ha₂ (hsymm _ R (fun t => (hm₃ t).1))))
  · exact homotopic_of_convex_avoiding B (meridianHalfPlane_convex _ _)
      (meridianHalfPlane_avoids _ _) _ _ he₃
      (htrans _ _ B (fun t => (hm₃ t).2)
        (htrans _ _ B ha₃ (hsymm _ B (fun t => (hm₀ t).2))))
end CurveComplex.Hyperbolic.PantsTheta

namespace CurveComplex.Hyperbolic.PantsTheta
open Set Topology
open scoped unitInterval

theorem four_arc_literal_circle_conjugacy
    (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (h : literalSmallCircleMap ρ hρ hρhalf (5*Real.pi/4) =
      literalSmallCircleMap ρ hρ hρhalf (-3*Real.pi/4))
    (γ : Path (literalSmallCircleMap ρ hρ hρhalf (2*Real.pi))
      (literalSmallCircleMap ρ hρ hρhalf (2*Real.pi)))
    (hγ : ∀ t : unitInterval, (γ t).val =
      (1+ρ*(Circle.exp (2*Real.pi*(t:ℝ)) : ℂ).re,
        ρ*(Circle.exp (2*Real.pi*(t:ℝ)) : ℂ).im)) :
    let a₀ := literalSmallCircleArc ρ hρ hρhalf (5*Real.pi/4) (3*Real.pi/4)
    let a₁ := literalSmallCircleArc ρ hρ hρhalf (3*Real.pi/4) (Real.pi/4)
    let a₂ := literalSmallCircleArc ρ hρ hρhalf (Real.pi/4) (-Real.pi/4)
    let a₃ := (literalSmallCircleArc ρ hρ hρhalf (-Real.pi/4) (-3*Real.pi/4)).cast rfl h
    let q := literalSmallCircleArc ρ hρ hρhalf (5*Real.pi/4) (2*Real.pi)
    Path.Homotopic (a₀.trans (a₁.trans (a₂.trans a₃)))
      (q.trans (γ.symm.trans q.symm)) := by
  dsimp only
  let f := literalSmallCircleMap ρ hρ hρhalf
  let L := 2*Real.pi
  let u := 5*Real.pi/4
  let v := 2*Real.pi
  let p : Path u (u-L) := (Path.segment u (3*Real.pi/4)).trans
    ((Path.segment (3*Real.pi/4) (Real.pi/4)).trans
      ((Path.segment (Real.pi/4) (-Real.pi/4)).trans (Path.segment (-Real.pi/4) (u-L))))
  let q : Path u v := Path.segment u v
  let r : Path v (v-L) := Path.segment v (v-L)
  have hp := periodic_angle_based_conjugacy f L u v
    (literalSmallCircleMap_periodic ρ hρ hρhalf) p q r
  have hr : (r.map f.continuous).cast rfl
      ((literalSmallCircleMap_periodic ρ hρ hρhalf).sub_eq v).symm = γ.symm := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change (f (r t)).val = (γ (unitInterval.symm t)).val
    rw [hγ]
    dsimp only [r,f]
    rw [literalSmallCircleMap_val]
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,
      Circle.coe_exp,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,
      unitInterval.coe_symm_eq]
    dsimp [v,L]
    congr 2 <;> ring
  rw [hr] at hp
  convert hp using 1
  apply Path.ext
  funext t
  dsimp only [p]
  simp only [Path.cast_coe,Path.map_trans,Path.trans_apply,Path.map_coe,
    Function.comp_apply]
  split_ifs <;> try rfl
  apply Subtype.ext
  simp only [literalSmallCircleArc,Path.cast_coe,Path.map_coe,Function.comp_apply]
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  dsimp [p,u,L]
  congr 2 <;> ring
  all_goals rfl
end CurveComplex.Hyperbolic.PantsTheta

namespace CurveComplex.Hyperbolic.PantsTheta
open Set Topology
open scoped unitInterval

/-- The shifted middle rectangle is the clockwise small-circle meridian,
conjugated by the literal straight stem in the same twice-punctured plane. -/
theorem actual_theta_middle_rectangle_literal_small_circle_conjugacy
    (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (D : Path (thetaVertex false 2) (thetaVertex true 2))
    (T : Path (thetaVertex true 3) (thetaVertex false 3))
    (hD : ∀ t : unitInterval, (D t).val = ((t:ℝ),-1))
    (hT : ∀ t : unitInterval, (T t).val = (1-(t:ℝ),1)) :
    let b := thetaRealEmbedding (thetaVertex false 2)
    let R := (thetaLeg false 2).trans
      (T.symm.trans ((thetaLeg true 2).symm.trans D.symm))
    b.val = ((1/2:ℝ),-1) ∧
    (∀ t : unitInterval, ((R.map thetaRealEmbedding.continuous) t).val ∈
      Icc (1/2:ℝ) (3/2) ×ˢ Icc (-1:ℝ) 1) ∧
    ∃ a : ActualPuncturedRealPlane, a.val = (1+ρ,0) ∧
    ∃ γ : Path a a, ∃ stem : Path b a,
      (∀ t : unitInterval, (γ t).val =
        (1+ρ*(Circle.exp (2*Real.pi*(t:ℝ)) : ℂ).re,
          ρ*(Circle.exp (2*Real.pi*(t:ℝ)) : ℂ).im)) ∧
      (∀ t : unitInterval, (stem t).val =
        ((1-(t:ℝ))*(1/2)+(t:ℝ)*(1+ρ),-1+(t:ℝ))) ∧
      Path.Homotopic (R.map thetaRealEmbedding.continuous)
        (stem.trans (γ.symm.trans stem.symm)) := by
  have hb := literal_rectangle_enclosure D T hD hT
  rcases literal_meridian_witnesses ρ hρ hρhalf with ⟨a,ha,γ,stem,hγ,hstem⟩
  dsimp only at hb ⊢
  refine ⟨hb.1,hb.2,a,ha,γ,stem,hγ,hstem,?_⟩
  have haeq : a = literalSmallCircleMap ρ hρ hρhalf (2*Real.pi) := by
    apply Subtype.ext
    rw [ha,literalSmallCircleMap_val]
    simp
  subst a
  let e₀ := (thetaLeg false 2).map thetaRealEmbedding.continuous
  let e₁ := T.symm.map thetaRealEmbedding.continuous
  let e₂ := (thetaLeg true 2).symm.map thetaRealEmbedding.continuous
  let e₃ := D.symm.map thetaRealEmbedding.continuous
  have he₀ : ∀ t, (e₀ t).val ∈ meridianHalfPlane (-1) 0 := by
    intro t
    norm_num [e₀,Path.map_coe,Function.comp_apply,thetaRealEmbedding,thetaLeg,thetaVertex,meridianHalfPlane]
  have he₁ : ∀ t, (e₁ t).val ∈ meridianHalfPlane 0 1 := by
    intro t
    have h0 := t.property.1
    have h1 := t.property.2
    change 0 < (T (unitInterval.symm t)).val.1+1/2 ∧
      0 < 0*((T (unitInterval.symm t)).val.1+1/2-1)+1*(T (unitInterval.symm t)).val.2
    rw [hT]
    simp only [Prod.fst,Prod.snd,unitInterval.coe_symm_eq]
    constructor <;> linarith
  have he₂ : ∀ t, (e₂ t).val ∈ meridianHalfPlane 1 0 := by
    intro t
    norm_num [e₂,Path.map_coe,Function.comp_apply,thetaRealEmbedding,Path.symm_apply,Function.comp_apply,
      thetaLeg,thetaVertex,meridianHalfPlane]
  have he₃ : ∀ t, (e₃ t).val ∈ meridianHalfPlane 0 (-1) := by
    intro t
    have h0 := t.property.1
    have h1 := t.property.2
    change 0 < (D (unitInterval.symm t)).val.1+1/2 ∧
      0 < 0*((D (unitInterval.symm t)).val.1+1/2-1)+(-1)*(D (unitInterval.symm t)).val.2
    rw [hD]
    simp only [Prod.fst,Prod.snd,unitInterval.coe_symm_eq]
    constructor <;> linarith
  rcases four_sector_rectangle_reduction ρ hρ hρhalf e₀ e₁ e₂ e₃ he₀ he₁ he₂ he₃ with
    ⟨h,c,hcmem,hrect⟩
  let q := literalSmallCircleArc ρ hρ hρhalf (5*Real.pi/4) (2*Real.pi)
  have hcirc := four_arc_literal_circle_conjugacy ρ hρ hρhalf h γ hγ
  have hloop := hrect.trans ((Path.Homotopic.refl c).hcomp
    (hcirc.hcomp (Path.Homotopic.refl c.symm)))
  let cσ := c.trans q
  have hcmem' : ∀ t, (c t).val ∈ lowerStemRegion := by
    intro t
    rcases hcmem t with ⟨⟨hx,hl⟩,⟨_,hbottom⟩⟩
    change 0 < (c t).val.1 ∧ (c t).val.2 ≤ 0 ∧
      ((c t).val.2=0 → 1 < (c t).val.1)
    change 0 < 0*((c t).val.1-1)+(-1)*(c t).val.2 at hbottom
    refine ⟨hx,by linarith,?_⟩
    intro hzero
    linarith
  have hσ : Path.Homotopic cσ stem := by
    apply homotopic_of_convex_avoiding lowerStemRegion lowerStemRegion_convex
      lowerStemRegion_avoids
    · exact path_trans_mem c q {z | z.val ∈ lowerStemRegion} hcmem'
        (literalSmallCircleArc_lower_stem_region ρ hρ hρhalf)
    · exact literal_stem_lower_region ρ hρ stem hstem
  have hreassoc : Path.Homotopic
      (c.trans ((q.trans (γ.symm.trans q.symm)).trans c.symm))
      (cσ.trans (γ.symm.trans cσ.symm)) := by
    apply Path.Homotopic.Quotient.exact
    simp only [cσ,Path.trans_symm,Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.trans_assoc]
  have hfinal := hloop.trans (hreassoc.trans
    (hσ.hcomp ((Path.Homotopic.refl γ.symm).hcomp hσ.symm₂)))
  simpa only [Path.map_trans] using hfinal
end CurveComplex.Hyperbolic.PantsTheta
