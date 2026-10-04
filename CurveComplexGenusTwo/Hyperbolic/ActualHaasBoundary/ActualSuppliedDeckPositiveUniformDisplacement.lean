import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualDeckDevelopmentIsometryPROVED
namespace CurveComplex.Hyperbolic
open Set Topology
open scoped UpperHalfPlane

/-- Positive uniform displacement of each nonidentity element of the actual
supplied quotient-cover action over a compact locally isometric base. -/
theorem actual_supplied_deck_positive_uniform_displacement
    {E G : Type} [MetricSpace E] [CompactSpace E] [Group G]
    (a : MulAction G H2) (p : H2 → E)
    (hq : letI := a; IsQuotientCoveringMap p G)
    (hmetric : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, dist (p y) (p z) = dist y z)
    (δ : G) (hδ : δ ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : H2,
      ε ≤ dist z (@SMul.smul G H2 a.toSMul δ z) := by
  exact open Matrix in
  open scoped MatrixGroups unitInterval in
  by
    classical
    letI := a
    let actualCoveringMap := hq.isCoveringMap
    have fiber_nonempty (x : E) : Nonempty (p ⁻¹' {x}) := by
      obtain ⟨z,hz⟩ := hq.surjective x
      exact ⟨⟨z,hz⟩⟩
    letI (x : E) : Nonempty (p ⁻¹' {x}) := fiber_nonempty x
    let actualTrivialization (x : E) := (actualCoveringMap x).toTrivialization
    have uniform_evenly_covered_radius : ∃ ε : ℝ, 0 < ε ∧ ∀ x : E,
        ∃ b : E, Metric.ball x ε ⊆ (actualTrivialization b).baseSet := by
      obtain ⟨ε,hε,hcover⟩ := lebesgue_number_lemma_of_metric isCompact_univ
        (fun x => (actualTrivialization x).open_baseSet)
        (show Set.univ ⊆ ⋃ x, (actualTrivialization x).baseSet from
          fun x _ => Set.mem_iUnion.mpr ⟨x,(actualCoveringMap x).mem_toTrivialization_baseSet⟩)
      exact ⟨ε,hε,fun x => hcover x (Set.mem_univ x)⟩
    have zero_eq_I : verticalPath 0 = UpperHalfPlane.I := by
      apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
    have vertical_radius_sphere (r : ℝ) (hr : 0 ≤ r) (z : H2)
        (h : dist UpperHalfPlane.I z = r) :
        Real.exp r * (z.re ^ 2 + z.im ^ 2 + 1) =
          z.im * (1 + (Real.exp r) ^ 2) := by
      have hstd : dist (verticalPath 0) (verticalPath r) = r := by
        simpa [Real.dist_eq,abs_of_nonneg hr,abs_of_nonpos (neg_nonpos.mpr hr)] using
          verticalPath_isometry.dist_eq 0 r
      have hc := congrArg Real.cosh (h.trans (zero_eq_I ▸ hstd).symm)
      rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc
      simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im] at hc
      simp only [UpperHalfPlane.I_re,UpperHalfPlane.I_im,zero_sub,neg_sq,
        one_pow,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hc
      field_simp at hc
      nlinarith [hc]
    have denominator_nonzero (a b : ℝ) (hab : 0 < a^2+b^2) (w : H2) :
        (-(b : ℂ) * (w : ℂ) + a) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp [Complex.mul_im] at him
      have hb : b = 0 := by
        rcases him with hb | hw
        · exact hb
        · exact (w.im_pos.ne' hw).elim
      have ha : a ≠ 0 := by
        intro ha
        rw [ha,hb] at hab
        norm_num at hab
      exact ha (by simpa [hb] using h)
    have rotation_maps_vertical_radius (r : ℝ) (hr : 0 ≤ r) (z : H2)
        (h : dist UpperHalfPlane.I z = r)
        (hab : 0 < (1-Real.exp r*z.im)^2+z.re^2) :
        (stabilizerRotation (1-Real.exp r*z.im) z.re hab • verticalPath r : H2) = z := by
      let a := 1-Real.exp r*z.im
      let b := z.re
      have hsphere := vertical_radius_sphere r hr z h
      have hEim : (Complex.exp (r : ℂ)).im = 0 := by
        simpa using Complex.exp_ofReal_im r
      have hEre : (Complex.exp (r : ℂ)).re = Real.exp r := by
        simpa using Complex.exp_ofReal_re r
      apply UpperHalfPlane.coe_injective
      rw [stabilizerRotation_coe_smul]
      apply (div_eq_iff (denominator_nonzero a b hab (verticalPath r))).2
      apply Complex.ext
      · simp [verticalPath,Complex.add_re,Complex.mul_re,Complex.neg_re,
          Complex.mul_im,Complex.neg_im]
        try rw [hEim]
        dsimp [a,b]
        ring
      · simp [verticalPath,Complex.add_im,Complex.mul_im,Complex.neg_im,
          Complex.mul_re,Complex.neg_re]
        try rw [hEre]
        dsimp [a,b]
        nlinarith [hsphere]
    have exists_stabilizer_radius (r : ℝ) (hr : 0 ≤ r) (z : H2) (h : dist UpperHalfPlane.I z = r) :
        ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = UpperHalfPlane.I ∧ e (verticalPath r) = z := by
      let a : ℝ := 1-Real.exp r*z.im
      let b : ℝ := z.re
      by_cases hpole : a = 0 ∧ b = 0
      · have him : z.im = Real.exp (-r) := by
          have he : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
          have ha : Real.exp r * z.im = 1 := by dsimp [a] at hpole;linarith [hpole.1]
          rw [Real.exp_neg,←one_div]
          exact (eq_div_iff he).2 (by simpa [mul_comm] using ha)
        have hz : z = verticalPath (-r) := by
          apply UpperHalfPlane.ext_re_im
          · simpa [verticalPath,b] using hpole.2
          · simpa [verticalPath] using him
        refine ⟨IsometryEquiv.constSMul
          (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S),?_,?_⟩
        · rw [←zero_eq_I]
          change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath 0
          have hh := modular_S_verticalPath 0
          change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath (-0) at hh
          simpa only [neg_zero] using hh
        · rw [hz]
          change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath r : H2) = verticalPath (-r)
          exact modular_S_verticalPath r
      · have hab : 0 < a^2+b^2 := by
          by_contra hn
          have ha : a = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
          have hb : b = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
          exact hpole ⟨ha,hb⟩
        refine ⟨IsometryEquiv.constSMul (stabilizerRotation a b hab),?_,?_⟩
        · exact stabilizerRotation_fixes_I a b hab
        · exact rotation_maps_vertical_radius r hr z h hab
    have ordered_pair_alignment (x y : H2) :
        ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = x ∧ e (verticalPath (dist x y)) = y := by
      let e0 : H2 ≃ᵢ H2 := IsometryEquiv.constSMul x.toSL2R
      have he0 : e0 UpperHalfPlane.I = x := x.toSL2R_smul_I
      let w := e0.symm y
      have hw : dist UpperHalfPlane.I w = dist x y := by
        have hd := e0.isometry.dist_eq UpperHalfPlane.I (e0.symm y)
        rw [e0.apply_symm_apply,he0] at hd
        exact hd.symm
      obtain ⟨s,hs0,hsr⟩ := exists_stabilizer_radius (dist x y) dist_nonneg w hw
      refine ⟨s.trans e0,?_,?_⟩
      · rw [IsometryEquiv.trans_apply,hs0,he0]
      · rw [IsometryEquiv.trans_apply,hsr]
        exact e0.apply_symm_apply y
    have actual_segment (x y : H2) :
        ∃ γ : Path x y, ∀ s t : unitInterval,
          dist (γ s) (γ t) = dist x y * dist (s : ℝ) (t : ℝ) := by
      obtain ⟨e,he0,he1⟩ := ordered_pair_alignment x y
      let γ : Path x y := {
        toFun := fun t => e (verticalPath ((t : ℝ) * dist x y))
        continuous_toFun := e.continuous.comp
          (verticalPath_isometry.continuous.comp (continuous_subtype_val.mul continuous_const))
        source' := by
          change e (verticalPath (0 * dist x y)) = x
          simpa only [zero_mul,zero_eq_I] using he0
        target' := by
          change e (verticalPath (1 * dist x y)) = y
          simpa only [one_mul] using he1 }
      refine ⟨γ,?_⟩
      intro s t
      change dist (e (verticalPath ((s : ℝ)*dist x y)))
        (e (verticalPath ((t : ℝ)*dist x y))) = _
      rw [e.isometry.dist_eq,verticalPath_isometry.dist_eq,Real.dist_eq,Real.dist_eq,
        ←sub_mul,abs_mul,abs_of_nonneg (dist_nonneg (x := x) (y := y)),mul_comm]
    have p_nonexpanding (x y : H2) :
        dist (p x) (p y) ≤ dist x y := by
      obtain ⟨γ,hγ⟩ := actual_segment x y
      choose U hU hxU hmetric using hmetric
      let V : unitInterval → Set unitInterval := fun t => γ ⁻¹' U (γ t)
      have hV (t : unitInterval) : IsOpen (V t) := (hU (γ t)).preimage γ.continuous
      have hcover : Set.univ ⊆ ⋃ t, V t := by
        intro t ht
        exact Set.mem_iUnion.mpr ⟨t,hxU (γ t)⟩
      obtain ⟨t,ht0,htmono,⟨N,hN⟩,hsub⟩ :=
        exists_monotone_Icc_subset_open_cover_unitInterval hV hcover
      have hstep (n : ℕ) :
          dist (p (γ (t n))) (p (γ (t (n+1)))) =
            dist x y * ((t (n+1) : ℝ) - (t n : ℝ)) := by
        obtain ⟨j,hj⟩ := hsub n
        have hle : t n ≤ t (n+1) := htmono (Nat.le_succ n)
        have hleft := hj (show t n ∈ Set.Icc (t n) (t (n+1)) from ⟨le_rfl,hle⟩)
        have hright := hj (show t (n+1) ∈ Set.Icc (t n) (t (n+1)) from ⟨hle,le_rfl⟩)
        rw [hmetric (γ j) _ hleft _ hright,hγ,Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr (show (t n : ℝ) ≤ (t (n+1) : ℝ) from hle))]
        simp only [neg_sub]
      have hbound (n : ℕ) :
          dist (p (γ (t 0))) (p (γ (t n))) ≤
            dist x y * ((t n : ℝ) - (t 0 : ℝ)) := by
        induction n with
        | zero => simp
        | succ n ih =>
          have htri := dist_triangle (p (γ (t 0)))
            (p (γ (t n))) (p (γ (t (n+1))))
          have hsn := hstep n
          nlinarith
      have h := hbound N
      rw [ht0,hN N le_rfl] at h
      simpa using h
    obtain ⟨coverRadius,coverRadius_pos,coverRadius_control⟩ := uniform_evenly_covered_radius
    refine ⟨coverRadius,coverRadius_pos,?_⟩
    intro z
    by_contra hle
    have hshort : dist z (δ • z) < coverRadius := lt_of_not_ge hle
    obtain ⟨b,hb⟩ := coverRadius_control (p z)
    obtain ⟨γ,hγ⟩ := actual_segment z (δ • z)
    let Γ : C(unitInterval,H2) := ⟨γ,γ.continuous⟩
    let T := actualTrivialization b
    letI : DiscreteTopology (p ⁻¹' {b}) := (actualCoveringMap b).discreteTopology_fiber
    have hsource (t : unitInterval) : Γ t ∈ T.source := by
      apply T.mem_source.mpr
      apply hb
      change dist (p (γ t)) (p z) < coverRadius
      have hπ := p_nonexpanding (γ t) z
      have hseg : dist (γ t) z = dist z (δ • z) * (t : ℝ) := by
        have h := hγ 0 t
        simpa [Real.dist_eq,abs_of_nonneg t.property.1,dist_comm] using h
      have hbound := mul_le_of_le_one_right (dist_nonneg (x := z) (y := δ • z)) t.property.2
      rw [hseg] at hπ
      exact lt_of_le_of_lt (hπ.trans hbound) hshort
    let label : unitInterval → (p ⁻¹' {b}) := fun t => (T (Γ t)).2
    have hlabel : Continuous label := continuous_snd.comp
      (T.toOpenPartialHomeomorph.continuousOn.comp_continuous Γ.continuous hsource)
    have hlabels : label 0 = label 1 :=
      (isPreconnected_range hlabel).subsingleton (mem_range_self 0) (mem_range_self 1)
    have hprojection : p (Γ 0) = p (Γ 1) := by
      change p (γ 0) = p (γ 1)
      rw [γ.source,γ.target]
      exact (hq.map_smul δ).symm
    have hcoords : T (Γ 0) = T (Γ 1) := by
      apply Prod.ext
      · change (T.toOpenPartialHomeomorph (Γ 0)).1 = (T.toOpenPartialHomeomorph (Γ 1)).1
        rw [T.proj_toFun _ (hsource 0),T.proj_toFun _ (hsource 1)]
        exact hprojection
      · exact hlabels
    have hend : Γ 0 = Γ 1 := T.injOn (hsource 0) (hsource 1) hcoords
    have hfixed : δ • z = z := by
      change γ 0 = γ 1 at hend
      simpa only [γ.source,γ.target] using hend.symm
    letI := hq.isCancelSMul
    apply hδ
    exact IsCancelSMul.right_cancel δ 1 z (by simpa using hfixed)

end CurveComplex.Hyperbolic
