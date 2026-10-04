import Mathlib
open Set Topology
open scoped Pointwise
set_option maxHeartbeats 8000000
set_option maxRecDepth 6000
theorem actual_free_homotopy_integer_meridian_supplied_root_same_component {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
    (a : MulAction G P) (p : P → E) (hq : letI := a;IsQuotientCoveringMap p G)
    (f m : C(Circle,E)) (n : ℤ) (H : C(Circle×unitInterval,E))
    (hH0 : ∀z,H (z,0)=f z) (hH1 : ∀z,H (z,1)=m (z^n))
    (W : Set E) (hinside : ∀z : Circle,∀s : unitInterval,H (z,s)∈W)
    (x : P) (hx : p x=f 1) :
    ∃δ η : G,∃y : P,∃hy : p y=m 1,y∈connectedComponentIn (p ⁻¹' W) x ∧ η^n=δ ∧
      (∀β : Path (f 1) (f 1),
        (∀t : unitInterval,β t=f (Circle.exp (2*Real.pi*(t:ℝ)))) →
        @SMul.smul G P a.toSMul δ x=(hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val) ∧
      (∀β : Path (m 1) (m 1),
        (∀t : unitInterval,β t=m (Circle.exp (2*Real.pi*(t:ℝ)))) →
        @SMul.smul G P a.toSMul η y=(hq.isCoveringMap.monodromy ⟦β⟧ ⟨y,hy⟩).val) := by
  have hClock {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
      (a : MulAction G P) (p : P → E)
      (hq : letI := a;IsQuotientCoveringMap p G)
      (f g : C(Circle,E)) (H : C(Circle×unitInterval,E))
      (hH0 : ∀ z : Circle,H (z,0)=f z) (hH1 : ∀ z : Circle,H (z,1)=g z)
      (x : P) (hx : p x=f 1) :
      ∃ L : C(unitInterval×ℝ,P),∃ δ : G,
        L (0,0)=x ∧
        (∀s : unitInterval,∀t : ℝ,p (L (s,t))=H (Circle.exp (2*Real.pi*t),s)) ∧
        (∀ t : ℝ,p (L (0,t))=f (Circle.exp (2*Real.pi*t))) ∧
        (∀ t : ℝ,p (L (1,t))=g (Circle.exp (2*Real.pi*t))) ∧
        (∀ s : unitInterval,∀ t : ℝ,
          @SMul.smul G P a.toSMul δ (L (s,t))=L (s,t+1)) ∧
        ∀ β : Path (f 1) (f 1),
          (∀ t : unitInterval,β t=f (Circle.exp (2*Real.pi*(t:ℝ)))) →
          @SMul.smul G P a.toSMul δ x=
            (hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val := by
    have hPeriodic {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
        (a : MulAction G P) (p : P → E)
        (hq : letI := a; IsQuotientCoveringMap p G)
        (α : ℝ → P) (hα : Continuous α) (T : ℝ)
        (hperiod : ∀ t : ℝ,p (α (t+T))=p (α t)) :
        ∃ δ : G,
          (∀ t : ℝ,@SMul.smul G P a.toSMul δ (α t)=α (t+T)) ∧
          (letI := a;δ∈MulAction.stabilizer G (range α)) ∧
          ∀ β : Path (p (α 0)) (p (α 0)),
            (∀ t : unitInterval,β t=p (α ((t:ℝ)*T))) →
            @SMul.smul G P a.toSMul δ (α 0)=
              (hq.isCoveringMap.monodromy ⟦β⟧ ⟨α 0,rfl⟩).val := by
      letI := a
      have hend : p (α T)=p (α 0) := by simpa using hperiod 0
      obtain ⟨δ,hδ⟩ := hq.apply_eq_iff_mem_orbit.mp hend
      have hshift : ∀ t : ℝ,δ • α t=α (t+T) := by
        have heq : (fun t : ℝ => δ • α t)=(fun t : ℝ => α (t+T)) :=
          hq.isCoveringMap.eq_of_comp_eq
            ((hq.continuous_const_smul δ).comp hα)
            (hα.comp (continuous_id.add continuous_const))
            (by funext t;exact (hq.map_smul δ).trans (hperiod t).symm)
            0 (by simpa using hδ)
        exact congrFun heq
      refine ⟨δ,hshift,?_,?_⟩
      · apply MulAction.mem_stabilizer_iff.mpr
        change (fun z : P => δ • z) '' range α=range α
        apply Subset.antisymm
        · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
          exact ⟨t+T,(hshift t).symm⟩
        · rintro _ ⟨t,rfl⟩
          refine ⟨α (t-T),mem_range_self _,?_⟩
          change δ • α (t-T)=α t
          rw [hshift,sub_add_cancel]
      · intro β hβ
        have heq : (fun t : unitInterval => α ((t:ℝ)*T))=
            hq.isCoveringMap.liftPath β (α 0) β.source := by
          apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
          refine ⟨hα.comp (continuous_subtype_val.mul continuous_const),?_,?_⟩
          · funext t;exact (hβ t).symm
          · simp
        change δ • α 0=hq.isCoveringMap.liftPath β (α 0) β.source 1
        rw [←heq,hshift]
        simp
    have hHomotopy {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
        (a : MulAction G P) (p : P → E)
        (hq : letI := a;IsQuotientCoveringMap p G)
        (F : C(unitInterval×ℝ,E)) (T : ℝ)
        (hperiod : ∀ s : unitInterval,∀ t : ℝ,F (s,t+T)=F (s,t))
        (α : C(ℝ,P)) (hzero : ∀ t : ℝ,F (0,t)=p (α t))
        (δ : G)
        (hδ : ∀ t : ℝ,@SMul.smul G P a.toSMul δ (α t)=α (t+T)) :
        ∃ L : C(unitInterval×ℝ,P),
          (∀ s t,p (L (s,t))=F (s,t)) ∧
          (∀ t,L (0,t)=α t) ∧
          (∀ s t,@SMul.smul G P a.toSMul δ (L (s,t))=L (s,t+T)) := by
      letI := a
      let L := hq.isCoveringMap.liftHomotopy F α hzero
      have hlift (s : unitInterval) (t : ℝ) : p (L (s,t))=F (s,t) :=
        congrFun (hq.isCoveringMap.liftHomotopy_lifts F α hzero) (s,t)
      have hstart (t : ℝ) : L (0,t)=α t :=
        hq.isCoveringMap.liftHomotopy_zero F α hzero t
      refine ⟨L,hlift,hstart,?_⟩
      have he : (fun x : unitInterval×ℝ => δ • L x)=
          (fun x : unitInterval×ℝ => L (x.1,x.2+T)) := by
        exact hq.isCoveringMap.eq_of_comp_eq
          ((hq.continuous_const_smul δ).comp L.continuous)
          (L.continuous.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)))
          (by
            funext x
            exact (hq.map_smul δ).trans ((hlift x.1 x.2).trans
              ((hperiod x.1 x.2).symm.trans (hlift x.1 (x.2+T)).symm)))
          (0,0) (by
            change δ • L (0,0)=L (0,0+T)
            rw [hstart,hstart]
            exact hδ 0)
      intro s t
      exact congrFun he (s,t)
    letI := a
    let γ : C(ℝ,E) := ⟨fun t => f (Circle.exp (2*Real.pi*t)),by fun_prop⟩
    have hγ0 : γ 0=p x := by simp [γ,hx]
    obtain ⟨α,⟨hα0,hαproj⟩,_⟩ := hq.isCoveringMap.existsUnique_continuousMap_lifts γ 0 x hγ0.symm
    have hproj (t : ℝ) : p (α t)=f (Circle.exp (2*Real.pi*t)) := congrFun hαproj t
    have hclock (t : ℝ) : Circle.exp (2*Real.pi*(t+1))=Circle.exp (2*Real.pi*t) := by
      rw [mul_add,mul_one,Circle.exp_add_two_pi]
    have hper : ∀t : ℝ,p (α (t+1))=p (α t) := by intro t;rw [hproj,hproj,hclock]
    obtain ⟨δ,hδ,hstab,hmono⟩ := hPeriodic a p hq α α.continuous 1 hper
    let F : C(unitInterval×ℝ,E) := ⟨fun st => H (Circle.exp (2*Real.pi*st.2),st.1),by fun_prop⟩
    have hFper : ∀s : unitInterval,∀t : ℝ,F (s,t+1)=F (s,t) := by
      intro s t
      change H (Circle.exp (2*Real.pi*(t+1)),s)=H (Circle.exp (2*Real.pi*t),s)
      rw [hclock]
    have hF0 : ∀t : ℝ,F (0,t)=p (α t) := by
      intro t
      exact (hH0 _).trans (hproj t).symm
    obtain ⟨L,hLp,hL0,hLeq⟩ := hHomotopy a p hq F 1 hFper α hF0 δ hδ
    refine ⟨L,δ,(hL0 0).trans hα0,hLp,?_,?_,hLeq,?_⟩
    · intro t;rw [hLp];exact hH0 _
    · intro t;rw [hLp];exact hH1 _
    · intro β hβ
      have heq : (fun t : unitInterval => α (t:ℝ))=
          hq.isCoveringMap.liftPath β x (β.source.trans hx.symm) := by
        apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
        refine ⟨α.continuous.comp continuous_subtype_val,?_,?_⟩
        · funext t;exact (hproj (t:ℝ)).trans (hβ t).symm
        · exact hα0
      change δ • x=hq.isCoveringMap.liftPath β x (β.source.trans hx.symm) 1
      rw [←heq,←hα0]
      change @SMul.smul G P a.toSMul δ (α 0)=α 1
      simpa using hδ 0
  have hInteger {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
      (a : MulAction G P) (p : P → E) (hq : letI := a;IsQuotientCoveringMap p G)
      (f : C(Circle,E)) (x : P) (hx : p x=f 1) :
      ∃η : G,∀n : ℤ,∀β : Path (f 1) (f 1),
        (∀t : unitInterval,β t=f (Circle.exp (2*Real.pi*(n:ℝ)*(t:ℝ)))) →
        @SMul.smul G P a.toSMul (η^n) x=
          (hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val := by
    have hPeriod {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
        (a : MulAction G P) (p : P → E)
        (hq : letI := a; IsQuotientCoveringMap p G)
        (α : ℝ → P) (hα : Continuous α) (T : ℝ)
        (hperiod : ∀ t : ℝ,p (α (t+T))=p (α t)) :
        ∃ δ : G,
          (∀ t : ℝ,@SMul.smul G P a.toSMul δ (α t)=α (t+T)) ∧
          (letI := a;δ∈MulAction.stabilizer G (range α)) ∧
          ∀ β : Path (p (α 0)) (p (α 0)),
            (∀ t : unitInterval,β t=p (α ((t:ℝ)*T))) →
            @SMul.smul G P a.toSMul δ (α 0)=
              (hq.isCoveringMap.monodromy ⟦β⟧ ⟨α 0,rfl⟩).val := by
      letI := a
      have hend : p (α T)=p (α 0) := by simpa using hperiod 0
      obtain ⟨δ,hδ⟩ := hq.apply_eq_iff_mem_orbit.mp hend
      have hshift : ∀ t : ℝ,δ • α t=α (t+T) := by
        have heq : (fun t : ℝ => δ • α t)=(fun t : ℝ => α (t+T)) :=
          hq.isCoveringMap.eq_of_comp_eq
            ((hq.continuous_const_smul δ).comp hα)
            (hα.comp (continuous_id.add continuous_const))
            (by funext t;exact (hq.map_smul δ).trans (hperiod t).symm)
            0 (by simpa using hδ)
        exact congrFun heq
      refine ⟨δ,hshift,?_,?_⟩
      · apply MulAction.mem_stabilizer_iff.mpr
        change (fun z : P => δ • z) '' range α=range α
        apply Subset.antisymm
        · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
          exact ⟨t+T,(hshift t).symm⟩
        · rintro _ ⟨t,rfl⟩
          refine ⟨α (t-T),mem_range_self _,?_⟩
          change δ • α (t-T)=α t
          rw [hshift,sub_add_cancel]
      · intro β hβ
        have heq : (fun t : unitInterval => α ((t:ℝ)*T))=
            hq.isCoveringMap.liftPath β (α 0) β.source := by
          apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
          refine ⟨hα.comp (continuous_subtype_val.mul continuous_const),?_,?_⟩
          · funext t;exact (hβ t).symm
          · simp
        change δ • α 0=hq.isCoveringMap.liftPath β (α 0) β.source 1
        rw [←heq,hshift]
        simp
    have hPowers {G P : Type} [Group G] (a : MulAction G P) (δ : G)
        (α : ℝ → P) (T : ℝ)
        (hδ : ∀t : ℝ,@SMul.smul G P a.toSMul δ (α t)=α (t+T)) :
        ∀n : ℤ,∀t : ℝ,@SMul.smul G P a.toSMul (δ^n) (α t)=α (t+(n:ℝ)*T) := by
      letI := a
      have hδ' (t : ℝ) : δ • α t=α (t+T) := hδ t
      have hinv (t : ℝ) : δ⁻¹ • α t=α (t-T) := by
        have h := congrArg (fun z => δ⁻¹ • z) (hδ' (t-T))
        simpa only [inv_smul_smul,sub_add_cancel] using h.symm
      have hpow (n : ℤ) : ∀t : ℝ,δ^n • α t=α (t+(n:ℝ)*T) := by
        refine Int.induction_on n ?_ ?_ ?_
        · intro t;simp
        · intro m ih t
          rw [zpow_add,zpow_one,mul_smul,hδ',ih]
          congr 1
          push_cast
          ring
        · intro m ih t
          rw [zpow_sub,zpow_one,mul_smul,hinv,ih]
          congr 1
          push_cast
          ring
      exact hpow
    let clock : C(ℝ,E) :=
      ⟨fun t => f (Circle.exp (2*Real.pi*t)),by fun_prop⟩
    have hxclock : p x=clock 0 := by simpa [clock] using hx
    obtain ⟨α,hα,_⟩ := hq.isCoveringMap.existsUnique_continuousMap_lifts clock 0 x hxclock
    have hproj (t : ℝ) : p (α t)=f (Circle.exp (2*Real.pi*t)) := congrFun hα.2 t
    have hperiod : ∀t : ℝ,p (α (t+1))=p (α t) := by
      intro t;rw [hproj,hproj]
      congr 1
      have he : 2*Real.pi*(t+1)=2*Real.pi*t+2*Real.pi := by ring
      rw [he,Circle.exp_add_two_pi]
    obtain ⟨η,hη,hstab,hmono⟩ := hPeriod a p hq α α.continuous 1 hperiod
    refine ⟨η,?_⟩
    intro n β hβ
    have hlift : (fun t : unitInterval => α ((n:ℝ)*(t:ℝ)))=
        hq.isCoveringMap.liftPath β x (β.source.trans hx.symm) := by
      apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
      refine ⟨α.continuous.comp (continuous_const.mul continuous_subtype_val),?_,?_⟩
      · funext t
        change p (α ((n:ℝ)*(t:ℝ)))=β t
        rw [hproj,hβ]
        congr 2;ring
      · simpa using hα.1
    change @SMul.smul G P a.toSMul (η^n) x=
      hq.isCoveringMap.liftPath β x (β.source.trans hx.symm) 1
    rw [←hlift,←hα.1]
    simpa using hPowers a η α 1 hη n 0
  let g : C(Circle,E) := ⟨fun z => m (z^n),by fun_prop⟩
  obtain ⟨L,δ,hL0,hLproj,hLinitial,hLterminal,hδ,hδmono⟩ :=
    hClock a p hq f g H hH0 hH1 x hx
  let y := L (1,0)
  have hy : p y=m 1 := by simpa [y,g] using hLterminal 0
  have hconn : IsPreconnected (range (fun s : unitInterval => L (s,0))) :=
    isPreconnected_range (L.continuous.comp (continuous_id.prodMk continuous_const))
  have hxrange : x∈range (fun s : unitInterval => L (s,0)) := ⟨0,hL0⟩
  have hsub : range (fun s : unitInterval => L (s,0))⊆p ⁻¹' W := by
    rintro _ ⟨s,rfl⟩
    change p (L (s,0))∈W
    rw [hLproj]
    exact hinside _ s
  have hyC : y∈connectedComponentIn (p ⁻¹' W) x :=
    hconn.subset_connectedComponentIn hxrange hsub (mem_range_self 1)
  obtain ⟨η,hη⟩ := hInteger a p hq m y hy
  let β : Path (m 1) (m 1) :=
    { toFun := fun t => m (Circle.exp (2*Real.pi*(n:ℝ)*(t:ℝ)))
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp [mul_comm (2*Real.pi) (n:ℝ),Circle.exp_int_mul_two_pi] }
  have hβlift : (fun t : unitInterval => L (1,(t:ℝ)))=
      hq.isCoveringMap.liftPath β y (β.source.trans hy.symm) := by
    apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
    refine ⟨L.continuous.comp (continuous_const.prodMk continuous_subtype_val),?_,rfl⟩
    funext t
    change p (L (1,(t:ℝ)))=m (Circle.exp (2*Real.pi*(n:ℝ)*(t:ℝ)))
    rw [hLterminal]
    change m ((Circle.exp (2*Real.pi*(t:ℝ)))^n)=_
    rw [←Circle.exp_zsmul]
    congr 2
    simp only [zsmul_eq_mul]
    ring
  have hηn := hη n β (fun t => rfl)
  change @SMul.smul G P a.toSMul (η^n) y=
    hq.isCoveringMap.liftPath β y (β.source.trans hy.symm) 1 at hηn
  rw [←hβlift] at hηn
  have hroot : η^n=δ := by
    letI := a
    letI := hq.isCancelSMul
    apply IsCancelSMul.right_cancel' (η^n) δ y
    change @SMul.smul G P a.toSMul (η^n) y = @SMul.smul G P a.toSMul δ y
    exact hηn.trans (by simpa [y] using (hδ 1 0).symm)
  refine ⟨δ,η,y,hy,hyC,hroot,hδmono,?_⟩
  intro γ hγ
  simpa only [zpow_one,Int.cast_one,mul_one] using hη 1 γ (by simpa only [Int.cast_one,mul_one] using hγ)
