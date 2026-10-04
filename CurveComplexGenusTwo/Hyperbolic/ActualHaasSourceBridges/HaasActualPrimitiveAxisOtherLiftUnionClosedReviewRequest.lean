import Mathlib
open Set Topology
theorem actual_primitive_axis_other_lift_union_is_closed {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
    (p : P → E) (hp : IsCoveringMap p) (α : ℝ → P) (hα : Isometry α)
    (T : ℝ) (hT : 0<T)
    (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T) :
    IsClosed (p ⁻¹' (p '' range α) \ range α) := by
  have hDescent {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
      (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
      (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
      ∃f : C(Circle,E),IsEmbedding f ∧
        (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
        range f=p '' range α := by
    classical
    let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
    have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
    let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
    have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
      obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
      apply (hfibre _ _).mpr
      refine ⟨k,?_⟩
      rw [hk]
      field_simp
    have hψ : Continuous ψ := by
      apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
      have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
      rw [heq]
      fun_prop
    let f : C(Circle,E) := ⟨ψ,hψ⟩
    have hfinj : Function.Injective f := by
      intro z w hzw
      obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
      have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
        have hπ : (2*Real.pi)≠0 := by positivity
        have hT' : T≠0 := hT.ne'
        field_simp at hk
        nlinarith
      rw [←hθ z,←hθ w]
      exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
    have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
      change _=ψ _
      rw [hfac]
      congr 2
      field_simp
    refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
    apply Subset.antisymm
    · rintro y ⟨z,rfl⟩
      exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
    · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
      exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
  obtain ⟨f,hf,hparam,hrange⟩ := hDescent ⟨p,hp.continuous⟩ ⟨α,hα.continuous⟩ T hT hfibre
  change ∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T)) at hparam
  change range f=p '' range α at hrange
  let S := p ⁻¹' range f
  let e : Circle ≃ₜ range f := hf.toHomeomorph
  let pS : S → range f := (range f).restrictPreimage p
  have hpS : IsCoveringMap pS := hp.restrictPreimage (range f)
  let q : S → Circle := e.symm ∘ pS
  have hq : IsCoveringMap q := hpS.homeomorph_comp e.symm
  let αS : ℝ → S := fun t => ⟨α t,by
    change p (α t)∈range f
    rw [hrange]
    exact ⟨α t,mem_range_self t,rfl⟩⟩
  have hαS : Continuous αS := hα.continuous.subtype_mk _
  have hqα (t : ℝ) : q (αS t)=Circle.exp (2*Real.pi*t/T) := by
    apply e.injective
    dsimp only [q,Function.comp_apply]
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change p (α t)=f (Circle.exp (2*Real.pi*t/T))
    exact hparam t
  let c : ℝ := 2*Real.pi/T
  have hc : c≠0 := by dsimp [c];positivity
  let scale : ℝ ≃ₜ ℝ := Homeomorph.mulRight₀ c hc
  have hclock : IsCoveringMap (fun t : ℝ => Circle.exp (2*Real.pi*t/T)) := by
    have hh := Circle.isAddQuotientCoveringMap_exp.isCoveringMap.comp_homeomorph scale
    convert hh using 1
    funext t
    congr 1
    change 2*Real.pi*t/T=t*c
    dsimp [c];ring
  have hcomp : IsLocalHomeomorph (q ∘ αS) := by
    have heq : q ∘ αS=(fun t : ℝ => Circle.exp (2*Real.pi*t/T)) := funext hqα
    rw [heq];exact hclock.isLocalHomeomorph
  have hopen : IsOpen (range αS) :=
    (hcomp.of_comp hq.isLocalHomeomorph hαS).isOpenMap.isOpen_range
  have hSclosed : IsClosed S := (isCompact_range f.continuous).isClosed.preimage hp.continuous
  have hresclosed : IsClosed ((Subtype.val : S → P) '' (range αS)ᶜ) :=
    hSclosed.isClosedMap_subtype_val _ hopen.isClosed_compl
  convert hresclosed using 1
  rw [←hrange]
  ext z
  constructor
  · rintro ⟨hz,hnot⟩
    refine ⟨⟨z,hz⟩,?_,rfl⟩
    rintro ⟨t,ht⟩
    exact hnot ⟨t,congrArg Subtype.val ht⟩
  · rintro ⟨z,hz,rfl⟩
    refine ⟨z.property,?_⟩
    rintro ⟨t,ht⟩
    apply hz
    refine ⟨t,?_⟩
    exact Subtype.ext ht
