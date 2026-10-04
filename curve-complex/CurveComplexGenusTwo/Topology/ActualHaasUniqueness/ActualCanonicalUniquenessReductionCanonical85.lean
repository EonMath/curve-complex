import CurveComplexGenusTwo.Topology.ActualNoSimplePole.NoGenusTwoSimplePole
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.CanonicalDegreeTwoFiberRigidity
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.IsolatedInvolutionStrictDerivativeNegative
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
open scoped Manifold ContDiff Bundle
open Bundle
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]

private theorem evaluation_zero (x : E) (s : ActualCanonicalSection E) :
    actualCanonicalEvaluation x s = 0 ↔ s x = 0 := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    change s x v = 0
    let c := tangentSpaceCastModel 𝓘(ℂ) x
    have hv : v = (c v) • (c.symm (1 : ℂ)) := by
      apply c.injective
      rw [c.map_smul, c.apply_symm_apply]
      simp
    rw [hv, map_smul]
    have hs : s x (c.symm 1) = 0 := h
    simp [hs]
  · intro h
    simp [actualCanonicalEvaluation, h]

private theorem evaluation_smooth (s : ActualCanonicalSection E) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) 𝓘(ℂ) ∞
      (fun v : TangentBundle 𝓘(ℂ) E => s v.proj v.2) := by
  have hs : ContMDiff (𝓘(ℂ).prod 𝓘(ℂ))
      (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ∞
      (fun v : TangentBundle 𝓘(ℂ) E =>
        TotalSpace.mk' (ℂ →L[ℂ] ℂ)
          (E := fun x : E => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial E ℂ x) v.proj (s v.proj)) :=
    s.contMDiff.comp (contMDiff_proj (F := ℂ) (IB := 𝓘(ℂ)) (n := ∞) (fun x : E => TangentSpace 𝓘(ℂ) x))
  have hv : ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ∞
      (fun v : TangentBundle 𝓘(ℂ) E => TotalSpace.mk' ℂ (E := fun x : E => TangentSpace 𝓘(ℂ) x) v.proj v.2) := contMDiff_id
  have happ := hs.clm_bundle_apply hv
  intro v
  have hcoord := (contMDiffAt_totalSpace.mp (happ v)).2
  simpa [Bundle.Trivial.fiberBundle_trivializationAt'] using hcoord

private theorem section_of_smooth_evaluation (α : ∀ x : E, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial E ℂ x)
    (hα : ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) 𝓘(ℂ) ∞
      (fun v : TangentBundle 𝓘(ℂ) E => α v.proj v.2)) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ∞
      (fun x => TotalSpace.mk' (ℂ →L[ℂ] ℂ) x (α x)) := by
  intro x₀
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℂ) x) x₀
  let v : E → TangentBundle 𝓘(ℂ) E := fun x => e.toOpenPartialHomeomorph.symm (x, 1)
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  have hv : ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞ v x₀ :=
    ((e.contMDiffOn_symm).contMDiffAt (e.open_target.mem_nhds (e.mem_target.mpr hx₀))).comp
      x₀ (contMDiffAt_id.prodMk contMDiffAt_const)
  have hscalar : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (fun x => α (v x).proj (v x).2) x₀ :=
    (hα (v x₀)).comp x₀ hv
  let L : E → ℂ →L[ℂ] ℂ := fun x => ContinuousLinearMap.inCoordinates
    ℂ (fun x : E => TangentSpace 𝓘(ℂ) x) ℂ (Bundle.Trivial E ℂ)
    x₀ x x₀ x (α x)
  have hcoeff : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (fun x => L x 1) x₀ := by
    apply hscalar.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx
    simp only [L, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_apply, e.symmL_apply hx]
    change α x (e.symmL ℂ x 1) = α (v x).proj (v x).2
    rw [e.symmL_apply hx]
    dsimp [v]
    rw [← e.mk_symm hx 1]
  have hfamily : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞
      (fun x => (L x 1) • ContinuousLinearMap.id ℂ ℂ) x₀ :=
    hcoeff.smul contMDiffAt_const
  apply hfamily.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro x
  apply ContinuousLinearMap.ext
  intro z
  change L x z = (L x 1) * z
  have hz : z = z • (1 : ℂ) := by simp
  rw [hz, map_smul]
  simp [smul_eq_mul, mul_comm]

noncomputable def actualCanonicalPullback (f : E → E)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f) :
    ActualCanonicalSection E →ₗ[ℂ] ActualCanonicalSection E where
  toFun := fun s => {
    toFun := fun x => (s (f x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x)
    contMDiff_toFun := by
      apply section_of_smooth_evaluation
      have h := (evaluation_smooth s).comp (hf.contMDiff_tangentMap (m := ∞) (by simp))
      simpa [tangentMap, Function.comp_def, ContinuousLinearMap.comp_apply] using h }
  map_add' := by
    intro s t
    apply ContMDiffSection.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.comp_apply]
  map_smul' := by
    intro c s
    apply ContMDiffSection.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.comp_apply]

private theorem pullback_involution (f : E → E) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f)
    (hinv : Function.Involutive f) :
    Function.Involutive (actualCanonicalPullback f hf) := by
  intro s
  apply ContMDiffSection.ext
  intro x
  have hf1 : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 f := hf.of_le (by simp)
  have hcomp : (mfderiv 𝓘(ℂ) 𝓘(ℂ) f (f x)).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x) = ContinuousLinearMap.id ℂ ℂ := by
    rw [← mfderiv_comp x (hf1.mdifferentiableAt one_ne_zero) (hf1.mdifferentiableAt one_ne_zero)]
    have hfunc : f ∘ f = id := funext hinv
    rw [hfunc, mfderiv_id]
    rfl
  apply ContinuousLinearMap.ext
  intro v
  change s (f (f x)) ((mfderiv 𝓘(ℂ) 𝓘(ℂ) f (f x))
    ((mfderiv 𝓘(ℂ) 𝓘(ℂ) f x) v)) = s x v
  rw [hinv x]
  have hv := congrArg (fun L : ℂ →L[ℂ] ℂ => L v) hcomp
  exact congrArg (s x) hv

noncomputable def actualCanonicalJacobian (f : E → E) (x : E) : ℂ :=
  (tangentSpaceCastModel 𝓘(ℂ) (f x))
    ((mfderiv 𝓘(ℂ) 𝓘(ℂ) f x) ((tangentSpaceCastModel 𝓘(ℂ) x).symm 1))

private theorem evaluation_pullback (f : E → E) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f) (x : E)
    (s : ActualCanonicalSection E) :
    actualCanonicalEvaluation x (actualCanonicalPullback f hf s) =
      actualCanonicalJacobian f x * actualCanonicalEvaluation (f x) s := by
  let c := tangentSpaceCastModel 𝓘(ℂ) (f x)
  let v := (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x) ((tangentSpaceCastModel 𝓘(ℂ) x).symm 1)
  have hv : v = (c v) • (c.symm (1 : ℂ)) := by
    apply c.injective
    rw [c.map_smul, c.apply_symm_apply]
    simp
  change s (f x) v = (c v) * s (f x) (c.symm 1)
  conv_lhs => rw [hv, map_smul]
  rfl

private theorem jacobian_fixed_chart (f : E → E) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 f)
    (q : E) (hfix : f q = q) :
    actualCanonicalJacobian f q =
      deriv (fun w => (chartAt ℂ q) (f ((chartAt ℂ q).symm w))) ((chartAt ℂ q) q) := by
  have hdiff := hf.mdifferentiableAt (x := q) one_ne_zero
  rw [actualCanonicalJacobian, mfderiv, if_pos hdiff]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  simp only [writtenInExtChartAt, hfix, extChartAt, OpenPartialHomeomorph.extend,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def, id_eq,
    Set.range_id, fderivWithin_univ, deriv, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl]
  rfl


open Set Filter Topology

private theorem fixed_sign [T1Space E] (f : E ≃ₜ E) (hmap : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f)
    (hinv : Function.Involutive f) (hfinite : {x : E | f x = x}.Finite)
    (q : E) (hfix : f q = q) :
    ∀ s : ActualCanonicalSection E,
      actualCanonicalEvaluation q (actualCanonicalPullback f hmap s) =
        -actualCanonicalEvaluation q s := by
  let c := chartAt ℂ q
  have hq : q ∈ c.source := mem_chart_source ℂ q
  have hhol : ContDiffAt ℂ 1 (fun w => c (f (c.symm w))) (c q) := by
    have hf := (contMDiffAt_iff_of_mem_source
      (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (n := ∞)
      (x := q) (y := q) (mem_chart_source ℂ q)
      (hfix.symm ▸ mem_chart_source ℂ q)).mp (hmap q)
    have hc := hf.2
    simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ, Function.comp_def]
      using hc.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  let G : ℂ → ℂ := fun w => c (f (c.symm w))
  have hGfix : G (c q) = c q := by simp [G, c.left_inv hq, hfix]
  have ht : Tendsto c.symm (𝓝 (c q)) (𝓝 q) := by
    simpa only [c.left_inv hq] using
      (c.symm.continuousAt (c.map_source hq)).tendsto
  have hsource : ∀ᶠ w in 𝓝 (c q), c.symm w ∈ c.source :=
    ht.eventually (c.open_source.mem_nhds hq)
  have hfsource : ∀ᶠ w in 𝓝 (c q), f (c.symm w) ∈ c.source := by
    have hfq : Tendsto f (𝓝 q) (𝓝 q) := by
      simpa [hfix] using (f.continuous.continuousAt (x := q)).tendsto
    exact (hfq.comp ht).eventually (c.open_source.mem_nhds hq)
  have htarget : ∀ᶠ w in 𝓝 (c q), w ∈ c.target :=
    c.open_target.mem_nhds (c.map_source hq)
  have hGinv : ∀ᶠ w in 𝓝 (c q), G (G w) = w := by
    filter_upwards [hfsource, htarget] with w hw ht
    dsimp [G]
    rw [c.left_inv hw, hinv, c.right_inv ht]
  have hqnot : q ∉ ({x : E | f x = x} \ {q}) := by simp
  have haven : ∀ᶠ w in 𝓝 (c q),
      c.symm w ∉ ({x : E | f x = x} \ {q}) :=
    ht.eventually ((hfinite.diff (t := {q})).isClosed.isOpen_compl.mem_nhds hqnot)
  have hisolated : ∀ᶠ w in 𝓝[≠] (c q), G w ≠ w := by
    have hmem : ∀ᶠ w in 𝓝[≠] (c q), w ≠ c q := self_mem_nhdsWithin
    filter_upwards [hsource.filter_mono nhdsWithin_le_nhds,
      hfsource.filter_mono nhdsWithin_le_nhds,
      htarget.filter_mono nhdsWithin_le_nhds,
      haven.filter_mono nhdsWithin_le_nhds,hmem] with w hs hfs htg hav hn
    intro heq
    have hfx : f (c.symm w) = c.symm w :=
      c.injOn hfs hs (by change G w = c (c.symm w); rw [c.right_inv htg]; exact heq)
    have hxq : c.symm w = q := by
      by_contra hne
      exact hav ⟨hfx,hne⟩
    exact hn (by rw [← c.right_inv htg, hxq])
  have hd := hhol.hasStrictDerivAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hminus : deriv G (c q) = -1 :=
    isolated_involution_strict_derivative_negative G (c q) _ hGfix hGinv hisolated hd
  have hjac : actualCanonicalJacobian f q = -1 := by
    rw [jacobian_fixed_chart f (hmap.of_le (by simp)) q hfix]
    exact hminus
  intro s
  rw [evaluation_pullback f hmap q s, hjac]
  simp [hfix]

example [T1Space E] (f : E ≃ₜ E) (hmap : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f)
    (hinv : Function.Involutive f) (hfinite : {x : E | f x = x}.Finite) :
    Function.Involutive (actualCanonicalPullback f hmap) ∧
    (∀ x (s : ActualCanonicalSection E),
      (actualCanonicalPullback f hmap s) x = (s (f x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x)) ∧
    (∀ x (s : ActualCanonicalSection E),
      actualCanonicalEvaluation x (actualCanonicalPullback f hmap s) =
        actualCanonicalJacobian f x * actualCanonicalEvaluation (f x) s) ∧
    (∀ q, f q = q → ∀ s : ActualCanonicalSection E,
      actualCanonicalEvaluation q (actualCanonicalPullback f hmap s) =
        -actualCanonicalEvaluation q s) ∧
    (∀ x (s : ActualCanonicalSection E), actualCanonicalEvaluation x s = 0 ↔ s x = 0) := by
  refine ⟨pullback_involution f hmap hinv, ?_, evaluation_pullback f hmap,
    fun q hq => fixed_sign f hmap hinv hfinite q hq, evaluation_zero⟩
  intro x s
  rfl

private theorem six_fixed_negation {E V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (hT : Function.Involutive T)
    (eval : E → V →ₗ[ℂ] ℂ) (F : Finset E) (hF : F.card = 6)
    (hfixed_pullback : ∀ x ∈ F, ∀ v, eval x (T v) = -eval x v)
    (hzero_bound : ∀ v : V, v ≠ 0 → ∃ Z : Finset E,
      Z.card ≤ 2 ∧ ∀ x : E, eval x v = 0 → x ∈ Z) :
    T = -LinearMap.id := by
  classical
  ext v
  have hsum : T v + v = 0 := by
    by_contra hnonzero
    obtain ⟨Z, hZcard, hZ⟩ := hzero_bound (T v + v) hnonzero
    have hinvariant : T (T v + v) = T v + v := by
      rw [map_add, hT v, add_comm]
    have hsubset : F ⊆ Z := by
      intro x hx
      apply hZ
      have h := hfixed_pullback x hx (T v + v)
      rw [hinvariant] at h
      linear_combination (1/2 : ℂ) * h
    have hc := Finset.card_le_card hsubset
    omega
  simpa using (eq_neg_of_add_eq_zero_left hsum)

example [T1Space E] (f : E ≃ₜ E) (hmap : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f)
    (hinv : Function.Involutive f) (F : Finset E)
    (hF : (F : Set E) = {x : E | f x = x}) (hcard : F.card = 6)
    (hzeros : ∀ s : ActualCanonicalSection E, s ≠ 0 →
      ∃ Z : Finset E, Z.card ≤ 2 ∧ ∀ x : E, s x = 0 → x ∈ Z) :
    actualCanonicalPullback f hmap = -LinearMap.id := by
  classical
  have hfinite : {x : E | f x = x}.Finite := hF ▸ F.finite_toSet
  apply six_fixed_negation (actualCanonicalPullback f hmap)
    (pullback_involution f hmap hinv) actualCanonicalEvaluation F hcard
  · intro x hx
    have hfix : f x = x := by
      have hmem : x ∈ (F : Set E) := hx
      rw [hF] at hmem
      exact hmem
    exact fixed_sign f hmap hinv hfinite x hfix
  · intro s hs
    obtain ⟨Z, hcard, hZ⟩ := hzeros s hs
    refine ⟨Z, hcard, fun x hx => hZ x ?_⟩
    exact (evaluation_zero x s).mp hx

private theorem two_basis_kernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin 2) ℂ V) (L : V →ₗ[ℂ] ℂ) :
    ∃ v : V, v ≠ 0 ∧ L v = 0 := by
  classical
  by_cases h₀ : L (b 0) = 0
  · exact ⟨b 0, b.ne_zero 0, h₀⟩
  · let v := L (b 1) • b 0 - L (b 0) • b 1
    refine ⟨v, ?_, ?_⟩
    · intro hv
      have h := congrArg (fun z => b.repr z 1) hv
      simp [v, map_sub, map_smul] at h
      exact h₀ h
    · simp [v, map_sub, map_smul, mul_comm]

private theorem projective_fiber_bound {E V : Type*} [AddCommGroup V] [Module ℂ V]
    (eval : E → V →ₗ[ℂ] ℂ) (hbase : ∀ x, eval x ≠ 0)
    (hkernel : ∀ x, ∃ v : V, v ≠ 0 ∧ eval x v = 0)
    (hzeros : ∀ v : V, v ≠ 0 → ∃ Z : Finset E,
      Z.card ≤ 2 ∧ ∀ x : E, eval x v = 0 → x ∈ Z) :
    let κ : E → Projectivization ℂ (V →ₗ[ℂ] ℂ) :=
      fun x => Projectivization.mk ℂ (eval x) (hbase x)
    ∀ b, ∃ Z : Finset E, Z.card ≤ 2 ∧ ∀ x, κ x = b → x ∈ Z := by
  classical
  dsimp only
  intro b
  by_cases hb : ∃ x, Projectivization.mk ℂ (eval x) (hbase x) = b
  · obtain ⟨x, hx⟩ := hb
    obtain ⟨v, hv, hxv⟩ := hkernel x
    obtain ⟨Z, hZcard, hZ⟩ := hzeros v hv
    refine ⟨Z, hZcard, ?_⟩
    intro y hy
    apply hZ
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ (eval y) (eval x)
      (hbase y) (hbase x)).mp (hy.trans hx.symm)
    have heq := congrArg (fun L : V →ₗ[ℂ] ℂ => L v) ha
    simpa [hxv] using heq.symm
  · refine ⟨∅, by simp, ?_⟩
    intro x hx
    exact False.elim (hb ⟨x, hx⟩)

private theorem projective_pullback_invariance {E V : Type*} [AddCommGroup V] [Module ℂ V]
    (eval : E → V →ₗ[ℂ] ℂ) (hbase : ∀ x, eval x ≠ 0)
    (f : E → E) (T : V →ₗ[ℂ] V) (hT : T = -LinearMap.id)
    (d : E → ℂ)
    (hpullback : ∀ x v, eval x (T v) = d x * eval (f x) v) :
    let κ : E → Projectivization ℂ (V →ₗ[ℂ] ℂ) :=
      fun x => Projectivization.mk ℂ (eval x) (hbase x)
    ∀ x, κ (f x) = κ x := by
  intro κ x
  apply Eq.symm
  apply (Projectivization.mk_eq_mk_iff' ℂ (eval x) (eval (f x)) (hbase x) (hbase (f x))).mpr
  refine ⟨-d x, ?_⟩
  ext v
  have h := hpullback x v
  simp only [hT, LinearMap.neg_apply, LinearMap.id_apply, map_neg] at h
  simp only [LinearMap.smul_apply, smul_eq_mul]
  linear_combination h

theorem actual_canonical_section_two_involutions_uniqueness_reduction [T2Space E] [PerfectSpace E]
    (b : Module.Basis (Fin 2) ℂ (ActualCanonicalSection E))
    (hbase : ∀ x : E, actualCanonicalEvaluation x ≠ 0)
    (hzeros : ∀ s : ActualCanonicalSection E, s ≠ 0 →
      ∃ Z : Finset E, Z.card ≤ 2 ∧ ∀ x : E, s x = 0 → x ∈ Z)
    (f g : E ≃ₜ E)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f)
    (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ g)
    (hfinv : Function.Involutive f) (hginv : Function.Involutive g)
    (F G : Finset E)
    (hF : (F : Set E) = {x : E | f x = x}) (hFcard : F.card = 6)
    (hG : (G : Set E) = {x : E | g x = x}) (hGcard : G.card = 6) : f = g := by
  classical
  have hz : ∀ s : ActualCanonicalSection E, s ≠ 0 →
      ∃ Z : Finset E, Z.card ≤ 2 ∧ ∀ x : E, actualCanonicalEvaluation x s = 0 → x ∈ Z := by
    intro s hs
    obtain ⟨Z, hZcard, hZ⟩ := hzeros s hs
    exact ⟨Z, hZcard, fun x hx => hZ x ((evaluation_zero x s).mp hx)⟩
  have neg : ∀ (u : E ≃ₜ E) (hu : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ u),
      Function.Involutive u → ∀ (K : Finset E),
      (K : Set E) = {x : E | u x = x} → K.card = 6 →
      actualCanonicalPullback u hu = -LinearMap.id := by
    intro u hu hinv K hK hKcard
    apply six_fixed_negation (actualCanonicalPullback u hu)
      (pullback_involution u hu hinv) actualCanonicalEvaluation K hKcard
    · intro x hx
      have hfix : u x = x := by
        have hm : x ∈ (K : Set E) := hx
        rw [hK] at hm
        exact hm
      exact fixed_sign u hu hinv (hK ▸ K.finite_toSet) x hfix
    · exact hz
  let κ : E → Projectivization ℂ (ActualCanonicalSection E →ₗ[ℂ] ℂ) :=
    fun x => Projectivization.mk ℂ (actualCanonicalEvaluation x) (hbase x)
  have hkernel : ∀ x : E, ∃ s : ActualCanonicalSection E,
      s ≠ 0 ∧ actualCanonicalEvaluation x s = 0 :=
    fun x => two_basis_kernel b (actualCanonicalEvaluation x)
  have hbound : ∀ a, ∃ Z : Finset E, Z.card ≤ 2 ∧ ∀ x : E, κ x = a → x ∈ Z :=
    projective_fiber_bound actualCanonicalEvaluation hbase hkernel hz
  apply canonical_degree_two_fiber_rigidity κ f g
  · exact projective_pullback_invariance actualCanonicalEvaluation hbase f
      (actualCanonicalPullback f hf) (neg f hf hfinv F hF hFcard)
      (actualCanonicalJacobian f) (evaluation_pullback f hf)
  · exact projective_pullback_invariance actualCanonicalEvaluation hbase g
      (actualCanonicalPullback g hg) (neg g hg hginv G hG hGcard)
      (actualCanonicalJacobian g) (evaluation_pullback g hg)
  · exact hF ▸ F.finite_toSet
  · exact hG ▸ G.finite_toSet
  · intro a
    obtain ⟨Z, hZcard, hZ⟩ := hbound a
    exact Z.finite_toSet.subset (fun x hx => hZ x hx)
  · intro a
    obtain ⟨Z, hZcard, hZ⟩ := hbound a
    calc
      (κ ⁻¹' {a}).ncard ≤ (Z : Set E).ncard :=
        Set.ncard_le_ncard (fun x hx => hZ x hx) Z.finite_toSet
      _ = Z.card := by simp
      _ ≤ 2 := hZcard
