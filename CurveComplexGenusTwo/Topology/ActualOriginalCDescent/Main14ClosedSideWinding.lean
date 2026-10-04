import CurveComplexGenusTwo.Topology.PositionExtension.CleanSideProjectionStatement

namespace CurveComplex.LocalSurgery

/-- An embedded lifted interval whose projected endpoints agree must traverse
the whole original circle. The angular lift is injective by uniqueness of
covering lifts, hence has a nonzero winding. -/
theorem embedded_lifted_interval_closed_projection_covers_circle
    {E S : Type} [TopologicalSpace E] [T2Space E] [TopologicalSpace S] [T2Space S]
    (p : E → S) (cov : IsCoveringMap p) (a : Curve S)
    (α : C(Interval,E)) (hα : Topology.IsEmbedding α)
    (hαa : Set.range α ⊆ p ⁻¹' a.image)
    (hclosed : p (α 0) = p (α 1)) :
    Set.range (p ∘ α) = a.image := by
  classical
  let f : C(Interval,S) := (⟨p,cov.continuous⟩ : C(E,S)).comp α
  have hfa : Set.range f ⊆ a.image := by
    rintro x ⟨t,rfl⟩
    exact hαa ⟨t,rfl⟩
  let q := subarcCircleCoordinates a f hfa
  let θ := subarcAngleCoordinates a f hfa
  have hq (t : Interval) : a.map (q t) = f t :=
    congrArg Subtype.val (a.embedded.toHomeomorph.apply_symm_apply ⟨f t,hfa ⟨t,rfl⟩⟩)
  have hθ : Circle.exp ∘ θ = q := Circle.isCoveringMap_exp.liftPath_lifts q
    (q 0).val.arg (Circle.exp_arg _).symm
  have hθp (t : Interval) : Circle.exp (θ t) = q t := congrFun hθ t
  let A : C(ℝ,S) := ⟨fun x => a.map (Circle.exp x), a.embedded.continuous.comp Circle.exp.continuous⟩
  have hbase : p (α 0) = A (θ 0) := by
    change f 0 = a.map (Circle.exp (θ 0))
    rw [hθp 0,hq]
  obtain ⟨L,⟨hL0,hL⟩,_⟩ := cov.existsUnique_continuousMap_lifts A (θ 0) (α 0) hbase
  have hident : (L.comp θ : Interval → E) = α := by
    apply cov.eq_of_comp_eq (L.comp θ).continuous α.continuous
    · funext t
      change p (L (θ t)) = p (α t)
      rw [show p (L (θ t)) = A (θ t) from congrFun hL (θ t)]
      change a.map (Circle.exp (θ t)) = f t
      rw [hθp t,hq]
    · exact hL0
  have hinj : Function.Injective θ := by
    intro t u he
    apply hα.injective
    rw [← congrFun hident t,← congrFun hident u]
    exact congrArg L he
  have hend : Circle.exp (θ 0) = Circle.exp (θ 1) := by
    apply a.embedded.injective
    rw [hθp 0,hθp 1,hq,hq]
    exact hclosed
  obtain ⟨m,hm⟩ := Circle.exp_eq_exp.mp hend
  have hmne : m ≠ 0 := by
    intro he
    rw [he,Int.cast_zero,zero_mul,add_zero] at hm
    have he' := hinj hm
    norm_num at he'
  have hspan : min (θ 0) (θ 1) + 2 * Real.pi ≤ max (θ 0) (θ 1) := by
    have hmchoice : m ≤ -1 ∨ 1 ≤ m := by omega
    rcases hmchoice with hmle | hmle
    · have hmreal : (m : ℝ) ≤ -1 := by exact_mod_cast hmle
      have hmul : (m : ℝ) * (2 * Real.pi) ≤ -(2 * Real.pi) := by
        nlinarith [Real.pi_pos]
      have h01 : θ 0 ≤ θ 1 := by linarith [Real.pi_pos]
      rw [min_eq_left h01,max_eq_right h01]
      linarith
    · have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hmle
      have hmul : 2 * Real.pi ≤ (m : ℝ) * (2 * Real.pi) := by
        nlinarith [Real.pi_pos]
      have h10 : θ 1 ≤ θ 0 := by linarith [Real.pi_pos]
      rw [min_eq_right h10,max_eq_left h10]
      linarith
  apply Set.Subset.antisymm hfa
  rintro z ⟨u,rfl⟩
  have hu : u ∈ Circle.exp '' Set.Icc (min (θ 0) (θ 1))
      (min (θ 0) (θ 1) + 2 * Real.pi) := by
    rw [Circle.periodic_exp.image_Icc (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact Set.mem_range.mpr (Circle.exp_surjective u)
  obtain ⟨v,hv,hvu⟩ := hu
  have hvend : v ∈ Set.uIcc (θ 0) (θ 1) := ⟨hv.1,hv.2.trans hspan⟩
  obtain ⟨t,_,ht⟩ := intermediate_value_uIcc θ.continuous.continuousOn hvend
  refine ⟨t,?_⟩
  change f t = a.map u
  rw [← hq t,← hθp t,ht,hvu]

end CurveComplex.LocalSurgery
