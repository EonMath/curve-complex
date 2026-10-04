import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalCountableUniversalCoverHeader
import CurveComplexGenusTwo.Dictionary.Genus

namespace CurveComplex.LocalSurgery
open Topology
open scoped Manifold ContDiff

/-- Concrete planar geometry: an integer return of the lift of an embedded
circle forces an actual embedded disk downstairs. The covering plane
identification is a geometric input; no injectivity premise is supplied. -/
theorem boundsDisc_of_integer_return_in_actual_planar_cover
    {S U G : Type} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace U] [Group G] [MulAction G U]
    (p : U → S) (hp : IsQuotientCoveringMap p G)
    (e : U ≃ₜ Schoenflies.Plane)
    (c : CurveComplex.Curve S) (β : C(ℝ, U))
    (hβ : ∀ t, p (β t) = c.map (Circle.exp t))
    (n : ℤ) (hn : n ≠ 0) (t : ℝ)
    (hreturn : β (t + (n : ℝ) * (2 * Real.pi)) = β t) :
    CurveComplex.BoundsDisc c := by
  classical
  letI : T2Space U := e.symm.t2Space
  let cov := hp.isCoveringMap
  have hperiod_of_return (m : ℤ) (v : ℝ)
      (hm : β (v + (m : ℝ) * (2 * Real.pi)) = β v) :
      Function.Periodic β ((m : ℝ) * (2 * Real.pi)) := by
    have hh : (fun w : ℝ => β (w + (m : ℝ) * (2 * Real.pi))) = β := by
      apply cov.eq_of_comp_eq (β.continuous.comp (by fun_prop)) β.continuous (a := v)
      · ext w
        change p (β (w + (m : ℝ) * (2 * Real.pi))) = p (β w)
        rw [hβ, hβ, Circle.periodic_exp.int_mul m]
      · exact hm
    exact congrFun hh
  have hnperiod := hperiod_of_return n t hreturn
  have hex : ∃ k : ℕ, 0 < k ∧
      Function.Periodic β ((k : ℝ) * (2 * Real.pi)) := by
    cases n with
    | ofNat j =>
      refine ⟨j, ?_, ?_⟩
      · have hj : j ≠ 0 := by intro hz; subst j; exact hn rfl
        omega
      · simpa using hnperiod
    | negSucc j =>
      refine ⟨j + 1, by omega, ?_⟩
      convert hnperiod.neg using 1 <;> push_cast <;> ring
  let k := Nat.find hex
  have hkpos : 0 < k := (Nat.find_spec hex).1
  have hkperiod : Function.Periodic β ((k : ℝ) * (2 * Real.pi)) :=
    (Nat.find_spec hex).2
  have hkmin (j : ℕ) (hj : 0 < j)
      (hjp : Function.Periodic β ((j : ℝ) * (2 * Real.pi))) : k ≤ j :=
    Nat.find_min' hex ⟨hj, hjp⟩
  have hperiod_abs (m : ℤ) (hm : Function.Periodic β ((m : ℝ) * (2 * Real.pi))) :
      Function.Periodic β ((m.natAbs : ℝ) * (2 * Real.pi)) := by
    cases m with
    | ofNat j => simpa using hm
    | negSucc j =>
      simp only [Int.natAbs_negSucc]
      convert hm.neg using 1 <;> push_cast <;> ring
  have hkinj : Set.InjOn β (Set.Ico 0 ((k : ℝ) * (2 * Real.pi))) := by
    intro v hv w hw hvw
    have hexp : Circle.exp v = Circle.exp w :=
      c.embedded.injective ((hβ v).symm.trans ((congrArg p hvw).trans (hβ w)))
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
    by_cases hm0 : m = 0
    · simpa [hm0] using hm
    have hmp := hperiod_of_return m w (by rw [← hm]; exact hvw)
    have hmpos : 0 < m.natAbs := Int.natAbs_pos.mpr hm0
    have hmk := hkmin m.natAbs hmpos (hperiod_abs m hmp)
    have hmkR : (k : ℝ) ≤ (m.natAbs : ℝ) := by exact_mod_cast hmk
    have hbound : |(m : ℝ)| < (k : ℝ) := by
      apply (abs_lt).mpr
      constructor <;> nlinarith [Real.pi_pos, hv.1, hv.2, hw.1, hw.2]
    have habs : (m.natAbs : ℝ) = |(m : ℝ)| := by
      simp only [Nat.cast_natAbs, Int.cast_abs]
    rw [habs] at hmkR
    exact False.elim (not_le_of_gt hbound hmkR)
  let period : ℝ := (k : ℝ) * (2 * Real.pi)
  have hperiodpos : 0 < period := mul_pos (by exact_mod_cast hkpos) (by positivity)
  letI : Fact (0 < period) := ⟨hperiodpos⟩
  let A := AddCircle period
  let α : C(A, U) := ⟨hkperiod.lift, β.continuous.quotient_lift _⟩
  have hαcoe (v : ℝ) : α (v : A) = β v := rfl
  have hαinj : Function.Injective α := by
    intro a b hab
    obtain ⟨v, hv, hva⟩ := AddCircle.eq_coe_Ico a
    obtain ⟨w, hw, hwb⟩ := AddCircle.eq_coe_Ico b
    rw [← hva, ← hwb, hαcoe, hαcoe] at hab
    have hvw := hkinj hv hw hab
    rw [← hva, ← hwb, hvw]
  let circleHomeo : A ≃ₜ Circle := AddCircle.homeomorphCircle (ne_of_gt hperiodpos)
  let r : C(Circle, U) := ⟨fun z => α (circleHomeo.symm z),
    α.continuous.comp circleHomeo.symm.continuous⟩
  have hr : IsEmbedding r :=
    (α.continuous.isClosedEmbedding hαinj).isEmbedding.comp circleHomeo.symm.isEmbedding
  have hrange : Set.range r = Set.range β := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨v, hv, hvw⟩ := AddCircle.eq_coe_Ico (circleHomeo.symm w)
      refine ⟨v, ?_⟩
      change β v = α (circleHomeo.symm w)
      rw [← hvw, hαcoe]
    · rintro ⟨v, rfl⟩
      refine ⟨circleHomeo (v : A), ?_⟩
      change α (circleHomeo.symm (circleHomeo (v : A))) = β v
      rw [circleHomeo.symm_apply_apply, hαcoe]
  let rP : C(Circle, Schoenflies.Plane) := ⟨fun z => e (r z),
    e.continuous.comp r.continuous⟩
  have hrP : IsEmbedding rP := e.isEmbedding.comp hr
  have hJordan := CurveComplex.isJordanCurve_range_of_isEmbedding_circle rP hrP
  obtain ⟨d, hd, hbd⟩ := CurveComplex.jordan_curve_bounds_disc
    (⟨rP, hrP⟩ : CurveComplex.Curve Schoenflies.Plane) hJordan
  have hregion : Set.range d = Schoenflies.inside (Set.range rP) ∪ Set.range rP :=
    CurveComplex.embedded_disc_range_eq_closed_inside d hd (Set.range rP) hJordan hbd
  have hturn : p (β (2 * Real.pi)) = p (β 0) := by
    rw [hβ, hβ]
    simpa using congrArg c.map (Circle.periodic_exp 0)
  obtain ⟨g, hg⟩ := hp.apply_eq_iff_mem_orbit.mp hturn
  have hgshift (v : ℝ) : g • β v = β (v + 2 * Real.pi) := by
    have hh : (fun w : ℝ => g • β w) = (fun w : ℝ => β (w + 2 * Real.pi)) := by
      apply cov.eq_of_comp_eq (hp.continuous_const_smul g |>.comp β.continuous)
        (β.continuous.comp (by fun_prop)) (a := 0)
      · ext w
        change p (g • β w) = p (β (w + 2 * Real.pi))
        rw [hp.map_smul, hβ, hβ, Circle.periodic_exp]
      · simpa using hg
    exact congrFun hh v
  have hgRange : (g • ·) '' Set.range r = Set.range r := by
    rw [hrange]
    ext z
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨v + 2 * Real.pi, (hgshift v).symm⟩
    · rintro ⟨v, rfl⟩
      refine ⟨β (v - 2 * Real.pi), ⟨_, rfl⟩, ?_⟩
      simpa using hgshift (v - 2 * Real.pi)
  let H : U ≃ₜ U := {
    toFun := fun z => g • z
    invFun := fun z => g⁻¹ • z
    left_inv := by intro z; simp
    right_inv := by intro z; simp
    continuous_toFun := hp.continuous_const_smul g
    continuous_invFun := hp.continuous_const_smul g⁻¹ }
  let HP : Schoenflies.Plane ≃ₜ Schoenflies.Plane := e.symm.trans (H.trans e)
  have hHP (z : U) : HP (e z) = e (g • z) := by simp [HP, H]
  have hBoundary : HP '' Set.range rP = Set.range rP := by
    ext z
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      obtain ⟨v, hv⟩ := hgRange ▸ (Set.mem_image_of_mem (g • ·) (Set.mem_range_self w))
      refine ⟨v, ?_⟩
      change e (r v) = HP (e (r w))
      rw [hHP, hv]
    · rintro ⟨w, rfl⟩
      obtain ⟨v, ⟨z, hz⟩, hv⟩ := hgRange.symm ▸ (Set.mem_range_self w)
      refine ⟨e v, ⟨z, ?_⟩, ?_⟩
      · change e (r z) = e v
        rw [hz]
      · change HP (e v) = e (r w)
        rw [hHP]
        exact congrArg e hv
  have hDisk : HP '' Set.range d = Set.range d := by
    rw [hregion, Set.image_union, CurveComplex.jordan_inside_homeomorph_image, hBoundary]
  have hgOne : g = 1 := by
    obtain ⟨z, hz⟩ := CurveComplex.fixedPoint_of_disc_subset_homeomorph_image
      d hd (fun u =>
        LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.BrouwerFixedPoint.brouwer_fixed_point
          u u.continuous) HP hDisk.symm.subset
    have hfix : g • e.symm z = e.symm z := by
      apply e.injective
      have hh := hHP (e.symm z)
      simp only [e.apply_symm_apply] at hh
      rw [e.apply_symm_apply]
      exact hh.symm.trans hz
    exact hp.isCancelSMul.right_cancel g 1 (e.symm z) (by simpa using hfix)
  have honeperiod : Function.Periodic β (2 * Real.pi) := by
    intro v
    simpa [hgOne] using (hgshift v).symm
  have hfactor : Function.FactorsThrough β Circle.exp := by
    intro v w hvw
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hvw
    rw [hm, honeperiod.int_mul m]
  let L : C(Circle, U) :=
    (Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective).lift β hfactor
  have hL (v : ℝ) : L (Circle.exp v) = β v := by
    exact congrArg (fun f : C(ℝ, U) => f v)
      ((Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective).lift_comp β hfactor)
  have hLp (z : Circle) : p (L z) = c.map z := by
    obtain ⟨v, rfl⟩ := Circle.exp_surjective z
    rw [hL, hβ]
  letI : MulAction G Schoenflies.Plane := e.symm.toEquiv.mulAction G
  have haction (g : G) (z : Schoenflies.Plane) :
      e.symm (g • z) = g • e.symm z := by
    change e.symm (e (g • e.symm z)) = _
    exact e.symm_apply_apply _
  let q : Schoenflies.Plane → S := p ∘ e.symm
  have hq : IsQuotientCoveringMap q G := {
    toIsQuotientMap := hp.toIsQuotientMap.comp e.symm.isQuotientMap
    continuous_const_smul := by
      intro a
      change Continuous (fun z => e (a • e.symm z))
      exact e.continuous.comp ((hp.continuous_const_smul a).comp e.symm.continuous)
    apply_eq_iff_mem_orbit := by
      intro z w
      change p (e.symm z) = p (e.symm w) ↔ _
      rw [hp.apply_eq_iff_mem_orbit]
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨a, e.symm.injective ?_⟩
        rw [haction]
        exact ha
      · rintro ⟨a, rfl⟩
        exact ⟨a, (haction a w).symm⟩
    disjoint := by
      intro z
      obtain ⟨V, hV, hVdisj⟩ := hp.disjoint (e.symm z)
      refine ⟨e.symm ⁻¹' V, e.symm.continuous.continuousAt.preimage_mem_nhds hV, ?_⟩
      intro a ha
      obtain ⟨w, ⟨v, hv, hvw⟩, hw⟩ := ha
      apply hVdisj a
      refine ⟨e.symm w, ⟨e.symm v, hv, ?_⟩, hw⟩
      exact (haction a v).symm.trans (congrArg e.symm hvw) }
  let LP : C(Circle, Schoenflies.Plane) :=
    ⟨fun z => e (L z), e.continuous.comp L.continuous⟩
  have hLPnull : LP.Nullhomotopic :=
    ((contractible_iff_id_nullhomotopic Schoenflies.Plane).mp
      (inferInstance : ContractibleSpace Schoenflies.Plane)).comp_left LP
  let Q : C(Schoenflies.Plane, S) := ⟨q, hq.isCoveringMap.continuous⟩
  have hQc : Q.comp LP = (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)) := by
    ext z
    change p (e.symm (e (L z))) = c.map z
    rw [e.symm_apply_apply, hLp]
  apply CurveComplex.boundsDisc_of_nullhomotopic_planar_quotient_cover_complete q hq c
  rw [← hQc]
  exact hLPnull.comp_right Q

/-- Least-period exclusion derived from concrete planar geometry and actual
 disk nonbounding; not from an assumed pi-one certificate. -/
theorem actual_planar_essential_lift_has_no_integer_return
    {S U G : Type} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace U] [Group G] [MulAction G U]
    (p : U → S) (hp : IsQuotientCoveringMap p G)
    (e : U ≃ₜ Schoenflies.Plane)
    (b : CurveComplex.EssentialCurve S) (β : C(ℝ, U))
    (hβ : ∀ t, p (β t) = b.val.map (Circle.exp t)) :
    ∀ (n : ℤ), n ≠ 0 → ∀ t : ℝ,
      β (t + (n : ℝ) * (2 * Real.pi)) ≠ β t := by
  intro n hn t hreturn
  exact b.property (boundsDisc_of_integer_return_in_actual_planar_cover
    p hp e b.val β hβ n hn t hreturn)

end CurveComplex.LocalSurgery
