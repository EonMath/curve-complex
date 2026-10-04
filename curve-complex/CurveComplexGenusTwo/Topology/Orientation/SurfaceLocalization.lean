import CurveComplexGenusTwo.Topology.Orientation.CompactHomologySupport
import CurveComplexGenusTwo.Topology.ChartLift
import CurveComplexGenusTwo.CWHurewicz.PairNaturality
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

open Set Topology unitInterval Schoenflies
open scoped NNReal
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.GenusOrientationCandidate
set_option backward.isDefEq.respectTransparency false

/-- Actual compactly supported chart motion moves a surface point to every
point in a sufficiently small neighborhood. -/
theorem surface_point_move_local
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (p : S) :
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, ∃ H : AmbientIsotopy S, H.finalMap p = q := by
  classical
  have hsmall (f : Plane → Plane)
        (c : ℝ≥0) (hc : (c : ℝ) < 1) (hf : LipschitzWith c f) :
        ∃ H : AmbientIsotopy Plane,
          (∀ t x, H.map (t, x) = x + (t : ℝ) • f x) ∧
          (∀ t x, f x = 0 → H.map (t, x) = x) := by
    classical
    let F : Interval × Plane → Plane :=
      fun p => p.2 + (p.1 : ℝ) • f p.2
    have hF : Continuous F := continuous_snd.add
      ((continuous_subtype_val.comp continuous_fst).smul
        (hf.continuous.comp continuous_snd))
    refine ⟨{ map := ⟨F, hF⟩, homeomorphism_at := ?_, at_zero := ?_ },
      fun t x => rfl, ?_⟩
    · intro t
      have happ : ApproximatesLinearOn (fun x => F (t, x))
          (ContinuousLinearEquiv.refl ℝ Plane : Plane →L[ℝ] Plane)
          Set.univ c := by
        intro x _ y _
        have heq : F (t, x) - F (t, y) - (x - y) =
            (t : ℝ) • (f x - f y) := by dsimp [F]; module
        change ‖F (t, x) - F (t, y) - (x - y)‖ ≤ _
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
        calc
          (t : ℝ) * ‖f x - f y‖ ≤ 1 * ‖f x - f y‖ :=
            mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
          _ ≤ c * ‖x - y‖ := by simpa [dist_eq_norm] using hf.dist_le_mul x y
      let e := happ.toHomeomorph (fun x => F (t, x)) (Or.inr (by simpa using hc))
      exact ⟨e, fun x => rfl⟩
    · intro x
      simp [F]
    · intro t x hx
      change x + (t : ℝ) • f x = x
      simp [hx]
  
  have hpush (p v : Plane) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ < 1) :
        ∃ H : AmbientIsotopy Plane,
          (∀ x, H.finalMap x = x + max (R - dist x p) 0 • v) ∧
          ∀ t x, R ≤ dist x p → H.map (t, x) = x := by
    classical
    let b : Plane → ℝ := fun x => max (R - dist x p) 0
    have hb0 : LipschitzWith 1 (fun x : Plane => R - dist x p) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
        sub_sub_sub_cancel_left, abs_sub_comm] using abs_dist_sub_le x y p
    have hb : LipschitzWith 1 b := hb0.max_const 0
    let f : Plane → Plane := fun x => b x • v
    have hf : LipschitzWith ‖v‖₊ f := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change ‖b x • v - b y • v‖ ≤ ‖v‖ * dist x y
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      have h := hb.dist_le_mul x y
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
      calc
        |b x - b y| * ‖v‖ ≤ dist x y * ‖v‖ :=
          mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ = ‖v‖ * dist x y := mul_comm _ _
    obtain ⟨H, hH, hfix⟩ := hsmall f ‖v‖₊ hv hf
    refine ⟨H, ?_, ?_⟩
    · intro x
      unfold AmbientIsotopy.finalMap
      rw [hH]
      simp [f, b]
    · intro t x hx
      apply hfix
      simp [f, b, max_eq_right (sub_nonpos.mpr hx)]
  let E := chartAt Plane p
  have hpE : p ∈ E.source := mem_chart_source Plane p
  obtain ⟨r, hr, hrE⟩ := Metric.isOpen_iff.mp E.open_target
    (E p) (E.map_source hpE)
  let R : ℝ := r / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRr : R < r := by dsimp [R]; linarith
  have hCV : Metric.closedBall (E p) R ⊆ E.target :=
    (Metric.closedBall_subset_ball hRr).trans hrE
  let U : Set S := E.source ∩ E ⁻¹' Metric.ball (E p) R
  have hU : IsOpen U :=
    E.continuousOn_toFun.isOpen_inter_preimage E.open_source Metric.isOpen_ball
  have hpU : p ∈ U := ⟨hpE, Metric.mem_ball_self hR⟩
  refine ⟨U, hU, hpU, ?_⟩
  intro q hq
  let v : Plane := R⁻¹ • (E q - E p)
  have hv : ‖v‖ < 1 := by
    have hdist : ‖E q - E p‖ < R := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hq.2
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    calc
      R⁻¹ * ‖E q - E p‖ = ‖E q - E p‖ / R := by rw [div_eq_mul_inv, mul_comm]
      _ < 1 := (div_lt_one hR).mpr hdist
  obtain ⟨H, hmove, hfix⟩ := hpush (E p) v R hR hv
  have hcenter : H.finalMap (E p) = E q := by
    rw [hmove]
    simp only [dist_self, sub_zero, max_eq_left hR.le]
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    module
  obtain ⟨K, G, hcoord, hGU, hGfix⟩ := position_surface_chart_lift S
    E.source E.target E.open_source E.toHomeomorphSourceTarget
    (Metric.closedBall (E p) R) (isCompact_closedBall _ _) hCV H (by
      intro t x hx
      apply hfix
      have hh : ¬ dist x (E p) ≤ R := hx
      exact (lt_of_not_ge hh).le)
  have hpoint : K.finalMap ⟨p,hpE⟩ = ⟨q,hq.1⟩ := by
    apply Subtype.ext
    apply E.injOn (K.finalMap ⟨p,hpE⟩).property hq.1
    have hh := hcoord (⟨1, by norm_num⟩ : Interval) ⟨p,hpE⟩
    change E (K.finalMap ⟨p,hpE⟩).val = H.finalMap (E p) at hh
    exact hh.trans hcenter
  refine ⟨G, ?_⟩
  have he := hGU (⟨1, by norm_num⟩ : Interval) ⟨p,hpE⟩
  change G.finalMap p = (K.finalMap ⟨p,hpE⟩).val at he
  rw [hpoint] at he
  exact he

/-- A global actual singular class has locally constant vanishing under point
localization, because chart motion is homotopic to identity. -/
theorem surface_localization_zero_locus_closed
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (n : ℕ) (z : H S n) :
    IsClosed {x : S | homologyToRelative S ({x}ᶜ : Set S) n z = 0} := by
  classical
  have htransport (x y : S) (f : C(S,S))
      (hf : ∀ t ∈ ({x}ᶜ : Set S), f t ∈ ({y}ᶜ : Set S))
      (hh : ContinuousMap.Homotopic f (ContinuousMap.id S))
      (hx : homologyToRelative S ({x}ᶜ : Set S) n z = 0) :
      homologyToRelative S ({y}ᶜ : Set S) n z = 0 := by
    have hn := pairRelativeHomologyMap_commutes
      ({x}ᶜ : Set S) ({y}ᶜ : Set S) f hf n
    have he : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) =
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map (𝟙 (TopCat.of S))) :=
      TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        hh.some (ModuleCat.of ℤ ℤ) n
    have hid : HomologicalComplex.homologyMap
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) n = 𝟙 (H S n) := by
      change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) = _
      rw [he]
      exact CategoryTheory.Functor.map_id _ _
    rw [hid] at hn
    have hp := congrArg (fun q => q z) hn
    change pairRelativeHomologyMap ({x}ᶜ : Set S) ({y}ᶜ : Set S) f hf n
      (homologyToRelative S ({x}ᶜ : Set S) n z) =
      homologyToRelative S ({y}ᶜ : Set S) n z at hp
    rw [hx, map_zero] at hp
    exact hp.symm
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U,hU,hxU,hmove⟩ := surface_point_move_local S x
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy
  change homologyToRelative S ({y}ᶜ : Set S) n z ≠ 0
  intro hzero
  obtain ⟨H,hH⟩ := hmove y hy
  obtain ⟨e,he⟩ := H.homeomorphism_at (⟨1, by norm_num⟩ : Interval)
  have hepq : e x = y := (he x).trans hH
  let f : C(S,S) := ⟨e,e.continuous⟩
  let fi : C(S,S) := ⟨e.symm,e.symm.continuous⟩
  let Hf : ContinuousMap.Homotopy (ContinuousMap.id S) f := {
    toContinuousMap := H.map
    map_zero_left := H.at_zero
    map_one_left := fun t => (he t).symm }
  have hfi : ContinuousMap.Homotopic fi (ContinuousMap.id S) := by
    have h := (ContinuousMap.Homotopic.symm ⟨Hf⟩).comp
      (ContinuousMap.Homotopic.refl fi)
    have hcomp : f.comp fi = ContinuousMap.id S := by
      ext t
      exact e.apply_symm_apply t
    rw [hcomp, ContinuousMap.id_comp] at h
    exact h.symm
  have hpres : ∀ t ∈ ({y}ᶜ : Set S), fi t ∈ ({x}ᶜ : Set S) := by
    intro t ht
    change t ≠ y at ht
    change e.symm t ≠ x
    intro hh
    apply ht
    have heq := congrArg e hh
    rw [e.apply_symm_apply] at heq
    exact heq.trans hepq
  exact hx (htransport y x fi hpres hfi hzero)

end CurveComplex.GenusOrientationCandidate
