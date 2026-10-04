import CurveComplexGenusTwo.Topology.IntersectionParity.CutCoverDefinitions
import CurveComplexGenusTwo.Topology.IntersectionParity.ActualLoopSweep
import CurveComplexGenusTwo.Topology.IntersectionParity.CutCoverLifts
import CurveComplexGenusTwo.Topology.IntersectionParity.LocalSheetFlip
import CurveComplexGenusTwo.Topology.IntersectionParity.FiniteSheetCount
import CurveComplexGenusTwo.Topology.IntersectionParity.RealIntervalCoordinates
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge

open Set Topology

open scoped unitInterval

namespace CurveComplex.LocalSurgery

/-- Count genuine crossings by the sheet changes of an actual cut-cover lift.
The cover is a geometric intermediate construction: existence must be proved
separately before it can be used for unconditional parity. -/
theorem cut_cover_lift_closes_iff_even_crossings
    {S : Type*} [TopologicalSpace S] {a : Curve S}
    (A : CurveCutCover a) (b : Curve S) (hab : Transverse a b)
    (z : Circle) (hz : b.map z ∉ a.image)
    (g : C(I, A.core.TotalSpace))
    (hlift : A.core.proj ∘ g = intervalCurveLoopFrom b z) :
    g 0 = g 1 ↔ Even hab.1.toFinset.card := by
  let γ := intervalCurveLoopFrom b z
  let events := γ ⁻¹' (a.image ∩ b.image)
  have hends : γ 0 = b.map z ∧ γ 1 = b.map z := by
    simp [γ, intervalCurveLoopFrom, intervalCircleParameterFrom,
      intervalCircleParameter]
  have heventInterior (u : unitInterval) (hu : u ∈ events) :
      0 < (u : ℝ) ∧ (u : ℝ) < 1 := by
    have huimage : γ u ∈ a.image := hu.1
    constructor
    · by_contra h
      have heq : u = 0 := Subtype.ext (le_antisymm (le_of_not_gt h) u.property.1)
      rw [heq, hends.1] at huimage
      exact hz huimage
    · by_contra h
      have heq : u = 1 := Subtype.ext (le_antisymm u.property.2 (le_of_not_gt h))
      rw [heq, hends.2] at huimage
      exact hz huimage
  have hγinj : Set.InjOn γ events := by
    intro u hu v hv heq
    have huI := heventInterior u hu
    have hvI := heventInterior v hv
    have hcircle := b.embedded.injective heq
    change z * Circle.exp (2 * Real.pi * (u : ℝ)) =
      z * Circle.exp (2 * Real.pi * (v : ℝ)) at hcircle
    have hexp := mul_left_cancel hcircle
    have hangle := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi)
      (by simp)
      (show 2 * Real.pi * (u : ℝ) ∈ Set.Ico 0 (2 * Real.pi) from
        ⟨mul_nonneg (by positivity) huI.1.le, by nlinarith [Real.pi_pos]⟩)
      (show 2 * Real.pi * (v : ℝ) ∈ Set.Ico 0 (2 * Real.pi) from
        ⟨mul_nonneg (by positivity) hvI.1.le, by nlinarith [Real.pi_pos]⟩) hexp
    apply Subtype.ext
    nlinarith [Real.pi_pos]
  have hfiniteEvents : events.Finite := hab.1.preimage hγinj
  have hexpRange : Circle.exp '' Set.Icc 0 (2 * Real.pi) = Set.univ := by
    simpa only [zero_add, Circle.exp_surjective.range_eq] using
      Circle.periodic_exp.image_Icc Real.two_pi_pos (0 : ℝ)
  have hparameterSurj : Function.Surjective (intervalCircleParameterFrom z) := by
    intro v
    have hv : z⁻¹ * v ∈ Circle.exp '' Set.Icc 0 (2 * Real.pi) := by
      rw [hexpRange]
      trivial
    obtain ⟨θ, hθI, hθ⟩ := hv
    let u : unitInterval := ⟨θ / (2 * Real.pi),
      ⟨div_nonneg hθI.1 Real.two_pi_pos.le,
        (div_le_one Real.two_pi_pos).mpr hθI.2⟩⟩
    refine ⟨u, ?_⟩
    change z * Circle.exp (2 * Real.pi * (θ / (2 * Real.pi))) = v
    have hscale : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
      field_simp
    rw [hscale, hθ]
    simp
  have hγrange : Set.range γ = b.image := by
    apply Set.ext
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨intervalCircleParameterFrom z u, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨u, hu⟩ := hparameterSurj v
      exact ⟨u, by change b.map (intervalCircleParameterFrom z u) = b.map v; rw [hu]⟩
  have hγbij : Set.BijOn γ events (a.image ∩ b.image) := by
    refine ⟨fun _ hu => hu, hγinj, ?_⟩
    intro x hx
    have hxrange : x ∈ Set.range γ := by rw [hγrange]; exact hx.2
    obtain ⟨u, hu⟩ := hxrange
    refine ⟨u, ?_, hu⟩
    change γ u ∈ a.image ∩ b.image
    rw [hu]
    exact hx
  have hcardEvents : hfiniteEvents.toFinset.card = hab.1.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfiniteEvents,
      ← Set.ncard_eq_toFinset_card _ hab.1]
    exact hγbij.ncard_eq
  classical
  have hγinjAll : Set.InjOn γ (Set.Ioo 0 1) := by
    intro u hu v hv heq
    have hcircle := b.embedded.injective heq
    change z * Circle.exp (2 * Real.pi * (u : ℝ)) =
      z * Circle.exp (2 * Real.pi * (v : ℝ)) at hcircle
    have hu1 : (u : ℝ) < 1 := hu.2
    have hv1 : (v : ℝ) < 1 := hv.2
    have hangle := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi)
      (by simp)
      (show 2 * Real.pi * (u : ℝ) ∈ Set.Ico 0 (2 * Real.pi) from
        ⟨mul_nonneg (by positivity) hu.1.le, by nlinarith [Real.pi_pos, hu1]⟩)
      (show 2 * Real.pi * (v : ℝ) ∈ Set.Ico 0 (2 * Real.pi) from
        ⟨mul_nonneg (by positivity) hv.1.le, by nlinarith [Real.pi_pos, hv1]⟩)
      (mul_left_cancel hcircle)
    apply Subtype.ext
    nlinarith [Real.pi_pos]
  let F : Finset ℝ := hfiniteEvents.toFinset.image Subtype.val
  have hFcard : F.card = hab.1.toFinset.card := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact hcardEvents
  have hFmem (x : ℝ) : x ∈ F ↔ ∃ u : unitInterval, u ∈ events ∧ (u : ℝ) = x := by
    simp [F]
  have hFinside : ∀ x ∈ F, 0 < x ∧ x < 1 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (hFmem x).mp hx
    exact heventInterior u hu
  let realg := realIntervalPath g
  let sheet : ℝ → ZMod 2 := fun x => (A.complementTriv (realg x)).2
  have hgreal (u : unitInterval) : realg (u : ℝ) = g u := by
    change g (Set.projIcc 0 1 (by norm_num) (u : ℝ)) = g u
    rw [Set.projIcc_of_mem _ u.property]
  have hOff (u : unitInterval) (huF : (u : ℝ) ∉ F) : A.core.proj (g u) ∉ a.image := by
    intro hp
    have hproj : A.core.proj (g u) = γ u := congrFun hlift u
    have huEvent : u ∈ events := ⟨hproj ▸ hp, by rw [← hγrange]; exact ⟨u, rfl⟩⟩
    exact huF ((hFmem _).mpr ⟨u, huEvent, rfl⟩)
  have hcont : ContinuousOn sheet (Set.Icc 0 1 \ (F : Set ℝ)) :=
    continuous_snd.comp_continuousOn
      (A.complementTriv.continuousOn.comp realg.continuous.continuousOn (by
        intro x hx
        let u : unitInterval := ⟨x, hx.1⟩
        have hOffu := hOff u hx.2
        apply A.complementTriv.mem_source.mpr
        rw [A.complement_baseSet]
        change A.core.proj (realg x) ∉ a.image
        rw [hgreal u]
        exact hOffu))
  have hflip : ∀ x ∈ F, ∃ δ : ℝ, 0 < δ ∧
      ∀ v w : ℝ, x - δ < v → v < x → x < w → w < x + δ →
        sheet v = sheet w + 1 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (hFmem x).mp hx
    have huinside := heventInterior u hu
    obtain ⟨d, hd, hlocal⟩ := cut_cover_sheet_flips_at_crossing A u huinside γ
      hγinjAll hγrange (hab.2 _ hu) g hlift
    let δ := min d (min (u : ℝ) (1 - (u : ℝ))) / 2
    have hδ : 0 < δ := div_pos
      (lt_min hd (lt_min huinside.1 (sub_pos.mpr huinside.2))) (by norm_num)
    have hδd : δ < d := by dsimp [δ]; linarith [min_le_left d (min (u : ℝ) (1 - (u : ℝ)))]
    have hδu : δ < (u : ℝ) := by
      dsimp [δ]
      linarith [min_le_right d (min (u : ℝ) (1 - (u : ℝ))), min_le_left (u : ℝ) (1 - (u : ℝ))]
    have hδone : δ < 1 - (u : ℝ) := by
      dsimp [δ]
      linarith [min_le_right d (min (u : ℝ) (1 - (u : ℝ))), min_le_right (u : ℝ) (1 - (u : ℝ))]
    refine ⟨δ, hδ, ?_⟩
    intro v w hvlo hvu huw hwhi
    let vI : unitInterval := ⟨v, by constructor <;> linarith⟩
    let wI : unitInterval := ⟨w, by constructor <;> linarith⟩
    have hf := hlocal vI wI (by change (u : ℝ) - d < v; linarith)
      hvu huw (by change w < (u : ℝ) + d; linarith)
    have hvReal : realg v = g vI := hgreal vI
    have hwReal : realg w = g wI := hgreal wI
    dsimp only [sheet]
    rw [hvReal, hwReal]
    exact hf
  have hsum := finite_sheet_flips_endpoint_count F hFinside sheet hcont hflip
  rw [hFcard] at hsum
  have hlabel : sheet 0 = sheet 1 ↔ (hab.1.toFinset.card : ZMod 2) = 0 := by
    rw [hsum]
    constructor
    · intro heq
      have heq' : sheet 1 + (hab.1.toFinset.card : ZMod 2) = sheet 1 + 0 := by simpa using heq
      exact add_left_cancel heq'
    · intro heq
      rw [heq, add_zero]
  have hendOff (u : unitInterval) (hue : u = 0 ∨ u = 1) : A.core.proj (g u) ∉ a.image := by
    have hp : A.core.proj (g u) = γ u := congrFun hlift u
    rw [hp]
    rcases hue with rfl | rfl <;> simpa only [hends.1, hends.2] using hz
  have hsource (u : unitInterval) (hue : u = 0 ∨ u = 1) : g u ∈ A.complementTriv.source := by
    apply A.complementTriv.mem_source.mpr
    rw [A.complement_baseSet]
    exact hendOff u hue
  have hprojEnd : A.core.proj (g 0) = A.core.proj (g 1) := by
    have h₀ : A.core.proj (g 0) = γ 0 := congrFun hlift 0
    have h₁ : A.core.proj (g 1) = γ 1 := congrFun hlift 1
    exact h₀.trans (hends.1.trans (hends.2.symm.trans h₁.symm))
  have hclosure : g 0 = g 1 ↔ sheet 0 = sheet 1 := by
    have hsheet0 : sheet 0 = (A.complementTriv (g 0)).2 := by
      change (A.complementTriv (realg 0)).2 = _
      exact congrArg (fun q => (A.complementTriv q).2) (by simpa using hgreal (0 : unitInterval))
    have hsheet1 : sheet 1 = (A.complementTriv (g 1)).2 := by
      change (A.complementTriv (realg 1)).2 = _
      exact congrArg (fun q => (A.complementTriv q).2) (by simpa using hgreal (1 : unitInterval))
    rw [hsheet0, hsheet1]
    constructor
    · intro heq
      rw [heq]
    · intro heq
      apply A.complementTriv.injOn (hsource 0 (Or.inl rfl)) (hsource 1 (Or.inr rfl))
      apply Prod.ext
      · exact (A.complementTriv.coe_fst (hsource 0 (Or.inl rfl))).trans
          (hprojEnd.trans (A.complementTriv.coe_fst (hsource 1 (Or.inr rfl))).symm)
      · exact heq
  exact hclosure.trans (hlabel.trans ((ZMod.natCast_eq_zero_iff _ 2).trans even_iff_two_dvd.symm))

end CurveComplex.LocalSurgery
