import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualDerivedTraceClock

namespace CurveComplex.HyperellipticModel.ArcSurgery.ActualFiniteEventTrace
open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
variable {M : HyperellipticModel E S} [LinearOrder (EssentialArcClass M)]
  {anchor : EssentialMarkedArc M}
local notation "K" => geometricComplex (actualA M)
local notation "Stage" σ => CurveComplex.RealizationPoint (CurveComplex.fullSubcomplex K (· ∈ σ))
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Depth is propagated by the actual completed-event normalization, never by
supplied stage times or a supplied homotopy. -/
noncomputable def atDepth : {σ : Finset (ActiveVertex (actualA M))} →
    ActualFiniteEventTrace M anchor σ → (ℝ × Stage σ) → geometricRealization (actualA M)
  | σ, .stop _, z => CurveComplex.fullToAmbient K (· ∈ σ) z.2
  | _, .cut c T, z => if z.1 ≤ c.selectedMass z.2 then c.clampedEvent z else
      T.atDepth ((z.1-c.selectedMass z.2)/c.endpointScale z.2, c.endpointToNext z.2)

theorem atDepth_before {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) (p : Stage σ) (depth : ℝ)
    (hd : depth ≤ 0) : T.atDepth (depth,p) = CurveComplex.fullToAmbient K (· ∈ σ) p := by
  cases T with
  | stop σ => rfl
  | cut c T =>
    rw [atDepth, ite_eq_left (hd.trans (c.selectedMass_nonneg p))]
    exact c.clampedEvent_before p depth hd

theorem atDepth_continuous {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) : Continuous T.atDepth := by
  induction T with
  | stop σ => exact (CurveComplex.fullToAmbient_continuous K _).comp continuous_snd
  | cut c T ih =>
    have hmass : Continuous (fun z : ℝ × Stage _ => c.selectedMass z.2) :=
      c.selectedMass_continuous.comp continuous_snd
    have hscale : Continuous (fun z : ℝ × Stage _ => c.endpointScale z.2) :=
      c.endpointScale_continuous.comp continuous_snd
    have hnext : Continuous (fun z : ℝ × Stage _ =>
        ((z.1-c.selectedMass z.2)/c.endpointScale z.2, c.endpointToNext z.2)) :=
      ((continuous_fst.sub hmass).div hscale
        (fun z => ne_of_gt (c.endpointScale_positive z.2))).prodMk
        (c.endpointToNext.continuous.comp continuous_snd)
    apply continuous_if_le continuous_fst hmass c.clampedEvent.continuous.continuousOn
      (ih.comp hnext).continuousOn
    intro z hz
    have hz0 : (z.1-c.selectedMass z.2)/c.endpointScale z.2 = 0 := by rw [hz]; simp
    change c.clampedEvent z = T.atDepth
      ((z.1-c.selectedMass z.2)/c.endpointScale z.2, c.endpointToNext z.2)
    rw [hz0, T.atDepth_before _ 0 le_rfl, c.endpointToNext_ambient]
    exact c.clampedEvent_after z.2 z.1 hz.ge

theorem totalWidth_nonneg {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) (p : Stage σ) : 0 ≤ T.totalWidth p := by
  rw [T.totalWidth_eq_sum]
  exact Finset.sum_nonneg (fun j _ => T.bandWidth_nonneg j p)

theorem endpoint_eq_start_of_zero_totalWidth {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) : ∀ p : Stage σ,
    T.totalWidth p = 0 → T.endpoint p = CurveComplex.fullToAmbient K (· ∈ σ) p := by
  induction T with
  | stop σ => intro p _; rfl
  | cut c T ih =>
    intro p hz
    have hm := c.selectedMass_nonneg p
    have hs := c.endpointScale_positive p
    have ht := T.totalWidth_nonneg (c.endpointToNext p)
    have hz' : c.selectedMass p + c.endpointScale p * T.totalWidth (c.endpointToNext p) = 0 := hz
    have hm0 : c.selectedMass p = 0 := by nlinarith
    have ht0 : T.totalWidth (c.endpointToNext p) = 0 := by nlinarith
    change T.endpoint (c.endpointToNext p) = _
    rw [ih _ ht0, c.endpointToNext_ambient]
    exact actualSurgeryFullStageEvent_zeroWeight_fixed M anchor c.classes c.position
      c.crossing c.surgery _ c.face c.contains c.selected_mem p 1 hm0

theorem atDepth_after {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) : ∀ p : Stage σ, ∀ depth : ℝ,
    T.totalWidth p ≤ depth → T.atDepth (depth,p) = T.endpoint p := by
  induction T with
  | stop σ => intro p depth _; rfl
  | cut c T ih =>
    intro p depth hd
    have hs := c.endpointScale_positive p
    have ht := T.totalWidth_nonneg (c.endpointToNext p)
    have hd' : c.selectedMass p + c.endpointScale p * T.totalWidth (c.endpointToNext p) ≤ depth := hd
    rw [atDepth]
    split_ifs with hm
    · have ht0 : T.totalWidth (c.endpointToNext p) = 0 := by nlinarith
      have hm' : c.selectedMass p ≤ depth := by nlinarith
      rw [c.clampedEvent_after _ _ hm']
      change c.event (1,p) = T.endpoint (c.endpointToNext p)
      rw [T.endpoint_eq_start_of_zero_totalWidth _ ht0, c.endpointToNext_ambient]
    · apply ih
      apply (le_div_iff₀ hs).mpr
      linarith

/-- The continuous trace evaluated at the intrinsically defined source depth tθ. -/
noncomputable def intrinsicDepthMap {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) :
    C(CurveComplex.EdgeTime × Stage σ, geometricRealization (actualA M)) :=
  ⟨fun z => T.atDepth (z.1.val * intrinsicThickness (anchor := anchor) σ z.2, z.2),
    T.atDepth_continuous.comp
      (((continuous_subtype_val.comp continuous_fst).mul
        ((intrinsicThickness_continuous (anchor := anchor) σ).comp continuous_snd)).prodMk
        continuous_snd)⟩

theorem intrinsicDepthMap_starts {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) (p : Stage σ) :
    T.intrinsicDepthMap (0,p) = CurveComplex.fullToAmbient K (· ∈ σ) p := by
  change T.atDepth (0 * intrinsicThickness (anchor := anchor) σ p,p) = _
  rw [zero_mul]
  exact T.atDepth_before p 0 le_rfl

/-- Trace-derived total width yields an unconditional actual homotopy. -/
noncomputable def derivedDepthHomotopy {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) :
    ContinuousMap.Homotopy
      ⟨CurveComplex.fullToAmbient K (· ∈ σ), CurveComplex.fullToAmbient_continuous K _⟩ T.endpoint where
  toFun z := T.atDepth (z.1.val * T.totalWidth z.2,z.2)
  continuous_toFun := T.atDepth_continuous.comp
    (((continuous_subtype_val.comp continuous_fst).mul
      (T.totalWidth_continuous.comp continuous_snd)).prodMk continuous_snd)
  map_zero_left p := by
    change T.atDepth (0*T.totalWidth p,p) = _
    rw [zero_mul]
    exact T.atDepth_before p 0 le_rfl
  map_one_left p := by
    change T.atDepth (1*T.totalWidth p,p) = _
    rw [one_mul]
    exact T.atDepth_after p _ le_rfl

end CurveComplex.HyperellipticModel.ArcSurgery.ActualFiniteEventTrace
