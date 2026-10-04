import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.PinchedCollarMotion

namespace CurveComplex
open Set Topology

/-- The terminal consumer needs the upper original loop sent to the lower one.
Reverse the transverse collar parameter while retaining all obstacle fixation. -/
theorem pinched_collared_band_reverse_motion_fixes_obstacle
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (P : Set X) (base : X) (N : C(Interval × Interval,X))
    (hends : ∀ w, N (0,w) = base ∧ N (1,w) = base)
    (hinj : ∀ s w s' w', N (s,w) = N (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (hopen : IsOpen (N '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.Ioo (0 : Interval) 1)))
    (havoid : ∀ s w, N (s,w) ≠ base → N (s,w) ∉ P) :
    ∃ H : AmbientIsotopy X,
      (∀ t x, x ∈ P → H.map (t,x) = x) ∧
      H.finalMap '' Set.range (fun s => N (s,⟨2/3,by norm_num⟩)) =
        Set.range (fun s => N (s,⟨1/3,by norm_num⟩)) := by
  let R : C(Interval × Interval,X) :=
    ⟨fun z => N (z.1,unitInterval.symm z.2),
      N.continuous.comp (continuous_fst.prodMk
        (unitInterval.continuous_symm.comp continuous_snd))⟩
  have hRend (w) : R (0,w) = base ∧ R (1,w) = base := hends _
  have hRinj (s w s' w') (he : R (s,w) = R (s',w')) :
      (s = s' ∧ w = w') ∨ ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)) := by
    rcases hinj _ _ _ _ he with h | h
    · exact Or.inl ⟨h.1,unitInterval.symm_bijective.injective h.2⟩
    · exact Or.inr h
  have hs (w : Interval) (hw : w ∈ Set.Ioo (0 : Interval) 1) :
      unitInterval.symm w ∈ Set.Ioo (0 : Interval) 1 := by
    change (0 : ℝ) < 1-(w : ℝ) ∧ 1-(w : ℝ) < 1
    have h0 : (0 : ℝ) < (w : ℝ) := hw.1
    have h1 : (w : ℝ) < 1 := hw.2
    constructor <;> linarith
  have heq : R '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.Ioo (0 : Interval) 1) =
      N '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.Ioo (0 : Interval) 1) := by
    ext x
    constructor
    · rintro ⟨⟨s,w⟩,hw,he⟩
      exact ⟨(s,unitInterval.symm w),⟨hw.1,hs w hw.2⟩,he⟩
    · rintro ⟨⟨s,w⟩,hw,he⟩
      refine ⟨(s,unitInterval.symm w),⟨hw.1,hs w hw.2⟩,?_⟩
      change N (s,unitInterval.symm (unitInterval.symm w)) = x
      rw [unitInterval.symm_symm]
      exact he
  have hRopen : IsOpen (R '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.Ioo (0 : Interval) 1)) :=
    heq.symm ▸ hopen
  obtain ⟨H,hfix,hmove⟩ := pinched_collared_band_motion_fixes_obstacle P base R
    hRend hRinj hRopen (fun s w hne => havoid s _ hne)
  refine ⟨H,hfix,?_⟩
  have hthird : unitInterval.symm (⟨1/3,by norm_num⟩ : Interval) = ⟨2/3,by norm_num⟩ :=
    Subtype.ext (by norm_num [unitInterval.symm])
  have htwothird : unitInterval.symm (⟨2/3,by norm_num⟩ : Interval) = ⟨1/3,by norm_num⟩ :=
    Subtype.ext (by norm_num [unitInterval.symm])
  have hRthird : (fun s => R (s,⟨1/3,by norm_num⟩)) =
      (fun s => N (s,⟨2/3,by norm_num⟩)) := by
    funext s
    change N (s,unitInterval.symm _) = _
    rw [hthird]
  have hRtwothird : (fun s => R (s,⟨2/3,by norm_num⟩)) =
      (fun s => N (s,⟨1/3,by norm_num⟩)) := by
    funext s
    change N (s,unitInterval.symm _) = _
    rw [htwothird]
  simpa only [hRthird,hRtwothird] using hmove

end CurveComplex
