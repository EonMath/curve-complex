import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.ConcatenatePinchedBands
import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.ConcatenatePinchedBandsTwoThirds

namespace CurveComplex
open Set Topology
variable {X : Type} [TopologicalSpace X]

/-- The collapsed base fiber consists of exactly the two angular ends. -/
theorem pinched_band_base_fiber
    (base : X) (N : C(Interval × Interval,X))
    (hends : ∀ w, N (0,w) = base ∧ N (1,w) = base)
    (hinj : ∀ s w s' w', N (s,w) = N (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (s w : Interval) : N (s,w) = base ↔ s = 0 ∨ s = 1 := by
  constructor
  · intro he
    rcases hinj s w 0 0 (he.trans (hends 0).1.symm) with he | he
    · exact Or.inl he.1
    · exact he.1
  · rintro (rfl | rfl)
    · exact (hends w).1
    · exact (hends w).2

private theorem strict_of_not_angular_end (s : Interval) (hs : ¬ (s = 0 ∨ s = 1)) :
    s ∈ Ioo (0 : Interval) 1 := by
  constructor
  · apply lt_of_le_of_ne s.property.1
    intro he
    exact hs (Or.inl (Subtype.ext he.symm))
  · apply lt_of_le_of_ne s.property.2
    intro he
    exact hs (Or.inr (Subtype.ext he))

/-- An exterior half-collar intersects the old strip only on its prescribed
boundary, with the base fiber retained in the statement. -/
theorem exterior_half_collar_strip_collision
    (base : X) (G C : C(Interval × Interval,X)) (edge : Interval) (U : Set X)
    (hGend : ∀ w, G (0,w) = base ∧ G (1,w) = base)
    (hCend : ∀ w, C (0,w) = base ∧ C (1,w) = base)
    (hGinj : ∀ s w s' w', G (s,w) = G (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (hCinj : ∀ s w s' w', C (s,w) = C (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (hC0 : ∀ s, C (s,0) = G (s,edge))
    (hinside : ∀ s ∈ Ioo (0 : Interval) 1, ∀ w, 0 < w → C (s,w) ∈ U)
    (hGavoid : ∀ s w, G (s,w) ∉ U) :
    ∀ s w s' w', C (s,w) = G (s',w') →
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)) ∨
      (s = s' ∧ w = 0 ∧ w' = edge) := by
  intro s w s' w' he
  by_cases hs : s = 0 ∨ s = 1
  · exact Or.inl ⟨hs,(pinched_band_base_fiber base G hGend hGinj s' w').mp
      (he.symm.trans ((pinched_band_base_fiber base C hCend hCinj s w).mpr hs))⟩
  · have hw : w = 0 := by
      by_contra hw
      have hwpos : 0 < w := lt_of_le_of_ne w.property.1 (Ne.symm hw)
      exact hGavoid s' w' (he ▸ hinside s (strict_of_not_angular_end s hs) w hwpos)
    rw [hw,hC0] at he
    rcases hGinj s edge s' w' he with h | h
    · exact Or.inr ⟨h.1,hw,h.2.symm⟩
    · exact False.elim (hs h.1)

/-- Glue the old strip to two disjoint exterior half-collars. The old boundary
loops occur at literal widths one third and two thirds in the resulting band. -/
theorem glue_exterior_half_collars
    (base : X) (G L R : C(Interval × Interval,X)) (U V : Set X)
    (hGend : ∀ w, G (0,w) = base ∧ G (1,w) = base)
    (hLend : ∀ w, L (0,w) = base ∧ L (1,w) = base)
    (hRend : ∀ w, R (0,w) = base ∧ R (1,w) = base)
    (hGinj : ∀ s w s' w', G (s,w) = G (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (hLinj : ∀ s w s' w', L (s,w) = L (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (hRinj : ∀ s w s' w', R (s,w) = R (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (hL0 : ∀ s, L (s,0) = G (s,0)) (hR0 : ∀ s, R (s,0) = G (s,1))
    (hLU : ∀ s ∈ Ioo (0 : Interval) 1, ∀ w, 0 < w → L (s,w) ∈ U)
    (hRV : ∀ s ∈ Ioo (0 : Interval) 1, ∀ w, 0 < w → R (s,w) ∈ V)
    (hUV : Disjoint U V) (hGU : ∀ s w, G (s,w) ∉ U)
    (hGV : ∀ s w, G (s,w) ∉ V) :
    ∃ N : C(Interval × Interval,X),
      (∀ w, N (0,w) = base ∧ N (1,w) = base) ∧
      (∀ s w s' w', N (s,w) = N (s',w') →
        (s = s' ∧ w = w') ∨
        ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1))) ∧
      (∀ s, N (s,⟨1/3,by norm_num⟩) = G (s,0)) ∧
      (∀ s, N (s,⟨2/3,by norm_num⟩) = G (s,1)) ∧
      range N ⊆ range L ∪ range G ∪ range R := by
  have hLG := exterior_half_collar_strip_collision base G L 0 U hGend hLend hGinj hLinj hL0 hLU hGU
  have hRG := exterior_half_collar_strip_collision base G R 1 V hGend hRend hGinj hRinj hR0 hRV hGV
  have hLR : ∀ s w s' w', L (s,w) = R (s',w') →
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)) := by
    intro s w s' w' he
    by_cases hs : s = 0 ∨ s = 1
    · exact ⟨hs,(pinched_band_base_fiber base R hRend hRinj s' w').mp
        (he.symm.trans ((pinched_band_base_fiber base L hLend hLinj s w).mpr hs))⟩
    · have hs' : ¬ (s' = 0 ∨ s' = 1) := by
        intro hs'
        exact hs ((pinched_band_base_fiber base L hLend hLinj s w).mp
          (he.trans ((pinched_band_base_fiber base R hRend hRinj s' w').mpr hs')))
      by_cases hw : w = 0
      · rw [hw,hL0] at he
        rcases hRG s' w' s 0 he.symm with hh | hh
        · exact False.elim (hs hh.2)
        · have hew := congrArg Subtype.val hh.2.2
          norm_num at hew
      · by_cases hw' : w' = 0
        · rw [hw',hR0] at he
          rcases hLG s w s' 1 he with hh | hh
          · exact False.elim (hs hh.1)
          · have hew := congrArg Subtype.val hh.2.2
            norm_num at hew
        · have hp : 0 < w := lt_of_le_of_ne w.property.1 (Ne.symm hw)
          have hp' : 0 < w' := lt_of_le_of_ne w'.property.1 (Ne.symm hw')
          exact False.elim (Set.disjoint_left.mp hUV (hLU s (strict_of_not_angular_end s hs) w hp)
            (he.symm ▸ hRV s' (strict_of_not_angular_end s' hs') w' hp'))
  let A : C(Interval × Interval,X) :=
    ⟨fun z => L (z.1,unitInterval.symm z.2),L.continuous.comp (by fun_prop)⟩
  have hAend : ∀ w, A (0,w) = base ∧ A (1,w) = base := fun w => hLend _
  have hAinj : ∀ s w s' w', A (s,w) = A (s',w') →
      (s = s' ∧ w = w') ∨ ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)) := by
    intro s w s' w' he
    rcases hLinj _ _ _ _ he with hh | hh
    · exact Or.inl ⟨hh.1,unitInterval.symm_bijective.injective hh.2⟩
    · exact Or.inr hh
  have hA1 : ∀ s, A (s,1) = G (s,0) := by
    intro s
    change L (s,unitInterval.symm 1) = _
    simpa only [unitInterval.symm_one] using hL0 s
  have hAG : ∀ s w s' w', A (s,w) = G (s',w') →
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)) ∨ (s = s' ∧ w = 1 ∧ w' = 0) := by
    intro s w s' w' he
    rcases hLG s (unitInterval.symm w) s' w' he with hh | hh
    · exact Or.inl hh
    · exact Or.inr ⟨hh.1,by
        have hv := congrArg unitInterval.symm hh.2.1
        simpa using hv,hh.2.2⟩
  obtain ⟨D,hD0,hD1,hDhalf,hDend,hDinj,hDrange⟩ :=
    concatenate_pinched_bands base A G hAend hGend hAinj hGinj hA1 hAG
  have hDR : ∀ s w s' w', D (s,w) = R (s',w') →
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)) ∨ (s = s' ∧ w = 1 ∧ w' = 0) := by
    intro s w s' w' he
    by_cases hs : s = 0 ∨ s = 1
    · exact Or.inl ⟨hs,(pinched_band_base_fiber base R hRend hRinj s' w').mp
        (he.symm.trans ((pinched_band_base_fiber base D hDend hDinj s w).mpr hs))⟩
    · have hDne : D (s,w) ≠ base := fun hh => hs ((pinched_band_base_fiber base D hDend hDinj s w).mp hh)
      rcases hDrange (Set.mem_range_self (s,w)) with ⟨⟨u,v⟩,huv⟩ | ⟨⟨u,v⟩,huv⟩
      · have hends := hLR u (unitInterval.symm v) s' w' (huv.trans he)
        have hbaseD : D (s,w) = base := huv.symm.trans
          ((pinched_band_base_fiber base L hLend hLinj u (unitInterval.symm v)).mpr hends.1)
        exact False.elim (hDne hbaseD)
      · rcases hRG s' w' u v (he.symm.trans huv.symm) with hh | hh
        · have hbaseD : D (s,w) = base := huv.symm.trans
            ((pinched_band_base_fiber base G hGend hGinj u v).mpr hh.2)
          exact False.elim (hDne hbaseD)
        · have hseameq : D (s,w) = D (s',1) :=
            he.trans ((congrArg (fun v => R (s',v)) hh.2.1).trans ((hR0 s').trans (hD1 s').symm))
          rcases hDinj s w s' 1 hseameq with hd | hd
          · exact Or.inr ⟨hd.1,hd.2,hh.2.1⟩
          · exact False.elim (hs hd.1)
  obtain ⟨N,hN0,hN1,hNtwo,hNone,hNend,hNinj,hNrange⟩ :=
    concatenate_pinched_bands_two_thirds base D R hDend hRend hDinj hRinj
      (fun s => (hD1 s).trans (hR0 s).symm) hDR
  refine ⟨N,hNend,hNinj,?_,?_,?_⟩
  · intro s
    exact (hNone s).trans ((hDhalf s).trans (hA1 s))
  · intro s
    exact (hNtwo s).trans (hD1 s)
  · intro x hx
    rcases hNrange hx with hd | hr
    · rcases hDrange hd with ⟨⟨s,w⟩,he⟩ | hg
      · exact Or.inl (Or.inl ⟨(s,unitInterval.symm w),he⟩)
      · exact Or.inl (Or.inr hg)
    · exact Or.inr hr

end CurveComplex
