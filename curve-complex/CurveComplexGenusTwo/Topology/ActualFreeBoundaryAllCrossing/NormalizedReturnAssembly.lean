import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.CleanTripleSelection
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.MixedHalfBoundary

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies FreeBoundaryNullGeometry
open CurveComplex.BranchedDoubleCover

/-- Assemble the exact half-boundary from normalized boundary tracks. Every
geometric premise is supplied by the original-source caller below. -/
theorem normalized_boundary_tracks_give_half_bigon
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (B : Set X) (a b : C(Interval,X)) (ha : IsEmbedding a) (hb : IsEmbedding b)
    (hends : a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B)
    (hproper : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B ∧ b t ∉ B)
    (hseam0 : b 0 ∉ range a) (hseam1 : b 1 ∉ range a)
    (hcontact : (range a ∩ range b).Nonempty)
    (p : Y → X) (hp : IsCoveringMap p)
    (A D : C(Interval,Y)) (hAp : ∀ t, p (A t) = a t) (hDp : ∀ t, p (D t) = b t)
    (hsingle : ∀ E : C(Interval,Y), (∀ t, p (E t) = a t) →
      ∀ l r, D l ∈ range E → D r ∈ range E → l = r)
    (L : Fin 2 → C(Interval,Y))
    (hL0 : ∀ i, L i 0 ∈ range A)
    (hL1 : L 0 1 = D 0 ∧ L 1 1 = D 1)
    (hLB : ∀ i t, p (L i t) ∈ B)
    (hfiniteD : {t : Interval | p (D t) ∈ range a}.Finite)
    (hfiniteL : ∀ i, {t : Interval | p (L i t) ∈ range a}.Finite)
    (hswitch : ∀ E : C(Interval,Y), (∀ t, p (E t) = a t) →
      ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range E)ᶜ ∧
        TrackSwitch (L 0) (range E) U V ∧ TrackSwitch D (range E) U V ∧
        TrackSwitch (L 1) (range E) U V)
    (hno : ∀ i, ∀ E : C(Interval,Y), (∀ t, p (E t) = a t) →
      ∀ l r, l < r → L i l ∈ range E → L i r ∈ range E →
        (∀ t, l < t → t < r → p (L i t) ∉ range a) → False)
    (hsimple : ∀ i u, u < 1 → p (L i u) ∈ range a →
      (∀ t, u < t → t ≤ 1 → p (L i t) ∉ range a) →
        IsEmbedding (fun t => p (L i (intervalAffine u 1 t)))) :
    Nonempty (NullHalfBigonBoundary B a b) := by
  let P : Path (L 0 0) (D 0) := ⟨L 0,rfl,hL1.1⟩
  let Q : Path (D 0) (D 1) := ⟨D,rfl,rfl⟩
  let R : Path (L 1 0) (D 1) := ⟨L 1,rfl,hL1.2⟩
  let Γ := (P.trans Q).trans R.symm
  have hPf : (P ⁻¹' (p ⁻¹' range a)).Finite := hfiniteL 0
  have hQf : (Q ⁻¹' (p ⁻¹' range a)).Finite := hfiniteD
  have hRf : (R ⁻¹' (p ⁻¹' range a)).Finite := hfiniteL 1
  have hΓfinite : {t : Interval | p (Γ t) ∈ range a}.Finite :=
    finite_trans_events (p ⁻¹' range a) (P.trans Q) R.symm
      (finite_trans_events _ P Q hPf hQf) (finite_symm_events _ R hRf)
  have hΓswitch (E : C(Interval,Y)) (hEp : ∀ t, p (E t) = a t) :
      ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range E)ᶜ ∧
        TrackSwitch Γ.toContinuousMap (range E) U V := by
    obtain ⟨U,V,hU,hV,hdis,hcover,hP,hQ,hR⟩ := hswitch E hEp
    have hproj {z : Y} (hz : z ∈ range E) : p z ∈ range a := by
      obtain ⟨t,ht⟩ := hz
      exact ⟨t,(hEp t).symm.trans (congrArg p ht)⟩
    have hb0 : D 0 ∉ range E := fun hh => hseam0 (hDp 0 ▸ hproj hh)
    have hb1 : D 1 ∉ range E := fun hh => hseam1 (hDp 1 ▸ hproj hh)
    exact ⟨U,V,hU,hV,hdis,hcover,trackSwitch_trans _ U V (P.trans Q) R.symm
      (trackSwitch_trans _ U V P Q hP hQ hb0) (trackSwitch_symm _ U V R hR) hb1⟩
  obtain ⟨E,l,r,hEp,hlr,hl,hr,hgap⟩ := free_finite_event_separating_cover_clean_return
    p hp a ha Γ.toContinuousMap hΓfinite hΓswitch A hAp 0 1 zero_lt_one
    (by simpa only [Γ,Path.coe_toContinuousMap,Path.source] using hL0 0)
    (by simpa only [Γ,Path.coe_toContinuousMap,Path.target] using hL0 1)
  have hct : ∃ t : Interval, p (Q t) ∈ range a := by
    obtain ⟨z,hza,t,ht⟩ := hcontact
    exact ⟨t,by change p (D t) ∈ range a; rw [hDp,ht]; exact hza⟩
  have hPa0 : p (D 0) ∉ range a := by rw [hDp]; exact hseam0
  have hPa1 : p (D 1) ∉ range a := by rw [hDp]; exact hseam1
  rcases clean_three_piece_return_is_mixed p a P Q R hPa0 hPa1 hct
    (hno 0) (hno 1) hsingle E hEp l r hlr hl hr hgap with
    ⟨u,v,hu,hv,huE,hvE,hPu,hQv⟩ | ⟨u,v,hu,hv,huE,hvE,hRu,hQv⟩
  · have hq (t : Interval) : p (Q t) = b t := hDp t
    have hpu : p (L 0 u) ∈ range a := by
      obtain ⟨t,ht⟩ := huE
      exact ⟨t,(hEp t).symm.trans (congrArg p ht)⟩
    apply mixed_track_return_gives_null_half_bigon B a b ha hends.1 hends.2.1
      (fun t ht => (hproper t ht).1) p hp.continuous P Q
      (by rw [show (fun t => p (Q t)) = b from funext hq]; exact hb)
      (by rintro _ ⟨t,rfl⟩; exact ⟨t,(hq t).symm⟩)
      (by rw [hq]; exact hends.2.2.1)
      (fun t ht => by rw [hq]; exact (hproper t ht).2)
      (hLB 0) E hEp u v hu hv huE hvE (hsimple 0 u hu hpu hPu) hQv
  · have hpu : p (L 1 u) ∈ range a := by
      obtain ⟨t,ht⟩ := huE
      exact ⟨t,(hEp t).symm.trans (congrArg p ht)⟩
    have hq (t : Interval) : p (Q.symm t) = b (unitInterval.symm t) := hDp _
    have hqs : IsEmbedding (fun t => p (Q.symm t)) := by
      have he : (fun t => p (Q.symm t)) = b ∘ unitInterval.symm := funext hq
      rw [he]
      exact hb.comp unitInterval.symmHomeomorph.isEmbedding
    apply mixed_track_return_gives_null_half_bigon B a b ha hends.1 hends.2.1
      (fun t ht => (hproper t ht).1) p hp.continuous R Q.symm hqs
      (by rintro _ ⟨t,rfl⟩; exact ⟨unitInterval.symm t,(hq t).symm⟩)
      (by simpa only [hq,unitInterval.symm_zero] using hends.2.2.2)
      (fun t ht => ?_) (hLB 1) E hEp u v hu hv huE hvE
      (hsimple 1 u hu hpu hRu) hQv
    rw [hq]
    apply (hproper _ ?_).2
    constructor
    · simpa only [unitInterval.symm_one] using (unitInterval.symm_lt_symm.mpr ht.2)
    · simpa only [unitInterval.symm_zero] using (unitInterval.symm_lt_symm.mpr ht.1)

end CoherentEndpointMotion.FreeBoundaryContactRepair
