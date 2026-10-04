import CurveComplexGenusTwo.Topology.ActualFreeBoundarySupportedContactDrop.FreeBoundaryContactDropGeometry
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryQCover
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryRepeatedLift
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundarySweepLifts
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryHalfFromLiftedSides
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.NormalizedReturnAssembly
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.BoundaryReturnExclusion
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.BoundaryGlobalSideSwitch

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies
open RegionalEmbeddedFamily
open CurveComplex.BranchedDoubleCover
open CoherentEndpointMotion.FreeBoundaryNullGeometry

theorem source_actual_original_free_boundary_all_crossing_selects_simple_Q_null_boundary
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (a b : C(Interval, ↥Q)),
      IsEmbedding a → IsEmbedding b →
      (a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B) →
      (∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B ∧ b t ∉ B) →
      (¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            range a ∪ range c) →
      (¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            range b ∪ range c) →
      Disjoint ({a 0, a 1} : Set ↥Q) {b 0, b 1} →
      (range a ∩ range b).Finite →
      (∃ H : AmbientIsotopy ↥Q,
        (∀ t, (fun y => H.map (t, y)) '' B = B) ∧
        H.finalMap '' range a = range b) →
      (range a ∩ range b).Nonempty →
      RegionalAllInteriorContactsCross Q a b →
      Nonempty (NullBigonBoundary B a b) ∨
        Nonempty (NullHalfBigonBoundary B a b) := by
  classical
  intro Q B a b ha hb hends hproper haEssential hbEssential hendsDisjoint hfinite hclass hcontact hcross
  let : ClosedSurface S := Classical.choice hS.2.1
  obtain ⟨top,hSC,hT2,hcov,hsurj,hsep⟩ := actual_Q_proper_arc_separating_cover
    S g hg hS x R hR htarget a ha hends.1 hends.2.1 (fun t ht => (hproper t ht).1)
  let X := Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y
  let : TopologicalSpace X := top
  let : SimplyConnectedSpace X := hSC
  let : T2Space X := hT2
  let p : X → ↥Q := Sigma.fst
  obtain ⟨H,hHB,hHa⟩ := hclass
  obtain ⟨ρ,A,D,W,hρ,hAp,hDp,hW0,hW1,hWemb,hWp,hWB⟩ :=
    free_boundary_ambient_sweep_lifts p hcov hsurj B a b ha hb hends hproper H hHB hHa
  by_cases hrepeat : ∃ (C : C(Interval,X)), (∀ t, p (C t) = a t) ∧
      ∃ l r : Interval, l < r ∧ D l ∈ range C ∧ D r ∈ range C
  · obtain ⟨C,hCp,l,r,hlr,hl,hr⟩ := hrepeat
    exact Or.inl (free_boundary_repeated_lift_gives_null_bigon B p hcov a b ha hb
      hends hproper hendsDisjoint hfinite hcross hsep D hDp C hCp l r hlr hl hr)
  · have hsingle : ∀ C : C(Interval,X), (∀ t, p (C t) = a t) →
        ∀ l r : Interval, D l ∈ range C → D r ∈ range C → l = r := by
      intro C hCp l r hl hr
      rcases lt_trichotomy l r with hlt | he | hgt
      · exact False.elim (hrepeat ⟨C,hCp,l,r,hlt,hl,hr⟩)
      · exact he
      · exact False.elim (hrepeat ⟨C,hCp,r,l,hgt,hr,hl⟩)
    have hseam (t : Interval) (ht : t = 0 ∨ t = 1) : b t ∉ range a := by
      rintro ⟨s,hs⟩
      have hti := (free_boundary_contact_parameters_interior B a b hends hproper
        hendsDisjoint s t hs).2.1
      rcases ht with rfl | rfl
      · exact lt_irrefl _ hti.1
      · exact lt_irrefl _ hti.2
    have hproj (E : C(Interval,X)) (hEp : ∀ t, p (E t) = a t)
        {z : X} (hz : z ∈ range E) : p z ∈ range a := by
      obtain ⟨t,ht⟩ := hz
      exact ⟨t,(hEp t).symm.trans (congrArg p ht)⟩
    have hmarker {z : ↥Q} (hza : z ∈ range a) (hzB : z ∈ B) :
        z ∈ ({a 0,a 1} : Set ↥Q) := by
      obtain ⟨t,rfl⟩ := hza
      by_cases ht0 : t = 0
      · simp [ht0]
      by_cases ht1 : t = 1
      · simp [ht1]
      exact False.elim ((hproper t ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
        lt_of_le_of_ne t.property.2 ht1⟩).1 hzB)
    have hmarkerRange : ({a 0,a 1} : Set ↥Q) ⊆ range a := by
      rintro z (rfl | rfl)
      · exact mem_range_self 0
      · exact mem_range_self 1
    let e : Fin 2 → Interval := fun i => if i = 0 then 0 else 1
    have he (i : Fin 2) : e i = 0 ∨ e i = 1 := by simp only [e]; split <;> simp
    let q : Fin 2 → Interval := fun i => ρ.symm (e i)
    have hq (i : Fin 2) : q i = 0 ∨ q i = 1 := by
      rcases he i with hi | hi <;> rcases hρ with ⟨h0,h1⟩ | ⟨h0,h1⟩
      · left; apply ρ.injective; simp only [q,ρ.apply_symm_apply,hi,h0]
      · right; apply ρ.injective; simp only [q,ρ.apply_symm_apply,hi,h1]
      · right; apply ρ.injective; simp only [q,ρ.apply_symm_apply,hi,h1]
      · left; apply ρ.injective; simp only [q,ρ.apply_symm_apply,hi,h0]
    have hqne : q 0 ≠ q 1 := by
      intro hh
      have hh' := congrArg ρ hh
      simp [q,e] at hh'
    let T : Fin 2 → C(Interval,X) := fun i =>
      ⟨fun t => W (t,q i),W.continuous.comp (continuous_id.prodMk continuous_const)⟩
    let τ : Fin 2 → C(Interval,↥Q) := fun i =>
      ⟨fun t => p (T i t),hcov.continuous.comp (T i).continuous⟩
    have hτ0 (i) : τ i 0 = a (q i) := by
      change p (W (0,q i)) = a (q i)
      rw [hW0,hAp]
    have hτ1 (i) : τ i 1 = b (e i) := by
      change p (W (1,q i)) = b (e i)
      rw [hW1,hDp]
      simp only [q,ρ.apply_symm_apply]
    have hτB (i t) : τ i t ∈ B := (hWB t (q i)).mpr (hq i)
    have hτne (t) : τ 0 t ≠ τ 1 t := by
      have hVi : IsEmbedding (fun s => p (W (t,s))) := by
        obtain ⟨j,hj⟩ := H.homeomorphism_at t
        have hh : (fun s => p (W (t,s))) = j ∘ a :=
          funext fun s => (hWp t s).trans (hj (a s)).symm
        rw [hh]
        exact j.isEmbedding.comp ha
      intro hh
      exact hqne (hVi.injective hh)
    have hτstart (i) : τ i 0 ≠ τ i 1 := by
      intro hh
      rw [hτ0,hτ1] at hh
      have haend : a (q i) ∈ ({a 0,a 1} : Set ↥Q) := by
        rcases hq i with h | h <;> simp [h]
      have hbend : b (e i) ∈ ({b 0,b 1} : Set ↥Q) := by
        rcases he i with h | h <;> simp [h]
      exact Set.disjoint_left.mp hendsDisjoint haend (hh.symm ▸ hbend)
    obtain ⟨β,θ,ℓ,J,hβ,hθ,hθgap,hθne,hℓ,hℓends,hJ,hJ01,hJends,hJB,hJne,hℓne,hnormLift⟩ :=
      source_actual_boundary_track_pair_normalization S g hg hS x R hR htarget τ hτB hτne hτstart
    obtain ⟨L,hLp,hLends⟩ := hnormLift X p hcov T (fun _ _ => rfl)
    have hL0 (i) : L i 0 ∈ range A := by
      refine ⟨q i,?_⟩
      exact (hW0 (q i)).symm.trans (hLends i).1.symm
    have hL1 : L 0 1 = D 0 ∧ L 1 1 = D 1 := by
      constructor
      · exact (hLends 0).2.trans (by
          change W (1,q 0) = D 0
          rw [hW1]
          simp [q,e])
      · exact (hLends 1).2.trans (by
          change W (1,q 1) = D 1
          rw [hW1]
          simp [q,e])
    have hLB (i t) : p (L i t) ∈ B := by
      rw [hLp,hℓ]
      exact (β _).property
    have hfiniteD : {t : Interval | p (D t) ∈ range a}.Finite := by
      simpa only [hDp] using regional_finite_contact_parameters b a hb
        (by simpa only [inter_comm] using hfinite)
    have hfiniteL (i) : {t : Interval | p (L i t) ∈ range a}.Finite := by
      have hf := source_actual_affine_boundary_track_finite_contacts S g hg hS x R hR htarget
        β (θ i 0) (θ i 1) (hθne i) (ℓ i) (hℓ i) {a 0,a 1} (Set.toFinite _)
      apply hf.subset
      intro t ht
      change ℓ i t ∈ ({a 0,a 1} : Set ↥Q)
      rw [← hLp]
      exact hmarker ht (hLB i t)
    have hswitch (E : C(Interval,X)) (hEp : ∀ t, p (E t) = a t) :
        ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range E)ᶜ ∧
          TrackSwitch (L 0) (range E) U V ∧ TrackSwitch D (range E) U V ∧
          TrackSwitch (L 1) (range E) U V := by
      obtain ⟨U,V,hU,hV,hdis,hcover,hfu,hfv⟩ := hsep E hEp
      have hboundary (i) : TrackSwitch (L i) (range E) U V := by
        exact source_actual_affine_boundary_lift_switches_global_sides S g hg hS x R hR htarget
          a ha hends.1 hends.2.1 (fun s hs => (hproper s hs).1) X p hcov E hEp
          U V hU hV hdis hcover hfu hfv β (θ i 0) (θ i 1) (hθne i) (L i)
          (fun t => (hLp i t).trans (hℓ i t))
      refine ⟨U,V,hU,hV,hdis,hcover,hboundary 0,?_,hboundary 1⟩
      intro t ht hDt
      obtain ⟨s,hs⟩ := hDt
      have hab : a s = b t := (hEp s).symm.trans ((congrArg p hs).trans (hDp t))
      have hsI := (free_boundary_contact_parameters_interior B a b hends hproper
        hendsDisjoint s t hab).1
      obtain ⟨C,hC⟩ := hcross s t hsI ht hab
      exact regional_crossing_lift_switches_separating_sides p hcov a b ha E D hEp hDp
        s t hs C hC U V hU hV hdis hcover hfu hfv
    have hno (i) (E : C(Interval,X)) (hEp : ∀ t, p (E t) = a t)
        (l r : Interval) (hlr : l < r) (hl : L i l ∈ range E) (hr : L i r ∈ range E)
        (hgap : ∀ t, l < t → t < r → p (L i t) ∉ range a) : False := by
      have hlm : ℓ i l ∈ ({a 0,a 1} : Set ↥Q) := by
        rw [← hLp]
        exact hmarker (hproj E hEp hl) (hLB i l)
      have hrm : ℓ i r ∈ ({a 0,a 1} : Set ↥Q) := by
        rw [← hLp]
        exact hmarker (hproj E hEp hr) (hLB i r)
      have hgapm : ∀ t, l < t → t < r → ℓ i t ∉ ({a 0,a 1} : Set ↥Q) := by
        intro t hlt htr hm
        apply hgap t hlt htr
        rw [hLp]
        exact hmarkerRange hm
      have ha01 : a 0 ≠ a 1 := fun hh => zero_ne_one (ha.injective hh)
      obtain ⟨hc,_⟩ := source_actual_affine_boundary_track_two_marker_subsegment
        S g hg hS x R hR htarget β (θ i 0) (θ i 1) (hθne i) (ℓ i) (hℓ i)
        (a 0) (a 1) hends.1 hends.2.1 ha01 l r hlr hlm hrm hgapm
      apply simple_boundary_lift_return_contradicts_essentiality S g hg hS Q B a ha
        (fun t ht => (hproper t ht).1) haEssential p hcov.continuous E (L i) hEp (hLB i) l r hl hr
      simpa only [hLp] using hc
    have hsimple (i) (u : Interval) (hu : u < 1) (hua : p (L i u) ∈ range a)
        (hgap : ∀ t, u < t → t ≤ 1 → p (L i t) ∉ range a) :
        IsEmbedding (fun t => p (L i (intervalAffine u 1 t))) := by
      have hc := source_actual_affine_boundary_track_one_marker_subsegment
        S g hg hS x R hR htarget β (θ i 0) (θ i 1) (hθne i) (ℓ i) (hℓ i)
        (ℓ i u) (by rw [← hLp]; exact hLB i u) u 1 hu rfl (by
          intro t hut ht1 heq
          apply hgap t hut ht1
          rw [hLp,heq,← hLp]
          exact hua)
      simpa only [hLp] using hc
    exact Or.inr (normalized_boundary_tracks_give_half_bigon B a b ha hb hends hproper
      (hseam 0 (Or.inl rfl)) (hseam 1 (Or.inr rfl)) hcontact p hcov A D hAp hDp
      hsingle L hL0 hL1 hLB hfiniteD hfiniteL hswitch hno hsimple)

end CoherentEndpointMotion.FreeBoundaryContactRepair
