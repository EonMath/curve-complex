import CurveComplexGenusTwo.Topology.ActualRegionalCompatibleReturn.RegionalReturnCleanupScaffold
import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalSeparatingCoverPROVED
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundarySweepLifts
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryRepeatedLift
import CurveComplexGenusTwo.Topology.ActualRegionalBoundaryTracks.RegionalEndpointTrackNormalization
import CurveComplexGenusTwo.Topology.ActualRegionalBoundaryTracks.RegionalAffineBoundaryContacts
import CurveComplexGenusTwo.Topology.ActualRegionalBoundaryTracks.RegionalBoundaryGlobalSideSwitch
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.CleanTripleSelection
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.MixedHalfBoundary
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.BoundaryReturnExclusion

open CurveComplex Set Topology RegionalTotalDecrease
open CoherentEndpointMotion.FreeBoundaryContactRepair
open CoherentEndpointMotion.FreeBoundaryNullGeometry
open CurveComplex.BranchedDoubleCover
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
universe v
private noncomputable local instance regionalCompatibleNullProgressDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- PLAN B3: different compatible classes yield a null ordinary or half boundary in the SAME F, via an actual disjoint comparison. -/
theorem regional_compatible_crossing_pair_has_F_null_boundary
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
      isRelLowerSet_faces := by
        intro τ hτ
        refine ⟨hτ.1,?_⟩
        intro μ hμτ hne
        obtain ⟨rep,hclass,hd⟩ := hτ.2
        refine ⟨hne,(fun u => rep ⟨u.val,hμτ u.property⟩),?_,?_⟩
        · intro u
          exact hclass ⟨u.val,hμτ u.property⟩
        · intro u w huw
          apply hd
          intro he
          exact huw (Subtype.ext (congrArg (fun z : ↥τ => z.val) he))
      singleton_mem := by
        intro u
        obtain ⟨a,ha⟩ := Quot.exists_rep u
        refine ⟨Finset.singleton_nonempty u,(fun _ => a),?_,?_⟩
        · intro z
          exact ha.trans (Finset.mem_singleton.mp z.property).symm
        · intro z w hzw
          exact False.elim (hzw (Subtype.ext
            ((Finset.mem_singleton.mp z.property).trans (Finset.mem_singleton.mp w.property).symm))) }
    ∀ a b bStar : IntrinsicEssentialArc,
      (a.val.val 0 ≠ b.val.val 0 ∧ a.val.val 0 ≠ b.val.val 1 ∧
        a.val.val 1 ≠ b.val.val 0 ∧ a.val.val 1 ≠ b.val.val 1) →
      (range a.val.val ∩ range b.val.val).Finite →
      0 < (range a.val.val ∩ range b.val.val).ncard →
      RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F a.val.val b.val.val →
      ∀ H : AmbientIsotopy ↥F,
        ClassMovie {y | y.val ∈ boundaryCircle} {y | y.val ∈ frontier F}
          b.val.val bStar.val.val H →
        Disjoint (range a.val.val) (range bStar.val.val) →
        Nonempty (NullBigonBoundary {y | y.val ∈ boundaryCircle} a.val.val b.val.val) ∨
          Nonempty (NullHalfBigonBoundary {y | y.val ∈ boundaryCircle} a.val.val b.val.val) := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  dsimp only
  intro a b bStar hends hfinite hpositive hcross H hmovie hterminal
  let B : Set ↥F := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
  have hBfront : B ⊆ {y : ↥F | y.val ∈ frontier F} := by
    intro y hy
    rw [hfrontier]
    exact Or.inl hy
  have hproper : ∀ t ∈ Ioo (0 : Interval) 1,
      a.val.val t ∉ B ∧ b.val.val t ∉ B := by
    intro t ht
    exact ⟨fun h => a.val.property.2.2.2 t ht (hBfront h),
      fun h => b.val.property.2.2.2 t ht (hBfront h)⟩
  have hbdends : a.val.val 0 ∈ B ∧ a.val.val 1 ∈ B ∧
      b.val.val 0 ∈ B ∧ b.val.val 1 ∈ B :=
    ⟨a.val.property.2.1,a.val.property.2.2.1,b.val.property.2.1,b.val.property.2.2.1⟩
  have hdisends : Disjoint ({a.val.val 0,a.val.val 1} : Set ↥F)
      {b.val.val 0,b.val.val 1} := by
    simp only [Set.disjoint_insert_left,Set.disjoint_singleton_left,
      Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    exact ⟨⟨hends.1,hends.2.1⟩,hends.2.2⟩
  obtain ⟨top,hSC,hT2,hcov,hsurj,hsep⟩ := source_actual_regional_proper_arc_separating_universal_cover
    S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular J c hdisjoint
    hbaseDisjoint hfrontier a.val.val a.val.property.1 a.val.property.2.1 a.val.property.2.2.1
    a.val.property.2.2.2
  let X := Σ y : ↥F, Path.Homotopic.Quotient (a.val.val 0) y
  let : TopologicalSpace X := top
  let : SimplyConnectedSpace X := hSC
  let : T2Space X := hT2
  let p : X → ↥F := Sigma.fst
  have hcomparisonEnds : b.val.val 0 ∈ B ∧ b.val.val 1 ∈ B ∧
      bStar.val.val 0 ∈ B ∧ bStar.val.val 1 ∈ B :=
    ⟨b.val.property.2.1,b.val.property.2.2.1,bStar.val.property.2.1,bStar.val.property.2.2.1⟩
  have hcomparisonProper : ∀ t ∈ Ioo (0 : Interval) 1,
      b.val.val t ∉ B ∧ bStar.val.val t ∉ B := by
    intro t ht
    exact ⟨fun h => b.val.property.2.2.2 t ht (hBfront h),
      fun h => bStar.val.property.2.2.2 t ht (hBfront h)⟩
  obtain ⟨ρ,D,E,W,hρ,hDp,hEp,hW0,hW1,hWemb,hWp,hWB⟩ :=
    free_boundary_ambient_sweep_lifts p hcov hsurj B b.val.val bStar.val.val
      b.val.property.1 bStar.val.property.1 hcomparisonEnds hcomparisonProper H hmovie.1 hmovie.2.2
  by_cases hrepeat : ∃ (A : C(Interval,X)), (∀ t, p (A t) = a.val.val t) ∧
      ∃ l r : Interval, l < r ∧ D l ∈ range A ∧ D r ∈ range A
  · obtain ⟨A,hAp,l,r,hlr,hl,hr⟩ := hrepeat
    exact Or.inl (free_boundary_repeated_lift_gives_null_bigon B p hcov
      a.val.val b.val.val a.val.property.1 b.val.property.1 hbdends hproper hdisends
      hfinite hcross hsep D hDp A hAp l r hlr hl hr)
  · have hsingle : ∀ A : C(Interval,X), (∀ t, p (A t) = a.val.val t) →
        ∀ l r, D l ∈ range A → D r ∈ range A → l = r := by
      intro A hAp l r hl hr
      rcases lt_trichotomy l r with hlt | he | hgt
      · exact False.elim (hrepeat ⟨A,hAp,l,r,hlt,hl,hr⟩)
      · exact he
      · exact False.elim (hrepeat ⟨A,hAp,r,l,hgt,hr,hl⟩)
    let τ : Fin 2 → C(Interval,↥F) := fun i =>
      ⟨fun t => H.map (t,b.val.val (endpoint i)),
        H.map.continuous.comp (continuous_id.prodMk continuous_const)⟩
    obtain ⟨β,θ,ℓ,JH,L,hβ,hθ,hθgap,hℓ,hℓend,hJ,hJ01,hJend,hJB,hJne,hℓne,hLp,hLend,hzero⟩ :=
      regional_actual_comparison_endpoint_tracks_normalization S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
        b bStar H hmovie X p hcov ρ D E W hρ hDp hEp hW0 hW1 hWemb hWp hWB τ (fun _ _ => rfl)
    have hLaff (i : Fin 2) (t : Interval) : p (L i t) =
        (β (Circle.exp ((1-t.val)*θ i 0+t.val*θ i 1))).val := (hLp i t).trans (hℓ i t)
    obtain ⟨Γ₀,A₀,l₀,r₀,hΓ₀,hA₀,hlr₀,hl₀,hr₀⟩ :=
      regional_disjoint_comparison_sweep_has_lifted_return S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
        a b bStar hends hfinite hpositive hcross H hmovie hterminal X p hcov hsurj hsep
        ρ D E W hρ hDp hEp hW0 hW1 hWemb hWp hWB β θ L hθ hθgap hLaff hLend
    have hseam (i : Fin 2) : b.val.val (endpoint i) ∉ range a.val.val := by
      rintro ⟨t,ht⟩
      have hst := free_boundary_contact_parameters_interior B a.val.val b.val.val
        hbdends hproper hdisends t (endpoint i) ht
      fin_cases i <;> norm_num [endpoint] at hst
    have hseam0 : b.val.val 0 ∉ range a.val.val := by simpa [endpoint] using hseam 0
    have hseam1 : b.val.val 1 ∉ range a.val.val := by simpa [endpoint] using hseam 1
    have hmarker {z : ↥F} (hz : z ∈ B) :
        z ∈ range a.val.val ↔ z ∈ ({a.val.val 0,a.val.val 1} : Set ↥F) := by
      constructor
      · rintro ⟨t,rfl⟩
        by_cases ht0 : t = 0
        · simp [ht0]
        by_cases ht1 : t = 1
        · simp [ht1]
        exact False.elim ((hproper t ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
          lt_of_le_of_ne t.property.2 ht1⟩).1 hz)
      · intro hz
        rcases hz with hz | hz
        · exact ⟨0,hz.symm⟩
        · exact ⟨1,hz.symm⟩
    let T : Fin 2 → C(Interval,X) := fun i =>
      ⟨fun t => L i (unitInterval.symm t),(L i).continuous.comp unitInterval.continuous_symm⟩
    let k : Fin 2 → C(Interval,↥F) := fun i => ⟨fun t => p (T i t),hcov.continuous.comp (T i).continuous⟩
    have hk (i : Fin 2) (t : Interval) : k i t =
        (β (Circle.exp ((1-t.val)*θ i 1+t.val*θ i 0))).val := by
      change p (L i (unitInterval.symm t)) = _
      rw [hLaff]
      congr 3
      change (1-(1-t.val))*θ i 0+(1-t.val)*θ i 1 = _
      ring
    have hkB (i : Fin 2) (t : Interval) : k i t ∈ B := by
      rw [hk]; exact (β _).property
    have hz (i : Fin 2) (he : θ i 1 = θ i 0) (t : Interval) :
        k i t = b.val.val (endpoint i) := by
      exact (hLp i (unitInterval.symm t)).trans (hzero i he.symm _)
    have hslope (i : Fin 2) (t : Interval) (ht : k i t ∈ range a.val.val) : θ i 1 ≠ θ i 0 := by
      intro he
      exact hseam i (hz i he t ▸ ht)
    have hfiniteL (i : Fin 2) : {t : Interval | p (T i t) ∈ range a.val.val}.Finite := by
      by_cases he : θ i 1 = θ i 0
      · have heq : {t : Interval | p (T i t) ∈ range a.val.val} = ∅ := by
          ext t
          simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
          exact fun ht => hslope i t ht he
        rw [heq]; exact Set.finite_empty
      · have hf := regional_affine_boundary_nonzero_slope_finite_contacts S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
          β (θ i 1) (θ i 0) he (k i) (hk i) {a.val.val 0,a.val.val 1} (Set.toFinite _)
        exact hf.subset (fun t ht => (hmarker (hkB i t)).mp ht)
    have hfiniteD : {t : Interval | p (D t) ∈ range a.val.val}.Finite := by
      have hf := RegionalEmbeddedFamily.regional_finite_contact_parameters b.val.val a.val.val
        b.val.property.1 (by simpa only [inter_comm] using hfinite)
      simpa only [hDp] using hf
    have hno : ∀ i, ∀ A : C(Interval,X), (∀ t, p (A t) = a.val.val t) →
        ∀ l r, l < r → T i l ∈ range A → T i r ∈ range A →
          (∀ t, l < t → t < r → p (T i t) ∉ range a.val.val) → False := by
      intro i A hAp l r hlr hl hr hgap
      have hproj {z : X} (hz : z ∈ range A) : p z ∈ range a.val.val := by
        obtain ⟨t,ht⟩ := hz
        exact ⟨t,(hAp t).symm.trans (congrArg p ht)⟩
      have hlm := (hmarker (hkB i l)).mp (hproj hl)
      have hrm := (hmarker (hkB i r)).mp (hproj hr)
      have hseg := (regional_affine_boundary_two_marker_subsegment S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
        β (θ i 1) (θ i 0) (hslope i l (hproj hl)) (k i) (hk i)
        (a.val.val 0) (a.val.val 1) a.val.property.2.1 a.val.property.2.2.1
        (fun he => zero_ne_one (a.val.property.1.injective he)) l r hlr hlm hrm
        (fun t hlt htr hh => hgap t hlt htr ((hmarker (hkB i t)).mpr hh))).1
      exact simple_boundary_lift_return_contradicts_essentiality S g hg hS F B
        a.val.val a.val.property.1 (fun t ht => (hproper t ht).1) a.property
        p hcov.continuous A (T i) hAp (hkB i) l r hl hr hseg
    have hsimple : ∀ i u, u < 1 → p (T i u) ∈ range a.val.val →
        (∀ t, u < t → t ≤ 1 → p (T i t) ∉ range a.val.val) →
          IsEmbedding (fun t => p (T i (intervalAffine u 1 t))) := by
      intro i u hu hum hclear
      exact regional_affine_boundary_one_marker_subsegment S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
        β (θ i 1) (θ i 0) (hslope i u hum) (k i) (hk i) (k i u) (hkB i u)
        u 1 hu rfl (fun t hut ht1 he => by
          apply hclear t hut ht1
          change p (T i t) ∈ range a.val.val
          have he' : p (T i t) = p (T i u) := by
            exact he
          rw [he']
          exact hum)
    have hswitch : ∀ A : C(Interval,X), (∀ t, p (A t) = a.val.val t) →
        ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range A)ᶜ ∧
          TrackSwitch (T 0) (range A) U V ∧ TrackSwitch D (range A) U V ∧
          TrackSwitch (T 1) (range A) U V := by
      intro A hAp
      obtain ⟨U,V,hU,hV,hdis,hcover,hfrontU,hfrontV⟩ := hsep A hAp
      have hLT (i : Fin 2) : TrackSwitch (T i) (range A) U V := by
        intro t ht hAt
        have hproj : k i t ∈ range a.val.val := by
          obtain ⟨s,hs⟩ := hAt
          exact ⟨s,(hAp s).symm.trans (congrArg p hs)⟩
        exact regional_affine_boundary_lift_switches_global_sides S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
          a X p hcov A hAp U V hU hV hdis hcover hfrontU hfrontV β
          (θ i 1) (θ i 0) (hslope i t hproj) (T i) (hk i) t ht hAt
      refine ⟨U,V,hU,hV,hdis,hcover,hLT 0,?_,hLT 1⟩
      intro t ht hAt
      obtain ⟨s,hs⟩ := hAt
      have hst : a.val.val s = b.val.val t := (hAp s).symm.trans ((congrArg p hs).trans (hDp t))
      have hsI := (free_boundary_contact_parameters_interior B a.val.val b.val.val
        hbdends hproper hdisends s t hst).1
      obtain ⟨C,hC⟩ := hcross s t hsI ht hst
      exact RegionalEmbeddedFamily.regional_crossing_lift_switches_separating_sides
        p hcov a.val.val b.val.val a.val.property.1 A D hAp hDp s t hs C hC
        U V hU hV hdis hcover hfrontU hfrontV
    have hTend : T 0 1 = D 0 ∧ T 1 1 = D 1 := by
      constructor
      · simpa [T,endpoint] using (hLend 0).1
      · simpa [T,endpoint] using (hLend 1).1
    let P : Path (T 0 0) (D 0) := ⟨T 0,rfl,hTend.1⟩
    let Q : Path (D 0) (D 1) := ⟨D,rfl,rfl⟩
    let R' : Path (T 1 0) (D 1) := ⟨T 1,rfl,hTend.2⟩
    let Γ := (P.trans Q).trans R'.symm
    let η : Interval → Interval := fun t =>
      ⟨if t.val ≤ 2/3 then 3*t.val/4 else (3*t.val-1)/2,by
        split_ifs with ht <;> constructor <;> linarith [t.property.1,t.property.2]⟩
    have hηmono : StrictMono η := by
      intro u v huv
      change u.val < v.val at huv
      change (if u.val ≤ 2/3 then 3*u.val/4 else (3*u.val-1)/2) <
        (if v.val ≤ 2/3 then 3*v.val/4 else (3*v.val-1)/2)
      split_ifs <;> linarith
    have hηΓ (t : Interval) : Γ (η t) = Γ₀ t := by
      rw [hΓ₀]
      by_cases ht1 : t.val ≤ 1/3
      · let z : Interval := projIcc 0 1 (by norm_num) (1-3*t.val)
        have hz : z.val = 1-3*t.val := by
          simp only [z,coe_projIcc]
          rw [min_eq_right (by linarith [t.property.1]),max_eq_right (by linarith)]
        have he : η t = halfClock (halfClock (unitInterval.symm z)) := by
          apply Subtype.ext
          simp only [η,halfClock,unitInterval.symm,ite_eq_left (show t.val ≤ 2/3 by linarith)]
          rw [hz]
          ring
        rw [he]
        change ((P.trans Q).trans R'.symm) _ = _
        rw [trans_halfClock,trans_halfClock]
        change L 0 (unitInterval.symm (unitInterval.symm z)) = comparisonReturn L D t
        rw [unitInterval.symm_symm]
        simp only [comparisonReturn,ite_eq_left ht1]
        rfl
      · by_cases ht2 : t.val ≤ 2/3
        · let z : Interval := projIcc 0 1 (by norm_num) (3*t.val-1)
          have hz : z.val = 3*t.val-1 := by
            simp only [z,coe_projIcc]
            rw [min_eq_right (by linarith),max_eq_right (by linarith)]
          have he : η t = halfClock (laterClock z) := by
            apply Subtype.ext
            simp only [η,halfClock,laterClock,ite_eq_left ht2]
            rw [hz]
            ring
          rw [he]
          change ((P.trans Q).trans R'.symm) _ = _
          rw [trans_halfClock,trans_laterClock]
          change D z = comparisonReturn L D t
          simp only [comparisonReturn,ite_eq_right ht1,ite_eq_left ht2]
          rfl
        · let z : Interval := projIcc 0 1 (by norm_num) (3*t.val-2)
          have hz : z.val = 3*t.val-2 := by
            simp only [z,coe_projIcc]
            rw [min_eq_right (by linarith [t.property.2]),max_eq_right (by linarith)]
          have he : η t = laterClock z := by
            apply Subtype.ext
            simp only [η,laterClock,ite_eq_right ht2]
            rw [hz]
            ring
          rw [he]
          change ((P.trans Q).trans R'.symm) _ = _
          rw [trans_laterClock]
          change L 1 (unitInterval.symm (unitInterval.symm z)) = comparisonReturn L D t
          rw [unitInterval.symm_symm]
          simp only [comparisonReturn,ite_eq_right ht1,ite_eq_right ht2]
          rfl
    have hPf : (P ⁻¹' (p ⁻¹' range a.val.val)).Finite := hfiniteL 0
    have hQf : (Q ⁻¹' (p ⁻¹' range a.val.val)).Finite := hfiniteD
    have hRf : (R' ⁻¹' (p ⁻¹' range a.val.val)).Finite := hfiniteL 1
    have hΓfinite : {t : Interval | p (Γ t) ∈ range a.val.val}.Finite :=
      finite_trans_events (p ⁻¹' range a.val.val) (P.trans Q) R'.symm
        (finite_trans_events _ P Q hPf hQf) (finite_symm_events _ R' hRf)
    have hΓswitch (A : C(Interval,X)) (hAp : ∀ t, p (A t) = a.val.val t) :
        ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range A)ᶜ ∧
          TrackSwitch Γ.toContinuousMap (range A) U V := by
      obtain ⟨U,V,hU,hV,hdis,hcover,hP,hQ,hR⟩ := hswitch A hAp
      have hproj {z : X} (hz : z ∈ range A) : p z ∈ range a.val.val := by
        obtain ⟨t,ht⟩ := hz
        exact ⟨t,(hAp t).symm.trans (congrArg p ht)⟩
      have hb0 : D 0 ∉ range A := fun hh => hseam0 (hDp 0 ▸ hproj hh)
      have hb1 : D 1 ∉ range A := fun hh => hseam1 (hDp 1 ▸ hproj hh)
      exact ⟨U,V,hU,hV,hdis,hcover,trackSwitch_trans _ U V (P.trans Q) R'.symm
        (trackSwitch_trans _ U V P Q hP hQ hb0) (trackSwitch_symm _ U V R' hR) hb1⟩
    obtain ⟨E,l,r,hEp,hlr,hl,hr,hgap⟩ := free_finite_event_separating_cover_clean_return
      p hcov a.val.val a.val.property.1 Γ.toContinuousMap hΓfinite hΓswitch A₀ hA₀
      (η l₀) (η r₀) (hηmono hlr₀) (by simpa only [Path.coe_toContinuousMap,hηΓ] using hl₀)
      (by simpa only [Path.coe_toContinuousMap,hηΓ] using hr₀)
    apply Or.inr
    have hct : ∃ t : Interval, p (Q t) ∈ range a.val.val := by
      obtain ⟨z,hza,t,ht⟩ := ((Set.ncard_pos hfinite).mp hpositive)
      exact ⟨t,by change p (D t) ∈ range a.val.val; rw [hDp,ht]; exact hza⟩
    have hPa0 : p (D 0) ∉ range a.val.val := by rw [hDp]; exact hseam0
    have hPa1 : p (D 1) ∉ range a.val.val := by rw [hDp]; exact hseam1
    rcases clean_three_piece_return_is_mixed p a.val.val P Q R' hPa0 hPa1 hct
      (hno 0) (hno 1) hsingle E hEp l r hlr hl hr hgap with
      ⟨u,v,hu,hv,huE,hvE,hPu,hQv⟩ | ⟨u,v,hu,hv,huE,hvE,hRu,hQv⟩
    · have hq (t : Interval) : p (Q t) = b.val.val t := hDp t
      have hpu : p (T 0 u) ∈ range a.val.val := by
        obtain ⟨t,ht⟩ := huE
        exact ⟨t,(hEp t).symm.trans (congrArg p ht)⟩
      apply mixed_track_return_gives_null_half_bigon B a.val.val b.val.val a.val.property.1 hbdends.1 hbdends.2.1
        (fun t ht => (hproper t ht).1) p hcov.continuous P Q
        (by rw [show (fun t => p (Q t)) = b.val.val from funext hq]; exact b.val.property.1)
        (by rintro _ ⟨t,rfl⟩; exact ⟨t,(hq t).symm⟩)
        (by rw [hq]; exact hbdends.2.2.1)
        (fun t ht => by rw [hq]; exact (hproper t ht).2)
        (hkB 0) E hEp u v hu hv huE hvE (hsimple 0 u hu hpu hPu) hQv
    · have hpu : p (T 1 u) ∈ range a.val.val := by
        obtain ⟨t,ht⟩ := huE
        exact ⟨t,(hEp t).symm.trans (congrArg p ht)⟩
      have hq (t : Interval) : p (Q.symm t) = b.val.val (unitInterval.symm t) := hDp _
      have hqs : IsEmbedding (fun t => p (Q.symm t)) := by
        have he : (fun t => p (Q.symm t)) = b.val.val ∘ unitInterval.symm := funext hq
        rw [he]
        exact b.val.property.1.comp unitInterval.symmHomeomorph.isEmbedding
      apply mixed_track_return_gives_null_half_bigon B a.val.val b.val.val a.val.property.1 hbdends.1 hbdends.2.1
        (fun t ht => (hproper t ht).1) p hcov.continuous R' Q.symm hqs
        (by rintro _ ⟨t,rfl⟩; exact ⟨unitInterval.symm t,(hq t).symm⟩)
        (by simpa only [hq,unitInterval.symm_zero] using hbdends.2.2.2)
        (fun t ht => ?_) (hkB 1) E hEp u v hu hv huE hvE
        (hsimple 1 u hu hpu hRu) hQv
      rw [hq]
      apply (hproper _ ?_).2
      constructor
      · simpa only [unitInterval.symm_one] using (unitInterval.symm_lt_symm.mpr ht.2)
      · simpa only [unitInterval.symm_zero] using (unitInterval.symm_lt_symm.mpr ht.1)
