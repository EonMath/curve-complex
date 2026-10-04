import CurveComplexGenusTwo.Topology.ActualRegionalBoundaryTracks.RegionalDecreaseSupport
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryContactFacts
import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalCrossingCoverTransfer

open CurveComplex Set Topology RegionalTotalDecrease RegionalEmbeddedFamily
open CoherentEndpointMotion.FreeBoundaryContactRepair
open CoherentEndpointMotion.FreeBoundaryNullGeometry
universe v
private noncomputable local instance regionalReturnCleanupScaffoldDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- PLAN B2: produce a return on the literal reverse-L₀ / D / L₁ path from a disjoint comparison sweep. -/
theorem regional_disjoint_comparison_sweep_has_lifted_return
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
        ∀ (Y : Type v) [TopologicalSpace Y] [T2Space Y] [SimplyConnectedSpace Y]
          (p : Y → ↥F), IsCoveringMap p → Function.Surjective p →
          (∀ A : C(Interval,Y), (∀ s, p (A s) = a.val.val s) →
            ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
              U ∪ V = (range A)ᶜ ∧ frontier U = range A ∧ frontier V = range A) →
          ∀ (ρ : Interval ≃ₜ Interval) (D E : C(Interval,Y))
            (W : C(Interval × Interval,Y)),
            ((ρ 0 = 0 ∧ ρ 1 = 1) ∨ (ρ 0 = 1 ∧ ρ 1 = 0)) →
            (∀ s, p (D s) = b.val.val s) → (∀ s, p (E s) = bStar.val.val s) →
            (∀ s, W (0,s) = D s) → (∀ s, W (1,s) = E (ρ s)) →
            (∀ t, IsEmbedding (fun s => W (t,s))) →
            (∀ t s, p (W (t,s)) = H.map (t,b.val.val s)) →
            (∀ t s, p (W (t,s)) ∈ {y | y.val ∈ boundaryCircle} ↔ s = 0 ∨ s = 1) →
            ∀ (β : Circle ≃ₜ ↥({y : ↥F | y.val ∈ boundaryCircle} : Set ↥F))
              (θ : Fin 2 → C(Interval,ℝ)) (L : Fin 2 → C(Interval,Y)),
              (∀ i t, (β (Circle.exp (θ i t))).val = H.map (t,b.val.val (endpoint i))) →
              (∀ t, 0 < θ 1 t-θ 0 t ∧ θ 1 t-θ 0 t < 2*Real.pi) →
              (∀ i t, p (L i t) =
                (β (Circle.exp ((1-t.val)*θ i 0+t.val*θ i 1))).val) →
              (∀ i, L i 0 = D (endpoint i) ∧ L i 1 = E (ρ (endpoint i))) →
              ∃ (Γ : C(Interval,Y)) (A₀ : C(Interval,Y)) (l₀ r₀ : Interval),
                (∀ t, Γ t = comparisonReturn L D t) ∧
                (∀ s, p (A₀ s) = a.val.val s) ∧ l₀ < r₀ ∧
                Γ l₀ ∈ range A₀ ∧ Γ r₀ ∈ range A₀ := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  dsimp only
  intro a b bStar hends hfinite hpositive hcross H hmovie hterminal
    Y _ _ _ p hp hsurj hsep ρ D E W hρ hDp hEp hW0 hW1 hWemb hWp hWboundary
    β θ L hθ hgap hLp hLends
  have hjoin0 : L 0 0 = D 0 := by simpa [endpoint] using (hLends 0).1
  have hjoin1 : L 1 0 = D 1 := by simpa [endpoint] using (hLends 1).1
  have hcontinuity : Continuous (comparisonReturn L D) := by
    unfold comparisonReturn
    apply Continuous.if_le
    · exact (L 0).continuous.comp (continuous_projIcc.comp (by fun_prop))
    · apply Continuous.if_le
      · exact D.continuous.comp (continuous_projIcc.comp (by fun_prop))
      · exact (L 1).continuous.comp (continuous_projIcc.comp (by fun_prop))
      · exact continuous_subtype_val
      · exact continuous_const
      · intro t ht
        norm_num [ht,projIcc]
        exact hjoin1.symm
    · exact continuous_subtype_val
    · exact continuous_const
    · intro t ht
      norm_num [ht,projIcc]
      exact hjoin0
  let Γ : C(Interval,Y) := ⟨comparisonReturn L D,hcontinuity⟩
  have hΓ0 : Γ 0 = E (ρ 0) := by
    change comparisonReturn L D 0 = _
    simpa [comparisonReturn,endpoint,projIcc] using (hLends 0).2
  have hΓ1 : Γ 1 = E (ρ 1) := by
    change comparisonReturn L D 1 = _
    norm_num [comparisonReturn,projIcc]
    simpa [endpoint] using (hLends 1).2
  let mid : Interval → Interval := fun t => ⟨(t.val+1)/3,by constructor <;> linarith [t.property.1,t.property.2]⟩
  have hmid (t : Interval) (ht : 0 < t) : Γ (mid t) = D t := by
    have ht' : 0 < t.val := ht
    have hlo : ¬(mid t).val ≤ (1/3:ℝ) := by dsimp [mid]; linarith
    have hhi : (mid t).val ≤ (2/3:ℝ) := by dsimp [mid]; linarith [t.property.2]
    change comparisonReturn L D (mid t) = _
    simp only [comparisonReturn,ite_eq_right hlo,ite_eq_left hhi]
    congr 1
    apply Subtype.ext
    simp only [coe_projIcc]
    dsimp [mid]
    rw [show 3*((t.val+1)/3)-1 = t.val by ring]
    rw [min_eq_right t.property.2,max_eq_right t.property.1]
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
  obtain ⟨z,⟨r,hr⟩,⟨s,hs⟩⟩ := (Set.ncard_pos hfinite).mp hpositive
  have hrs : a.val.val r = b.val.val s := hr.trans hs.symm
  obtain ⟨hrI,hsI,_⟩ := free_boundary_contact_parameters_interior B a.val.val b.val.val
    hbdends hproper hdisends r s hrs
  let : ContractibleSpace Interval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
  let : LocallyPathConnectedSpace Interval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨A,hA,_⟩ := hp.existsUnique_continuousMap_lifts a.val.val r (D s)
    ((hDp s).trans hrs.symm)
  have hAp : ∀ t, p (A t) = a.val.val t := fun t => congrFun hA.2 t
  have hAr : A r = D s := hA.1
  obtain ⟨U,V,hU,hV,hUV,hcover,hfrontU,hfrontV⟩ := hsep A hAp
  have hEavoid : range E ⊆ U ∪ V := by
    rintro y ⟨t,rfl⟩
    rw [hcover]
    rintro ⟨u,hu⟩
    have he : a.val.val u = bStar.val.val t :=
      (hAp u).symm.trans ((congrArg p hu).trans (hEp t))
    exact Set.disjoint_left.mp hterminal (⟨u,he⟩) (mem_range_self t)
  have hsame : (Γ 0 ∈ U ∧ Γ 1 ∈ U) ∨ (Γ 0 ∈ V ∧ Γ 1 ∈ V) := by
    have hconn : IsPreconnected (range E) := isPreconnected_range E.continuous
    rcases hconn.subset_or_subset hU hV hUV hEavoid with hu | hv
    · left
      exact ⟨hΓ0 ▸ hu (mem_range_self _),hΓ1 ▸ hu (mem_range_self _)⟩
    · right
      exact ⟨hΓ0 ▸ hv (mem_range_self _),hΓ1 ▸ hv (mem_range_self _)⟩
  obtain ⟨C,hC⟩ := hcross r s hrI hsI hrs
  have hswitch : ∀ l u : Interval, l < s → s < u →
      ∃ v w : Interval, l < v ∧ v < s ∧ s < w ∧ w < u ∧
        ((D v ∈ U ∧ D w ∈ V) ∨ (D v ∈ V ∧ D w ∈ U)) := by
    obtain ⟨Dchart,harD,hDz,hDval,hDaxis⟩ := contact_chart_in_region C
    obtain ⟨N,hN,hrN,hNsingle⟩ := contact_cover_lift_locally_single p hp
      a.val.val a.val.property.1.injective A hAp r
    obtain ⟨e,her,he⟩ := hp.isLocalHomeomorph (A r)
    let K := (e.trans Dchart).restr N
    have hKsrc : K.source = (e.source ∩ e ⁻¹' Dchart.source) ∩ N := by
      simp only [K,OpenPartialHomeomorph.restr_source,hN.interior_eq,
        OpenPartialHomeomorph.trans_source]
    have hKval (z : Y) (hz : z ∈ K.source) : K z = C.chart (p z).val := by
      have hzD : p z ∈ Dchart.source := by
        rw [he]
        exact (hKsrc ▸ hz).1.2
      change Dchart (e z) = C.chart (p z).val
      rw [← he]
      exact hDval _ hzD
    have hsK : D s ∈ K.source := by
      rw [← hAr,hKsrc]
      refine ⟨⟨her,?_⟩,hrN⟩
      change e (A r) ∈ Dchart.source
      rw [← he,hAp]
      exact harD
    have hz : K (D s) = 0 := by
      rw [hKval _ hsK,← hAr,hAp,C.contact_at_origin]
    have haxis : ∀ z ∈ K.source, z ∈ Set.range A ↔ K z 1 = 0 := by
      intro z hz
      rw [← hNsingle z (hKsrc ▸ hz).2]
      have hzD : p z ∈ Dchart.source := by rw [he]; exact (hKsrc ▸ hz).1.2
      change p z ∈ Set.range a.val.val ↔ Dchart (e z) 1 = 0
      rw [← he]
      exact hDaxis _ hzD
    apply contact_chart_opposite_signs_switch_global_sides D (Set.range A) U V
      hU hV hUV hcover hfrontU hfrontV K s C.bLeft C.bRight
      C.b_cuts.2.1 C.b_cuts.2.2.1 hsK hz haxis
    rcases hC with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · left
      constructor
      · intro t ht htK
        rw [hKval _ htK,hDp]
        exact hl t ht
      · intro t ht htK
        rw [hKval _ htK,hDp]
        exact hr t ht
    · right
      constructor
      · intro t ht htK
        rw [hKval _ htK,hDp]
        exact hl t ht
      · intro t ht htK
        rw [hKval _ htK,hDp]
        exact hr t ht
  obtain ⟨v,w,hv0,hvs,hsw,hw1,hvw⟩ := hswitch 0 1 hsI.1 hsI.2
  have hmid0 (t : Interval) : 0 < mid t := by
    change (0:ℝ) < (t.val+1)/3
    linarith [t.property.1]
  have hmid1 (t : Interval) : mid t < 1 := by
    change (t.val+1)/3 < (1:ℝ)
    linarith [t.property.2]
  have hmono : StrictMono mid := by
    intro u v huv
    change u.val < v.val at huv
    change (u.val+1)/3 < (v.val+1)/3
    linarith
  have hmidcross : ∃ l w : Interval, (0:Interval) < l ∧ l < mid s ∧
      mid s < w ∧ w < 1 ∧ ((Γ l ∈ U ∧ Γ w ∈ V) ∨ (Γ l ∈ V ∧ Γ w ∈ U)) := by
    refine ⟨mid v,mid w,hmid0 v,hmono hvs,hmono hsw,hmid1 w,?_⟩
    rwa [hmid v hv0,hmid w (hsI.1.trans hsw)]
  have hsecond : ∃ q ∈ Ioo (0:Interval) 1, q ≠ mid s ∧ Γ q ∈ range A := by
    rcases hsame with hh | hh
    · exact contact_crossing_inside_return_has_second_contact Γ Γ.continuous
        (range A) U V hU hV hUV hcover 0 1 (mid s) (hmid0 s) (hmid1 s)
        hh.1 hh.2 hmidcross
    · apply contact_crossing_inside_return_has_second_contact Γ Γ.continuous
        (range A) V U hV hU hUV.symm (by rw [union_comm,hcover])
        0 1 (mid s) (hmid0 s) (hmid1 s) hh.1 hh.2
      obtain ⟨l,w,hl0,hls,hsw,hw1,hh⟩ := hmidcross
      exact ⟨l,w,hl0,hls,hsw,hw1,hh.symm⟩
  obtain ⟨q,hq,hqne,hqA⟩ := hsecond
  have hsA : Γ (mid s) ∈ range A := by rw [hmid s hsI.1]; exact ⟨r,hAr⟩
  rcases lt_or_gt_of_ne hqne with hlt | hgt
  · exact ⟨Γ,A,q,mid s,(fun _ => rfl),hAp,hlt,hqA,hsA⟩
  · exact ⟨Γ,A,mid s,q,(fun _ => rfl),hAp,hgt,hsA,hqA⟩

