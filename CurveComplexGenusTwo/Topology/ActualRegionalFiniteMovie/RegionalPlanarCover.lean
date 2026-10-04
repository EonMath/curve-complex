import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalNullBigon
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalBRecognitionConsumer
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.FiniteFundamentalGroupFirstHomologyProof

open CurveComplex Set Topology

namespace RegionalEmbeddedFamily

theorem clean_regional_arcs_form_null_curve_in_region
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F : Set S) (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hmeet : ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hhom : Path.Homotopic
      (⟨a, rfl, rfl⟩ : Path (a 0) (a 1))
      (⟨b, h0, h1⟩ : Path (a 0) (a 1))) :
    ∃ c : Curve ↥F,
      c.image = Set.range a ∪ Set.range b ∧
      (⟨c.map, c.embedded.continuous⟩ : C(Circle, ↥F)).Nullhomotopic := by
  exact clean_homotopic_arcs_bound_null_curve
    (⟨a, rfl, rfl⟩ : Path (a 0) (a 1))
    (⟨b, h0, h1⟩ : Path (a 0) (a 1)) ha hb hmeet hhom

theorem lift_nullhomotopy_staying_in_region
    {A S E : Type*} [TopologicalSpace A] [TopologicalSpace S]
    [TopologicalSpace E]
    (F : Set S) (f : C(A, ↥F)) (hf : f.Nullhomotopic)
    (p : E → S) (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) :
    ∃ (g : C(A, E)) (y : E),
      (∀ a, p (g a) = (f a).val) ∧
      ∃ H : ContinuousMap.Homotopy g (ContinuousMap.const A y),
        ∀ t, p (H t) ∈ F := by
  obtain ⟨x, ⟨H⟩⟩ := hf
  obtain ⟨y, hy⟩ := hsurj x.val
  let R : ContinuousMap.Homotopy
      (ContinuousMap.const A x) f := H.symm
  let inc : C(↥F, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let RS : ContinuousMap.Homotopy
      (ContinuousMap.const A x.val) (inc.comp f) := {
    toContinuousMap := inc.comp R.toContinuousMap
    map_zero_left := by
      intro a
      exact congrArg Subtype.val (R.map_zero_left a)
    map_one_left := by
      intro a
      exact congrArg Subtype.val (R.map_one_left a)
  }
  let gy : C(A, E) := ContinuousMap.const A y
  have hzero : ∀ a, RS (0, a) = p (gy a) := by
    intro a
    change (R (0, a)).val = p y
    exact (congrArg Subtype.val (R.map_zero_left a)).trans hy.symm
  let K := hp.liftHomotopy RS gy hzero
  let g : C(A, E) := ⟨fun a => K (1, a),
    K.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hone : ∀ a, p (g a) = (f a).val := by
    intro a
    have h := congrFun (hp.liftHomotopy_lifts RS gy hzero) (1, a)
    exact h.trans (RS.map_one_left a)
  let KK : ContinuousMap.Homotopy gy g := {
    toContinuousMap := K
    map_zero_left := by
      intro a
      change K (0, a) = y
      exact hp.liftHomotopy_zero RS gy hzero a
    map_one_left := by intro a; rfl
  }
  let KH : ContinuousMap.Homotopy g (ContinuousMap.const A y) := KK.symm
  refine ⟨g, y, hone, KH, ?_⟩
  intro ta
  have h := congrFun (hp.liftHomotopy_lifts RS gy hzero)
    ((unitInterval.symm ta.1), ta.2)
  change p (K (unitInterval.symm ta.1, ta.2)) =
    (R (unitInterval.symm ta.1, ta.2)).val at h
  have hF : (R ((unitInterval.symm ta.1), ta.2)).val ∈ F :=
    (R ((unitInterval.symm ta.1), ta.2)).property
  change p (K (unitInterval.symm ta.1, ta.2)) ∈ F
  rw [h]
  exact hF

theorem genus_at_least_two_first_homology_infinite
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) :
    Infinite (integralHomology S 1) := by
  obtain ⟨E⟩ := hS.2.2.2
  let j : Fin (2 * g) := ⟨0, by omega⟩
  let v : ℤ → integralHomology S 1 :=
    fun n => E.toLinearEquiv.symm (fun _ => n)
  apply Infinite.of_injective v
  intro n m he
  have hh := congrArg (fun w => E.toLinearEquiv w j) he
  simpa [v] using hh

theorem genus_at_least_two_universal_cover_plane
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (u : S) :
    ∃ t : TopologicalSpace (Σ y : S, Path.Homotopic.Quotient u y),
      letI : TopologicalSpace (Σ y : S, Path.Homotopic.Quotient u y) := t
      IsCoveringMap (Sigma.fst : (Σ y : S, Path.Homotopic.Quotient u y) → S) ∧
      Function.Surjective (Sigma.fst : (Σ y : S, Path.Homotopic.Quotient u y) → S) ∧
      Nonempty ((EuclideanSpace ℝ (Fin 2)) ≃ₜ
        (Σ y : S, Path.Homotopic.Quotient u y)) := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  let U := Σ y : S, Path.Homotopic.Quotient u y
  obtain ⟨t, hCover⟩ :=
    CurveComplex.LocalSurgery.closed_surface_actual_second_countable_universal_cover u
  letI : TopologicalSpace U := t
  rcases hCover with ⟨hSC, hT2, hChart, hSimply, hQuot, hSurj, hLift⟩
  letI : SecondCountableTopology U := hSC
  letI : T2Space U := hT2
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) U := hChart.some
  letI : SimplyConnectedSpace U := hSimply
  let cov := hQuot.isCoveringMap
  have hmodel : Nonempty ((EuclideanSpace ℝ (Fin 2)) ≃ₜ U) ∨
      Nonempty ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₜ U) :=
    CurveComplex.LocalSurgery.closed_surface_simply_connected_cover_plane_or_sphere
      (Sigma.fst : U → S) cov hSurj
  have hplane : Nonempty ((EuclideanSpace ℝ (Fin 2)) ≃ₜ U) := by
    rcases hmodel with hp | hsphere
    · exact hp
    · obtain ⟨esphere⟩ := hsphere
      letI : CompactSpace U := esphere.compactSpace
      let K : Set U := (Sigma.fst : U → S) ⁻¹' {u}
      have hKclosed : IsClosed K :=
        isClosed_singleton.preimage cov.continuous
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hKclosed.isCompact
      letI : DiscreteTopology K := (cov u).discreteTopology_fiber
      letI : Finite K := finite_of_compact_of_discrete
      let point : Path.Homotopic.Quotient u u → K :=
        fun q => ⟨⟨u, q⟩, rfl⟩
      have hpoint : Function.Injective point := by
        intro q r he
        have hh : HEq q r := (Sigma.mk.inj_iff.mp (congrArg Subtype.val he)).2
        exact eq_of_heq hh
      letI : Finite (Path.Homotopic.Quotient u u) :=
        Finite.of_injective point hpoint
      letI : Finite (FundamentalGroup S u) := by
        change Finite (Path.Homotopic.Quotient u u)
        infer_instance
      letI : LocallyPathConnectedSpace S :=
        ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
      letI : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
      have hFiniteH1 : Finite (integralHomology S 1) :=
        CurveComplex.LocalSurgery.finite_integral_first_homology_of_finite_fundamental_group S u
      letI := hFiniteH1
      letI := genus_at_least_two_first_homology_infinite S g hg hS
      exact (not_finite (integralHomology S 1)).elim
  exact ⟨t, cov, hSurj, hplane⟩

theorem regional_null_curve_has_planar_avoiding_lift
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (c : Curve ↥F)
    (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, ↥F)).Nullhomotopic) :
    ∃ (p : EuclideanSpace ℝ (Fin 2) → S)
      (cp : Curve (EuclideanSpace ℝ (Fin 2)))
      (y : EuclideanSpace ℝ (Fin 2))
      (H : ContinuousMap.Homotopy
        (⟨cp.map, cp.embedded.continuous⟩ : C(Circle, EuclideanSpace ℝ (Fin 2)))
        (ContinuousMap.const Circle y)),
      IsCoveringMap p ∧
      (∀ z, p (cp.map z) = (c.map z).val) ∧
      (∀ t, p (H t) ∈ F) := by
  classical
  let u : S := (c.map (1 : Circle)).val
  obtain ⟨t, hcov, hsurj, ⟨e⟩⟩ :=
    genus_at_least_two_universal_cover_plane S g hg hS u
  let U := Σ z : S, Path.Homotopic.Quotient u z
  letI : TopologicalSpace U := t
  let f : C(Circle, ↥F) := ⟨c.map, c.embedded.continuous⟩
  obtain ⟨r, y, hr, H, hH⟩ :=
    lift_nullhomotopy_staying_in_region F f hc
      (Sigma.fst : U → S) hcov hsurj
  let p : EuclideanSpace ℝ (Fin 2) → S := Sigma.fst ∘ e
  have hp : Continuous p := hcov.continuous.comp e.continuous
  have hpcov : IsCoveringMap p := hcov.comp_homeomorph e
  let rp : C(Circle, EuclideanSpace ℝ (Fin 2)) :=
    ⟨fun z => e.symm (r z), e.symm.continuous.comp r.continuous⟩
  have hrp : Topology.IsEmbedding rp := by
    apply Topology.IsEmbedding.of_comp rp.continuous hp
    have hfun : p ∘ (rp : Circle → EuclideanSpace ℝ (Fin 2)) =
        Subtype.val ∘ c.map := by
      funext z
      exact (congrArg Sigma.fst (e.apply_symm_apply (r z))).trans (hr z)
    rw [hfun]
    exact Topology.IsEmbedding.subtypeVal.comp c.embedded
  let cp : Curve (EuclideanSpace ℝ (Fin 2)) := ⟨rp, hrp⟩
  let yp : EuclideanSpace ℝ (Fin 2) := e.symm y
  let HP : ContinuousMap.Homotopy rp (ContinuousMap.const Circle yp) := {
    toContinuousMap := ⟨fun ta => e.symm (H ta),
      e.symm.continuous.comp H.continuous⟩
    map_zero_left := by intro z; exact congrArg e.symm (H.map_zero_left z)
    map_one_left := by intro z; exact congrArg e.symm (H.map_one_left z)
  }
  refine ⟨p, cp, yp, HP, hpcov, ?_, ?_⟩
  · intro z
    exact (congrArg Sigma.fst (e.apply_symm_apply (r z))).trans (hr z)
  · intro ta
    change (Sigma.fst (e (e.symm (H ta)))) ∈ F
    rw [e.apply_symm_apply]
    exact hH ta

theorem regional_null_curve_planar_inside_projects_to_region
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (c : Curve ↥F)
    (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, ↥F)).Nullhomotopic) :
    ∃ (p : EuclideanSpace ℝ (Fin 2) → S)
      (cp : Curve (EuclideanSpace ℝ (Fin 2))),
      IsCoveringMap p ∧
      (∀ z, p (cp.map z) = (c.map z).val) ∧
      Schoenflies.inside cp.image ⊆ p ⁻¹' F := by
  obtain ⟨p, cp, y, H, hcov, hp, hH⟩ :=
    regional_null_curve_has_planar_avoiding_lift S g hg hS F c hc
  refine ⟨p, cp, hcov, hp, ?_⟩
  intro z hz
  obtain ⟨ta, hta⟩ :=
    CurveComplex.actual_planar_jordan_inside_subset_nullhomotopy_range cp y H hz
  exact hta ▸ hH ta

theorem embedded_closed_disk_lifts_through_cover
    {S E : Type*} [TopologicalSpace S] [TopologicalSpace E]
    (p : E → S) (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d) :
    ∃ dl : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, E),
      Topology.IsEmbedding dl ∧ ∀ z, p (dl z) = d z := by
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  letI : ContractibleSpace D :=
    (convex_closedBall _ _).contractibleSpace ⟨0, by simp⟩
  letI : LocallyPathConnectedSpace D :=
    (convex_closedBall _ _).locallyPathConnectedSpace
  let z : D := ⟨0, by simpa [D]⟩
  obtain ⟨y, hy⟩ := hsurj (d z)
  obtain ⟨dl, ⟨hdl0, hdl⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts d z y hy
  refine ⟨dl, ?_, ?_⟩
  · apply Topology.IsEmbedding.of_comp dl.continuous hp.continuous
    have he : p ∘ (dl : D → E) = d := by
      funext x
      exact congrFun hdl x
    rw [he]
    exact hd
  · intro x
    exact congrFun hdl x

theorem nullhomotopic_of_embedded_circle_same_range
    {X : Type*} [TopologicalSpace X]
    (f g : C(Circle, X))
    (hf : Topology.IsEmbedding f)
    (hg : Topology.IsEmbedding g)
    (hrange : Set.range f = Set.range g)
    (hnull : f.Nullhomotopic) : g.Nullhomotopic := by
  let ef := hf.toHomeomorph
  let r : C(Circle, Circle) :=
    ⟨fun z => ef.symm ⟨g z, hrange ▸ Set.mem_range_self z⟩,
      ef.symm.continuous.comp (g.continuous.subtype_mk _)⟩
  have hcomp : f.comp r = g := by
    ext z
    exact congrArg Subtype.val
      (ef.apply_symm_apply ⟨g z, hrange ▸ Set.mem_range_self z⟩)
  exact hcomp ▸ hnull.comp_left r

theorem chosen_lift_nullhomotopy_staying_in_region
    {A S E : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    [Nonempty A] [TopologicalSpace S] [TopologicalSpace E]
    (F : Set S) (f : C(A, ↥F)) (hf : f.Nullhomotopic)
    (p : E → S) (hp : IsCoveringMap p)
    (r : C(A, E)) (hpr : ∀ a, p (r a) = (f a).val) :
    ∃ y : E,
      ∃ H : ContinuousMap.Homotopy r (ContinuousMap.const A y),
        ∀ t, p (H t) ∈ F := by
  obtain ⟨x, ⟨H⟩⟩ := hf
  let inc : C(↥F, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let HS : ContinuousMap.Homotopy (inc.comp f)
      (ContinuousMap.const A x.val) := {
    toContinuousMap := inc.comp H.toContinuousMap
    map_zero_left := by
      intro a
      exact congrArg Subtype.val (H.map_zero_left a)
    map_one_left := by
      intro a
      exact congrArg Subtype.val (H.map_one_left a)
  }
  have hzero : ∀ a, HS (0, a) = p (r a) := by
    intro a
    exact (HS.map_zero_left a).trans (hpr a).symm
  let K := hp.liftHomotopy HS r hzero
  let y : E := K (1, Classical.arbitrary A)
  have hend : ∀ a, K (1, a) = y := by
    intro a
    have hconst : ∀ a b, p (K (1, a)) = p (K (1, b)) := by
      intro a b
      have ha := congrFun (hp.liftHomotopy_lifts HS r hzero) (1, a)
      have hb := congrFun (hp.liftHomotopy_lifts HS r hzero) (1, b)
      calc
        p (K (1, a)) = HS (1, a) := ha
        _ = x.val := HS.map_one_left a
        _ = HS (1, b) := (HS.map_one_left b).symm
        _ = p (K (1, b)) := hb.symm
    exact hp.const_of_comp
      (K.continuous.comp (continuous_const.prodMk continuous_id))
      hconst a (Classical.arbitrary A)
  let HK : ContinuousMap.Homotopy r (ContinuousMap.const A y) := {
    toContinuousMap := K
    map_zero_left := hp.liftHomotopy_zero HS r hzero
    map_one_left := hend
  }
  refine ⟨y, HK, ?_⟩
  intro ta
  have h := congrFun (hp.liftHomotopy_lifts HS r hzero) ta
  change p (K ta) = (H ta).val at h
  change p (K ta) ∈ F
  rw [h]
  exact (H ta).property

end RegionalEmbeddedFamily
