import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalInterior
import CurveComplexGenusTwo.Topology.LocalSurgery.LoopCircleStatement
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalFirstDiskActualCoverAssemblyProved
import Mathlib

open CurveComplex Set Topology

namespace RegionalEmbeddedFamily

theorem nullhomotopic_curve_bounds_disk_on_closed_surface
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (u : S) (c : Curve S)
    (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)).Nullhomotopic) :
    BoundsDisc c := by
  classical
  let U := Σ y : S, Path.Homotopic.Quotient u y
  obtain ⟨t, hCover⟩ :=
    CurveComplex.LocalSurgery.closed_surface_actual_second_countable_universal_cover u
  letI : TopologicalSpace U := t
  rcases hCover with ⟨hSC, hT2, hChart, hSimply, hQuot, hSurj, hLift⟩
  letI : SecondCountableTopology U := hSC
  letI : T2Space U := hT2
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) U := hChart.some
  letI : SimplyConnectedSpace U := hSimply
  let p : U → S := Sigma.fst
  have hModel : Nonempty ((EuclideanSpace ℝ (Fin 2)) ≃ₜ U) ∨
      Nonempty ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₜ U) :=
    CurveComplex.LocalSurgery.closed_surface_simply_connected_cover_plane_or_sphere
      p hQuot.isCoveringMap hSurj
  rcases hModel with hPlane | hSphere
  · obtain ⟨e⟩ := hPlane
    obtain ⟨action, hq⟩ :=
      CurveComplex.LocalSurgery.actual_quotient_cover_domain_homeomorph_transport
        p hQuot e
    letI := action
    exact CurveComplex.boundsDisc_of_nullhomotopic_planar_quotient_cover_complete
      (p ∘ e) hq c hc
  · obtain ⟨e⟩ := hSphere
    obtain ⟨action, hq⟩ :=
      CurveComplex.LocalSurgery.actual_quotient_cover_domain_homeomorph_transport
        p hQuot e
    letI := action
    exact CurveComplex.LocalSurgery.boundsDisc_of_nullhomotopic_spherical_quotient_cover_complete
      (p ∘ e) hq c hc

theorem essential_curve_avoids_disk_of_boundary_disjoint
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (b : EssentialCurve S)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d)
    (hb : Disjoint b.val.image
      (d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1})) :
    Disjoint b.val.image (Set.range d) := by
  let K : Set S := Set.range d
  let U : Set S := interior K
  have hKc : IsClosed K := (isCompact_range d.continuous).isClosed
  have hKI : ∀ y ∈ K,
      y ∉ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} →
      y ∈ U := by
    rintro y ⟨z, rfl⟩ hn
    change d z ∈ interior (Set.range d)
    rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd]
    have hdist : dist z.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 := z.property
    have hlt : dist z.val (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
      apply lt_of_le_of_ne hdist
      intro he
      exact hn ⟨z, he, rfl⟩
    exact ⟨z, hlt, rfl⟩
  apply Set.disjoint_left.mpr
  intro y hyb hyd
  have hyU : y ∈ U := hKI y hyd (fun hbdy => Set.disjoint_left.mp hb hyb hbdy)
  have hcurveU : b.val.image ⊆ U := by
    apply (isConnected_range b.val.embedded.continuous).isPreconnected.subset_of_closure_inter_subset
      isOpen_interior ⟨y, hyb, hyU⟩
    intro z hz
    have hzK : z ∈ K := closure_minimal interior_subset hKc hz.1
    exact hKI z hzK (fun hbdy => Set.disjoint_left.mp hb hz.2 hbdy)
  obtain ⟨e, he, hboundary, hsub⟩ :=
    CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
      b.val d hd (hcurveU.trans interior_subset)
  exact b.property ⟨e, he, hboundary⟩

theorem embedded_surface_disk_frontier_eq_boundary_image
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d) :
    frontier (Set.range d) =
      d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
  have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
  rw [hclosed.frontier_eq,
    CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd]
  ext p
  constructor
  · rintro ⟨⟨x, rfl⟩, hxnot⟩
    refine ⟨x, ?_, rfl⟩
    have hxle : dist x.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 := x.property
    have hxge : 1 ≤ dist x.val (0 : EuclideanSpace ℝ (Fin 2)) := by
      by_contra hn
      apply hxnot
      exact ⟨x, lt_of_not_ge hn, rfl⟩
    exact le_antisymm hxle hxge
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro ⟨y, hy, he⟩
    have hxy := hd.injective he
    subst y
    change dist x.val (0 : EuclideanSpace ℝ (Fin 2)) < 1 at hy
    change dist x.val (0 : EuclideanSpace ℝ (Fin 2)) = 1 at hx
    linarith

theorem connected_open_set_avoiding_disk_boundary_dichotomy
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (O : Set S) (hO : IsPreconnected O)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d)
    (hboundary : Disjoint O
      (d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1})) :
    O ⊆ interior (Set.range d) ∨ O ⊆ (Set.range d)ᶜ := by
  let U : Set S := interior (Set.range d)
  let V : Set S := (Set.range d)ᶜ
  have hU : IsOpen U := isOpen_interior
  have hV : IsOpen V := (isCompact_range d.continuous).isClosed.isOpen_compl
  have hUV : Disjoint U V := disjoint_compl_right.mono_left interior_subset
  have hcover : O ⊆ U ∪ V := by
    intro y hy
    by_cases hyD : y ∈ Set.range d
    · left
      by_contra hn
      have hyFront : y ∈ frontier (Set.range d) :=
        (mem_frontier_iff_notMem_interior hyD).mpr hn
      exact Set.disjoint_left.mp hboundary hy
        ((embedded_surface_disk_frontier_eq_boundary_image d hd) ▸ hyFront)
    · exact Or.inr hyD
  exact hO.subset_or_subset hU hV hUV hcover

theorem source_chart_open_disk_inside_or_outside_clean_bigondisk
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d)
    (hboundary : d '' {z | z.val ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆ F) :
    let O := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    O ⊆ interior (Set.range d) ∨ O ⊆ (Set.range d)ᶜ := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let O := e.symm '' Metric.ball (e x) R
  have hball : Metric.ball (e x) R ⊆ e.target :=
    (Metric.ball_subset_closedBall).trans htarget
  have hconn : IsPreconnected O :=
    ((Metric.isConnected_ball hR).image e.symm
      (e.symm.continuousOn.mono hball)).isPreconnected
  have hdis : Disjoint O
      (d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    apply Set.disjoint_left.mpr
    intro y hyO hyD
    exact (houtside (hboundary hyD)) hyO
  exact connected_open_set_avoiding_disk_boundary_dichotomy O hconn d hd hdis

theorem source_chart_sphere_mem_closure_open_disk
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
    closure ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R) := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  rintro y ⟨w, hw, rfl⟩
  have hwclosed : w ∈ Metric.closedBall (e x) R := Metric.sphere_subset_closedBall hw
  have hwtarget : w ∈ e.target := htarget hwclosed
  have hwcont : ContinuousAt e.symm w :=
    e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hwtarget)
  have hwcl : w ∈ closure (Metric.ball (e x) R) := by
    rw [closure_ball _ (ne_of_gt hR)]
    exact hwclosed
  exact mem_closure_image hwcont hwcl

theorem source_chart_sphere_inside_bigondisk_of_open_disk_inside
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hinside : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      interior (Set.range d)) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      Set.range d := by
  have hclosed : IsClosed (Set.range d) :=
    (isCompact_range d.continuous).isClosed
  exact (source_chart_sphere_mem_closure_open_disk S x R hR htarget).trans
    ((closure_mono (hinside.trans interior_subset)).trans
      (hclosed.closure_eq.le))

theorem base_circle_except_corners_inside_bigondisk
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (B : Set S) (u z : S)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d)
    (hB : B ⊆ Set.range d)
    (hboundary : d '' {v | v.val ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 2)) 1} ∩ B ⊆ {u, z}) :
    B \ {u, z} ⊆ interior (Set.range d) := by
  intro y hy
  have hyD : y ∈ Set.range d := hB hy.1
  have hynot : y ∉ d '' {v | v.val ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    intro hyBoundary
    exact hy.2 (hboundary ⟨hyBoundary, hy.1⟩)
  by_contra hn
  have hyFront : y ∈ frontier (Set.range d) :=
    (mem_frontier_iff_notMem_interior hyD).mpr hn
  exact hynot ((embedded_surface_disk_frontier_eq_boundary_image d hd) ▸ hyFront)

theorem source_clean_bigondisk_base_circle_except_endpoints_inside
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S)
    (a b : C(Interval, ↥F))
    (haClear : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (a t).val ∉ frontier F)
    (hbClear : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (b t).val ∉ frontier F)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hbaseFront : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ frontier F)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d)
    (hboundary : d '' {v | v.val ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      Set.range (fun t => (a t).val) ∪ Set.range (fun t => (b t).val))
    (hinside : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      interior (Set.range d)) :
    ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R) \
        {(a 0).val, (a 1).val} ⊆ interior (Set.range d) := by
  let B := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
  have hB : B ⊆ Set.range d :=
    source_chart_sphere_inside_bigondisk_of_open_disk_inside
      S x R hR htarget d hinside
  apply base_circle_except_corners_inside_bigondisk B (a 0).val (a 1).val d hd hB
  rw [hboundary]
  rintro y ⟨hy, hyB⟩
  rcases hy with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · by_cases ht0 : t = 0
    · subst t
      exact Or.inl rfl
    · by_cases ht1 : t = 1
      · subst t
        exact Or.inr rfl
      · exfalso
        exact haClear t ⟨bot_lt_iff_ne_bot.mpr ht0,
          lt_top_iff_ne_top.mpr ht1⟩ (hbaseFront hyB)
  · by_cases ht0 : t = 0
    · subst t
      exact Or.inl (congrArg Subtype.val h0)
    · by_cases ht1 : t = 1
      · subst t
        exact Or.inr (congrArg Subtype.val h1)
      · exfalso
        exact hbClear t ⟨bot_lt_iff_ne_bot.mpr ht0,
          lt_top_iff_ne_top.mpr ht1⟩ (hbaseFront hyB)

theorem clean_homotopic_arcs_bound_null_curve
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {u z : X} (p q : Path u z)
    (hp : Topology.IsEmbedding p) (hq : Topology.IsEmbedding q)
    (hmeet : ∀ s t, p s = q t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hhom : p.Homotopic q) :
    ∃ c : Curve X, c.image = Set.range p ∪ Set.range q ∧
      (⟨c.map, c.embedded.continuous⟩ : C(Circle, X)).Nullhomotopic := by
  have hnull : (p.trans q.symm).Homotopic (Path.refl u) :=
    (hhom.hcomp (Path.Homotopic.refl q.symm)).trans
      (Path.Homotopic.trans_symm q)
  have hcollision : ∀ s t, (p.trans q.symm) s = (p.trans q.symm) t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    intro s t h
    simp only [Path.trans_apply, Path.symm_apply] at h
    split_ifs at h with hs ht ht
    · left
      have he := congrArg Subtype.val (hp.injective h)
      apply Subtype.ext
      dsimp at he
      linarith
    · have he := hmeet _ _ h
      rcases he with ⟨hs0, ht0⟩ | ⟨hs1, ht1⟩
      · right; left
        constructor <;> apply Subtype.ext
        · change (s : ℝ) = 0
          have := congrArg Subtype.val hs0; dsimp at this; linarith
        · change (t : ℝ) = 1
          have := congrArg Subtype.val ht0
          simp only [unitInterval.coe_symm_eq] at this
          dsimp at this; linarith
      · exfalso
        have := congrArg Subtype.val ht1
        simp only [unitInterval.coe_symm_eq] at this
        dsimp at this; linarith
    · have he := hmeet _ _ h.symm
      rcases he with ⟨ht0, hs0⟩ | ⟨ht1, hs1⟩
      · right; right
        constructor <;> apply Subtype.ext
        · change (s : ℝ) = 1
          have := congrArg Subtype.val hs0
          simp only [unitInterval.coe_symm_eq] at this
          dsimp at this; linarith
        · change (t : ℝ) = 0
          have := congrArg Subtype.val ht0; dsimp at this; linarith
      · exfalso
        have := congrArg Subtype.val hs1
        simp only [unitInterval.coe_symm_eq] at this
        dsimp at this; linarith
    · left
      have he := congrArg Subtype.val (hq.injective h)
      apply Subtype.ext
      simp only [unitInterval.coe_symm_eq] at he
      linarith
  obtain ⟨c, hc, hcn⟩ :=
    CurveComplex.LocalSurgery.nullhomotopic_loop_with_only_endpoint_collision_gives_curve
      u (p.trans q.symm) hcollision hnull
  refine ⟨c, ?_, hcn⟩
  simpa only [Path.trans_range, Path.symm_range] using hc

theorem clean_homotopic_arcs_bound_disk_on_closed_surface
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    {u z : S} (p q : Path u z)
    (hp : Topology.IsEmbedding p) (hq : Topology.IsEmbedding q)
    (hmeet : ∀ s t, p s = q t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hhom : p.Homotopic q) :
    ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S),
      Topology.IsEmbedding d ∧
      d '' {v | v.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range p ∪ Set.range q := by
  obtain ⟨c, hc, hnull⟩ :=
    clean_homotopic_arcs_bound_null_curve p q hp hq hmeet hhom
  obtain ⟨d, hd, hboundary⟩ :=
    nullhomotopic_curve_bounds_disk_on_closed_surface S u c hnull
  exact ⟨d, hd, hboundary.trans hc⟩

theorem clean_regional_arcs_bound_ambient_disk
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (F : Set S) (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hmeet : ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hhom : Path.Homotopic
      (⟨a, rfl, rfl⟩ : Path (a 0) (a 1))
      (⟨b, h0, h1⟩ : Path (a 0) (a 1))) :
    ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S),
      Topology.IsEmbedding d ∧
      d '' {v | v.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range (fun s => (a s).val) ∪ Set.range (fun s => (b s).val) := by
  let e : C(↥F, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let p : Path (a 0).val (a 1).val :=
    (⟨a, rfl, rfl⟩ : Path (a 0) (a 1)).map continuous_subtype_val
  let q : Path (a 0).val (a 1).val :=
    (⟨b, h0, h1⟩ : Path (a 0) (a 1)).map continuous_subtype_val
  have hp : Topology.IsEmbedding p := by
    exact Topology.IsEmbedding.subtypeVal.comp ha
  have hq : Topology.IsEmbedding q := by
    exact Topology.IsEmbedding.subtypeVal.comp hb
  have hmeet' : ∀ s t, p s = q t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t h
    exact hmeet s t (Subtype.ext h)
  have hhom' : p.Homotopic q := hhom.map e
  obtain ⟨d, hd, hboundary⟩ :=
    clean_homotopic_arcs_bound_disk_on_closed_surface
      S p q hp hq hmeet' hhom'
  exact ⟨d, hd, hboundary⟩

theorem clean_source_regional_arcs_ambient_disk_avoids_retained_curves
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F B : Set S) (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hCB : ∀ i, Disjoint (c i).val.image B)
    (hfrontier : frontier F = B ∪ ⋃ i, (c i).val.image)
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (ha0 : (a 0).val ∈ B) (ha1 : (a 1).val ∈ B)
    (hb0 : (b 0).val ∈ B) (hb1 : (b 1).val ∈ B)
    (haClear : ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F)
    (hbClear : ∀ t ∈ Set.Ioo (0 : Interval) 1, (b t).val ∉ frontier F)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hmeet : ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hhom : Path.Homotopic
      (⟨a, rfl, rfl⟩ : Path (a 0) (a 1))
      (⟨b, h0, h1⟩ : Path (a 0) (a 1))) :
    ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S),
      Topology.IsEmbedding d ∧
      d '' {v | v.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range (fun s => (a s).val) ∪ Set.range (fun s => (b s).val) ∧
      ∀ i, Disjoint (c i).val.image (Set.range d) := by
  letI : ClosedSurface S := Classical.choice hS.2.1
  obtain ⟨d, hd, hboundary⟩ :=
    clean_regional_arcs_bound_ambient_disk S F a b ha hb h0 h1 hmeet hhom
  refine ⟨d, hd, hboundary, ?_⟩
  intro i
  have hCi : (c i).val.image ⊆ frontier F := by
    rw [hfrontier]
    intro y hy
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, hy⟩)
  have hAi := proper_arc_avoids_retained_frontier_curve
    (hCB i) hCi a ha0 ha1 haClear
  have hBi := proper_arc_avoids_retained_frontier_curve
    (hCB i) hCi b hb0 hb1 hbClear
  apply essential_curve_avoids_disk_of_boundary_disjoint (c i) d hd
  rw [hboundary]
  apply Set.disjoint_left.mpr
  intro y hy hyy
  rcases hyy with hya | hyb
  · exact Set.disjoint_left.mp hAi hy hya
  · exact Set.disjoint_left.mp hBi hy hyb

end RegionalEmbeddedFamily
