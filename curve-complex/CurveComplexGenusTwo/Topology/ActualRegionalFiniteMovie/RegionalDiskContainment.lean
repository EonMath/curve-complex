import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalPlanarCover

open CurveComplex Set Topology ClassificationJordanCurve.Arcs

namespace RegionalEmbeddedFamily

private noncomputable def diskCirclePoint (z : Circle) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  ⟨(circleHomeoSphere z).val,
    Metric.sphere_subset_closedBall (circleHomeoSphere z).property⟩

theorem boundary_circle_of_embedded_disk_in_region_nullhomotopic
    {S : Type} [TopologicalSpace S]
    (F : Set S) (c : Curve ↥F)
    (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, ↥F)).Nullhomotopic)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hboundary : d '' {z | z.val ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      Subtype.val '' c.image) :
    ∃ b : C(Circle, ↥F),
      b.Nullhomotopic ∧
      (∀ z, (b z).val = d (diskCirclePoint z)) := by
  classical
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  let k : C(Circle, D) :=
    ⟨diskCirclePoint,
      (continuous_subtype_val.comp circleHomeoSphere.continuous).subtype_mk _⟩
  have hkbd (z : Circle) : k z ∈ {v : D | v.val ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
    (circleHomeoSphere z).property
  have hmem (z : Circle) : ∃ w : ↥F,
      w ∈ c.image ∧ w.val = d (k z) := by
    have hm : d (k z) ∈ Subtype.val '' c.image := by
      rw [← hboundary]
      exact ⟨k z, hkbd z, rfl⟩
    exact hm
  have hFz (z : Circle) : d (k z) ∈ F := by
    obtain ⟨w, hw, he⟩ := hmem z
    exact he ▸ w.property
  let b : C(Circle, ↥F) :=
    ⟨fun z => ⟨d (k z), hFz z⟩,
      (d.continuous.comp k.continuous).subtype_mk _⟩
  have hbmem (z : Circle) : b z ∈ c.image := by
    obtain ⟨w, hw, he⟩ := hmem z
    have hbe : b z = w := Subtype.ext he.symm
    exact hbe ▸ hw
  let ec := c.embedded.toHomeomorph
  let ρ : C(Circle, Circle) :=
    ⟨fun z => ec.symm ⟨b z, hbmem z⟩,
      ec.symm.continuous.comp (b.continuous.subtype_mk _)⟩
  have hbc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, ↥F)).comp ρ = b := by
    ext z
    exact congrArg (fun w : c.image => ((w : ↥F) : S))
      (ec.apply_symm_apply ⟨b z, hbmem z⟩)
  refine ⟨b, hbc ▸ hc.comp_left ρ, ?_⟩
  intro z
  rfl

theorem embedded_disk_with_region_nullhomotopic_boundary_lies_in_region
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (c : Curve ↥F)
    (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, ↥F)).Nullhomotopic)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d)
    (hboundary : d '' {z | z.val ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      Subtype.val '' c.image) :
    Set.range d ⊆ F := by
  classical
  let u : S := (c.map (1 : Circle)).val
  obtain ⟨t, hcov, hsurj, ⟨e⟩⟩ :=
    genus_at_least_two_universal_cover_plane S g hg hS u
  let U := Σ y : S, Path.Homotopic.Quotient u y
  letI : TopologicalSpace U := t
  let p : EuclideanSpace ℝ (Fin 2) → S := Sigma.fst ∘ e
  have hp : IsCoveringMap p := hcov.comp_homeomorph e
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨v, hv⟩ := hsurj y
    refine ⟨e.symm v, ?_⟩
    exact (congrArg Sigma.fst (e.apply_symm_apply v)).trans hv
  obtain ⟨dl, hdl, hpd⟩ :=
    embedded_closed_disk_lifts_through_cover p hp hpsurj d hd
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  let k : C(Circle, D) :=
    ⟨diskCirclePoint,
      (continuous_subtype_val.comp circleHomeoSphere.continuous).subtype_mk _⟩
  have hk : Topology.IsEmbedding k := by
    have hki : Function.Injective k := by
      intro z w he
      apply circleHomeoSphere.injective
      apply Subtype.ext
      change (circleHomeoSphere z).val = (circleHomeoSphere w).val
      exact congrArg (fun v : D => v.val) he
    exact (k.continuous.isClosedEmbedding hki).isEmbedding
  have hkrange : Set.range k = {z : D | z.val ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (circleHomeoSphere w).property
    · intro hz
      refine ⟨circleHomeoSphere.symm ⟨z.val, hz⟩, ?_⟩
      apply Subtype.ext
      change (circleHomeoSphere (circleHomeoSphere.symm ⟨z.val, hz⟩)).val = z.val
      exact congrArg (fun v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 => v.val)
        (circleHomeoSphere.apply_symm_apply ⟨z.val, hz⟩)
  let r : C(Circle, EuclideanSpace ℝ (Fin 2)) := dl.comp k
  have hr : Topology.IsEmbedding r := hdl.comp hk
  let cp : Curve (EuclideanSpace ℝ (Fin 2)) := ⟨r, hr⟩
  obtain ⟨b, hbnull, hbproj⟩ :=
    boundary_circle_of_embedded_disk_in_region_nullhomotopic F c hc d hboundary
  have hpr (z : Circle) : p (r z) = (b z).val := by
    exact (hpd (k z)).trans (hbproj z).symm
  obtain ⟨y, H, hH⟩ :=
    chosen_lift_nullhomotopy_staying_in_region F b hbnull p hp r hpr
  have hinside : Schoenflies.inside cp.image ⊆ p ⁻¹' F := by
    intro z hz
    obtain ⟨ta, hta⟩ :=
      CurveComplex.actual_planar_jordan_inside_subset_nullhomotopy_range cp y H hz
    exact hta ▸ hH ta
  have hrJordan : Schoenflies.IsJordanCurve cp.image :=
    CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr
  have hdlboundary : dl '' {z : D | z.val ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 2)) 1} = cp.image := by
    rw [← hkrange]
    change dl '' Set.range k = Set.range (dl.comp k)
    exact (Set.range_comp (dl : D → EuclideanSpace ℝ (Fin 2))
      (k : Circle → D)).symm
  have hrange := CurveComplex.embedded_disc_range_eq_closed_inside
    dl hdl cp.image hrJordan hdlboundary
  intro z hz
  obtain ⟨v, hv⟩ := hz
  subst z
  have hvRange : dl v ∈ Set.range dl := Set.mem_range_self v
  rw [hrange] at hvRange
  have hvF : p (dl v) ∈ F := by
    rcases hvRange with hvInside | hvBoundary
    · exact hinside hvInside
    · obtain ⟨w, hw⟩ := hvBoundary
      have hproj : p (r w) = (b w).val := hpr w
      exact hw ▸ (hproj.symm ▸ (b w).property)
  exact (hpd v) ▸ hvF

theorem clean_homotopic_regional_arcs_bound_disk_in_region
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hmeet : ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hhom : Path.Homotopic
      (⟨a, rfl, rfl⟩ : Path (a 0) (a 1))
      (⟨b, h0, h1⟩ : Path (a 0) (a 1))) :
    ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥F),
      Topology.IsEmbedding d ∧
      d '' {z | z.val ∈ Metric.sphere
        (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range a ∪ Set.range b := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  obtain ⟨c, hcRange, hcNull⟩ :=
    clean_regional_arcs_form_null_curve_in_region F a b ha hb h0 h1 hmeet hhom
  obtain ⟨d, hd, hboundary⟩ :=
    clean_regional_arcs_bound_ambient_disk S F a b ha hb h0 h1 hmeet hhom
  have hboundary' : d '' {z | z.val ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      Subtype.val '' c.image := by
    rw [hboundary, hcRange, Set.image_union]
    simp only [← Set.range_comp]
    rfl
  have hD : Set.range d ⊆ F :=
    embedded_disk_with_region_nullhomotopic_boundary_lies_in_region
      S g hg hS F c hcNull d hd hboundary'
  let dr : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥F) :=
    ⟨fun z => ⟨d z, hD (Set.mem_range_self z)⟩,
      d.continuous.subtype_mk _⟩
  have hdr : Topology.IsEmbedding dr := by
    apply Topology.IsEmbedding.of_comp dr.continuous continuous_subtype_val
    change Topology.IsEmbedding d
    exact hd
  refine ⟨dr, hdr, ?_⟩
  apply (Set.image_injective.mpr (Subtype.val_injective :
    Function.Injective (Subtype.val : ↥F → S)))
  rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
  rw [← Set.image_comp]
  change d '' {z | z.val ∈ Metric.sphere
    (0 : EuclideanSpace ℝ (Fin 2)) 1} =
    Set.range (fun s => (a s).val) ∪ Set.range (fun s => (b s).val)
  exact hboundary

theorem embedded_regional_disk_interior_avoids_frontier
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (F : Set S)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥F))
    (hd : Topology.IsEmbedding d)
    (z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hz : z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (d z).val ∉ frontier F := by
  let ds : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S) :=
    ⟨fun w => (d w).val, continuous_subtype_val.comp d.continuous⟩
  have hds : Topology.IsEmbedding ds := Topology.IsEmbedding.subtypeVal.comp hd
  have hrange : Set.range ds ⊆ F := by
    rintro y ⟨w, rfl⟩
    exact (d w).property
  have hzi : ds z ∈ interior (Set.range ds) := by
    rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq ds hds]
    exact ⟨z, hz, rfl⟩
  have hzF : (d z).val ∈ interior F :=
    interior_mono hrange hzi
  intro hfront
  exact ((mem_frontier_iff_notMem_interior (interior_subset hzF)).mp hfront) hzF

theorem clean_homotopic_regional_arcs_bound_frontier_clear_disk
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hmeet : ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hhom : Path.Homotopic
      (⟨a, rfl, rfl⟩ : Path (a 0) (a 1))
      (⟨b, h0, h1⟩ : Path (a 0) (a 1))) :
    ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥F),
      Topology.IsEmbedding d ∧
      d '' {z | z.val ∈ Metric.sphere
        (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range a ∪ Set.range b ∧
      ∀ z, z.val ∈ Metric.ball
        (0 : EuclideanSpace ℝ (Fin 2)) 1 →
        (d z).val ∉ frontier F := by
  obtain ⟨d, hd, hboundary⟩ :=
    clean_homotopic_regional_arcs_bound_disk_in_region
      S g hg hS F a b ha hb h0 h1 hmeet hhom
  letI : ClosedSurface S := Classical.choice hS.2.1
  exact ⟨d, hd, hboundary,
    fun z hz => embedded_regional_disk_interior_avoids_frontier S F d hd z hz⟩

end RegionalEmbeddedFamily
