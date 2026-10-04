import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalSquareSweep
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualModelSquareClosedCapInteriorKernelRecovery

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

private abbrev UnitDisk := Metric.closedBall (0 : Plane) 1
private def UnitBoundary : Set UnitDisk :=
  {z | z.val ∈ Metric.sphere (0 : Plane) 1}

theorem unit_sphere_isJordanCurve :
    IsJordanCurve (Metric.sphere (0 : Plane) 1) := by
  let r : C(Circle, Plane) :=
    ⟨fun z => (ClassificationJordanCurve.Arcs.circleHomeoSphere z : Plane),
      continuous_subtype_val.comp
        ClassificationJordanCurve.Arcs.circleHomeoSphere.continuous⟩
  have hr : Topology.IsEmbedding r :=
    Topology.IsEmbedding.subtypeVal.comp
      ClassificationJordanCurve.Arcs.circleHomeoSphere.isEmbedding
  have hrange : Set.range r = Metric.sphere (0 : Plane) 1 := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (ClassificationJordanCurve.Arcs.circleHomeoSphere z).property
    · intro hx
      refine ⟨ClassificationJordanCurve.Arcs.circleHomeoSphere.symm ⟨x, hx⟩, ?_⟩
      change (ClassificationJordanCurve.Arcs.circleHomeoSphere
        (ClassificationJordanCurve.Arcs.circleHomeoSphere.symm ⟨x, hx⟩) : Plane) = x
      rw [ClassificationJordanCurve.Arcs.circleHomeoSphere.apply_symm_apply]
  rw [← hrange]
  exact CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr

theorem inside_unit_sphere :
    Schoenflies.inside (Metric.sphere (0 : Plane) 1) =
      Metric.ball (0 : Plane) 1 := by
  have hsub : Metric.ball (0 : Plane) 1 ⊆
      (Metric.sphere (0 : Plane) 1)ᶜ := by
    intro x hx hs
    exact (ne_of_lt (Metric.mem_ball.mp hx)) (Metric.mem_sphere.mp hs)
  have hfr : frontier (Metric.ball (0 : Plane) 1) ∩
      (Metric.sphere (0 : Plane) 1)ᶜ = ∅ := by
    rw [frontier_ball (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)]
    exact Set.inter_compl_self _
  have hzero : (0 : Plane) ∈ Metric.ball (0 : Plane) 1 := by simp
  have hcomp := Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint
    Metric.isOpen_ball (convex_ball (0 : Plane) 1).isPreconnected hsub hfr hzero
  have hinside : (0 : Plane) ∈
      Schoenflies.inside (Metric.sphere (0 : Plane) 1) := by
    refine ⟨hsub hzero, ?_⟩
    rw [hcomp]
    exact Metric.isBounded_ball
  exact ((Schoenflies.jordan_curve_theorem unit_sphere_isJordanCurve).connectedComponentIn_eq_inside
    hinside).symm.trans hcomp

theorem planar_embedded_path_isArcBetween
    (f : C(Interval, Plane)) (hf : Topology.IsEmbedding f) :
    IsArcBetween (Set.range f) (f 0) (f 1) := by
  let fc : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
  have hfc : Continuous fc := f.continuous.comp continuous_projIcc
  have he (t : Interval) : fc t = f t := by
    simp [fc, Set.projIcc_of_mem zero_le_one t.property]
  refine ⟨fc, hfc.continuousOn, ?_, ?_, he 0, he 1⟩
  · intro t ht u hu h
    exact congrArg Subtype.val (hf.injective (by
      simpa only [← he] using h : f ⟨t, ht⟩ = f ⟨u, hu⟩))
  · ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, (he ⟨t, ht⟩).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, he t⟩

theorem embedded_disk_boundary_arc_lift
    {X : Type*} [TopologicalSpace X]
    (d : C(UnitDisk, X)) (hd : Topology.IsEmbedding d)
    (a : C(Interval, X)) (ha : Topology.IsEmbedding a)
    (hboundary : Set.range a ⊆ d '' UnitBoundary) :
    ∃ g : C(Interval, UnitDisk),
      Topology.IsEmbedding g ∧
      (∀ s, d (g s) = a s) ∧
      (∀ s, (g s).val ∈ Metric.sphere (0 : Plane) 1) := by
  have haRange (s : Interval) : a s ∈ Set.range d := by
    obtain ⟨z, hz, he⟩ := hboundary (Set.mem_range_self s)
    exact ⟨z, he⟩
  let aa : C(Interval, Set.range d) :=
    ⟨fun s => ⟨a s, haRange s⟩, a.continuous.subtype_mk _⟩
  let g : C(Interval, UnitDisk) :=
    ⟨fun s => hd.toHomeomorph.symm (aa s),
      hd.toHomeomorph.symm.continuous.comp aa.continuous⟩
  have hgd (s : Interval) : d (g s) = a s := by
    exact congrArg Subtype.val
      (hd.toHomeomorph.apply_symm_apply (aa s))
  have hga : Topology.IsEmbedding aa := by
    apply Topology.IsEmbedding.of_comp aa.continuous continuous_subtype_val
    exact ha
  have hg : Topology.IsEmbedding g :=
    hd.toHomeomorph.symm.isEmbedding.comp hga
  refine ⟨g, hg, hgd, ?_⟩
  intro s
  obtain ⟨z, hz, hdz⟩ := hboundary (Set.mem_range_self s)
  have he : g s = z := hd.injective ((hgd s).trans hdz.symm)
  exact he ▸ hz

theorem embedded_disk_boundary_arc_planar_lift
    {X : Type*} [TopologicalSpace X]
    (d : C(UnitDisk, X)) (hd : Topology.IsEmbedding d)
    (a : C(Interval, X)) (ha : Topology.IsEmbedding a)
    (hboundary : Set.range a ⊆ d '' UnitBoundary) :
    ∃ g : C(Interval, Plane),
      Topology.IsEmbedding g ∧
      (∀ s, ∃ z : UnitDisk, z.val = g s ∧ d z = a s) ∧
      (Set.range g ⊆ Metric.sphere (0 : Plane) 1) := by
  obtain ⟨u, hu, hud, huSphere⟩ :=
    embedded_disk_boundary_arc_lift d hd a ha hboundary
  let g : C(Interval, Plane) :=
    ⟨fun s => (u s).val, continuous_subtype_val.comp u.continuous⟩
  have hg : Topology.IsEmbedding g :=
    Topology.IsEmbedding.subtypeVal.comp hu
  refine ⟨g, hg, ?_, ?_⟩
  · intro s
    exact ⟨u s, rfl, hud s⟩
  · rintro z ⟨s, rfl⟩
    exact huSphere s

theorem clean_disk_boundary_pair_planar_lifts
    {X : Type*} [TopologicalSpace X]
    (d : C(UnitDisk, X)) (hd : Topology.IsEmbedding d)
    (a b : C(Interval, X))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hmeet : ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hboundary : d '' UnitBoundary = Set.range a ∪ Set.range b) :
    ∃ (g h : C(Interval, Plane)),
      Topology.IsEmbedding g ∧ Topology.IsEmbedding h ∧
      g 0 = h 0 ∧ g 1 = h 1 ∧
      Set.range g ∪ Set.range h = Metric.sphere (0 : Plane) 1 ∧
      (∀ s t, g s = h t →
        (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) ∧
      (∀ s, ∃ z : UnitDisk, z.val = g s ∧ d z = a s) ∧
      (∀ s, ∃ z : UnitDisk, z.val = h s ∧ d z = b s) := by
  have hAbound : Set.range a ⊆ d '' UnitBoundary := by
    rw [hboundary]
    exact Set.subset_union_left
  have hBbound : Set.range b ⊆ d '' UnitBoundary := by
    rw [hboundary]
    exact Set.subset_union_right
  obtain ⟨g, hg, hgLift, hgSphere⟩ :=
    embedded_disk_boundary_arc_planar_lift d hd a ha hAbound
  obtain ⟨h, hh, hhLift, hhSphere⟩ :=
    embedded_disk_boundary_arc_planar_lift d hd b hb hBbound
  have heq (s t : Interval) (hst : a s = b t) : g s = h t := by
    obtain ⟨u, hu, hud⟩ := hgLift s
    obtain ⟨v, hv, hvd⟩ := hhLift t
    have huv : u = v := hd.injective (hud.trans (hst.trans hvd.symm))
    exact hu.symm.trans ((congrArg Subtype.val huv).trans hv)
  refine ⟨g, h, hg, hh, heq 0 0 h0.symm, heq 1 1 h1.symm, ?_, ?_, hgLift,
    hhLift⟩
  · apply Set.Subset.antisymm
    · exact Set.union_subset hgSphere hhSphere
    · intro z hz
      have hzD : (⟨z, Metric.sphere_subset_closedBall hz⟩ : UnitDisk) ∈
          UnitBoundary := hz
      have hdz : d ⟨z, Metric.sphere_subset_closedBall hz⟩ ∈
          Set.range a ∪ Set.range b := hboundary ▸
            Set.mem_image_of_mem d hzD
      rcases hdz with ⟨s, hs⟩ | ⟨t, ht⟩
      · left
        obtain ⟨u, hu, hud⟩ := hgLift s
        have he : u = ⟨z, Metric.sphere_subset_closedBall hz⟩ :=
          hd.injective (hud.trans hs)
        exact ⟨s, hu.symm.trans (congrArg Subtype.val he)⟩
      · right
        obtain ⟨u, hu, hud⟩ := hhLift t
        have he : u = ⟨z, Metric.sphere_subset_closedBall hz⟩ :=
          hd.injective (hud.trans ht)
        exact ⟨t, hu.symm.trans (congrArg Subtype.val he)⟩
  · intro s t hst
    obtain ⟨u, hu, hud⟩ := hgLift s
    obtain ⟨v, hv, hvd⟩ := hhLift t
    have huv : u = v := Subtype.ext (hu.trans (hst.trans hv.symm))
    exact hmeet s t (hud.symm.trans ((congrArg d huv).trans hvd))

theorem planar_clean_pair_boundary_alignment
    (g h : C(Interval, Plane))
    (hg : Topology.IsEmbedding g) (hh : Topology.IsEmbedding h)
    (h0 : g 0 = h 0) (h1 : g 1 = h 1)
    (hmeet : ∀ s t, g s = h t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ e : ↥(Set.range g ∪ Set.range h) ≃ₜ
      ↥((sideTop ∪ sideLeft) ∪ (sideBottom ∪ sideRight)),
      Subtype.val '' (e '' {z : ↥(Set.range g ∪ Set.range h) |
        z.val ∈ Set.range h}) = sideBottom ∪ sideRight ∧
      e ⟨g 0, Or.inl (Set.mem_range_self 0)⟩ =
        ⟨cornerNE, Or.inl isArcBetween_upperSides.left_mem⟩ ∧
      e ⟨g 1, Or.inl (Set.mem_range_self 1)⟩ =
        ⟨cornerSW, Or.inl isArcBetween_upperSides.right_mem⟩ := by
  let A := Set.range g
  let P := Set.range h
  let B := sideTop ∪ sideLeft
  let Q := sideBottom ∪ sideRight
  have hA : IsArcBetween A (g 0) (g 1) := planar_embedded_path_isArcBetween g hg
  have hP : IsArcBetween P (g 0) (g 1) := by
    rw [h0, h1]
    exact planar_embedded_path_isArcBetween h hh
  have hB : IsArcBetween B cornerNE cornerSW := by
    simpa [B] using isArcBetween_upperSides
  have hQ : IsArcBetween Q cornerNE cornerSW := by
    simpa [Q] using isArcBetween_lowerSides.reverse
  have hmeet : A ∩ P = {g 0, g 1} := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨s, rfl⟩, ⟨t, hst⟩⟩
      rcases hmeet s t hst.symm with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · left
        exact congrArg g hs
      · right
        exact congrArg g hs
    · intro z hz
      rcases (by simpa using hz : z = g 0 ∨ z = g 1) with rfl | rfl
      · exact ⟨⟨0,rfl⟩, ⟨0,h0.symm⟩⟩
      · exact ⟨⟨1,rfl⟩, ⟨1,h1.symm⟩⟩
  have hmeetTarget : B ∩ Q = {cornerNE, cornerSW} := by
    apply Set.Subset.antisymm
    · intro z hz
      have hz' : z ∈ (sideTop ∪ sideLeft) ∧ z ∈
          (sideBottom ∪ sideRight) := hz
      rcases upperSides_meet_lowerSides z hz'.1 hz'.2 with rfl | rfl
      · simp
      · simp
    · intro z hz
      have hz' : z = cornerNE ∨ z = cornerSW := by simpa using hz
      rcases hz' with rfl | rfl
      · exact ⟨hB.left_mem, hQ.left_mem⟩
      · exact ⟨hB.right_mem, hQ.right_mem⟩
  obtain ⟨e, heQ, he0, he1⟩ :=
    exists_homeomorph_union_arcs_preserving_second hA hP hB hQ hmeet hmeetTarget
  exact ⟨e, heQ, he0, he1⟩

theorem planar_clean_pair_schoenflies_alignment
    (g h : C(Interval, Plane))
    (hg : Topology.IsEmbedding g) (hh : Topology.IsEmbedding h)
    (h0 : g 0 = h 0) (h1 : g 1 = h 1)
    (hmeet : ∀ s t, g s = h t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsphere : Set.range g ∪ Set.range h = Metric.sphere (0 : Plane) 1) :
    ∃ φ : Plane ≃ₜ Plane,
      φ '' Metric.sphere (0 : Plane) 1 = modelCurve ∧
      φ '' Metric.ball (0 : Plane) 1 = Plane.openSquare 0 1 ∧
      φ '' Metric.closedBall (0 : Plane) 1 = Plane.closedSquare 0 1 ∧
      φ '' Set.range g = sideTop ∪ sideLeft ∧
      φ '' Set.range h = sideBottom ∪ sideRight ∧
      φ (g 0) = cornerNE ∧ φ (g 1) = cornerSW := by
  obtain ⟨e, heQ, he0, he1⟩ :=
    planar_clean_pair_boundary_alignment g h hg hh h0 h1 hmeet
  let es : ↥(Metric.sphere (0 : Plane) 1) ≃ₜ ↥modelCurve :=
    (Homeomorph.setCongr hsphere.symm).trans
      (e.trans (Homeomorph.setCongr modelCurve_eq_sides.symm))
  obtain ⟨φ, hφ⟩ := jordan_schoenflies_of_homeomorph
    unit_sphere_isJordanCurve isJordanCurve_modelCurve es
  have hφsphere : φ '' Metric.sphere (0 : Plane) 1 = modelCurve := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hφ ⟨w, hw⟩]
      exact (es ⟨w, hw⟩).property
    · intro hz
      let w := es.symm ⟨z, hz⟩
      refine ⟨w.val, w.property, ?_⟩
      rw [hφ w]
      exact congrArg Subtype.val (es.apply_symm_apply ⟨z, hz⟩)
  have hφball : φ '' Metric.ball (0 : Plane) 1 = Plane.openSquare 0 1 := by
    rw [← inside_unit_sphere, CurveComplex.jordan_inside_homeomorph_image φ,
      hφsphere, inside_modelCurve]
  have hφclosed : φ '' Metric.closedBall (0 : Plane) 1 =
      Plane.closedSquare 0 1 := by
    rw [← Metric.ball_union_sphere, Set.image_union, hφball, hφsphere]
    rw [← inside_modelCurve]
    exact (Set.union_comm _ _).trans
      CurveComplex.LocalSurgery.actualModelSquareClosedRegion
  have hφh : φ '' Set.range h = sideBottom ∪ sideRight := by
    ext z
    constructor
    · rintro ⟨w, ⟨s, rfl⟩, rfl⟩
      have hw : h s ∈ Metric.sphere (0 : Plane) 1 := by
        rw [← hsphere]
        exact Or.inr (Set.mem_range_self s)
      rw [hφ ⟨h s, hw⟩]
      have heMem : es ⟨h s, hw⟩ ∈
          {z : modelCurve | z.val ∈ sideBottom ∪ sideRight} := by
        change (es ⟨h s, hw⟩).val ∈ sideBottom ∪ sideRight
        have he : (es ⟨h s, hw⟩ : Plane) =
            (e ⟨h s, Or.inr (Set.mem_range_self s)⟩ : Plane) := rfl
        rw [he]
        have himage : (e ⟨h s, Or.inr (Set.mem_range_self s)⟩ : Plane) ∈
            Subtype.val '' (e '' {z : ↥(Set.range g ∪ Set.range h) |
              z.val ∈ Set.range h}) :=
          ⟨e ⟨h s, Or.inr (Set.mem_range_self s)⟩,
            ⟨⟨h s, Or.inr (Set.mem_range_self s)⟩,
              Set.mem_range_self s, rfl⟩, rfl⟩
        rw [heQ] at himage
        exact himage
      exact heMem
    · intro hz
      have hzModel : z ∈ modelCurve := by
        rw [modelCurve_eq_sides]
        exact Or.inr hz
      have hzSphere : z ∈ φ '' Metric.sphere (0 : Plane) 1 := hφsphere.symm ▸ hzModel
      obtain ⟨w, hw, hzw⟩ := hzSphere
      let u : ↥(Set.range g ∪ Set.range h) :=
        ⟨w, hsphere ▸ hw⟩
      have hφu : (es ⟨w, hw⟩ : Plane) = z := by
        rw [← hzw]
        exact (hφ ⟨w, hw⟩).symm
      have huQ : (e u : Plane) ∈ sideBottom ∪ sideRight := by
        change (es ⟨w, hw⟩ : Plane) ∈ sideBottom ∪ sideRight
        rw [hφu]
        exact hz
      have huImage : (e u : Plane) ∈
          Subtype.val '' (e '' {v : ↥(Set.range g ∪ Set.range h) |
            v.val ∈ Set.range h}) := heQ.symm ▸ huQ
      obtain ⟨v, ⟨w', hw'h, hv⟩, hve⟩ := huImage
      have heq : e w' = e u := by
        apply Subtype.ext
        exact (congrArg Subtype.val hv).trans hve
      have hwu : w' = u := e.injective heq
      obtain ⟨s, hs⟩ := hw'h
      refine ⟨h s, ⟨s, rfl⟩, ?_⟩
      calc
        φ (h s) = φ w := congrArg φ (hs.trans (congrArg Subtype.val hwu))
        _ = z := hzw
  have hφ0 : φ (g 0) = cornerNE := by
    have hw : g 0 ∈ Metric.sphere (0 : Plane) 1 := by
      rw [← hsphere]
      exact Or.inl (Set.mem_range_self 0)
    rw [hφ ⟨g 0, hw⟩]
    exact congrArg Subtype.val he0
  have hφ1 : φ (g 1) = cornerSW := by
    have hw : g 1 ∈ Metric.sphere (0 : Plane) 1 := by
      rw [← hsphere]
      exact Or.inl (Set.mem_range_self 1)
    rw [hφ ⟨g 1, hw⟩]
    exact congrArg Subtype.val he1
  have hφg : φ '' Set.range g = sideTop ∪ sideLeft := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, ⟨s, rfl⟩, rfl⟩
      have hzModel : φ (g s) ∈ modelCurve := by
        rw [← hφsphere]
        exact ⟨g s, (hsphere ▸ Or.inl (Set.mem_range_self s)), rfl⟩
      rw [modelCurve_eq_sides] at hzModel
      rcases hzModel with hzB | hzQ
      · exact hzB
      · have hpre : g s ∈ Set.range h := by
          have hzImg : φ (g s) ∈ φ '' Set.range h := hφh.symm ▸ hzQ
          obtain ⟨w, hw, he⟩ := hzImg
          exact φ.injective he ▸ hw
        obtain ⟨t, ht⟩ := hpre
        rcases hmeet s t ht.symm with ⟨hs, _⟩ | ⟨hs, _⟩
        · simpa [hs, hφ0] using isArcBetween_upperSides.left_mem
        · simpa [hs, hφ1] using isArcBetween_upperSides.right_mem
    · intro z hzB
      have hzModel : z ∈ modelCurve := by
        rw [modelCurve_eq_sides]
        exact Or.inl hzB
      have hzImage : z ∈ φ '' Metric.sphere (0 : Plane) 1 := hφsphere.symm ▸ hzModel
      obtain ⟨w, hw, hzw⟩ := hzImage
      have hwUnion : w ∈ Set.range g ∪ Set.range h := hsphere ▸ hw
      rcases hwUnion with hwg | hwh
      · exact ⟨w, hwg, hzw⟩
      · have hzQ : z ∈ sideBottom ∪ sideRight := by
          rw [← hφh]
          exact ⟨w, hwh, hzw⟩
        have hzCorner : z = cornerNE ∨ z = cornerSW := by
          have hzInt : z ∈ (sideTop ∪ sideLeft) ∩
              (sideBottom ∪ sideRight) := ⟨hzB, hzQ⟩
          exact upperSides_meet_lowerSides z hzInt.1 hzInt.2
        rcases hzCorner with rfl | rfl
        · exact ⟨g 0, Set.mem_range_self 0, hφ0⟩
        · exact ⟨g 1, Set.mem_range_self 1, hφ1⟩
  exact ⟨φ, hφsphere, hφball, hφclosed, hφg, hφh, hφ0, hφ1⟩

end RegionalEmbeddedFamily
