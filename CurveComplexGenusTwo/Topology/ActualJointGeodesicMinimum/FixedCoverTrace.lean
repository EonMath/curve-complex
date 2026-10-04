import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.FixedCoverLines
import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.Providers
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.OriginalLoopDefinitions
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting


namespace CurveComplex.Hyperbolic.JointMinimum
open Set Topology CurveComplex.LocalSurgery
open scoped Manifold UpperHalfPlane
section Surface
variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem fixed_cover_geodesic_local_single_line_trace
    (H : ClosedHyperbolicMetric E) (base : E)
    (p : H2 → connectedComponent base) (hp : IsCoveringMap p)
    (hlocal : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ w ∈ U,
        @dist E H.metric.toDist (p y).val (p w).val = dist y w)
    (c : Curve E) (L : ℝ → H2) (hL : Isometry L)
    (hproject : Set.range (fun t => (p (L t)).val) = c.image) :
    ∀ z ∈ Set.range L, ∃ U : Set H2, IsOpen U ∧ z ∈ U ∧
      ∀ y ∈ U, (p y).val ∈ c.image ↔ y ∈ Set.range L := by
  classical
  have hproj (t : ℝ) : (p (L t)).val ∈ c.image := by
    rw [← hproject]
    exact Set.mem_range_self t
  let ce : Circle ≃ₜ c.image := c.embedded.toHomeomorph
  let α : C(ℝ, Circle) :=
    ⟨fun t => ce.symm ⟨(p (L t)).val, hproj t⟩,
      ce.symm.continuous.comp ((continuous_subtype_val.comp
        (hp.continuous.comp hL.continuous)).subtype_mk _)⟩
  obtain ⟨a, ha⟩ := Circle.exp_surjective (α 0)
  obtain ⟨q, hq, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts α 0 a ha
  have hclock (t : ℝ) : c.map (Circle.exp (q t)) = (p (L t)).val := by
    have he := congrFun hq.2 t
    change Circle.exp (q t) = ce.symm ⟨(p (L t)).val, hproj t⟩ at he
    rw [he]
    exact congrArg Subtype.val (ce.apply_symm_apply _)
  rintro z ⟨t, rfl⟩
  obtain ⟨S, hS, htS, hSinj⟩ := hp.isLocalHomeomorph.isLocallyInjective (L t)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hS.preimage hL.continuous) t htS
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hsegment (u : ℝ) (hu : u ∈ Icc (t-r) (t+r)) : L u ∈ S := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hbound : |u-t| ≤ r := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    exact hbound.trans_lt (by dsimp [r]; linarith)
  have hqi : Set.InjOn q (Icc (t-r) (t+r)) := by
    intro u hu v hv heq
    apply hL.injective
    apply hSinj (hsegment u hu) (hsegment v hv)
    apply Subtype.ext
    rw [← hclock u, ← hclock v, heq]
  have hopenq : IsOpen (q '' Ioo (t-r) (t+r)) := by
    rcases q.continuous.continuousOn.strictMonoOn_of_injOn_Icc'
      (by linarith : t-r ≤ t+r) hqi with hm | hm
    · rw [q.continuous.continuousOn.image_Ioo_of_strictMonoOn (by linarith) hm]
      exact isOpen_Ioo
    · rw [q.continuous.continuousOn.image_Ioo_of_strictAntiOn (by linarith) hm]
      exact isOpen_Ioo
  let V : Set c.image := ce '' (Circle.exp '' (q '' Ioo (t-r) (t+r)))
  have hV : IsOpen V := ce.isOpenMap _ (Circle.isCoveringMap_exp.isLocalHomeomorph.isOpenMap _ hopenq)
  obtain ⟨W, hW, hWV⟩ := (IsInducing.subtypeVal.isOpen_iff).mp hV
  have htV : (⟨(p (L t)).val, hproj t⟩ : c.image) ∈ V := by
    refine ⟨Circle.exp (q t), ⟨q t, ⟨t, ⟨by linarith, by linarith⟩, rfl⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    exact hclock t
  refine ⟨S ∩ (fun y : H2 => (p y).val) ⁻¹' W,
    hS.inter (hW.preimage (continuous_subtype_val.comp hp.continuous)),
    ⟨htS, ?_⟩, ?_⟩
  · have h := htV
    rw [← hWV] at h
    exact h
  · intro y hy
    constructor
    · intro hyc
      have hyV : (⟨(p y).val, hyc⟩ : c.image) ∈ V := by
        rw [← hWV]
        exact hy.2
      obtain ⟨v, ⟨w, ⟨u, hu, huq⟩, hwv⟩, hvy⟩ := hyV
      have hpu : p (L u) = p y := by
        apply Subtype.ext
        calc
          (p (L u)).val = c.map (Circle.exp (q u)) := (hclock u).symm
          _ = (p y).val := by
            rw [huq, hwv]
            exact congrArg Subtype.val hvy
      exact ⟨u, hSinj (hsegment u (Ioo_subset_Icc_self hu)) hy.1 hpu⟩
    · rintro ⟨u, rfl⟩
      exact hproj u

theorem fixed_cover_geodesic_path_confined_to_line
    (H : ClosedHyperbolicMetric E) (c : Curve E) (base : E)
    (hgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic c.image)
    (p : H2 → connectedComponent base) (hp : IsCoveringMap p)
    (hlocal : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ w ∈ U,
        @dist E H.metric.toDist (p y).val (p w).val = dist y w)
    (h : C(Interval, H2)) (himage : ∀ t, (p (h t)).val ∈ c.image) :
    ∃ L : ℝ → H2, Isometry L ∧ Set.range h ⊆ Set.range L ∧
      Set.range (fun t => (p (L t)).val) = c.image := by
  classical
  letI : MetricSpace E := H.metric
  let A := connectedComponent base
  let componentMetric : MetricSpace A :=
    MetricSpace.induced Subtype.val Subtype.val_injective H.metric
  have componentMetricTopology :
      componentMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace A) := by
    change TopologicalSpace.induced Subtype.val
      H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced Subtype.val (inferInstance : TopologicalSpace E)
    rw [H.compatible]
  letI : MetricSpace A := componentMetric.replaceTopology componentMetricTopology.symm
  obtain ⟨path, period, hperiod, hcont, hperiodic, hrange, hunit⟩ := hgeo
  have hconnected : IsConnected c.image := by
    change IsConnected (Set.range c.map)
    exact isConnected_range c.embedded.continuous
  have himageA : Set.range path ⊆ A := by
    rw [hrange]
    have hcomp := connectedComponent_eq (p (h 0)).property
    change c.image ⊆ connectedComponent base
    rw [hcomp]
    exact hconnected.subset_connectedComponent (himage 0)
  let γA : C(ℝ, A) :=
    ⟨fun t => ⟨path t, himageA (Set.mem_range_self t)⟩, hcont.subtype_mk _⟩
  have hunitA : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s u : ℝ, |s-t| < ε → |u-t| < ε →
        dist (γA s) (γA u) = |s-u| := by
    intro t
    obtain ⟨ε, hε, hm⟩ := hunit t
    refine ⟨ε, hε, ?_⟩
    intro s u hs hu
    change @dist E H.metric.toDist (path s) (path u) = |s-u|
    exact hm s u hs hu
  obtain ⟨axes, haxes, hprojection, hanchors, hunion⟩ :=
    developed_lines_project_onto_path p hp (by
      intro x
      obtain ⟨U, hU, hxU, hm⟩ := hlocal x
      exact ⟨U, hU, hxU, by
        intro y hy z hz
        change @dist E H.metric.toDist (p y).val (p z).val = dist y z
        exact hm y hy z hz⟩) γA hunitA
  have hγimage : Subtype.val '' Set.range γA = c.image := by
    rw [←Set.range_comp]
    have hpath : (Subtype.val ∘ γA) = path := rfl
    rw [hpath]
    exact hrange
  have hzero : p (h 0) ∈ Set.range γA := by
    have hz : (p (h 0)).val ∈ Subtype.val '' Set.range γA := by
      rw [hγimage]
      exact himage 0
    obtain ⟨u, hu, he⟩ := hz
    have heu : u = p (h 0) := Subtype.ext he
    exact heu ▸ hu
  let i : {x : H2 // p x ∈ Set.range γA} := ⟨h 0, hzero⟩
  let L : ℝ → H2 := axes i
  have hL : Isometry L := haxes i
  have hproject : Set.range (fun t => (p (L t)).val) = c.image := by
    have he : (fun t => (p (L t)).val) = Subtype.val ∘ γA := by
      funext t
      exact congrArg Subtype.val (hprojection i t)
    rw [he, Set.range_comp]
    exact hγimage
  have htrace := fixed_cover_geodesic_local_single_line_trace H base p hp hlocal c L hL hproject
  let S : Set Interval := h ⁻¹' Set.range L
  have hclosed : IsClosed S := hL.isClosedEmbedding.isClosed_range.preimage h.continuous
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨U, hU, htU, he⟩ := htrace (h t) ht
    apply Filter.mem_of_superset ((hU.preimage h.continuous).mem_nhds htU)
    intro u hu
    exact (he (h u) hu).mp (himage u)
  have hS : S = Set.univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ
    ⟨0, hanchors i⟩
  refine ⟨L, hL, ?_, hproject⟩
  rintro y ⟨t, rfl⟩
  have ht : t ∈ S := by rw [hS]; exact Set.mem_univ _
  exact ht

end Surface
end CurveComplex.Hyperbolic.JointMinimum
