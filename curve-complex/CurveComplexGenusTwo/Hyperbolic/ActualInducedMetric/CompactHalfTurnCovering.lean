import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfTurnLocalCover
import Mathlib.Topology.Covering.Basic

namespace CurveComplex.Hyperbolic
open Set Topology

theorem halfTurnMetricCone_projection_surjective : Function.Surjective toHalfTurnMetricCone := by
  intro w
  obtain ⟨⟨z⟩, hz⟩ := SeparationQuotient.surjective_mk w
  exact ⟨z, hz⟩

theorem halfTurnMetricCone_projection_continuous : Continuous toHalfTurnMetricCone := by
  exact (LipschitzWith.of_dist_le_mul (K := 1) (fun a b => by
    simpa using halfTurnMetricCone_projection_distance_le a b)).continuous

theorem halfTurnMetricCone_ball_image (z : H2) (r : ℝ) :
    toHalfTurnMetricCone '' Metric.ball z r = Metric.ball (toHalfTurnMetricCone z) r := by
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact lt_of_le_of_lt (halfTurnMetricCone_projection_distance_le a z) ha
  · intro hw
    obtain ⟨a, rfl⟩ := halfTurnMetricCone_projection_surjective w
    change dist (toHalfTurnMetricCone a) (toHalfTurnMetricCone z) < r at hw
    rw [halfTurnMetricCone_distance, min_lt_iff] at hw
    rcases hw with ha | ha
    · exact ⟨a, ha, rfl⟩
    · refine ⟨vertexHalfTurnEquiv a, ?_, halfTurnMetricCone_halfTurn_eq a⟩
      change dist (vertexHalfTurnEquiv a) z < r
      calc
        _ = dist (vertexHalfTurnEquiv a) (vertexHalfTurnEquiv (vertexHalfTurnEquiv z)) :=
          congrArg (dist (vertexHalfTurnEquiv a)) (vertexHalfTurn_involutive z).symm
        _ = dist a (vertexHalfTurnEquiv z) := vertexHalfTurnEquiv.dist_eq _ _
        _ < r := ha

theorem halfTurnMetricCone_projection_open : IsOpenMap toHalfTurnMetricCone := by
  intro U hU
  apply Metric.isOpen_iff.mpr
  rintro w ⟨z, hz, rfl⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU z hz
  refine ⟨r, hr, ?_⟩
  rw [← halfTurnMetricCone_ball_image z r]
  exact Set.image_mono hsub

theorem halfTurnMetricCone_projection_closed : IsClosedMap toHalfTurnMetricCone := by
  have hquot := halfTurnMetricCone_projection_open.isQuotientMap
    halfTurnMetricCone_projection_continuous halfTurnMetricCone_projection_surjective
  intro F hF
  apply hquot.isCoinducing.isClosed_preimage.mp
  have hpre : toHalfTurnMetricCone ⁻¹' (toHalfTurnMetricCone '' F) =
      F ∪ vertexHalfTurnEquiv ⁻¹' F := by
    ext z
    constructor
    · rintro ⟨a, ha, heq⟩
      rcases (halfTurnMetricCone_eq_iff a z).mp heq with heq | heq
      · exact Or.inl (heq ▸ ha)
      · apply Or.inr
        change vertexHalfTurnEquiv z ∈ F
        exact heq ▸ ha
    · rintro (hz | hz)
      · exact ⟨z, hz, rfl⟩
      · exact ⟨vertexHalfTurnEquiv z, hz, halfTurnMetricCone_halfTurn_eq z⟩
  rw [hpre]
  exact hF.union (hF.preimage vertexHalfTurnEquiv.continuous)

theorem halfTurnMetricCone_local_projection_chart (z : H2)
    (hz : vertexHalfTurnEquiv z ≠ z) :
    ∃ e : OpenPartialHomeomorph H2 HalfTurnMetricCone,
      z ∈ e.source ∧ ∀ a ∈ e.source, e a = toHalfTurnMetricCone a := by
  classical
  let r := dist z (vertexHalfTurnEquiv z) / 4
  have hr : 0 < r := by dsimp [r]; exact div_pos (dist_pos.mpr (Ne.symm hz)) (by norm_num)
  let U := Metric.ball z r
  have hcenter : z ∈ U := Metric.mem_ball_self hr
  let : Nonempty U := ⟨⟨z, hcenter⟩⟩
  let f : U → HalfTurnMetricCone := fun a => toHalfTurnMetricCone a.val
  have hf : Isometry f := halfTurnMetricCone_isometry_on_small_ball z hz
  have hrange : Set.range f = Metric.ball (toHalfTurnMetricCone z) r := by
    change Set.range (toHalfTurnMetricCone ∘ Subtype.val) = _
    rw [Set.range_comp, Subtype.range_coe_subtype]
    change toHalfTurnMetricCone '' Metric.ball z r = _
    exact halfTurnMetricCone_ball_image z r
  have hopen : IsOpenEmbedding f := ⟨hf.isEmbedding, by rw [hrange]; exact Metric.isOpen_ball⟩
  let s : TopologicalSpace.Opens H2 := ⟨U, Metric.isOpen_ball⟩
  let a := s.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty U)
  let b := hopen.toOpenPartialHomeomorph f
  refine ⟨a.symm.trans b, ?_, ?_⟩
  · simpa [a, b, s, U] using hcenter
  · intro v hv
    change f (a.symm v) = toHalfTurnMetricCone v
    have hvU : v ∈ U := by simpa [a, b, s] using hv
    have hvTarget : v ∈ a.target := by simpa [a, s] using hvU
    have hval : (a.symm v).val = v := a.right_inv hvTarget
    exact congrArg toHalfTurnMetricCone hval

theorem halfTurnMetricCone_punctured_covering (p : H2) (hp : p.re = 0) (hi : p.im = 1) :
    IsCoveringMapOn toHalfTurnMetricCone {toHalfTurnMetricCone p}ᶜ := by
  apply halfTurnMetricCone_projection_closed.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro w hw
    obtain ⟨a, rfl⟩ := halfTurnMetricCone_projection_surjective w
    apply (Set.finite_singleton a |>.union (Set.finite_singleton (vertexHalfTurnEquiv a))).subset
    intro z hz
    exact (halfTurnMetricCone_eq_iff z a).mp hz
  · intro z hz
    have hzne : vertexHalfTurnEquiv z ≠ z := by
      intro heq
      obtain ⟨hzre, hzim⟩ := vertexHalfTurn_fixed_iff z |>.mp heq
      have hzp : z = p := UpperHalfPlane.ext_re_im (hzre.trans hp.symm) (hzim.trans hi.symm)
      exact hz (by change toHalfTurnMetricCone z = toHalfTurnMetricCone p; rw [hzp])
    obtain ⟨e, hze, he⟩ := halfTurnMetricCone_local_projection_chart z hzne
    have heq : e.source.domRestrict toHalfTurnMetricCone = e.source.domRestrict e := by
      funext a
      exact (he a.val a.property).symm
    have hInj : Set.InjOn toHalfTurnMetricCone e.source := by
      intro a ha b hb hab
      apply e.injOn ha hb
      rw [he a ha, he b hb]
      exact hab
    have hopen : IsOpenMap (e.source.domRestrict toHalfTurnMetricCone) := by
      rw [heq]
      exact e.isOpenEmbedding_restrict.isOpenMap
    exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict hInj.toPartialEquiv
      halfTurnMetricCone_projection_continuous.continuousOn hopen e.open_source, hze, rfl⟩

end CurveComplex.Hyperbolic
