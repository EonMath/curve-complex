import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.SquareLiftLogMonodromy
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.SquareLiftOpenImage

namespace CurveComplex.Hyperbolic
open Set Topology

theorem local_plane_homeomorphism_square_lift
    (h : OpenPartialHomeomorph ℂ ℂ) (hsource : (0 : ℂ) ∈ h.source)
    (hzero : h 0 = 0) :
    ∃ g : OpenPartialHomeomorph ℂ ℂ,
      (0 : ℂ) ∈ g.source ∧ g 0 = 0 ∧
      (∀ z ∈ g.source, z ^ 2 ∈ h.source ∧ (g z) ^ 2 = h (z ^ 2)) ∧
      (∀ z ∈ g.source, -z ∈ g.source ∧ g (-z) = -g z) := by
  classical
  obtain ⟨A, F, k, hk, hF, hmaps, heq, hperiod⟩ :=
    local_plane_homeomorphism_log_lift_unit_period h hsource hzero
  let R := Real.exp (A / 2)
  let r := R / 2
  have hR : 0 < R := Real.exp_pos _
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  let f := extendedSquareLift F
  have hcont : ContinuousOn f (Metric.ball (0 : ℂ) R) :=
    extendedSquareLift_continuousOn_ball h hsource hzero A F k hF heq hperiod
  have hinj : InjOn f (Metric.ball (0 : ℂ) R) :=
    extendedSquareLift_injective_on_ball h A F k hk hmaps heq hperiod
  have hclsub : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) R := by
    intro z hz
    exact lt_of_le_of_lt hz hrR
  letI : CompactSpace (Metric.closedBall (0 : ℂ) r) := inferInstance
  let fcl : Metric.closedBall (0 : ℂ) r → ℂ := fun z => f z.val
  have hfcl : Continuous fcl := continuousOn_iff_continuous_domRestrict.mp (hcont.mono hclsub)
  have hfclinj : Function.Injective fcl := by
    intro a b hab
    apply Subtype.ext
    exact hinj (hclsub a.property) (hclsub b.property) hab
  let U := Metric.ball (0 : ℂ) r
  let fb : U → ℂ := fun z => f z.val
  have hfb : IsEmbedding fb := (hfcl.isClosedEmbedding hfclinj).isEmbedding.comp
    (Topology.IsEmbedding.inclusion Metric.ball_subset_closedBall)
  have hUsub : U ⊆ Metric.ball (0 : ℂ) R := Metric.ball_subset_ball hrR.le
  have hneg : ∀ z ∈ U, -z ∈ U ∧ f (-z) = -f z := by
    intro z hz
    refine ⟨?_, extendedSquareLift_neg A F k hk hperiod z (hUsub hz)⟩
    simpa only [U, Metric.mem_ball, dist_zero_right, norm_neg] using hz
  have hmem : ∀ z ∈ U, z ^ 2 ∈ h.source := fun z hz =>
    extendedSquareLift_square_source h hsource A hmaps z (hUsub hz)
  have hsquare : ∀ z ∈ U, f z ^ 2 = h (z ^ 2) := fun z hz =>
    extendedSquareLift_square h hzero A F heq z (hUsub hz)
  have hopenimage : IsOpen (f '' U) := square_lift_symmetric_image_isOpen h f U
    Metric.isOpen_ball hmem hneg hsquare
  have hrange : Set.range fb = f '' U := by
    change Set.range (f ∘ Subtype.val) = _
    rw [Set.range_comp, Subtype.range_coe_subtype]
    rfl
  have hfbo : IsOpenEmbedding fb := ⟨hfb, by rw [hrange]; exact hopenimage⟩
  have hzU : (0 : ℂ) ∈ U := Metric.mem_ball_self hr
  letI : Nonempty U := ⟨⟨0, hzU⟩⟩
  let s : TopologicalSpace.Opens ℂ := ⟨U, Metric.isOpen_ball⟩
  let a := s.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty U)
  let b := hfbo.toOpenPartialHomeomorph fb
  let g := a.symm.trans b
  have hsourceg : g.source = U := by simp [g, a, b, s]
  have hvalue (z : ℂ) (hz : z ∈ g.source) : g z = f z := by
    have hzU : z ∈ U := hsourceg ▸ hz
    change fb (a.symm z) = f z
    have ht : z ∈ a.target := by simpa [a, s] using hzU
    exact congrArg f (a.right_inv ht)
  have hzg : (0 : ℂ) ∈ g.source := hsourceg.symm ▸ hzU
  refine ⟨g, hzg, ?_, ?_, ?_⟩
  · rw [hvalue 0 hzg]
    exact extendedSquareLift_zero F
  · intro z hz
    have hzU : z ∈ U := hsourceg ▸ hz
    rw [hvalue z hz]
    exact ⟨hmem z hzU, hsquare z hzU⟩
  · intro z hz
    have hzU : z ∈ U := hsourceg ▸ hz
    have hn := hneg z hzU
    have hnsource : -z ∈ g.source := hsourceg.symm ▸ hn.1
    refine ⟨hnsource, ?_⟩
    rw [hvalue _ hnsource, hvalue _ hz]
    exact hn.2

theorem local_plane_homeomorphism_square_lift_in_neighborhoods
    (h : OpenPartialHomeomorph ℂ ℂ) (hsource : (0 : ℂ) ∈ h.source)
    (hzero : h 0 = 0) (U V : Set ℂ) (hU : IsOpen U) (hV : IsOpen V)
    (hzeroU : (0 : ℂ) ∈ U) (hzeroV : (0 : ℂ) ∈ V) :
    ∃ g : OpenPartialHomeomorph ℂ ℂ,
      (0 : ℂ) ∈ g.source ∧ g 0 = 0 ∧ g.source ⊆ U ∧ g.target ⊆ V ∧
      (∀ z ∈ g.source, z ^ 2 ∈ h.source ∧ (g z) ^ 2 = h (z ^ 2)) ∧
      (∀ z ∈ g.source, -z ∈ g.source ∧ g (-z) = -g z) := by
  obtain ⟨g, hgs, hgzero, hgsquare, hgneg⟩ := local_plane_homeomorphism_square_lift h hsource hzero
  let W := (g.source ∩ g ⁻¹' V) ∩ U
  have hW : IsOpen W := (g.isOpen_inter_preimage hV).inter hU
  have hzW : (0 : ℂ) ∈ W := ⟨⟨hgs, by simpa only [Set.mem_preimage, hgzero] using hzeroV⟩, hzeroU⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hW 0 hzW
  let f := g.restrOpen (Metric.ball (0 : ℂ) r) Metric.isOpen_ball
  have hsrc : f.source = Metric.ball (0 : ℂ) r := by
    change g.source ∩ Metric.ball (0 : ℂ) r = Metric.ball (0 : ℂ) r
    exact Set.inter_eq_right.mpr (fun z hz => (hsub hz).1.1)
  have hzsrc : (0 : ℂ) ∈ f.source := hsrc.symm ▸ Metric.mem_ball_self hr
  have hsrcU : f.source ⊆ U := fun z hz => (hsub (hsrc ▸ hz)).2
  have htgtV : f.target ⊆ V := by
    rw [← f.image_source_eq_target]
    rintro v ⟨z, hz, rfl⟩
    exact (hsub (hsrc ▸ hz)).1.2
  refine ⟨f, hzsrc, hgzero, hsrcU, htgtV, ?_, ?_⟩
  · intro z hz
    exact hgsquare z (hsub (hsrc ▸ hz)).1.1
  · intro z hz
    have hzball : z ∈ Metric.ball (0 : ℂ) r := hsrc ▸ hz
    have hnball : -z ∈ Metric.ball (0 : ℂ) r := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hzball
    refine ⟨hsrc.symm ▸ hnball, ?_⟩
    exact (hgneg z (hsub hzball).1.1).2

end CurveComplex.Hyperbolic
