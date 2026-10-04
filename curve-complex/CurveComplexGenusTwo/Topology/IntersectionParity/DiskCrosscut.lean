import CurveComplexGenusTwo.Topology.IntersectionParity.SurfaceDiskInterior
import CurveComplexGenusTwo.Topology.IntersectionParity.ActualLoopSweep
import CurveComplexGenusTwo.Topology.IntersectionParity.RealIntervalCoordinates

open Set Topology

namespace CurveComplex.LocalSurgery

/-- A genuine embedded curve entering a disk and also leaving its closed image
has an actual embedded crosscut, whose interior stays in the disk interior. -/
theorem curve_entering_disk_has_crosscut
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (c : Curve S)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d) (hout : ¬ c.image ⊆ Set.range d)
    (hin : (c.image ∩ (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})).Nonempty) :
    ∃ f : C(Interval, S), Topology.IsEmbedding f ∧
      Set.range f ⊆ c.image ∧
      f 0 ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ∧
      f 1 ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ∧
      f '' Set.Ioo (0 : Interval) 1 ⊆
        d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
  classical
  let K : Set S := Set.range d
  let U : Set S := d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
  have hUopen : IsOpen U := embedded_surface_disk_interior_isOpen d hd
  have hKclosed : IsClosed K := (isCompact_range d.continuous).isClosed
  have hUK : U ⊆ K := Set.image_subset_range _ _
  obtain ⟨x, hxc, hxout⟩ := Set.not_subset.mp hout
  obtain ⟨z, rfl⟩ := hxc
  let γ := intervalCurveLoopFrom c z
  let realγ := realIntervalPath γ
  have hreal (u : Interval) : realγ u.val = γ u := by
    change γ (Set.projIcc 0 1 (by norm_num) u.val) = γ u
    rw [Set.projIcc_of_mem _ u.property]
  have hends : realγ 0 = c.map z ∧ realγ 1 = c.map z := by
    constructor
    · simpa [γ, intervalCurveLoopFrom, intervalCircleParameterFrom, intervalCircleParameter] using hreal (0 : Interval)
    · simpa [γ, intervalCurveLoopFrom, intervalCircleParameterFrom, intervalCircleParameter] using hreal (1 : Interval)
  have hγinj : Set.InjOn γ (Set.Ioo (0 : Interval) 1) := by
    intro u hu v hv heq
    have hcircle := c.embedded.injective heq
    change z * Circle.exp (2 * Real.pi * (u : ℝ)) = z * Circle.exp (2 * Real.pi * (v : ℝ)) at hcircle
    have hu1 : (u : ℝ) < 1 := hu.2
    have hv1 : (v : ℝ) < 1 := hv.2
    have hangle := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
      (show 2 * Real.pi * (u : ℝ) ∈ Set.Ico 0 (2 * Real.pi) from
        ⟨mul_nonneg (by positivity) hu.1.le, by nlinarith [Real.pi_pos, hu1]⟩)
      (show 2 * Real.pi * (v : ℝ) ∈ Set.Ico 0 (2 * Real.pi) from
        ⟨mul_nonneg (by positivity) hv.1.le, by nlinarith [Real.pi_pos, hv1]⟩)
      (mul_left_cancel hcircle)
    apply Subtype.ext
    nlinarith [Real.pi_pos]
  have hγrange : Set.range γ = c.image := by
    have hexpRange : Circle.exp '' Set.Icc 0 (2 * Real.pi) = Set.univ := by
      simpa only [zero_add, Circle.exp_surjective.range_eq] using
        Circle.periodic_exp.image_Icc Real.two_pi_pos (0 : ℝ)
    have hparameterSurj : Function.Surjective (intervalCircleParameterFrom z) := by
      intro v
      have hv : z⁻¹ * v ∈ Circle.exp '' Set.Icc 0 (2 * Real.pi) := hexpRange.symm ▸ Set.mem_univ _
      obtain ⟨θ, hθI, hθ⟩ := hv
      let u : Interval := ⟨θ / (2 * Real.pi), ⟨div_nonneg hθI.1 Real.two_pi_pos.le,
        (div_le_one Real.two_pi_pos).mpr hθI.2⟩⟩
      refine ⟨u, ?_⟩
      change z * Circle.exp (2 * Real.pi * (θ / (2 * Real.pi))) = v
      rw [mul_div_cancel₀ _ (ne_of_gt Real.two_pi_pos), hθ]
      simp
    change Set.range (c.map ∘ intervalCircleParameterFrom z) = Set.range c.map
    rw [Set.range_comp, hparameterSurj.range_eq, Set.image_univ]
  obtain ⟨y, hyc, hyU⟩ := hin
  obtain ⟨t, ht⟩ := hγrange.symm ▸ hyc
  have htU : realγ t.val ∈ U := by rw [hreal, ht]; exact hyU
  have htinside : 0 < t.val ∧ t.val < 1 := by
    constructor
    · by_contra h
      have ht0 : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt h) t.property.1)
      subst t
      have hb := hUK htU
      change realγ 0 ∈ K at hb
      rw [hends.1] at hb
      exact hxout hb
    · by_contra h
      have ht1 : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt h))
      subst t
      have hb := hUK htU
      change realγ 1 ∈ K at hb
      rw [hends.2] at hb
      exact hxout hb
  let L := Set.Icc (0 : ℝ) t.val ∩ realγ ⁻¹' Uᶜ
  let R := Set.Icc t.val (1 : ℝ) ∩ realγ ⁻¹' Uᶜ
  have hcomp : IsClosed (realγ ⁻¹' Uᶜ) := hUopen.isClosed_compl.preimage realγ.continuous
  have hLne : L.Nonempty := ⟨0, ⟨le_rfl, t.property.1⟩, by change realγ 0 ∉ U; rw [hends.1]; exact fun h => hxout (hUK h)⟩
  have hRne : R.Nonempty := ⟨1, ⟨t.property.2, le_rfl⟩, by change realγ 1 ∉ U; rw [hends.2]; exact fun h => hxout (hUK h)⟩
  obtain ⟨r, hrmem, hrmax⟩ := (isCompact_Icc.inter_right hcomp).exists_isGreatest hLne
  obtain ⟨s, hsmem, hsmin⟩ := (isCompact_Icc.inter_right hcomp).exists_isLeast hRne
  have hrt : r < t.val := lt_of_le_of_ne hrmem.1.2 (by intro heq; exact hrmem.2 (heq ▸ htU))
  have hts : t.val < s := lt_of_le_of_ne hsmem.1.1 (by intro heq; exact hsmem.2 (heq.symm ▸ htU))
  have hrs : r < s := hrt.trans hts
  have hinside (v : ℝ) (hv : v ∈ Set.Ioo r s) : realγ v ∈ U := by
    by_contra hvout
    by_cases hvt : v ≤ t.val
    · have hm : v ∈ L := ⟨⟨hrmem.1.1.trans hv.1.le, hvt⟩, hvout⟩
      exact (not_lt_of_ge (hrmax hm)) hv.1
    · have hm : v ∈ R := ⟨⟨le_of_not_ge hvt, hv.2.le.trans hsmem.1.2⟩, hvout⟩
      exact (not_lt_of_ge (hsmin hm)) hv.2
  have hclosedPre : IsClosed (realγ ⁻¹' K) := hKclosed.preimage realγ.continuous
  have hIccK : Set.Icc r s ⊆ realγ ⁻¹' K := by
    rw [← closure_Ioo hrs.ne]
    apply hclosedPre.closure_subset_iff.mpr
    exact fun v hv => hUK (hinside v hv)
  have hrK : realγ r ∈ K := hIccK ⟨le_rfl, hrs.le⟩
  have hsK : realγ s ∈ K := hIccK ⟨hrs.le, le_rfl⟩
  have hrpos : 0 < r := lt_of_le_of_ne hrmem.1.1 (by intro heq; rw [← heq, hends.1] at hrK; exact hxout hrK)
  have hsone : s < 1 := lt_of_le_of_ne hsmem.1.2 (by intro heq; rw [heq, hends.2] at hsK; exact hxout hsK)
  have hboundary (v : ℝ) (hvK : realγ v ∈ K) (hvU : realγ v ∉ U) :
      realγ v ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    obtain ⟨u, hu⟩ := hvK
    refine ⟨u, ?_, hu⟩
    have hn : ‖u.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using u.property
    have hnnot : ¬ ‖u.val‖ < 1 := by
      intro h
      exact hvU ⟨u, by change u.val ∈ Metric.ball 0 1; simpa only [Metric.mem_ball, dist_zero_right] using h, hu⟩
    change u.val ∈ Metric.sphere 0 1
    simpa only [Metric.mem_sphere, dist_zero_right] using le_antisymm hn (le_of_not_gt hnnot)
  let affine : Interval → ℝ := fun u => r + (s - r) * u.val
  let f : C(Interval, S) := ⟨realγ ∘ affine, realγ.continuous.comp (by fun_prop)⟩
  have haffine (u : Interval) : affine u ∈ Set.Icc r s := by
    dsimp [affine]
    constructor <;> nlinarith [u.property.1, u.property.2]
  have hfInjective : Function.Injective f := by
    intro u v heq
    let uI : Interval := ⟨affine u, ⟨hrpos.le.trans (haffine u).1, (haffine u).2.trans hsone.le⟩⟩
    let vI : Interval := ⟨affine v, ⟨hrpos.le.trans (haffine v).1, (haffine v).2.trans hsone.le⟩⟩
    have hui : uI ∈ Set.Ioo (0 : Interval) 1 := ⟨hrpos.trans_le (haffine u).1, (haffine u).2.trans_lt hsone⟩
    have hvi : vI ∈ Set.Ioo (0 : Interval) 1 := ⟨hrpos.trans_le (haffine v).1, (haffine v).2.trans_lt hsone⟩
    have heq' : γ uI = γ vI := by rw [← hreal uI, ← hreal vI]; exact heq
    have hv := congrArg Subtype.val (hγinj hui hvi heq')
    apply Subtype.ext
    dsimp [uI, vI, affine] at hv
    nlinarith
  refine ⟨f, (f.continuous.isClosedEmbedding hfInjective).isEmbedding, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨u, rfl⟩
    let uI : Interval := ⟨affine u, ⟨hrpos.le.trans (haffine u).1, (haffine u).2.trans hsone.le⟩⟩
    rw [← hγrange]
    exact ⟨uI, (hreal uI).symm⟩
  · change realγ (affine 0) ∈ _
    have h0 : affine 0 = r := by simp [affine]
    rw [h0]
    exact hboundary r hrK hrmem.2
  · change realγ (affine 1) ∈ _
    have h1 : affine 1 = s := by simp [affine]
    rw [h1]
    exact hboundary s hsK hsmem.2
  · rintro y ⟨u, hu, rfl⟩
    apply hinside
    change r < affine u ∧ affine u < s
    have hu0 : 0 < u.val := hu.1
    have hu1 : u.val < 1 := hu.2
    dsimp [affine]
    constructor <;> nlinarith

end CurveComplex.LocalSurgery
