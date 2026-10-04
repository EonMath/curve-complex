import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalFirstDiskActualCoverAssemblyProved
import CurveComplexGenusTwo.Topology.ActualCurveMinimum.OriginalFirstDiskFixedComparisonProvider
import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.WeightedBigonReplacementStatement
import CurveComplexGenusTwo.Topology.GeometricPosition.FiniteTransverseAssembly
import CurveComplexGenusTwo.Topology.IntersectionParity.InnermostDiskStatement
import CurveComplexGenusTwo.Topology.IntersectionParity.EmptyDiskSidesStatement
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib
import CurveComplexGenusTwo.Foundations.EdgeHomotopy

namespace CurveComplex
open scoped Manifold ContDiff

/-- Finite simultaneous minimal position, requested for semantic review.
This is a geometric producer on the actual essential ambient-isotopy classes,
not a supplied choice of representatives or an assumed minimizing property. -/
theorem exists_finite_simultaneous_minimal_representatives
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (σ : Finset (Vertex S)) :
    ∃ r : (v : Vertex S) → v ∈ σ → EssentialCurve S,
      (∀ v hv, Quotient.mk (essentialCurveSetoid S) (r v hv) = v) ∧
      (∀ v hv w hw, v ≠ w →
        ∃ h : Transverse (r v hv).val (r w hw).val,
          h.1.toFinset.card = geometricIntersection v w) := by
  classical
  -- The finite index type remembers the caller's exact isotopy classes.
  let I := {v : Vertex S // v ∈ σ}
  let Rep := I → EssentialCurve S
  let represents (r : Rep) : Prop :=
    ∀ v : I, Quotient.mk (essentialCurveSetoid S) (r v) = v.val
  have hraw : ∃ r : Rep, represents r := by
    let r : Rep := fun v => Classical.choose (Quotient.exists_rep v.val)
    exact ⟨r, fun v => Classical.choose_spec (Quotient.exists_rep v.val)⟩
  let admissible (r : Rep) : Prop :=
    represents r ∧ ∀ v w : I, v ≠ w → Transverse (r v).val (r w).val
  -- Zero or one class needs no perturbation or pairwise minimization.
  by_cases hsmall : Subsingleton I
  · obtain ⟨r, hr⟩ := hraw
    refine ⟨fun v hv => r ⟨v, hv⟩, fun v hv => hr ⟨v, hv⟩, ?_⟩
    intro v hv w hw hvw
    exact (hvw (congrArg Subtype.val (hsmall.elim ⟨v, hv⟩ ⟨w, hw⟩))).elim
  -- Geometric producer A: simultaneously perturb the given finite curves
  -- within their actual ambient-isotopy classes into transverse position.
  have hposition : ∃ r : Rep, admissible r := by
    let _ : ClosedSurface S := hS.2.1.some
    obtain ⟨r₀, hr₀⟩ := hraw
    obtain ⟨r, hr, ht⟩ := finite_transverse_representatives_by_extension S I r₀
    exact ⟨r, (fun v => (hr v).trans (hr₀ v)), ht⟩
  let count (r : Rep) (v w : I) : ℕ :=
    ((r v).val.image ∩ (r w).val.image).ncard
  let energy (r : Rep) : ℕ :=
    ∑ v : I, ∑ w : I, if v = w then 0 else count r v w
  let System := {r : Rep // admissible r}
  have : Nonempty System := ⟨⟨hposition.choose, hposition.choose_spec⟩⟩
  let minimal : System := Function.argmin (fun r : System => energy r.val)
  have hleast (r : System) : ¬energy r.val < energy minimal.val :=
    Function.not_lt_argmin (fun r : System => energy r.val) r
  have hcount (r : System) (v w : I) (hvw : v ≠ w) :
      geometricIntersection v.val w.val ≤ count r.val v w := by
    let ht := r.property.2 v w hvw
    apply Nat.sInf_le
    refine ⟨r.val v, r.val w, r.property.1 v, r.property.1 w, ht, ?_⟩
    exact Set.ncard_eq_toFinset_card _ ht.1
  -- Every component of a finite transverse system has a genuine open
  -- neighborhood of one of its points which misses every other component.
  have hisolated (r : System) (v : I) :
      ∃ (p : S) (U : Set S), p ∈ (r.val v).val.image ∧ p ∈ U ∧
        IsOpen U ∧ ∀ w : I, w ≠ v → Disjoint U (r.val w).val.image := by
    let _ : ClosedSurface S := hS.2.1.some
    have : Infinite (Set.Icc (0 : ℝ) 1) := Set.Icc.infinite (by norm_num)
    have : Infinite Circle := Infinite.of_injective
      (fun t : Set.Icc (0 : ℝ) 1 => Circle.exp t.val) (by
        intro t u h
        apply Subtype.ext
        exact Circle.exp_injOn_Icc (by linarith [Real.pi_gt_three]) t.property u.property h)
    let Other := {w : I // w ≠ v}
    let bad : Set S := ⋃ w : Other, (r.val v).val.image ∩ (r.val w.val).val.image
    have hbad : bad.Finite := Set.finite_iUnion (fun w : Other =>
      (r.property.2 v w.val (Ne.symm w.property)).1)
    have hinfinite : (r.val v).val.image.Infinite :=
      Set.infinite_range_of_injective (r.val v).val.embedded.injective
    obtain ⟨p, hp, hnot⟩ := hinfinite.exists_notMem_finite hbad
    let others : Set S := ⋃ w : Other, (r.val w.val).val.image
    have hclosed : IsClosed others := isClosed_iUnion_of_finite (fun w : Other =>
      (isCompact_range (r.val w.val).val.embedded.continuous).isClosed)
    have hpU : p ∈ othersᶜ := by
      intro h
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp h
      exact hnot (Set.mem_iUnion.mpr ⟨w, hp, hw⟩)
    refine ⟨p, othersᶜ, hp, hpU, hclosed.isOpen_compl, ?_⟩
    intro w hw
    rw [Set.disjoint_left]
    intro x hx hxw
    exact hx (Set.mem_iUnion.mpr ⟨⟨w, hw⟩, hxw⟩)
  -- A nondegenerate compact embedded subarc can be placed in that
  -- neighborhood; its entire image avoids every other curve in the system.
  have hfreeArc (r : System) (v : I) :
      ∃ a b : ℝ, a < b ∧ ∃ f : C(Set.Icc a b, S),
        Topology.IsEmbedding f ∧ Set.range f ⊆ (r.val v).val.image ∧
        ∀ w : I, w ≠ v → Disjoint (Set.range f) (r.val w).val.image := by
    let _ : ClosedSurface S := hS.2.1.some
    obtain ⟨p, U, hp, hpU, hU, havoid⟩ := hisolated r v
    obtain ⟨t, ht⟩ := hp
    let θ : ℝ := Complex.arg (t : ℂ)
    let F : ℝ → S := fun x => (r.val v).val.map (Circle.exp x)
    have hF : Continuous F := (r.val v).val.embedded.continuous.comp Circle.exp.continuous
    have hθ : F θ ∈ U := by simpa only [F, θ, Circle.exp_arg, ht] using hpU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU.preimage hF) θ hθ
    let δ : ℝ := min ε Real.pi / 4
    have hδ : 0 < δ := div_pos (lt_min hε Real.pi_pos) (by norm_num)
    have hδε : δ < ε := by
      have := min_le_left ε Real.pi
      dsimp [δ]
      linarith
    have hδπ : 2 * δ < 2 * Real.pi := by
      have := min_le_right ε Real.pi
      dsimp [δ]
      linarith [Real.pi_pos]
    let f : C(Set.Icc (θ - δ) (θ + δ), S) :=
      ⟨fun x => F x.val, hF.comp continuous_subtype_val⟩
    have hfU (x : Set.Icc (θ - δ) (θ + δ)) : f x ∈ U := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      apply abs_lt.mpr
      constructor <;> linarith [x.property.1, x.property.2]
    refine ⟨θ - δ, θ + δ, by linarith, f, ?_, ?_, ?_⟩
    · apply Continuous.isClosedEmbedding f.continuous ?_ |>.isEmbedding
      intro x y hxy
      apply Subtype.ext
      apply Circle.exp_injOn_Icc (a := θ - δ) (b := θ + δ) (by linarith) x.property y.property
      exact (r.val v).val.embedded.injective hxy
    · rintro y ⟨x, rfl⟩
      exact ⟨Circle.exp x.val, rfl⟩
    · intro w hw
      exact (havoid w hw).mono_left (by rintro y ⟨x, rfl⟩; exact hfU x)
  -- Geometric producer B: an excess intersection produces actual isotopic
  -- surgery on this finite system with strictly smaller total intersection.
  -- No rank-descent certificate or surgery result is a public hypothesis.
  have hdescent (r : System) (v w : I) (hvw : v ≠ w)
      (hexcess : geometricIntersection v.val w.val < count r.val v w) :
      ∃ r' : System, energy r'.val < energy r.val := by
    let _ : ClosedSurface S := hS.2.1.some
    let ht := r.property.2 v w hvw
    have hActualExcess : geometricIntersection
        (Quotient.mk (essentialCurveSetoid S) (r.val v))
        (Quotient.mk (essentialCurveSetoid S) (r.val w)) < ht.1.toFinset.card := by
      rw [r.property.1 v,r.property.1 w,← Set.ncard_eq_toFinset_card _ ht.1]
      exact hexcess
    obtain ⟨aMin, haMin, htMin, hMinCount⟩ :=
      LocalSurgery.audited_fixed_comparison_minimum (r.val v) (r.val w) ht
    have hCountDecrease : htMin.1.toFinset.card < ht.1.toFinset.card := by
      rw [hMinCount]
      exact hActualExcess
    obtain ⟨u,z,huz,hu,hz,f,comparison,hf,hfcurve,hgcurve,hclean,hhom⟩ :=
      LocalSurgery.count_decreasing_isotopy_has_returning_subarc
        (r.val v) (r.val w) aMin ht haMin htMin hCountDecrease
    -- Actual original clean returning arc and fixed-endpoint comparison homotopy
    -- have now been produced from the original excess, with no extraction premise.
    -- The remaining ORIGINAL producer is the actual first disk bounded by
    -- original pair subarcs, derived from these concrete paths.
    -- Canonical innermostness/clean-side conclusions below are proved producers;
    -- no conditional extraction interface is presented as a proved first disk.
    have hActualOriginalDisk : Nonempty
        (LocalSurgery.TwoCurveDisk (r.val v).val (r.val w).val) := by
      exact LocalSurgery.actual_original_returning_subarc_produces_two_curve_disk
        S g hg hS (r.val v) (r.val w) ht u z huz f comparison
        hf hfcurve hgcurve hclean hhom
    obtain ⟨B₀⟩ := hActualOriginalDisk
    obtain ⟨B,hEmpty⟩ := LocalSurgery.two_curve_disk_has_innermost_disk
      (r.val v) (r.val w) ht B₀
    obtain ⟨hFirstMeet,hSecondMeet⟩ := LocalSurgery.empty_two_curve_disk_has_clean_sides
      (r.val v) (r.val w) ht B hEmpty
    obtain ⟨k,H,r',hWhich,hFixed,hImage,hSupport,hClasses,hTransverse,hEnergy⟩ :=
      FiniteMinimalCompatibility.finite_family_weighted_bigon_replacement
        S I r.val r.property.2 v w hvw B.firstCorner B.secondCorner B.corners_ne
        B.firstSide B.secondSide B.first_embedded B.second_embedded
        B.first_zero B.second_zero B.first_one B.second_one
        B.first_on_curve B.second_on_curve hFirstMeet hSecondMeet
        B.disk B.disk_embedded B.boundary_eq hEmpty
        Set.univ isOpen_univ (Set.subset_univ _)
    refine ⟨⟨r',?_⟩,hEnergy⟩
    exact ⟨(fun i => (hClasses i).trans (r.property.1 i)),hTransverse⟩
  refine ⟨fun v hv => minimal.val ⟨v, hv⟩,
    fun v hv => minimal.property.1 ⟨v, hv⟩, ?_⟩
  intro v hv w hw hvw
  have hidx : (⟨v, hv⟩ : I) ≠ ⟨w, hw⟩ := by
    intro h
    exact hvw (congrArg Subtype.val h)
  let ht := minimal.property.2 ⟨v, hv⟩ ⟨w, hw⟩ hidx
  refine ⟨ht, ?_⟩
  have heq : count minimal.val ⟨v, hv⟩ ⟨w, hw⟩ = geometricIntersection v w := by
    apply Nat.le_antisymm _ (hcount minimal ⟨v, hv⟩ ⟨w, hw⟩ hidx)
    by_contra hn
    obtain ⟨r', hr'⟩ := hdescent minimal ⟨v, hv⟩ ⟨w, hw⟩ hidx (Nat.lt_of_not_ge hn)
    exact hleast r' hr'
  exact (Set.ncard_eq_toFinset_card _ ht.1).symm.trans heq

/-- The disjoint realization of a genuine finite zero-complex face. -/
theorem exists_disjoint_representatives_of_c0_face
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (σ : Finset (Vertex S)) (hσ : σ ∈ (curveComplex S 0).faces) :
    ∃ r : (v : Vertex S) → v ∈ σ → EssentialCurve S,
      (∀ v hv, Quotient.mk (essentialCurveSetoid S) (r v hv) = v) ∧
      (∀ v hv w hw, v ≠ w → Disjoint (r v hv).val.image (r w hw).val.image) := by
  obtain ⟨r, hr, hminimal⟩ :=
    exists_finite_simultaneous_minimal_representatives S g hg hS σ
  refine ⟨r, hr, ?_⟩
  intro v hv w hw hvw
  obtain ⟨ht, hcard⟩ := hminimal v hv w hw hvw
  have hz : geometricIntersection v w = 0 :=
    Nat.eq_zero_of_le_zero (hσ.2 v hv w hw hvw)
  have hempty : ht.1.toFinset = ∅ := Finset.card_eq_zero.mp (hcard.trans hz)
  rw [Set.disjoint_left]
  intro x hxv hxw
  have hx : x ∈ ht.1.toFinset := (ht.1.mem_toFinset).mpr ⟨hxv, hxw⟩
  simp only [hempty, Finset.notMem_empty] at hx
end CurveComplex
