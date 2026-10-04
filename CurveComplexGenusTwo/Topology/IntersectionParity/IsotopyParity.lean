import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import CurveComplexGenusTwo.Topology.IntersectionParity.ActualLoopSweep
import CurveComplexGenusTwo.Topology.IntersectionParity.CutCoverDefinitions
import CurveComplexGenusTwo.Topology.IntersectionParity.CutCoverLifts
import CurveComplexGenusTwo.Topology.IntersectionParity.CutCoverCount
import CurveComplexGenusTwo.Topology.IntersectionParity.CutCoverExistence
import CurveComplexGenusTwo.Topology.IntersectionParity.CoverEndpoint
namespace CurveComplex.LocalSurgery

/-- Unproved candidate for review: one curve moves by an actual ambient isotopy,
while the other is fixed; both endpoint pairs have genuine finite crossings.
This is a geometric proof obligation, not an external assumption. -/
theorem transverse_intersection_mod_two_ambient_isotopy
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a b c : Curve S) (hab : Transverse a b) (hac : Transverse a c)
    (H : AmbientIsotopy S) (hH : H.finalMap '' b.image = c.image) :
    Nat.ModEq 2 hab.1.toFinset.card hac.1.toFinset.card := by
  classical
  obtain ⟨e, he⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
  have hfinal : H.finalMap = e := (funext he).symm
  let b' : Curve S := ⟨e ∘ b.map, e.isEmbedding.comp b.embedded⟩
  have hb'image : b'.image = c.image := by
    change Set.range (e ∘ b.map) = c.image
    rw [Set.range_comp]
    change (e : S → S) '' b.image = c.image
    rw [← hfinal]
    exact hH
  have hab' : Transverse a b' := by
    simpa only [Transverse, CrossesAt, hb'image] using hac
  have hfinite₀ : {z : Circle | b.map z ∈ a.image}.Finite := by
    have hpre := hab.1.preimage b.embedded.injective.injOn
    have hset : b.map ⁻¹' (a.image ∩ b.image) = {z | b.map z ∈ a.image} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact and_iff_left ⟨z, rfl⟩
    rwa [hset] at hpre
  have hfinite₁ : {z : Circle | b'.map z ∈ a.image}.Finite := by
    have hpre := hab'.1.preimage b'.embedded.injective.injOn
    have hset : b'.map ⁻¹' (a.image ∩ b'.image) = {z | b'.map z ∈ a.image} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact and_iff_left ⟨z, rfl⟩
    rwa [hset] at hpre
  have hbase : ∃ z : Circle, b.map z ∉ a.image ∧ b'.map z ∉ a.image := by
    by_contra h
    push Not at h
    have huniv : {z : Circle | b.map z ∈ a.image} ∪
        {z : Circle | b'.map z ∈ a.image} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      rcases em (b.map z ∈ a.image) with hz | hz
      · exact Or.inl hz
      · exact Or.inr (h z hz)
    have hfin : (Set.univ : Set Circle).Finite := by
      rw [← huniv]
      exact hfinite₀.union hfinite₁
    let : Finite Circle := Set.finite_univ_iff.mp hfin
    let : DiscreteTopology Circle := inferInstance
    let : Subsingleton Circle := subsingleton_of_preconnected_totallyDisconnected
    have hcontra := congrArg Subtype.val
      (Subsingleton.elim (1 : Circle) (⟨(-1 : ℂ), by change dist (-1 : ℂ) 0 = 1; simp [dist_eq_norm]⟩ : Circle))
    norm_num at hcontra
  obtain ⟨z, hz₀, hz₁⟩ := hbase
  let sweep := ambientCurveLoopSweepFrom b H z
  have hloop : ∀ t : unitInterval, sweep (t, 0) = sweep (t, 1) := by
    intro t
    simp [sweep, ambientCurveLoopSweepFrom, intervalCurveLoopFrom,
      intervalCircleParameterFrom, intervalCircleParameter]
  have hcover : Nonempty (CurveCutCover a) := by
    exact embedded_curve_has_cut_double_cover a
  obtain ⟨A⟩ := hcover
  let cov : IsCoveringMap A.core.proj :=
    FiberBundle.isCoveringMap (F := ZMod 2) (E := A.core.Fiber)
  let start : A.core.TotalSpace := ⟨b.map z, (0 : ZMod 2)⟩
  have hstart : intervalCurveLoopFrom b z 0 = A.core.proj start := by
    simp [intervalCurveLoopFrom, intervalCircleParameterFrom,
      intervalCircleParameter, start]
  let f := cov.liftPath (intervalCurveLoopFrom b z) start hstart
  have hf : A.core.proj ∘ f = intervalCurveLoopFrom b z :=
    cov.liftPath_lifts (intervalCurveLoopFrom b z) start hstart
  have hzero : ∀ u : unitInterval, sweep (0, u) = A.core.proj (f u) := by
    intro u
    have hfu : A.core.proj (f u) = intervalCurveLoopFrom b z u := congrFun hf u
    rw [hfu]
    exact H.at_zero _
  let L := cov.liftHomotopy sweep f hzero
  let g : C(unitInterval, A.core.TotalSpace) :=
    ⟨fun u => L (1, u), L.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hg : A.core.proj ∘ g = intervalCurveLoopFrom b' z := by
    funext u
    have hlifts : A.core.proj (L (1, u)) = sweep (1, u) :=
      congrFun (cov.liftHomotopy_lifts sweep f hzero) (1, u)
    change A.core.proj (L (1, u)) = intervalCurveLoopFrom b' z u
    rw [hlifts]
    change H.finalMap (b.map (intervalCircleParameterFrom z u)) =
      e (b.map (intervalCircleParameterFrom z u))
    rw [hfinal]
  have hclosed : g 0 = g 1 ↔ f 0 = f 1 :=
    covering_lift_loop_closure_invariant cov sweep hloop f hzero
  have countClosure (q : Curve S) (haq : Transverse a q)
      (w : Circle) (hw : q.map w ∉ a.image)
      (j : C(unitInterval, A.core.TotalSpace))
      (hj : A.core.proj ∘ j = intervalCurveLoopFrom q w) :
      j 0 = j 1 ↔ Even haq.1.toFinset.card := by
    exact cut_cover_lift_closes_iff_even_crossings A q haq w hw j hj
  have heven : Even hab.1.toFinset.card ↔ Even hab'.1.toFinset.card :=
    (countClosure b hab z hz₀ f hf).symm.trans
      (hclosed.symm.trans (countClosure b' hab' z hz₁ g hg))
  have hcard' : hab'.1.toFinset.card = hac.1.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hab'.1,
      ← Set.ncard_eq_toFinset_card _ hac.1, hb'image]
  rw [hcard'] at heven
  simp only [Nat.even_iff] at heven
  change hab.1.toFinset.card % 2 = hac.1.toFinset.card % 2
  have hmod₀ := Nat.mod_lt hab.1.toFinset.card (by decide : 0 < 2)
  have hmod₁ := Nat.mod_lt hac.1.toFinset.card (by decide : 0 < 2)
  omega

end CurveComplex.LocalSurgery
