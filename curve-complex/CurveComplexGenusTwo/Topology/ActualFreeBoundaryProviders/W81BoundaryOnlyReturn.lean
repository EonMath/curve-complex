import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryContactFacts
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.SubsetNullBoundaryDiskFilling

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies RegionalEmbeddedFamily

/-- A simple boundary connector with the same actual lifted endpoints as a
proper arc bounds the literal disk forbidden by the source essentiality. The
codomain remains the caller's subset of the given genus-at-least-two surface. -/
theorem free_boundary_matched_lifts_bound_literal_disk
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (B : Set ↥F)
    (a c : C(Interval,↥F)) (ha : IsEmbedding a) (hc : IsEmbedding c)
    (hai : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (hcB : ∀ t, c t ∈ B)
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (p : X → ↥F) (hp : Continuous p)
    (E J : C(Interval,X))
    (hEp : ∀ t, p (E t) = a t) (hJp : ∀ t, p (J t) = c t)
    (hJ0 : J 0 = E 0) (hJ1 : J 1 = E 1) :
    ∃ d : C(Metric.closedBall (0 : Plane) 1,↥F),
      IsEmbedding d ∧
      d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range a ∪ range c := by
  let : ClosedSurface S := Classical.choice hS.2.1
  let P : Path (E 0) (E 1) := ⟨E,rfl,rfl⟩
  let Q : Path (E 0) (E 1) := ⟨J,hJ0,hJ1⟩
  let first := P.map hp
  let second := Q.map hp
  have hfirsteq (t : Interval) : first t = a t := hEp t
  have hsecondeq (t : Interval) : second t = c t := hJp t
  have hfirst : IsEmbedding first := by
    rw [show (first : Interval → ↥F) = a from funext hfirsteq]
    exact ha
  have hsecond : IsEmbedding second := by
    rw [show (second : Interval → ↥F) = c from funext hsecondeq]
    exact hc
  have hcollision : ∀ s t, first s = second t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t hst
    have hsB : a s ∈ B := by
      rw [← hfirsteq,hst,hsecondeq]
      exact hcB t
    have hs : s = 0 ∨ s = 1 := by
      by_contra h
      push Not at h
      exact hai s ⟨lt_of_le_of_ne s.property.1 (Ne.symm h.1),
        lt_of_le_of_ne s.property.2 h.2⟩ hsB
    rcases hs with hs | hs
    · refine Or.inl ⟨hs,hsecond.injective ?_⟩
      exact hst.symm.trans ((congrArg first hs).trans
        (first.source.trans second.source.symm))
    · refine Or.inr ⟨hs,hsecond.injective ?_⟩
      exact hst.symm.trans ((congrArg first hs).trans
        (first.target.trans second.target.symm))
  have hhom : first.Homotopic second :=
    (SimplyConnectedSpace.paths_homotopic P Q).map ⟨p,hp⟩
  obtain ⟨loop,hloop,hnull⟩ := clean_homotopic_arcs_bound_null_curve
    first second hfirst hsecond hcollision hhom
  obtain ⟨d,hd,hbd⟩ :=
    subset_nullhomotopic_curve_bounds_literal_disk S g hg hS F loop hnull
  refine ⟨d,hd,hbd.trans ?_⟩
  simpa only [show range first = range a from congrArg range (funext hfirsteq),
    show range second = range c from congrArg range (funext hsecondeq)] using hloop

/-- Endpoint matching is unordered. Reversing the connector and its lift
keeps its whole original trace, and hence the exact same disk boundary. -/
theorem free_boundary_unordered_lifts_bound_literal_disk
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (B : Set ↥F)
    (a c : C(Interval,↥F)) (ha : IsEmbedding a) (hc : IsEmbedding c)
    (hai : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (hcB : ∀ t, c t ∈ B)
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (p : X → ↥F) (hp : Continuous p)
    (E J : C(Interval,X))
    (hEp : ∀ t, p (E t) = a t) (hJp : ∀ t, p (J t) = c t)
    (hend : (J 0 = E 0 ∧ J 1 = E 1) ∨ (J 0 = E 1 ∧ J 1 = E 0)) :
    ∃ d : C(Metric.closedBall (0 : Plane) 1,↥F),
      IsEmbedding d ∧
      d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range a ∪ range c := by
  rcases hend with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact free_boundary_matched_lifts_bound_literal_disk
      S g hg hS F B a c ha hc hai hcB p hp E J hEp hJp h0 h1
  · let cr : C(Interval,↥F) :=
      ⟨c ∘ unitInterval.symm,c.continuous.comp unitInterval.symmHomeomorph.continuous⟩
    let Jr : C(Interval,X) :=
      ⟨J ∘ unitInterval.symm,J.continuous.comp unitInterval.symmHomeomorph.continuous⟩
    have hcr : IsEmbedding cr := hc.comp unitInterval.symmHomeomorph.isEmbedding
    have hJr0 : Jr 0 = E 0 := by simpa only [Jr,ContinuousMap.coe_mk,
      Function.comp_apply,unitInterval.symm_zero] using h1
    have hJr1 : Jr 1 = E 1 := by simpa only [Jr,ContinuousMap.coe_mk,
      Function.comp_apply,unitInterval.symm_one] using h0
    obtain ⟨d,hd,hbd⟩ := free_boundary_matched_lifts_bound_literal_disk
      S g hg hS F B a cr ha hcr hai (fun t => hcB (unitInterval.symm t))
      p hp E Jr hEp (fun t => hJp (unitInterval.symm t)) hJr0 hJr1
    have hrange : range cr = range c := by
      change range (c ∘ unitInterval.symm) = range c
      rw [Set.range_comp]
      have hs : Function.Surjective unitInterval.symm := unitInterval.symmHomeomorph.surjective
      rw [hs.range_eq,Set.image_univ]
    exact ⟨d,hd,by simpa only [hrange] using hbd⟩

/-- This negated disk predicate is literally the original essentiality input,
with the actual codomain supplied by the caller. -/
theorem free_boundary_essential_excludes_boundary_only_lift_return
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (B : Set ↥F)
    (a : C(Interval,↥F)) (ha : IsEmbedding a)
    (hai : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (haEssential : ¬ ∃ c : C(Interval,↥F), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : Plane) 1,↥F),
        IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range a ∪ range c)
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (p : X → ↥F) (hp : Continuous p)
    (E J : C(Interval,X)) (c : C(Interval,↥F))
    (hc : IsEmbedding c) (hcB : ∀ t, c t ∈ B)
    (hEp : ∀ t, p (E t) = a t) (hJp : ∀ t, p (J t) = c t)
    (hend : (J 0 = E 0 ∧ J 1 = E 1) ∨ (J 0 = E 1 ∧ J 1 = E 0)) : False := by
  exact haEssential ⟨c,hc,hcB,free_boundary_unordered_lifts_bound_literal_disk
    S g hg hS F B a c ha hc hai hcB p hp E J hEp hJp hend⟩

end CoherentEndpointMotion.FreeBoundaryContactRepair
