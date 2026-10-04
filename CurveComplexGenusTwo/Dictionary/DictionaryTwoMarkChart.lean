import CurveComplexGenusTwo.Dictionary.OneBranchDiscBoundary
import CurveComplexGenusTwo.TwoMarkedSideNoFullPreimage
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- Extract a consumer-facing one-mark disc chart from an already certified disc bound.
The boundary convention is exactly the unit-circle convention used by the 2-mark
pasting consumer. -/
theorem one_mark_disc_chart_of_boundsDisc
    {c : Curve S} (hc : BoundsDisc c) :
    ∃ F : C(Metric.closedBall (0 : Schoenflies.Plane) 1, S),
      IsEmbedding F ∧
      F '' {z | ‖z.val‖ = 1} = c.image := by
  rcases hc with ⟨F, hF, hboundary⟩
  have hboundary' : F '' {z | ‖z.val‖ = 1} = c.image := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hboundary
  exact ⟨F, hF, hboundary'⟩

/-- A path on a punctured base circle has a continuous lift through the
unramified double cover.  The construction uses only the actual covering-map
lifting API and the branch avoidance field of `PuncturedCircle`. -/
theorem exists_puncturedCircle_path_lift
    (M : HyperellipticModel E S)
    (a : PuncturedCircle M) (β : C(Interval, S))
    (hβrange : Set.range β = a.image) :
    ∃ γ : C(Interval, E),
      ∀ t, M.cover.projection (γ t) = β t := by
  classical
  let q := M.cover
  letI : ContractibleSpace Interval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  letI : LocallyPathConnectedSpace Interval :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  have hβavoid (t : Interval) : β t ∉ q.branch := by
    intro ht
    have hmem : β t ∈ a.image := by
      rw [← hβrange]
      exact Set.mem_range_self t
    exact Set.disjoint_left.mp a.avoids_branch hmem ht
  let b : C(Interval, q.unramifiedBase) :=
    ⟨fun t => ⟨β t, hβavoid t⟩,
      β.continuous.subtype_mk hβavoid⟩
  obtain ⟨e, he⟩ := q.projection_surjective (β 0)
  let e₀ : q.unramifiedTotal := ⟨e, by
    change q.projection e ∉ q.branch
    rw [he]
    exact hβavoid 0⟩
  obtain ⟨F, hF, _⟩ := q.unramified_isCoveringMap.existsUnique_continuousMap_lifts
    b (0 : Interval) e₀ (by
      apply Subtype.ext
      exact he)
  let γ : C(Interval, E) :=
    ⟨fun t => (F t).val,
      continuous_subtype_val.comp F.continuous⟩
  refine ⟨γ, ?_⟩
  intro t
  have h := congrFun hF.2 t
  exact congrArg Subtype.val h

/-- Specialize the branch-free 2-mark obstruction by constructing the outer
covering lift from its exact punctured-circle range. -/
theorem two_marked_side_no_full_preimage_lifted
    (M : HyperellipticModel E S)
    {X : Type} [TopologicalSpace X]
    (a : PuncturedCircle M) (K : Set X) (f : C(K,S)) (hf : IsEmbedding f)
    (u v : K) (P χ : Path u v) (Q : Path v u)
    (F : Fin 2 → C(Metric.closedBall (0 : Schoenflies.Plane) 1,S))
    (hF : ∀ i, IsEmbedding (F i))
    (m : Fin 2 → Metric.closedBall (0 : Schoenflies.Plane) 1)
    (hm : ∀ i, ‖(m i).val‖<1)
    (honly : ∀ i z, F i z ∈ M.cover.branch ↔ z=m i)
    (hcell0 : Set.range (fun t => f ((P.trans χ.symm) t))=F 0 '' {z | ‖z.val‖=1})
    (hcell1 : Set.range (fun t => f ((χ.trans Q) t))=F 1 '' {z | ‖z.val‖=1})
    (hcoll0 : ∀ s t, (P.trans χ.symm) s=(P.trans χ.symm) t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hcoll1 : ∀ s t, (χ.trans Q) s=(χ.trans Q) t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hcollOuter : ∀ s t, f ((P.trans Q) s)=f ((P.trans Q) t) → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hOuterRange : Set.range (fun t => f ((P.trans Q) t)) = a.image)
    (c : Curve E) (hc : c.image=M.cover.projection ⁻¹' a.image) : False := by
  let β : C(Interval, S) :=
    ⟨fun t => f ((P.trans Q) t), f.continuous.comp (P.trans Q).continuous⟩
  have hβrange : Set.range β = a.image := by
    simpa [β] using hOuterRange
  obtain ⟨γ, hγπ⟩ := exists_puncturedCircle_path_lift M a β hβrange
  apply two_marked_side_no_full_preimage M a K f hf u v P χ Q F hF m hm honly
    hcell0 hcell1 hcoll0 hcoll1 hcollOuter hOuterRange c hc γ
  exact hγπ

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.one_mark_disc_chart_of_boundsDisc
#print axioms CurveComplex.HyperellipticModel.exists_puncturedCircle_path_lift
#print axioms CurveComplex.HyperellipticModel.two_marked_side_no_full_preimage_lifted
