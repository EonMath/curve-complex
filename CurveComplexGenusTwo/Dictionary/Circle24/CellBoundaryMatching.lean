import CurveComplexGenusTwo.Dictionary.Circle24.OneMarkFullCell
open Set Topology
namespace CurveComplex.BranchedDoubleCover
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

/-- Equality of genuine boundary lifts from a common attaching anchor. -/
theorem boundary_lifts_eq_of_common_anchor (q : BranchedDoubleCover E S)
    (γ δ : C(Interval,E))
    (hπ : ∀ t, q.projection (γ t)=q.projection (δ t))
    (havoid : ∀ t, q.projection (γ t) ∉ q.branch)
    (hanchor : γ 0=δ 0) : γ=δ := by
  let g : C(Interval,q.unramifiedTotal) :=
    ⟨fun t => ⟨γ t,havoid t⟩,γ.continuous.subtype_mk _⟩
  have hδavoid (t) : q.projection (δ t) ∉ q.branch := by rw [← hπ t]; exact havoid t
  let d : C(Interval,q.unramifiedTotal) :=
    ⟨fun t => ⟨δ t,hδavoid t⟩,δ.continuous.subtype_mk _⟩
  have heq : q.unramifiedProjection ∘ g=q.unramifiedProjection ∘ d := by
    funext t
    exact Subtype.ext (hπ t)
  have hgd : (g:Interval → q.unramifiedTotal)=d :=
    q.unramified_isCoveringMap.eq_of_comp_eq g.continuous d.continuous heq
      0 (Subtype.ext hanchor)
  apply DFunLike.coe_injective
  funext t
  exact congrArg Subtype.val (congrFun hgd t)

end CurveComplex.BranchedDoubleCover
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000

/-- The actual whole-cell radial filling can use a prescribed boundary lift
as its outer edge. This is the compatible parameterization required when its
boundary arcs attach to previously constructed corridor sheets. -/
theorem one_mark_disc_full_filling_prescribed_boundary
    (M : HyperellipticModel E S)
    (f : C(Metric.closedBall (0:Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
    (m : Metric.closedBall (0:Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1)
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
    (β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1))
    (hends : β 0=β 1)
    (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hrange : Set.range β={z | ‖z.val‖=1})
    (γ : C(Interval,E)) (hγπ : ∀ t, M.cover.projection (γ t)=f (β t)) :
    ∃ L : C(Interval × Interval,E),
      (∀ t : Interval, L (1,t)=γ t) ∧
      (∀ r : Interval, L (r,1)=M.cover.deck (L (r,0))) ∧
      (∀ t t' : Interval, L (0,t)=L (0,t')) ∧
      Set.range L ∪ M.cover.deck '' Set.range L=M.cover.projection ⁻¹' Set.range f := by
  obtain ⟨h,L,hzero,hboundary,hanchor,hπ,hedge,hcenter,hcover⟩ :=
    M.one_mark_disc_full_cell_filling f hf m hm honly β hends hcoll hrange (γ 0) (hγπ 0)
  have hnorm (t : Interval) : ‖(β t).val‖=1 := by
    have hh := Set.mem_range_self t (f := β)
    rw [hrange] at hh
    exact hh
  let δ : C(Interval,E) := ⟨fun t => L (1,t),
    L.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hδπ (t) : M.cover.projection (δ t)=f (β t) := by
    convert hπ 1 t using 1
    apply congrArg f
    trans h (β t)
    · exact (hboundary _ (hnorm t)).symm
    · apply congrArg h
      apply Subtype.ext
      simp
  have havoid (t) : M.cover.projection (δ t) ∉ M.cover.branch := by
    rw [hδπ,honly]
    intro he
    have hn := hnorm t
    rw [he] at hn
    linarith
  have hδγ : δ=γ := M.cover.boundary_lifts_eq_of_common_anchor δ γ
    (fun t => (hδπ t).trans (hγπ t).symm) havoid hanchor
  refine ⟨L,?_,hedge,hcenter,hcover⟩
  intro t
  exact congrFun (congrArg DFunLike.coe hδγ) t

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.BranchedDoubleCover.boundary_lifts_eq_of_common_anchor
#print axioms CurveComplex.HyperellipticModel.one_mark_disc_full_filling_prescribed_boundary
