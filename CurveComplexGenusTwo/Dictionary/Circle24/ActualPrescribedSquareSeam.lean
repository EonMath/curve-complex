import CurveComplexGenusTwo.Dictionary.Circle24.PolarSquareSeams
import CurveComplexGenusTwo.Dictionary.Circle24.PrescribedPolarBoundary
open Set Topology
namespace CurveComplex
noncomputable def halfInterval (t : Interval) : Interval :=
  ⟨t.val/2,⟨by linarith [t.property.1],by linarith [t.property.2]⟩⟩
noncomputable def squareLeftSeam (t : Interval) : Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1 :=
  ⟨(-1,2*t.val-1),⟨by norm_num,⟨by linarith [t.property.1],by linarith [t.property.2]⟩⟩⟩
noncomputable def squareRightSeam (t : Interval) : Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1 :=
  ⟨(1,1-2*t.val),⟨by norm_num,⟨by linarith [t.property.2],by linarith [t.property.1]⟩⟩⟩
@[simp] theorem halfInterval_zero : halfInterval 0=0 := Subtype.ext (by norm_num [halfInterval])
namespace HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 9000000

/-- Construct a full one-mark square lift with both vertical attaching seams
agreeing pointwise with a prescribed source seam lift and its deck mate.
All filling and charts are constructed; neither an upstairs disk nor a
compatible square chart is an input. -/
theorem one_mark_disc_square_prescribed_seam
    (M : HyperellipticModel E S)
    (f : C(Metric.closedBall (0:Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
    (m : Metric.closedBall (0:Schoenflies.Plane) 1) (hm : ‖m.val‖<1)
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
    (β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1))
    (hends : β 0=β 1)
    (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hrange : Set.range β={z | ‖z.val‖=1})
    (η : C(Interval,E)) (hηπ : ∀ t, M.cover.projection (η t)=f (β (halfInterval t))) :
    ∃ D : (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ≃ₜ M.cover.projection ⁻¹' Set.range f,
      (∀ t : Interval, (D (squareLeftSeam t)).val=η t) ∧
      (∀ t : Interval, (D (squareRightSeam t)).val=M.cover.deck (η t)) := by
  let : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by simp⟩
  let : LocallyPathConnectedSpace Interval := (convex_Icc (0:ℝ) 1).locallyPathConnectedSpace
  have hnorm (t : Interval) : ‖(β t).val‖=1 := by
    have h := hrange ▸ Set.mem_range_self t (f:=β)
    exact h
  let b : C(Interval,S) := f.comp β
  have havoid (t) : b t ∉ M.cover.branch := by
    change f (β t) ∉ M.cover.branch
    rw [honly]
    intro he
    have hn := hnorm t
    rw [he] at hn
    linarith
  have h0 : M.cover.projection (η 0)=b 0 := by
    simpa only [b,ContinuousMap.comp_apply,halfInterval_zero] using hηπ 0
  obtain ⟨γ,hγ,_⟩ := M.cover.unbranched_cover.existsUnique_continuousMap_lifts b h0 havoid
  have hγπ (t) : M.cover.projection (γ t)=f (β t) := congrFun hγ.2 t
  let σ : C(Interval,E) := γ.comp ⟨halfInterval,by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.div_const 2⟩
  have hση : σ=η := M.cover.boundary_lifts_eq_of_common_anchor σ η
    (fun t => (hγπ (halfInterval t)).trans (hηπ t).symm)
    (fun t => by change M.cover.projection (γ (halfInterval t)) ∉ M.cover.branch
                 rw [hγπ]; exact havoid (halfInterval t)) (by
      change γ (halfInterval 0)=η 0
      simpa only [halfInterval_zero] using hγ.1)
  have hp (t : Interval) : γ (halfInterval t)=η t :=
    congrFun (congrArg DFunLike.coe hση) t
  obtain ⟨H,hH0,hH1,hB⟩ := M.one_mark_disc_polar_cell_homeomorph_prescribed
    f hf m hm honly β hends hcoll hrange γ hγπ
  obtain ⟨K,hK⟩ := one_mark_polar_cell_square_chart
  let D := K.symm.trans H
  have hhalf (t : Interval) : (halfInterval t).val≤1/2 := by
    dsimp [halfInterval]; linarith [t.property.2]
  have hl (t : Interval) : K (Quot.mk oneMarkPolarRel ((1,halfInterval t),false))=squareLeftSeam t := by
    apply Subtype.ext
    rw [hK]
    simp only [polarSquareMap,polarSquareBoundary,Bool.false_eq_true,↓reduceIte,
      polarSquareHalf,ite_eq_left (hhalf t)]
    apply Prod.ext <;> dsimp [halfInterval,squareLeftSeam] <;> ring
  have hr (t : Interval) : K (Quot.mk oneMarkPolarRel ((1,halfInterval t),true))=squareRightSeam t := by
    apply Subtype.ext
    rw [hK]
    simp only [polarSquareMap,polarSquareBoundary,↓reduceIte,
      polarSquareHalf,ite_eq_left (hhalf t)]
    apply Prod.ext <;> dsimp [halfInterval,squareRightSeam] <;> ring
  refine ⟨D,?_,?_⟩
  · intro t
    change (H (K.symm (squareLeftSeam t))).val=η t
    rw [← hl t,K.symm_apply_apply,hH0,hp]
  · intro t
    change (H (K.symm (squareRightSeam t))).val=M.cover.deck (η t)
    rw [← hr t,K.symm_apply_apply,hH1,hp]

end HyperellipticModel
end CurveComplex
#print axioms CurveComplex.HyperellipticModel.one_mark_disc_square_prescribed_seam
