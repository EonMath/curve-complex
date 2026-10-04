import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleNoContinuousSection
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

open Set Topology Schoenflies CurveComplex

/-- An actual circle coordinate projection equal to the ORIGINAL circle
parameter excludes an embedded bounding disk. A hypothetical disk constructs a
continuous section of the actual circle covering, which is impossible. -/
theorem actual_circle_projected_curve_is_essential
    {X : Type*} [TopologicalSpace X] (c : Curve X) (π : C(X,Circle))
    (hπ : ∀ z, π (c.map z)=z) : Essential c := by
  rintro ⟨f,hf,hBoundary⟩
  let D := Metric.closedBall (0 : Plane) 1
  let z₀ : D := ⟨0,by change (0 : Plane)∈Metric.closedBall 0 1; simp⟩
  have hConvex : Convex ℝ (Metric.closedBall (0 : Plane) 1) := convex_closedBall _ _
  let := hConvex.contractibleSpace ⟨0,by simp⟩
  let := hConvex.locallyPathConnectedSpace
  let q : C(D,Circle) := ⟨fun z => π (f z),π.continuous.comp f.continuous⟩
  obtain ⟨a,ha⟩ := Circle.exp_surjective (q z₀)
  obtain ⟨S,⟨_,hS⟩,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts q z₀ a ha
  let e : D ≃ₜ range f := hf.toHomeomorph
  have hRange (z : Circle) : c.map z∈range f := by
    have hz : c.map z∈c.image := mem_range_self z
    rw [← hBoundary] at hz
    obtain ⟨w,_,hw⟩ := hz
    exact ⟨w,hw⟩
  let v : C(Circle,range f) := ⟨fun z => ⟨c.map z,hRange z⟩,
    c.embedded.continuous.subtype_mk _⟩
  let g : C(Circle,D) := ⟨fun z => e.symm (v z),e.symm.continuous.comp v.continuous⟩
  have hfg (z : Circle) : f (g z)=c.map z := by
    have hh := congrArg Subtype.val (e.apply_symm_apply (v z))
    exact hh
  let s : C(Circle,ℝ) := S.comp g
  apply actual_circle_exp_has_no_continuous_section s
  intro z
  change Circle.exp (S (g z))=z
  have hh := congrFun hS (g z)
  change Circle.exp (S (g z))=π (f (g z)) at hh
  rw [hfg,hπ] at hh
  exact hh

#print axioms actual_circle_projected_curve_is_essential
