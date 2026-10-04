import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualSuppliedFieldBoundaryIndexInternal
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualUniformLiteralChartCapsInternal
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualUnionFiniteZeroDiscsPrivateCandidate
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRealFieldLiteralDiscBoundaryModelsPrivateCandidate
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualUnionSupportedIndexSumPrivateCandidate
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualSameAtlasRealComplexFieldComparisonPrivateCandidate
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualActualFieldsUniformCapsIndexComparisonPrivateCandidate

open scoped Manifold ContDiff Bundle
open Bundle Filter Topology Metric CategoryTheory CategoryTheory.Limits Set
open CurveComplex CurveComplexGenusTwo.CWHurewicz CurveComplex.GenusOrientationCandidate
set_option backward.isDefEq.respectTransparency false

section
variable {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
private theorem supplied_real_field_complex_representative
    (V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hV : Continuous (fun x => TotalSpace.mk' ℂ x (V x))) :
    let W : ∀ x : E, TangentSpace 𝓘(ℂ) x := fun x =>
      (tangentSpaceCastModel 𝓘(ℂ) x).symm ((tangentSpaceCastModel 𝓘(ℝ,ℂ) x) (V x));
    Continuous (fun x => TotalSpace.mk' ℂ x (W x)) ∧
    (∀ x, W x = 0 ↔ V x = 0) ∧
    ∀ q x (hx : x ∈ (chartAt ℂ q).source),
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q
        (TotalSpace.mk' ℂ x (W x))).2 =
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
        (TotalSpace.mk' ℂ x (V x))).2 := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualSameAtlasRealComplexFieldComparisonPrivateCandidate") 0)
        "actual_same_atlas_real_tangent_field_has_continuous_complex_representative"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent `V) $(Lean.mkIdent `hV)))
end

set_option maxHeartbeats 6000000 in
private theorem actual_same_atlas_two_supplied_fields_literal_sign_sum_eq
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A;
    letI : IsManifold 𝓘(ℂ) ∞ E := hA;
    ∀ hR : IsManifold 𝓘(ℝ,ℂ) ∞ E,
    letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := hR;
    ∀ V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x,
      ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (V x)) →
    ∀ Z : Finset E, (Z : Set E) = {x | V x = 0} →
    ∀ D : Z → (ℂ ≃L[ℝ] ℂ),
      (∀ q : Z, HasFDerivAt
        (fun w : ℂ =>
          let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val + w)
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
            (TotalSpace.mk' ℂ x (V x))).2)
        (D q).toContinuousLinearMap 0) →
    ∀ W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x,
      ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (W x)) →
    ∀ Q : Finset E, (Q : Set E) = {x | W x = 0} →
    ∀ L : Q → (ℂ ≃L[ℝ] ℂ),
      (∀ q : Q, HasFDerivAt
        (fun w : ℂ =>
          let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val + w)
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
            (TotalSpace.mk' ℂ x (W x))).2)
        (L q).toContinuousLinearMap 0) →
      (∑ q : Z,
        if 0 < (D q 1).re * (D q Complex.I).im - (D q Complex.I).re * (D q 1).im
          then (1 : ℤ) else -1) =
      ∑ q : Q,
        if 0 < (L q 1).re * (L q Complex.I).im - (L q Complex.I).re * (L q 1).im
          then (1 : ℤ) else -1 := by
  classical
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  intro hR
  letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := hR
  letI : ClosedSurface E := Classical.choice hg.2.1
  intro V hV Z hZ D hD W hW Q hQ L hL
  have hlocal (U : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
      (hU : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (U x)))
      (T : Finset E) (hT : (T : Set E) = {x | U x = 0})
      (B : T → (ℂ ≃L[ℝ] ℂ))
      (hB : ∀ q : T, HasFDerivAt
        (fun w : ℂ =>
          let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+w)
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
            (TotalSpace.mk' ℂ x (U x))).2)
        (B q).toContinuousLinearMap 0) :
      ∃ r : T → ℝ, (∀ q, 0 < r q) ∧
        ∀ q : T, ∀ ρ : ℝ, 0 < ρ → ρ < r q →
          let b : ℂ → ℂ := fun w =>
            let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+w)
            (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
              (TotalSpace.mk' ℂ x (U x))).2;
          (∀ z : Circle, b ((ρ:ℂ)*z) ≠ 0) ∧
          ∀ f : C(Circle,Circle),
            (∀ z, (f z:ℂ) = b ((ρ:ℂ)*z)/(‖b ((ρ:ℂ)*z)‖:ℂ)) →
            Classical.choose (actual_circle_map_winding_homotopy_source f) =
              if 0 < (B q 1).re*(B q Complex.I).im -
                (B q Complex.I).re*(B q 1).im then 1 else -1 := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualSuppliedFieldBoundaryIndexInternal") 0)
        "actual_supplied_field_literal_nondegenerate_boundary_indices"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent `U) $(Lean.mkIdent `hU) $(Lean.mkIdent `T) $(Lean.mkIdent `hT) $(Lean.mkIdent `B) $(Lean.mkIdent `hB)))
  obtain ⟨rV,hrV,hmodelV⟩ := hlocal V hV Z hZ D hD
  obtain ⟨rW,hrW,hmodelW⟩ := hlocal W hW Q hQ L hL
  let bV (x : E) := if hx : x ∈ Z then rV ⟨x,hx⟩ else 1
  let bW (x : E) := if hx : x ∈ Q then rW ⟨x,hx⟩ else 1
  let bound (x : E) := min (bV x) (bW x)
  have hbound (x : E) : 0 < bound x := by
    apply lt_min
    · dsimp only [bV]
      split
      · exact hrV _
      · norm_num
    · dsimp only [bW]
      split
      · exact hrW _
      · norm_num
  have hdiscs : ∃ ρ : E → ℝ,
      (∀ q, 0 < ρ q ∧ ρ q < bound q ∧
        closedBall ((chartAt ℂ q) q) (ρ q) ⊆ (chartAt ℂ q).target) ∧
      ((↑(Z ∪ Q) : Set E).PairwiseDisjoint
        (fun q => (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) (ρ q))) ∧
      ∀ q ∈ Z ∪ Q,
        q ∈ (chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) (ρ q) ∧
        IsOpen ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) (ρ q)) ∧
        IsCompact ((chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) (ρ q)) ∧
        ∀ x ∈ (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) (ρ q),
          x ∈ Z ∪ Q → x = q := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualUnionFiniteZeroDiscsPrivateCandidate") 0)
        "actual_finite_union_zero_discs_with_arbitrary_positive_radius_bounds"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent `Z) $(Lean.mkIdent `Q) $(Lean.mkIdent `bound) $(Lean.mkIdent `hbound)))
  obtain ⟨ρ,hρ,hdisj,hdiscdata⟩ := hdiscs
  let ρU : ↥(Z ∪ Q) → ℝ := fun q => ρ q.val
  have hpositive (q : ↥(Z ∪ Q)) : 0 < ρU q := (hρ q.val).1
  have htarget (q : ↥(Z ∪ Q)) :
      closedBall ((chartAt ℂ q.val) q.val) (ρU q) ⊆ (chartAt ℂ q.val).target := (hρ q.val).2.2
  have hsmallV (q : ↥(Z ∪ Q)) (hq : q.val ∈ Z) : ρU q < rV ⟨q.val,hq⟩ := by
    have hh := lt_of_lt_of_le (hρ q.val).2.1 (min_le_left (bV q.val) (bW q.val))
    simpa only [bV,dif_pos hq] using hh
  have hsmallW (q : ↥(Z ∪ Q)) (hq : q.val ∈ Q) : ρU q < rW ⟨q.val,hq⟩ := by
    have hh := lt_of_lt_of_le (hρ q.val).2.1 (min_le_right (bV q.val) (bW q.val))
    simpa only [bW,dif_pos hq] using hh
  have hisolation (q : ↥(Z ∪ Q)) :
      ∀ x ∈ (chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρU q),
        x ∈ Z ∪ Q → x = q.val := (hdiscdata q.val q.property).2.2.2
  have hmodels (U : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
      (hU : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (U x)))
      (S T : Finset E) (hT : (T : Set E) = {x | U x = 0})
      (B : T → (ℂ ≃L[ℝ] ℂ)) (r : T → ℝ) (hr : ∀ q, 0 < r q)
      (hm : ∀ q : T, ∀ ρ : ℝ, 0 < ρ → ρ < r q →
        let b : ℂ → ℂ := fun w =>
          let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+w)
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
            (TotalSpace.mk' ℂ x (U x))).2;
        (∀ z : Circle, b ((ρ:ℂ)*z) ≠ 0) ∧
        ∀ f : C(Circle,Circle),
          (∀ z, (f z:ℂ) = b ((ρ:ℂ)*z)/(‖b ((ρ:ℂ)*z)‖:ℂ)) →
          Classical.choose (actual_circle_map_winding_homotopy_source f) =
            if 0 < (B q 1).re*(B q Complex.I).im -
              (B q Complex.I).re*(B q 1).im then 1 else -1)
      (hsm : ∀ q : ↥(S ∪ T), ∀ hq : q.val ∈ T, ρ q.val < r ⟨q.val,hq⟩)
      (htg : ∀ q : ↥(S ∪ T), closedBall ((chartAt ℂ q.val) q.val) (ρ q.val) ⊆ (chartAt ℂ q.val).target)
      (hiso : ∀ q : ↥(S ∪ T), ∀ x ∈ (chartAt ℂ q.val).symm ''
        closedBall ((chartAt ℂ q.val) q.val) (ρ q.val), x ∈ S ∪ T → x = q.val) :
      ∃ f : ↥(S ∪ T) → C(Circle,Circle),
        (∀ q (z : Circle),
          let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+(ρ q.val:ℂ)*z)
          let b := (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
            (TotalSpace.mk' ℂ x (U x))).2
          (f q z:ℂ) = b/(‖b‖:ℂ)) ∧
        ∀ q, Classical.choose (actual_circle_map_winding_homotopy_source (f q)) =
          if hq : q.val ∈ T then
            if 0 < (B ⟨q.val,hq⟩ 1).re*(B ⟨q.val,hq⟩ Complex.I).im -
              (B ⟨q.val,hq⟩ Complex.I).re*(B ⟨q.val,hq⟩ 1).im then 1 else -1
          else 0 := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualRealFieldLiteralDiscBoundaryModelsPrivateCandidate") 0)
        "actual_given_reference_field_union_boundary_models_at_given_radius"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent `U) $(Lean.mkIdent `hU) $(Lean.mkIdent `S) $(Lean.mkIdent `T) $(Lean.mkIdent `hT) $(Lean.mkIdent `B) $(Lean.mkIdent `r) $(Lean.mkIdent `hr) $(Lean.mkIdent `hm) (fun q => $(Lean.mkIdent `ρ) q.val) (fun q => ($(Lean.mkIdent `hρ) q.val).1) $(Lean.mkIdent `htg) $(Lean.mkIdent `hsm) $(Lean.mkIdent `hiso)))
  have hVM := hmodels V hV Q Z hZ D rV hrV hmodelV
    (by rw [Finset.union_comm Q Z]; exact hsmallV)
    (by rw [Finset.union_comm Q Z]; exact htarget)
    (by rw [Finset.union_comm Q Z]; exact hisolation)
  rw [Finset.union_comm Q Z] at hVM
  obtain ⟨u,hu,hdegreeV⟩ := hVM
  obtain ⟨v,hv,hdegreeW⟩ := hmodels W hW Z Q hQ L rW hrW hmodelW hsmallW htarget hisolation
  have hsum (T : Finset E) (hT : T ⊆ Z ∪ Q) (d : T → ℤ)
      (g : ↥(Z ∪ Q) → ℤ)
      (he : ∀ q, g q = if hq : q.val ∈ T then d ⟨q.val,hq⟩ else 0) :
      (∑ q : ↥(Z ∪ Q), g q) = ∑ q : T, d q := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualUnionSupportedIndexSumPrivateCandidate") 0)
        "actual_finite_supported_index_sum"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) ($(Lean.mkIdent `Z) ∪ $(Lean.mkIdent `Q)) $(Lean.mkIdent `T) $(Lean.mkIdent `hT) $(Lean.mkIdent `d) $(Lean.mkIdent `g) $(Lean.mkIdent `he)))
  have hsumV := hsum Z Finset.subset_union_left
    (fun q => if 0 < (D q 1).re * (D q Complex.I).im - (D q Complex.I).re * (D q 1).im then (1:ℤ) else -1)
    (fun q => Classical.choose (actual_circle_map_winding_homotopy_source (u q))) hdegreeV
  have hsumW := hsum Q Finset.subset_union_right
    (fun q => if 0 < (L q 1).re * (L q Complex.I).im - (L q Complex.I).re * (L q 1).im then (1:ℤ) else -1)
    (fun q => Classical.choose (actual_circle_map_winding_homotopy_source (v q))) hdegreeW
  have hdisjoint : Set.univ.Pairwise (fun q t : ↥(Z ∪ Q) => Disjoint
      ((chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρU q))
      ((chartAt ℂ t.val).symm '' closedBall ((chartAt ℂ t.val) t.val) (ρU t))) := by
    intro q _ t _ hqt
    exact hdisj q.property t.property (fun he => hqt (Subtype.ext he))
  let P : Set E := (⋃ q : ↥(Z ∪ Q),
    (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρU q))ᶜ
  have hcaps : ∃ (β : ↥(Z ∪ Q) → C(Circle,P)) (r : relativeHomology E P 2)
      (caps : ↥(Z ∪ Q) → relativeHomology E P 2) (k : ℤ),
      k ≠ 0 ∧ r = k • ∑ q : ↥(Z ∪ Q), caps q ∧ relativeConnecting E P 1 r = 0 ∧
      (∀ q z, (β q z : E) = (chartAt ℂ q.val).symm
        ((chartAt ℂ q.val) q.val + (ρU q : ℂ)*z)) ∧
      ∀ q, relativeConnecting E P 1 (caps q) =
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (β q))) CircleFundamentalCycle.fundamentalClass := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualUniformLiteralChartCapsInternal") 0)
        "actual_same_atlas_disjoint_chart_caps_uniform_global_class"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent `E) $(Lean.mkIdent `hg) $(Lean.mkIdent `A) $(Lean.mkIdent `hA) ($(Lean.mkIdent `Z) ∪ $(Lean.mkIdent `Q)) $(Lean.mkIdent `ρU) $(Lean.mkIdent `hpositive) $(Lean.mkIdent `htarget) $(Lean.mkIdent `hdisjoint)))
  obtain ⟨β,r,caps,k,hk,hr,hboundary,hβ,hcapboundary⟩ := hcaps
  let VC : ∀ x : E, TangentSpace 𝓘(ℂ) x := fun x =>
    (tangentSpaceCastModel 𝓘(ℂ) x).symm ((tangentSpaceCastModel 𝓘(ℝ,ℂ) x) (V x))
  let WC : ∀ x : E, TangentSpace 𝓘(ℂ) x := fun x =>
    (tangentSpaceCastModel 𝓘(ℂ) x).symm ((tangentSpaceCastModel 𝓘(ℝ,ℂ) x) (W x))
  obtain ⟨hVC,hVCzero,hVCcoords⟩ := supplied_real_field_complex_representative V hV.continuous
  obtain ⟨hWC,hWCzero,hWCcoords⟩ := supplied_real_field_complex_representative W hW.continuous
  have hnozeros (x : E) (hx : x ∈ P) : V x ≠ 0 ∧ W x ≠ 0 := by
    have hn : x ∉ Z ∪ Q := by
      intro hz
      apply hx
      let q : ↥(Z ∪ Q) := ⟨x,hz⟩
      exact Set.mem_iUnion.mpr ⟨q,(chartAt ℂ x) x,mem_ball_self (hρ x).1,
        (chartAt ℂ x).left_inv (mem_chart_source ℂ x)⟩
    constructor
    · intro hz
      apply hn
      exact Finset.mem_union.mpr (Or.inl (by change x ∈ (Z:Set E); rw [hZ]; exact hz))
    · intro hz
      apply hn
      exact Finset.mem_union.mpr (Or.inr (by change x ∈ (Q:Set E); rw [hQ]; exact hz))
  have hVP : ∀ x ∈ P, VC x ≠ 0 := fun x hx hz => (hnozeros x hx).1 ((hVCzero x).mp hz)
  have hWP : ∀ x ∈ P, WC x ≠ 0 := fun x hx hz => (hnozeros x hx).2 ((hWCzero x).mp hz)
  have hsource (q : ↥(Z ∪ Q)) (z : Circle) : (β q z).val ∈ (chartAt ℂ q.val).source := by
    rw [hβ q z]
    apply (chartAt ℂ q.val).map_target
    apply htarget q
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (hpositive q),Circle.norm_coe,mul_one]
  let c (q : ↥(Z ∪ Q)) (z : Circle) : TangentSpace 𝓘(ℂ) (β q z).val ≃L[ℂ] ℂ :=
    (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q.val).continuousLinearEquivAt ℂ
      (β q z).val (hsource q z)
  have hunormal (q : ↥(Z ∪ Q)) (z : Circle) : (u q z : ℂ) = c q z (VC (β q z).val) /
      (‖c q z (VC (β q z).val)‖:ℂ) := by
    change (u q z : ℂ) =
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q.val
        (TotalSpace.mk' ℂ (β q z).val (VC (β q z).val))).2 /
      (‖(trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q.val
        (TotalSpace.mk' ℂ (β q z).val (VC (β q z).val))).2‖ : ℂ)
    rw [hVCcoords q.val (β q z).val (hsource q z),hβ q z]
    exact hu q z
  have hvnormal (q : ↥(Z ∪ Q)) (z : Circle) : (v q z : ℂ) = c q z (WC (β q z).val) /
      (‖c q z (WC (β q z).val)‖:ℂ) := by
    change (v q z : ℂ) =
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q.val
        (TotalSpace.mk' ℂ (β q z).val (WC (β q z).val))).2 /
      (‖(trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q.val
        (TotalSpace.mk' ℂ (β q z).val (WC (β q z).val))).2‖ : ℂ)
    rw [hWCcoords q.val (β q z).val (hsource q z),hβ q z]
    exact hv q z
  have hindices :
      (∑ q : ↥(Z ∪ Q), Classical.choose (actual_circle_map_winding_homotopy_source (v q))) =
      ∑ q : ↥(Z ∪ Q), Classical.choose (actual_circle_map_winding_homotopy_source (u q)) := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualActualFieldsUniformCapsIndexComparisonPrivateCandidate") 0)
        "actual_two_tangent_fields_uniform_caps_boundary_index_invariance"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent `P) $(Lean.mkIdent `VC) $(Lean.mkIdent `WC) $(Lean.mkIdent `hVC) $(Lean.mkIdent `hWC) $(Lean.mkIdent `hVP) $(Lean.mkIdent `hWP) $(Lean.mkIdent `r) $(Lean.mkIdent `caps) $(Lean.mkIdent `β) $(Lean.mkIdent `k) $(Lean.mkIdent `hk) $(Lean.mkIdent `hr) $(Lean.mkIdent `hboundary) $(Lean.mkIdent `hcapboundary) $(Lean.mkIdent `c) $(Lean.mkIdent `u) $(Lean.mkIdent `v) $(Lean.mkIdent `hunormal) $(Lean.mkIdent `hvnormal)))
  exact hsumV.symm.trans (hindices.symm.trans hsumW)

