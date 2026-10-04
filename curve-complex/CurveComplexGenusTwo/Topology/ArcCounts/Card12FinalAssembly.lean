import CurveComplexGenusTwo.Filtration.Geometry.ActualCommonBasepointLoopIsotopy
import CurveComplexGenusTwo.Topology.ArcCounts.ActualLowDegreeAssembly
import CurveComplexGenusTwo.Topology.ArcCounts.ActualTwoTraceShape
import CurveComplexGenusTwo.Topology.ArcCounts.ActualCrossComponentForest
import CurveComplexGenusTwo.Topology.ArcCounts.ActualStrongQuantitativeEulerLowerBound
import CurveComplexGenusTwo.Topology.ArcCounts.GlobalFaceCoverage
namespace CurveComplex.HyperellipticModel
open Set
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance finalClassDecEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
theorem actual_bad_unmarked_low_degree_cross_component
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (hsigma : sigma.Nonempty)
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hbad : badVertices (actualArcLabels M) sigma = sigma)
    (U : Set S) (hU : IsComplementComponent (⋃ k, (r k).val.image) U)
    (hdegree : actualIncidentEdgeDegree M r U < 3)
    (hfree : ∀ b ∈ M.cover.branch, b ∉ U) :
    ∃ i j : {v // v ∈ sigma},
      connectedComponentIn (⋃ k, (r k).val.image) ((r i).val.map 0) ≠
        connectedComponentIn (⋃ k, (r k).val.image) ((r j).val.map 0) ∧
      (frontier U ∩ (r i).val.image).Nonempty ∧
      (frontier U ∩ (r j).val.image).Nonempty := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨i,j,hij,hi,hj,hboundary,hpair,hparallel⟩ :=
    actual_unmarked_low_degree_two_nonparallel_traces M hsigma r hr hd U hU hdegree hfree
  refine ⟨i,j,?_,?_,?_⟩
  · intro hsame
    have hbad' : @badVertices (EssentialArcClass M) S (fun a b => Quotient.decidableEq a b) (actualArcLabels M) sigma = sigma := by
      convert hbad using 1 <;> congr 1
      exact Subsingleton.elim _ _
    rcases actual_unmarked_two_trace_same_component_shape M r hr hd hbad' U hU hfree
      i j hij hi hj hboundary hsame with ⟨hin,hjn,hends⟩ | ⟨ha,hb,hbase⟩
    · exact hparallel hin hjn hends
    · have hmeet : (r i).val.image ∩ (r j).val.image = {(r i).val.map 0} := by
        rw [markedArc_disjoint_interiors_inter_image _ _ (hd i j hij)]
        change (({(r i).val.map 0, (r i).val.map 1} : Finset S) : Set S) ∩
          (({(r j).val.map 0, (r j).val.map 1} : Finset S) : Set S) = {(r i).val.map 0}
        simp [← ha, ← hb, ← hbase]
      have he := actual_common_basepoint_loops_empty_face_class_equality M (r i) (r j)
        ha hb hbase hmeet (⋃ k, (r k).val.image) U
        (markedFamily_graph_compact (fun k => (r k).val)).isClosed
        (Set.subset_iUnion (fun k => (r k).val.image) i)
        (Set.subset_iUnion (fun k => (r k).val.image) j) hU hboundary hfree
      rw [hr,hr] at he
      exact hij (Subtype.ext he)
  · obtain ⟨x,hx,hxi⟩ := hi
    exact ⟨x,hx,hxi.1⟩
  · obtain ⟨x,hx,hxj⟩ := hj
    exact ⟨x,hx,hxj.1⟩

theorem actual_bad_weighted_face_bound
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (hsigma : sigma.Nonempty)
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hbad : badVertices (actualArcLabels M) sigma = sigma)
    (F : Finset (Set S))
    (hF : ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).val.image) U) :
    3 * F.card ≤ 2 * sigma.card +
      3 * (6 - (markedFamilyVertices (fun i => (r i).val)).card) +
      3 * ((Finset.univ.image (fun i : {v // v ∈ sigma} =>
        connectedComponentIn (⋃ k, (r k).val.image) ((r i).val.map 0))).card - 1) := by
  classical
  let L := (F.filter (fun U => actualIncidentEdgeDegree M r U < 3)).filter
    (fun U => ∀ b ∈ M.cover.branch, b ∉ U)
  have hLF : ∀ U ∈ L, IsComplementComponent (⋃ i, (r i).val.image) U := by
    intro U hU
    exact hF U (Finset.mem_filter.mp (Finset.mem_filter.mp hU).1).1
  have hcross : ∀ U ∈ L, ∃ i j : {v // v ∈ sigma},
      connectedComponentIn (⋃ k, (r k).val.image) ((r i).val.map 0) ≠
        connectedComponentIn (⋃ k, (r k).val.image) ((r j).val.map 0) ∧
      (frontier U ∩ (r i).val.image).Nonempty ∧
      (frontier U ∩ (r j).val.image).Nonempty := by
    intro U hU
    obtain ⟨hU,hfree⟩ := Finset.mem_filter.mp hU
    obtain ⟨hUF,hdegree⟩ := Finset.mem_filter.mp hU
    exact actual_bad_unmarked_low_degree_cross_component M hsigma r hr hd hbad U
      (hF U hUF) hdegree hfree
  have hcard := actual_cross_component_faces_card_le_components_sub_one M sigma hsigma
    r hr hd L hLF hcross
  have hpre := actual_bad_weighted_face_bound_before_cross_classification M r hr hd hbad F hF
  change 3 * F.card ≤ 2 * sigma.card +
    3 * (6 - (markedFamilyVertices (fun i => (r i).val)).card) + 3 * L.card at hpre
  omega

theorem actual_bad_simplex_card_le_twelve
    (M : HyperellipticModel E S) (sigma : Finset (EssentialArcClass M))
    (hsigma : sigma.Nonempty)
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hbad : badVertices (actualArcLabels M) sigma = sigma) :
    sigma.card ≤ 12 := by
  classical
  letI : Nonempty {v // v ∈ sigma} := hsigma.to_subtype
  obtain ⟨F,hEuler,hF⟩ := actual_strong_quantitative_euler_lower_bound M r hd
  exact card12_of_one_weighted_face_family M sigma hsigma r hr hd F hF hEuler
    (fun hF => actual_bad_weighted_face_bound M hsigma r hr hd hbad F hF)
end CurveComplex.HyperellipticModel
