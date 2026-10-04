import ActualSameClassOriginalNonloopHomotopy
import ActualTwoEndpointPuncturedJordan

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- A genuinely parallel original same-class pair PRODUCES its mark-free
comparison region. Neither punctured homotopy nor a selected region is input.
This is the zero-mutual-crossing nonloop branch of target comparison. -/
theorem actual_same_class_parallel_nonloops_produce_empty_region
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b)
    (ha : a.val.map 0 ≠ a.val.map 1)
    (h0 : a.val.map 0 = b.val.map 0) (h1 : a.val.map 1 = b.val.map 1)
    (hmeet : a.val.image ∩ b.val.image = {a.val.map 0,a.val.map 1}) :
    ∃ Ω : Set S, IsComplementComponent (a.val.image ∪ b.val.image) Ω ∧
      frontier Ω = a.val.image ∪ b.val.image ∧ Disjoint Ω (M.cover.branch : Set S) := by
  obtain ⟨hu,hv,α,β,hα,hβ,hhom⟩ :=
    actual_same_class_original_nonloop_path_homotopy M a b hclass ha h0 h1
  have hb : b.val.map 0 ≠ b.val.map 1 := by simpa only [← h0,← h1] using ha
  let f : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  let g : C(Interval,S) := ⟨b.val.map,b.val.continuous⟩
  obtain ⟨Ω,hn,hconn,hsub,hmax,hfrontier,hfree⟩ :=
    actual_two_endpoint_punctured_homotopic_jordan_sides_have_empty_region M f g
      (a.val.map 0) (a.val.map 1) (NonLoopArc.isEmbedding ⟨a.val,ha⟩)
      (NonLoopArc.isEmbedding ⟨b.val,hb⟩) rfl h0.symm rfl h1.symm ha hmeet
      hu hv α β hα hβ hhom
  exact ⟨Ω,⟨hn,hconn,hsub,hmax⟩,hfrontier,hfree⟩

/-- Literal same class determines the endpoint orientation alternative.
It does not assume that two independently chosen parametrizations agree. -/
theorem actual_same_class_nonloop_endpoint_orientation
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b)
    (ha : a.val.map 0 ≠ a.val.map 1) :
    (a.val.map 0 = b.val.map 0 ∧ a.val.map 1 = b.val.map 1) ∨
      (a.val.map 0 = b.val.map 1 ∧ a.val.map 1 = b.val.map 0) := by
  classical
  have he := arcEndpoints_isotopy_invariant M a b (Quotient.exact hclass)
  change ({a.val.map 0,a.val.map 1} : Finset S) = {b.val.map 0,b.val.map 1} at he
  have hA0 : a.val.map 0 = b.val.map 0 ∨ a.val.map 0 = b.val.map 1 := by
    have h : a.val.map 0 ∈ ({b.val.map 0,b.val.map 1} : Finset S) :=
      he ▸ Finset.mem_insert_self _ _
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  have hA1 : a.val.map 1 = b.val.map 0 ∨ a.val.map 1 = b.val.map 1 := by
    have h : a.val.map 1 ∈ ({b.val.map 0,b.val.map 1} : Finset S) :=
      he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  rcases hA0 with h00 | h01 <;> rcases hA1 with h10 | h11
  · exact False.elim (ha (h00.trans h10.symm))
  · exact Or.inl ⟨h00,h11⟩
  · exact Or.inr ⟨h01,h10⟩
  · exact False.elim (ha (h01.trans h11.symm))
end
end CurveComplex.HyperellipticModel
