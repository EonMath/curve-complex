import CurveComplexGenusTwo.Foundations.Definitions

/-!
The first four candidate declarations in
`scratch/formalizer/foundations/Intersection.lean`, ported unchanged against
the now-proved master `Foundations.Definitions`. This local port isolates the
old formalizer `.olean`, whose earlier `Definitions` import still has `sorryAx`.
-/

namespace CurveComplex

/-- A topological crossing: in a common local chart, the two curve images are
exactly the two coordinate axes. Tangencies are excluded. -/
def CrossesAt {S : Type*} [TopologicalSpace S]
    (a b : Curve S) (p : S) : Prop :=
  ∃ (U : Set S) (V : Set (ℝ × ℝ))
    (hU : p ∈ U) (h : U ≃ₜ V),
    IsOpen U ∧ IsOpen V ∧
    ((h ⟨p, hU⟩ : V) : ℝ × ℝ) = (0, 0) ∧
    (∀ (x : S) (hx : x ∈ U),
      (x ∈ a.image ↔ ((h ⟨x, hx⟩ : V) : ℝ × ℝ).1 = 0) ∧
      (x ∈ b.image ↔ ((h ⟨x, hx⟩ : V) : ℝ × ℝ).2 = 0))

/-- Finite intersection is separate from local transversality. -/
def Transverse {S : Type*} [TopologicalSpace S] (a b : Curve S) : Prop :=
  (a.image ∩ b.image).Finite ∧
  ∀ p ∈ a.image ∩ b.image, CrossesAt a b p

/-- Admissible transverse intersection counts between essential classes. -/
def intersectionCounts {S : Type*} [TopologicalSpace S]
    (α β : Vertex S) : Set ℕ :=
  {n | ∃ a b : EssentialCurve S,
    Quotient.mk (essentialCurveSetoid S) a = α ∧
    Quotient.mk (essentialCurveSetoid S) b = β ∧
    ∃ h : Transverse a.val b.val,
      n = h.1.toFinset.card}

/-- Geometric intersection number, as in the candidate definition. -/
noncomputable def geometricIntersection {S : Type*} [TopologicalSpace S]
    (α β : Vertex S) : ℕ :=
  sInf (intersectionCounts α β)

end CurveComplex

#print axioms CurveComplex.CrossesAt
#print axioms CurveComplex.Transverse
#print axioms CurveComplex.intersectionCounts
#print axioms CurveComplex.geometricIntersection
