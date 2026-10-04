import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

def MarkedArc.reverse {M : HyperellipticModel E S} (a : MarkedArc M) : MarkedArc M where
  map := a.map ∘ unitInterval.symm
  continuous := a.continuous.comp unitInterval.continuous_symm
  injective_except_loop_closure := by
    intro t u he
    rcases a.injective_except_loop_closure _ _ he with hh | ⟨h0,h1⟩ | ⟨h1,h0⟩
    · exact Or.inl (unitInterval.symm_bijective.injective hh)
    · exact Or.inr (Or.inr ⟨by simpa using congrArg unitInterval.symm h0,
        by simpa using congrArg unitInterval.symm h1⟩)
    · exact Or.inr (Or.inl ⟨by simpa using congrArg unitInterval.symm h1,
        by simpa using congrArg unitInterval.symm h0⟩)
  start_marked := by simpa using a.end_marked
  end_marked := by simpa using a.start_marked
  marked_only_at_ends := by
    intro t ht
    rcases a.marked_only_at_ends _ ht with h0 | h1
    · exact Or.inr (by simpa using congrArg unitInterval.symm h0)
    · exact Or.inl (by simpa using congrArg unitInterval.symm h1)

@[simp] theorem MarkedArc.reverse_image {M : HyperellipticModel E S} (a : MarkedArc M) :
    a.reverse.image = a.image := by
  ext x
  constructor
  · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symm t,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨unitInterval.symm t,by simp [MarkedArc.reverse,Function.comp_def]⟩

def EssentialMarkedArc.reverse {M : HyperellipticModel E S} (a : EssentialMarkedArc M) :
    EssentialMarkedArc M := ⟨a.val.reverse,by
  rcases a.property with hn | hl
  · left
    change a.val.map 0 ≠ a.val.map 1 at hn
    change a.val.map (unitInterval.symm 0) ≠ a.val.map (unitInterval.symm 1)
    simpa using hn.symm
  · right
    intro U hU
    rw [MarkedArc.reverse_image] at hU
    exact hl U hU⟩

@[simp] theorem EssentialMarkedArc.reverse_map {M : HyperellipticModel E S}
    (a : EssentialMarkedArc M) (t : Interval) :
    a.reverse.val.map t = a.val.map (unitInterval.symm t) := rfl

@[simp] theorem EssentialMarkedArc.reverse_image {M : HyperellipticModel E S}
    (a : EssentialMarkedArc M) : a.reverse.val.image = a.val.image := a.val.reverse_image

 theorem EssentialMarkedArc.reverse_class {M : HyperellipticModel E S}
    (a : EssentialMarkedArc M) :
    Quotient.mk (essentialArcSetoid M) a.reverse = Quotient.mk (essentialArcSetoid M) a := by
  apply Quotient.sound
  change MarkedIsotopyRel M a.reverse.val.image a.val.image
  rw [EssentialMarkedArc.reverse_image]
  exact (markedIsotopy_equivalence M).refl _

end CurveComplex.HyperellipticModel
