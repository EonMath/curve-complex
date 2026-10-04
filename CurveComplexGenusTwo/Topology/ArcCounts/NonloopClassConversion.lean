import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions
namespace CurveComplex.HyperellipticModel
open scoped Classical
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

def NonLoopArc.toEssential {M : HyperellipticModel E S} (a : NonLoopArc M) :
    EssentialMarkedArc M := ⟨a.val, Or.inl a.property⟩

def nonloopToEssentialClass (M : HyperellipticModel E S) :
    NonLoopArcClass M → EssentialArcClass M :=
  Quotient.map (fun a => a.toEssential) (fun _ _ h => h)

theorem nonloopToEssentialClass_injective (M : HyperellipticModel E S) :
    Function.Injective (nonloopToEssentialClass M) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y h
  change Quotient.mk (essentialArcSetoid M) x.toEssential =
    Quotient.mk (essentialArcSetoid M) y.toEssential at h
  have hr : MarkedIsotopyRel M x.val.image y.val.image := Quotient.exact h
  exact Quotient.sound hr

@[simp] theorem nonloopToEssentialClass_mk (M : HyperellipticModel E S)
    (a : NonLoopArc M) :
    nonloopToEssentialClass M (Quotient.mk (nonLoopArcSetoid M) a) =
      Quotient.mk (essentialArcSetoid M) a.toEssential := rfl

theorem nonloopToEssentialClass_image_card (M : HyperellipticModel E S)
    (sigma : Finset (NonLoopArcClass M)) :
    (sigma.image (nonloopToEssentialClass M)).card = sigma.card := by
  classical
  exact Finset.card_image_of_injective _ (nonloopToEssentialClass_injective M)
end CurveComplex.HyperellipticModel
