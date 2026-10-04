import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions

/-! Definition-only import bridge for the verified actual arc-geometry helpers.
All three local definition bodies are exact copies of the frozen V3 scaffold.
Base actual objects and the three endpoint facts reuse the canonical master module.
Open source producers and their consumers are deliberately absent. -/
namespace CurveComplex.HyperellipticModel
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualArcFiltrationV3_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

noncomputable def actualY (M : HyperellipticModel E S) (p : ℤ) :
    FiniteComplex (EssentialArcClass M) :=
  filtration (actualA M) (actualArcLabels M) p

abbrev ActualStratum (M : HyperellipticModel E S) (p : ℕ) :=
  strata (actualA M) (actualArcLabels M) p

noncomputable def actualRestrictedLink (M : HyperellipticModel E S)
    {p : ℕ} (T : ActualStratum M p) :
    FiniteComplex (EssentialArcClass M) :=
  restrictedLink (actualA M) (actualArcLabels M) (p := p) T

end CurveComplex.HyperellipticModel
