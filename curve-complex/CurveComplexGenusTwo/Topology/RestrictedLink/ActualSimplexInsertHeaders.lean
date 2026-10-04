import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
namespace CurveComplex.HyperellipticModel
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualSimplexInsertHeaders_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
theorem actual_simplex_insert_disjoint_representative (M : HyperellipticModel E S) (σ : Finset (EssentialArcClass M))
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (a : EssentialMarkedArc M)
    (ha : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v))) :
    IsArcSimplex M (insert (Quotient.mk (essentialArcSetoid M) a) σ) := by
  classical
  let v0 := Quotient.mk (essentialArcSetoid M) a
  let rep : {v // v ∈ insert v0 σ} → EssentialMarkedArc M := fun v =>
    if h : v.val = v0 then a else r ⟨v.val, (Finset.mem_insert.mp v.property).resolve_left h⟩
  refine ⟨rep, ?_, ?_⟩
  · intro v
    dsimp [rep]
    split_ifs with h
    · exact h.symm
    · exact hr _
  · intro v w hvw
    have hne : v.val ≠ w.val := fun h => hvw (Subtype.ext h)
    dsimp [rep]
    split_ifs with hv hw
    · exact False.elim (hne (hv.trans hw.symm))
    · exact ha _
    · exact (ha _).symm
    · exact hd _ _ (fun h => hne (congrArg (fun x : {v // v ∈ σ} => x.val) h))
end CurveComplex.HyperellipticModel
