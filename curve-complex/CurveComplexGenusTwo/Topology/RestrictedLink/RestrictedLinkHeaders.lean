import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
namespace CurveGenusTwo.Filtration
variable {V B : Type} [DecidableEq V]
/-- A new nonloop endpoint pair introduces no new bad vertices. -/
theorem badVertices_insert_fresh_endpoint (a : ArcLabels V B) (σ : Finset V) (v : V)
    (hl : ¬ a.isLoop v)
    (he : ∀ w ∈ σ, w ≠ v → ¬ a.isLoop w → a.endpointPair w ≠ a.endpointPair v) :
    badVertices a (insert v σ) = badVertices a σ := by
  classical
  by_cases hv : v ∈ σ
  · simp [Finset.insert_eq_of_mem hv]
  ext w
  simp only [badVertices, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hw, hb⟩
    have hwv : w ≠ v := by
      intro h
      subst w
      rcases hb with h | ⟨z, hz, hzv, _, hzl, hze⟩
      · exact hl h
      · rcases hz with rfl | hz
        · exact hzv rfl
        · exact he z hz hzv hzl hze
    have hwσ : w ∈ σ := hw.resolve_left hwv
    refine ⟨hwσ, ?_⟩
    rcases hb with h | ⟨z, hz, hzw, hwl, hzl, hze⟩
    · exact Or.inl h
    · refine Or.inr ⟨z, ?_, hzw, hwl, hzl, hze⟩
      rcases hz with rfl | hz
      · exact False.elim (he w hwσ hwv hwl hze.symm)
      · exact hz
  · rintro ⟨hw, hb⟩
    refine ⟨Or.inr hw, ?_⟩
    rcases hb with hl | ⟨z, hz, hzw, hwl, hzl, heq⟩
    · exact Or.inl hl
    · exact Or.inr ⟨z, Or.inr hz, hzw, hwl, hzl, heq⟩

end CurveGenusTwo.Filtration
