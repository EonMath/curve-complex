import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualPeriodicVerticalShear

open Set Topology Schoenflies CurveComplex unitInterval

/-- A literal horizontal graph has an actual puncture-relative periodic
straightening. The target height is derived from the source at the mark's
horizontal coordinate, not prescribed by incompatible physical endpoints. -/
theorem actual_periodic_graph_has_marked_straightening
    (G : C(ℝ, Plane)) (T : ℝ) (p : Plane)
    (hFirst : ∀ x, G x 0 = x)
    (hPeriod : ∀ (k : ℤ) x,
      G (x + (k : ℝ) * T) = G x + Plane.mk ((k : ℝ) * T) 0) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t (i : ℤ × ℤ) z,
        H.map (t, z + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) =
          H.map (t,z) + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) ∧
      (∀ t (i : ℤ × ℤ),
        H.map (t,p + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) =
          p + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) ∧
      (∀ x, H.finalMap (G x) = Plane.mk x (G (p 0) 1)) ∧
      H.finalMap '' range G = range (fun x : ℝ => Plane.mk x (G (p 0) 1)) := by
  let β : C(ℝ, ℝ) := ⟨fun x => G (p 0) 1 - G x 1, by fun_prop⟩
  have hβ : ∀ (k : ℤ) x, β (x + (k : ℝ) * T) = β x := by
    intro k x
    have hy := congrArg (fun z : Plane => z 1) (hPeriod k x)
    change G (x + (k : ℝ) * T) 1 = G x 1 + 0 at hy
    change G (p 0) 1 - G (x + (k : ℝ) * T) 1 = G (p 0) 1 - G x 1
    rw [hy, add_zero]
  obtain ⟨H,hMap,hEq,hFix,_⟩ := actual_periodic_vertical_shear_isotopy β T 1 hβ
  have hMove : ∀ x, H.finalMap (G x) = Plane.mk x (G (p 0) 1) := by
    intro x
    rw [AmbientIsotopy.finalMap, hMap, hFirst]
    ext k
    fin_cases k <;> simp [β]
  refine ⟨H,hEq,?_,hMove,?_⟩
  · intro t i
    apply hFix
    change β (p 0 + (i.1 : ℝ) * T) = 0
    rw [hβ]
    simp [β]
  · ext z
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      exact ⟨x,(hMove x).symm⟩
    · rintro ⟨x,rfl⟩
      exact ⟨G x,⟨x,rfl⟩,hMove x⟩
