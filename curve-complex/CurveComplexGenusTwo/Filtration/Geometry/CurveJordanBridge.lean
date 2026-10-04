import CurveComplexGenusTwo.Filtration.Geometry.ActualBigon
import CurveComplexGenusTwo.Dependencies.SpherePort

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Original embedded circles, including actual parallel-pair circles, feed the existing sphere Jordan API. -/
theorem actualCurve_sphereJordan (M : HyperellipticModel E S) (c : Curve S) :
    ∃ J : CurveComplex.SpherePort.JordanCurve, J.image = M.sphere '' c.image := by
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  let f : Interval → CurveComplex.SpherePort.Sphere := fun t =>
    M.sphere (c.map (e ((t : ℝ) : AddCircle (1 : ℝ))))
  have hf : Continuous f := M.sphere.continuous.comp (c.embedded.continuous.comp
    (e.continuous.comp ((AddCircle.continuous_mk' 1).comp continuous_subtype_val)))
  have hinj : ∀ t u : Interval, f t = f u →
      t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0) := by
    intro t u h
    have hm : ((t : ℝ) : AddCircle (1 : ℝ)) = ((u : ℝ) : AddCircle (1 : ℝ)) :=
      e.injective (c.embedded.injective (M.sphere.injective h))
    by_cases ht : (t : ℝ) = 1
    · by_cases hu : (u : ℝ) = 1
      · exact Or.inl (Subtype.ext (ht.trans hu.symm))
      · have huLt : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 hu
        have hm0 : (0 : AddCircle (1 : ℝ)) = ((u : ℝ) : AddCircle (1 : ℝ)) := by
          simpa only [ht, AddCircle.coe_period] using hm
        have hu0 : (u : ℝ) = 0 :=
          ((AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
            (p := (1 : ℝ)) (by norm_num) (by simpa using (show (u : ℝ) ∈ Set.Ico 0 1 from ⟨u.property.1, huLt⟩))).mp hm0).symm
        exact Or.inr (Or.inr ⟨Subtype.ext ht, Subtype.ext hu0⟩)
    · have htLt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
      by_cases hu : (u : ℝ) = 1
      · have hm0 : ((t : ℝ) : AddCircle (1 : ℝ)) = (0 : AddCircle (1 : ℝ)) := by
          simpa only [hu, AddCircle.coe_period] using hm
        have ht0 : (t : ℝ) = 0 :=
          (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
            (p := (1 : ℝ)) (by simpa using (show (t : ℝ) ∈ Set.Ico 0 1 from ⟨t.property.1, htLt⟩)) (by norm_num)).mp hm0
        exact Or.inr (Or.inl ⟨Subtype.ext ht0, Subtype.ext hu⟩)
      · have huLt : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 hu
        exact Or.inl (Subtype.ext ((AddCircle.coe_eq_coe_iff_of_mem_Ico
          (a := (0 : ℝ)) (p := (1 : ℝ)) (by simpa using (show (t : ℝ) ∈ Set.Ico 0 1 from ⟨t.property.1, htLt⟩))
          (by simpa using (show (u : ℝ) ∈ Set.Ico 0 1 from ⟨u.property.1, huLt⟩))).mp hm))
  let J : CurveComplex.SpherePort.JordanCurve := {
    map := f
    continuous := hf
    injective_except_ends := hinj
    closed := by
      dsimp [f]
      simp only [AddCircle.coe_period] }
  refine ⟨J, ?_⟩
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨c.map (e ((t : ℝ) : AddCircle (1 : ℝ))), ⟨_, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    obtain ⟨t, ht, hte⟩ := AddCircle.eq_coe_Ico (e.symm z)
    refine ⟨⟨t, ht.1, ht.2.le⟩, ?_⟩
    change M.sphere (c.map (e (t : AddCircle (1 : ℝ)))) = M.sphere (c.map z)
    rw [hte, e.apply_symm_apply]

end CurveComplex.HyperellipticModel
