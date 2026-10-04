import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedIntervalMesh

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A literal compact subinterval converts local real slices to slices of the
whole actual marked arc. -/
theorem actual_compact_interval_slice_image
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1)
    (η : C(Interval,S))
    (hη : ∀ t, η t = a.val.map ⟨l+(u-l)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩)
    (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1) :
    (η ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc A B =
      (a.val.map ∘ Set.projIcc 0 1 zero_le_one) ''
        Set.Icc (l+(u-l)*A) (l+(u-l)*B) := by
  have hpos : 0 < u-l := sub_pos.mpr hlu
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    have ht0 : 0 ≤ t := hA.trans ht.1
    have ht1 : t ≤ 1 := ht.2.trans hB
    refine ⟨l+(u-l)*t,⟨by nlinarith [ht.1],by nlinarith [ht.2]⟩,?_⟩
    have hp : Set.projIcc 0 1 zero_le_one t = (⟨t,⟨ht0,ht1⟩⟩:Interval) := Set.projIcc_of_mem _ _
    have htglobal : l+(u-l)*t ∈ Set.Icc (0:ℝ) 1 := by constructor <;> nlinarith
    simp only [Function.comp_apply]
    rw [hp,hη]
    exact congrArg a.val.map (Set.projIcc_of_mem zero_le_one htglobal)
  · rintro ⟨t,ht,rfl⟩
    let s : ℝ := (t-l)/(u-l)
    have hslow : A ≤ s := by
      dsimp [s]
      apply (le_div_iff₀ hpos).mpr
      nlinarith [ht.1]
    have hshigh : s ≤ B := by
      dsimp [s]
      apply (div_le_iff₀ hpos).mpr
      nlinarith [ht.2]
    have hs0 : 0 ≤ s := hA.trans hslow
    have hs1 : s ≤ 1 := hshigh.trans hB
    have ht0 : 0 ≤ t := by nlinarith [ht.1]
    have ht1 : t ≤ 1 := by nlinarith [ht.2]
    refine ⟨s,⟨hslow,hshigh⟩,?_⟩
    rw [Function.comp_apply,Set.projIcc_of_mem zero_le_one ⟨hs0,hs1⟩,hη,
      Function.comp_apply,Set.projIcc_of_mem zero_le_one ⟨ht0,ht1⟩]
    apply congrArg a.val.map
    apply Subtype.ext
    change l+(u-l)*((t-l)/(u-l)) = t
    field_simp
    ring

end CurveComplex.HyperellipticModel
