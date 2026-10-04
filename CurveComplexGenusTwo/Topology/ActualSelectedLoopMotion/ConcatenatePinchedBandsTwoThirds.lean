import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib

namespace CurveComplex
open Set Topology

/-- Two pinched bands glue along their exact prescribed seam, including the
common base. The cross-band collision premise identifies only that seam. -/
theorem concatenate_pinched_bands_two_thirds
    {X : Type} [TopologicalSpace X] (base : X)
    (A B : C(Interval × Interval,X))
    (hAend : ∀ w, A (0,w) = base ∧ A (1,w) = base)
    (hBend : ∀ w, B (0,w) = base ∧ B (1,w) = base)
    (hAinj : ∀ s w s' w', A (s,w) = A (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (hBinj : ∀ s w s' w', B (s,w) = B (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (hseam : ∀ s, A (s,1) = B (s,0))
    (hmeet : ∀ s w s' w', A (s,w) = B (s',w') →
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)) ∨
      (s = s' ∧ w = 1 ∧ w' = 0)) :
    ∃ C : C(Interval × Interval,X),
      (∀ s, C (s,0) = A (s,0)) ∧
      (∀ s, C (s,1) = B (s,1)) ∧
      (∀ s, C (s,⟨2/3,by norm_num⟩) = A (s,1)) ∧
      (∀ s, C (s,⟨1/3,by norm_num⟩) = A (s,⟨1/2,by norm_num⟩)) ∧
      (∀ w, C (0,w) = base ∧ C (1,w) = base) ∧
      (∀ s w s' w', C (s,w) = C (s',w') →
        (s = s' ∧ w = w') ∨
        ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1))) ∧
      Set.range C ⊆ Set.range A ∪ Set.range B := by
  let L : Interval → Interval := fun w => Set.projIcc 0 1 zero_le_one (3*(w : ℝ)/2)
  let R : Interval → Interval := fun w => Set.projIcc 0 1 zero_le_one (3*(w : ℝ)-2)
  have hLc : Continuous L := continuous_projIcc.comp (by fun_prop)
  have hRc : Continuous R := continuous_projIcc.comp (by fun_prop)
  have hL (w : Interval) (hw : (w : ℝ) ≤ 2/3) : (L w : ℝ) = 3*(w : ℝ)/2 := by
    exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one
      (show 3*(w : ℝ)/2 ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith [w.property.1]))
  have hR (w : Interval) (hw : 2/3 ≤ (w : ℝ)) : (R w : ℝ) = 3*(w : ℝ)-2 := by
    exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one
      (show 3*(w : ℝ)-2 ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith [w.property.2]))
  have hLhalf : L ⟨2/3,by norm_num⟩ = 1 := Subtype.ext (by rw [hL]; norm_num; norm_num)
  have hRhalf : R ⟨2/3,by norm_num⟩ = 0 := Subtype.ext (by rw [hR]; norm_num; norm_num)
  let C : C(Interval × Interval,X) :=
    ⟨fun z => if (z.2 : ℝ) ≤ 2/3 then A (z.1,L z.2) else B (z.1,R z.2),by
      apply continuous_if_le (by fun_prop) continuous_const
        (A.continuous.comp (continuous_fst.prodMk (hLc.comp continuous_snd))).continuousOn
        (B.continuous.comp (continuous_fst.prodMk (hRc.comp continuous_snd))).continuousOn
      intro z hz
      change A (z.1,L z.2) = B (z.1,R z.2)
      have hw : z.2 = ⟨2/3,by norm_num⟩ := Subtype.ext hz
      rw [hw,hLhalf,hRhalf]
      exact hseam z.1⟩
  have hleft (s w : Interval) (hw : (w : ℝ) ≤ 2/3) : C (s,w) = A (s,L w) := ite_eq_left hw
  have hright (s w : Interval) (hw : ¬ (w : ℝ) ≤ 2/3) : C (s,w) = B (s,R w) := ite_eq_right hw
  refine ⟨C,?_,?_,?_,?_,?_,?_,?_⟩
  · intro s
    rw [hleft s 0 (by norm_num)]
    congr 2
    apply Subtype.ext
    rw [hL]
    · norm_num
    · norm_num
  · intro s
    rw [hright s 1 (by norm_num)]
    congr 2
    apply Subtype.ext
    rw [hR]
    · norm_num
    · norm_num
  · intro s
    rw [hleft s _ (by norm_num),hLhalf]
  · intro s
    rw [hleft s _ (by norm_num)]
    congr 2
    apply Subtype.ext
    rw [hL]
    · norm_num
    · norm_num
  · intro w
    by_cases hw : (w : ℝ) ≤ 2/3
    · rw [hleft 0 w hw,hleft 1 w hw]
      exact hAend _
    · rw [hright 0 w hw,hright 1 w hw]
      exact hBend _
  · intro s w s' w' he
    by_cases hw : (w : ℝ) ≤ 2/3
    · by_cases hw' : (w' : ℝ) ≤ 2/3
      · rw [hleft s w hw,hleft s' w' hw'] at he
        rcases hAinj _ _ _ _ he with h | h
        · left
          refine ⟨h.1,Subtype.ext ?_⟩
          have hew := congrArg Subtype.val h.2
          rw [hL w hw,hL w' hw'] at hew
          linarith
        · exact Or.inr h
      · rw [hleft s w hw,hright s' w' hw'] at he
        rcases hmeet _ _ _ _ he with h | h
        · exact Or.inr h
        · have hew := congrArg Subtype.val h.2.2
          rw [hR w' (not_le.mp hw').le] at hew
          have hh := not_le.mp hw'
          norm_num at hew
          linarith
    · by_cases hw' : (w' : ℝ) ≤ 2/3
      · rw [hright s w hw,hleft s' w' hw'] at he
        rcases hmeet _ _ _ _ he.symm with h | h
        · exact Or.inr ⟨h.2,h.1⟩
        · have hew := congrArg Subtype.val h.2.2
          rw [hR w (not_le.mp hw).le] at hew
          have hh := not_le.mp hw
          norm_num at hew
          linarith
      · rw [hright s w hw,hright s' w' hw'] at he
        rcases hBinj _ _ _ _ he with h | h
        · left
          refine ⟨h.1,Subtype.ext ?_⟩
          have hew := congrArg Subtype.val h.2
          rw [hR w (not_le.mp hw).le,hR w' (not_le.mp hw').le] at hew
          linarith
        · exact Or.inr h
  · rintro z ⟨⟨s,w⟩,rfl⟩
    by_cases hw : (w : ℝ) ≤ 2/3
    · exact Or.inl ⟨(s,L w),(hleft s w hw).symm⟩
    · exact Or.inr ⟨(s,R w),(hright s w hw).symm⟩

end CurveComplex
