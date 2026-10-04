import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualCommonStripFiniteEdgeStraightening
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual quotient-cone construction in the product max-norm square,
extracted from the existing local construction. No filling is assumed. -/
theorem actual_square_convex_cone_filling (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (f : C({z : ℝ × ℝ // ‖z‖ = 1},V)) (v : V) :
    ∃ (q : C(unitInterval × {z : ℝ × ℝ // ‖z‖ = 1},{z : ℝ × ℝ // ‖z‖ ≤ 1}))
      (G : C({z : ℝ × ℝ // ‖z‖ ≤ 1},V)), Function.Surjective q ∧
      (∀ a, (q a).val = (1-a.1.val) • (a.2 : ℝ × ℝ)) ∧
      ∀ a, (G (q a)).val = (1-a.1.val) • (f a.2).val+a.1.val • v.val := by
  have hQ : IsCompact {z : ℝ × ℝ | ‖z‖ ≤ 1} := by
    convert (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)) using 1
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_prod,Set.mem_Icc,Prod.norm_def,
      Real.norm_eq_abs,max_le_iff,abs_le]
  have hB : IsClosed {z : ℝ × ℝ | ‖z‖ = 1} :=
    isClosed_eq (continuous_fst.norm.max continuous_snd.norm) continuous_const
  let : CompactSpace {z : ℝ × ℝ // ‖z‖ ≤ 1} := isCompact_iff_compactSpace.mp hQ
  let : CompactSpace {z : ℝ × ℝ // ‖z‖ = 1} :=
    isCompact_iff_compactSpace.mp (hQ.of_isClosed_subset hB (fun z hz => hz.le))
  have hradial : ∃ q : C(unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}, {z : ℝ × ℝ // ‖z‖ ≤ 1}),
      Function.Surjective q ∧
      (∀ a b, q a = q b → a = b ∨ a.1 = 1 ∧ b.1 = 1) ∧
      (∀ a : unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}, (q a : ℝ × ℝ) = (1-a.1.val) • (a.2 : ℝ × ℝ)) := by
    let q : C(unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}, {z : ℝ × ℝ // ‖z‖ ≤ 1}) :=
      ⟨fun a => ⟨(1 - (a.1 : ℝ)) • (a.2 : ℝ × ℝ), by
        rw [norm_smul, a.2.property, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr a.1.property.2)]
        linarith [a.1.property.1]⟩,
        by fun_prop⟩
    have hnorm (a : unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}) : ‖(q a : ℝ × ℝ)‖ = 1 - (a.1 : ℝ) := by
      change ‖(1 - (a.1 : ℝ)) • (a.2 : ℝ × ℝ)‖ = _
      rw [norm_smul, a.2.property, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr a.1.property.2)]
    refine ⟨q, ?_, ?_, ?_⟩
    · intro z
      by_cases hz : (z : ℝ × ℝ) = 0
      · refine ⟨(1, ⟨(1,0), by simp⟩), ?_⟩
        apply Subtype.ext
        simp [q, hz]
      · have hn : ‖(z : ℝ × ℝ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
        let u : {z : ℝ × ℝ // ‖z‖ = 1} := ⟨‖(z : ℝ × ℝ)‖⁻¹ • (z : ℝ × ℝ), by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          exact inv_mul_cancel₀ hn⟩
        refine ⟨(⟨1 - ‖(z : ℝ × ℝ)‖, by constructor <;> linarith [z.property, norm_nonneg (z : ℝ × ℝ)]⟩, u), ?_⟩
        apply Subtype.ext
        change (1 - (1 - ‖(z : ℝ × ℝ)‖)) • (‖(z : ℝ × ℝ)‖⁻¹ • (z : ℝ × ℝ)) = (z : ℝ × ℝ)
        rw [sub_sub_cancel, smul_smul, mul_inv_cancel₀ hn, one_smul]
    · intro a b hab
      have ht : a.1 = b.1 := by
        apply Subtype.ext
        have h := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ ≤ 1} => ‖(z : ℝ × ℝ)‖) hab
        rw [hnorm, hnorm] at h
        linarith
      by_cases ha : a.1 = 1
      · exact Or.inr ⟨ha, ht.symm.trans ha⟩
      · left
        apply Prod.ext ht
        apply Subtype.ext
        have h := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ ≤ 1} => (z : ℝ × ℝ)) hab
        change (1 - (a.1 : ℝ)) • (a.2 : ℝ × ℝ) = (1 - (b.1 : ℝ)) • (b.2 : ℝ × ℝ) at h
        rw [← ht] at h
        have hn : 1 - (a.1 : ℝ) ≠ 0 := by
          intro he
          apply ha
          apply Subtype.ext
          change (a.1 : ℝ) = 1
          linarith
        exact (smul_right_injective _ hn) h
    · intro a
      rfl
  obtain ⟨q,hsurj,hfiber,hqformula⟩ := hradial
  let K : C(unitInterval × {z : ℝ × ℝ // ‖z‖ = 1},V) :=
    ⟨fun a => ⟨(1-a.1.val) • (f a.2).val+a.1.val • v.val,
      hV (f a.2).property v.property (by linarith [a.1.property.2]) a.1.property.1 (by ring)⟩,
      by fun_prop⟩
  have hrespect (a b : unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}) (hab : q a = q b) : K a = K b := by
    rcases hfiber a b hab with hab | ⟨ha,hb⟩
    · rw [hab]
    · apply Subtype.ext
      simp [K,ha,hb]
  let G : {z : ℝ × ℝ // ‖z‖ ≤ 1} → V := fun z => K (Function.surjInv hsurj z)
  have hGq (a : unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}) : G (q a) = K a :=
    hrespect _ _ (Function.surjInv_eq hsurj (q a))
  have hquot := q.continuous.isClosedMap.isQuotientMap q.continuous hsurj
  have hGc : Continuous G := hquot.continuous_iff.mpr (by
    have heq : G ∘ q = K := funext hGq
    rw [heq]; exact K.continuous)
  refine ⟨q,⟨G,hGc⟩,hsurj,hqformula,?_⟩
  intro a
  exact congrArg Subtype.val (hGq a)
end CurveComplex.HyperellipticModel
