import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualLocalizedCrossingPlane
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingSlidePositions

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

theorem actual_finite_nonzero_coordinate_margin (K : Set ℝ) (hK : K.Finite)
    (hzero : ∀ x ∈ K, x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x ∈ K, ε < |x| := by
  classical
  induction K, hK using Set.Finite.induction_on with
  | empty => exact ⟨1/2,by norm_num,by norm_num,by simp⟩
  | @insert x K hx hK ih =>
    obtain ⟨δ,hδ,hδ1,hcover⟩ := ih (fun y hy => hzero y (mem_insert_of_mem x hy))
    have hx0 : 0 < |x| := abs_pos.mpr (hzero x (mem_insert x K))
    let ε := min δ (|x|/2)
    refine ⟨ε,lt_min hδ (half_pos hx0),(min_le_left _ _).trans_lt hδ1,?_⟩
    intro y hy
    rcases mem_insert_iff.mp hy with rfl | hy
    · exact (min_le_right _ _).trans_lt (by linarith)
    · exact (min_le_left _ _).trans_lt (hcover y hy)

/-- Choose a literal smaller slide support from the actual finite contacts.
All other original contact points are outside that support, including contacts
of the selected representative itself. No clearance radius is an input. -/
theorem actual_position_contact_coordinate_margin
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (U : Set S) (V : Set Plane) (e : U ≃ₜ V)
    (haxis : ∀ q : U, q.val ∈ anchor.val.image ↔ (e q).val 1 = 0)
    (p : U) (hp0 : (e p).val = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ v q, q ∈ crossings M anchor (P.rep v) → q ≠ p.val →
        ∀ hq : q ∈ U, ε < |(e ⟨q,hq⟩).val 0| := by
  classical
  let C : Set S := ⋃ v : {v // v ∈ F}, crossings M anchor (P.rep v)
  have hC : C.Finite := finite_iUnion P.finite
  let K : Set ℝ := (fun q : U => (e q).val 0) ''
    {q : U | q.val ∈ C ∧ q.val ≠ p.val}
  have hK : K.Finite := ((hC.preimage Subtype.val_injective.injOn).subset
    (show {q : U | q.val ∈ C ∧ q.val ≠ p.val} ⊆ Subtype.val ⁻¹' C from fun _ h => h.1)).image _
  have hn : ∀ x ∈ K, x ≠ 0 := by
    rintro x ⟨q,hq,rfl⟩ he
    apply hq.2
    have hqa : q.val ∈ anchor.val.image := by
      obtain ⟨v,hv⟩ := mem_iUnion.mp hq.1
      exact hv.1.1
    have hy := (haxis q).mp hqa
    have hqp : (e q).val = (e p).val := by
      rw [hp0]
      ext i
      fin_cases i
      · exact he
      · exact hy
    exact congrArg Subtype.val (e.injective (Subtype.ext hqp))
  obtain ⟨ε,hε,hε1,hcover⟩ := actual_finite_nonzero_coordinate_margin K hK hn
  refine ⟨ε,hε,hε1,?_⟩
  intro v q hq hne hqU
  exact hcover _ ⟨⟨q,hqU⟩,⟨mem_iUnion.mpr ⟨v,hq⟩,hne⟩,rfl⟩
end
end CurveComplex.HyperellipticModel.ArcSurgery
