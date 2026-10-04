import CurveComplexGenusTwo.Topology.WeightedSurgery.FiniteRealizationTransport

namespace CurveComplex.WeightedFlowScratch

open scoped BigOperators
set_option maxHeartbeats 1000000
variable {V B : Type*} [DecidableEq V] [DecidableEq B]

noncomputable def surgeryCutMass (σ : Finset V) (selected : σ)
    (z : EdgeTime × FiniteSimplex σ) : ℝ := z.1.val * z.2.val selected

noncomputable def surgeryNormalization (σ : Finset V) (selected : σ)
    (branches : Finset B) (z : EdgeTime × FiniteSimplex σ) : ℝ :=
  1 + ((branches.card : ℝ) - 1) * surgeryCutMass σ selected z

theorem surgeryNormalization_positive (σ : Finset V) (selected : σ)
    (branches : Finset B) (hne : branches.Nonempty) (z : EdgeTime × FiniteSimplex σ) :
    0 < surgeryNormalization σ selected branches z := by
  have hn : (1 : ℝ) ≤ branches.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hr : 0 ≤ surgeryCutMass σ selected z :=
    mul_nonneg z.1.property.1 (z.2.property.1 selected)
  have h := mul_nonneg (sub_nonneg.mpr hn) hr
  unfold surgeryNormalization
  linarith

noncomputable def surgeryUnnormalizedWeight (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (replacement : B → V)
    (z : EdgeTime × FiniteSimplex σ) (v : V) : ℝ :=
  (faceInclusion K σ hσ z.2).weight v -
    (if v = selected.val then surgeryCutMass σ selected z else 0) +
      ∑ b ∈ branches, if replacement b = v then surgeryCutMass σ selected z else 0

theorem surgeryUnnormalizedWeight_nonneg (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (replacement : B → V)
    (z : EdgeTime × FiniteSimplex σ) (v : V) :
    0 ≤ surgeryUnnormalizedWeight K σ hσ selected branches replacement z v := by
  have hc : 0 ≤ (faceInclusion K σ hσ z.2).weight v -
      (if v = selected.val then surgeryCutMass σ selected z else 0) := by
    by_cases hv : v = selected.val
    · subst v
      rw [if_pos rfl, faceInclusion_weight_of_mem K σ hσ z.2 selected.val selected.property]
      exact sub_nonneg.mpr (mul_le_of_le_one_left (z.2.property.1 selected) z.1.property.2)
    · rw [if_neg hv, sub_zero]
      exact (faceInclusion K σ hσ z.2).nonneg v
  apply add_nonneg hc
  apply Finset.sum_nonneg
  intro b hb
  split_ifs
  · exact mul_nonneg z.1.property.1 (z.2.property.1 selected)
  · exact le_refl 0

theorem surgeryUnnormalizedWeight_zero_outside (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (replacement : B → V)
    (z : EdgeTime × FiniteSimplex σ) (v : V)
    (hv : v ∉ σ ∪ branches.image replacement) :
    surgeryUnnormalizedWeight K σ hσ selected branches replacement z v = 0 := by
  have hvs : v ∉ σ := fun hs => hv (Finset.mem_union_left _ hs)
  have hvr : v ∉ branches.image replacement := fun hr => hv (Finset.mem_union_right _ hr)
  have hsel : v ≠ selected.val := by
    intro h
    exact hvs (h.symm ▸ selected.property)
  unfold surgeryUnnormalizedWeight
  rw [faceInclusion_weight_of_not_mem K σ hσ z.2 v hvs, if_neg hsel]
  simp only [sub_zero, zero_add]
  apply Finset.sum_eq_zero
  intro b hb
  have hrep : replacement b ≠ v := by
    intro h
    exact hvr (Finset.mem_image.mpr ⟨b, hb, h⟩)
  exact if_neg hrep

theorem surgeryUnnormalizedWeight_sum (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (replacement : B → V)
    (z : EdgeTime × FiniteSimplex σ) :
    (∑ v ∈ σ ∪ branches.image replacement,
      surgeryUnnormalizedWeight K σ hσ selected branches replacement z v) =
        surgeryNormalization σ selected branches z := by
  let τ := σ ∪ branches.image replacement
  have hsel : selected.val ∈ τ := Finset.mem_union_left _ selected.property
  have hsum : (∑ v ∈ τ, (faceInclusion K σ hσ z.2).weight v) = 1 :=
    weight_sum_of_supported K (faceInclusion K σ hσ z.2) τ
      (fun v hv => faceInclusion_weight_of_not_mem K σ hσ z.2 v
        (fun hs => hv (Finset.mem_union_left _ hs)))
  have hcut : (∑ v ∈ τ, if v = selected.val then surgeryCutMass σ selected z else 0) =
      surgeryCutMass σ selected z := by simp [hsel]
  have hnew : (∑ v ∈ τ, ∑ b ∈ branches,
      if replacement b = v then surgeryCutMass σ selected z else 0) =
      (branches.card : ℝ) * surgeryCutMass σ selected z := by
    rw [Finset.sum_comm]
    have heq : (∑ b ∈ branches, ∑ v ∈ τ,
        if replacement b = v then surgeryCutMass σ selected z else 0) =
        ∑ _b ∈ branches, surgeryCutMass σ selected z := by
      apply Finset.sum_congr rfl
      intro b hb
      have hrep : replacement b ∈ τ :=
        Finset.mem_union_right _ (Finset.mem_image_of_mem replacement hb)
      simp [eq_comm, hrep]
    rw [heq]
    simp only [Finset.sum_const, nsmul_eq_mul]
  change (∑ v ∈ τ, ((faceInclusion K σ hσ z.2).weight v -
    (if v = selected.val then surgeryCutMass σ selected z else 0) +
      ∑ b ∈ branches, if replacement b = v then surgeryCutMass σ selected z else 0)) = _
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, hcut, hnew]
  unfold surgeryNormalization
  ring

noncomputable def branchingSurgeryPoint (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (hne : branches.Nonempty) (replacement : B → V)
    (hτ : σ ∪ branches.image replacement ∈ K.faces)
    (z : EdgeTime × FiniteSimplex σ) : RealizationPoint K :=
  ⟨fun v => surgeryUnnormalizedWeight K σ hσ selected branches replacement z v /
      surgeryNormalization σ selected branches z,
    (fun v => div_nonneg (surgeryUnnormalizedWeight_nonneg K σ hσ selected branches replacement z v)
      (le_of_lt (surgeryNormalization_positive σ selected branches hne z))), by
      refine ⟨σ ∪ branches.image replacement, hτ, ?_, ?_⟩
      · intro v hv
        rw [surgeryUnnormalizedWeight_zero_outside K σ hσ selected branches replacement z v hv]
        exact zero_div _
      · rw [← Finset.sum_div, surgeryUnnormalizedWeight_sum]
        exact div_self (ne_of_gt (surgeryNormalization_positive σ selected branches hne z))⟩

theorem surgeryCutMass_continuous (σ : Finset V) (selected : σ) :
    Continuous (surgeryCutMass σ selected) := by
  unfold surgeryCutMass
  exact (continuous_subtype_val.comp continuous_fst).mul
    ((continuous_apply selected).comp (continuous_subtype_val.comp continuous_snd))

theorem branchingSurgeryPoint_continuous (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (hne : branches.Nonempty) (replacement : B → V)
    (hτ : σ ∪ branches.image replacement ∈ K.faces) :
    Continuous (branchingSurgeryPoint K σ hσ selected branches hne replacement hτ) := by
  apply continuous_of_face_coordinates K (σ ∪ branches.image replacement) hτ
  · intro z v hv
    change surgeryUnnormalizedWeight K σ hσ selected branches replacement z v /
      surgeryNormalization σ selected branches z = 0
    rw [surgeryUnnormalizedWeight_zero_outside K σ hσ selected branches replacement z v hv]
    exact zero_div _
  · intro v
    have hc : Continuous (fun z : EdgeTime × FiniteSimplex σ =>
        (faceInclusion K σ hσ z.2).weight v) :=
      ((continuous_weight K v).comp (continuous_faceInclusion K σ hσ)).comp continuous_snd
    have hr := surgeryCutMass_continuous σ selected
    have hcut : Continuous (fun z : EdgeTime × FiniteSimplex σ =>
        if v = selected.val then surgeryCutMass σ selected z else 0) := by
      split_ifs
      · exact hr
      · exact continuous_const
    have hnew : Continuous (fun z : EdgeTime × FiniteSimplex σ =>
        ∑ b ∈ branches, if replacement b = v then surgeryCutMass σ selected z else 0) := by
      apply continuous_finsetSum
      intro b hb
      split_ifs
      · exact hr
      · exact continuous_const
    have hd : Continuous (surgeryNormalization σ selected branches) :=
      continuous_const.add (continuous_const.mul hr)
    exact ((hc.sub hcut).add hnew).div hd
      (fun z => ne_of_gt (surgeryNormalization_positive σ selected branches hne z))

theorem branchingSurgeryPoint_zero (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (hne : branches.Nonempty) (replacement : B → V)
    (hτ : σ ∪ branches.image replacement ∈ K.faces) (x : FiniteSimplex σ) :
    branchingSurgeryPoint K σ hσ selected branches hne replacement hτ (0, x) =
      faceInclusion K σ hσ x := by
  apply RealizationPoint.ext
  funext v
  simp [branchingSurgeryPoint, surgeryNormalization, surgeryCutMass, surgeryUnnormalizedWeight]

theorem branchingSurgeryPoint_zeroWeight_fixed (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (hne : branches.Nonempty) (replacement : B → V)
    (hτ : σ ∪ branches.image replacement ∈ K.faces)
    (t : EdgeTime) (x : FiniteSimplex σ) (hx : x.val selected = 0) :
    branchingSurgeryPoint K σ hσ selected branches hne replacement hτ (t, x) =
      faceInclusion K σ hσ x := by
  apply RealizationPoint.ext
  funext v
  simp [branchingSurgeryPoint, surgeryNormalization, surgeryCutMass, surgeryUnnormalizedWeight, hx]

end CurveComplex.WeightedFlowScratch
