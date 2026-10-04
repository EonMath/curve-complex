import CurveComplexGenusTwo.Topology.ActualCompactSideDoubledCut.HalfStripOpenEmbedding
import CurveComplexGenusTwo.Topology.ActualCompactSideDoubledCut.QuadrantFlatten

open Set Topology CurveComplex

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

private abbrev Nonneg := Set.Ici (0 : ℝ)
private abbrev HalfWidth := Set.Icc (0 : ℝ) 1
private abbrev HalfBand := Interval × HalfWidth

def leftPatch : Set HalfBand :=
  {z | (z.1 : ℝ) < 1 ∧ (z.2 : ℝ) < 1}

def quadrantPatch : Set (Nonneg × Nonneg) :=
  {z | (z.1 : ℝ) < 1 ∧ (z.2 : ℝ) < 1}

theorem quadrantPatch_isOpen : IsOpen quadrantPatch := by
  exact (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)

theorem leftPatch_isOpen : IsOpen leftPatch := by
  exact (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)

theorem leftPatch_subset_halfOpen : leftPatch ⊆ halfOpen := by
  intro z hz
  exact hz.2

noncomputable def leftPatchHomeomorph : ↥leftPatch ≃ₜ ↥quadrantPatch where
  toFun z := ⟨(⟨z.val.1.val, z.val.1.property.1⟩,
    ⟨z.val.2.val, z.val.2.property.1⟩), z.property⟩
  invFun z := ⟨(⟨z.val.1.val, ⟨z.val.1.property, le_of_lt z.property.1⟩⟩,
    ⟨z.val.2.val, ⟨z.val.2.property, le_of_lt z.property.2⟩⟩), z.property⟩
  left_inv := by intro z; apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv := by intro z; apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem leftPatch_to_halfSpace_openEmbedding :
    Topology.IsOpenEmbedding
      (fun z : ↥leftPatch => quadrantHalfSpace
        (leftPatchHomeomorph z).val) := by
  have hq : Topology.IsOpenEmbedding
      (fun z : ↥quadrantPatch => (z.val : Nonneg × Nonneg)) :=
    ⟨Topology.IsEmbedding.subtypeVal, by
      simpa only [Subtype.range_coe] using quadrantPatch_isOpen⟩
  exact quadrantHalfSpace.isOpenEmbedding.comp
    (hq.comp leftPatchHomeomorph.isOpenEmbedding)

theorem leftPatch_cut_openEmbedding
    {S : Type} [TopologicalSpace S] {n : ℕ}
    (E : Fin n → C(Interval × Set.Icc (-1 : ℝ) 1,S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) :
    Topology.IsOpenEmbedding (fun z : ↥leftPatch => halfCut E i b z.val) := by
  let inc : ↥leftPatch → ↥halfOpen := Set.inclusion leftPatch_subset_halfOpen
  have hinc : Topology.IsOpenEmbedding inc :=
    Topology.IsOpenEmbedding.inclusion leftPatch_subset_halfOpen
      (by exact leftPatch_isOpen.preimage continuous_subtype_val)
  exact (halfCut_openEmbedding E hemb hdisjoint i b).comp hinc

noncomputable def leftCutChart
    {S : Type} [TopologicalSpace S] {n : ℕ}
    (E : Fin n → C(Interval × Set.Icc (-1 : ℝ) 1,S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) :
    OpenPartialHomeomorph (CutQuotient E) (EuclideanHalfSpace 2) := by
  letI : Nonempty ↥leftPatch :=
    ⟨⟨(0,⟨0,by norm_num⟩), by norm_num [leftPatch]⟩⟩
  exact (leftPatch_to_halfSpace_openEmbedding.toOpenPartialHomeomorph _).lift_openEmbedding
    (leftPatch_cut_openEmbedding E hemb hdisjoint i b)

def rightPatch : Set HalfBand :=
  {z | 0 < (z.1 : ℝ) ∧ (z.2 : ℝ) < 1}

theorem rightPatch_isOpen : IsOpen rightPatch := by
  exact (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).inter
    (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)

theorem rightPatch_subset_halfOpen : rightPatch ⊆ halfOpen := by
  intro z hz
  exact hz.2

noncomputable def rightPatchHomeomorph : ↥rightPatch ≃ₜ ↥quadrantPatch where
  toFun z := ⟨(⟨1 - z.val.1.val, by
      exact sub_nonneg.mpr z.val.1.property.2⟩,
    ⟨z.val.2.val, z.val.2.property.1⟩), by
      change 1 - z.val.1.val < 1 ∧ z.val.2.val < 1
      exact ⟨by linarith [z.property.1], z.property.2⟩⟩
  invFun z := ⟨(⟨1 - z.val.1.val, by
      have h0 : 0 ≤ z.val.1.val := z.val.1.property
      have h1 : z.val.1.val < 1 := z.property.1
      constructor <;> linarith⟩,
    ⟨z.val.2.val, ⟨z.val.2.property, le_of_lt z.property.2⟩⟩), by
      change 0 < 1 - z.val.1.val ∧ z.val.2.val < 1
      exact ⟨by linarith [z.property.1], z.property.2⟩⟩
  left_inv := by intro z; apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> ring
  right_inv := by intro z; apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem rightPatch_to_halfSpace_openEmbedding :
    Topology.IsOpenEmbedding
      (fun z : ↥rightPatch => quadrantHalfSpace
        (rightPatchHomeomorph z).val) := by
  have hq : Topology.IsOpenEmbedding
      (fun z : ↥quadrantPatch => (z.val : Nonneg × Nonneg)) :=
    ⟨Topology.IsEmbedding.subtypeVal, by
      simpa only [Subtype.range_coe] using quadrantPatch_isOpen⟩
  exact quadrantHalfSpace.isOpenEmbedding.comp
    (hq.comp rightPatchHomeomorph.isOpenEmbedding)

theorem rightPatch_cut_openEmbedding
    {S : Type} [TopologicalSpace S] {n : ℕ}
    (E : Fin n → C(Interval × Set.Icc (-1 : ℝ) 1,S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) :
    Topology.IsOpenEmbedding (fun z : ↥rightPatch => halfCut E i b z.val) := by
  let inc : ↥rightPatch → ↥halfOpen := Set.inclusion rightPatch_subset_halfOpen
  have hinc : Topology.IsOpenEmbedding inc :=
    Topology.IsOpenEmbedding.inclusion rightPatch_subset_halfOpen
      (by exact rightPatch_isOpen.preimage continuous_subtype_val)
  exact (halfCut_openEmbedding E hemb hdisjoint i b).comp hinc

noncomputable def rightCutChart
    {S : Type} [TopologicalSpace S] {n : ℕ}
    (E : Fin n → C(Interval × Set.Icc (-1 : ℝ) 1,S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) :
    OpenPartialHomeomorph (CutQuotient E) (EuclideanHalfSpace 2) := by
  letI : Nonempty ↥rightPatch :=
    ⟨⟨(1,⟨0,by norm_num⟩), by norm_num [rightPatch]⟩⟩
  exact (rightPatch_to_halfSpace_openEmbedding.toOpenPartialHomeomorph _).lift_openEmbedding
    (rightPatch_cut_openEmbedding E hemb hdisjoint i b)

theorem halfCut_mem_endpoint_chart
    {S : Type} [TopologicalSpace S] {n : ℕ}
    (E : Fin n → C(Interval × Set.Icc (-1 : ℝ) 1,S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) (z : HalfBand)
    (hz : z ∈ halfOpen) :
    halfCut E i b z ∈ (leftCutChart E hemb hdisjoint i b).source ∨
      halfCut E i b z ∈ (rightCutChart E hemb hdisjoint i b).source := by
  letI : Nonempty ↥leftPatch :=
    ⟨⟨(0,⟨0,by norm_num⟩), by norm_num [leftPatch]⟩⟩
  letI : Nonempty ↥rightPatch :=
    ⟨⟨(1,⟨0,by norm_num⟩), by norm_num [rightPatch]⟩⟩
  by_cases ht : (z.1 : ℝ) < 1
  · left
    rw [leftCutChart, OpenPartialHomeomorph.lift_openEmbedding_source]
    exact ⟨⟨z, ⟨ht,hz⟩⟩, by
      simp [leftPatch_to_halfSpace_openEmbedding.toOpenPartialHomeomorph_source], rfl⟩
  · right
    have ht' : 0 < (z.1 : ℝ) := by
      have h0 := z.1.property.1
      have h1 := z.1.property.2
      push_neg at ht
      linarith
    rw [rightCutChart, OpenPartialHomeomorph.lift_openEmbedding_source]
    exact ⟨⟨z, ⟨ht',hz⟩⟩, by
      simp [rightPatch_to_halfSpace_openEmbedding.toOpenPartialHomeomorph_source], rfl⟩

theorem leftCutChart_coord0
    {S : Type} [TopologicalSpace S] {n : ℕ}
    (E : Fin n → C(Interval × Set.Icc (-1 : ℝ) 1,S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) (z : ↥leftPatch) :
    ((leftCutChart E hemb hdisjoint i b) (halfCut E i b z.val)).val 0 =
      min (z.val.1 : ℝ) (z.val.2 : ℝ) := by
  simp only [leftCutChart, OpenPartialHomeomorph.lift_openEmbedding_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  exact quadrantHalfSpace_coord0 (leftPatchHomeomorph z).val

theorem rightCutChart_coord0
    {S : Type} [TopologicalSpace S] {n : ℕ}
    (E : Fin n → C(Interval × Set.Icc (-1 : ℝ) 1,S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) (z : ↥rightPatch) :
    ((rightCutChart E hemb hdisjoint i b) (halfCut E i b z.val)).val 0 =
      min (1 - (z.val.1 : ℝ)) (z.val.2 : ℝ) := by
  simp only [rightCutChart, OpenPartialHomeomorph.lift_openEmbedding_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  exact quadrantHalfSpace_coord0 (rightPatchHomeomorph z).val

theorem cutSide_boundary_chart_zero
    {S : Type} [TopologicalSpace S] {n : ℕ}
    (E : Fin n → C(Interval × Set.Icc (-1 : ℝ) 1,S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) (t : Interval) :
    ∃ e : OpenPartialHomeomorph (CutQuotient E) (EuclideanHalfSpace 2),
      cutSide E i b t ∈ e.source ∧ (e (cutSide E i b t)).val 0 = 0 := by
  by_cases ht : (t : ℝ) < 1
  · let z : ↥leftPatch := ⟨(t,⟨0,by norm_num⟩),⟨ht,by norm_num⟩⟩
    refine ⟨leftCutChart E hemb hdisjoint i b, ?_, ?_⟩
    · rw [leftCutChart, OpenPartialHomeomorph.lift_openEmbedding_source]
      exact ⟨z, by simp, rfl⟩
    · change ((leftCutChart E hemb hdisjoint i b)
        (halfCut E i b z.val)).val 0 = 0
      rw [leftCutChart_coord0 E hemb hdisjoint i b z]
      simp [z, min_eq_right t.property.1]
  · have ht0 : 0 < (t : ℝ) := by
      have h0 := t.property.1
      have h1 := t.property.2
      push_neg at ht
      linarith
    let z : ↥rightPatch := ⟨(t,⟨0,by norm_num⟩),⟨ht0,by norm_num⟩⟩
    refine ⟨rightCutChart E hemb hdisjoint i b, ?_, ?_⟩
    · rw [rightCutChart, OpenPartialHomeomorph.lift_openEmbedding_source]
      exact ⟨z, by simp, rfl⟩
    · change ((rightCutChart E hemb hdisjoint i b)
        (halfCut E i b z.val)).val 0 = 0
      rw [rightCutChart_coord0 E hemb hdisjoint i b z]
      have ht1 : (t : ℝ) = 1 := by
        have h1 := t.property.2
        push_neg at ht
        linarith
      simp [z,ht1]

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
