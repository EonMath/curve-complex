import CurveComplexGenusTwo.Topology.ArcCounts.ObjectGapGlobalFaceBridge

namespace CurveComplex.HyperellipticModel
open Set
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

noncomputable local instance coverageDecidableEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/--
A concrete finite global-face constructor from the object-face API.  The
`hfreeAll` premise says every complementary component of every source object
is free from the other source objects.  The `hcoverage` premise is the forward
coverage assertion: every full-graph face occurs as such a free object gap.
Under these two geometric premises, the union of the finite per-object face
families is an exact finite enumeration of the full graph faces.
-/
theorem actual_global_face_family_of_free_object_gaps
    (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : badVertices (actualArcLabels M) σ = σ)
    (hfreeAll : ∀ (O : Finset (EssentialArcClass M)), O ∈ actualObjectFamily M σ →
      ∀ U : Set S, IsComplementComponent (actualObjectTrace M r O) U →
      ∀ P ∈ actualObjectFamily M σ, P ≠ O →
        ¬ actualObjectTrace M r P ⊆ closure U)
    (hcoverage : ∀ U : Set S,
      IsComplementComponent (⋃ v, (r v).val.image) U →
      ∃ O ∈ actualObjectFamily M σ,
        IsComplementComponent (actualObjectTrace M r O) U) :
    ∃ F : Finset (Set S),
      ∀ U : Set S,
        IsComplementComponent (⋃ v, (r v).val.image) U ↔ U ∈ F := by
  classical
  letI : DecidableEq (EssentialArcClass M) := Classical.decEq _
  let G : Finset (EssentialArcClass M) → Finset (Set S) := fun O =>
    if hO : O ∈ actualObjectFamily M σ then
      Classical.choose (actual_object_face_count M r hr hd O hO)
    else ∅
  have hG : ∀ (O : Finset (EssentialArcClass M)), O ∈ actualObjectFamily M σ →
      ∀ U : Set S,
        IsComplementComponent (actualObjectTrace M r O) U ↔ U ∈ G O := by
    intro O hO U
    simp only [G, dif_pos hO]
    exact (Classical.choose_spec (actual_object_face_count M r hr hd O hO)).2 U
  let F : Finset (Set S) := (actualObjectFamily M σ).biUnion G
  refine ⟨F, ?_⟩
  intro U
  constructor
  · intro hU
    obtain ⟨O, hO, hOU⟩ := hcoverage U hU
    apply Finset.mem_biUnion.mpr
    exact ⟨O, hO, (hG O hO U).1 hOU⟩
  · intro hUF
    obtain ⟨O, hO, hUG⟩ := Finset.mem_biUnion.mp hUF
    have hOU : IsComplementComponent (actualObjectTrace M r O) U :=
      (hG O hO U).2 hUG
    exact actual_free_gap_is_face M hbad r hr hd hO hOU (hfreeAll O hO U hOU)

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_global_face_family_of_free_object_gaps

namespace CurveComplex.HyperellipticModel
open Set
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/--
Single-family Card12 consumer.  The weighted side-walk certificate is only
required for the one finite face family `F` supplied with the Euler lower
bound; no producer for unrelated finite subfamilies is needed.
-/
theorem card12_of_one_weighted_face_family
    (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M))
    (hσ : σ.Nonempty)
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (F : Finset (Set S))
    (hF : ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).val.image) U)
    (hEuler : Fintype.card {v // v ∈ σ} +
        (Finset.univ.image (fun i : {v // v ∈ σ} =>
          connectedComponentIn (⋃ j, (r j).val.image) ((r i).val.map 0))).card + 1 ≤
        F.card + (markedFamilyVertices (fun i => (r i).val)).card)
    (hweighted : (∀ U ∈ F, IsComplementComponent (⋃ i, (r i).val.image) U) →
      3 * F.card ≤ 2 * σ.card +
        3 * (6 - (markedFamilyVertices (fun i => (r i).val)).card) +
        3 * ((Finset.univ.image (fun i : {v // v ∈ σ} =>
          connectedComponentIn (⋃ j, (r j).val.image) ((r i).val.map 0))).card - 1)) :
    σ.card ≤ 12 := by
  classical
  letI : Nonempty {v // v ∈ σ} := hσ.to_subtype
  have hV := markedFamilyVertices_card_le_six (fun i => (r i).val)
  have hC : 1 ≤ (Finset.univ.image (fun i : {v // v ∈ σ} =>
      connectedComponentIn (⋃ j, (r j).val.image) ((r i).val.map 0))).card := by
    apply Finset.card_pos.mpr
    obtain ⟨i⟩ := ‹Nonempty {v // v ∈ σ}›
    exact ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hW := hweighted hF
  rw [Fintype.card_coe] at hEuler
  omega

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.card12_of_one_weighted_face_family

namespace CurveComplex.HyperellipticModel
open Set
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/--
Finite exact enumeration using only free-gap coverage.  Unlike
`actual_global_face_family_of_free_object_gaps`, this does not assume that
all object gaps are free: each finite object face family is filtered by the
explicit free-gap predicate before taking the finite union.  Consequently the
only geometric coverage premise is that every full-graph face has at least one
free object-gap witness.
-/
noncomputable local instance coverageDecidableEq2 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

theorem actual_global_face_family_of_covered_free_gaps
    (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : badVertices (actualArcLabels M) σ = σ)
    (hcoverage : ∀ U : Set S,
      IsComplementComponent (⋃ v, (r v).val.image) U →
      ∃ O ∈ actualObjectFamily M σ,
        IsComplementComponent (actualObjectTrace M r O) U ∧
        (∀ P ∈ actualObjectFamily M σ, P ≠ O →
          ¬ actualObjectTrace M r P ⊆ closure U)) :
    ∃ F : Finset (Set S),
      ∀ U : Set S,
        IsComplementComponent (⋃ v, (r v).val.image) U ↔ U ∈ F := by
  classical
  letI : DecidableEq (EssentialArcClass M) := Classical.decEq _
  let G : Finset (EssentialArcClass M) → Finset (Set S) := fun O =>
    if hO : O ∈ actualObjectFamily M σ then
      Classical.choose (actual_object_face_count M r hr hd O hO)
    else ∅
  have hG : ∀ (O : Finset (EssentialArcClass M)), O ∈ actualObjectFamily M σ →
      ∀ U : Set S,
        IsComplementComponent (actualObjectTrace M r O) U ↔ U ∈ G O := by
    intro O hO U
    simp only [G, dif_pos hO]
    exact (Classical.choose_spec (actual_object_face_count M r hr hd O hO)).2 U
  let Free : Finset (EssentialArcClass M) → Finset (Set S) := fun O =>
    (G O).filter (fun U => ∀ P ∈ actualObjectFamily M σ, P ≠ O →
      ¬ actualObjectTrace M r P ⊆ closure U)
  let F : Finset (Set S) := (actualObjectFamily M σ).biUnion Free
  refine ⟨F, ?_⟩
  intro U
  constructor
  · intro hU
    obtain ⟨O, hO, hOU, hfree⟩ := hcoverage U hU
    apply Finset.mem_biUnion.mpr
    refine ⟨O, hO, Finset.mem_filter.mpr ⟨(hG O hO U).1 hOU, hfree⟩⟩
  · intro hUF
    obtain ⟨O, hO, hUfree⟩ := Finset.mem_biUnion.mp hUF
    have hUG : U ∈ G O := (Finset.mem_filter.mp hUfree).1
    have hfree : ∀ P ∈ actualObjectFamily M σ, P ≠ O →
        ¬ actualObjectTrace M r P ⊆ closure U :=
      (Finset.mem_filter.mp hUfree).2
    have hOU : IsComplementComponent (actualObjectTrace M r O) U :=
      (hG O hO U).2 hUG
    exact actual_free_gap_is_face M hbad r hr hd hO hOU hfree

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_global_face_family_of_covered_free_gaps
