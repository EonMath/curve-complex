import CurveComplexGenusTwo.Topology.ArcCounts.ActualObjectFaceCountNamedHeader
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualTwoFreeGapsHeaders

namespace CurveComplex.HyperellipticModel
open Set
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance bridgeDecidableEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/--
The object-face count can be transported to the full representative graph once
all object gaps in the selected object are known to be free.  The transport is
performed through the source-faithful `actual_free_gap_is_face` theorem; no
abstract finiteness or equality of the global face family is postulated.
-/
theorem actual_object_gap_global_face_enumeration
    (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : badVertices (actualArcLabels M) σ = σ)
    {O : Finset (EssentialArcClass M)} (hO : O ∈ actualObjectFamily M σ)
    (hfree : ∀ U : Set S,
      IsComplementComponent (actualObjectTrace M r O) U →
      ∀ P ∈ actualObjectFamily M σ, P ≠ O →
        ¬ actualObjectTrace M r P ⊆ closure U) :
    ∃ G : Finset (Set S),
      G.card = (if O.card = 1 then 2 else O.card) ∧
      (∀ U : Set S,
        IsComplementComponent (actualObjectTrace M r O) U ↔ U ∈ G) ∧
      (∀ U ∈ G, IsComplementComponent (⋃ v, (r v).val.image) U) := by
  classical
  obtain ⟨G, hcard, hG⟩ := actual_object_face_count M r hr hd O hO
  refine ⟨G, hcard, hG, ?_⟩
  intro U hUG
  have hU : IsComplementComponent (actualObjectTrace M r O) U :=
    (hG U).2 hUG
  apply actual_free_gap_is_face M hbad r hr hd hO hU
  intro P hP hne
  exact hfree U hU P hP hne

/--
If a finite family `F` enumerates all complementary components of the full
representative graph, the preceding bridge embeds every free object face into
that family.  This is the exact finite-set interface needed before a global
side-incidence count can be applied.
-/
theorem actual_object_gap_global_face_subset
    (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : badVertices (actualArcLabels M) σ = σ)
    {O : Finset (EssentialArcClass M)} (hO : O ∈ actualObjectFamily M σ)
    (hfree : ∀ U : Set S,
      IsComplementComponent (actualObjectTrace M r O) U →
      ∀ P ∈ actualObjectFamily M σ, P ≠ O →
        ¬ actualObjectTrace M r P ⊆ closure U)
    (F : Finset (Set S))
    (hF : ∀ U : Set S,
      IsComplementComponent (⋃ v, (r v).val.image) U ↔ U ∈ F) :
    ∃ G : Finset (Set S),
      G.card = (if O.card = 1 then 2 else O.card) ∧
      (∀ U : Set S,
        IsComplementComponent (actualObjectTrace M r O) U ↔ U ∈ G) ∧
      G ⊆ F := by
  obtain ⟨G, hcard, hG, hglobal⟩ :=
    actual_object_gap_global_face_enumeration M r hr hd hbad hO hfree
  refine ⟨G, hcard, hG, ?_⟩
  intro U hUG
  exact (hF U).1 (hglobal U hUG)


/--
Exact global enumeration interface: a proposed coverage witness identifies every
full-graph face with a free gap of one source object.  The reverse implication
is discharged by `actual_free_gap_is_face`, so this statement exposes the
coverage premise without weakening the geometric face predicate.
-/
theorem actual_global_face_iff_free_object_gap
    (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : badVertices (actualArcLabels M) σ = σ)
    (F : Finset (Set S))
    (hF : ∀ U : Set S,
      IsComplementComponent (⋃ v, (r v).val.image) U ↔ U ∈ F)
    (hcoverage : ∀ U : Set S,
      IsComplementComponent (⋃ v, (r v).val.image) U →
      ∃ O ∈ actualObjectFamily M σ,
        IsComplementComponent (actualObjectTrace M r O) U ∧
        (∀ P ∈ actualObjectFamily M σ, P ≠ O →
          ¬ actualObjectTrace M r P ⊆ closure U)) :
    ∀ U : Set S, U ∈ F ↔
      ∃ O ∈ actualObjectFamily M σ,
        IsComplementComponent (actualObjectTrace M r O) U ∧
        (∀ P ∈ actualObjectFamily M σ, P ≠ O →
          ¬ actualObjectTrace M r P ⊆ closure U) := by
  intro U
  constructor
  · intro hUF
    obtain hUG := (hF U).2 hUF
    exact hcoverage U hUG
  · rintro ⟨O, hO, hU, hfree⟩
    apply (hF U).1
    exact actual_free_gap_is_face M hbad r hr hd hO hU hfree


/--
The existing two-free-gap theorem supplies two disjoint members of the global
face family.  This consumer is kept separate from the per-object enumeration:
it makes the remaining global incidence/coverage obligation explicit.
-/
theorem actual_two_disjoint_global_faces_bridge
    (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : badVertices (actualArcLabels M) σ = σ)
    {O : Finset (EssentialArcClass M)} (hO : O ∈ actualObjectFamily M σ) :
    ∃ P ∈ actualObjectFamily M σ, ∃ Q ∈ actualObjectFamily M σ,
      ∃ U V : Set S,
      IsComplementComponent (⋃ v, (r v).val.image) U ∧
      IsComplementComponent (⋃ v, (r v).val.image) V ∧
      Disjoint U V := by
  obtain ⟨P, hP, Q, hQ, U, V, _, _, _, _, hU, hV, hdisj⟩ :=
    actual_two_disjoint_free_faces M r hr hd hbad hO
  exact ⟨P, hP, Q, hQ, U, V, hU, hV, hdisj⟩

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_object_gap_global_face_enumeration
#print axioms CurveComplex.HyperellipticModel.actual_object_gap_global_face_subset
#print axioms CurveComplex.HyperellipticModel.actual_two_disjoint_global_faces_bridge
#print axioms CurveComplex.HyperellipticModel.actual_global_face_iff_free_object_gap
