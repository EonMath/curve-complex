import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
import CurveComplexGenusTwo.Topology.RestrictedLink.RestrictedLinkHeaders
namespace CurveComplex.HyperellipticModel
open Set CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualGapArcLinkHeaders_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
theorem actual_gap_arc_link_vertex (M : HyperellipticModel E S) (σ : Finset (EssentialArcClass M))
    (r : {w // w ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
    (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (hbad : badVertices (actualArcLabels M) σ = σ)
    (U : Set S) (hU : U ⊆ (⋃ w, (r w).val.image)ᶜ)
    (a : EssentialMarkedArc M) (hne : a.val.map 0 ≠ a.val.map 1)
    (ha : arcInterior M a ⊆ U) (hend : a.val.map 0 ∈ U ∨ a.val.map 1 ∈ U) :
    ({Quotient.mk (essentialArcSetoid M) a} : Finset (EssentialArcClass M)) ∈
      restrictedLinkSet (actualA M) (actualArcLabels M) σ := by
  classical
  have insertSimplex (M : HyperellipticModel E S) (σ : Finset (EssentialArcClass M))
      (r : {v // v ∈ σ} → EssentialMarkedArc M)
      (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
      (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
      (a : EssentialMarkedArc M)
      (ha : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v))) :
      IsArcSimplex M (insert (Quotient.mk (essentialArcSetoid M) a) σ) := by
    classical
    let v0 := Quotient.mk (essentialArcSetoid M) a
    let rep : {v // v ∈ insert v0 σ} → EssentialMarkedArc M := fun v =>
      if h : v.val = v0 then a else r ⟨v.val, (Finset.mem_insert.mp v.property).resolve_left h⟩
    refine ⟨rep, ?_, ?_⟩
    · intro v
      dsimp [rep]
      split_ifs with h
      · exact h.symm
      · exact hr _
    · intro v w hvw
      have hne : v.val ≠ w.val := fun h => hvw (Subtype.ext h)
      dsimp [rep]
      split_ifs with hv hw
      · exact False.elim (hne (hv.trans hw.symm))
      · exact ha _
      · exact (ha _).symm
      · exact hd _ _ (fun h => hne (congrArg (fun x : {v // v ∈ σ} => x.val) h))
  let v := Quotient.mk (essentialArcSetoid M) a
  obtain ⟨q,hqU,hqEnd⟩ : ∃ q ∈ U, q ∈ classEndpoints M v := by
    rcases hend with h0 | h1
    · refine ⟨a.val.map 0,h0,?_⟩
      change a.val.map 0 ∈ classEndpoints M (Quotient.mk (essentialArcSetoid M) a)
      rw [← markedArcEndset_eq_classEndpoints]
      simp [markedArcEndset]
    · refine ⟨a.val.map 1,h1,?_⟩
      change a.val.map 1 ∈ classEndpoints M (Quotient.mk (essentialArcSetoid M) a)
      rw [← markedArcEndset_eq_classEndpoints]
      simp [markedArcEndset]
  have endpointOnGraph (w : EssentialArcClass M) (hw : w ∈ σ)
      (q : S) (hq : q ∈ classEndpoints M w) : q ∈ ⋃ w, (r w).val.image := by
    let wσ : {w // w ∈ σ} := ⟨w,hw⟩
    have hlabel : markedArcEndset (r wσ).val = classEndpoints M w :=
      (markedArcEndset_eq_classEndpoints M (r wσ)).trans (congrArg (classEndpoints M) (hr wσ))
    rw [← hlabel] at hq
    simp only [markedArcEndset,Finset.mem_insert,Finset.mem_singleton] at hq
    apply mem_iUnion.mpr
    refine ⟨wσ,?_⟩
    rcases hq with rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  have hvnot : v ∉ σ := fun hv => hU hqU (endpointOnGraph v hv q hqEnd)
  have hnonloop : ¬ (actualArcLabels M).isLoop v := by
    change (classEndpoints M v).card ≠ 1
    rw [← markedArcEndset_eq_classEndpoints]
    simp [markedArcEndset,hne]
  have hfresh : ∀ w ∈ σ, w ≠ v → ¬ (actualArcLabels M).isLoop w →
      (actualArcLabels M).endpointPair w ≠ (actualArcLabels M).endpointPair v := by
    intro w hw _ _ he
    have he : classEndpoints M w = classEndpoints M v := he
    exact hU hqU (endpointOnGraph w hw q (he.symm ▸ hqEnd))
  have hdis (w : {w // w ∈ σ}) : Disjoint (arcInterior M a) (arcInterior M (r w)) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxR
    exact hU (ha hxA) (mem_iUnion.mpr ⟨w,hxR.1⟩)
  have hsimplex := insertSimplex M σ r hr hd a hdis
  have hb := badVertices_insert_fresh_endpoint (actualArcLabels M) σ v hnonloop hfresh
  change Disjoint σ {v} ∧ σ ∪ {v} ∈ actualA M ∧ badVertices (actualArcLabels M) (σ ∪ {v}) = σ
  refine ⟨?_,?_,?_⟩
  · exact Finset.disjoint_singleton_right.mpr hvnot
  · change IsArcSimplex M (σ ∪ {v})
    simpa only [Finset.union_singleton] using hsimplex
  · simpa only [Finset.union_singleton,hbad] using hb
end CurveComplex.HyperellipticModel
