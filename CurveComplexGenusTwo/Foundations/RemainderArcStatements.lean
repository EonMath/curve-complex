import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.TwoArcs
import Schoenflies.FaceCyclesLand
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter

namespace CurveComplex

/-- A closed nondegenerate two-piece splitting of the parameter circle at two
points consists of two embedded arcs. This will be applied to a crossing-disk
piece and its outside remainder, not to an assumed outside-arc witness. -/
theorem circle_closed_split_has_embedded_paths
    (A B : Set Circle) (u v : Circle) (huv : u ≠ v)
    (hA : IsCompact A) (hB : IsCompact B)
    (hcover : A ∪ B = Set.univ) (hmeet : A ∩ B = {u,v})
    (hAn : (A \ {u,v}).Nonempty) (hBn : (B \ {u,v}).Nonempty) :
    ∃ (p q : Path u v),
      Topology.IsEmbedding p ∧ Topology.IsEmbedding q ∧
      Set.range p = A ∧ Set.range q = B := by
  classical
  let j : Circle → Schoenflies.Plane := fun z =>
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).symm ![(z : ℂ).re,(z : ℂ).im]
  have hjc : Continuous j := by fun_prop
  have hji : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Complex.ext
    · simpa [j] using congrArg (fun z : Schoenflies.Plane => z 0) h
    · simpa [j] using congrArg (fun z : Schoenflies.Plane => z 1) h
  have hje : Topology.IsEmbedding j := (hjc.isClosedEmbedding hji).isEmbedding
  have hJ := isJordanCurve_range_of_isEmbedding_circle ⟨j,hjc⟩ hje
  obtain ⟨A',B',hA',hB',hcov',hmeet'⟩ := hJ.two_arcs
    (Set.mem_range_self u) (Set.mem_range_self v) (fun h => huv (hji h))
  have hcov : j '' A ∪ j '' B = Set.range j := by
    rw [← Set.image_union, hcover, Set.image_univ]
  have hmeetj : j '' A ∩ j '' B = {j u,j v} := by
    rw [← Set.image_inter hji, hmeet]
    simp
  have hnon (D : Set Circle) (hn : (D \ {u,v}).Nonempty) :
      ¬ j '' D ⊆ ({j u,j v} : Set Schoenflies.Plane) := by
    intro hsub
    obtain ⟨z,hz,hzne⟩ := hn
    have hh := hsub (Set.mem_image_of_mem j hz)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    exact hzne (hh.elim (fun h => Or.inl (hji h)) (fun h => Or.inr (hji h)))
  have hsplit := Schoenflies.two_arcs_unique_of_isClosed hcov' hmeet' hcov hmeetj
    hA' hB' (hA.image hjc).isClosed (hB.image hjc).isClosed
    (hnon A hAn) (hnon B hBn)
  have hAJ : Schoenflies.IsArcBetween (j '' A) (j u) (j v) := by
    rcases hsplit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
  have hBJ : Schoenflies.IsArcBetween (j '' B) (j u) (j v) := by
    rcases hsplit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
  have liftArc (D : Set Circle) (hD : Schoenflies.IsArcBetween (j '' D) (j u) (j v)) :
      ∃ p : Path u v, Topology.IsEmbedding p ∧ Set.range p = D := by
    obtain ⟨f,hfc,hfi,hfr,hf0,hf1⟩ := hD
    have hr (t : unitInterval) : f t ∈ Set.range j := by
      have ht : f t ∈ j '' D := hfr ▸ Set.mem_image_of_mem f t.property
      exact Set.image_subset_range _ _ ht
    let lift : unitInterval → Circle := fun t => hje.toHomeomorph.symm ⟨f t,hr t⟩
    have hlc : Continuous lift := hje.toHomeomorph.symm.continuous.comp
      ((hfc.comp_continuous continuous_subtype_val (fun t => t.property)).subtype_mk hr)
    have hjl (t : unitInterval) : j (lift t) = f t :=
      congrArg Subtype.val (hje.toHomeomorph.apply_symm_apply _)
    have hl0 : lift 0 = u := hji ((hjl 0).trans hf0)
    have hl1 : lift 1 = v := hji ((hjl 1).trans hf1)
    let p : Path u v := ⟨⟨lift,hlc⟩,hl0,hl1⟩
    have hli : Function.Injective lift := by
      intro x y hxy
      apply Subtype.ext
      apply hfi x.property y.property
      rw [← hjl x, ← hjl y, hxy]
    refine ⟨p,(hlc.isClosedEmbedding hli).isEmbedding, ?_⟩
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      have hh : f t ∈ j '' D := hfr ▸ Set.mem_image_of_mem f t.property
      obtain ⟨w,hw,heq⟩ := hh
      have heq' : w = lift t := hji (heq.trans (hjl t).symm)
      change lift t ∈ D
      exact heq' ▸ hw
    · intro hz
      have hh : j z ∈ f '' unitInterval := hfr.symm ▸ Set.mem_image_of_mem j hz
      obtain ⟨t,ht,heq⟩ := hh
      exact ⟨⟨t,ht⟩,hji ((hjl ⟨t,ht⟩).trans heq)⟩
  obtain ⟨p,hp,hpA⟩ := liftArc A hAJ
  obtain ⟨q,hq,hqB⟩ := liftArc B hBJ
  exact ⟨p,q,hp,hq,hpA,hqB⟩

/-- The surface-level version uses the actual source curve embedding. Its
hypotheses are a compact decomposition of its image, with exact two-point
intersection and a nonendpoint point on each piece. -/
theorem curve_closed_split_has_embedded_paths
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (c : Curve S) (A B : Set S) (u v : S) (huv : u ≠ v)
    (hA : IsCompact A) (hB : IsCompact B)
    (hcover : A ∪ B = c.image) (hmeet : A ∩ B = {u,v})
    (hAn : (A \ {u,v}).Nonempty) (hBn : (B \ {u,v}).Nonempty) :
    ∃ (p q : Path u v),
      Topology.IsEmbedding p ∧ Topology.IsEmbedding q ∧
      Set.range p = A ∧ Set.range q = B := by
  classical
  have hAsub : A ⊆ c.image := by rw [← hcover]; exact Set.subset_union_left
  have hBsub : B ⊆ c.image := by rw [← hcover]; exact Set.subset_union_right
  have huAB : u ∈ A ∩ B := by rw [hmeet]; simp
  have hvAB : v ∈ A ∩ B := by rw [hmeet]; simp
  obtain ⟨u',hu'⟩ := hAsub huAB.1
  obtain ⟨v',hv'⟩ := hAsub hvAB.1
  have huv' : u' ≠ v' := by intro h; apply huv; rw [← hu',← hv',h]
  let A' : Set Circle := c.map ⁻¹' A
  let B' : Set Circle := c.map ⁻¹' B
  have hA' : IsCompact A' := (hA.isClosed.preimage c.embedded.continuous).isCompact
  have hB' : IsCompact B' := (hB.isClosed.preimage c.embedded.continuous).isCompact
  have hcov' : A' ∪ B' = Set.univ := by
    change c.map ⁻¹' A ∪ c.map ⁻¹' B = _
    rw [← Set.preimage_union,hcover]
    ext t; simp [Curve.image]
  have hmeet' : A' ∩ B' = {u',v'} := by
    change c.map ⁻¹' A ∩ c.map ⁻¹' B = _
    rw [← Set.preimage_inter,hmeet,← hu',← hv']
    ext t
    simp only [Set.mem_preimage,Set.mem_insert_iff,Set.mem_singleton_iff,
      c.embedded.injective.eq_iff]
  have hnon (D : Set S) (hD : D ⊆ c.image) (hn : (D \ {u,v}).Nonempty) :
      ((c.map ⁻¹' D) \ {u',v'}).Nonempty := by
    obtain ⟨z,hz,hzne⟩ := hn
    obtain ⟨t,ht⟩ := hD hz
    refine ⟨t,(show c.map t ∈ D from ht.symm ▸ hz), ?_⟩
    intro h
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    apply hzne
    rcases h with rfl | rfl
    · exact Or.inl (ht.symm.trans hu')
    · exact Or.inr (ht.symm.trans hv')
  obtain ⟨p,q,hp,hq,hpA,hqB⟩ := circle_closed_split_has_embedded_paths A' B' u' v'
    huv' hA' hB' hcov' hmeet' (hnon A hAsub hAn) (hnon B hBsub hBn)
  let P : Path u v := (p.map c.embedded.continuous).cast hu'.symm hv'.symm
  let Q : Path u v := (q.map c.embedded.continuous).cast hu'.symm hv'.symm
  refine ⟨P,Q,c.embedded.comp hp,c.embedded.comp hq,?_,?_⟩
  · change Set.range (c.map ∘ p) = A
    rw [Set.range_comp,hpA]
    exact Set.image_preimage_eq_of_subset hAsub
  · change Set.range (c.map ∘ q) = B
    rw [Set.range_comp,hqB]
    exact Set.image_preimage_eq_of_subset hBsub
end CurveComplex

#print axioms CurveComplex.circle_closed_split_has_embedded_paths
#print axioms CurveComplex.curve_closed_split_has_embedded_paths
