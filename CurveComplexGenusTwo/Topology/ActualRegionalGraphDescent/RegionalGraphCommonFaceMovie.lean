import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalGraphQuotientCommonFace
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalFiniteLabelMovie

open CurveComplex Set
noncomputable local instance actualGraphDescentRegionalGraphCommonFaceMoviePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- The geometric indexed graph common-face API induces actual continuous
    maps and a coherent replacement movie on a finite domain realization. -/
theorem regional_graph_quotient_replacement_realization_movie
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (Arc : Type*) (rel : Arc → Arc → Prop)
    (underlying : Arc → C(Interval,↥F))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : AbstractSimplicialComplex ι) (L : AbstractSimplicialComplex (Quot rel))
    (haccept : ∀ τ : Finset (Quot rel),
      τ.Nonempty → (∃ rep : ↥τ → Arc,
        (∀ z, Quot.mk rel (rep z) = z.val) ∧
        ∀ z w, z ≠ w → Disjoint (Set.range (underlying (rep z)))
          (Set.range (underlying (rep w)))) → τ ∈ L.faces)
    (a : ι → Arc) (adjacent : ι → ι → Prop)
    (hclique : ∀ σ : Finset ι, σ ∈ K.faces →
      ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → adjacent i j)
    (hdis : ∀ i j, adjacent i j →
      Disjoint (Set.range (underlying (a i))) (Set.range (underlying (a j))))
    (k : ι) (branch copy : Arc)
    (hcopyLabel : Quot.mk rel copy = Quot.mk rel (a k))
    (hcopyOther : ∀ i, adjacent k i →
      Disjoint (Set.range (underlying copy)) (Set.range (underlying (a i))))
    (hbranchCopy : Disjoint (Set.range (underlying branch))
      (Set.range (underlying copy)))
    (hbranchOther : ∀ i, adjacent k i →
      Disjoint (Set.range (underlying branch)) (Set.range (underlying (a i)))) :
    let f : ι → Quot rel := fun i => Quot.mk rel (a i)
    let g := Function.update f k (Quot.mk rel branch)
    ∃ H : C(ConeTime × RealizationPoint K,RealizationPoint L),
      ∀ t x v, (H (t,x)).weight v =
        (1-(t : ℝ)) * (∑ i : ι, if f i = v then x.weight i else 0) +
        (t : ℝ) * (∑ i : ι, if g i = v then x.weight i else 0) := by
  classical
  dsimp only
  let f : ι → Quot rel := fun i => Quot.mk rel (a i)
  have hface : ∀ σ : Finset ι, σ ∈ K.faces → σ.image f ∈ L.faces := by
    intro σ hσ
    have hne : σ.Nonempty := (K.isRelLowerSet_faces hσ).1
    obtain ⟨hn,rep,hl,hd⟩ := regional_indexed_quotient_clique_face Arc rel underlying
      a σ hne (fun i hi j hj hij => hdis i j (hclique σ hσ i hi j hj hij))
    exact haccept _ hn ⟨rep,hl,hd⟩
  have hcommon : ∀ σ : Finset ι, σ ∈ K.faces → k ∈ σ →
      insert (Quot.mk rel branch) (σ.image f) ∈ L.faces := by
    intro σ hσ hk
    obtain ⟨hn,rep,hl,hd⟩ := regional_indexed_graph_quotient_common_face Arc rel
      underlying a adjacent hdis k branch copy hcopyLabel hcopyOther hbranchCopy
      hbranchOther σ hk (hclique σ hσ)
    exact haccept _ hn ⟨rep,hl,hd⟩
  exact regional_finite_label_contiguity_movie K L f
    (Function.update f k (Quot.mk rel branch))
    (regional_indexed_label_replacement_contiguous K L f k (Quot.mk rel branch)
      hface hcommon)

#print axioms regional_graph_quotient_replacement_realization_movie
