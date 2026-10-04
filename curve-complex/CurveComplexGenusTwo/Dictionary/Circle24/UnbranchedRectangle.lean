import CurveComplexGenusTwo.Dictionary.BranchedCover
import Mathlib.Topology.Homotopy.Lifting
open Set Topology
namespace CurveComplex.BranchedDoubleCover
variable {E S K : Type} [TopologicalSpace E] [TopologicalSpace S] [TopologicalSpace K]

/-- The full preimage of an embedded compact simply connected branch-free
region is constructed as two disjoint embedded copies of that region. -/
theorem compact_simplyConnected_two_sheet_lifts
    [T2Space E] [CompactSpace K] [SimplyConnectedSpace K] [LocallyPathConnectedSpace K]
    (q : BranchedDoubleCover E S) (f : C(K,S)) (hf : IsEmbedding f)
    (havoid : ∀ x, f x ∉ q.branch) (k₀ : K) :
    ∃ F G : C(K,E), IsEmbedding F ∧ IsEmbedding G ∧
      (∀ x, q.projection (F x) = f x) ∧
      (∀ x, q.projection (G x) = f x) ∧
      (∀ x, G x = q.deck (F x)) ∧
      Disjoint (Set.range F) (Set.range G) ∧
      Set.range F ∪ Set.range G = q.projection ⁻¹' Set.range f := by
  obtain ⟨e,he⟩ := q.projection_surjective (f k₀)
  obtain ⟨F,hF,_⟩ := q.unbranched_cover.existsUnique_continuousMap_lifts f he havoid
  have hπ (x : K) : q.projection (F x) = f x := congrFun hF.2 x
  have hinj : Function.Injective F := by
    intro x y heq
    apply hf.injective
    rw [← hπ x,← hπ y,heq]
  let G : C(K,E) := ⟨fun x => q.deck (F x),q.deck.continuous.comp F.continuous⟩
  have hGπ (x : K) : q.projection (G x) = f x := (q.projection_deck (F x)).trans (hπ x)
  have hGinj : Function.Injective G := q.deck.injective.comp hinj
  have hdisj : Disjoint (Set.range F) (Set.range G) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,rfl⟩ ⟨y,hy⟩
    have hxy : y=x := hf.injective ((hGπ y).symm.trans ((congrArg q.projection hy).trans (hπ x)))
    subst y
    have hbranch := (q.fixed_iff_branch (F x)).mp hy
    rw [hπ] at hbranch
    exact havoid x hbranch
  refine ⟨F,G,(F.continuous.isClosedEmbedding hinj).isEmbedding,
    (G.continuous.isClosedEmbedding hGinj).isEmbedding,hπ,hGπ,fun _ => rfl,hdisj,?_⟩
  ext z
  constructor
  · rintro (⟨x,rfl⟩ | ⟨x,rfl⟩)
    · exact ⟨x,(hπ x).symm⟩
    · exact ⟨x,(hGπ x).symm⟩
  · rintro ⟨x,hx⟩
    rcases (q.fiber_pair (F x) z).mp ((hπ x).trans hx) with hz | hz
    · exact Or.inl ⟨x,hz.symm⟩
    · exact Or.inr ⟨x,hz.symm⟩

/-- A source corridor rectangle has two actual embedded rectangle lifts,
constructed through the covering restriction rather than assumed. -/
theorem closed_rectangle_two_sheet_lifts [T2Space E]
    (q : BranchedDoubleCover E S) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (f : C(Icc a b ×ˢ Icc c d,S)) (hf : IsEmbedding f)
    (havoid : ∀ x, f x ∉ q.branch) :
    ∃ F G : C(Icc a b ×ˢ Icc c d,E), IsEmbedding F ∧ IsEmbedding G ∧
      (∀ x, q.projection (F x) = f x) ∧
      (∀ x, q.projection (G x) = f x) ∧
      (∀ x, G x = q.deck (F x)) ∧
      Disjoint (Set.range F) (Set.range G) ∧
      Set.range F ∪ Set.range G = q.projection ⁻¹' Set.range f := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc c d
  let k₀ : K := ⟨(a,c),⟨⟨le_refl a,hab.le⟩,⟨le_refl c,hcd.le⟩⟩⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  let : ContractibleSpace K := ((convex_Icc a b).prod (convex_Icc c d)).contractibleSpace ⟨k₀.val,k₀.property⟩
  let : LocallyPathConnectedSpace K := ((convex_Icc a b).prod (convex_Icc c d)).locallyPathConnectedSpace
  exact q.compact_simplyConnected_two_sheet_lifts f hf havoid k₀

end CurveComplex.BranchedDoubleCover
#print axioms CurveComplex.BranchedDoubleCover.closed_rectangle_two_sheet_lifts
