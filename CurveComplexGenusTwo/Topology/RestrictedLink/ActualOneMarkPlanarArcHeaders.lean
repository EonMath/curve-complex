import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Topology.ArcStraightening
namespace CurveComplex.HyperellipticModel
open Set Schoenflies unitInterval
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actual_one_mark_planar_arc (M : HyperellipticModel E S) (f : Plane → S)
    (hf : Topology.IsOpenEmbedding f) (C P : Set Plane) (x q : Plane)
    (hC : IsJordanCurve C) (hP : IsArcBetween P x q)
    (hx : x ∈ C) (hq : q ∈ inside C) (hin : P \ {x} ⊆ inside C)
    (hxB : f x ∈ M.cover.branch) (hqB : f q ∈ M.cover.branch)
    (hmarks : ∀ z ∈ inside C, f z ∈ M.cover.branch → z = q) :
    ∃ a : EssentialMarkedArc M, a.val.image = f '' P ∧
      a.val.map 0 = f x ∧ a.val.map 1 = f q ∧
      arcInterior M a ⊆ f '' inside C := by
  classical
  obtain ⟨g,hgc,hgi,hgim,hg0,hg1⟩ := hP
  let k : Interval → S := fun t => f (g t)
  have kc : Continuous k := hf.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hgc)
  have ki : Function.Injective k := by
    intro t u he
    exact Subtype.ext (hgi t.property u.property (hf.injective he))
  have k0 : k 0 = f x := congrArg f hg0
  have k1 : k 1 = f q := congrArg f hg1
  have gin (t : Interval) (ht : t ≠ 0) : g t ∈ inside C := by
    apply hin ⟨hgim ▸ mem_image_of_mem g t.property, ?_⟩
    intro he
    have heq : g t = g 0 := (mem_singleton_iff.mp he).trans hg0.symm
    exact ht (Subtype.ext (hgi t.property (by norm_num) heq))
  let a : MarkedArc M := {
    map := k
    continuous := kc
    injective_except_loop_closure := fun t u h => Or.inl (ki h)
    start_marked := k0 ▸ hxB
    end_marked := k1 ▸ hqB
    marked_only_at_ends := by
      intro t ht
      by_cases ht0 : t = 0
      · exact Or.inl ht0
      · have he := hmarks (g t) (gin t ht0) ht
        exact Or.inr (ki ((congrArg f he).trans k1.symm)) }
  have essential : IsEssentialMarkedArc M a := Or.inl (by
    change k 0 ≠ k 1
    rw [k0,k1]
    intro he
    have hxq := hf.injective he
    exact inside_subset_compl hq (hxq ▸ hx))
  refine ⟨⟨a,essential⟩,?_,k0,k1,?_⟩
  · ext z
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨g t,hgim ▸ mem_image_of_mem g t.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨t,ht,hzt⟩ := hgim.symm ▸ hz
      exact ⟨⟨t,ht⟩,congrArg f hzt⟩
  · rintro z ⟨⟨t,rfl⟩,hn⟩
    have ht0 : t ≠ 0 := by
      intro he
      apply hn
      change k t ∈ M.cover.branch
      rw [he,k0]
      exact hxB
    exact mem_image_of_mem f (gin t ht0)
end CurveComplex.HyperellipticModel
