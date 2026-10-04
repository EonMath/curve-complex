import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Topology.Extraction
namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actual_two_interior_marks_arc (M : HyperellipticModel E S) (U : Set S) (e : Plane ≃ₜ U)
    (p q : S) (hp : p ∈ U) (hq : q ∈ U) (hpB : p ∈ M.cover.branch)
    (hqB : q ∈ M.cover.branch) (hpq : p ≠ q)
    (hmarks : ∀ x ∈ U, x ∈ M.cover.branch → x = p ∨ x = q) :
    ∃ a : EssentialMarkedArc M,
      a.val.map 0 = p ∧ a.val.map 1 = q ∧ a.val.image ⊆ U := by
  let x : Plane := e.symm ⟨p, hp⟩
  let y : Plane := e.symm ⟨q, hq⟩
  have hxy : x ≠ y := by
    intro h
    have he := congrArg (fun z => (e z).val) h
    simp only [x, y, e.apply_symm_apply] at he
    exact hpq he
  obtain ⟨A, _, _, f, hf, hi, hA, hf0, hf1⟩ :=
    exists_simple_arc_of_isPreconnected isOpen_univ isPreconnected_univ
      (mem_univ x) (mem_univ y) hxy
  let g : Interval → S := fun t => (e (f t.val)).val
  have hg0 : g 0 = p := by simp [g, hf0, x]
  have hg1 : g 1 = q := by simp [g, hf1, y]
  have hgi : Function.Injective g := by
    intro t u h
    apply Subtype.ext
    apply hi t.property u.property
    exact e.injective (Subtype.ext h)
  let a : MarkedArc M := {
    map := g
    continuous := continuous_subtype_val.comp (e.continuous.comp
      (continuousOn_iff_continuous_restrict.mp hf))
    injective_except_loop_closure := fun t u h => Or.inl (hgi h)
    start_marked := hg0 ▸ hpB
    end_marked := hg1 ▸ hqB
    marked_only_at_ends := by
      intro t ht
      have htg : g t ∈ U := (e (f t.val)).property
      rcases hmarks (g t) htg ht with ht | ht
      · exact Or.inl (hgi (ht.trans hg0.symm))
      · exact Or.inr (hgi (ht.trans hg1.symm)) }
  have hae : IsEssentialMarkedArc M a := Or.inl (by
    change g 0 ≠ g 1
    rwa [hg0, hg1])
  refine ⟨⟨a, hae⟩, hg0, hg1, ?_⟩
  rintro z ⟨t, rfl⟩
  exact (e (f t.val)).property
end CurveComplex.HyperellipticModel
