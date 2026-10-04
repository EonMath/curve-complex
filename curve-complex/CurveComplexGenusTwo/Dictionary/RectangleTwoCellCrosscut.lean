import CurveComplexGenusTwo.Dictionary.RectangleNamed
import CurveComplexGenusTwo.Dictionary.RectangleNamedHorizontal
open Set Topology
namespace CurveComplex
/-- Named two-cell crosscut decomposition for either an axis-aligned vertical or
horizontal split of a rectangle.  The two returned cell boundaries are the
boundaries indexed by `r 0` and `r 1`; all three loops have endpoint-only
self-collision. -/
theorem rectangle_two_cell_crosscut
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (lo hi : Fin 2 → ℝ × ℝ)
    (hshape :
      (∃ k : ℝ, lo = ![(a,c),(k,c)] ∧ hi = ![(k,d),(b,d)] ∧ a < k ∧ k < b) ∨
      (∃ k : ℝ, lo = ![(a,c),(a,k)] ∧ hi = ![(b,k),(b,d)] ∧ c < k ∧ k < d)) :
    ∃ r : Fin 2 → Fin 2, ∃ x y : ℝ × ℝ,
    ∃ P : Path x y, ∃ Q : Path y x, ∃ χ : Path x y,
      Set.range (P.trans χ.symm) =
          frontier (Icc (lo (r 0)).1 (hi (r 0)).1 ×ˢ
            Icc (lo (r 0)).2 (hi (r 0)).2) ∧
      Set.range (χ.trans Q) =
          frontier (Icc (lo (r 1)).1 (hi (r 1)).1 ×ˢ
            Icc (lo (r 1)).2 (hi (r 1)).2) ∧
      Set.range (P.trans Q) = frontier (Icc a b ×ˢ Icc c d) ∧
      (∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
      (∀ s t, (χ.trans Q) s = (χ.trans Q) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
      (∀ s t, (P.trans Q) s = (P.trans Q) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) := by
  rcases hshape with ⟨k, hlo, hhi, hak, hkb⟩ | ⟨k, hlo, hhi, hck, hkd⟩
  · obtain ⟨P, Q, χ, h0, h1, ho, hc0, hc1, hco⟩ :=
      rectangle_cut_package_vertical a k b c d hak hkb hcd
    refine ⟨id, (k,c), (k,d), P, Q, χ, ?_⟩
    simpa [hlo, hhi] using And.intro h0 (And.intro h1 (And.intro ho (And.intro hc0 (And.intro hc1 hco))))
  · obtain ⟨P, Q, χ, h0, h1, ho, hc0, hc1, hco⟩ :=
      rectangle_cut_package_horizontal a b c k d hab hck hkd
    refine ⟨id, (a,k), (b,k), P, Q, χ, ?_⟩
    simpa [hlo, hhi] using And.intro h0 (And.intro h1 (And.intro ho (And.intro hc0 (And.intro hc1 hco))))
end CurveComplex
