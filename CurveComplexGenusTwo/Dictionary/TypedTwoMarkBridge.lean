import CurveComplexGenusTwo.Dictionary.TypedTwoCellClean
import CurveComplexGenusTwo.Dictionary.DictionaryTwoMarkChart
open Set Topology Metric
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 12000000
set_option linter.style.haveILetI false

/--
The typed 2|4 bridge: a rectangle crosscut whose two cell frontiers admit the
one-mark disc charts is forbidden when its outer frontier is a punctured circle.
The theorem packages all subtype/range/index transports needed by the branch-free
2-mark obstruction.  The geometric chart and outer-frontier equalities remain
explicit inputs.
-/
theorem rectangle_two_marked_side_obstruction_typed
    (M : HyperellipticModel E S)
    (a : PuncturedCircle M)
    (a₀ b₀ c₀ d₀ : ℝ) (ha₀b₀ : a₀ < b₀) (hc₀d₀ : c₀ < d₀)
    (lo hi : Fin 2 → ℝ × ℝ)
    (hshape :
      (∃ k : ℝ, lo = ![(a₀,c₀),(k,c₀)] ∧ hi = ![(k,d₀),(b₀,d₀)] ∧ a₀ < k ∧ k < b₀) ∨
      (∃ k : ℝ, lo = ![(a₀,c₀),(a₀,k)] ∧ hi = ![(b₀,k),(b₀,d₀)] ∧ c₀ < k ∧ k < d₀))
    (f : C(Icc a₀ b₀ ×ˢ Icc c₀ d₀, S)) (hf : IsEmbedding f)
    (F : Fin 2 → C(Metric.closedBall (0 : Schoenflies.Plane) 1, S))
    (hF : ∀ i, IsEmbedding (F i))
    (m : Fin 2 → Metric.closedBall (0 : Schoenflies.Plane) 1)
    (hm : ∀ i, ‖(m i).val‖ < 1)
    (honly : ∀ i z, F i z ∈ M.cover.branch ↔ z = m i)
    (hcell : ∀ i,
      f '' {z : Icc a₀ b₀ ×ˢ Icc c₀ d₀ |
        z.val ∈ frontier (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)} =
        F i '' {z | ‖z.val‖ = 1})
    (houter :
      f '' {z : Icc a₀ b₀ ×ˢ Icc c₀ d₀ |
        z.val ∈ frontier (Icc a₀ b₀ ×ˢ Icc c₀ d₀)} = a.image)
    (c : Curve E) (hc : c.image = M.cover.projection ⁻¹' a.image) : False := by
  obtain ⟨r, x, y, P, Q, χ, h0, h1, ho, hc0, hc1, hco⟩ :=
    rectangle_two_cell_crosscut_typed_clean a₀ b₀ c₀ d₀ ha₀b₀ hc₀d₀ lo hi hshape
  let K : Set (ℝ × ℝ) := Icc a₀ b₀ ×ˢ Icc c₀ d₀
  have hmapRange {u v : K} (δ : Path u v) (A : Set (ℝ × ℝ))
      (hδ : Set.range (fun t => (δ t).val) = A) :
      Set.range (fun t => f (δ t)) =
        f '' {z : K | z.val ∈ A} := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨δ t, Set.mem_ofPred_eq.mpr (hδ ▸ Set.mem_range_self t), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : w.val ∈ Set.range (fun t => (δ t).val) := by
        rw [hδ]
        exact hw
      rcases hw' with ⟨t, ht⟩
      have he : δ t = w := Subtype.ext ht
      exact ⟨t, by change f (δ t) = f w; rw [he]⟩
  let F' : Fin 2 → C(Metric.closedBall (0 : Schoenflies.Plane) 1, S) := fun i => F (r i)
  let m' : Fin 2 → Metric.closedBall (0 : Schoenflies.Plane) 1 := fun i => m (r i)
  have hF' : ∀ i, IsEmbedding (F' i) := by
    intro i
    exact hF (r i)
  have hm' : ∀ i, ‖(m' i).val‖ < 1 := by
    intro i
    exact hm (r i)
  have honly' : ∀ i z, F' i z ∈ M.cover.branch ↔ z = m' i := by
    intro i z
    exact honly (r i) z
  have hcell0 :
      Set.range (fun t => f ((P.trans χ.symm) t)) = F' 0 '' {z | ‖z.val‖ = 1} := by
    have hr := hmapRange (P.trans χ.symm)
      (frontier (Icc (lo (r 0)).1 (hi (r 0)).1 ×ˢ
        Icc (lo (r 0)).2 (hi (r 0)).2)) h0
    rw [hr]
    simpa [F', m'] using hcell (r 0)
  have hcell1 :
      Set.range (fun t => f ((χ.trans Q) t)) = F' 1 '' {z | ‖z.val‖ = 1} := by
    have hr := hmapRange (χ.trans Q)
      (frontier (Icc (lo (r 1)).1 (hi (r 1)).1 ×ˢ
        Icc (lo (r 1)).2 (hi (r 1)).2)) h1
    rw [hr]
    simpa [F', m'] using hcell (r 1)
  have hco' : ∀ s t, f ((P.trans Q) s) = f ((P.trans Q) t) →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    intro s t h
    apply hco s t
    exact hf.injective h
  have hOuterRange :
      Set.range (fun t => f ((P.trans Q) t)) = a.image := by
    have hr := hmapRange (P.trans Q) (frontier (Icc a₀ b₀ ×ˢ Icc c₀ d₀)) ho
    rw [hr]
    exact houter
  exact two_marked_side_no_full_preimage_lifted M a K f hf x y P χ Q F' hF' m' hm'
    honly' hcell0 hcell1 hc0 hc1 hco' hOuterRange c hc

end CurveComplex.HyperellipticModel
