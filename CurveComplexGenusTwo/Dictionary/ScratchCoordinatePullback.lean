import CurveComplexGenusTwo.Dictionary.TypedTwoMarkBridge
import CurveComplexGenusTwo.Dictionary.TwoMarkedRectangleDiscCells

open Set Topology Metric

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

set_option maxHeartbeats 12000000
set_option linter.style.haveILetI false

noncomputable def dictPullbackEquiv : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).symm

noncomputable def dictPullbackRect : Set (ℝ × ℝ) :=
  Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1

noncomputable def dictPullbackSquare : Set Schoenflies.Plane :=
  dictPullbackEquiv '' dictPullbackRect

noncomputable def dictPullbackHomeomorph : dictPullbackRect ≃ₜ dictPullbackSquare :=
  Homeomorph.sets dictPullbackEquiv.toHomeomorph (by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact dictPullbackEquiv.injective hxy ▸ hy)

private theorem dictPullbackHomeomorph_image_frontier (C : Set (ℝ × ℝ))
    (hCfront : frontier C ⊆ dictPullbackRect) :
    dictPullbackHomeomorph '' {x : dictPullbackRect | x.val ∈ frontier C} =
      {z : dictPullbackSquare | z.val ∈ frontier (dictPullbackEquiv '' C)} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change dictPullbackEquiv.toHomeomorph x.val ∈
      frontier (dictPullbackEquiv.toHomeomorph '' C)
    rw [← dictPullbackEquiv.toHomeomorph.image_frontier]
    exact ⟨x.val, hx, rfl⟩
  · intro hz
    change z.val ∈ frontier (dictPullbackEquiv.toHomeomorph '' C) at hz
    rw [← dictPullbackEquiv.toHomeomorph.image_frontier] at hz
    rcases hz with ⟨x, hx, hzx⟩
    refine ⟨⟨x, hCfront hx⟩, hx, ?_⟩
    · apply Subtype.ext
      exact hzx

private theorem dictPullbackHomeomorph_image_square_frontier :
    dictPullbackHomeomorph '' {x : dictPullbackRect |
      x.val ∈ frontier ((Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1)} =
      {z : dictPullbackSquare | z.val ∈ frontier dictPullbackSquare} := by
  simpa [dictPullbackSquare, dictPullbackRect] using
    dictPullbackHomeomorph_image_frontier
      ((Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1) (by
        intro x hx
        exact (isClosed_Icc.prod isClosed_Icc).frontier_subset hx)

theorem two_marked_disc_chart_obstruction_coordinate_pullback
    (M : HyperellipticModel E S)
    (a : PuncturedCircle M)
    (f : C(dictPullbackSquare, S))
    (hf : IsEmbedding f)
    (hboundary : ∀ z, z.val ∈ frontier dictPullbackSquare → f z ∉ M.cover.branch)
    (hcard : (by classical exact
      (M.cover.branch.filter (fun b => b ∈ f '' {z |
        z.val ∈ interior dictPullbackSquare})).card = 2))
    (houter : f '' {z : dictPullbackSquare | z.val ∈ frontier dictPullbackSquare} = a.image)
    (c : Curve E) (hc : c.image = M.cover.projection ⁻¹' a.image) : False := by
  classical
  let g : C(dictPullbackRect, S) :=
    ⟨fun x => f (dictPullbackHomeomorph x),
      f.continuous.comp dictPullbackHomeomorph.continuous⟩
  have hg : IsEmbedding g := hf.comp dictPullbackHomeomorph.isEmbedding
  have hboundary' : ∀ x : dictPullbackRect, x.val ∈ frontier dictPullbackRect →
      g x ∉ M.cover.branch := by
    intro x hx
    apply hboundary (dictPullbackHomeomorph x)
    change dictPullbackHomeomorph x ∈
      {z : dictPullbackSquare | z.val ∈ frontier dictPullbackSquare}
    rw [← dictPullbackHomeomorph_image_square_frontier]
    exact ⟨x, hx, rfl⟩
  have hcard' : (M.cover.branch.filter (fun b => b ∈ g '' {x : dictPullbackRect |
      x.val ∈ interior dictPullbackRect})).card = 2 := by
    have hmap (A : Set dictPullbackRect) :
        g '' A = f '' (dictPullbackHomeomorph '' A) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨dictPullbackHomeomorph x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    have hinterior : dictPullbackHomeomorph '' {x : dictPullbackRect |
        x.val ∈ interior dictPullbackRect} =
        {z : dictPullbackSquare | z.val ∈ interior dictPullbackSquare} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        change dictPullbackEquiv.toHomeomorph x.val ∈
          interior (dictPullbackEquiv.toHomeomorph '' dictPullbackRect)
        rw [← dictPullbackEquiv.toHomeomorph.image_interior]
        exact ⟨x.val, hx, rfl⟩
      · intro hz
        change z.val ∈ interior (dictPullbackEquiv.toHomeomorph '' dictPullbackRect) at hz
        rw [← dictPullbackEquiv.toHomeomorph.image_interior] at hz
        rcases hz with ⟨x, hx, hzx⟩
        refine ⟨⟨x, interior_subset hx⟩, hx, ?_⟩
        apply Subtype.ext
        exact hzx
    rw [hmap, hinterior]
    exact hcard
  obtain ⟨lo, hi, F, m, hdims, _hcover, hshape, hfamily⟩ :=
    two_marked_rectangle_disc_cells M f hf hboundary hcard
  choose hFi hmi honly hcell using hfamily
  have hcell' : ∀ i, g '' {x : dictPullbackRect | x.val ∈ frontier
      (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)} =
      F i '' {z | ‖z.val‖ = 1} := by
    intro i
    have himage : dictPullbackHomeomorph '' {x : dictPullbackRect | x.val ∈
        frontier (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)} =
        {z : dictPullbackSquare | z.val ∈ frontier
          (dictPullbackEquiv '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2))} := by
      apply dictPullbackHomeomorph_image_frontier _
      intro x hx
      rcases hshape with ⟨k, hlo, hhi, hak, hkb⟩ | ⟨k, hlo, hhi, hck, hkd⟩
      · subst lo hi
        have hsub : ∀ i, (Icc ((![(-1,-1),(k,-1)] : Fin 2 → ℝ × ℝ) i).1
            ((![ (k,1),(1,1)] : Fin 2 → ℝ × ℝ) i).1 ×ˢ
            Icc ((![(-1,-1),(k,-1)] : Fin 2 → ℝ × ℝ) i).2
              ((![ (k,1),(1,1)] : Fin 2 → ℝ × ℝ) i).2) ⊆ dictPullbackRect := by
          intro j z hz
          fin_cases j <;> simp only [Set.mem_prod, Set.mem_Icc] at hz ⊢ <;>
            dsimp at hz ⊢ <;> constructor <;> constructor <;>
              linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
        exact hsub i ((isClosed_Icc.prod isClosed_Icc).frontier_subset hx)
      · subst lo hi
        have hsub : ∀ i, (Icc ((![(-1,-1),(-1,k)] : Fin 2 → ℝ × ℝ) i).1
            ((![ (1,k),(1,1)] : Fin 2 → ℝ × ℝ) i).1 ×ˢ
            Icc ((![(-1,-1),(-1,k)] : Fin 2 → ℝ × ℝ) i).2
              ((![ (1,k),(1,1)] : Fin 2 → ℝ × ℝ) i).2) ⊆ dictPullbackRect := by
          intro j z hz
          fin_cases j <;> simp only [Set.mem_prod, Set.mem_Icc] at hz ⊢ <;>
            dsimp at hz ⊢ <;> constructor <;> constructor <;>
              linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
        exact hsub i ((isClosed_Icc.prod isClosed_Icc).frontier_subset hx)
    have hmap (A : Set dictPullbackRect) :
        g '' A = f '' (dictPullbackHomeomorph '' A) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨dictPullbackHomeomorph x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [hmap, himage]
    exact (hcell i).symm
  have houter' : g '' {x : dictPullbackRect | x.val ∈ frontier dictPullbackRect} = a.image := by
    have hmap (A : Set dictPullbackRect) :
        g '' A = f '' (dictPullbackHomeomorph '' A) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨dictPullbackHomeomorph x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    have hfront : dictPullbackHomeomorph '' {x : dictPullbackRect |
        x.val ∈ frontier dictPullbackRect} =
        {z : dictPullbackSquare | z.val ∈ frontier dictPullbackSquare} := by
      simpa [dictPullbackRect] using dictPullbackHomeomorph_image_square_frontier
    rw [hmap, hfront]
    exact houter
  have hrectangle : (∀ i, ‖(m i).val‖ < 1) := fun i => hmi i
  exact rectangle_two_marked_side_obstruction_typed M a (-1) 1 (-1) 1
    (by norm_num) (by norm_num) lo hi hshape g hg F hFi m hrectangle honly
    hcell' houter' c hc

end CurveComplex.HyperellipticModel
