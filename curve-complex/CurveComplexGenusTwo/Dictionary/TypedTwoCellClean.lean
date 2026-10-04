import CurveComplexGenusTwo.Dictionary.RectangleTwoCellCrosscut
open Set Topology
namespace CurveComplex
set_option maxHeartbeats 12000000
/-- Typed subtype adapter for two-cell rectangle crosscut. -/
theorem rectangle_two_cell_crosscut_typed_clean
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (lo hi : Fin 2 → ℝ × ℝ)
    (hshape :
      (∃ k : ℝ, lo = ![(a,c),(k,c)] ∧ hi = ![(k,d),(b,d)] ∧ a < k ∧ k < b) ∨
      (∃ k : ℝ, lo = ![(a,c),(a,k)] ∧ hi = ![(b,k),(b,d)] ∧ c < k ∧ k < d)) :
    let R := Icc a b ×ˢ Icc c d
    ∃ r : Fin 2 → Fin 2, ∃ x y : R,
    ∃ P : Path x y, ∃ Q : Path y x, ∃ χ : Path x y,
      Set.range (fun t => ((P.trans χ.symm) t).val) =
          frontier (Icc (lo (r 0)).1 (hi (r 0)).1 ×ˢ
            Icc (lo (r 0)).2 (hi (r 0)).2) ∧
      Set.range (fun t => ((χ.trans Q) t).val) =
          frontier (Icc (lo (r 1)).1 (hi (r 1)).1 ×ˢ
            Icc (lo (r 1)).2 (hi (r 1)).2) ∧
      Set.range (fun t => ((P.trans Q) t).val) = frontier (Icc a b ×ˢ Icc c d) ∧
      (∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
      (∀ s t, (χ.trans Q) s = (χ.trans Q) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
      (∀ s t, (P.trans Q) s = (P.trans Q) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) := by
  dsimp
  let R : Set (ℝ × ℝ) := Icc a b ×ˢ Icc c d
  have hContain : ∀ i, (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2) ⊆ R := by
    rcases hshape with ⟨k, hlo, hhi, hak, hkb⟩ | ⟨k, hlo, hhi, hck, hkd⟩
    · subst lo hi
      intro i
      fin_cases i <;> intro z hz <;>
        simp only [Set.mem_prod, Set.mem_Icc] at hz ⊢ <;>
        dsimp at hz ⊢ <;>
        constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    · subst lo hi
      intro i
      fin_cases i <;> intro z hz <;>
        simp only [Set.mem_prod, Set.mem_Icc] at hz ⊢ <;>
        dsimp at hz ⊢ <;>
        constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  have hfront (i : Fin 2) : frontier (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2) ⊆ R := by
    intro z hz
    have hclosed : IsClosed (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2) :=
      isClosed_Icc.prod isClosed_Icc
    exact hContain i (hclosed.frontier_subset hz)
  have houter : frontier R ⊆ R := by
    intro z hz
    exact (isClosed_Icc.prod isClosed_Icc).frontier_subset hz
  obtain ⟨r, x, y, P, Q, χ, h0, h1, ho, hc0, hc1, hco⟩ :=
    rectangle_two_cell_crosscut a b c d hab hcd lo hi hshape
  have hP : ∀ t, P t ∈ R := by
    intro t
    apply hfront (r 0)
    rw [← h0]
    rw [Path.trans_range]
    exact Or.inl ⟨t, rfl⟩
  have hχ : ∀ t, χ t ∈ R := by
    intro t
    apply hfront (r 1)
    rw [← h1]
    rw [Path.trans_range]
    exact Or.inl ⟨t, rfl⟩
  have hQ : ∀ t, Q t ∈ R := by
    intro t
    apply houter
    rw [← ho]
    rw [Path.trans_range]
    exact Or.inr ⟨t, rfl⟩
  have hLift {x y : ℝ × ℝ} (γ : Path x y) (hγ : ∀ t, γ t ∈ R)
      (hx : x ∈ R) (hy : y ∈ R) :
      ∃ δ : Path (⟨x, hx⟩ : R) ⟨y, hy⟩, δ.map continuous_subtype_val = γ := by
    let δ : Path (⟨x, hx⟩ : R) ⟨y, hy⟩ :=
      { toContinuousMap := ⟨fun t => ⟨γ t, hγ t⟩, γ.continuous.subtype_mk hγ⟩
        source' := Subtype.ext γ.source
        target' := Subtype.ext γ.target }
    refine ⟨δ, ?_⟩
    apply Path.ext
    funext t
    rfl
  have hx : x ∈ R := by simpa using hP 0
  have hy : y ∈ R := by simpa using hP 1
  obtain ⟨P', hPm⟩ := hLift P hP hx hy
  obtain ⟨Q', hQm⟩ := hLift Q hQ hy hx
  obtain ⟨χ', hχm⟩ := hLift χ hχ hx hy
  have hL : (P'.trans χ'.symm).map continuous_subtype_val = P.trans χ.symm := by
    rw [Path.map_trans, ← Path.map_symm, hPm, hχm]
  have hR : (χ'.trans Q').map continuous_subtype_val = χ.trans Q := by
    rw [Path.map_trans, hχm, hQm]
  have hO : (P'.trans Q').map continuous_subtype_val = P.trans Q := by
    rw [Path.map_trans, hPm, hQm]
  have hRange {x y : R} (δ : Path x y) (γ : Path x.val y.val)
      (he : δ.map continuous_subtype_val = γ) :
      Set.range (fun t => (δ t).val) = Set.range γ := by
    exact congrArg (fun p : Path x.val y.val => Set.range p) he
  have hColl {x : R} (δ : Path x x) (γ : Path x.val x.val)
      (he : δ.map continuous_subtype_val = γ)
      (hc : ∀ s t, γ s = γ t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) :
      ∀ s t, δ s = δ t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
    intro s t hst
    apply hc s t
    have hh := congrArg Subtype.val hst
    change (δ.map continuous_subtype_val) s = (δ.map continuous_subtype_val) t at hh
    simpa only [he] using hh
  refine ⟨r, ⟨x,hx⟩, ⟨y,hy⟩, P', Q', χ',
    (hRange _ _ hL).trans h0, (hRange _ _ hR).trans h1,
    (hRange _ _ hO).trans ho, hColl _ _ hL hc0, hColl _ _ hR hc1,
    hColl _ _ hO hco⟩
end CurveComplex
