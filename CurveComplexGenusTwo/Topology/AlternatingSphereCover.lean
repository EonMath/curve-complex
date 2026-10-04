import Mathlib

/-! Statement-review packet: global alternating equator gluing. -/
namespace AlternatingSphereCover

abbrev Sphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def height (x : Sphere) : ℝ := x.val 2

def seamPolynomial (x : Sphere) : ℝ :=
  x.val 1 * (3 * (x.val 0)^2 - (x.val 1)^2)

def branch (x : Sphere) : Prop := height x = 0 ∧ seamPolynomial x = 0

/-- Two hemispheres, each carrying two sheets. Hemisphere true is the northern one. -/
abbrev Raw := {p : Sphere × Bool × Bool //
  if p.2.1 then 0 ≤ height p.1 else height p.1 ≤ 0}

noncomputable def label (x : Raw) : Bool :=
  x.val.2.2 ^^ (x.val.2.1 && decide (0 < seamPolynomial x.val.1))

/-- Across the equator, glue opposite sheets on positive polynomial arcs and
identical sheets on negative arcs. At the six zeroes glue all incident banks. -/
def Rel (x y : Raw) : Prop :=
  x.val.1 = y.val.1 ∧ (branch x.val.1 ∨ label x = label y)

def setoid : Setoid Raw where
  r := Rel
  iseqv := by
    refine ⟨fun x => ⟨rfl, Or.inr rfl⟩, ?_, ?_⟩
    · intro x y h
      exact ⟨h.1.symm, h.2.elim (fun hb => Or.inl (h.1 ▸ hb))
        (fun hl => Or.inr hl.symm)⟩
    · intro x y z hxy hyz
      refine ⟨hxy.1.trans hyz.1, ?_⟩
      rcases hxy.2 with hb | hl
      · exact Or.inl hb
      rcases hyz.2 with hb | hl'
      · exact Or.inl (hxy.1 ▸ hb)
      · exact Or.inr (hl.trans hl')

abbrev Total := Quotient setoid

/-- The quotient topology is inherited from the four closed hemispheres. -/
instance : TopologicalSpace Total := inferInstanceAs (TopologicalSpace (Quotient setoid))

def projection : Total → Sphere :=
  Quotient.lift (fun x : Raw => x.val.1) (by intro x y h; exact h.1)

def rawDeck (x : Raw) : Raw :=
  ⟨(x.val.1, x.val.2.1, !x.val.2.2), x.property⟩

theorem label_rawDeck (x : Raw) : label (rawDeck x) = !(label x) := by
  simp [label, rawDeck, Bool.not_xor] <;> rfl

theorem rawDeck_continuous : Continuous rawDeck := by
  unfold rawDeck
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact continuous_fst.comp continuous_subtype_val
  apply Continuous.prodMk
  · exact continuous_fst.comp (continuous_snd.comp continuous_subtype_val)
  · exact (continuous_of_discreteTopology : Continuous Bool.not).comp
      (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))

def deck : Total → Total := Quotient.map rawDeck (by
  intro x y h
  refine ⟨h.1, ?_⟩
  rcases h.2 with hb | hl
  · exact Or.inl hb
  · exact Or.inr (by rw [label_rawDeck, label_rawDeck, hl]))

theorem projection_continuous : Continuous projection := by
  exact (continuous_fst.comp continuous_subtype_val).quotient_lift _

theorem projection_surjective : Function.Surjective projection := by
  intro b
  by_cases hb : 0 ≤ height b
  · exact ⟨Quotient.mk setoid ⟨(b, true, false), hb⟩, rfl⟩
  · exact ⟨Quotient.mk setoid ⟨(b, false, false), le_of_not_ge hb⟩, rfl⟩

theorem deck_continuous : Continuous deck := by
  exact (continuous_quotient_mk'.comp rawDeck_continuous).quotient_lift _

theorem deck_involution (x : Total) : deck (deck x) = x := by
  induction x using Quotient.inductionOn with
  | h x =>
    change Quotient.mk setoid (rawDeck (rawDeck x)) = Quotient.mk setoid x
    congr 1
    apply Subtype.ext
    simp [rawDeck]

def deckHomeomorph : Total ≃ₜ Total where
  toFun := deck
  invFun := deck
  left_inv := deck_involution
  right_inv := deck_involution
  continuous_toFun := deck_continuous
  continuous_invFun := deck_continuous

theorem projection_deck (x : Total) : projection (deck x) = projection x := by
  induction x using Quotient.inductionOn with
  | h x => rfl

theorem fiber_pair (x y : Total) :
    projection x = projection y ↔ y = x ∨ y = deck x := by
  constructor
  · induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro hxy
        change x.val.1 = y.val.1 at hxy
        by_cases h : label y = label x
        · exact Or.inl (Quotient.sound ⟨hxy.symm, Or.inr h⟩)
        · right
          apply Quotient.sound
          refine ⟨hxy.symm, Or.inr ?_⟩
          have hd : label (rawDeck x) = !(label x) := by
            simp [label, rawDeck, Bool.not_xor] <;> rfl
          rw [hd]
          cases hx : label x <;> cases hy : label y <;> simp_all
  · rintro (rfl | rfl)
    · rfl
    · exact (projection_deck x).symm

theorem fixed_iff_branch (x : Total) : deck x = x ↔ branch (projection x) := by
  induction x using Quotient.inductionOn with
  | h x =>
    change Quotient.mk setoid (rawDeck x) = Quotient.mk setoid x ↔ branch x.val.1
    rw [Quotient.eq]
    change (x.val.1 = x.val.1 ∧ (branch x.val.1 ∨ label (rawDeck x) = label x)) ↔ _
    have hd : label (rawDeck x) = !(label x) := by
      simp [label, rawDeck, Bool.not_xor] <;> rfl
    rw [hd]
    cases label x <;> simp

theorem fiber_finite (b : Sphere) : Set.Finite (projection ⁻¹' {b}) := by
  obtain ⟨x, rfl⟩ := projection_surjective b
  apply (Set.toFinite {x, deck x}).subset
  intro y hy
  have h : projection x = projection y := (Set.mem_preimage.mp hy).symm
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (fiber_pair x y).mp h

theorem branch_fiber_unique {b : Sphere} (hb : branch b) :
    ∃! x : Total, projection x = b := by
  obtain ⟨x, hx⟩ := projection_surjective b
  have hf : deck x = x := (fixed_iff_branch x).mpr (hx ▸ hb)
  refine ⟨x, hx, ?_⟩
  intro y hy
  rcases (fiber_pair x y).mp (hx.trans hy.symm) with h | h
  · exact h
  · exact h.trans hf

theorem nonbranch_fiber_pair {b : Sphere} (hb : ¬ branch b) :
    ∃ x y : Total, x ≠ y ∧ projection ⁻¹' {b} = {x, y} := by
  obtain ⟨x, hx⟩ := projection_surjective b
  refine ⟨x, deck x, ?_, ?_⟩
  · intro h
    exact hb (hx ▸ (fixed_iff_branch x).mp h.symm)
  · ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff]
    rw [← fiber_pair]
    exact ⟨fun h => hx.trans h.symm, fun h => h.symm.trans hx⟩

end AlternatingSphereCover
