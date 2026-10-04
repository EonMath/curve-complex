import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedCrossingStrips
import Mathlib.Topology.OpenPartialHomeomorph.Composition

namespace CurveComplex
open Set Topology

/-- Turn the actual two-axis crossing chart into an open partial homeomorphism,
localized inside any prescribed open neighbourhood of the crossing. -/
theorem source_crossing_open_partial_chart
    {S : Type} [TopologicalSpace S]
    {a b : Curve S} {p : S} (hp : CrossesAt a b p)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ E : OpenPartialHomeomorph S (ℝ × ℝ),
      p ∈ E.source ∧ E.source ⊆ W ∧ E p = (0,0) ∧
      (∀ x ∈ E.source, x ∈ a.image ↔ (E x).1 = 0) ∧
      (∀ x ∈ E.source, x ∈ b.image ↔ (E x).2 = 0) := by
  classical
  obtain ⟨U,V,hpU,e,hU,hV,hep,haxes⟩ := hp
  have : Nonempty U := ⟨⟨p,hpU⟩⟩
  let coeU : OpenPartialHomeomorph U S :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  let f : U → ℝ × ℝ := fun u => (e u : ℝ × ℝ)
  have hf : IsOpenEmbedding f := hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  let coeE : OpenPartialHomeomorph U (ℝ × ℝ) := hf.toOpenPartialHomeomorph f
  let E0 := coeU.symm.trans coeE
  have hE0source : E0.source = U := by
    simp [E0,coeU,coeE,
      IsOpenEmbedding.toOpenPartialHomeomorph_target]
  have hE0 (x : S) (hx : x ∈ U) : E0 x = (e ⟨x,hx⟩ : ℝ × ℝ) := by
    have hu : coeU.symm x = ⟨x,hx⟩ := by
      exact hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv (x := ⟨x,hx⟩)
    change f (coeU.symm x) = _
    rw [hu]
  let E := E0.restr W
  have hEs : E.source = U ∩ W := by
    simp [E,hW.interior_eq,hE0source]
  refine ⟨E,hEs.symm ▸ ⟨hpU,hpW⟩,?_,?_,?_,?_⟩
  · intro x hx
    exact (hEs.le hx).2
  · change E0 p = (0,0)
    exact (hE0 p hpU).trans hep
  · intro x hx
    change x ∈ a.image ↔ (E0 x).1 = 0
    rw [hE0 x (hEs.le hx).1]
    exact (haxes x (hEs.le hx).1).1
  · intro x hx
    change x ∈ b.image ↔ (E0 x).2 = 0
    rw [hE0 x (hEs.le hx).1]
    exact (haxes x (hEs.le hx).1).2

/-- Actual mutually disjoint retained-crossing charts for the WHOLE chosen
raw surgery boundary. The charts avoid both the first-return arc and the other
closing arc, so the raw branch and current curve have exactly the same local
horizontal trace. -/
theorem source_retained_branch_crossing_charts
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ E : ↥(source_surgery_retained_crossings B i) →
        OpenPartialHomeomorph S (ℝ × ℝ),
      (∀ p, p.val ∈ (E p).source ∧ E p p.val = (0,0)) ∧
      (∀ p q, p ≠ q → Disjoint (E p).source (E q).source) ∧
      (∀ p, Disjoint (E p).source (Set.range D.first)) ∧
      (∀ p, Disjoint (E p).source (Set.range (B.closing (!i)))) ∧
      (∀ p x, x ∈ (E p).source → (x ∈ a.image ↔ (E p x).1 = 0)) ∧
      (∀ p x, x ∈ (E p).source → (x ∈ b.image ↔ (E p x).2 = 0)) ∧
      (∀ p x, x ∈ (E p).source →
        (x ∈ (B.boundary i).image ↔ (E p x).2 = 0)) := by
  classical
  let R := source_surgery_retained_crossings B i
  have hRfin : R.Finite := (source_surgery_closing_crossings_budget D B ht i).1
  have hclosing (x : S) (hx : x ∈ Set.range (B.closing i)) : x ∈ b.image := by
    rw [← B.closing_cover]
    cases i
    · exact Or.inl hx
    · exact Or.inr hx
  have hRold (p : R) : p.val ∈ a.image ∩ b.image :=
    ⟨p.property.1.2,hclosing _ p.property.1.1⟩
  have hRfirst (p : R) : p.val ∉ Set.range D.first := by
    rintro ⟨t,htp⟩
    by_cases ht0 : t = 0
    · exact p.property.2 (Or.inl (htp.symm.trans (ht0 ▸ D.first_zero)))
    by_cases ht1 : t = 1
    · exact p.property.2 (Or.inr (htp.symm.trans (ht1 ▸ D.first_one)))
    exact D.first_interior_avoids t ht0 ht1 (htp.symm ▸ (hRold p).2)
  have hRother (p : R) : p.val ∉ Set.range (B.closing (!i)) := by
    intro hp
    apply p.property.2
    rw [← B.closing_inter]
    cases i
    · exact ⟨p.property.1.1,hp⟩
    · exact ⟨hp,p.property.1.1⟩
  obtain ⟨N,hN,hNdis⟩ := hRfin.t2_separation
  let W : R → Set S := fun p =>
    (N p.val ∩ (Set.range D.first)ᶜ) ∩ (Set.range (B.closing (!i)))ᶜ
  have hW (p : R) : IsOpen (W p) :=
    ((hN p.val).2.inter (isCompact_range D.first.continuous).isClosed.isOpen_compl).inter
      (isCompact_range (B.closing (!i)).continuous).isClosed.isOpen_compl
  have hpW (p : R) : p.val ∈ W p := ⟨⟨(hN p.val).1,hRfirst p⟩,hRother p⟩
  choose E hpE hEW hEzero ha hb using fun p : R =>
    source_crossing_open_partial_chart (ht.2 p.val (hRold p)) (W p) (hW p) (hpW p)
  refine ⟨E,(fun p => ⟨hpE p,hEzero p⟩),?_,?_,?_,ha,hb,?_⟩
  · intro p q hpq
    exact (hNdis p.property q.property (fun he => hpq (Subtype.ext he))).mono
      (fun _ hx => (hEW p hx).1.1) (fun _ hx => (hEW q hx).1.1)
  · intro p
    exact Set.disjoint_left.mpr (fun _ hx hf => (hEW p hx).1.2 hf)
  · intro p
    exact Set.disjoint_left.mpr (fun _ hx hf => (hEW p hx).2 hf)
  · intro p x hx
    rw [← hb p x hx,B.boundary_image]
    constructor
    · intro hc
      rcases hc with hf | hc
      · exact False.elim ((hEW p hx).1.2 hf)
      · exact hclosing x hc
    · intro hxb
      rw [← B.closing_cover] at hxb
      cases i
      · exact Or.inr (hxb.resolve_right (hEW p hx).2)
      · exact Or.inr (hxb.resolve_left (hEW p hx).2)

end CurveComplex
#print axioms CurveComplex.source_crossing_open_partial_chart
#print axioms CurveComplex.source_retained_branch_crossing_charts
