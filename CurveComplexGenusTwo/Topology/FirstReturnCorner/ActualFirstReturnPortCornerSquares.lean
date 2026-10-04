import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualClosedSeparatedCornerSquares
namespace CurveComplex
open Set Topology Schoenflies
/-- Produce actual corner charts whose center parameters lie in the first or
last third of BOTH source arcs. Closed support separation and the full actual
two-axis/positive-L traces are retained. No parameter-order premise is used. -/
theorem source_first_return_ordered_port_corner_squares
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ E : Bool → OpenPartialHomeomorph S Plane,
      (∀ k, (if k then D.finish else D.start) ∈ (E k).source ∧
        E k (if k then D.finish else D.start)=0) ∧
      (∀ k, Plane.closedSquare 0 1 ⊆ (E k).target) ∧
      Disjoint (closure (E false).source) (closure (E true).source) ∧
      (∀ k, Disjoint (closure (E k).source) (source_surgery_retained_crossings B i)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ a.image ↔ E k x 0=0)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ b.image ↔ E k x 1=0)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ (B.boundary i).image ↔
        (E k x 0=0 ∧ 0≤E k x 1) ∨ (0≤E k x 0 ∧ E k x 1=0))) ∧
      (∀ k u, D.first u ∈ (E k).source →
        if k then (2/3:ℝ)<(u:ℝ) else (u:ℝ)<1/3) ∧
      (∀ k u, B.closing i u ∈ (E k).source →
        if k then (2/3:ℝ)<(u:ℝ) else (u:ℝ)<1/3) := by
  classical
  obtain ⟨A,hpA,hsqA,hdisA,hAR,haA,hbA,hbrA⟩ :=
    source_first_return_closed_separated_corner_squares S D B ht i
  let Bad : Bool → Set Interval := fun k =>
    if k then {u | (u:ℝ)≤2/3} else {u | (1/3:ℝ)≤(u:ℝ)}
  have hBad (k : Bool) : IsCompact (Bad k) := by
    cases k
    · exact (isClosed_le continuous_const continuous_subtype_val).isCompact
    · exact (isClosed_le continuous_subtype_val continuous_const).isCompact
  have hfBad (k : Bool) : IsClosed (D.first '' Bad k) :=
    ((hBad k).image D.first.continuous).isClosed
  have hgBad (k : Bool) : IsClosed (B.closing i '' Bad k) :=
    ((hBad k).image (B.closing i).continuous).isClosed
  have hpfirst (k : Bool) : (if k then D.finish else D.start) ∉ D.first '' Bad k := by
    rintro ⟨u,hu,he⟩
    cases k
    · have hu0 : u=0 := D.first_embedded.injective (he.trans D.first_zero.symm)
      subst u
      norm_num [Bad] at hu
    · have hu1 : u=1 := D.first_embedded.injective (he.trans D.first_one.symm)
      subst u
      norm_num [Bad] at hu
  have hpclosing (k : Bool) : (if k then D.finish else D.start) ∉ B.closing i '' Bad k := by
    rintro ⟨u,hu,he⟩
    cases k
    · have hu0 : u=0 := (B.closing_embedded i).injective (he.trans (B.closing_zero i).symm)
      subst u
      norm_num [Bad] at hu
    · have hu1 : u=1 := (B.closing_embedded i).injective (he.trans (B.closing_one i).symm)
      subst u
      norm_num [Bad] at hu
  let V : Bool → Set S := fun k => (A k).source ∩
    (D.first '' Bad k ∪ B.closing i '' Bad k)ᶜ
  have hV (k : Bool) : IsOpen (V k) :=
    (A k).open_source.inter ((hfBad k).union (hgBad k)).isOpen_compl
  have hpV (k : Bool) : (if k then D.finish else D.start) ∈ V k :=
    ⟨(hpA k).1,fun hh => hh.elim (hpfirst k) (hpclosing k)⟩
  have hex (k : Bool) : ∃ W : Set S, IsOpen W ∧
      (if k then D.finish else D.start) ∈ W ∧ closure W ⊆ V k := by
    obtain ⟨W,hW,hpW,hclW⟩ := normal_exists_closure_subset
      (isClosed_singleton : IsClosed ({if k then D.finish else D.start} : Set S))
      (hV k) (Set.singleton_subset_iff.mpr (hpV k))
    exact ⟨W,hW,hpW (Set.mem_singleton _),hclW⟩
  choose W hW hpW hcW using hex
  choose E hpE hE0 hEW hsq hER ha hb hbr using fun k =>
    source_first_return_corner_square_in_open S D B ht i k (W k) (hW k) (hpW k)
  have hEclosed (k : Bool) : closure (E k).source ⊆ V k :=
    (closure_mono (hEW k)).trans (hcW k)
  have hEold (k : Bool) : closure (E k).source ⊆ closure (A k).source :=
    fun _ hx => subset_closure ((hEclosed k hx).1)
  refine ⟨E,(fun k => ⟨hpE k,hE0 k⟩),hsq,hdisA.mono (hEold false) (hEold true),
    (fun k => (hAR k).mono_left (hEold k)),ha,hb,hbr,?_,?_⟩
  · intro k u hu
    have hnot := (hEclosed k (subset_closure hu)).2
    have hn : u ∉ Bad k := fun hh => hnot (Or.inl ⟨u,hh,rfl⟩)
    cases k
    · exact lt_of_not_ge hn
    · exact lt_of_not_ge hn
  · intro k u hu
    have hnot := (hEclosed k (subset_closure hu)).2
    have hn : u ∉ Bad k := fun hh => hnot (Or.inr ⟨u,hh,rfl⟩)
    cases k
    · exact lt_of_not_ge hn
    · exact lt_of_not_ge hn
end CurveComplex
#print axioms CurveComplex.source_first_return_ordered_port_corner_squares
