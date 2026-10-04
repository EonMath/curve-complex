import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnBudgetTracks
namespace CurveComplex
open Set Topology
/-- The entire four-piece pushed trace, using the actual common track widths. -/
def SourceFirstReturnBudgetTracks.trace
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    {D : SourceFirstReturnBoundary a b} {B : SourceTwoSurgeryBranches D} {i : Bool}
    (P : SourceFirstReturnBudgetTracks D B i) : Set S :=
    (fun u=>P.F.N (u,P.caps.w)) '' Set.Icc (P.F.θf false) (P.F.θf true) ∪
    (fun u=>P.F.M (u,P.caps.z)) '' Set.Icc (P.F.θg false) (P.F.θg true) ∪
    Set.range (P.caps.C false) ∪ Set.range (P.caps.C true)

/-- The actual WHOLE trace has at most one current contact and at most
R+1 target contacts. The latter is strictly below the starting transverse
intersection number. No crossing count is supplied as a hypothesis. -/
theorem source_first_return_whole_trace_budget
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool)
    (P : SourceFirstReturnBudgetTracks D B i) :
    (P.trace ∩ a.image).Finite ∧ (P.trace ∩ b.image).Finite ∧
      (P.trace ∩ a.image).ncard≤(source_surgery_retained_crossings B i).ncard+1 ∧
      (P.trace ∩ b.image).ncard≤1 ∧
      (P.trace ∩ a.image).ncard<ht.1.toFinset.card := by
  classical
  let R := source_surgery_retained_crossings B i
  let : Fintype R := (source_surgery_closing_crossings_budget D B ht i).1.fintype
  let Tf := (fun u=>P.F.N (u,P.caps.w)) '' Set.Icc (P.F.θf false) (P.F.θf true)
  let Tg := (fun u=>P.F.M (u,P.caps.z)) '' Set.Icc (P.F.θg false) (P.F.θg true)
  have hfa : Disjoint Tf a.image := Set.disjoint_left.mpr (by
    rintro x ⟨u,hu,rfl⟩ hx
    exact P.caps.width_nonzero.1 ((P.first_middle u hu P.caps.w).2.mp hx))
  have hfb : Disjoint Tf b.image := Set.disjoint_left.mpr (by
    rintro x ⟨u,hu,rfl⟩ hx
    exact (P.first_middle u hu P.caps.w).1 hx)
  have hgb : Disjoint Tg b.image := Set.disjoint_left.mpr (by
    rintro x ⟨u,hu,rfl⟩ hx
    exact P.caps.width_nonzero.2 ((P.closing_middle u hu P.caps.z).1.mp hx))
  let Q : R → S := fun p=>P.F.M (P.F.θR p,P.caps.z)
  have hQi : Function.Injective Q := by
    intro p q he
    exact P.F.θR_injective (congrArg Prod.fst (P.F.closing_embedding.injective he))
  have hgsub : Tg ∩ a.image ⊆ Set.range Q := by
    rintro x ⟨⟨u,hu,rfl⟩,hx⟩
    obtain ⟨p,hup⟩ := (P.closing_middle u hu P.caps.z).2 hx
    exact ⟨p,by rw [hup]⟩
  have hgfin : (Tg ∩ a.image).Finite := (Set.finite_range Q).subset hgsub
  have hgcard : (Tg ∩ a.image).ncard≤R.ncard := by
    have hh := Set.ncard_le_ncard hgsub (Set.finite_range Q)
    rw [Set.ncard_range_of_injective hQi,Nat.card_coe_set_eq R] at hh
    exact hh
  have htarget : P.trace ∩ a.image=(Tg ∩ a.image) ∪ (Set.range (P.caps.C true) ∩ a.image) := by
    ext x
    constructor
    · rintro ⟨((hx|hx)|hx)|hx,hxa⟩
      · exact (Set.disjoint_left.mp hfa hx hxa).elim
      · exact Or.inl ⟨hx,hxa⟩
      · exact (Set.disjoint_left.mp P.caps.start_avoids_target hx hxa).elim
      · exact Or.inr ⟨hx,hxa⟩
    · rintro (⟨hx,hxa⟩|⟨hx,hxa⟩)
      · exact ⟨Or.inl (Or.inl (Or.inr hx)),hxa⟩
      · exact ⟨Or.inr hx,hxa⟩
  have hcurrent : P.trace ∩ b.image=Set.range (P.caps.C true) ∩ b.image := by
    ext x
    constructor
    · rintro ⟨((hx|hx)|hx)|hx,hxb⟩
      · exact (Set.disjoint_left.mp hfb hx hxb).elim
      · exact (Set.disjoint_left.mp hgb hx hxb).elim
      · exact (Set.disjoint_left.mp P.caps.start_avoids_current hx hxb).elim
      · exact ⟨hx,hxb⟩
    · rintro ⟨hx,hxb⟩
      exact ⟨Or.inr hx,hxb⟩
  have hbudget : (P.trace ∩ a.image).ncard≤R.ncard+1 := by
    rw [htarget]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add hgcard (P.caps.target_budget true))
  refine ⟨htarget ▸ hgfin.union (P.caps.target_finite true),
    hcurrent ▸ P.caps.current_finite true,hbudget,hcurrent ▸ P.caps.current_budget true,?_⟩
  have hold := (source_surgery_closing_crossings_budget D B ht i).2
  change R.ncard+2≤(a.image ∩ b.image).ncard at hold
  rw [Set.ncard_eq_toFinset_card _ ht.1] at hold
  omega

theorem source_first_return_actual_strictly_reduced_trace
    (S : Type) [TopologicalSpace S] [ChartedSpace Schoenflies.Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ P : SourceFirstReturnBudgetTracks D B i,
      (P.trace ∩ a.image).Finite ∧ (P.trace ∩ b.image).Finite ∧
      (P.trace ∩ a.image).ncard≤(source_surgery_retained_crossings B i).ncard+1 ∧
      (P.trace ∩ b.image).ncard≤1 ∧ (P.trace ∩ a.image).ncard<ht.1.toFinset.card := by
  obtain ⟨P⟩ := source_first_return_actual_budget_tracks S D B ht i
  exact ⟨P,source_first_return_whole_trace_budget D B ht i P⟩
end CurveComplex
#print axioms CurveComplex.source_first_return_whole_trace_budget
#print axioms CurveComplex.source_first_return_actual_strictly_reduced_trace
