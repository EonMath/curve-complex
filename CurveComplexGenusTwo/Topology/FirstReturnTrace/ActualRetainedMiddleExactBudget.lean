import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualClosingPortSourceOrder
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnBudgetTracks
namespace CurveComplex
open Set Topology
/-- Every actual retained crossing lies STRICTLY between the closing ports.
This follows from the exact source prefix/suffix and closed corner separation. -/
theorem source_retained_parameters_strictly_between_closing_ports
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (i : Bool)
    (F : SourceFirstReturnFramedStrips D B i) :
    ∀ p : source_surgery_retained_crossings B i,
      (F.θg false:ℝ)<F.θR p ∧ (F.θR p:ℝ)<F.θg true := by
  intro p
  constructor
  · by_contra hn
    have hh : F.θR p≤F.θg false := le_of_not_gt hn
    have hs := ((source_first_return_closing_ports_exact_source_order D B i F false (F.θR p)).mp hh).1
    rw [F.θR_center] at hs
    exact Set.disjoint_left.mp (F.retained_disjoint false) (subset_closure hs) p.property
  · by_contra hn
    have hh : F.θg true≤F.θR p := le_of_not_gt hn
    have hs := ((source_first_return_closing_ports_exact_source_order D B i F true (F.θR p)).mp hh).1
    rw [F.θR_center] at hs
    exact Set.disjoint_left.mp (F.retained_disjoint true) (subset_closure hs) p.property

/-- The ENTIRE closing middle track has EXACTLY R target contacts, for every
width: all original retained parameters are present and their framing points
are distinct. The whole-middle exclusion producer supplies the converse. -/
theorem source_closing_budget_middle_exact_target_count
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool)
    (P : SourceFirstReturnBudgetTracks D B i) (z : Set.Icc (-1:ℝ) 1) :
    ((fun u=>P.F.M (u,z)) '' Set.Icc (P.F.θg false) (P.F.θg true) ∩ a.image).Finite ∧
    ((fun u=>P.F.M (u,z)) '' Set.Icc (P.F.θg false) (P.F.θg true) ∩ a.image).ncard=
      (source_surgery_retained_crossings B i).ncard := by
  classical
  let R := source_surgery_retained_crossings B i
  let : Fintype R := (source_surgery_closing_crossings_budget D B ht i).1.fintype
  let Q : R → S := fun p=>P.F.M (P.F.θR p,z)
  have hQi : Function.Injective Q := by
    intro p q he
    exact P.F.θR_injective (congrArg Prod.fst (P.F.closing_embedding.injective he))
  have htarget (p : R) : Q p ∈ a.image := by
    obtain ⟨hs,hcoords⟩ := P.F.retained_framing p (P.F.θR p) z
      (by simpa using (P.F.retained_positive p).2)
    apply (P.F.retained_target_axis p _ hs).mpr
    have hh := congrArg (fun q : Schoenflies.Plane=>q 0) hcoords
    change P.F.ER p (P.F.M (P.F.θR p,z)) 0=P.F.ER p (B.closing i (P.F.θR p)) 0 at hh
    rw [P.F.θR_center,(P.F.retained_point p).2] at hh
    exact hh
  have hcharge : (fun u=>P.F.M (u,z)) '' Set.Icc (P.F.θg false) (P.F.θg true) ∩ a.image=Set.range Q := by
    ext x
    constructor
    · rintro ⟨⟨u,hu,rfl⟩,hx⟩
      obtain ⟨p,hup⟩ := (P.closing_middle u hu z).2 hx
      exact ⟨p,by rw [hup]⟩
    · rintro ⟨p,rfl⟩
      have hp := source_retained_parameters_strictly_between_closing_ports D B i P.F p
      exact ⟨⟨P.F.θR p,⟨hp.1.le,hp.2.le⟩,rfl⟩,htarget p⟩
  refine ⟨hcharge ▸ Set.finite_range Q,?_⟩
  rw [hcharge,Set.ncard_range_of_injective hQi]
  exact Nat.card_coe_set_eq R
end CurveComplex
#print axioms CurveComplex.source_retained_parameters_strictly_between_closing_ports
#print axioms CurveComplex.source_closing_budget_middle_exact_target_count
