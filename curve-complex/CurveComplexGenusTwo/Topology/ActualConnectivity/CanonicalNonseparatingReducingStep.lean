import CurveComplexGenusTwo.Topology.ActualConnectivity.CanonicalSourceSurgeryPreparation
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnBranchPushOff
import CurveComplexGenusTwo.Topology.ThetaRetention.ThetaRetention
namespace CurveComplex
theorem source_genus_two_nonseparating_reducing_step
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
    (α β : {v : Vertex S // nonseparatingVertex v})
    (hlarge : 1 < geometricIntersection α.val β.val) :
    ∃ γ : {v : Vertex S // nonseparatingVertex v},
      geometricIntersection α.val γ.val ≤ 1 ∧
      geometricIntersection γ.val β.val < geometricIntersection α.val β.val := by
  let : ClosedSurface S := Classical.choice hS.2.1
  obtain ⟨P⟩ := source_nonseparating_surgery_preparation S α β hlarge
  obtain ⟨i,hraw⟩ := source_genus_two_theta_nonseparating_retention S hS
    P.first_return P.branches P.current_nonseparating
  obtain ⟨d,hrel,hbd,had,hb,ha⟩ := source_genus_two_first_return_branch_push_off
    S hS P.first_return P.branches (transverse_symm_of_chart P.transverse) i
  have hrawEssential := source_nonseparating_curve_essential S (P.branches.boundary i) hraw
  have hdEssential : Essential d := (essential_isotopy_invariant hrel).mp hrawEssential
  let raw : EssentialCurve S := ⟨P.branches.boundary i,hrawEssential⟩
  let dc : EssentialCurve S := ⟨d,hdEssential⟩
  have hdNonseparating : Nonseparating d :=
    (nonseparating_isotopy_invariant (a:=raw) (b:=dc) hrel).mp hraw
  let γ : {v : Vertex S // nonseparatingVertex v} :=
    ⟨Quotient.mk (essentialCurveSetoid S) dc,hdNonseparating⟩
  have hcurrent : geometricIntersection α.val γ.val ≤ hbd.1.toFinset.card := by
    apply Nat.sInf_le
    exact ⟨P.current,dc,P.current_class,rfl,hbd,rfl⟩
  have htarget : geometricIntersection β.val γ.val ≤ had.1.toFinset.card := by
    apply Nat.sInf_le
    exact ⟨P.target,dc,P.target_class,rfl,had,rfl⟩
  have hretained := (P.crossing_budget i).2
  change (source_surgery_retained_crossings P.branches i).ncard+2≤
    geometricIntersection α.val β.val at hretained
  refine ⟨γ,hcurrent.trans hb,?_⟩
  rw [geometricIntersection_symm_of_chart γ.val β.val]
  exact htarget.trans_lt (by omega)
end CurveComplex
#print axioms CurveComplex.source_genus_two_nonseparating_reducing_step
