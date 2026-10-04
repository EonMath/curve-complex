import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteScalarNegativeIntervals
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- A literal interior scalar root belongs to the actual adjacent mesh intervals;
no assumed combinatorial root-node assignment is needed. -/
theorem actual_scalar_mesh_root_adjacent_intervals
    (m : ℕ) (mesh : Fin (m+2) → Interval) (hmono : StrictMono mesh)
    (h0 : mesh 0=0) (h1 : mesh (Fin.last (m+1))=1) (g : C(Interval,ℝ))
    (hno : ∀ (j : Fin (m+1)) t,mesh j.castSucc < t → t < mesh j.succ → g t≠0)
    (u : Interval) (hu : 0<u.val ∧ u.val < 1) (hroot : g u=0) :
    ∃ l r : Fin (m+1),mesh l.succ=u ∧ mesh r.castSucc=u := by
  obtain ⟨j,hjl,hjr⟩ := actual_ordered_scalar_mesh_cover mesh hmono h0 h1 u
  have hnode : ∃ q : Fin (m+2),mesh q=u := by
    by_cases hl : mesh j.castSucc=u
    · exact ⟨j.castSucc,hl⟩
    · by_cases hr : mesh j.succ=u
      · exact ⟨j.succ,hr⟩
      · exact False.elim (hno j u (lt_of_le_of_ne hjl hl) (lt_of_le_of_ne hjr (Ne.symm hr)) hroot)
  obtain ⟨q,hq⟩ := hnode
  have hq0 : q≠0 := by
    intro he
    rw [he,h0] at hq
    have hh := hu.1
    rw [← hq] at hh
    exact (lt_irrefl 0) hh
  have hq1 : q≠Fin.last (m+1) := by
    intro he
    rw [he,h1] at hq
    have hh := hu.2
    rw [← hq] at hh
    exact (lt_irrefl 1) hh
  obtain ⟨l,hl⟩ := Fin.exists_succ_eq.mpr hq0
  obtain ⟨r,hr⟩ := Fin.exists_castSucc_eq.mpr hq1
  exact ⟨l,r,by rw [hl,hq],by rw [hr,hq]⟩
end CurveComplex.HyperellipticModel
