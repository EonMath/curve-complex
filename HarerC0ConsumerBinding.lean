import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceC0PathConnectedProof
import C0SourceFiniteCurveLoopSurgeryExact

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CategoryTheory.Limits Set CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false

theorem source_c0_simplyConnected_allGenus
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) :
    SimplyConnectedSpace (curveComplexRealization S 0) := by
  classical
  letI : DecidableEq (Vertex S) := Classical.decEq _
  letI : PathConnectedSpace (curveComplexRealization S 0) :=
    source_c0_pathConnected_allGenus S g hg hS
  let x : curveComplexRealization S 0 := Classical.choice PathConnectedSpace.nonempty
  obtain ⟨σ, hσ, _⟩ := x.liesInFace
  obtain ⟨v, hv⟩ := hσ.1
  have hvface : ({v} : Finset (Vertex S)) ∈ (curveComplex S 0).faces :=
    (curveComplex S 0).singleton_mem v
  let b := realizationVertex (curveComplex S 0) v hvface
  -- Genuine finite loop surgery/Harer filling, not the boundary relation of a simplex.
  have hedge : ∀ (q : Path b b), IsFiniteAffineEdgePath (curveComplex S 0) q →
      Path.Homotopic q (Path.refl b) := by
    intro q hq
    exact source_c0_finite_curve_loop_surgery S g hg hS v q hq
  have hnull (p : Path b b) : Path.Homotopic p (Path.refl b) := by
    obtain ⟨q, hpq, hq⟩ :=
      exists_based_loop_affine_edge_path (curveComplex S 0) v hvface p
    exact hpq.trans (hedge q hq)
  have hbase : ∀ a c : FundamentalGroup (curveComplexRealization S 0) b, a = c := by
    intro a c
    induction a using Quotient.inductionOn with
    | h p =>
      induction c using Quotient.inductionOn with
      | h q => exact Quotient.sound ((hnull p).trans (hnull q).symm)
  have hall (y : curveComplexRealization S 0) :
      ∀ a c : FundamentalGroup (curveComplexRealization S 0) y, a = c := by
    let e := FundamentalGroup.fundamentalGroupMulEquivOfPath
      (PathConnectedSpace.somePath b y)
    intro a c
    calc
      a = e (e.symm a) := (e.apply_symm_apply a).symm
      _ = e (e.symm c) := congrArg e (hbase (e.symm a) (e.symm c))
      _ = c := e.apply_symm_apply c
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro y γ
  exact Quotient.eq.mp (hall y (⟦γ⟧ : FundamentalGroup (curveComplexRealization S 0) y) 1)

end CurveComplexGenusTwo.SourceTopology
