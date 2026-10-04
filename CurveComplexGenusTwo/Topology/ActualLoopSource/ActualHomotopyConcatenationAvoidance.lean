import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualHomotopyConcatenationPointCompatibility
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual concatenation preserves the branch/forbidden-set avoidance of the
constructed component movies. -/
theorem actual_homotopy_concatenation_avoidance
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f0 f1 f2 : C(X,Y)} (F : f0.Homotopy f1) (G : f1.Homotopy f2)
    (forbidden : Set Y) (hF : ∀ σ x,F (σ,x) ∉ forbidden)
    (hG : ∀ σ x,G (σ,x) ∉ forbidden) :
    ∀ σ x,(F.trans G) (σ,x) ∉ forbidden := by
  intro σ x
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hF _ x
  · exact hG _ x
theorem actual_three_stage_concatenation_avoidance
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f0 f1 f2 f3 : C(X,Y)}
    (F : f0.Homotopy f1) (G : f1.Homotopy f2) (K : f2.Homotopy f3)
    (forbidden : Set Y) (hF : ∀ σ x,F (σ,x) ∉ forbidden)
    (hG : ∀ σ x,G (σ,x) ∉ forbidden) (hK : ∀ σ x,K (σ,x) ∉ forbidden) :
    ∀ σ x,((F.trans G).trans K) (σ,x) ∉ forbidden := by
  exact actual_homotopy_concatenation_avoidance (F.trans G) K forbidden
    (actual_homotopy_concatenation_avoidance F G forbidden hF hG) hK
end CurveComplex.HyperellipticModel
