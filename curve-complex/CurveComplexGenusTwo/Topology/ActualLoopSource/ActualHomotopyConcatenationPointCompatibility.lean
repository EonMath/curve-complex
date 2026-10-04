import Mathlib.Topology.Homotopy.Basic
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Concatenation retains actual pointwise agreement of both component movies,
even when the two cells have different parameter domains. -/
theorem actual_homotopy_concatenation_point_compatibility
    {X X' Y : Type} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
    {f0 f1 f2 : C(X,Y)} {g0 g1 g2 : C(X',Y)}
    (F : f0.Homotopy f1) (G : f1.Homotopy f2)
    (F' : g0.Homotopy g1) (G' : g1.Homotopy g2)
    (x : X) (y : X')
    (hF : ∀ σ,F (σ,x)=F' (σ,y)) (hG : ∀ σ,G (σ,x)=G' (σ,y)) :
    ∀ σ,(F.trans G) (σ,x)=(F'.trans G') (σ,y) := by
  intro σ
  rw [ContinuousMap.Homotopy.trans_apply,ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hF _
  · exact hG _
/-- The common three-stage schedule preserves actual shared-edge agreement. -/
theorem actual_three_stage_point_compatibility
    {X X' Y : Type} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
    {f0 f1 f2 f3 : C(X,Y)} {g0 g1 g2 g3 : C(X',Y)}
    (F : f0.Homotopy f1) (G : f1.Homotopy f2) (K : f2.Homotopy f3)
    (F' : g0.Homotopy g1) (G' : g1.Homotopy g2) (K' : g2.Homotopy g3)
    (x : X) (y : X')
    (hF : ∀ σ,F (σ,x)=F' (σ,y)) (hG : ∀ σ,G (σ,x)=G' (σ,y))
    (hK : ∀ σ,K (σ,x)=K' (σ,y)) :
    ∀ σ,((F.trans G).trans K) (σ,x)=((F'.trans G').trans K') (σ,y) := by
  exact actual_homotopy_concatenation_point_compatibility
    (F.trans G) K (F'.trans G') K' x y
    (actual_homotopy_concatenation_point_compatibility F G F' G' x y hF hG) hK
end CurveComplex.HyperellipticModel
