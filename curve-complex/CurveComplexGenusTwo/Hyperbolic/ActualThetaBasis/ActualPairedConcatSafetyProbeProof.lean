import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualPairedConcatGeometryProof
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualLoopTransportDefinitions
open Set Topology
namespace CurveComplex.Hyperbolic.PantsTheta
theorem paired_concat_interpolation_safety (n : ℕ) (p q : Fin (n+1) → ActualPuncturedRealPlane)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (G : (i : Fin n) → Path (q i.castSucc) (q i.succ))
    (hp : ∀ s : unitInterval,
      (1-s.val) • (p 0).val+s.val • (q 0).val ≠ ((0:ℝ),0) ∧
      (1-s.val) • (p 0).val+s.val • (q 0).val ≠ ((1:ℝ),0))
    (hF : ∀ (i : Fin n) (t s : unitInterval),
      (1-s.val) • (F i t).val+s.val • (G i t).val ≠ ((0:ℝ),0) ∧
      (1-s.val) • (F i t).val+s.val • (G i t).val ≠ ((1:ℝ),0)) :
    ∀ (t s : unitInterval),
      (1-s.val) • (Path.concat p F t).val+s.val • (Path.concat q G t).val ≠ ((0:ℝ),0) ∧
      (1-s.val) • (Path.concat p F t).val+s.val • (Path.concat q G t).val ≠ ((1:ℝ),0) := by
  let M : Set (ActualPuncturedRealPlane × ActualPuncturedRealPlane) := {z | ∀ s : unitInterval,
      (1-s.val) • z.1.val+s.val • z.2.val ≠ ((0:ℝ),0) ∧
      (1-s.val) • z.1.val+s.val • z.2.val ≠ ((1:ℝ),0)}
  have h := concat_paths_range_subset n (fun i=>(p i,q i))
    (fun i=>(F i).prod (G i)) M hp (fun i t => hF i t)
  rw [concat_prod_paths] at h
  exact h
end CurveComplex.Hyperbolic.PantsTheta
