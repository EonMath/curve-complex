import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualSquareThetaCover
open Set Topology
namespace CurveComplex.Hyperbolic.PantsTheta
theorem concat_prod_paths {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (p : Fin (n+1) → X) (q : Fin (n+1) → Y)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (G : (i : Fin n) → Path (q i.castSucc) (q i.succ)) :
    Path.concat (fun i=>(p i,q i)) (fun i=>(F i).prod (G i))=
      (Path.concat p F).prod (Path.concat q G) := by
  induction n with
  | zero => simp only [Path.concat_zero];rfl
  | succ n ih =>
    rw [Path.concat_succ,Path.concat_succ p,Path.concat_succ q,ih,
      Path.trans_prod_eq_prod_trans]
    rfl

theorem concat_paths_range_subset {X : Type*} [TopologicalSpace X] (n : ℕ)
    (p : Fin (n+1) → X)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (M : Set X) (hp : p 0 ∈ M) (hF : ∀ i t,F i t ∈ M) :
    ∀ t,Path.concat p F t ∈ M := by
  induction n with
  | zero => simpa only [Path.concat_zero,Path.refl_apply] using fun _ : unitInterval => hp
  | succ n ih =>
    intro t
    rw [Path.concat_succ]
    have ht : (Path.concat (p ∘ Fin.castSucc) (fun i=>F i.castSucc)).trans (F (Fin.last n)) t ∈
        Set.range (Path.concat (p ∘ Fin.castSucc) (fun i=>F i.castSucc)) ∪ Set.range (F (Fin.last n)) := by
      rw [← Path.trans_range]
      exact Set.mem_range_self t
    rcases ht with ⟨u,hu⟩|⟨u,hu⟩
    · exact hu ▸ ih _ _ hp (fun i=>hF i.castSucc) u
    · exact hu ▸ hF _ u
theorem concat_map_paths {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (p : Fin (n+1) → X)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ)) (f : C(X,Y)) :
    (Path.concat p F).map f.continuous=
      Path.concat (fun i=>f (p i)) (fun i=>(F i).map f.continuous) := by
  induction n with
  | zero => simp only [Path.concat_zero];rfl
  | succ n ih =>
    erw [Path.concat_succ,Path.map_trans,Path.concat_succ,ih]
    rfl
end CurveComplex.Hyperbolic.PantsTheta
