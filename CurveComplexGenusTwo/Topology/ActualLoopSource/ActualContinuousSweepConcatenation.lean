import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Topology.Path
import Mathlib.Topology.CompactOpen

namespace CurveComplex
open Set
noncomputable section

/-- Actual concatenation of two continuous sweeps, with every slice literally
one of the input slices. This retains embeddedness and endpoint constraints. -/
theorem actual_continuous_sweep_concatenation {S : Type} [TopologicalSpace S]
    (F G : C(Interval × Interval,S)) (hmatch : ∀ t, F (1,t)=G (0,t)) :
    ∃ K : C(Interval × Interval,S),
      (∀ t, K (0,t)=F (0,t)) ∧ (∀ t, K (1,t)=G (1,t)) ∧
      ∀ τ, (∃ σ, ∀ t, K (τ,t)=F (σ,t)) ∨ (∃ σ, ∀ t, K (τ,t)=G (σ,t)) := by
  let p : Path (F.curry 0) (F.curry 1) :=
    { toContinuousMap := F.curry, source' := rfl, target' := rfl }
  let q : Path (F.curry 1) (G.curry 1) :=
    { toContinuousMap := G.curry, source' := ContinuousMap.ext (fun t => (hmatch t).symm), target' := rfl }
  let K : C(Interval × Interval,S) := (p.trans q).toContinuousMap.uncurry
  refine ⟨K,?_,?_,?_⟩
  · intro t
    change (p.trans q) 0 t = F (0,t)
    simp [p]
  · intro t
    change (p.trans q) 1 t = G (1,t)
    simp
  · intro τ
    have h := Path.trans_apply p q τ
    split at h
    · rename_i ht
      refine Or.inl ⟨⟨2*τ.val,by constructor <;> nlinarith [τ.property.1]⟩,?_⟩
      intro t
      exact congrArg (fun f : C(Interval,S) => f t) h
    · rename_i ht
      refine Or.inr ⟨⟨2*τ.val-1,by constructor <;> nlinarith [τ.property.2]⟩,?_⟩
      intro t
      exact congrArg (fun f : C(Interval,S) => f t) h
end
end CurveComplex
