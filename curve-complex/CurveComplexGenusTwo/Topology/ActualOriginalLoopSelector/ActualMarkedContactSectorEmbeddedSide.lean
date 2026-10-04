import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualMarkedContactTraceEmbeddedStraightening
import Mathlib.Topology.Homotopy.Basic
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- An ACTUAL filled corner sector is continued by a constructed trace
straightening, producing a marked-relative square with embedded old-loop
terminal side. No homotopy or side-straightening certificate is supplied. -/
theorem actual_marked_contact_sector_embedded_side
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (U : Set S) (V : Set Plane) (e : U ≃ₜ V)
    (hmarks : Disjoint U ((M.cover.branch : Set S) \ {a.val.map 0}))
    (haxis : ∀ q : U,q.val ∈ a.val.image ↔ (e q).val 1=0)
    (hp : a.val.map 0 ∈ U) (hezero : (e ⟨a.val.map 0,hp⟩).val=0)
    (F : C(unitInterval × Icc (0:ℝ) (1/2),S))
    (hFU : ∀ z,F z ∈ U)
    (hbase : ∀ σ,F (σ,⟨0,le_rfl,by norm_num⟩)=a.val.map 0)
    (hpositive : ∀ z,0<z.2.val → F z ∉ (M.cover.branch : Set S))
    (hold : ∀ t,F (1,t) ∈ a.val.image) :
    ∃ Q : C(unitInterval × Icc (0:ℝ) (1/2),S),
      (∀ t,Q (0,t)=F (0,t)) ∧
      (∀ σ,Q (σ,⟨0,le_rfl,by norm_num⟩)=a.val.map 0) ∧
      (∀ z,Q z ∈ U) ∧
      (∀ z,0<z.2.val → Q z ∉ (M.cover.branch : Set S)) ∧
      (∀ t,Q (1,t) ∈ a.val.image) ∧ IsEmbedding (fun t => Q (1,t)) ∧
      (∀ t,Q (1,t) ∈ range (fun u => F (1,u))) ∧
      Q (1,⟨1/2,by norm_num,le_rfl⟩)=F (1,⟨1/2,by norm_num,le_rfl⟩) := by
  let T : C(Icc (0:ℝ) (1/2),S) := ⟨fun t => F (1,t),by fun_prop⟩
  obtain ⟨G,hG0,hGbase,hGend,hGrange,hGold,hGmarks,_,hGembed⟩ :=
    actual_marked_contact_trace_embedded_straightening M a U V e hmarks haxis hp hezero
      T (fun t => hFU (1,t)) (hbase 1) hold
      (fun t ht he => hpositive (1,t) ht (he.symm ▸ a.val.start_marked))
  have hGU (z) : G z ∈ U := by
    obtain ⟨t,ht⟩ := hGrange z
    exact ht ▸ hFU (1,t)
  let f0 : C(Icc (0:ℝ) (1/2),S) := ⟨fun t => F (0,t),by fun_prop⟩
  let f1 : C(Icc (0:ℝ) (1/2),S) := T
  let f2 : C(Icc (0:ℝ) (1/2),S) := ⟨fun t => G (1,t),by fun_prop⟩
  let HF : f0.Homotopy f1 := {
    toContinuousMap := F
    map_zero_left := fun _ => rfl
    map_one_left := fun _ => rfl }
  let HG : f1.Homotopy f2 := {
    toContinuousMap := G
    map_zero_left := hG0
    map_one_left := fun _ => rfl }
  let Q := (HF.trans HG).toContinuousMap
  have hQ0 (t) : Q (0,t)=F (0,t) := (HF.trans HG).apply_zero t
  have hQ1 (t) : Q (1,t)=G (1,t) := (HF.trans HG).apply_one t
  have hQcase (z) : (∃ σ,Q z=F (σ,z.2)) ∨ (∃ σ,Q z=G (σ,z.2)) := by
    change (∃ σ,(HF.trans HG) z=F (σ,z.2)) ∨ (∃ σ,(HF.trans HG) z=G (σ,z.2))
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · left; exact ⟨_,rfl⟩
    · right; exact ⟨_,rfl⟩
  refine ⟨Q,hQ0,?_,?_,?_,?_,?_,?_,?_⟩
  · intro σ
    rcases hQcase (σ,⟨0,le_rfl,by norm_num⟩) with ⟨τ,hτ⟩ | ⟨τ,hτ⟩
    · exact hτ.trans (hbase τ)
    · exact hτ.trans (hGbase τ)
  · intro z
    rcases hQcase z with ⟨τ,hτ⟩ | ⟨τ,hτ⟩
    · exact hτ.symm ▸ hFU (τ,z.2)
    · exact hτ.symm ▸ hGU (τ,z.2)
  · intro z ht
    rcases hQcase z with ⟨τ,hτ⟩ | ⟨τ,hτ⟩
    · exact hτ.symm ▸ hpositive (τ,z.2) ht
    · exact hτ.symm ▸ hGmarks (τ,z.2) ht
  · intro t
    exact (hQ1 t).symm ▸ hGold (1,t)
  · have he : (fun t => Q (1,t))=(fun t => G (1,t)) := funext hQ1
    rw [he]; exact hGembed
  · intro t
    exact (hQ1 t).symm ▸ hGrange (1,t)
  · exact (hQ1 _).trans (hGend 1)
end CurveComplex.HyperellipticModel
