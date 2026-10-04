import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualOriginalOuterCollarGluingLocal

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]
set_option maxHeartbeats 3000000

-- Consume the DERIVED collar-side alternative to select a genuine exterior half.
example (M : HyperellipticModel E S) (U : Set E)
    (e : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (he : Topology.IsOpenEmbedding e)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1)
    (hchoice : (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∉ U) ∨
      (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∉ U)) :
    ∃ L : C(Circle × Interval,E), Topology.IsEmbedding L ∧
      (∀ z, L (z,0) = e (⟨0,by norm_num⟩,z)) ∧
      (∀ (z : Circle) (u : Interval), 0 < (u:ℝ) → L (z,u) ∉ U) ∧
      Set.range L ⊆ e '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε} := by
  audit_main14_base3
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    obtain ⟨σ,hσ,hout⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∀ w : Set.Ioo (-1:ℝ) 1, 0 < σ*(w:ℝ) → σ*(w:ℝ) < ε → ∀ z, e (w,z) ∉ U := by
      rcases hchoice with hp | hn
      · exact ⟨1,Or.inl rfl,fun w h0 h1 z => hp w (by simpa using h0) (by simpa using h1) z⟩
      · refine ⟨-1,Or.inr rfl,?_⟩
        intro w h0 h1 z
        exact hn w (by linarith) (by linarith) z
    let q : Interval → Set.Ioo (-1:ℝ) 1 := fun u =>
      ⟨σ*ε/2*(u:ℝ),by rcases hσ with hs | hs <;> rw [hs] <;>
        constructor <;> nlinarith [u.property.1,u.property.2]⟩
    have hqc : Continuous q := by dsimp [q]; fun_prop
    have hqi : Function.Injective q := by
      intro u v h
      apply Subtype.ext
      have hh := congrArg Subtype.val h
      change σ*ε/2*(u:ℝ) = σ*ε/2*(v:ℝ) at hh
      rcases hσ with hs | hs <;> rw [hs] at hh <;> nlinarith
    have hq0 : q 0 = ⟨0,by norm_num⟩ := by apply Subtype.ext; dsimp [q]; ring
    have hqabs (u : Interval) : |(q u:ℝ)| < ε := by
      rw [abs_lt]
      dsimp [q]
      rcases hσ with hs | hs <;> rw [hs] <;> constructor <;>
        nlinarith [u.property.1,u.property.2]
    let L : C(Circle × Interval,E) := ⟨fun p => e (q p.2,p.1),
      e.continuous.comp ((hqc.comp continuous_snd).prodMk continuous_fst)⟩
    have hLi : Function.Injective L := by
      intro p w h
      have hh := he.injective h
      apply Prod.ext
      · have hz := congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => p.2) hh
        exact hz
      · exact hqi (congrArg Prod.fst hh)
    refine ⟨L,(L.continuous.isClosedEmbedding hLi).isEmbedding,?_,?_,?_⟩
    · intro z
      change e (q 0,z) = _
      rw [hq0]
    · intro z u hu
      apply hout (q u)
      · dsimp [q]
        rcases hσ with hs | hs <;> rw [hs] <;> nlinarith
      · dsimp [q]
        rcases hσ with hs | hs <;> rw [hs] <;> nlinarith [u.property.2]
    · rintro x ⟨p,rfl⟩
      exact ⟨(q p.2,p.1),hqabs p.2,rfl⟩

end CurveComplex.HyperellipticModel
