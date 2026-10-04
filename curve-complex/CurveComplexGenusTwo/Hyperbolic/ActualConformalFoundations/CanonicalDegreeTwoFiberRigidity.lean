import Mathlib.Topology.Perfect
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Set.Card

open Set

theorem canonical_degree_two_fiber_rigidity {E B : Type*} [TopologicalSpace E] [T2Space E] [PerfectSpace E]
    (κ : E → B) (f g : E ≃ₜ E)
    (hf : ∀ x, κ (f x) = κ x) (hg : ∀ x, κ (g x) = κ x)
    (hfFix : {x : E | f x = x}.Finite)
    (hgFix : {x : E | g x = x}.Finite)
    (hfinite : ∀ b, (κ ⁻¹' {b}).Finite)
    (hdegree : ∀ b, (κ ⁻¹' {b}).ncard ≤ 2) : f = g := by
  classical
  have hdense : ∀ (s : Set E), s.Finite → Dense sᶜ := by
    intro s hs
    induction s, hs using Set.Finite.induction_on with
    | empty => simpa using (dense_univ : Dense (Set.univ : Set E))
    | @insert a s ha hs ih =>
      have he : (insert a s)ᶜ = sᶜ ∩ {a}ᶜ := by
        ext t
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_inter_iff,
          Set.mem_singleton_iff]
        tauto
      rw [he]
      exact ih.inter_of_isOpen_right (dense_compl_singleton a) isOpen_compl_singleton
  have heq : Set.EqOn (fun x => f x) (fun x => g x)
      ({x : E | f x = x} ∪ {x : E | g x = x})ᶜ := by
    intro x hx
    have hfx : f x ≠ x := fun h => hx (Or.inl h)
    have hgx : g x ≠ x := fun h => hx (Or.inr h)
    by_contra hfg
    have hthree : 2 < (κ ⁻¹' {κ x}).ncard :=
      (Set.two_lt_ncard_iff (hfinite (κ x))).2
        ⟨x, f x, g x, rfl, hf x, hg x, hfx.symm, hgx.symm, hfg⟩
    exact (not_lt_of_ge (hdegree (κ x))) hthree
  apply Homeomorph.ext
  intro x
  apply heq.closure f.continuous g.continuous
  rw [(hdense _ (hfFix.union hgFix)).closure_eq]
  exact Set.mem_univ x
