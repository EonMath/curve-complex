import CurveComplexGenusTwo.Dictionary.BranchedCover
import Mathlib.Data.Finset.Preimage
open Set Topology
namespace CurveComplex.BranchedDoubleCover
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

private theorem separating_interval (x y : ℝ) (hne : x ≠ y)
    (hx : -1 < x ∧ x < 1) (hy : -1 < y ∧ y < 1) :
    ∃ a b : ℝ, -1 < a ∧ a < b ∧ b < 1 ∧
      x ∉ Icc a b ∧ y ∉ Icc a b ∧
      ((x < a ∧ b < y) ∨ (y < a ∧ b < x)) := by
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨(3*x+y)/4,(x+3*y)/4,by linarith,by linarith,by linarith,?_,?_,?_⟩
    · simp only [Set.mem_Icc,not_and_or]
      left; linarith
    · simp only [Set.mem_Icc,not_and_or]
      right; linarith
    · exact Or.inl ⟨by linarith,by linarith⟩
  · refine ⟨(3*y+x)/4,(y+3*x)/4,by linarith,by linarith,by linarith,?_,?_,?_⟩
    · simp only [Set.mem_Icc,not_and_or]
      right; linarith
    · simp only [Set.mem_Icc,not_and_or]
      left; linarith
    · exact Or.inr ⟨by linarith,by linarith⟩

/-- The actual two interior marks in a square chart determine a positive-width
branch-free corridor across that chart. No corridor certificate is assumed. -/
theorem two_mark_square_has_branch_free_corridor
    (q : BranchedDoubleCover E S)
    (f : C(Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,S)) (hf : IsEmbedding f)
    (hboundary : ∀ z, z.val ∈ frontier (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) →
      f z ∉ q.branch)
    (hcount : (by classical exact
      (q.branch.filter (fun b => b ∈ f '' {z | z.val ∈
        interior (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)})).card = 2)) :
    ∃ a b c d : ℝ, a < b ∧ c < d ∧
      (Icc a b ×ˢ Icc c d) ⊆ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ∧
      ((c = -1 ∧ d = 1 ∧ -1 < a ∧ b < 1) ∨
       (a = -1 ∧ b = 1 ∧ -1 < c ∧ d < 1)) ∧
      ∃ p₀ p₁ : Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
      (∀ z, f z ∈ q.branch ↔ z = p₀ ∨ z = p₁) ∧
      (((p₀.val.1 < a ∧ b < p₁.val.1) ∨ (p₁.val.1 < a ∧ b < p₀.val.1)) ∨
       ((p₀.val.2 < c ∧ d < p₁.val.2) ∨ (p₁.val.2 < c ∧ d < p₀.val.2))) ∧
      ∀ z : Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
        z.val ∈ Icc a b ×ˢ Icc c d → f z ∉ q.branch := by
  classical
  let K : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  have hKclosed : IsClosed K := isClosed_Icc.prod isClosed_Icc
  have hInterior (z : K) (hz : f z ∈ q.branch) : z.val ∈ interior K := by
    by_contra hn
    apply hboundary z _ hz
    exact ⟨hKclosed.closure_eq.symm ▸ z.property,hn⟩
  let s := q.branch.preimage f hf.injective.injOn
  have hRange : q.branch.filter (fun b => b ∈ Set.range f) =
      q.branch.filter (fun b => b ∈ f '' {z : K | z.val ∈ interior K}) := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hb,z,rfl⟩
      exact ⟨hb,z,hInterior z hb,rfl⟩
    · rintro ⟨hb,z,hz,rfl⟩
      exact ⟨hb,z,rfl⟩
  have hs : s.card = 2 := by
    rw [Finset.card_preimage,hRange]
    exact hcount
  have hiff (z : K) : f z ∈ q.branch ↔ z ∈ s := by simp [s]
  obtain ⟨p,q₀,hpq,hsEq⟩ := Finset.card_eq_two.mp hs
  have hp : p.val ∈ interior K := hInterior p ((hiff p).mpr (by rw [hsEq]; simp))
  have hq : q₀.val ∈ interior K := hInterior q₀ ((hiff q₀).mpr (by rw [hsEq]; simp))
  have hpBounds : (-1 < p.val.1 ∧ p.val.1 < 1) ∧ (-1 < p.val.2 ∧ p.val.2 < 1) := by
    simpa only [K,interior_prod_eq,interior_Icc,Set.mem_prod,Set.mem_Ioo] using hp
  have hqBounds : (-1 < q₀.val.1 ∧ q₀.val.1 < 1) ∧ (-1 < q₀.val.2 ∧ q₀.val.2 < 1) := by
    simpa only [K,interior_prod_eq,interior_Icc,Set.mem_prod,Set.mem_Ioo] using hq
  have hmarks (z : K) (hz : f z ∈ q.branch) : z=p ∨ z=q₀ := by
    have hh := (hiff z).mp hz
    rw [hsEq] at hh
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have hmarkiff (z : K) : f z ∈ q.branch ↔ z=p ∨ z=q₀ := by
    rw [hiff,hsEq]
    simp only [Finset.mem_insert,Finset.mem_singleton]
  by_cases hx : p.val.1 ≠ q₀.val.1
  · obtain ⟨a,b,ha,hab,hb,hpa,hqa,hsep⟩ := separating_interval _ _ hx hpBounds.1 hqBounds.1
    refine ⟨a,b,-1,1,hab,by norm_num,?_,Or.inl ⟨rfl,rfl,ha,hb⟩,
      p,q₀,hmarkiff,Or.inl hsep,?_⟩
    · rintro z ⟨hzx,hzy⟩
      exact ⟨⟨ha.le.trans hzx.1,hzx.2.trans hb.le⟩,hzy⟩
    · intro z hz hbranch
      rcases hmarks z hbranch with rfl | rfl
      · exact hpa hz.1
      · exact hqa hz.1
  · have hy : p.val.2 ≠ q₀.val.2 := by
      intro he
      apply hpq
      exact Subtype.ext (Prod.ext (not_ne_iff.mp hx) he)
    obtain ⟨c,d,hc,hcd,hd,hpc,hqc,hsep⟩ := separating_interval _ _ hy hpBounds.2 hqBounds.2
    refine ⟨-1,1,c,d,by norm_num,hcd,?_,Or.inr ⟨rfl,rfl,hc,hd⟩,
      p,q₀,hmarkiff,Or.inr hsep,?_⟩
    · rintro z ⟨hzx,hzy⟩
      exact ⟨hzx,⟨hc.le.trans hzy.1,hzy.2.trans hd.le⟩⟩
    · intro z hz hbranch
      rcases hmarks z hbranch with rfl | rfl
      · exact hpc hz.2
      · exact hqc hz.2

end CurveComplex.BranchedDoubleCover
#print axioms CurveComplex.BranchedDoubleCover.two_mark_square_has_branch_free_corridor
