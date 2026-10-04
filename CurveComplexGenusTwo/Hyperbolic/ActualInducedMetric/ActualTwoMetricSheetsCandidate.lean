import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCoverLocalCharts

namespace CurveComplex
open Set Topology

set_option maxHeartbeats 1000000 in
theorem BranchedDoubleCover.actual_two_metric_sheets {E S B : Type}
    [TopologicalSpace E] [TopologicalSpace S] [T2Space S] [MetricSpace B]
    (m : MetricSpace E) (ht : m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace E›)
    (q : BranchedDoubleCover E S) (identify : S ≃ₜ B)
    (hlocal : ∀ x : E, x ∉ q.ramification → ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, m.dist y z = dist (identify (q.projection y)) (identify (q.projection z)))
    (b : S) (hb : b ∉ (q.branch : Set S)) :
    ∃ U : Set S, IsOpen U ∧ b ∈ U ∧ U ⊆ (q.branch : Set S)ᶜ ∧
      ∃ e₁ e₂ : OpenPartialHomeomorph E S,
        e₁.target = U ∧ e₂.target = U ∧ Disjoint e₁.source e₂.source ∧
        q.projection ⁻¹' U = e₁.source ∪ e₂.source ∧
        (∀ y : E, e₁ y = q.projection y) ∧ (∀ y : E, e₂ y = q.projection y) ∧
        (∀ y ∈ e₁.source, ∀ z ∈ e₁.source, m.dist y z = dist (identify (e₁ y)) (identify (e₁ z))) ∧
        (∀ y ∈ e₂.source, ∀ z ∈ e₂.source, m.dist y z = dist (identify (e₂ y)) (identify (e₂ z))) := by
  cases ht
  letI : MetricSpace E := m
  obtain ⟨x, hxb⟩ := q.projection_surjective b
  have hx : x ∉ q.ramification := by simpa [BranchedDoubleCover.ramification, hxb] using hb
  have hdx : q.deck x ∉ q.ramification := by
    simpa [BranchedDoubleCover.ramification, q.projection_deck, hxb] using hb
  have hne : x ≠ q.deck x := by
    intro h
    have hfixed := (q.fixed_iff_branch x).mp h.symm
    rw [hxb] at hfixed
    exact hb hfixed
  obtain ⟨A, C, hA, hC, hxA, hdxC, hAC⟩ := t2_separation hne
  obtain ⟨W₁, hW₁, hxW₁, hdist₁⟩ := hlocal x hx
  obtain ⟨W₂, hW₂, hdxW₂, hdist₂⟩ := hlocal (q.deck x) hdx
  obtain ⟨c₁, hxc₁, hc₁, _⟩ := q.actual_unramified_chart x hx
  obtain ⟨c₂, hdxc₂, hc₂, _⟩ := q.actual_unramified_chart (q.deck x) hdx
  let d₁ := c₁.restrOpen (W₁ ∩ A) (hW₁.inter hA)
  let d₂ := c₂.restrOpen (W₂ ∩ C) (hW₂.inter hC)
  have hxd₁ : x ∈ d₁.source := ⟨hxc₁, hxW₁, hxA⟩
  have hdxd₂ : q.deck x ∈ d₂.source := ⟨hdxc₂, hdxW₂, hdxC⟩
  have hd₁ (y : E) : d₁ y = q.projection y := hc₁ y
  have hd₂ (y : E) : d₂ y = q.projection y := hc₂ y
  let U : Set S := d₁.target ∩ d₂.target ∩ (q.branch : Set S)ᶜ
  have hU : IsOpen U := (d₁.open_target.inter d₂.open_target).inter q.branch.finite_toSet.isClosed.isOpen_compl
  have hbU : b ∈ U := by
    refine ⟨⟨?_, ?_⟩, hb⟩
    · simpa only [hd₁, hxb] using d₁.map_source hxd₁
    · simpa only [hd₂, q.projection_deck, hxb] using d₂.map_source hdxd₂
  let e₁ := (d₁.symm.restrOpen U hU).symm
  let e₂ := (d₂.symm.restrOpen U hU).symm
  have ht₁ : e₁.target = U := by
    change d₁.target ∩ U = U
    exact inter_eq_right.mpr fun y hy => hy.1.1
  have ht₂ : e₂.target = U := by
    change d₂.target ∩ U = U
    exact inter_eq_right.mpr fun y hy => hy.1.2
  have hs₁ : e₁.source ⊆ d₁.source := inter_subset_left
  have hs₂ : e₂.source ⊆ d₂.source := inter_subset_left
  have he₁ (y : E) : e₁ y = q.projection y := hd₁ y
  have he₂ (y : E) : e₂ y = q.projection y := hd₂ y
  have hdisj : Disjoint e₁.source e₂.source := by
    apply hAC.mono
    · intro y hy; exact (hs₁ hy).2.2
    · intro y hy; exact (hs₂ hy).2.2
  have hpre : q.projection ⁻¹' U = e₁.source ∪ e₂.source := by
    ext y
    constructor
    · intro hy
      have hyt₁ : q.projection y ∈ e₁.target := ht₁.symm ▸ hy
      have hyt₂ : q.projection y ∈ e₂.target := ht₂.symm ▸ hy
      let z₁ := e₁.symm (q.projection y)
      let z₂ := e₂.symm (q.projection y)
      have hz₁ : z₁ ∈ e₁.source := e₁.map_target hyt₁
      have hz₂ : z₂ ∈ e₂.source := e₂.map_target hyt₂
      have hp₁ : q.projection z₁ = q.projection y := by
        rw [← he₁]; exact e₁.right_inv hyt₁
      have hp₂ : q.projection z₂ = q.projection y := by
        rw [← he₂]; exact e₂.right_inv hyt₂
      have hzz : z₂ = q.deck z₁ := by
        rcases (q.fiber_pair z₁ z₂).mp (hp₁.trans hp₂.symm) with h | h
        · exact (disjoint_left.mp hdisj hz₁ (h ▸ hz₂)).elim
        · exact h
      rcases (q.fiber_pair z₁ y).mp hp₁ with h | h
      · exact Or.inl (h.symm ▸ hz₁)
      · exact Or.inr ((h.trans hzz.symm).symm ▸ hz₂)
    · rintro (hy | hy)
      · have h := e₁.map_source hy; rwa [ht₁, he₁] at h
      · have h := e₂.map_source hy; rwa [ht₂, he₂] at h
  refine ⟨U, hU, hbU, fun y hy => hy.2, e₁, e₂, ht₁, ht₂, hdisj, hpre, he₁, he₂, ?_, ?_⟩
  · intro y hy z hz
    rw [he₁, he₁]
    exact hdist₁ y (hs₁ hy).2.1 z (hs₁ hz).2.1
  · intro y hy z hz
    rw [he₂, he₂]
    exact hdist₂ y (hs₂ hy).2.1 z (hs₂ hz).2.1

end CurveComplex
