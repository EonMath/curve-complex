import BoundaryBandSupport

open Set Topology CurveComplex
open LeanEval.Topology.ClassificationOfSurfaces

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry

/-- The actual boundary-edge triangle trapezoid with its full barycentric formula,
closed-height boundary test and complete closed range certificate. -/
theorem boundary_edge_triangle_trapezoid
    (V : Type) [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) (hfaces : ∀ τ ∈ F, τ.card = 3)
    (a b z : V) (ht : {a,b,z} ∈ F) (he : {a,b} ∈ boundaryEdges F)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < (1 : ℝ)/2) :
    ∃ E : C(↥(Icc (0 : ℝ) δ) × Interval, GeometricRealization V F),
      (∀ (r : ↥(Icc (0 : ℝ) δ)) (s : Interval) (w : V),
        (E (r,s)).val w =
          ((1 - (r : ℝ)) - (s : ℝ) * (1 - 5 * (r : ℝ) / 3)) *
            (if a = w then 1 else 0) +
          (2 * (r : ℝ) / 3 + (s : ℝ) * (1 - 5 * (r : ℝ) / 3)) *
            (if b = w then 1 else 0) +
          ((r : ℝ) / 3) * (if z = w then 1 else 0)) ∧
      IsEmbedding E ∧
      (∀ (r : ↥(Icc (0 : ℝ) δ)) (s : Interval),
        E (r,s) ∈ boundaryLocus F ↔ (r : ℝ) = 0) ∧
      (∀ q : GeometricRealization V F, q ∈ range E ↔
        q.val ∈ GeometricFace V {a,b,z} ∧
          0 ≤ 3 * q.val z ∧ 3 * q.val z ≤ δ ∧
          2 * q.val z ≤ q.val a ∧ 2 * q.val z ≤ q.val b) := by
  have hab : a ≠ b := by
    have hc := boundaryEdge_card (F := F) he
    by_contra h
    subst b
    simp at hc
  have haz : a ≠ z := by
    have hc := hfaces _ ht
    by_contra h
    subst z
    have hs : ({a,b,a} : Finset V) = {a,b} := by ext w; simp [or_comm]
    rw [hs] at hc
    have hec := boundaryEdge_card (F := F) he
    omega
  have hbz : b ≠ z := by
    have hc := hfaces _ ht
    by_contra h
    subst z
    have hs : ({a,b,b} : Finset V) = {a,b} := by ext w; simp
    rw [hs] at hc
    have hec := boundaryEdge_card (F := F) he
    omega
  let A (r s : ℝ) : ℝ := 1 - r - s * (1 - 5 * r / 3)
  let B (r s : ℝ) : ℝ := 2 * r / 3 + s * (1 - 5 * r / 3)
  let f (p : ↥(Icc (0 : ℝ) δ) × Interval) (w : V) : ℝ :=
    A p.1 p.2 * (if a = w then 1 else 0) +
    B p.1 p.2 * (if b = w then 1 else 0) +
    (p.1 : ℝ) / 3 * (if z = w then 1 else 0)
  have hweights (p : ↥(Icc (0 : ℝ) δ) × Interval) :
      0 ≤ A p.1 p.2 ∧ 0 ≤ B p.1 p.2 ∧ 0 ≤ (p.1 : ℝ) / 3 ∧
        A p.1 p.2 + B p.1 p.2 + (p.1 : ℝ) / 3 = 1 := by
    have hr0 : 0 ≤ (p.1 : ℝ) := p.1.property.1
    have hrδ : (p.1 : ℝ) ≤ δ := p.1.property.2
    have hs0 : 0 ≤ (p.2 : ℝ) := p.2.property.1
    have hs1 : (p.2 : ℝ) ≤ 1 := p.2.property.2
    have hr1 : (p.1 : ℝ) ≤ 1 := by linarith
    have hc : 0 ≤ 1 - 5 * (p.1 : ℝ) / 3 := by linarith
    have hsc : (p.2 : ℝ) * (1 - 5 * (p.1 : ℝ) / 3) ≤
        1 - 5 * (p.1 : ℝ) / 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hc]
    dsimp [A, B]
    constructor
    · linarith
    constructor
    · nlinarith [mul_nonneg hs0 hc]
    constructor
    · positivity
    · ring
  have hface (p : ↥(Icc (0 : ℝ) δ) × Interval) :
      f p ∈ GeometricFace V {a,b,z} := by
    have hw := hweights p
    constructor
    · constructor
      · intro w
        dsimp [f]
        split_ifs <;> nlinarith [hw.1, hw.2.1, hw.2.2.1]
      · dsimp [f]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp
        exact hw.2.2.2
    · intro w hw
      have hwa : a ≠ w := by
        intro h
        exact hw (by simp [h])
      have hwb : b ≠ w := by
        intro h
        exact hw (by simp [h])
      have hwz : z ≠ w := by
        intro h
        exact hw (by simp [h])
      simp [f, hwa, hwb, hwz]
  let E : C(↥(Icc (0 : ℝ) δ) × Interval, GeometricRealization V F) :=
    ⟨fun p => ⟨f p, (hface p).1, {a,b,z}, ht, (hface p).2⟩, by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro w
      dsimp [f, A, B]
      fun_prop⟩
  have hcoord (p : ↥(Icc (0 : ℝ) δ) × Interval) (w : V) :
      (E p).val w = f p w := rfl
  have hA (p : ↥(Icc (0 : ℝ) δ) × Interval) :
      (E p).val a = A p.1 p.2 := by
    rw [hcoord]
    simp [f, hab.symm, haz.symm]
  have hB (p : ↥(Icc (0 : ℝ) δ) × Interval) :
      (E p).val b = B p.1 p.2 := by
    rw [hcoord]
    simp [f, hab, hbz.symm]
  have hZ (p : ↥(Icc (0 : ℝ) δ) × Interval) :
      (E p).val z = (p.1 : ℝ) / 3 := by
    rw [hcoord]
    simp [f, haz, hbz]
  have hinj : Function.Injective E := by
    intro p q hpq
    have hzq := congrArg (fun x : GeometricRealization V F => x.val z) hpq
    rw [hZ, hZ] at hzq
    have hrval : (p.1 : ℝ) = (q.1 : ℝ) := by linarith
    have hr : p.1 = q.1 := Subtype.ext hrval
    have hbq := congrArg (fun x : GeometricRealization V F => x.val b) hpq
    rw [hB, hB] at hbq
    have hc : 0 < 1 - 5 * (p.1 : ℝ) / 3 := by
      have h := p.1.property.2
      linarith
    have hsval : (p.2 : ℝ) = (q.2 : ℝ) := by
      have hm : ((p.2 : ℝ) - (q.2 : ℝ)) *
          (1 - 5 * (p.1 : ℝ) / 3) = 0 := by
        dsimp [B] at hbq
        rw [← hrval] at hbq
        nlinarith
      rcases mul_eq_zero.mp hm with hm | hm
      · linarith
      · linarith
    exact Prod.ext hr (Subtype.ext hsval)
  have hembed : IsEmbedding E :=
    (E.continuous.isClosedEmbedding hinj).isEmbedding
  have hboundary (p : ↥(Icc (0 : ℝ) δ) × Interval) :
      E p ∈ boundaryLocus F ↔ (p.1 : ℝ) = 0 := by
    constructor
    · intro hp
      by_contra hr
      have hrpos : 0 < (p.1 : ℝ) := lt_of_le_of_ne p.1.property.1 (Ne.symm hr)
      have hc : 0 ≤ 1 - 5 * (p.1 : ℝ) / 3 := by
        have h := p.1.property.2
        linarith
      have hs0 : 0 ≤ (p.2 : ℝ) := p.2.property.1
      have hs1 : (p.2 : ℝ) ≤ 1 := p.2.property.2
      have hsc : (p.2 : ℝ) * (1 - 5 * (p.1 : ℝ) / 3) ≤
          1 - 5 * (p.1 : ℝ) / 3 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hc]
      have hapos : 0 < (E p).val a := by rw [hA]; dsimp [A]; linarith
      have hbpos : 0 < (E p).val b := by
        rw [hB]
        dsimp [B]
        nlinarith [mul_nonneg hs0 hc]
      have hzpos : 0 < (E p).val z := by rw [hZ]; linarith
      obtain ⟨e, he', hqe⟩ := hp
      have ha : a ∈ e := by
        by_contra h
        exact (not_le_of_gt hapos) (le_of_eq (hqe.2 a h))
      have hb : b ∈ e := by
        by_contra h
        exact (not_le_of_gt hbpos) (le_of_eq (hqe.2 b h))
      have hz : z ∈ e := by
        by_contra h
        exact (not_le_of_gt hzpos) (le_of_eq (hqe.2 z h))
      have hsub : ({a,b,z} : Finset V) ⊆ e := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with h | h | h <;> simpa [h] using (by first | exact ha | exact hb | exact hz)
      have hc3 : ({a,b,z} : Finset V).card = 3 := hfaces _ ht
      have hc2 := boundaryEdge_card (F := F) he'
      have hle := Finset.card_le_card hsub
      omega
    · intro hr
      refine ⟨{a,b}, he, ?_⟩
      constructor
      · exact (hface p).1
      · intro w hw
        have hwa : a ≠ w := by intro h; exact hw (by simp [h])
        have hwb : b ≠ w := by intro h; exact hw (by simp [h])
        rw [hcoord]
        simp [f, A, B, hr, hwa, hwb]
  have hface_sum (q : GeometricRealization V F)
      (hq : q.val ∈ GeometricFace V {a,b,z}) :
      q.val a + q.val b + q.val z = 1 := by
    have hs : (∑ w ∈ ({a,b,z} : Finset V), q.val w) =
        ∑ w : V, q.val w := by
      apply Finset.sum_subset (by simp)
      intro w _ hw
      exact hq.2 w hw
    have hs' := hs.trans hq.1.2
    simpa [hab, haz, hbz, add_assoc, add_comm, add_left_comm] using hs'
  have hrange (q : GeometricRealization V F) : q ∈ range E ↔
      q.val ∈ GeometricFace V {a,b,z} ∧
        0 ≤ 3 * q.val z ∧ 3 * q.val z ≤ δ ∧
        2 * q.val z ≤ q.val a ∧ 2 * q.val z ≤ q.val b := by
    constructor
    · rintro ⟨p, rfl⟩
      have hr0 := p.1.property.1
      have hrδ := p.1.property.2
      have hs0 := p.2.property.1
      have hs1 := p.2.property.2
      have hc : 0 ≤ 1 - 5 * (p.1 : ℝ) / 3 := by linarith
      have hsc : (p.2 : ℝ) * (1 - 5 * (p.1 : ℝ) / 3) ≤
          1 - 5 * (p.1 : ℝ) / 3 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hc]
      refine ⟨hface p, ?_, ?_, ?_, ?_⟩
      · rw [hZ]; linarith
      · rw [hZ]; linarith
      · rw [hZ, hA]; dsimp [A]; linarith
      · rw [hZ, hB]; dsimp [B]; nlinarith [mul_nonneg hs0 hc]
    · rintro ⟨hqface, hr0, hrδ, hqa, hqb⟩
      have hsum := hface_sum q hqface
      let r : ↥(Icc (0 : ℝ) δ) := ⟨3 * q.val z, ⟨hr0, hrδ⟩⟩
      have hden : 0 < 1 - 5 * q.val z := by linarith
      let s : Interval := ⟨(q.val b - 2 * q.val z) / (1 - 5 * q.val z), by
        constructor
        · exact div_nonneg (by linarith) (le_of_lt hden)
        · apply (div_le_iff₀ hden).2
          linarith⟩
      have hsmul : (s : ℝ) * (1 - 5 * q.val z) = q.val b - 2 * q.val z := by
        change (q.val b - 2 * q.val z) / (1 - 5 * q.val z) *
          (1 - 5 * q.val z) = _
        exact div_mul_cancel₀ _ (ne_of_gt hden)
      refine ⟨(r,s), ?_⟩
      apply Subtype.ext
      funext w
      by_cases hwa : w = a
      · subst w
        rw [hA]
        change 1 - 3 * q.val z - (s : ℝ) * (1 - 5 * (3 * q.val z) / 3) = q.val a
        have hc : 1 - 5 * (3 * q.val z) / 3 = 1 - 5 * q.val z := by ring
        rw [hc, hsmul]
        linarith [hsum]
      by_cases hwb : w = b
      · subst w
        rw [hB]
        change 2 * (3 * q.val z) / 3 + (s : ℝ) *
          (1 - 5 * (3 * q.val z) / 3) = q.val b
        have hc : 1 - 5 * (3 * q.val z) / 3 = 1 - 5 * q.val z := by ring
        rw [hc, hsmul]
        ring
      by_cases hwz : w = z
      · subst w
        rw [hZ]
        dsimp [r]
        ring
      · rw [hcoord]
        have hw : w ∉ ({a,b,z} : Finset V) := by simp [hwa,hwb,hwz]
        rw [hqface.2 w hw]
        simp [f, Ne.symm hwa, Ne.symm hwb, Ne.symm hwz]
  refine ⟨E, ?_, hembed, ?_, hrange⟩
  · intro r s w
    exact hcoord (r,s) w
  · intro r s
    exact hboundary (r,s)

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry
