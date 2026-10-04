import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort

/-!
Exact geometric-intersection bridge for source Lemma 7.5.

This imports a source-identical local port of the four candidate definitions
against the proved master `Foundations.Definitions`.
-/

namespace CurveComplex

theorem crossesAt_symm_of_chart {S : Type*} [TopologicalSpace S]
    {a b : Curve S} {p : S} (hcross : CrossesAt a b p) :
    CrossesAt b a p := by
  rcases hcross with ⟨U, V, hpU, h, hU, hV, hzero, haxes⟩
  let swap : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.prodComm ℝ ℝ
  let W : Set (ℝ × ℝ) := swap '' V
  let hs : V ≃ₜ W := Homeomorph.image swap V
  let h' : U ≃ₜ W := h.trans hs
  refine ⟨U, W, hpU, h', hU, ?_, ?_, ?_⟩
  · exact swap.isOpenMap V hV
  · change swap (h ⟨p, hpU⟩) = (0, 0)
    simpa [swap] using congrArg swap hzero
  · intro x hx
    rcases haxes x hx with ⟨ha, hb⟩
    constructor
    · change x ∈ b.image ↔ (swap (h ⟨x, hx⟩)).1 = 0
      simpa [swap] using hb
    · change x ∈ a.image ↔ (swap (h ⟨x, hx⟩)).2 = 0
      simpa [swap] using ha

theorem transverse_symm_of_chart {S : Type*} [TopologicalSpace S]
    {a b : Curve S} (h : Transverse a b) : Transverse b a := by
  refine ⟨?_, ?_⟩
  · simpa [Set.inter_comm] using h.1
  · intro p hp
    exact crossesAt_symm_of_chart (h.2 p (by simpa [Set.inter_comm] using hp))

theorem intersectionCounts_symm_of_chart {S : Type*} [TopologicalSpace S]
    (α β : Vertex S) : intersectionCounts α β = intersectionCounts β α := by
  ext n
  constructor
  · rintro ⟨a, b, ha, hb, htrans, hn⟩
    refine ⟨b, a, hb, ha, transverse_symm_of_chart htrans, ?_⟩
    simpa [Set.inter_comm] using hn
  · rintro ⟨b, a, hb, ha, htrans, hn⟩
    refine ⟨a, b, ha, hb, transverse_symm_of_chart htrans, ?_⟩
    simpa [Set.inter_comm] using hn

theorem geometricIntersection_symm_of_chart {S : Type*} [TopologicalSpace S]
    (α β : Vertex S) :
    geometricIntersection α β = geometricIntersection β α := by
  unfold geometricIntersection
  rw [intersectionCounts_symm_of_chart]

/-- Disjoint essential representatives have geometric intersection zero.
The empty intersection is already a transverse representative pair. -/
theorem geometricIntersection_eq_zero_of_disjoint_representatives
    {S : Type*} [TopologicalSpace S]
    (a c : EssentialCurve S)
    (hdisj : Disjoint a.val.image c.val.image) :
    geometricIntersection
      (Quotient.mk (essentialCurveSetoid S) a)
      (Quotient.mk (essentialCurveSetoid S) c) = 0 := by
  have hempty : a.val.image ∩ c.val.image = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hdisj
  have htrans : Transverse a.val c.val := by
    constructor
    · rw [hempty]
      exact Set.finite_empty
    · intro p hp
      rw [hempty] at hp
      simp at hp
  have hzero : 0 ∈ intersectionCounts
      (Quotient.mk (essentialCurveSetoid S) a)
      (Quotient.mk (essentialCurveSetoid S) c) := by
    refine ⟨a, c, rfl, rfl, htrans, ?_⟩
    simp [hempty]
  have hle : geometricIntersection
      (Quotient.mk (essentialCurveSetoid S) a)
      (Quotient.mk (essentialCurveSetoid S) c) ≤ 0 :=
    Nat.sInf_le hzero
  exact Nat.eq_zero_of_le_zero hle

/-- Once transverse representatives exist, intersection number one is attained
by an actual pair with exactly one crossing. -/
theorem geometricIntersection_one_has_transverse_representatives
    {S : Type*} [TopologicalSpace S]
    (α β : Vertex S)
    (hne : (intersectionCounts α β).Nonempty)
    (hone : geometricIntersection α β = 1) :
    ∃ a b : EssentialCurve S,
      Quotient.mk (essentialCurveSetoid S) a = α ∧
      Quotient.mk (essentialCurveSetoid S) b = β ∧
      ∃ h : Transverse a.val b.val,
        h.1.toFinset.card = 1 := by
  have hmem : 1 ∈ intersectionCounts α β := by
    rw [← hone]
    exact Nat.sInf_mem hne
  obtain ⟨a, b, ha, hb, htrans, hcard⟩ := hmem
  exact ⟨a, b, ha, hb, htrans, hcard.symm⟩

/-- A transverse representative pair with count one has one actual crossing
point, equipped with the local coordinate-axis chart needed for thickening. -/
theorem unique_crossing_chart_of_count_one
    {S : Type*} [TopologicalSpace S]
    (a b : Curve S) (h : Transverse a b)
    (hcard : h.1.toFinset.card = 1) :
    ∃ p : S,
      p ∈ a.image ∩ b.image ∧
      CrossesAt a b p ∧
      ∀ q ∈ a.image ∩ b.image, q = p := by
  classical
  obtain ⟨p, hp, hunique⟩ :=
    Finset.card_eq_one_iff_existsUnique.mp hcard
  have hp' : p ∈ a.image ∩ b.image := by
    simpa using hp
  refine ⟨p, hp', h.2 p hp', ?_⟩
  intro q hq
  exact hunique q (by simpa using hq)

/-- Every topological crossing chart contains a closed Euclidean disk around
the crossing. This is the local disk to be glued to bands along the two loops
in a regular-neighborhood construction. -/
theorem exists_closed_disk_in_crossing_chart
    {S : Type*} [TopologicalSpace S]
    {a b : Curve S} {p : S} (hcross : CrossesAt a b p) :
    ∃ (U : Set S) (V : Set (ℝ × ℝ))
      (hp : p ∈ U) (h : U ≃ₜ V),
      IsOpen U ∧ IsOpen V ∧
      ((h ⟨p, hp⟩ : V) : ℝ × ℝ) = (0, 0) ∧
      (∀ (x : S) (hx : x ∈ U),
        (x ∈ a.image ↔ ((h ⟨x, hx⟩ : V) : ℝ × ℝ).1 = 0) ∧
        (x ∈ b.image ↔ ((h ⟨x, hx⟩ : V) : ℝ × ℝ).2 = 0)) ∧
      ∃ ε : ℝ, 0 < ε ∧
        Metric.closedBall ((0, 0) : ℝ × ℝ) ε ⊆ V := by
  rcases hcross with ⟨U, V, hp, h, hU, hV, hzero, haxes⟩
  have h0 : ((0, 0) : ℝ × ℝ) ∈ V := by
    have hh := (h ⟨p, hp⟩).property
    simpa [hzero] using hh
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV ((0, 0) : ℝ × ℝ) h0
  refine ⟨U, V, hp, h, hU, hV, hzero, haxes, δ / 2, by linarith, ?_⟩
  exact (Metric.closedBall_subset_ball (by linarith)).trans hball

end CurveComplex

#print axioms CurveComplex.crossesAt_symm_of_chart
#print axioms CurveComplex.transverse_symm_of_chart
#print axioms CurveComplex.intersectionCounts_symm_of_chart
#print axioms CurveComplex.geometricIntersection_symm_of_chart
#print axioms CurveComplex.geometricIntersection_eq_zero_of_disjoint_representatives
#print axioms CurveComplex.geometricIntersection_one_has_transverse_representatives
#print axioms CurveComplex.unique_crossing_chart_of_count_one
#print axioms CurveComplex.exists_closed_disk_in_crossing_chart
