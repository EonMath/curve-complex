import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedGraphStraightening

open Set Topology Schoenflies CurveComplex

/-- The source-derived graph target avoids the full puncture orbit. Its height
is not assumed to avoid punctures, and no support-avoidance inference is used. -/
theorem actual_periodic_graph_adapted_target_avoids_marks
    (G : C(ℝ, Plane)) (T : ℝ) (p : Plane)
    (hFirst : ∀ x, G x 0 = x)
    (hPeriod : ∀ (k : ℤ) x,
      G (x + (k : ℝ) * T) = G x + Plane.mk ((k : ℝ) * T) 0)
    (hAvoid : Disjoint (range G)
      (⋃ i : ℤ × ℤ, {p + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)})) :
    Disjoint (range (fun x : ℝ => Plane.mk x (G (p 0) 1)))
      (⋃ i : ℤ × ℤ, {p + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)}) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x,rfl⟩ hm
  obtain ⟨i,hi⟩ := mem_iUnion.mp hm
  have he : Plane.mk x (G (p 0) 1) =
      p + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T) := mem_singleton_iff.mp hi
  have hx : x = p 0 + (i.1 : ℝ) * T := congrArg (fun w : Plane => w 0) he
  have hg : G x = Plane.mk x (G (p 0) 1) := by
    rw [hx, hPeriod]
    ext k
    fin_cases k
    · change G (p 0) 0 + (i.1 : ℝ) * T = p 0 + (i.1 : ℝ) * T
      rw [hFirst]
    · change G (p 0) 1 + 0 = G (p 0) 1
      exact add_zero _
  exact Set.disjoint_left.mp hAvoid ⟨x,hg⟩ hm
