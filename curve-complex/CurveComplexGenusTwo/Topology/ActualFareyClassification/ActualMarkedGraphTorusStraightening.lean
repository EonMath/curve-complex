import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualAdaptedGraphTargetAvoidance
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusIsotopyDescent

open Set Topology Schoenflies CurveComplex unitInterval

/-- Actual graph straightening descends to a marked torus isotopy carrying the
entire projected source onto its source-derived horizontal reference. -/
theorem actual_periodic_graph_has_marked_torus_straightening
    (G : C(ℝ, Plane)) (p : Plane)
    (hFirst : ∀ x, G x 0 = x)
    (hPeriod : ∀ (k : ℤ) x,
      G (x + (k : ℝ) * (2 * Real.pi)) =
        G x + Plane.mk ((k : ℝ) * (2 * Real.pi)) 0) :
    ∃ K : AmbientIsotopy (Circle × Circle),
      (∀ t, K.map (t,(Circle.exp (p 0),Circle.exp (p 1))) =
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      K.finalMap '' range (fun x : ℝ => (Circle.exp (G x 0),Circle.exp (G x 1))) =
        range (fun z : Circle => (z,Circle.exp (G (p 0) 1))) := by
  obtain ⟨H,hEq,hFix,hMove,_⟩ :=
    actual_periodic_graph_has_marked_straightening G (2 * Real.pi) p hFirst hPeriod
  have hMark : ∀ t, H.map (t,p) = p := by
    intro t
    have hh := hFix t (0,0)
    have hz : Plane.mk 0 0 = (0 : Plane) := by ext k; fin_cases k <;> rfl
    simpa only [Int.cast_zero,zero_mul,hz,add_zero] using hh
  obtain ⟨K,hComm,hKFix⟩ := actual_lattice_isotopy_descends_to_marked_torus H hEq p hMark
  have hFinal (x : ℝ) : K.finalMap (Circle.exp (G x 0),Circle.exp (G x 1)) =
      (Circle.exp x,Circle.exp (G (p 0) 1)) := by
    have hh := hComm 1 (G x)
    change K.finalMap _ = (Circle.exp (H.finalMap (G x) 0),
      Circle.exp (H.finalMap (G x) 1)) at hh
    rw [hMove] at hh
    exact hh
  refine ⟨K,hKFix,?_⟩
  ext z
  constructor
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    exact ⟨Circle.exp x,(hFinal x).symm⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨x,rfl⟩ := Circle.exp_surjective a
    exact ⟨_,⟨x,rfl⟩,hFinal x⟩
