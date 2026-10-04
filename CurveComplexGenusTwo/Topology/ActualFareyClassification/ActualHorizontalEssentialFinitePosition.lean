import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHomeomorphEssentialPositionTransport

open Set Topology Schoenflies CurveComplex

/-- Actual horizontal-reference finite position, obtained by conjugating the
existing finite-position producer. This does NOT axis-swap a reducing theorem. -/
theorem actual_horizontal_essential_has_marked_finite_position
    [ChartedSpace Plane (Circle×Circle)] [ClosedSurface (Circle×Circle)]
    (a b : EssentialCurve (Circle×Circle)) (c : ℝ) (p : Plane)
    (ha : a.val.image={z : Circle×Circle | z.2=Circle.exp c})
    (hpgrid : ∀ i : ℤ, p 1+(i:ℝ)*(2*Real.pi)≠c)
    (hAvoid : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image) :
    ∃ P Q : AmbientIsotopy (Circle×Circle), ∃ a' b' : EssentialCurve (Circle×Circle),
    ∃ cf : ℝ,
      (∀ t, P.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      (∀ t, Q.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      P.finalMap '' b.val.image=b'.val.image ∧
      Q.finalMap '' a.val.image=a'.val.image ∧
      a'.val.image={z : Circle×Circle | z.2=Circle.exp cf} ∧
      Transverse a'.val b'.val ∧
      (∀ i : ℤ, p 1+(i:ℝ)*(2*Real.pi)≠cf) ∧
      (Circle.exp (p 0),Circle.exp (p 1))∉b'.val.image := by
  let e : (Circle×Circle) ≃ₜ (Circle×Circle) := Homeomorph.prodComm Circle Circle
  let ps : Plane := Plane.mk (p 1) (p 0)
  obtain ⟨as,hAsMap,hAs⟩ := actual_homeomorph_transports_essential_curve e a
  obtain ⟨bs,hBsMap,hBs⟩ := actual_homeomorph_transports_essential_curve e b
  have hAsRef : as.val.image={z : Circle×Circle | z.1=Circle.exp c} := by
    rw [hAs,ha]
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact hw
    · intro hz
      exact ⟨e.symm z,hz,e.apply_symm_apply z⟩
  have hBsAvoid : (Circle.exp (ps 0),Circle.exp (ps 1))∉bs.val.image := by
    rw [hBs]
    rintro ⟨z,hz,he⟩
    apply hAvoid
    have hzEq : z=(Circle.exp (p 0),Circle.exp (p 1)) := by
      apply e.injective
      exact he
    rwa [hzEq] at hz
  obtain ⟨H,K,ar,br,q,cf,_,hHFix,hKFix,hHImage,hKImage,hArRef,hTrans,hCf,hBrAvoid⟩ :=
    actual_essential_torus_has_puncture_relative_finite_position as bs c ps hAsRef hpgrid hBsAvoid
  obtain ⟨P,hP⟩ := actual_homeomorph_conjugates_ambient_isotopy e H
  obtain ⟨Q,hQ⟩ := actual_homeomorph_conjugates_ambient_isotopy e K
  obtain ⟨a',hA'Map,hA'⟩ := actual_homeomorph_transports_essential_curve e.symm ar
  obtain ⟨b',hB'Map,hB'⟩ := actual_homeomorph_transports_essential_curve e.symm br
  obtain ⟨aa,bb,_,_,hAA,hBB,hAB⟩ :=
    actual_homeomorph_transports_finite_transverse_curves e.symm ar.val br.val hTrans
  have hTrans' : Transverse a'.val b'.val := by
    have ha' : aa.image=a'.val.image := hAA.trans hA'.symm
    have hb' : bb.image=b'.val.image := hBB.trans hB'.symm
    simpa only [Transverse,CrossesAt,ha',hb'] using hAB
  have hPImage : P.finalMap '' b.val.image=b'.val.image := by
    rw [hB',← hHImage,hBs,image_image,image_image]
    congr 1
    funext z
    exact hP _ z
  have hQImage : Q.finalMap '' a.val.image=a'.val.image := by
    rw [hA',← hKImage,hAs,image_image,image_image]
    congr 1
    funext z
    exact hQ _ z
  have hA'Ref : a'.val.image={z : Circle×Circle | z.2=Circle.exp cf} := by
    rw [hA',hArRef]
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact hw
    · intro hz
      exact ⟨e z,hz,e.symm_apply_apply z⟩
  have hPFix : ∀ t, P.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
      (Circle.exp (p 0),Circle.exp (p 1)) := by
    intro t
    rw [hP]
    change e.symm (H.map (t,(Circle.exp (ps 0),Circle.exp (ps 1))))=_
    rw [hHFix]
    rfl
  have hQFix : ∀ t, Q.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
      (Circle.exp (p 0),Circle.exp (p 1)) := by
    intro t
    rw [hQ]
    change e.symm (K.map (t,(Circle.exp (ps 0),Circle.exp (ps 1))))=_
    rw [hKFix]
    rfl
  have hAvoid' : (Circle.exp (p 0),Circle.exp (p 1))∉b'.val.image := by
    rw [hB']
    rintro ⟨z,hz,he⟩
    apply hBrAvoid
    have hzEq : z=(Circle.exp (ps 0),Circle.exp (ps 1)) := by
      apply e.symm.injective
      exact he
    rwa [hzEq] at hz
  exact ⟨P,Q,a',b',cf,hPFix,hQFix,hPImage,hQImage,hA'Ref,hTrans',hCf,hAvoid'⟩

#print axioms actual_horizontal_essential_has_marked_finite_position
