import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualStandardTorusSurface

open Set Topology Schoenflies CurveComplex

/-- The standard torus source-to-terminal-strip construction assumes no surface
structure: its plane-model closed-surface structure is produced internally. -/
theorem actual_standard_torus_original_horizontal_source_has_marked_terminal_strip
    (a b : EssentialCurve (Circle×Circle)) (c : ℝ) (p : Plane)
    (ha : a.val.image={z : Circle×Circle | z.1=Circle.exp c})
    (hpgrid : ∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠c)
    (hAvoid : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image)
    (F : C(ℝ,ℝ×ℝ))
    (hproj : ∀ x, (Circle.exp (F x).1,Circle.exp (F x).2)=b.val.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x, F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+(k:ℝ)*(2*Real.pi),(F x).2)) :
    ∃ H Q : AmbientIsotopy (Circle×Circle), ∃ Gf : C(ℝ,Plane), ∃ cf r : ℝ,
      (∀ t, H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      (∀ t, Q.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      H.finalMap '' b.val.image=
        (fun z : Plane => (Circle.exp (z 0),Circle.exp (z 1))) '' range Gf ∧
      Q.finalMap '' a.val.image={z : Circle×Circle | z.1=Circle.exp cf} ∧
      IsClosedEmbedding Gf ∧
      (∀ (k : ℤ) x, Gf (x+(k:ℝ)*(2*Real.pi))=
        Gf x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ),
        Gf x=Gf y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi)) → j=0) ∧
      (∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠cf) ∧
      Disjoint (range Gf)
        (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}) ∧
      {t : ℝ | Gf t 0=cf}={r} ∧
      (∀ t∈Ioo r (r+2*Real.pi), cf<Gf t 0 ∧ Gf t 0<cf+2*Real.pi) := by
  obtain ⟨C,hC⟩ := actual_standard_torus_has_closed_surface_structure
  let := C
  let := hC
  exact actual_original_horizontal_winding_essential_has_marked_terminal_strip
    a b c p ha hpgrid hAvoid F hproj hp

#print axioms actual_standard_torus_original_horizontal_source_has_marked_terminal_strip
