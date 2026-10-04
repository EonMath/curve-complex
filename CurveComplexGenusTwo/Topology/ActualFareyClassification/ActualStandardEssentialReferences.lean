import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleProjectionEssential

open Set Topology Schoenflies CurveComplex

/-- Construct the ACTUAL standard vertical and horizontal essential references.
Essentiality is proved from their literal circle projection, not supplied as an
additional certificate. -/
theorem actual_standard_torus_has_essential_straight_references
    (c h : ℝ) :
    ∃ a b : EssentialCurve (Circle×Circle),
      (∀ z, a.val.map z=(Circle.exp c,z)) ∧
      (∀ z, b.val.map z=(z,Circle.exp h)) ∧
      a.val.image={z : Circle×Circle | z.1=Circle.exp c} ∧
      b.val.image={z : Circle×Circle | z.2=Circle.exp h} := by
  let a : Curve (Circle×Circle) := {
    map := fun z => (Circle.exp c,z)
    embedded := isEmbedding_prodMkRight (Circle.exp c) }
  let b : Curve (Circle×Circle) := {
    map := fun z => (z,Circle.exp h)
    embedded := isEmbedding_prodMkLeft (Circle.exp h) }
  have ha : Essential a := actual_circle_projected_curve_is_essential a
    ⟨Prod.snd,continuous_snd⟩ (fun _ => rfl)
  have hb : Essential b := actual_circle_projected_curve_is_essential b
    ⟨Prod.fst,continuous_fst⟩ (fun _ => rfl)
  refine ⟨⟨a,ha⟩,⟨b,hb⟩,fun _ => rfl,fun _ => rfl,?_,?_⟩
  · ext z
    constructor
    · rintro ⟨w,rfl⟩
      rfl
    · intro hz
      exact ⟨z.2,Prod.ext hz.symm rfl⟩
  · ext z
    constructor
    · rintro ⟨w,rfl⟩
      rfl
    · intro hz
      exact ⟨z.1,Prod.ext rfl hz.symm⟩

#print axioms actual_standard_torus_has_essential_straight_references
