import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedReferenceClass
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusImageTransport
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusIsotopyDescent
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHomeomorphEssentialPositionTransport
open Set Topology Schoenflies CurveComplex
/-- Any two actual puncture-free horizontal reference circles are related by
an actual torus ambient isotopy fixing the puncture at every time. -/
theorem actual_puncture_free_horizontal_references_are_relative_isotopic
    (c b : ℝ) (p : Plane)
    (hpc : ∀ i : ℤ,p 1+(i:ℝ)*(2*Real.pi)≠c)
    (hpb : ∀ i : ℤ,p 1+(i:ℝ)*(2*Real.pi)≠b) :
    ∃ H : AmbientIsotopy (Circle×Circle),
      (∀ t,H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      H.finalMap '' range (fun z : Circle => (z,Circle.exp c))=
        range (fun z : Circle => (z,Circle.exp b)) := by
  let q := Plane.mk (p 1) (p 0)
  obtain ⟨P,hPfix,hPeq,hPgrid⟩ :=
    actual_puncture_free_vertical_reference_grids_are_relative_isotopic
      (2*Real.pi) c b q (by positivity) hpc hpb
  have hz : Plane.mk 0 0=(0:Plane) := by ext k; fin_cases k <;> rfl
  have hPq : ∀ t,P.map (t,q)=q := by intro t; simpa [hz] using hPfix t (0,0)
  obtain ⟨K,hKcomm,hKfix⟩ := actual_lattice_isotopy_descends_to_marked_torus P hPeq q hPq
  let π : Plane→Circle×Circle := fun z => (Circle.exp (z 0),Circle.exp (z 1))
  have hKcircle : K.finalMap '' {z : Circle×Circle | z.1=Circle.exp c}=
      {z : Circle×Circle | z.1=Circle.exp b} := by
    rw [← actual_vertical_grid_projection_is_reference_circle c,
      actual_quotient_commutation_transports_final_image π P K hKcomm,hPgrid,
      actual_vertical_grid_projection_is_reference_circle]
  let e := Homeomorph.prodComm Circle Circle
  obtain ⟨H,hH⟩ := actual_homeomorph_conjugates_ambient_isotopy e K
  have hflip (d : ℝ) : e '' range (fun z : Circle => (z,Circle.exp d))=
      {z : Circle×Circle | z.1=Circle.exp d} := by
    ext z
    constructor
    · rintro ⟨_,⟨w,rfl⟩,rfl⟩; rfl
    · intro hz
      exact ⟨(z.2,Circle.exp d),mem_range_self z.2,Prod.ext hz.symm rfl⟩
  have hback : e.symm '' {z : Circle×Circle | z.1=Circle.exp b}=
      range (fun z : Circle => (z,Circle.exp b)) := by
    rw [← hflip b,image_image]
    change (id : Circle×Circle→Circle×Circle) '' range (fun z : Circle => (z,Circle.exp b))=_
    exact image_id _
  refine ⟨H,?_,?_⟩
  · intro t
    rw [hH]
    have hh := hKfix t
    change K.map (t,(Circle.exp (p 1),Circle.exp (p 0)))=
      (Circle.exp (p 1),Circle.exp (p 0)) at hh
    change e.symm (K.map (t,(Circle.exp (p 1),Circle.exp (p 0))))=_
    rw [hh]
    rfl
  · calc
      H.finalMap '' range (fun z : Circle => (z,Circle.exp c))=
          e.symm '' (K.finalMap '' (e '' range (fun z : Circle => (z,Circle.exp c)))) := by
        rw [image_image,image_image]
        apply image_congr
        intro z _
        exact hH ⟨1,by norm_num⟩ z
      _ = _ := by rw [hflip c,hKcircle,hback]
#print axioms actual_puncture_free_horizontal_references_are_relative_isotopic
