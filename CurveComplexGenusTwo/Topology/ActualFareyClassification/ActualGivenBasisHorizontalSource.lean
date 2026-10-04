import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualIntegerBasisTorusHomeomorph
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHomeomorphEssentialPositionTransport
open Set Topology Schoenflies CurveComplex
/-- Normalize the ORIGINAL essential source and its literal original winding by
an actual unimodular torus homeomorphism, retaining its parametrization. -/
theorem actual_given_primitive_basis_has_horizontal_source_normalization
    (b : EssentialCurve (Circle×Circle)) (m n u v : ℤ) (hbez : m*u+n*v=1)
    (F : C(ℝ,ℝ×ℝ))
    (hproj : ∀ x,(Circle.exp (F x).1,Circle.exp (F x).2)=b.val.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x,F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+(k:ℝ)*(m:ℝ)*(2*Real.pi),(F x).2+(k:ℝ)*(n:ℝ)*(2*Real.pi))) :
    ∃ b' : EssentialCurve (Circle×Circle), ∃ G : C(ℝ,ℝ×ℝ),
      (∀ z,b'.val.map z=actual_integer_basis_torus_homeomorph m n u v hbez (b.val.map z)) ∧
      b'.val.image=actual_integer_basis_torus_homeomorph m n u v hbez '' b.val.image ∧
      (∀ x,(Circle.exp (G x).1,Circle.exp (G x).2)=b'.val.map (Circle.exp x)) ∧
      (∀ (k : ℤ) x,G (x+(k:ℝ)*(2*Real.pi))=
        ((G x).1+(k:ℝ)*(2*Real.pi),(G x).2)) := by
  let e := actual_integer_basis_torus_homeomorph m n u v hbez
  obtain ⟨b',hparam,himage⟩ := actual_homeomorph_transports_essential_curve e b
  let G : C(ℝ,ℝ×ℝ) := ⟨fun x =>
    ((u:ℝ)*(F x).1+(v:ℝ)*(F x).2,-(n:ℝ)*(F x).1+(m:ℝ)*(F x).2),by fun_prop⟩
  have hb : (m:ℝ)*(u:ℝ)+(n:ℝ)*(v:ℝ)=1 := by exact_mod_cast hbez
  refine ⟨b',G,hparam,himage,?_,?_⟩
  · intro x
    rw [hparam,← hproj]
    exact (actual_integer_basis_torus_commutes_with_projection m n u v hbez (F x)).symm
  · intro k x
    change ((u:ℝ)*(F (x+(k:ℝ)*(2*Real.pi))).1+(v:ℝ)*(F (x+(k:ℝ)*(2*Real.pi))).2,
      -(n:ℝ)*(F (x+(k:ℝ)*(2*Real.pi))).1+(m:ℝ)*(F (x+(k:ℝ)*(2*Real.pi))).2)=_
    rw [hp]
    apply Prod.ext
    · change (u:ℝ)*((F x).1+(k:ℝ)*(m:ℝ)*(2*Real.pi))+
        (v:ℝ)*((F x).2+(k:ℝ)*(n:ℝ)*(2*Real.pi))=
        (u:ℝ)*(F x).1+(v:ℝ)*(F x).2+(k:ℝ)*(2*Real.pi)
      linear_combination ((k:ℝ)*(2*Real.pi))*hb
    · change -(n:ℝ)*((F x).1+(k:ℝ)*(m:ℝ)*(2*Real.pi))+
        (m:ℝ)*((F x).2+(k:ℝ)*(n:ℝ)*(2*Real.pi))=
        -(n:ℝ)*(F x).1+(m:ℝ)*(F x).2
      ring
#print axioms actual_given_primitive_basis_has_horizontal_source_normalization
