import CurveComplexGenusTwo.Topology.PrimitiveEssential
import Schoenflies.Plane
import Mathlib
open Set Schoenflies CurveComplex Topology
open CurveComplexGenusTwo.Topology.PuncturedTorusCandidate

noncomputable def integer_basis_plane_homeomorph (m n u v : ℤ)
    (hbez : m*u+n*v=1) : (ℝ × ℝ) ≃ₜ Plane where
  toFun := fun z => Plane.mk ((u:ℝ)*z.1+(v:ℝ)*z.2) (-(n:ℝ)*z.1+(m:ℝ)*z.2)
  invFun := fun z => ((m:ℝ)*z 0-(v:ℝ)*z 1,(n:ℝ)*z 0+(u:ℝ)*z 1)
  left_inv := by
    have hb : (m:ℝ)*(u:ℝ)+(n:ℝ)*(v:ℝ)=1 := by exact_mod_cast hbez
    intro z
    apply Prod.ext <;> simp [Plane.mk]
    · linear_combination z.1*hb
    · linear_combination z.2*hb
  right_inv := by
    have hb : (m:ℝ)*(u:ℝ)+(n:ℝ)*(v:ℝ)=1 := by exact_mod_cast hbez
    intro z
    ext i
    fin_cases i <;> simp [Plane.mk]
    · linear_combination z 0*hb
    · linear_combination z 1*hb
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  continuous_invFun := by fun_prop

theorem primitive_lift_has_normalized_line (F : C(ℝ, ℝ × ℝ)) (hF : IsClosedEmbedding F)
    (m n : ℤ) (hgcd : m.gcd n=1)
    (hp : ∀ (k : ℤ) (x : ℝ), F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+(k:ℝ)*(m:ℝ)*(2*Real.pi),(F x).2+(k:ℝ)*(n:ℝ)*(2*Real.pi)))
    (hc : ∀ (x y : ℝ) (a b : ℤ),
      F x=((F y).1+(a:ℝ)*(2*Real.pi),(F y).2+(b:ℝ)*(2*Real.pi)) →
      ∃ k : ℤ, a=k*m ∧ b=k*n) :
    ∃ u v : ℤ, ∃ hbez : m*u+n*v=1, ∃ G : C(ℝ,Plane),
      (∀ x, G x=integer_basis_plane_homeomorph m n u v hbez (F x)) ∧
      IsClosedEmbedding G ∧
      (∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*(2*Real.pi))=G x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0) ∧
      (∀ (x y : ℝ) (a b : ℤ),
        G x=G y+Plane.mk ((a:ℝ)*(2*Real.pi)) ((b:ℝ)*(2*Real.pi)) → b=0) := by
  let u := Int.gcdA m n
  let v := Int.gcdB m n
  have hbez : m*u+n*v=1 := by
    have h := Int.gcd_eq_gcd_ab m n
    rw [hgcd] at h
    exact h.symm
  let e := integer_basis_plane_homeomorph m n u v hbez
  let G : C(ℝ,Plane) := ⟨fun x => e (F x),e.continuous.comp F.continuous⟩
  have hb : (m:ℝ)*(u:ℝ)+(n:ℝ)*(v:ℝ)=1 := by exact_mod_cast hbez
  refine ⟨u,v,hbez,G,fun x => rfl,e.isClosedEmbedding.comp hF,?_,?_⟩
  · intro k x
    change e (F (x+(k:ℝ)*(2*Real.pi)))=e (F x)+Plane.mk ((k:ℝ)*(2*Real.pi)) 0
    rw [hp]
    ext i
    fin_cases i <;> simp [e,integer_basis_plane_homeomorph,Plane.mk]
    · linear_combination ((k:ℝ)*(2*Real.pi))*hb
    · ring
  · intro x y a b hxy
    have hFxy : F x=((F y).1+((m*a-v*b:ℤ):ℝ)*(2*Real.pi),
        (F y).2+((n*a+u*b:ℤ):ℝ)*(2*Real.pi)) := by
      have h := congrArg e.symm hxy
      change e.symm (e (F x))=e.symm (e (F y)+Plane.mk ((a:ℝ)*(2*Real.pi)) ((b:ℝ)*(2*Real.pi))) at h
      have hshift (z : Plane) :
          e.symm (z+Plane.mk ((a:ℝ)*(2*Real.pi)) ((b:ℝ)*(2*Real.pi)))=
          ((e.symm z).1+((m*a-v*b:ℤ):ℝ)*(2*Real.pi),
           (e.symm z).2+((n*a+u*b:ℤ):ℝ)*(2*Real.pi)) := by
        apply Prod.ext <;> simp [e,integer_basis_plane_homeomorph,Plane.mk] <;> push_cast <;> ring
      rw [hshift,e.symm_apply_apply,e.symm_apply_apply] at h
      exact h
    obtain ⟨k,hA,hB⟩ := hc x y (m*a-v*b) (n*a+u*b) hFxy
    have hbzero : (m*u+n*v)*b=0 := by
      linear_combination m*hB-n*hA
    rw [hbez,one_mul] at hbzero
    exact hbzero

/-- The source essential embedded torus curve supplies the normalized line;
its original parametrization is retained through the inverse basis chart. -/
theorem essential_torus_curve_has_normalized_line (c : Curve Torus) (hc : Essential c) :
    ∃ m n u v : ℤ, ∃ hbez : m*u+n*v=1, ∃ G : C(ℝ,Plane),
      (∀ x, (Circle.exp (((integer_basis_plane_homeomorph m n u v hbez).symm (G x)).1),
        Circle.exp (((integer_basis_plane_homeomorph m n u v hbez).symm (G x)).2))=c.map (Circle.exp x)) ∧
      IsClosedEmbedding G ∧
      (∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*(2*Real.pi))=G x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0) ∧
      (∀ (x y : ℝ) (a b : ℤ),
        G x=G y+Plane.mk ((a:ℝ)*(2*Real.pi)) ((b:ℝ)*(2*Real.pi)) → b=0) := by
  obtain ⟨m,n,F,hproj,hperiod,hprim,hcollision⟩ := torus_curve_has_primitive_or_zero_deck_lift c
  have hnz : m ≠ 0 ∨ n ≠ 0 := by
    by_contra hzero
    have ⟨hm,hn⟩ : m=0 ∧ n=0 := by simpa using hzero
    have hz (k : ℤ) (x : ℝ) : F (x+(k:ℝ)*(2*Real.pi))=F x := by
      simpa [hm,hn] using hperiod k x
    exact hc (torus_boundsDisc_of_nullhomotopic_from_cover c
      (torus_curve_nullhomotopic_of_zero_deck_lift c F hproj hz))
  obtain ⟨hgcd,hproper,hF⟩ := hprim hnz
  obtain ⟨u,v,hbez,G,hG,hclosed,hp,hcoll⟩ := primitive_lift_has_normalized_line F hF m n hgcd hperiod hcollision
  refine ⟨m,n,u,v,hbez,G,?_,hclosed,hp,hcoll⟩
  intro x
  rw [hG,(integer_basis_plane_homeomorph m n u v hbez).symm_apply_apply]
  exact hproj x

#print axioms primitive_lift_has_normalized_line
#print axioms essential_torus_curve_has_normalized_line
