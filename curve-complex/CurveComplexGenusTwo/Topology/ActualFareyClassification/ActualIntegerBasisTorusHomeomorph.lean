import CurveComplexGenusTwo.Topology.TorusStrip.EssentialCurveNormalizedLine
open Set Topology Schoenflies CurveComplex
/-- The actual unimodular integer basis change descends to a torus
homeomorphism with its literal exponential commutation law. -/
noncomputable def actual_integer_basis_torus_homeomorph (m n u v : ℤ)
    (hbez : m*u+n*v=1) : (Circle×Circle) ≃ₜ (Circle×Circle) where
  toFun := fun z => (z.1^u*z.2^v,z.1^(-n)*z.2^m)
  invFun := fun z => (z.1^m*z.2^(-v),z.1^n*z.2^u)
  left_inv := by
    intro z
    apply Prod.ext
    · simp only [mul_zpow,← zpow_mul]
      rw [mul_mul_mul_comm,← zpow_add,← zpow_add]
      have h1 : u*m+(-n)*(-v)=1 := by linear_combination hbez
      have h0 : v*m+m*(-v)=0 := by ring
      rw [h1,h0]
      simp
    · simp only [mul_zpow,← zpow_mul]
      rw [mul_mul_mul_comm,← zpow_add,← zpow_add]
      have h0 : u*n+(-n)*u=0 := by ring
      have h1 : v*n+m*u=1 := by linear_combination hbez
      rw [h0,h1]
      simp
  right_inv := by
    intro z
    apply Prod.ext
    · simp only [mul_zpow,← zpow_mul]
      rw [mul_mul_mul_comm,← zpow_add,← zpow_add]
      have h1 : m*u+n*v=1 := hbez
      have h0 : (-v)*u+u*v=0 := by ring
      rw [h1,h0]
      simp
    · simp only [mul_zpow,← zpow_mul]
      rw [mul_mul_mul_comm,← zpow_add,← zpow_add]
      have h0 : m*(-n)+n*m=0 := by ring
      have h1 : (-v)*(-n)+u*m=1 := by linear_combination hbez
      rw [h0,h1]
      simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem actual_integer_basis_torus_commutes_with_projection
    (m n u v : ℤ) (hbez : m*u+n*v=1) (z : ℝ×ℝ) :
    actual_integer_basis_torus_homeomorph m n u v hbez
      (Circle.exp z.1,Circle.exp z.2)=
    (Circle.exp (integer_basis_plane_homeomorph m n u v hbez z 0),
      Circle.exp (integer_basis_plane_homeomorph m n u v hbez z 1)) := by
  apply Prod.ext
  · change (Circle.exp z.1)^u*(Circle.exp z.2)^v=
      Circle.exp ((u:ℝ)*z.1+(v:ℝ)*z.2)
    rw [Circle.exp_add]
    simp only [← Circle.exp_zsmul,zsmul_eq_mul]
  · change (Circle.exp z.1)^(-n)*(Circle.exp z.2)^m=
      Circle.exp (-(n:ℝ)*z.1+(m:ℝ)*z.2)
    rw [Circle.exp_add]
    simp only [← Circle.exp_zsmul,zsmul_eq_mul,Int.cast_neg]
#print axioms actual_integer_basis_torus_homeomorph
#print axioms actual_integer_basis_torus_commutes_with_projection
