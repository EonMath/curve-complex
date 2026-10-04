import CurveComplexGenusTwo.Topology.TorusStrip.PeriodicCellCrosscut

open Set Topology Schoenflies CurveComplex

/-- Concrete SAME physical chart for a fundamental rectangle. Its open
interior, rather than its closed boundary, has disjoint lattice translates. -/
theorem actual_physical_fundamental_rectangle_chart
    (T c d : ℝ) (hT : 0<T) :
    ∃ φ : Plane ≃ₜ Plane,
      (∀ z, φ z=Plane.mk (c+T/2+(T/2)*z 0) (d+T/2+(T/2)*z 1)) ∧
      (∀ z, φ.symm z=Plane.mk (2*(z 0-c)/T-1) (2*(z 1-d)/T-1)) ∧
      φ '' Plane.openSquare 0 1=
        {z : Plane | c<z 0 ∧ z 0<c+T ∧ d<z 1 ∧ z 1<d+T} ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint (φ '' Plane.openSquare 0 1)
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          (φ '' Plane.openSquare 0 1))) := by
  let φ : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk (c+T/2+(T/2)*z 0) (d+T/2+(T/2)*z 1)
    invFun := fun z => Plane.mk (2*(z 0-c)/T-1) (2*(z 1-d)/T-1)
    left_inv := by
      intro z
      ext k
      fin_cases k
      · change 2*((c+T/2+(T/2)*z 0)-c)/T-1=z 0
        field_simp [ne_of_gt hT]
        <;> ring
      · change 2*((d+T/2+(T/2)*z 1)-d)/T-1=z 1
        field_simp [ne_of_gt hT]
        <;> ring
    right_inv := by
      intro z
      ext k
      fin_cases k
      · change c+T/2+(T/2)*(2*(z 0-c)/T-1)=z 0
        field_simp [ne_of_gt hT]
        <;> ring
      · change d+T/2+(T/2)*(2*(z 1-d)/T-1)=z 1
        field_simp [ne_of_gt hT]
        <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hmem (z : Plane) : φ.symm z∈Plane.openSquare 0 1 ↔
      c<z 0 ∧ z 0<c+T ∧ d<z 1 ∧ z 1<d+T := by
    rw [mem_openSquare_zero_one]
    change max |2*(z 0-c)/T-1| |2*(z 1-d)/T-1|<1 ↔ _
    rw [max_lt_iff,abs_lt,abs_lt]
    constructor
    · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
      have he0 := (lt_div_iff₀ hT).mp (show 0<2*(z 0-c)/T by linarith)
      have he1 := (div_lt_iff₀ hT).mp (show 2*(z 0-c)/T<2 by linarith)
      have he2 := (lt_div_iff₀ hT).mp (show 0<2*(z 1-d)/T by linarith)
      have he3 := (div_lt_iff₀ hT).mp (show 2*(z 1-d)/T<2 by linarith)
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · rintro ⟨h0,h1,h2,h3⟩
      have he0 : 0<2*(z 0-c)/T := (lt_div_iff₀ hT).mpr (by linarith)
      have he1 : 2*(z 0-c)/T<2 := (div_lt_iff₀ hT).mpr (by linarith)
      have he2 : 0<2*(z 1-d)/T := (lt_div_iff₀ hT).mpr (by linarith)
      have he3 : 2*(z 1-d)/T<2 := (div_lt_iff₀ hT).mpr (by linarith)
      exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  have hopen : φ '' Plane.openSquare 0 1=
      {z : Plane | c<z 0 ∧ z 0<c+T ∧ d<z 1 ∧ z 1<d+T} := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (hmem (φ w)).mp (by simpa using hw)
    · intro hz
      exact ⟨φ.symm z,(hmem z).mpr hz,φ.apply_symm_apply z⟩
  refine ⟨φ,fun _ => rfl,fun _ => rfl,hopen,?_⟩
  intro i hi
  rw [hopen]
  apply Set.disjoint_left.mpr
  rintro z hz ⟨w,hw,he⟩
  have he0 := congrArg (fun z : Plane => z 0) he
  have he1 := congrArg (fun z : Plane => z 1) he
  change w 0+(i.1:ℝ)*T=z 0 at he0
  change w 1+(i.2:ℝ)*T=z 1 at he1
  have h0lo : (-1:ℝ)<(i.1:ℝ) := by nlinarith [hz.1,hw.2.1]
  have h0hi : (i.1:ℝ)<1 := by nlinarith [hz.2.1,hw.1]
  have h1lo : (-1:ℝ)<(i.2:ℝ) := by nlinarith [hz.2.2.1,hw.2.2.2]
  have h1hi : (i.2:ℝ)<1 := by nlinarith [hz.2.2.2,hw.2.2.1]
  have h0loZ : (-1:ℤ)< i.1 := by exact_mod_cast h0lo
  have h0hiZ : i.1<1 := by exact_mod_cast h0hi
  have h1loZ : (-1:ℤ)< i.2 := by exact_mod_cast h1lo
  have h1hiZ : i.2<1 := by exact_mod_cast h1hi
  apply hi
  apply Prod.ext <;> dsimp <;> omega

#print axioms actual_physical_fundamental_rectangle_chart
