import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTerminalReturningParameters

open Set Topology Schoenflies CurveComplex

/-- Zero finite quotient events excludes the entire physical reference grid,
including all parameters outside the chosen counting window. -/
theorem actual_zero_horizontal_quotient_events_avoids_grid
    (G : C(ℝ,Plane)) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) x, G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hfinite : {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.Finite)
    (hzero : {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.ncard=0) :
    ∀ (x : ℝ) (i : ℤ), G x 1≠c+(i:ℝ)*T := by
  have hempty := (Set.ncard_eq_zero hfinite).mp hzero
  intro x i hx
  obtain ⟨k,t,ht,hxt⟩ := actual_parameter_has_fundamental_window T 0 x hT
  have hy : G x 1=G t 1 := by
    rw [hxt,hp]
    change G t 1+0=G t 1
    exact add_zero _
  have hevent : (⟨t,ht⟩ : Ico 0 (0+T)) ∈
      {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T} := ⟨i,hy.symm.trans hx⟩
  rw [hempty] at hevent
  exact hevent

/-- Actual avoidance of the horizontal grid places the WHOLE continuous
source in one physical complementary band. No boundedness or graph premise. -/
theorem actual_horizontal_grid_avoidance_has_physical_band
    (G : C(ℝ,Plane)) (T c : ℝ) (hT : 0<T)
    (havoid : ∀ (x : ℝ) (i : ℤ), G x 1≠c+(i:ℝ)*T) :
    ∃ k : ℤ, ∀ x, c+(k:ℝ)*T<G x 1 ∧ G x 1<c+((k+1:ℤ):ℝ)*T := by
  let k : ℤ := Int.floor ((G 0 1-c)/T)
  have hlo : c+(k:ℝ)*T≤G 0 1 := by
    have hh := (le_div_iff₀ hT).mp (Int.floor_le ((G 0 1-c)/T))
    dsimp [k]
    linarith
  have hhi : G 0 1<c+((k+1:ℤ):ℝ)*T := by
    have hh := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one ((G 0 1-c)/T))
    push_cast
    dsimp [k]
    linarith
  have hlo' : c+(k:ℝ)*T<G 0 1 := lt_of_le_of_ne hlo (havoid 0 k).symm
  have hsides (j : ℤ) : range (fun x : ℝ => G x 1) ⊆ Iio (c+(j:ℝ)*T) ∨
      range (fun x : ℝ => G x 1) ⊆ Ioi (c+(j:ℝ)*T) := by
    have hh : Continuous (fun x : ℝ => G x 1) := by fun_prop
    apply (isPreconnected_range hh).subset_or_subset isOpen_Iio isOpen_Ioi
    · exact Set.disjoint_left.mpr (by
        intro y hy hz
        change y<c+(j:ℝ)*T at hy
        change c+(j:ℝ)*T<y at hz
        exact lt_asymm hy hz)
    · rintro y ⟨x,rfl⟩
      exact lt_or_gt_of_ne (havoid x j)
  obtain hl | hl := hsides k
  · exact False.elim (lt_asymm hlo' (hl (mem_range_self 0)))
  obtain hu | hu := hsides (k+1)
  · exact ⟨k,fun x => ⟨hl (mem_range_self x),hu (mem_range_self x)⟩⟩
  · exact False.elim (lt_asymm hhi (hu (mem_range_self 0)))

#print axioms actual_zero_horizontal_quotient_events_avoids_grid
#print axioms actual_horizontal_grid_avoidance_has_physical_band
