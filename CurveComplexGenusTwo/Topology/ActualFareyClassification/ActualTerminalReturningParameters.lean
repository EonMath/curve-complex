import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualPeriodicCoordinateGraph

open Set Topology Schoenflies CurveComplex

/-- Normalize an actual parameter into the fixed half-open period window. -/
theorem actual_parameter_has_fundamental_window (T r x : ℝ) (hT : 0 < T) :
    ∃ k : ℤ, ∃ t ∈ Ico r (r + T), x = t + (k : ℝ) * T := by
  let k : ℤ := Int.floor ((x-r)/T)
  let t := x-(k : ℝ)*T
  have hlo : (k : ℝ) ≤ (x-r)/T := Int.floor_le _
  have hhi : (x-r)/T < (k : ℝ)+1 := Int.lt_floor_add_one _
  have hl := (le_div_iff₀ hT).mp hlo
  have hu := (div_lt_iff₀ hT).mp hhi
  refine ⟨k,t,⟨?_,?_⟩,?_⟩ <;> dsimp [t] <;> linarith

/-- An actual failure of horizontal injectivity in a terminal strip supplies
an actual returning short subarc entirely within the original period window.
No returning-arc, finite-contact, or bigon certificate is assumed. -/
theorem actual_terminal_noninjective_coordinate_has_short_return
    (G : C(ℝ,Plane)) (c r T : ℝ) (hT : 0 < T)
    (hp : ∀ (k : ℤ) x, G (x + (k : ℝ)*T) = G x + Plane.mk ((k : ℝ)*T) 0)
    (hFiber : {x : ℝ | G x 0 = c} = {r})
    (hStrip : ∀ x ∈ Ioo r (r+T), c < G x 0 ∧ G x 0 < c+T)
    (hNot : ¬ Function.Injective (fun x => G x 0)) :
    ∃ a b : ℝ, r < a ∧ a < b ∧ b < r+T ∧ b-a < T ∧
      G a 0 = G b 0 ∧ c < G a 0 ∧ G a 0 < c+T := by
  have hr : G r 0 = c := by
    have hh : r ∈ ({x : ℝ | G x 0 = c} : Set ℝ) := by rw [hFiber]; simp
    exact hh
  have hBounds (t : ℝ) (ht : t ∈ Ico r (r+T)) : c ≤ G t 0 ∧ G t 0 < c+T := by
    rcases eq_or_lt_of_le ht.1 with he | he
    · rw [← he,hr]
      exact ⟨le_rfl,by linarith⟩
    · exact ⟨(hStrip t ⟨he,ht.2⟩).1.le,(hStrip t ⟨he,ht.2⟩).2⟩
  simp only [Function.Injective] at hNot
  push Not at hNot
  obtain ⟨x,y,hxy,hne⟩ := hNot
  obtain ⟨i,a,ha,hxa⟩ := actual_parameter_has_fundamental_window T r x hT
  obtain ⟨j,b,hb,hyb⟩ := actual_parameter_has_fundamental_window T r y hT
  have hLevel : G a 0 + (i : ℝ)*T = G b 0 + (j : ℝ)*T := by
    rw [hxa,hyb,hp,hp] at hxy
    exact hxy
  have hi : i = j := by
    have hA := hBounds a ha
    have hB := hBounds b hb
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · have hStep : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
      nlinarith
    · have hStep : (j : ℝ)+1 ≤ (i : ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
      nlinarith
  have hab : a ≠ b := by
    intro hab
    apply hne
    rw [hxa,hyb,hi,hab]
  have hSame : G a 0 = G b 0 := by rw [hi] at hLevel; linarith
  have har : r < a := by
    apply lt_of_le_of_ne ha.1
    intro hh
    have hbr : b ∈ ({t : ℝ | G t 0 = c} : Set ℝ) := by
      change G b 0 = c
      rw [← hSame,← hh,hr]
    rw [hFiber] at hbr
    exact hab (hh.symm.trans (mem_singleton_iff.mp hbr).symm)
  have hbr : r < b := by
    apply lt_of_le_of_ne hb.1
    intro hh
    have har' : a ∈ ({t : ℝ | G t 0 = c} : Set ℝ) := by
      change G a 0 = c
      rw [hSame,← hh,hr]
    rw [hFiber] at har'
    exact hab ((mem_singleton_iff.mp har').trans hh)
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact ⟨a,b,har,hab,hb.2,by linarith [hb.2],hSame,(hStrip a ⟨har,ha.2⟩).1,
      (hStrip a ⟨har,ha.2⟩).2⟩
  · exact ⟨b,a,hbr,hba,ha.2,by linarith [ha.2],hSame.symm,(hStrip b ⟨hbr,hb.2⟩).1,
      (hStrip b ⟨hbr,hb.2⟩).2⟩
