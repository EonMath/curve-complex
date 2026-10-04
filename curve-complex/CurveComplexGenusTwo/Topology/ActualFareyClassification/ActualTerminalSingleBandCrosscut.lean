import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualPhysicalFundamentalRectangleChart
import CurveComplexGenusTwo.Topology.TorusStrip.ArcInterval

open Set Topology Schoenflies CurveComplex

/-- Actual terminal source and actual whole-source horizontal band produce
ONE common physical rectangle for source and straight target, and the genuine
periodic crosscut move. No chart or separation certificate is supplied. -/
theorem actual_terminal_single_band_has_periodic_straight_crosscut
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c d r : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) x, G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hFiber : {x : ℝ | G x 0=c}={r})
    (hStrip : ∀ x∈Ioo r (r+T), c<G x 0 ∧ G x 0<c+T)
    (hBand : ∀ x, d<G x 1 ∧ G x 1<d+T) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ) z,
        H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      H.finalMap '' (G '' Icc r (r+T))=
        (fun x : ℝ => Plane.mk x (G r 1)) '' Icc c (c+T) := by
  obtain ⟨φ,hφ,hφinv,hopen,hdeck⟩ := actual_physical_fundamental_rectangle_chart T c d hT
  have hr0 : G r 0=c := by
    have hh : r∈({x : ℝ | G x 0=c} : Set ℝ) := by rw [hFiber]; simp
    exact hh
  have hperiod : G (r+T)=G r+Plane.mk T 0 := by
    simpa using hp 1 r
  have hr1 : G (r+T) 0=c+T := by rw [hperiod]; change G r 0+T=c+T; rw [hr0]
  have hheight : G (r+T) 1=G r 1 := by rw [hperiod]; change G r 1+0=G r 1; ring
  have hBoundary (z : Plane) (hx : z 0=c ∨ z 0=c+T)
      (hy : d<z 1 ∧ z 1<d+T) : φ.symm z∈modelCurve := by
    rw [hφinv]
    change max |2*(z 0-c)/T-1| |2*(z 1-d)/T-1|=1
    have hy0 : 0<2*(z 1-d)/T := (lt_div_iff₀ hT).mpr (by linarith [hy.1])
    have hy1 : 2*(z 1-d)/T<2 := (div_lt_iff₀ hT).mpr (by linarith [hy.2])
    have habs : |2*(z 1-d)/T-1|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hxabs : |2*(z 0-c)/T-1|=1 := by
      rcases hx with hx | hx
      · rw [hx]; norm_num
      · rw [hx]
        have hh : 2*(c+T-c)/T-1=1 := by field_simp [ne_of_gt hT]; ring
        rw [hh]; norm_num
    rw [hxabs,max_eq_left habs]
  have ha : φ.symm (G r)∈modelCurve := hBoundary _ (Or.inl hr0) (hBand r)
  have hb : φ.symm (G (r+T))∈modelCurve := hBoundary _ (Or.inr hr1) (hBand (r+T))
  let J : C(ℝ,Plane) := ⟨fun x => Plane.mk x (G r 1),by fun_prop⟩
  have hJinj : Function.Injective J := by
    intro x y he
    exact congrArg (fun z : Plane => z 0) he
  have hLeft : J c=G r := by ext k; fin_cases k; exact hr0.symm; rfl
  have hRight : J (c+T)=G (r+T) := by ext k; fin_cases k; exact hr1.symm; exact hheight.symm
  have hA : IsArcBetween (G '' Icc r (r+T)) (G r) (G (r+T)) :=
    continuous_injective_interval_isArcBetween G hG.injective (by linarith)
  have hB : IsArcBetween (J '' Icc c (c+T)) (G r) (G (r+T)) := by
    rw [← hLeft,← hRight]
    exact continuous_injective_interval_isArcBetween J hJinj (by linarith)
  have hAi : (G '' Icc r (r+T)) \ {G r,G (r+T)} ⊆ φ '' Plane.openSquare 0 1 := by
    rintro z ⟨⟨x,hx,rfl⟩,hn⟩
    have hxl : r<x := lt_of_le_of_ne hx.1 (by
      intro he
      apply hn
      simp [he])
    have hxu : x<r+T := lt_of_le_of_ne hx.2 (by
      intro he
      apply hn
      simp [he])
    rw [hopen]
    exact ⟨(hStrip x ⟨hxl,hxu⟩).1,(hStrip x ⟨hxl,hxu⟩).2,(hBand x).1,(hBand x).2⟩
  have hBi : (J '' Icc c (c+T)) \ {G r,G (r+T)} ⊆ φ '' Plane.openSquare 0 1 := by
    rintro z ⟨⟨x,hx,rfl⟩,hn⟩
    have hxl : c<x := lt_of_le_of_ne hx.1 (by
      intro he
      apply hn
      rw [← hLeft]
      simp [he])
    have hxu : x<c+T := lt_of_le_of_ne hx.2 (by
      intro he
      apply hn
      rw [← hRight]
      simp [he])
    rw [hopen]
    exact ⟨hxl,hxu,(hBand r).1,(hBand r).2⟩
  obtain ⟨H,hHeq,hHimage,_⟩ := periodic_chart_crosscut_isotopy_of_interior_separation
    T hT φ hdeck (G '' Icc r (r+T)) (J '' Icc c (c+T)) (G r) (G (r+T)) hA hB ha hb hAi hBi
  have hzero : (fun z : Plane => z+Plane.mk (((0:ℤ×ℤ).1:ℝ)*T) (((0:ℤ×ℤ).2:ℝ)*T))=id := by
    funext z
    ext k
    fin_cases k <;> simp [Plane.mk]
  have hImage := hHimage (0:ℤ×ℤ)
  rw [hzero,image_id,image_id] at hImage
  exact ⟨H,hHeq,hImage⟩

#print axioms actual_terminal_single_band_has_periodic_straight_crosscut
