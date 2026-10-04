import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTerminalSingleBandCrosscut
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTerminalReturningParameters

open Set Topology Schoenflies CurveComplex

/-- The genuine fundamental crosscut move straightens the WHOLE original
periodic line, not only a chosen subarc. -/
theorem actual_terminal_single_band_has_whole_periodic_straightening
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c d r : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) x, G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hFiber : {x : ℝ | G x 0=c}={r})
    (hStrip : ∀ x∈Ioo r (r+T), c<G x 0 ∧ G x 0<c+T)
    (hBand : ∀ x, d<G x 1 ∧ G x 1<d+T) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ) z,
        H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      H.finalMap '' range G=range (fun x : ℝ => Plane.mk x (G r 1)) := by
  obtain ⟨H,hHeq,hSingle⟩ := actual_terminal_single_band_has_periodic_straight_crosscut
    G hG T c d r hT hp hFiber hStrip hBand
  have hShift (k : ℤ) (z : Plane) :
      H.finalMap (z+Plane.mk ((k:ℝ)*T) 0)=H.finalMap z+Plane.mk ((k:ℝ)*T) 0 := by
    simpa only [AmbientIsotopy.finalMap,Int.cast_zero,zero_mul] using hHeq (⟨1,by norm_num⟩ : Interval) (k,0) z
  refine ⟨H,hHeq,?_⟩
  ext z
  constructor
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    obtain ⟨k,t,ht,hxt⟩ := actual_parameter_has_fundamental_window T r x hT
    have htmem : H.finalMap (G t)∈
        (fun x : ℝ => Plane.mk x (G r 1)) '' Icc c (c+T) := by
      rw [← hSingle]
      exact mem_image_of_mem _ (mem_image_of_mem _ ⟨ht.1,ht.2.le⟩)
    obtain ⟨u,hu,hU⟩ := htmem
    refine ⟨u+(k:ℝ)*T,?_⟩
    rw [hxt,hp,hShift,← hU]
    ext j
    fin_cases j <;> simp [Plane.mk]
  · rintro ⟨x,rfl⟩
    obtain ⟨k,u,hu,hxu⟩ := actual_parameter_has_fundamental_window T c x hT
    have hTarget : Plane.mk u (G r 1)∈H.finalMap '' (G '' Icc r (r+T)) := by
      rw [hSingle]
      exact ⟨u,⟨hu.1,hu.2.le⟩,rfl⟩
    obtain ⟨_,⟨s,hs,rfl⟩,hS⟩ := hTarget
    refine ⟨G (s+(k:ℝ)*T),mem_range_self _,?_⟩
    rw [hp,hShift,hS,hxu]
    ext j
    fin_cases j <;> simp [Plane.mk]

#print axioms actual_terminal_single_band_has_whole_periodic_straightening
