import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualPlanePointFixedNormalization

open Set Topology Schoenflies CurveComplex

/-- Actual terminal single-band geometry constructs a marked ambient graph
straightening. The rectangle is allowed to contain p; explicit normalization
fixes p. Neither raw puncture fixing nor a terminal graph is assumed. -/
theorem actual_terminal_single_band_has_marked_periodic_graph
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c d r : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) x, G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hFiber : {x : ℝ | G x 0=c}={r})
    (hStrip : ∀ x∈Ioo r (r+T), c<G x 0 ∧ G x 0<c+T)
    (hBand : ∀ x, d<G x 1 ∧ G x 1<d+T) (p : Plane) :
    ∃ P : AmbientIsotopy Plane, ∃ J : C(ℝ,Plane),
      (∀ t (i : ℤ×ℤ) z,
        P.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          P.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t, P.map (t,p)=p) ∧ P.finalMap '' range G=range J ∧
      (∀ x, J x 0=x) ∧
      (∀ (k : ℤ) x, J (x+(k:ℝ)*T)=J x+Plane.mk ((k:ℝ)*T) 0) := by
  obtain ⟨H,hHeq,hHimage⟩ := actual_terminal_single_band_has_whole_periodic_straightening
    G hG T c d r hT hp hFiber hStrip hBand
  obtain ⟨P,hP,hPFix,hPEq,_⟩ :=
    actual_equivariant_plane_isotopy_has_point_fixed_normalization H T p hHeq
  let h : ℝ := G r 1-H.finalMap p 1+p 1
  let J : C(ℝ,Plane) := ⟨fun x => Plane.mk x h,by fun_prop⟩
  have hPfinal (z : Plane) : P.finalMap z=H.finalMap z-H.finalMap p+p :=
    hP (⟨1,by norm_num⟩ : Interval) z
  have hImage : P.finalMap '' range G=range J := by
    ext z
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      have hz : H.finalMap (G x)∈range (fun x : ℝ => Plane.mk x (G r 1)) := by
        rw [← hHimage]
        exact mem_image_of_mem _ (mem_range_self x)
      obtain ⟨a,ha⟩ := hz
      refine ⟨a-H.finalMap p 0+p 0,?_⟩
      rw [hPfinal,← ha]
      ext k
      fin_cases k
      · rfl
      · rfl
    · rintro ⟨x,rfl⟩
      have hz : Plane.mk (x+H.finalMap p 0-p 0) (G r 1)∈H.finalMap '' range G := by
        rw [hHimage]
        exact mem_range_self _
      obtain ⟨_,⟨s,rfl⟩,hs⟩ := hz
      refine ⟨G s,mem_range_self s,?_⟩
      rw [hPfinal,hs]
      ext k
      fin_cases k
      · change x+H.finalMap p 0-p 0-H.finalMap p 0+p 0=x
        ring
      · rfl
  refine ⟨P,J,hPEq,hPFix,hImage,fun _ => rfl,?_⟩
  intro k x
  ext j
  fin_cases j <;> simp [J,Plane.mk]

#print axioms actual_terminal_single_band_has_marked_periodic_graph
