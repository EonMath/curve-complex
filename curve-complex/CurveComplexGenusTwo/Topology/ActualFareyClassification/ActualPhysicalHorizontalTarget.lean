import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedReferenceFiberShear
import CurveComplexGenusTwo.Topology.TorusStrip.ArcInterval

open Set Topology Schoenflies CurveComplex

/-- Choose an actual physical straight target avoiding the ENTIRE puncture
orbit. Its two fundamental fragments are actual compatible nondegenerate
straight segments, and their endpoints and winding are literal. -/
theorem actual_puncture_orbit_has_compatible_physical_horizontal_target
    (c r : ℝ) (p : Plane) :
    ∃ h : ℝ, ∃ L : C(ℝ,Plane),
      h=p 1+Real.pi ∧
      (∀ x, L x=Plane.mk (c+x-r) h) ∧ IsClosedEmbedding L ∧
      range L={z : Plane | z 1=h} ∧
      (∀ (k : ℤ) x, L (x+(k:ℝ)*(2*Real.pi))=
        L x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ),
        L x=L y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi)) → j=0) ∧
      Disjoint (range L)
        (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}) ∧
      L r=Plane.mk c h ∧
      L (r+Real.pi)=Plane.mk (c+Real.pi) h ∧
      L (r+2*Real.pi)=Plane.mk (c+2*Real.pi) h ∧
      IsArcBetween (segment ℝ (L r) (L (r+Real.pi))) (L r) (L (r+Real.pi)) ∧
      IsArcBetween (segment ℝ (L (r+Real.pi)) (L (r+2*Real.pi)))
        (L (r+Real.pi)) (L (r+2*Real.pi)) ∧
      segment ℝ (L r) (L (r+Real.pi)) ∩
        segment ℝ (L (r+Real.pi)) (L (r+2*Real.pi))={L (r+Real.pi)} := by
  let h := p 1+Real.pi
  let L : C(ℝ,Plane) := ⟨fun x => Plane.mk (c+x-r) h,by fun_prop⟩
  have hEmb : IsEmbedding L := by
    apply IsEmbedding.of_leftInverse (f:=fun z : Plane => z 0-c+r)
    · intro x
      change c+x-r-c+r=x
      ring
    · fun_prop
    · exact L.continuous
  have hRange : range L={z : Plane | z 1=h} := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      rfl
    · intro hz
      refine ⟨z 0-c+r,?_⟩
      ext k
      fin_cases k
      · change c+(z 0-c+r)-r=z 0
        ring
      · exact hz.symm
  have hClosed : IsClosedEmbedding L := ⟨hEmb,hRange.symm ▸ isClosed_eq (by fun_prop) continuous_const⟩
  have hEnd0 : L r=Plane.mk c h := by ext k; fin_cases k <;> simp [L,Plane.mk]
  have hEnd1 : L (r+Real.pi)=Plane.mk (c+Real.pi) h := by
    ext k; fin_cases k <;> simp [L,Plane.mk]
    ring
  have hEnd2 : L (r+2*Real.pi)=Plane.mk (c+2*Real.pi) h := by
    ext k; fin_cases k <;> simp [L,Plane.mk]
    ring
  have hNe01 : L r≠L (r+Real.pi) := hEmb.injective.ne (by linarith [Real.pi_pos])
  have hNe12 : L (r+Real.pi)≠L (r+2*Real.pi) := hEmb.injective.ne (by linarith [Real.pi_pos])
  refine ⟨h,L,rfl,fun _ => rfl,hClosed,hRange,?_,?_,?_,hEnd0,hEnd1,hEnd2,
    isArcBetween_segment hNe01,isArcBetween_segment hNe12,?_⟩
  · intro k x
    ext j
    fin_cases j <;> simp [L,Plane.mk]
    ring
  · intro x y i j he
    have hh := congrArg (fun z : Plane => z 1) he
    change h=h+(j:ℝ)*(2*Real.pi) at hh
    have hz : (j:ℝ)=0 := by nlinarith [Real.pi_pos]
    exact_mod_cast hz
  · apply disjoint_left.mpr
    rintro z ⟨x,rfl⟩ hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have he := congrArg (fun z : Plane => z 1) (mem_singleton_iff.mp hi)
    change p 1+Real.pi=p 1+(i.2:ℝ)*(2*Real.pi) at he
    have hh : (2:ℝ)*(i.2:ℝ)=1 := by nlinarith [Real.pi_pos]
    have hhZ : (2:ℤ)*i.2=1 := by exact_mod_cast hh
    omega
  · rw [hEnd0,hEnd1,hEnd2]
    ext z
    simp only [mem_inter_iff,mem_singleton_iff]
    constructor
    · rintro ⟨ha,hb⟩
      rw [segment_eq_image_lineMap] at ha hb
      obtain ⟨u,hu,he⟩ := ha
      obtain ⟨v,hv,hvE⟩ := hb
      have hz0 := congrArg (fun w : Plane => w 0) he
      have hz0' := congrArg (fun w : Plane => w 0) hvE
      simp [AffineMap.lineMap_apply,Plane.mk] at hz0 hz0'
      have hu1 : u=1 := by nlinarith [hu.2,hv.1,Real.pi_pos]
      simpa [hu1] using he.symm
    · intro hz
      rw [hz]
      exact ⟨right_mem_segment _ _ _,left_mem_segment _ _ _⟩

#print axioms actual_puncture_orbit_has_compatible_physical_horizontal_target
