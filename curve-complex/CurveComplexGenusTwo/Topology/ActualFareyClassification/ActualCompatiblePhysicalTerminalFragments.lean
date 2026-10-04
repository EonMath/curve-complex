import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualInteriorFiberMarkedShear

open Set Topology Schoenflies CurveComplex

/-- Construct actual matching physical endpoints for the terminal source's two
SHORT fragments. Both marked shears are ACTUAL; no endpoint-alignment, target,
isotopy, finite-intersection, or fragmentation certificate is supplied. -/
theorem actual_terminal_source_has_compatible_physical_fragments
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (c r : ℝ) (p : Plane)
    (hp : ∀ (k : ℤ) x, G (x+(k:ℝ)*(2*Real.pi))=
      G x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0)
    (hc : ∀ (x y : ℝ) (i j : ℤ),
      G x=G y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi)) → j=0)
    (hpgrid : ∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠c)
    (hGM : Disjoint (range G)
      (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}))
    (hFiber : {t : ℝ | G t 0=c}={r})
    (hStrip : ∀ t∈Ioo r (r+2*Real.pi), c<G t 0 ∧ G t 0<c+2*Real.pi) :
    ∃ H : AmbientIsotopy Plane, ∃ G₂ : C(ℝ,Plane), ∃ b s h : ℝ,
      h=p 1+Real.pi ∧ c<b ∧ b<c+2*Real.pi ∧ s∈Ioo r (r+2*Real.pi) ∧
      (∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠b) ∧
      (∀ t (i : ℤ×ℤ),
        H.map (t,p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))=
          p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))) ∧
      (∀ t (i : ℤ×ℤ) z,
        H.map (t,z+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))=
          H.map (t,z)+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))) ∧
      (∀ x, G₂ x=H.finalMap (G x)) ∧
      (∀ x, G₂ x 0=G x 0) ∧ IsClosedEmbedding G₂ ∧
      (∀ (k : ℤ) x, G₂ (x+(k:ℝ)*(2*Real.pi))=
        G₂ x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ),
        G₂ x=G₂ y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi)) → j=0) ∧
      Disjoint (range G₂)
        (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}) ∧
      {t : ℝ | G₂ t 0=c}={r} ∧
      (∀ t∈Ioo r (r+2*Real.pi), c<G₂ t 0 ∧ G₂ t 0<c+2*Real.pi) ∧
      G₂ r=Plane.mk c h ∧ G₂ s=Plane.mk b h ∧
      G₂ (r+2*Real.pi)=Plane.mk (c+2*Real.pi) h ∧
      s-r<2*Real.pi ∧ r+2*Real.pi-s<2*Real.pi ∧
      IsArcBetween (G₂ '' Icc r s) (G₂ r) (G₂ s) ∧
      IsArcBetween (G₂ '' Icc s (r+2*Real.pi)) (G₂ s) (G₂ (r+2*Real.pi)) ∧
      IsArcBetween (segment ℝ (G₂ r) (G₂ s)) (G₂ r) (G₂ s) ∧
      IsArcBetween (segment ℝ (G₂ s) (G₂ (r+2*Real.pi))) (G₂ s) (G₂ (r+2*Real.pi)) := by
  obtain ⟨P,G₁,h,hHeight,hPFix,hPEq,hG₁Eq,hFirst₁,hG₁,hPeriod₁,hColl₁,hAvoid₁,
      hFiber₁,hStrip₁,hLeft₁,hRight₁⟩ :=
    actual_terminal_source_has_marked_physical_endpoint_alignment G hG c r p hp hc hpgrid hGM hFiber hStrip
  have hLeftFirst : G₁ r 0=c := congrArg (fun z : Plane => z 0) hLeft₁
  have hRightFirst : G₁ (r+2*Real.pi) 0=c+2*Real.pi :=
    congrArg (fun z : Plane => z 0) hRight₁
  obtain ⟨b,s,hcb,hbc,hs,hGs,hbp,hbcGrid⟩ :=
    actual_terminal_source_has_puncture_free_interior_fiber G₁ c r p hLeftFirst hRightFirst
  obtain ⟨J,hJEq,hJFix,hJRef,hJMove,hJFirst⟩ :=
    actual_interior_fiber_has_marked_shear_fixing_reference b c (h-G₁ s 1) p hbp hbcGrid
  obtain ⟨G₂,hG₂Eq,hG₂,hPeriod₂,hColl₂⟩ :=
    actual_equivariant_isotopy_preserves_normalized_source G₁ hG₁ (2*Real.pi) hPeriod₁ hColl₁ J hJEq
  have hFirst₂ (x : ℝ) : G₂ x 0=G₁ x 0 := by
    rw [hG₂Eq]
    exact hJFirst ⟨1,by norm_num⟩ (G₁ x)
  have hLeft₂ : G₂ r=Plane.mk c h := by
    rw [hG₂Eq,hLeft₁]
    simpa [AmbientIsotopy.finalMap] using hJRef ⟨1,by norm_num⟩ 0 h
  have hRight₂ : G₂ (r+2*Real.pi)=Plane.mk (c+2*Real.pi) h := by
    rw [hG₂Eq,hRight₁]
    simpa [AmbientIsotopy.finalMap] using hJRef ⟨1,by norm_num⟩ 1 h
  have hMiddle₂ : G₂ s=Plane.mk b h := by
    have hMid : G₁ s=Plane.mk b (G₁ s 1) := by
      ext k
      fin_cases k
      · exact hGs
      · rfl
    rw [hG₂Eq,hMid]
    simpa [AmbientIsotopy.finalMap] using hJMove ⟨1,by norm_num⟩ 0 (G₁ s 1)
  have hAvoid₂ : Disjoint (range G₂)
      (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}) := by
    apply disjoint_left.mpr
    rintro z ⟨x,rfl⟩ hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have he : G₂ x=p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)) :=
      mem_singleton_iff.mp hi
    obtain ⟨e,heMap⟩ := J.homeomorphism_at ⟨1,by norm_num⟩
    have hh : G₁ x=p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)) := by
      apply e.injective
      rw [heMap,heMap,hJFix]
      exact (hG₂Eq x).symm.trans he
    exact disjoint_left.mp hAvoid₁ (mem_range_self x) (mem_iUnion.mpr ⟨i,hh⟩)
  have hNe₁ : G₂ r≠G₂ s := hG₂.injective.ne (ne_of_lt hs.1)
  have hNe₂ : G₂ s≠G₂ (r+2*Real.pi) := hG₂.injective.ne (ne_of_lt hs.2)
  refine ⟨P.compose J,G₂,b,s,h,hHeight,hcb,hbc,hs,hbp,?_,?_,?_,?_,hG₂,hPeriod₂,hColl₂,hAvoid₂,
    ?_,?_,hLeft₂,hMiddle₂,hRight₂,by linarith [hs.2],by linarith [hs.1],
    continuous_injective_interval_isArcBetween G₂ hG₂.injective hs.1,
    continuous_injective_interval_isArcBetween G₂ hG₂.injective hs.2,
    isArcBetween_segment hNe₁,isArcBetween_segment hNe₂⟩
  · intro t i
    change J.map (t,P.map (t,p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))))=_
    rw [hPFix,hJFix]
  · intro t i z
    change J.map (t,P.map (t,z+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))))=_
    rw [hPEq,hJEq]
    rfl
  · intro x
    rw [hG₂Eq,hG₁Eq,AmbientIsotopy.compose_finalMap]
    rfl
  · intro x
    exact (hFirst₂ x).trans (hFirst₁ x)
  · simpa only [hFirst₂] using hFiber₁
  · intro t ht
    simpa only [hFirst₂] using hStrip₁ t ht

#print axioms actual_terminal_source_has_compatible_physical_fragments
