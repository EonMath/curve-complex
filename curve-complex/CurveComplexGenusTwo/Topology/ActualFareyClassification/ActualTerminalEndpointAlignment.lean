import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualPhysicalHorizontalTarget
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualEquivariantSourcePreservation

open Set Topology Schoenflies CurveComplex

/-- The actual terminal source can have its two fundamental endpoints aligned
with an actual puncture-free physical horizontal target, by an ACTUAL marked
periodic ambient shear. The reference fiber and strict strip are preserved. -/
theorem actual_terminal_source_has_marked_physical_endpoint_alignment
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
    ∃ H : AmbientIsotopy Plane, ∃ G' : C(ℝ,Plane), ∃ h : ℝ,
      h=p 1+Real.pi ∧
      (∀ t (i : ℤ×ℤ),
        H.map (t,p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))=
          p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))) ∧
      (∀ t (i : ℤ×ℤ) z,
        H.map (t,z+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))=
          H.map (t,z)+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))) ∧
      (∀ x, G' x=H.finalMap (G x)) ∧
      (∀ x, G' x 0=G x 0) ∧ IsClosedEmbedding G' ∧
      (∀ (k : ℤ) x, G' (x+(k:ℝ)*(2*Real.pi))=
        G' x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ),
        G' x=G' y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi)) → j=0) ∧
      Disjoint (range G')
        (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}) ∧
      {t : ℝ | G' t 0=c}={r} ∧
      (∀ t∈Ioo r (r+2*Real.pi), c<G' t 0 ∧ G' t 0<c+2*Real.pi) ∧
      G' r=Plane.mk c h ∧ G' (r+2*Real.pi)=Plane.mk (c+2*Real.pi) h := by
  let h := p 1+Real.pi
  obtain ⟨ρ,hρ,H,hEq,hFix,hGrid,hOutside,hFirst⟩ :=
    actual_puncture_free_reference_has_marked_vertical_shear c (h-G r 1) p hpgrid
  obtain ⟨G',hG'Eq,hG',hG'period,hG'coll⟩ :=
    actual_equivariant_isotopy_preserves_normalized_source G hG (2*Real.pi) hp hc H hEq
  have hFirst' (x : ℝ) : G' x 0=G x 0 := by
    rw [hG'Eq]
    exact hFirst ⟨1,by norm_num⟩ (G x)
  have hr : G r 0=c := by
    have hh : r∈{t : ℝ | G t 0=c} := hFiber.symm ▸ mem_singleton r
    exact hh
  have hGr : G r=Plane.mk c (G r 1) := by
    ext k
    fin_cases k
    · exact hr
    · rfl
  have hEnd0 : G' r=Plane.mk c h := by
    rw [hG'Eq,hGr]
    have hh := hGrid ⟨1,by norm_num⟩ 0 (G r 1)
    simpa [AmbientIsotopy.finalMap] using hh
  have hEnd1 : G' (r+2*Real.pi)=Plane.mk (c+2*Real.pi) h := by
    have hh := hG'period 1 r
    simp only [Int.cast_one,one_mul] at hh
    rw [hh,hEnd0]
    ext k
    fin_cases k <;> simp [Plane.mk]
  have hAvoid : Disjoint (range G')
      (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}) := by
    apply disjoint_left.mpr
    rintro z ⟨x,rfl⟩ hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have he : G' x=p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)) :=
      mem_singleton_iff.mp hi
    obtain ⟨e,heMap⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
    have hh : G x=p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)) := by
      apply e.injective
      rw [heMap,heMap,hFix]
      exact (hG'Eq x).symm.trans he
    exact disjoint_left.mp hGM (mem_range_self x) (mem_iUnion.mpr ⟨i,hh⟩)
  refine ⟨H,G',h,rfl,hFix,hEq,hG'Eq,hFirst',hG',hG'period,hG'coll,hAvoid,?_,?_,hEnd0,hEnd1⟩
  · simpa only [hFirst'] using hFiber
  · intro t ht
    simpa only [hFirst'] using hStrip t ht

#print axioms actual_terminal_source_has_marked_physical_endpoint_alignment
