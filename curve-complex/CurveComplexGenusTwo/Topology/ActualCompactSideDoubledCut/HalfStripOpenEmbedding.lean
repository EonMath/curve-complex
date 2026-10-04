import CurveComplexGenusTwo.Topology.ActualCompactSideDoubledCut.RawCompactCutQuotient

open Set Topology CurveComplex

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

variable {S : Type} [TopologicalSpace S] {n : ℕ}

private abbrev HalfWidth := Set.Icc (0 : ℝ) 1
private abbrev FullWidth := Set.Icc (-1 : ℝ) 1
private abbrev HalfBand := Interval × HalfWidth
private abbrev FullBand := Interval × FullWidth

def halfOpen : Set HalfBand := {z | (z.2 : ℝ) < 1}

theorem halfOpen_isOpen : IsOpen halfOpen := by
  exact isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const

def halfRaw (E : Fin n → C(FullBand, S)) (i : Fin n) (b : Bool)
    (z : HalfBand) : RawCut E := Sum.inr ⟨i,b,z⟩

def halfCut (E : Fin n → C(FullBand, S)) (i : Fin n) (b : Bool)
    (z : HalfBand) : CutQuotient E := Quotient.mk (rawSetoid E) (halfRaw E i b z)

theorem halfRaw_open_range (E : Fin n → C(FullBand, S))
    (i : Fin n) (b : Bool) (V : Set HalfBand) (hV : IsOpen V) :
    IsOpen (halfRaw E i b '' V) := by
  have h : IsOpen
    ((Sum.inr : (Σ _i : Fin n, Σ _b : Bool, HalfBand) → RawCut E) ''
      ((fun v : Σ _b : Bool, HalfBand => (⟨i,v⟩ :
      Σ _i : Fin n, Σ _b : Bool, HalfBand)) ''
      ((fun z : HalfBand => (⟨b,z⟩ : Σ _b : Bool, HalfBand)) '' V))) :=
    isOpenMap_inr _ (isOpenMap_sigmaMk _ (isOpenMap_sigmaMk _ hV))
  simp only [Set.image_image] at h
  exact h

theorem halfRaw_class_singleton (E : Fin n → C(FullBand, S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) (z : HalfBand)
    (hz : z ∈ halfOpen) (r : RawCut E)
    (hr : rawRel E r (halfRaw E i b z)) : r = halfRaw E i b z := by
  rcases hr with h | ⟨h,hoff⟩
  · exact h
  rcases r with y | y
  · have hw : (-1 : ℝ) < (signedWidth b z.2).val ∧
        (signedWidth b z.2).val < 1 := by
      change (z.2 : ℝ) < 1 at hz
      cases b <;> dsimp [signedWidth] <;> constructor <;>
        nlinarith [z.2.property.1]
    have hmem : E i (z.1, signedWidth b z.2) ∈ bandInterior E i :=
      ⟨(z.1, signedWidth b z.2), hw, rfl⟩
    have hnot : y.val ∉ bandInterior E i := by
      intro hy
      exact y.property (Set.mem_iUnion.mpr ⟨i, hy⟩)
    change y.val = E i (z.1, signedWidth b z.2) at h
    exact False.elim (hnot (h.symm ▸ hmem))
  · exact congrArg Sum.inr
      (right_projection_injective_off_centers E hemb hdisjoint h hoff)

theorem halfCut_injective (E : Fin n → C(FullBand, S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) :
    Function.Injective (fun z : ↥halfOpen => halfCut E i b z.val) := by
  intro z w h
  have hr := Quotient.exact h
  have heq := halfRaw_class_singleton E hemb hdisjoint i b w.val w.property
    (halfRaw E i b z.val) hr
  apply Subtype.ext
  have heq' := Sum.inr.inj heq
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using heq'

theorem halfCut_openMap (E : Fin n → C(FullBand, S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) :
    IsOpenMap (fun z : ↥halfOpen => halfCut E i b z.val) := by
  intro V hV
  obtain ⟨U, hU, hVeq⟩ := isOpen_induced_iff.mp hV
  have hUopen : IsOpen (U ∩ halfOpen) := hU.inter halfOpen_isOpen
  apply isOpen_coinduced.mpr
  have heq : (Quotient.mk (rawSetoid E) : RawCut E → CutQuotient E) ⁻¹'
      ((fun z : ↥halfOpen => halfCut E i b z.val) '' V) =
      halfRaw E i b '' (U ∩ halfOpen) := by
    ext r
    constructor
    · rintro ⟨z,hz,hq⟩
      have hr := (rawSetoid E).symm (Quotient.exact hq)
      have heqr := halfRaw_class_singleton E hemb hdisjoint i b z.val z.property r hr
      refine ⟨z.val, ?_, heqr.symm⟩
      change z.val ∈ U ∩ halfOpen
      exact ⟨by simpa [← hVeq] using hz, z.property⟩
    · rintro ⟨z, ⟨hzU,hzO⟩, rfl⟩
      exact ⟨⟨z,hzO⟩, by simpa [← hVeq] using hzU, rfl⟩
  change IsOpen ((Quotient.mk (rawSetoid E) : RawCut E → CutQuotient E) ⁻¹'
      ((fun z : ↥halfOpen => halfCut E i b z.val) '' V))
  rw [heq]
  exact halfRaw_open_range E i b _ hUopen

theorem halfCut_openEmbedding (E : Fin n → C(FullBand, S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (b : Bool) :
    Topology.IsOpenEmbedding (fun z : ↥halfOpen => halfCut E i b z.val) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_quotient_mk'.comp
      (continuous_inr.comp
        (continuous_sigmaMk.comp
          (continuous_sigmaMk.comp continuous_subtype_val)))
  · exact halfCut_injective E hemb hdisjoint i b
  · exact halfCut_openMap E hemb hdisjoint i b

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
