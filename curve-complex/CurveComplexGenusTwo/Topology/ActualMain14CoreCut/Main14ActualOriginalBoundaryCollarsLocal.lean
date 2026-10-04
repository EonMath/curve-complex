import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualCommonBandMotionSourceLocal
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]
set_option maxHeartbeats 3000000

-- Actual collars of BOTH original outer components, with their literal parametrizations.
example (M : HyperellipticModel E S) (U : Set E)
    (T : Circle × Interval ≃ₜ U) :
    ∃ e₀ e₁ : C(Set.Ioo (-1:ℝ) 1 × Circle,E),
      Topology.IsOpenEmbedding e₀ ∧ Topology.IsOpenEmbedding e₁ ∧
      (∀ z, e₀ (⟨0,by norm_num⟩,z) = (T (z,0)).val) ∧
      (∀ z, e₁ (⟨0,by norm_num⟩,z) = (T (z,1)).val) := by
  audit_main14_base3
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    have hcollar (c : Curve E) : ∃ e : C(Set.Ioo (-1:ℝ) 1 × Circle,E),
        Topology.IsOpenEmbedding e ∧ ∀ z, e (⟨0,by norm_num⟩,z) = c.map z := by
      rcases LocalSurgery.embedded_circle_annular_collar_or_local_reflection E c with hc | ⟨x,⟨W⟩⟩
      · exact hc
      · exact False.elim (GenusOrientationCandidate.no_local_reflection_witness 2 M.genusTwo x
          (GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) W)
    let c₀ : Curve E := ⟨fun z => (T (z,0)).val,
      Topology.IsEmbedding.subtypeVal.comp (T.isEmbedding.comp (isEmbedding_prodMkLeft 0))⟩
    let c₁ : Curve E := ⟨fun z => (T (z,1)).val,
      Topology.IsEmbedding.subtypeVal.comp (T.isEmbedding.comp (isEmbedding_prodMkLeft 1))⟩
    obtain ⟨e₀,he₀,hc₀⟩ := hcollar c₀
    obtain ⟨e₁,he₁,hc₁⟩ := hcollar c₁
    exact ⟨e₀,e₁,he₀,he₁,hc₀,hc₁⟩

-- Actual uniformly restricted outer collars: mutually disjoint and clear of the common band.
example (M : HyperellipticModel E S) (U W : Set E)
    (T : Circle × Interval ≃ₜ U) (A : Circle × Interval ≃ₜ W)
    (hWdis : Disjoint W (Set.range (fun z : Circle => (T (z,0)).val) ∪
      Set.range (fun z : Circle => (T (z,1)).val))) :
    ∃ e₀ e₁ : C(Set.Ioo (-1:ℝ) 1 × Circle,E), ∃ ε₀ ε₁ : ℝ,
      Topology.IsOpenEmbedding e₀ ∧ Topology.IsOpenEmbedding e₁ ∧
      (∀ z, e₀ (⟨0,by norm_num⟩,z) = (T (z,0)).val) ∧
      (∀ z, e₁ (⟨0,by norm_num⟩,z) = (T (z,1)).val) ∧
      0 < ε₀ ∧ ε₀ < 1 ∧ 0 < ε₁ ∧ ε₁ < 1 ∧
      Disjoint (e₀ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₀})
        (e₁ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₁}) ∧
      Disjoint (e₀ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₀}) W ∧
      Disjoint (e₁ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₁}) W := by
  audit_main14_base3
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    letI : CompactSpace W := A.compactSpace
    have hWclosed : IsClosed W := by
      have hh := (isCompact_univ : IsCompact (Set.univ : Set W)).image
        (continuous_subtype_val : Continuous (Subtype.val : W → E))
      have he : (Subtype.val : W → E) '' Set.univ = W := by
        rw [Set.image_univ,Subtype.range_coe_subtype]
        rfl
      exact (he ▸ hh).isClosed
    let c₀ : Curve E := ⟨fun z => (T (z,0)).val,
      Topology.IsEmbedding.subtypeVal.comp (T.isEmbedding.comp (isEmbedding_prodMkLeft 0))⟩
    let c₁ : Curve E := ⟨fun z => (T (z,1)).val,
      Topology.IsEmbedding.subtypeVal.comp (T.isEmbedding.comp (isEmbedding_prodMkLeft 1))⟩
    have hd : Disjoint c₀.image c₁.image := by
      apply Set.disjoint_left.mpr
      rintro x ⟨z,hz⟩ ⟨w,hw⟩
      have hh := T.injective (Subtype.ext (hz.trans hw.symm))
      have hu := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
      norm_num at hu
    have hc₀ : IsClosed c₀.image := by
      simpa [Curve.image] using (isCompact_univ.image c₀.embedded.continuous).isClosed
    have hc₁ : IsClosed c₁.image := by
      simpa [Curve.image] using (isCompact_univ.image c₁.embedded.continuous).isClosed
    obtain ⟨O₀,O₁,hO₀,hO₁,hcO₀,hcO₁,hOdis⟩ := normal_separation hc₀ hc₁ hd
    let V₀ := O₀ ∩ Wᶜ
    let V₁ := O₁ ∩ Wᶜ
    have hV₀ : IsOpen V₀ := hO₀.inter hWclosed.isOpen_compl
    have hV₁ : IsOpen V₁ := hO₁.inter hWclosed.isOpen_compl
    have hcV₀ (z : Circle) : c₀.map z ∈ V₀ := by
      refine ⟨hcO₀ (Set.mem_range_self z),?_⟩
      intro hw
      exact Set.disjoint_left.mp hWdis hw (Or.inl (Set.mem_range_self z))
    have hcV₁ (z : Circle) : c₁.map z ∈ V₁ := by
      refine ⟨hcO₁ (Set.mem_range_self z),?_⟩
      intro hw
      exact Set.disjoint_left.mp hWdis hw (Or.inr (Set.mem_range_self z))
    have hcollar (c : Curve E) : ∃ e : C(Set.Ioo (-1:ℝ) 1 × Circle,E),
        Topology.IsOpenEmbedding e ∧ ∀ z, e (⟨0,by norm_num⟩,z) = c.map z := by
      rcases LocalSurgery.embedded_circle_annular_collar_or_local_reflection E c with hc | ⟨x,⟨F⟩⟩
      · exact hc
      · exact False.elim (GenusOrientationCandidate.no_local_reflection_witness 2 M.genusTwo x
          (GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) F)
    obtain ⟨e₀,he₀,hcenter₀⟩ := hcollar c₀
    obtain ⟨e₁,he₁,hcenter₁⟩ := hcollar c₁
    -- Uniform restriction is the actual G3 compact-circle clearance argument.
    have hclear (e : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (O : Set E)
        (hO : IsOpen O) (hcenter : ∀ z, e (⟨0,by norm_num⟩,z) ∈ O) :
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
          ∀ w : Set.Ioo (-1:ℝ) 1, |(w:ℝ)| < ε → ∀ z : Circle, e (w,z) ∈ O := by
      let w0 : Set.Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
      let Ω := e ⁻¹' O
      have hΩ : IsOpen Ω := hO.preimage e.continuous
      have hbase : ({w0} : Set (Set.Ioo (-1:ℝ) 1)) ×ˢ (Set.univ : Set Circle) ⊆ Ω := by
        rintro ⟨w,z⟩ ⟨hw,_⟩
        have hh : w = w0 := hw
        subst w
        exact hcenter z
      obtain ⟨P,Q,hP,hQ,h0,hall,hPQ⟩ :=
        generalized_tube_lemma isCompact_singleton
          (isCompact_univ : IsCompact (Set.univ : Set Circle)) hΩ hbase
      have hw0 : w0 ∈ P := h0 (Set.mem_singleton w0)
      obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hP.mem_nhds hw0)
      let ε := min δ (1/2)
      have hε : 0 < ε := lt_min hδ (by norm_num)
      refine ⟨ε,hε,lt_of_le_of_lt (min_le_right _ _) (by norm_num),?_⟩
      intro w hw z
      have hwd : |(w:ℝ)| < δ := lt_of_lt_of_le hw (min_le_left _ _)
      have hwP : w ∈ P := hball (by
        change dist (w:ℝ) (w0:ℝ) < δ
        simpa [w0,Real.dist_eq] using hwd)
      exact hPQ ⟨hwP,hall (Set.mem_univ z)⟩
    obtain ⟨ε₀,hε₀,hε₀one,hclear₀⟩ := hclear e₀ V₀ hV₀ (fun z => by rw [hcenter₀]; exact hcV₀ z)
    obtain ⟨ε₁,hε₁,hε₁one,hclear₁⟩ := hclear e₁ V₁ hV₁ (fun z => by rw [hcenter₁]; exact hcV₁ z)
    refine ⟨e₀,e₁,ε₀,ε₁,he₀,he₁,hcenter₀,hcenter₁,hε₀,hε₀one,hε₁,hε₁one,?_,?_,?_⟩
    · apply Set.disjoint_left.mpr
      rintro x ⟨p,hp,hpe⟩ ⟨q,hq,hqe⟩
      have h0 := (hclear₀ p.1 hp p.2).1
      have h1 := (hclear₁ q.1 hq q.2).1
      rw [hpe] at h0
      rw [hqe] at h1
      exact Set.disjoint_left.mp hOdis h0 h1
    · apply Set.disjoint_left.mpr
      rintro x ⟨p,hp,rfl⟩ hw
      exact (hclear₀ p.1 hp p.2).2 hw
    · apply Set.disjoint_left.mpr
      rintro x ⟨p,hp,rfl⟩ hw
      exact (hclear₁ p.1 hp p.2).2 hw

end CurveComplex.HyperellipticModel
