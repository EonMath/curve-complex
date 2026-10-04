import CurveComplexGenusTwo.Topology.FrontierCircle.SeamGluingProbe

open Set Topology unitInterval
namespace CurveComplex

theorem attached_band_zero_interior_probe
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : I × BandWidth → S) (hB : IsEmbedding B) (i j : Fin 4)
    (h0 : ∀ t, B (0,t) = D.square (squarePort D.radius D.radius_pos i t))
    (h1 : ∀ t, B (1,t) = D.square (squarePort D.radius D.radius_pos j t))
    (hmeet : Set.range B ∩ Set.range D.square =
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos i t)) ∪
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos j t))) :
    B (0,⟨0,by norm_num⟩) ∈ interior (Set.range D.square ∪ Set.range B) := by
  let L : BandWidth × I → S := fun z =>
    D.ends i (z.1,⟨-(z.2:ℝ),by constructor <;> linarith [z.2.property.1,z.2.property.2]⟩)
  let R : BandWidth × I → S := fun z =>
    B (⟨(z.2:ℝ)/2,by constructor <;> linarith [z.2.property.1,z.2.property.2]⟩,z.1)
  have hLC : Continuous L := (D.ends_embedded i).continuous.comp
    (continuous_fst.prodMk (((continuous_subtype_val.comp continuous_snd).neg).subtype_mk _))
  have hRC : Continuous R := hB.continuous.comp
    ((((continuous_subtype_val.comp continuous_snd).div_const 2).subtype_mk _).prodMk continuous_fst)
  have hLI : Function.Injective L := by
    intro z w he
    have hh := (D.ends_embedded i).injective he
    apply Prod.ext
    · exact congrArg (fun x : EndRectangle => x.1) hh
    · apply Subtype.ext
      have hv := congrArg (fun x : EndRectangle => (x.2:ℝ)) hh
      dsimp at hv
      exact neg_injective hv
  have hRI : Function.Injective R := by
    intro z w he
    have hh := hB.injective he
    apply Prod.ext
    · exact congrArg Prod.snd hh
    · apply Subtype.ext
      have hv := congrArg (fun x : I × BandWidth => (x.1:ℝ)) hh
      dsimp at hv
      linarith
  have hLR (t : BandWidth) : L (t,0) = R (t,0) := by
    change D.ends i (t,⟨-(0:I),_⟩) = B (⟨(0:I)/2,_⟩,t)
    simpa using (D.ends_seam i t).trans (h0 t).symm
  have hLsub : Set.range L ⊆ Set.range D.square := by
    rintro z ⟨w,rfl⟩
    apply (D.ends_square i _).mpr
    change -(w.2:ℝ) ≤ 0
    exact neg_nonpos.mpr w.2.property.1
  have hRsub : Set.range R ⊆ Set.range B := by
    rintro z ⟨w,rfl⟩
    exact Set.mem_range_self _
  have hLRmeet : Set.range L ∩ Set.range R = Set.range (fun t => L (t,0)) := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨z,rfl⟩,w,he⟩
      have hx : L z ∈ Set.range B ∩ Set.range D.square :=
        ⟨hRsub ⟨w,he⟩,hLsub (Set.mem_range_self z)⟩
      rw [hmeet] at hx
      rcases hx with ⟨v,hv⟩ | ⟨v,hv⟩
      · have he' : L z = D.ends i (v,⟨0,by norm_num⟩) :=
          hv.symm.trans (D.ends_seam i v).symm
        have hh := (D.ends_embedded i).injective he'
        have hz0 := congrArg (fun x : EndRectangle => (x.2:ℝ)) hh
        dsimp at hz0
        have hz : z.2 = 0 := Subtype.ext (neg_eq_zero.mp hz0)
        refine ⟨z.1,?_⟩
        rw [← hz]
      · have hb : R w = B (1,v) := he.trans (hv.symm.trans (h1 v).symm)
        have hh := hB.injective hb
        have hw := congrArg (fun x : I × BandWidth => (x.1:ℝ)) hh
        dsimp at hw
        norm_num at hw
        exfalso
        linarith [w.2.property.2]
    · rintro x ⟨t,rfl⟩
      exact ⟨Set.mem_range_self _,⟨(t,0),(hLR t).symm⟩⟩
  have hin := glued_half_rectangles_seam_interior_probe L R
    (hLC.isClosedEmbedding hLI).isEmbedding (hRC.isClosedEmbedding hRI).isEmbedding
    hLR hLRmeet ⟨0,by norm_num⟩ (by norm_num) (by norm_num)
  have hsub : Set.range L ∪ Set.range R ⊆ Set.range D.square ∪ Set.range B :=
    Set.union_subset_union hLsub hRsub
  have hfinal := interior_mono hsub hin
  have he : L (⟨0,by norm_num⟩,0) = B (0,⟨0,by norm_num⟩) := by
    simpa [R] using hLR ⟨0,by norm_num⟩
  rwa [he] at hfinal

theorem attached_band_one_interior_probe
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : I × BandWidth → S) (hB : IsEmbedding B) (i j : Fin 4)
    (h0 : ∀ t, B (0,t) = D.square (squarePort D.radius D.radius_pos i t))
    (h1 : ∀ t, B (1,t) = D.square (squarePort D.radius D.radius_pos j t))
    (hmeet : Set.range B ∩ Set.range D.square =
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos i t)) ∪
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos j t))) :
    B (1,⟨0,by norm_num⟩) ∈ interior (Set.range D.square ∪ Set.range B) := by
  let e : (I × BandWidth) ≃ₜ (I × BandWidth) :=
    unitInterval.symmHomeomorph.prodCongr (Homeomorph.refl _)
  let C : I × BandWidth → S := B ∘ e
  have hC : IsEmbedding C := hB.comp e.isEmbedding
  have hrange : Set.range C = Set.range B := by
    change Set.range (B ∘ e) = _
    rw [Set.range_comp,e.surjective.range_eq,Set.image_univ]
  have hC0 (t) : C (0,t) = D.square (squarePort D.radius D.radius_pos j t) := by
    simpa [C,e] using h1 t
  have hC1 (t) : C (1,t) = D.square (squarePort D.radius D.radius_pos i t) := by
    simpa [C,e] using h0 t
  have hCm : Set.range C ∩ Set.range D.square =
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos j t)) ∪
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos i t)) := by
    rw [hrange,hmeet,Set.union_comm]
  have hh := attached_band_zero_interior_probe D C hC j i hC0 hC1 hCm
  rw [hrange] at hh
  simpa [C,e] using hh

#print axioms attached_band_one_interior_probe
#print axioms attached_band_zero_interior_probe
end CurveComplex
