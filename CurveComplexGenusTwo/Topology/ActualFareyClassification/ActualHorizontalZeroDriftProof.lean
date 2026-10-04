import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalRenewedFixedWindowReducer
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalPunctureReferenceNormalization
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalReferenceTranslationTransversality

open Set Topology Schoenflies CurveComplex

theorem actual_horizontal_zero_drift_has_marked_crossing_reduction_verified
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hfinite : {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.Finite)
    (hcount : 0<{t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.ncard)
    (htrans : ∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) → q 1=c+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 1=c+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
    (p : Plane) (hpgrid : ∀ i : ℤ, p 1+(i:ℝ)*T≠c)
    (hGM : Disjoint (range G)
      (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)})) :
    ∃ K P : AmbientIsotopy Plane, ∃ G2 : C(ℝ,Plane), ∃ c' : ℝ,
      c'=c-K.finalMap p 1+p 1 ∧
      (∀ x, G2 x=P.finalMap (G x)) ∧
      (∀ t (i : ℤ×ℤ), P.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ) z, P.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        P.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      IsClosedEmbedding G2 ∧
      (∀ (k : ℤ) (x : ℝ), G2 (x+(k:ℝ)*T)=G2 x+Plane.mk ((k:ℝ)*T) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ), G2 x=G2 y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0) ∧
      (∀ i : ℤ, p 1+(i:ℝ)*T≠c') ∧
      Disjoint (range G2) (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)}) ∧
      {t : Ico 0 (0+T) | ∃ i : ℤ, G2 t.val 1=c'+(i:ℝ)*T}.Finite ∧
      {t : Ico 0 (0+T) | ∃ i : ℤ, G2 t.val 1=c'+(i:ℝ)*T}.ncard <
        {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.ncard ∧
      (∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G2 x+Plane.mk 0 ((j:ℝ)*T))) → q 1=c'+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 1=c'+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G2 x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
 := by
  obtain ⟨H,hHeq,G1,hG1Eq,hG1,hp1,hc1,hFinite1,hFixedDrop1,hTrans1⟩ :=
    actual_horizontal_positive_count_has_renewed_fixed_window_reducer G hG T c hT hp hc hfinite hcount htrans p hpgrid hGM
  obtain ⟨K,P,hKG,hPfix,hPeq,hPFinal,hReference,hImageGM⟩ :=
    actual_move_has_horizontal_puncture_free_translated_reference G hG T c hT hp hc p hGM H hHeq
  obtain ⟨G2,hG2Eq,hG2,hp2,hc2⟩ := actual_equivariant_isotopy_preserves_normalized_source G hG T hp hc P hPeq
  let d : Plane := -K.finalMap p+p
  let c' := c+d 1
  have hc' : c'=c-K.finalMap p 1+p 1 := by
    change c+(-K.finalMap p+p) 1=c-K.finalMap p 1+p 1
    change c+(-K.finalMap p 1+p 1)=c-K.finalMap p 1+p 1
    ring
  have hTranslated (x : ℝ) : G2 x=G1 x+d := by
    rw [hG2Eq,hPFinal,hG1Eq]
    dsimp [d]
    abel
  have hGrid : {t : Ico 0 (0+T) | ∃ i : ℤ, G2 t.val 1=c'+(i:ℝ)*T}=
      {t : Ico 0 (0+T) | ∃ i : ℤ, G1 t.val 1=c+(i:ℝ)*T} := by
    ext t
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨i,?_⟩
      rw [hTranslated] at hi
      change G1 t.val 1+d 1=(c+d 1)+(i:ℝ)*T at hi
      linarith
    · rintro ⟨i,hi⟩
      refine ⟨i,?_⟩
      rw [hTranslated]
      change G1 t.val 1+d 1=(c+d 1)+(i:ℝ)*T
      linarith
  have hRange : range G2=P.finalMap '' range G := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨G x,mem_range_self _,(hG2Eq x).symm⟩
    · rintro ⟨w,⟨x,rfl⟩,he⟩
      exact ⟨x,(hG2Eq x).trans he⟩
  have hTrans2 := actual_translation_transports_horizontal_family_axis_charts G1 T c d hTrans1
  refine ⟨K,P,G2,c',hc',hG2Eq,hPfix,hPeq,hG2,hp2,hc2,?_,?_,?_,?_,?_⟩
  · simpa only [hc'] using hReference
  · rwa [hRange]
  · rw [hGrid]; exact hFinite1
  · rw [hGrid]; exact hFixedDrop1
  · simpa only [hTranslated] using hTrans2


#print axioms actual_horizontal_zero_drift_has_marked_crossing_reduction_verified
