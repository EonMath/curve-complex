import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedSourceReducer
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalZeroDriftProof

open Set Topology Schoenflies CurveComplex

/-- REVIEW SCAFFOLD ONLY. The genuinely missing zero-drift reduction.
The finite quantity is the number of horizontal-reference events in one FIXED
parameter window, not the number of coordinate folds. A reducing ambient move
and renewed finite transverse data are conclusions, not certificates supplied
by the caller. This intermediate lemma is NOT a replacement original head. -/
theorem actual_horizontal_zero_drift_has_marked_crossing_reduction
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
  exact actual_horizontal_zero_drift_has_marked_crossing_reduction_verified
    G hG T c hT hp hc hfinite hcount htrans p hpgrid hGM

#print axioms actual_horizontal_zero_drift_has_marked_crossing_reduction
