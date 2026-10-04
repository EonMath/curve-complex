import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedBandRetainingVerticalReducer

open Set Topology Schoenflies CurveComplex

/-- Actual source-driven Nat descent on the FIXED quotient window. Every reducing move, renewed source and
translated puncture-free reference are CONSTRUCTED; no iteration or descent
certificate is a hypothesis. The final ambient isotopy fixes all puncture lifts. -/
theorem actual_marked_vertical_finite_descent_retains_horizontal_band
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c d : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hBand : ∀ x, d<G x 1 ∧ G x 1<d+T)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (htrans : ∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) → q 0=c+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 0=c+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
    (p : Plane) (hpgrid : ∀ i : ℤ, p 0+(i:ℝ)*T≠c)
    (hGM : Disjoint (range G)
      (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)})) :
    ∃ P : AmbientIsotopy Plane, ∃ Gf : C(ℝ,Plane), ∃ cf df : ℝ,
      (∀ x, Gf x=P.finalMap (G x)) ∧
      (∀ t (i : ℤ×ℤ), P.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ) z, P.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        P.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      IsClosedEmbedding Gf ∧
      (∀ (k : ℤ) (x : ℝ), Gf (x+(k:ℝ)*T)=Gf x+Plane.mk ((k:ℝ)*T) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ), Gf x=Gf y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0) ∧
      (∀ x, df<Gf x 1 ∧ Gf x 1<df+T) ∧
      (∀ i : ℤ, p 0+(i:ℝ)*T≠cf) ∧
      Disjoint (range Gf) (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)}) ∧
      {t : ℝ | Gf t 0=cf}.Finite ∧ {t : ℝ | Gf t 0=cf}.ncard ≤ 1 ∧
      {t : Ico 0 (0+T) | ∃ i : ℤ, Gf t.val 0=cf+(i:ℝ)*T}.ncard ≤
        {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 0=c+(i:ℝ)*T}.ncard ∧
      (∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => Gf x+Plane.mk 0 ((j:ℝ)*T))) → q 0=cf+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 0=cf+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => Gf x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
 := by
  generalize hn : {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 0=c+(i:ℝ)*T}.ncard=n
  induction n using Nat.strong_induction_on generalizing G c d with
  | h n ih =>
    by_cases hcount : 1<{t : ℝ | G t 0=c}.ncard
    · obtain ⟨K,Q,G2,c2,d2,_,_,hG2Eq,hQfix,hQeq,hG2,hp2,hc2,hBand2,hReference2,hGM2,hFinite2,_hDrop2,hFixedDrop2,hTrans2⟩ :=
        actual_marked_vertical_reducing_source_retains_translated_horizontal_band G hG T c d hT hp hc hBand hfinite hcount htrans p hpgrid hGM
      have hlt : {t : Ico 0 (0+T) | ∃ i : ℤ, G2 t.val 0=c2+(i:ℝ)*T}.ncard<n := by rwa [hn] at hFixedDrop2
      obtain ⟨R,Gf,cf,df,hGfEq,hRfix,hReq,hGf,hpf,hcf,hBandf,hReferencef,hGMf,hFinitef,hFinalCount,hFinalBound,hTransf⟩ :=
        ih {t : Ico 0 (0+T) | ∃ i : ℤ, G2 t.val 0=c2+(i:ℝ)*T}.ncard hlt G2 hG2 c2 d2 hp2 hc2 hBand2 hFinite2 hTrans2 hReference2 hGM2 rfl
      refine ⟨Q.compose R,Gf,cf,df,?_,?_,?_,hGf,hpf,hcf,hBandf,hReferencef,hGMf,hFinitef,hFinalCount,
        hFinalBound.trans hlt.le,hTransf⟩
      · intro x
        rw [hGfEq,hG2Eq]
        rfl
      · intro t i
        change R.map (t,Q.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)))=
          p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
        rw [hQfix,hRfix]
      · intro t i z
        change R.map (t,Q.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)))=
          R.map (t,Q.map (t,z))+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
        rw [hQeq,hReq]
    · refine ⟨AmbientIsotopy.identity Plane,G,c,d,?_,?_,?_,hG,hp,hc,hBand,hpgrid,hGM,hfinite,
        le_of_not_gt hcount,by rw [hn],htrans⟩
      · intro x; rfl
      · intro t i; rfl
      · intro t i z; rfl

#print axioms actual_marked_vertical_finite_descent_retains_horizontal_band
