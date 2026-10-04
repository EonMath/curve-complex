import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalMarkedFiniteDescent
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualZeroHorizontalEventsBand

open Set Topology Schoenflies CurveComplex

/-- Actual marked fixed-window termination confines the WHOLE original
source image to a physical horizontal band of height T. No band certificate. -/
theorem actual_horizontal_source_has_marked_physical_band
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hfinite : {t : Ico 0 (0+T) | ∃ i : ℤ,G t.val 1=c+(i:ℝ)*T}.Finite)
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
    ∃ P : AmbientIsotopy Plane, ∃ Gf : C(ℝ,Plane), ∃ cf d : ℝ,
      (∀ x, Gf x=P.finalMap (G x)) ∧
      (∀ t (i : ℤ×ℤ), P.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ) z, P.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        P.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      IsClosedEmbedding Gf ∧
      (∀ (k : ℤ) (x : ℝ), Gf (x+(k:ℝ)*T)=Gf x+Plane.mk ((k:ℝ)*T) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ), Gf x=Gf y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0) ∧
      (∀ i : ℤ, p 1+(i:ℝ)*T≠cf) ∧
      Disjoint (range Gf) (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)}) ∧
      (∀ x,d<Gf x 1 ∧ Gf x 1<d+T) := by
  obtain ⟨P,Gf,cf,hGfEq,hPfix,hPeq,hGf,hpf,hcf,hRef,hGMf,hFinite,hZero,_,_⟩ :=
    actual_horizontal_source_has_marked_finite_descent_to_zero G hG T c hT hp hc hfinite htrans p hpgrid hGM
  have hAvoid := actual_zero_horizontal_quotient_events_avoids_grid Gf T cf hT hpf hFinite hZero
  obtain ⟨k,hBand⟩ := actual_horizontal_grid_avoidance_has_physical_band Gf T cf hT hAvoid
  refine ⟨P,Gf,cf,cf+(k:ℝ)*T,hGfEq,hPfix,hPeq,hGf,hpf,hcf,hRef,hGMf,?_⟩
  intro x
  obtain ⟨hl,hu⟩ := hBand x
  refine ⟨hl,?_⟩
  push_cast at hu
  linarith

#print axioms actual_horizontal_source_has_marked_physical_band
