import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalClosedBigonSupport
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSourceFamilyOperationChart

open Set Topology Schoenflies CurveComplex unitInterval

theorem actual_horizontal_positive_count_has_closed_deck_free_bigon
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
    :
    ∃ k : ℤ, ∃ r s : ℝ, r<s ∧ s-r<T ∧ G r 1=c+(k:ℝ)*T ∧ G s 1=c+(k:ℝ)*T ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
        (⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))) ∧
      (∀ i : ℤ, ∀ t∈Ioo r s, G t 1≠c+(i:ℝ)*T) ∧
      segment ℝ (G r) (G s) ∩
        (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s} ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint
        (closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) ∧
      Pairwise (fun i j : ℤ×ℤ => Disjoint
        (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) ∧
      ((∀ z∈(G '' Icc r s) ∪ segment ℝ (G r) (G s),
          c+(k:ℝ)*T-T≤z 1 ∧ z 1≤c+(k:ℝ)*T) ∨
        (∀ z∈(G '' Icc r s) ∪ segment ℝ (G r) (G s),
          c+(k:ℝ)*T≤z 1 ∧ z 1≤c+(k:ℝ)*T+T)) := by
  obtain ⟨k,r,s,hrs,hshort,hr,hs,hJ,he,hno,hcontact,hsep,hslab⟩ :=
    actual_horizontal_positive_count_has_clean_short_bigon G hG T c hT hp hc hfinite hcount htrans
  have hclosed := actual_clean_horizontal_bigon_closed_disk_deck_free G hG T r s (c+(k:ℝ)*T)
    hT hrs hshort hr hs hp hc hcontact hJ hsep
  exact ⟨k,r,s,hrs,hshort,hr,hs,hJ,he,hno,hcontact,hclosed,hsep,hslab⟩


theorem actual_horizontal_positive_count_has_attached_family_support
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
    :
    ∃ k : ℤ, ∃ r s : ℝ, r<s ∧ s-r<T ∧
      G r 1=c+(k:ℝ)*T ∧ G s 1=c+(k:ℝ)*T ∧
      (∀ i : ℤ, ∀ t∈Ioo r s, G t 1≠c+(i:ℝ)*T) ∧
    let K := closure (inside ((G '' Icc r s)∪segment ℝ (G r) (G s)))
    let L := ⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
    ∃ a b rho sigma : ℝ, a<r ∧ s<b ∧ b-a<T ∧ 0<rho ∧ rho≤1 ∧ 0<sigma ∧ sigma≤1 ∧
    ∃ F : Plane ≃ₜ Plane, F (G r)=Plane.mk 1 0 ∧ F (G s)=Plane.mk (-1) 0 ∧
      F '' K=Plane.closedSquare 0 1 ∧
    ∃ E Q : I×Icc (-1:ℝ) 1 → Plane,
      IsEmbedding E ∧ IsEmbedding Q ∧ Disjoint (range E) (range Q) ∧
      (∀ w : Icc (-1:ℝ) 1, E (0,w)=F.symm (Plane.mk 1 (rho*w))) ∧
      (∀ w : Icc (-1:ℝ) 1, Q (0,w)=F.symm (Plane.mk (-1) (-sigma*w))) ∧
      (∀ t : I, E (t,⟨0,by norm_num⟩)=G (reparam r a t)) ∧
      (∀ t : I, Q (t,⟨0,by norm_num⟩)=G (reparam s b t)) ∧
      range E∩K=(fun w : Icc (-1:ℝ) 1 => F.symm (Plane.mk 1 (rho*w))) '' univ ∧
      range Q∩K=(fun w : Icc (-1:ℝ) 1 => F.symm (Plane.mk (-1) (-sigma*w))) '' univ ∧
      ((K∪range E)∪range Q)∩L=G '' Icc a b ∧
      IsCompact ((K∪range E)∪range Q) ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint ((K∪range E)∪range Q)
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' ((K∪range E)∪range Q))) := by
  obtain ⟨k,r,s,hrs,hshort,hr,hs,hJ,he,hno,hcontact,hdeck,_,_⟩ :=
    actual_horizontal_positive_count_has_closed_deck_free_bigon G hG T c hT hp hc hfinite hcount htrans
  refine ⟨k,r,s,hrs,hshort,hr,hs,hno,?_⟩
  exact normalized_clean_bigon_has_actual_attached_family_collars G hG T r s hT hrs hshort hp hc hJ he hcontact hdeck


theorem actual_horizontal_positive_count_has_closed_family_disk
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
    :
    ∃ k : ℤ, ∃ r s a b : ℝ, r<s ∧ a<r ∧ s<b ∧ b-a<T ∧
      G r 1=c+(k:ℝ)*T ∧ G s 1=c+(k:ℝ)*T ∧
      (∀ i : ℤ, ∀ t∈Ioo r s, G t 1≠c+(i:ℝ)*T) ∧
    ∃ Phi : Plane ≃ₜ Plane,
      (Phi '' Plane.closedSquare 0 1)∩
        (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=G '' Icc a b ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint (Phi '' Plane.closedSquare 0 1)
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          (Phi '' Plane.closedSquare 0 1))) := by
  obtain ⟨k,r,s,hrs,_,hr,hs,hno,a,b,rho,sigma,har,hsb,hba,hrho,hrho1,hsigma,hsigma1,
    F,hrF,hsF,hFK,E,Q,hE,hQ,hEQ,hEport,hQport,hEcenter,hQcenter,hEK,hQK,hcontact,_,hdeck⟩ :=
    actual_horizontal_positive_count_has_attached_family_support G hG T c hT hp hc hfinite hcount htrans
  obtain ⟨Phi,hPhi⟩ := actual_two_attached_half_collars_disk_chart _ F hFK rho sigma hrho hrho1 hsigma hsigma1
    E Q hE hQ hEQ hEport hQport hEK hQK
  refine ⟨k,r,s,a,b,hrs,har,hsb,hba,hr,hs,hno,Phi,?_,?_⟩
  · rwa [hPhi]
  · rwa [hPhi]


theorem actual_horizontal_positive_count_has_family_operation_chart
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
    :
    ∃ k : ℤ, ∃ r s a b : ℝ, r<s ∧ a<r ∧ s<b ∧ b-a<T ∧
      G r 1=c+(k:ℝ)*T ∧ G s 1=c+(k:ℝ)*T ∧
      (∀ i : ℤ, ∀ t∈Ioo r s, G t 1≠c+(i:ℝ)*T) ∧
    ∃ phi : Plane ≃ₜ Plane,
      (phi '' Plane.closedSquare 0 1)∩
        (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=G '' Icc a b ∧
      (G '' Icc a b)\{G a,G b}⊆phi '' Plane.openSquare 0 1 ∧
      phi.symm (G a)∈modelCurve ∧ phi.symm (G b)∈modelCurve ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint (phi '' Plane.closedSquare 0 1)
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          (phi '' Plane.closedSquare 0 1))) := by
  obtain ⟨k,r,s,a,b,hrs,har,hsb,hba,hr,hs,hno,Phi,hcontact,hdeck⟩ :=
    actual_horizontal_positive_count_has_closed_family_disk G hG T c hT hp hc hfinite hcount htrans
  obtain ⟨phi,_,hcontact',hInterior,haModel,hbModel,hdeck'⟩ :=
    normalized_actual_closed_family_disk_operation_chart G hG T a b hT (har.trans (hrs.trans hsb)) hp hc Phi hcontact hdeck
  exact ⟨k,r,s,a,b,hrs,har,hsb,hba,hr,hs,hno,phi,hcontact',hInterior,haModel,hbModel,hdeck'⟩


#print axioms actual_horizontal_positive_count_has_closed_deck_free_bigon
#print axioms actual_horizontal_positive_count_has_attached_family_support
#print axioms actual_horizontal_positive_count_has_closed_family_disk
#print axioms actual_horizontal_positive_count_has_family_operation_chart
