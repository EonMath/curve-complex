import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalFamilyNoHalfplaneTouch
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFarSideEndpoints

open Set Topology Schoenflies Metric

theorem actual_horizontal_family_has_both_sides_near_parameter
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T t c d : ℝ) (hT : 0<T) (hd : 0<d)
    (hp : ∀ (k : ℤ) (u : ℝ), G (u+(k:ℝ)*T)=G u+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (htc : G t 1=c)
    (U : Set Plane) (V : Set (ℝ×ℝ)) (htU : G t∈U) (h : U ≃ₜ V)
    (hU : IsOpen U) (hV : IsOpen V)
    (ht0 : ((h ⟨G t,htU⟩ : V) : ℝ×ℝ)=(0,0))
    (haxes : ∀ z (hz : z∈U),
      (z 1=c ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
      (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
        ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0))
    (N : Set Plane) (hN : IsOpen N) (htN : G t∈N) :
    (∃ a∈Ioo (t-d) (t+d), G a∈N ∧ G a 1<c) ∧
    (∃ b∈Ioo (t-d) (t+d), G b∈N ∧ c<G b 1) := by
  let L : ℤ → Set Plane := fun j => range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
  obtain ⟨hclosed,hpair,hlf⟩ := normalized_line_deck_family G hG T hT hp hc
  change Pairwise (fun i j => Disjoint (L i) (L j)) at hpair
  have hL0 : L 0=range G := by
    have hh : (fun x : ℝ => G x+Plane.mk 0 (((0:ℤ):ℝ)*T))=G := by
      funext x
      ext k
      fin_cases k <;> simp [Plane.mk]
    change range (fun x : ℝ => G x+Plane.mk 0 (((0:ℤ):ℝ)*T))=range G
    rw [hh]
  let J := ⋃ j : {j : ℤ // j≠0}, L j.val
  have hJ : IsClosed J :=
    (hlf.comp_injective Subtype.val_injective).isClosed_iUnion (fun j => hclosed j.val)
  have hGJ : Disjoint (range G) J := by
    apply disjoint_left.mpr
    intro z hz hj
    obtain ⟨j,hj⟩ := mem_iUnion.mp hj
    exact disjoint_left.mp (hpair (Ne.symm j.property)) (hL0.symm ▸ hz) hj
  let bad := (G '' (Ioo (t-d) (t+d))ᶜ)∪J
  have hbad : IsClosed bad := (hG.isClosedMap _ isOpen_Ioo.isClosed_compl).union hJ
  have htbad : G t∉bad := by
    rintro (⟨u,hu,he⟩|hh)
    · have hut := hG.injective he
      subst u
      exact hu ⟨by linarith,by linarith⟩
    · exact disjoint_left.mp hGJ ⟨t,rfl⟩ hh
  obtain ⟨hl,hr⟩ := actual_horizontal_fiber_set_crossing_has_both_sides
    (⋃ j : ℤ,L j) (G t) c htc U V htU h hU hV ht0 haxes
    (N∩badᶜ) (hN.inter hbad.isOpen_compl) ⟨htN,htbad⟩
  have hnear (z : Plane) (hz : z∈(N∩badᶜ)∩(⋃ j : ℤ,L j)) :
      ∃ u∈Ioo (t-d) (t+d), G u=z ∧ G u∈N := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp hz.2
    have hj0 : j=0 := by
      by_contra hn
      exact hz.1.2 (Or.inr (mem_iUnion.mpr ⟨⟨j,hn⟩,hj⟩))
    subst j
    rw [hL0] at hj
    obtain ⟨u,hu⟩ := hj
    refine ⟨u,?_,hu,hu.symm ▸ hz.1.1⟩
    by_contra hn
    exact hz.1.2 (Or.inl ⟨u,hn,hu⟩)
  constructor
  · obtain ⟨z,hz,hzc⟩ := hl
    obtain ⟨u,hu,he,hN⟩ := hnear z hz
    exact ⟨u,hu,hN,he.symm ▸ hzc⟩
  · obtain ⟨z,hz,hzc⟩ := hr
    obtain ⟨u,hu,he,hN⟩ := hnear z hz
    exact ⟨u,hu,hN,he.symm ▸ hzc⟩

theorem actual_horizontal_one_sided_bigon_has_far_side_endpoints
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s c : ℝ) (hT : 0<T)
    (hrs : r<s) (hshort : s-r<T)
    (hp : ∀ (k : ℤ) (u : ℝ), G (u+(k:ℝ)*T)=G u+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hr : G r 1=c) (hs : G s 1=c)
    (hside : (∀ t∈Icc r s, G t 1 ≤ c) ∨ (∀ t∈Icc r s, c ≤ G t 1))
    (htrans : ∀ t, G t 1=c →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (htU : G t∈U) (h : U ≃ₜ V),
      IsOpen U ∧ IsOpen V ∧ ((h ⟨G t,htU⟩ : V) : ℝ×ℝ)=(0,0) ∧
      (∀ z (hz : z∈U),
        (z 1=c ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
        (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
          ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
    (N M : Set Plane) (hN : IsOpen N) (hM : IsOpen M)
    (hrN : G r∈N) (hsM : G s∈M) :
    ∃ a b : ℝ, a<r ∧ s<b ∧ b-a<T ∧ G a∈N ∧ G b∈M ∧
      (((∀ t∈Icc r s, G t 1 ≤ c) ∧ c<G a 1 ∧ c<G b 1) ∨
       ((∀ t∈Icc r s, c ≤ G t 1) ∧ G a 1<c ∧ G b 1<c)) := by
  let d := min ((s-r)/2) ((T-(s-r))/4)
  have hd : 0<d := by dsimp [d]; positivity
  have hdsr : d<s-r := by
    have hh := min_le_left ((s-r)/2) ((T-(s-r))/4)
    dsimp [d]; linarith
  have hdT : d ≤ (T-(s-r))/4 := min_le_right _ _
  obtain ⟨U,V,hrU,h,hU,hV,hr0,haxr⟩ := htrans r hr
  obtain ⟨Ur,Vr,hsU,j,hUr,hVr,hs0,haxs⟩ := htrans s hs
  have hpr := actual_horizontal_family_has_both_sides_near_parameter
    G hG T r c d hT hd hp hc hr U V hrU h hU hV hr0 haxr N hN hrN
  have hps := actual_horizontal_family_has_both_sides_near_parameter
    G hG T s c d hT hd hp hc hs Ur Vr hsU j hUr hVr hs0 haxs M hM hsM
  rcases hside with hleft|hright
  · obtain ⟨a,ha,haN,hac⟩ := hpr.2
    obtain ⟨b,hb,hbM,hbc⟩ := hps.2
    have har : a<r := by
      by_contra hh
      have haI : a∈Icc r s := ⟨le_of_not_gt hh,by linarith [ha.2]⟩
      exact not_lt_of_ge (hleft a haI) hac
    have hsb : s<b := by
      by_contra hh
      have hbI : b∈Icc r s := ⟨by linarith [hb.1],le_of_not_gt hh⟩
      exact not_lt_of_ge (hleft b hbI) hbc
    refine ⟨a,b,har,hsb,?_,haN,hbM,Or.inl ⟨hleft,hac,hbc⟩⟩
    linarith [ha.1,hb.2]
  · obtain ⟨a,ha,haN,hac⟩ := hpr.1
    obtain ⟨b,hb,hbM,hbc⟩ := hps.1
    have har : a<r := by
      by_contra hh
      have haI : a∈Icc r s := ⟨le_of_not_gt hh,by linarith [ha.2]⟩
      exact not_lt_of_ge (hright a haI) hac
    have hsb : s<b := by
      by_contra hh
      have hbI : b∈Icc r s := ⟨by linarith [hb.1],le_of_not_gt hh⟩
      exact not_lt_of_ge (hright b hbI) hbc
    refine ⟨a,b,har,hsb,?_,haN,hbM,Or.inr ⟨hright,hac,hbc⟩⟩
    linarith [ha.1,hb.2]


#print axioms actual_horizontal_one_sided_bigon_has_far_side_endpoints
