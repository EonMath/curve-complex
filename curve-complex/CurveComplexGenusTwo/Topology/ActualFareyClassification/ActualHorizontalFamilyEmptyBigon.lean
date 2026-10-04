import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalShortJordanBigon
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalLocalSubdiskGeometry
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalFamilyNoHalfplaneTouch

open Set Topology Schoenflies CurveComplex

theorem actual_vertical_orbit_horizontal_grid_translation_invariant
    (G : ℝ → Plane) (T c : ℝ) (j : ℤ) (z : Plane) :
    Plane.mk 0 ((j:ℝ)*T)+z ∈
      (⋃ k : ℤ, range (fun t => G t+Plane.mk 0 ((k:ℝ)*T))) ∩
      {w : Plane | ∃ i : ℤ, w 1=c+(i:ℝ)*T} ↔
    z ∈ (⋃ k : ℤ, range (fun t => G t+Plane.mk 0 ((k:ℝ)*T))) ∩
      {w : Plane | ∃ i : ℤ, w 1=c+(i:ℝ)*T} := by
  constructor
  · rintro ⟨hz,⟨i,hi⟩⟩
    obtain ⟨k,t,ht⟩ := mem_iUnion.mp hz
    refine ⟨mem_iUnion.mpr ⟨k-j,t,?_⟩,i-j,?_⟩
    · have he : G t+Plane.mk 0 (((k-j:ℤ):ℝ)*T) =
          (G t+Plane.mk 0 ((k:ℝ)*T))-Plane.mk 0 ((j:ℝ)*T) := by
        ext q
        fin_cases q <;> simp [Plane.mk,Int.cast_sub] <;> ring
      change G t+Plane.mk 0 (((k-j:ℤ):ℝ)*T)=z
      dsimp only at ht
      rw [he,ht]
      abel
    · change (j:ℝ)*T+z 1=c+(i:ℝ)*T at hi
      push_cast
      linarith
  · rintro ⟨hz,⟨i,hi⟩⟩
    obtain ⟨k,t,ht⟩ := mem_iUnion.mp hz
    refine ⟨mem_iUnion.mpr ⟨j+k,t,?_⟩,j+i,?_⟩
    · rw [← ht]
      ext q
      fin_cases q <;> simp [Plane.mk,Int.cast_add] <;> ring
    · change (j:ℝ)*T+z 1=c+((j+i:ℤ):ℝ)*T
      rw [hi]
      push_cast
      ring

/-- Minimizing actual compact full-orbit contacts removes all translated source
lines from the open bigon. Neither emptiness nor global fiber finiteness is supplied. -/
theorem actual_horizontal_positive_count_has_family_empty_bigon
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
    : ∃ (i : ℤ) (r s : ℝ), r<s ∧ G r 1=c+(i:ℝ)*T ∧ G s 1=c+(i:ℝ)*T ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      (∀ u∈Ioo r s, G u 1≠c+(i:ℝ)*T) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
        (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) := by
  classical
  let L := fun j : ℤ => range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
  let E := (⋃ j : ℤ,L j) ∩ {z : Plane | ∃ i : ℤ,z 1=c+(i:ℝ)*T}
  let count (r s : ℝ) := (E ∩ segment ℝ (G r) (G s)).ncard
  let Q : ℕ → Prop := fun n => ∃ (i : ℤ) (r s : ℝ),
    r<s ∧ G r 1=c+(i:ℝ)*T ∧ G s 1=c+(i:ℝ)*T ∧
    (∀ u∈Ioo r s,G u 1≠c+(i:ℝ)*T) ∧ count r s=n
  have hex : ∃ n,Q n := by
    obtain ⟨i,r,s,hrs,hshort,hr,hs,hno,hC⟩ :=
      actual_horizontal_positive_count_has_short_jordan_bigon G hG T c hT hp hc hfinite hcount htrans
    exact ⟨count r s,i,r,s,hrs,hr,hs,hno,rfl⟩
  obtain ⟨i,r,s,hrs,hr,hs,hno,hn⟩ := Nat.find_spec hex
  have hmin (k : ℤ) (a b : ℝ) (hab : a<b)
      (ha : G a 1=c+(k:ℝ)*T) (hb : G b 1=c+(k:ℝ)*T)
      (havoid : ∀ u∈Ioo a b,G u 1≠c+(k:ℝ)*T) : count r s≤count a b := by
    rw [hn]
    exact Nat.find_min' hex ⟨k,a,b,hab,ha,hb,havoid,rfl⟩
  have hC := horizontal_fiber_free_interval_actual_jordan_candidate G hG.injective
    (c+(i:ℝ)*T) r s hrs hr hs hno
  obtain ⟨hclosed,hpair,hlf⟩ := normalized_line_deck_family G hG T hT hp hc
  have hzero : Plane.mk 0 (((0:ℤ):ℝ)*T)=(0:Plane) := by
    ext i
    fin_cases i <;> simp
  have hbase (t : ℝ) : G t ∈ L 0 := ⟨t,by change G t+Plane.mk 0 (((0:ℤ):ℝ)*T)=G t; rw [hzero,add_zero]⟩
  have hsegment (z : Plane) (hz : z ∈ segment ℝ (G r) (G s)) : z 1=c+(i:ℝ)*T := by
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨v,hv,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change v*(G s 1-G r 1)+G r 1=c+(i:ℝ)*T
    rw [hr,hs]
    ring
  have hEf : (E ∩ segment ℝ (G r) (G s)).Finite :=
    actual_horizontal_full_family_grid_contacts_finite_in_compact G T c hT hp hfinite
      _ (isCompact_segment (G r) (G s))
  refine ⟨i,r,s,hrs,hr,hs,hC,hno,disjoint_left.mpr ?_⟩
  intro z hz hzL
  obtain ⟨j,t,ht⟩ := mem_iUnion.mp hzL
  let F : C(ℝ,Plane) := ⟨fun u => G u+Plane.mk 0 ((j:ℝ)*T),
    G.continuous.add continuous_const⟩
  have hF : IsClosedEmbedding F :=
    (Homeomorph.addRight (Plane.mk 0 ((j:ℝ)*T))).isClosedEmbedding.comp hG
  have htI : F t ∈ inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) := by
    simpa only [F,ContinuousMap.coe_mk,ht] using hz
  obtain ⟨a,b,hat,htb,haC,hbC,hin,hArc⟩ :=
    proper_line_entering_jordan_has_interval_crosscut F hF _ hC t htI
  have hab : a < b := hat.trans htb
  have hend : F a ∈ segment ℝ (G r) (G s) ∧
      F b ∈ segment ℝ (G r) (G s) ∧
      ¬ (F a=G r ∧ F b=G s) ∧ ¬ (F a=G s ∧ F b=G r) := by
    by_cases hj : j=0
    · subst j
      have hFG : F=G := by
        apply ContinuousMap.ext
        intro u
        change G u+Plane.mk 0 (((0:ℤ):ℝ)*T)=G u
        rw [hzero,add_zero]
      rw [hFG] at haC hbC hin ⊢
      exact interval_crosscut_of_line_bigon_endpoints_on_other_side
        G hG.injective r s a b hrs hab hC haC hbC hin
    · have hdis := hpair hj
      have hn (u : ℝ) : F u ∉ range G := by
        rintro ⟨v,hv⟩
        apply disjoint_left.mp hdis (show F u ∈ L j from ⟨u,rfl⟩)
        rw [← hv]
        exact hbase v
      have ha : F a ∈ segment ℝ (G r) (G s) := by
        rcases haC with ha | ha
        · obtain ⟨u,hu,he⟩ := ha
          exact False.elim (hn a ⟨u,he⟩)
        · exact ha
      have hb : F b ∈ segment ℝ (G r) (G s) := by
        rcases hbC with hb | hb
        · obtain ⟨u,hu,he⟩ := hb
          exact False.elim (hn b ⟨u,he⟩)
        · exact hb
      exact ⟨ha,hb,fun hh => hn a ⟨r,hh.1.symm⟩,fun hh => hn a ⟨s,hh.1.symm⟩⟩
  obtain ⟨ha,hb,hnot,hnot'⟩ := hend
  have ha0 : G a 1=c+((i-j:ℤ):ℝ)*T := by
    have hh := hsegment _ ha
    change G a 1+(j:ℝ)*T=c+(i:ℝ)*T at hh
    push_cast
    linarith
  have hb0 : G b 1=c+((i-j:ℤ):ℝ)*T := by
    have hh := hsegment _ hb
    change G b 1+(j:ℝ)*T=c+(i:ℝ)*T at hh
    push_cast
    linarith
  have havoid (u : ℝ) (hu : u ∈ Ioo a b) : G u 1≠c+((i-j:ℤ):ℝ)*T := by
    intro he
    have hh := horizontal_fiber_free_interval_bigon_inside_avoids_fiber G
      (c+(i:ℝ)*T) r s hr hs hno hC _ (hin u hu)
    apply hh
    change G u 1+(j:ℝ)*T=c+(i:ℝ)*T
    rw [he]
    push_cast
    ring
  have hp : G r ∈ E := ⟨mem_iUnion.mpr ⟨0,hbase r⟩,⟨i,hr⟩⟩
  have hq : G s ∈ E := ⟨mem_iUnion.mpr ⟨0,hbase s⟩,⟨i,hs⟩⟩
  have hlt := horizontal_spatial_contacts_strict_subsegment E (G r) (G s) (F a) (F b)
    hEf hp hq (fun hh => (ne_of_lt hrs) (hG.injective hh))
    (hr.trans hs.symm) ha hb hnot hnot'
  have heq : (E ∩ segment ℝ (F a) (F b)).ncard =
      (E ∩ segment ℝ (G a) (G b)).ncard := by
    have hh := translation_invariant_spatial_segment_count E
      (Plane.mk 0 ((j:ℝ)*T)) (G a) (G b)
      (actual_vertical_orbit_horizontal_grid_translation_invariant G T c j)
    simpa only [F,ContinuousMap.coe_mk,add_comm] using hh
  rw [heq] at hlt
  exact not_lt_of_ge (hmin (i-j) a b hab ha0 hb0 havoid) hlt


#print axioms actual_horizontal_positive_count_has_family_empty_bigon
