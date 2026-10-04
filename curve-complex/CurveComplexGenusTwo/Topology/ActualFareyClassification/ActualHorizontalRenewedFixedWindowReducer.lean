import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalGenuineFixedWindowErase
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalRenewedFamilyTransversality
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualEquivariantSourcePreservation

open Set Topology Schoenflies CurveComplex

/-- Actual fixed-window erasure renews the actual normalized source and
WHOLE-family horizontal transversality, with no supplied reducing move. -/
theorem actual_horizontal_positive_count_has_renewed_fixed_window_reducer
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
    ∃ H : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ) z, H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
    ∃ G' : C(ℝ,Plane), (∀ x, G' x=H.finalMap (G x)) ∧ IsClosedEmbedding G' ∧
      (∀ (k : ℤ) (x : ℝ), G' (x+(k:ℝ)*T)=G' x+Plane.mk ((k:ℝ)*T) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ), G' x=G' y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0) ∧
      {t : Ico 0 (0+T) | ∃ i : ℤ,G' t.val 1=c+(i:ℝ)*T}.Finite ∧
      {t : Ico 0 (0+T) | ∃ i : ℤ, G' t.val 1=c+(i:ℝ)*T}.ncard <
        {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.ncard ∧
      (∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G' x+Plane.mk 0 ((j:ℝ)*T))) → q 1=c+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 1=c+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G' x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0))) := by
  obtain ⟨k,r,s,a,b,hrs,har,hsb,hba,hr,hs,_,_,hcontact,hside,hold,phi,hfamily,hAi,haModel,hbModel,hFi,hdeck⟩ :=
    actual_horizontal_positive_count_has_coherent_event_family_chart G hG T c hT hp hc hfinite hcount htrans
  have hGL : range G⊆⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) := by
    rintro z ⟨t,rfl⟩
    refine mem_iUnion.mpr ⟨0,t,?_⟩
    ext i; fin_cases i <;> simp [Plane.mk]
  have htx := fun t ht => htrans (G t) k (hGL (mem_range_self _)) ht
  have hpgridK : ∀ i : ℤ, p 1+(i:ℝ)*T≠c+(k:ℝ)*T := by
    intro i hi
    apply hpgrid (i-k)
    push_cast
    linarith
  have holdK : (G '' Icc a b)∩{z : Plane | ∃ i : ℤ, z 1=(c+(k:ℝ)*T)+(i:ℝ)*T}={G r,G s} := by
    convert hold using 2
    ext z
    constructor
    · rintro ⟨i,hi⟩; refine ⟨k+i,?_⟩; push_cast; linarith
    · rintro ⟨i,hi⟩; refine ⟨i-k,?_⟩; push_cast; linarith
  obtain ⟨B,hB,hBi,hBG,hBM⟩ := actual_horizontal_two_event_chart_has_grid_free_target G hG T (c+(k:ℝ)*T)
    r s a b hT hrs har hsb hba hp hc hr hs hcontact hside htx holdK phi hAi hFi p hpgridK hGM
  have hBGOriginal : ∀ z∈B, ∀ i : ℤ, z 1≠c+(i:ℝ)*T := by
    intro z hz i hi
    apply hBG z hz (i-k)
    push_cast
    linarith
  have hab : a<b := har.trans (hrs.trans hsb)
  have hA := continuous_injective_interval_isArcBetween G hG.injective hab
  obtain ⟨H,hHeq,hHmove,hHfix⟩ := periodic_chart_crosscut_isotopy T hT phi hdeck
    (G '' Icc a b) B (G a) (G b) hA hB haModel hbModel hAi hBi
  obtain ⟨_,hlocal⟩ := normalized_actual_family_disk_full_lattice_contact G T a b hp phi hfamily
  have havoid := plane_actual_horizontal_grid_free_full_lattice_orbit T c B hBGOriginal
  have holdOrbit := plane_actual_horizontal_grid_contacts_full_lattice_orbit T c (G '' Icc a b) {G r,G s} hold
  have htwoImage (i : ℤ×ℤ) :
      (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' ({G r,G s} : Set Plane)=
      {G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} := by simp
  simp_rw [htwoImage] at holdOrbit
  have hcorners : ({G r,G s} : Set Plane)⊆phi '' Plane.openSquare 0 1 := by
    intro z hz
    rcases hz with hz|hz
    · subst z
      apply hAi
      refine ⟨⟨r,⟨har.le,hrs.le.trans hsb.le⟩,rfl⟩,?_⟩
      intro hh
      rcases hh with hh|hh
      · have h := hG.injective hh; linarith
      · have h := hG.injective (show G r=G b from hh); linarith
    · have hz' : z=G s := hz
      subst z
      apply hAi
      refine ⟨⟨s,⟨har.le.trans hrs.le,hsb.le⟩,rfl⟩,?_⟩
      intro hh
      rcases hh with hh|hh
      · have h := hG.injective hh; linarith
      · have h := hG.injective (show G s=G b from hh); linarith
  have hsupported : (⋃ i : ℤ×ℤ, ({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
      G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane))⊆
      ⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (phi '' Plane.openSquare 0 1) := by
    apply iUnion_mono
    intro i
    rw [←htwoImage]
    exact image_mono hcorners
  have herase := crossing_parameters_of_periodic_supported_crosscut_replacement G T hT phi H
    (G '' Icc a b) B {z : Plane | ∃ i : ℤ, z 1=c+(i:ℝ)*T} (G r) (G s)
    hlocal hHmove hHfix havoid holdOrbit hsupported
  let gamma : Ico 0 (0+T)→Plane := fun t => G t.val
  let L : Set Plane := {z : Plane | ∃ i : ℤ,z 1=c+(i:ℝ)*T}
  have herase0 : {t : Ico 0 (0+T) | H.finalMap (gamma t)∈L}=
      {t : Ico 0 (0+T) | gamma t∈L}\gamma ⁻¹'
        (⋃ i : ℤ×ℤ,({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
          G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) := by
    ext t
    exact Set.ext_iff.mp herase t.val
  obtain ⟨l,u,hu,hru⟩ := actual_parameter_has_fundamental_window T 0 r hT
  let tu : Ico 0 (0+T) := ⟨u,hu⟩
  have huContact : G u 1=c+(k:ℝ)*T := by
    have hh := hr
    rw [hru,hp] at hh
    change G u 1+0=c+(k:ℝ)*T at hh
    simpa using hh
  have huOrbit : gamma tu∈⋃ i : ℤ×ℤ,
      ({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
        G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane) := by
    refine mem_iUnion.mpr ⟨(-l,0),Or.inl ?_⟩
    change G u=G r+Plane.mk (((-l:ℤ):ℝ)*T) (((0:ℤ):ℝ)*T)
    rw [hru,hp]
    ext q
    fin_cases q <;> simp [Plane.mk] <;> ring
  have hDrop := finite_crossing_count_strict_after_full_lattice_orbit_erase gamma
    (fun t => H.finalMap (gamma t)) L T (G r) (G s) hfinite herase0 tu ⟨k,huContact⟩ huOrbit
  obtain ⟨G',hG'Eq,hG',hp',hc'⟩ := actual_equivariant_isotopy_preserves_normalized_source G hG T hp hc H hHeq
  have hTransNew := actual_horizontal_supported_erase_renews_whole_family_transversality G T a b c r s
    hT hp phi hfamily hold H hHeq hHfix herase htrans
  refine ⟨H,hHeq,G',hG'Eq,hG',hp',hc',?_,?_,?_⟩
  · simpa only [hG'Eq,gamma,L,mem_setOf_eq] using hDrop.1
  · simpa only [hG'Eq,gamma,L,mem_setOf_eq] using hDrop.2
  · simpa only [hG'Eq] using hTransNew

#print axioms actual_horizontal_positive_count_has_renewed_fixed_window_reducer
