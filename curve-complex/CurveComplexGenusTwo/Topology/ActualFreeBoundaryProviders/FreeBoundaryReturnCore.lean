import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalCrossingReturnCore

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies RegionalEmbeddedFamily

theorem free_contact_finite_family_minimal_return
    {X : Type*} [TopologicalSpace X]
    (B : C(Interval,X))
    (K : Finset C(Interval,X))
    (hfinite : {t : Interval | ∃ A ∈ K, B t ∈ Set.range A}.Finite)
    (hpair : ∀ A ∈ K, ∀ C ∈ K, A ≠ C → Disjoint (Set.range A) (Set.range C))
    (A₀ : C(Interval,X)) (hA₀ : A₀ ∈ K)
    (l₀ r₀ : Interval) (hlr₀ : l₀ < r₀)
    (hzero : B l₀ ∈ Set.range A₀) (hone : B r₀ ∈ Set.range A₀) :
    ∃ A ∈ K, ∃ l r : Interval,
      l < r ∧ B l ∈ Set.range A ∧ B r ∈ Set.range A ∧
      (∀ u : Interval, l < u → u < r → B u ∉ Set.range A) ∧
      (∀ C ∈ K, C ≠ A → ∀ u v : Interval,
        u ∈ Set.Icc l r → v ∈ Set.Icc l r →
        B u ∈ Set.range C → B v ∈ Set.range C → u = v) := by
  classical
  let T : Set Interval := {t | ∃ A ∈ K, B t ∈ Set.range A}
  let D : Set ℝ := {d | ∃ A ∈ K, ∃ l r : Interval,
    l < r ∧ B l ∈ Set.range A ∧ B r ∈ Set.range A ∧ d = r.val - l.val}
  have hDfinite : D.Finite := by
    apply ((hfinite.prod hfinite).image (fun z : Interval × Interval => z.2.val-z.1.val)).subset
    rintro d ⟨A,hA,l,r,hlr,hl,hr,rfl⟩
    exact ⟨(l,r),⟨⟨A,hA,hl⟩,⟨A,hA,hr⟩⟩,rfl⟩
  have hDnonempty : D.Nonempty := ⟨r₀.val-l₀.val,A₀,hA₀,l₀,r₀,hlr₀,hzero,hone,rfl⟩
  obtain ⟨d,hd,hmin⟩ := Set.exists_min_image D id hDfinite hDnonempty
  obtain ⟨A,hA,l,r,hlr,hl,hr,hd⟩ := hd
  have hminimal (C : C(Interval,X)) (hC : C ∈ K)
      (u v : Interval) (huv : u < v)
      (hu : B u ∈ Set.range C) (hv : B v ∈ Set.range C) :
      r.val-l.val ≤ v.val-u.val := by
    have hh := hmin (v.val-u.val) ⟨C,hC,u,v,huv,hu,hv,rfl⟩
    simpa only [id_eq,hd] using hh
  refine ⟨A,hA,l,r,hlr,hl,hr,?_,?_⟩
  · intro u hlu hur hu
    have hh := hminimal A hA l u hlu hl hu
    change u.val < r.val at hur
    linarith
  · intro C hC hCA u v hu hv hBu hBv
    have hlu : l < u := lt_of_le_of_ne hu.1 (by
      intro he
      exact Set.disjoint_left.mp (hpair C hC A hA hCA) hBu (he ▸ hl))
    have hur : u < r := lt_of_le_of_ne hu.2 (by
      intro he
      exact Set.disjoint_left.mp (hpair C hC A hA hCA) hBu (he.symm ▸ hr))
    have hlv : l < v := lt_of_le_of_ne hv.1 (by
      intro he
      exact Set.disjoint_left.mp (hpair C hC A hA hCA) hBv (he ▸ hl))
    have hvr : v < r := lt_of_le_of_ne hv.2 (by
      intro he
      exact Set.disjoint_left.mp (hpair C hC A hA hCA) hBv (he.symm ▸ hr))
    rcases lt_trichotomy u v with huv | huv | hvu
    · have hh := hminimal C hC u v huv hBu hBv
      change l.val < u.val at hlu
      change v.val < r.val at hvr
      linarith
    · exact huv
    · have hh := hminimal C hC v u hvu hBv hBu
      change l.val < v.val at hlv
      change u.val < r.val at hur
      linarith


/-- A shortest return is clean against the whole family when each other
member separates and actual local crossings switch its two sides. -/
theorem free_contact_finite_separating_family_has_clean_return
    {X : Type*} [TopologicalSpace X]
    (B : C(Interval,X)) (K : Finset C(Interval,X))
    (hfinite : {t : Interval | ∃ A ∈ K, B t ∈ Set.range A}.Finite)
    (hpair : ∀ A ∈ K, ∀ C ∈ K, A ≠ C → Disjoint (Set.range A) (Set.range C))
    (hsep : ∀ C ∈ K, ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (Set.range C)ᶜ ∧
      ∀ t : Interval, t ∈ Set.Ioo (0 : Interval) 1 → B t ∈ Set.range C →
        ∀ l r : Interval, l < t → t < r →
          ∃ u v : Interval, l < u ∧ u < t ∧ t < v ∧ v < r ∧
            ((B u ∈ U ∧ B v ∈ V) ∨ (B u ∈ V ∧ B v ∈ U)))
    (A₀ : C(Interval,X)) (hA₀ : A₀ ∈ K)
    (l₀ r₀ : Interval) (hlr₀ : l₀ < r₀)
    (hzero : B l₀ ∈ Set.range A₀) (hone : B r₀ ∈ Set.range A₀) :
    ∃ A ∈ K, ∃ l r : Interval,
      l < r ∧ B l ∈ Set.range A ∧ B r ∈ Set.range A ∧
      ∀ u : Interval, l < u → u < r →
        ∀ C ∈ K, B u ∉ Set.range C := by
  obtain ⟨A,hA,l,r,hlr,hl,hr,hgap,hsingle⟩ :=
    free_contact_finite_family_minimal_return B K hfinite hpair A₀ hA₀ l₀ r₀ hlr₀ hzero hone
  refine ⟨A,hA,l,r,hlr,hl,hr,?_⟩
  intro t hlt htr C hC htC
  by_cases hCA : C = A
  · exact hgap t hlt htr (hCA ▸ htC)
  obtain ⟨U,V,hU,hV,hUV,hcover,hcross⟩ := hsep C hC
  have hAS : Set.range A ⊆ U ∪ V := by
    rw [hcover]
    intro z hz
    exact fun hzC => Set.disjoint_left.mp (hpair A hA C hC (Ne.symm hCA)) hz hzC
  have hside := (isPreconnected_range A.continuous).subset_or_subset hU hV hUV hAS
  have htI : t ∈ Set.Ioo (0 : Interval) 1 :=
    ⟨lt_of_le_of_lt l.property.1 hlt, lt_of_lt_of_le htr r.property.2⟩
  have hc := hcross t htI htC l r hlt htr
  have hex : ∃ v ∈ Set.Ioo l r, v ≠ t ∧ B v ∈ Set.range C := by
    rcases hside with hAU | hAV
    · exact contact_crossing_inside_return_has_second_contact B B.continuous
        (Set.range C) U V hU hV hUV hcover l r t hlt htr (hAU hl) (hAU hr) hc
    · apply contact_crossing_inside_return_has_second_contact B B.continuous
        (Set.range C) V U hV hU hUV.symm (by rw [union_comm,hcover])
        l r t hlt htr (hAV hl) (hAV hr)
      obtain ⟨u,v,hlu,hut,htv,hvr,hh⟩ := hc
      exact ⟨u,v,hlu,hut,htv,hvr,hh.symm⟩
  obtain ⟨v,hv,hvt,hvC⟩ := hex
  exact hvt (hsingle C hC hCA v t ⟨hv.1.le,hv.2.le⟩ ⟨hlt.le,htr.le⟩ hvC htC)


end CoherentEndpointMotion.FreeBoundaryContactRepair
