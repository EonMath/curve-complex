import CurveComplexGenusTwo.Topology.ActualRegionalContactGeometry.RegionalFiniteContactGeometry
import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalEmbeddedSubarcBetween

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

theorem contact_local_connected_arms_opposite_sides
    {X : Type*} [TopologicalSpace X] (L U V N A B : Set X) (p x y : X)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = Lᶜ) (hN : IsOpen N) (hpN : p ∈ N)
    (hpU : p ∈ closure U) (hpV : p ∈ closure V)
    (hsplit : N \ L = A ∪ B) (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hx : x ∈ A) (hy : y ∈ B) :
    (x ∈ U ∧ y ∈ V) ∨ (x ∈ V ∧ y ∈ U) := by
  have hAS : A ⊆ U ∪ V := by
    intro z hz
    rw [hcover]
    exact (hsplit.symm ▸ (show z ∈ A ∪ B from Or.inl hz)).2
  have hBS : B ⊆ U ∪ V := by
    intro z hz
    rw [hcover]
    exact (hsplit.symm ▸ (show z ∈ A ∪ B from Or.inr hz)).2
  have hbothU : ¬ (A ⊆ U ∧ B ⊆ U) := by
    rintro ⟨hAU,hBU⟩
    obtain ⟨z,hzN,hzV⟩ := mem_closure_iff.mp hpV N hN hpN
    have hzL : z ∉ L := by
      have : z ∈ U ∪ V := Or.inr hzV
      rw [hcover] at this
      exact this
    have hzAB : z ∈ A ∪ B := hsplit ▸ ⟨hzN,hzL⟩
    exact Set.disjoint_left.mp hdis (hzAB.elim (fun h => hAU h) (fun h => hBU h)) hzV
  have hbothV : ¬ (A ⊆ V ∧ B ⊆ V) := by
    rintro ⟨hAV,hBV⟩
    obtain ⟨z,hzN,hzU⟩ := mem_closure_iff.mp hpU N hN hpN
    have hzL : z ∉ L := by
      have : z ∈ U ∪ V := Or.inl hzU
      rw [hcover] at this
      exact this
    have hzAB : z ∈ A ∪ B := hsplit ▸ ⟨hzN,hzL⟩
    exact Set.disjoint_left.mp hdis hzU (hzAB.elim (fun h => hAV h) (fun h => hBV h))
  rcases hA.subset_or_subset hU hV hdis hAS with hAU | hAV <;>
    rcases hB.subset_or_subset hU hV hdis hBS with hBU | hBV
  · exact False.elim (hbothU ⟨hAU,hBU⟩)
  · exact Or.inl ⟨hAU hx,hBV hy⟩
  · exact Or.inr ⟨hAV hx,hBU hy⟩
  · exact False.elim (hbothV ⟨hAV,hBV⟩)


theorem contact_interval_separator_contact
    {X : Type*} [TopologicalSpace X] (F : Interval → X) (hF : Continuous F)
    (L U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = Lᶜ) (r s : Interval) (hrs : r < s)
    (hr : F r ∈ U) (hs : F s ∈ V) :
    ∃ t ∈ Set.Ioo r s, F t ∈ L := by
  by_contra h
  have havoid : F '' Set.Icc r s ⊆ U ∪ V := by
    rintro _ ⟨t,ht,rfl⟩
    rw [hcover]
    intro hmem
    have htstrict : t ∈ Set.Ioo r s := by
      constructor
      · rcases eq_or_lt_of_le ht.1 with heq | hlt
        · subst t
          have : F r ∈ Lᶜ := by rw [←hcover]; exact Or.inl hr
          exact False.elim (this hmem)
        · exact hlt
      · rcases eq_or_lt_of_le ht.2 with heq | hlt
        · subst t
          have : F s ∈ Lᶜ := by rw [←hcover]; exact Or.inr hs
          exact False.elim (this hmem)
        · exact hlt
    exact h ⟨t,htstrict,hmem⟩
  have hconn := (isPreconnected_Icc (a := r) (b := s)).image F hF.continuousOn
  rcases hconn.subset_or_subset hU hV hdis havoid with hu | hv
  · exact Set.disjoint_left.mp hdis (hu ⟨s,⟨hrs.le,le_rfl⟩,rfl⟩) hs
  · exact Set.disjoint_left.mp hdis hr (hv ⟨r,⟨le_rfl,hrs.le⟩,rfl⟩)

theorem contact_crossing_inside_return_has_second_contact
    {X : Type*} [TopologicalSpace X] (F : Interval → X) (hF : Continuous F)
    (L U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = Lᶜ) (r s u : Interval) (hru : r < u) (hus : u < s)
    (hr : F r ∈ U) (hs : F s ∈ U)
    (hcross : ∃ l w : Interval, r < l ∧ l < u ∧ u < w ∧ w < s ∧
      ((F l ∈ U ∧ F w ∈ V) ∨ (F l ∈ V ∧ F w ∈ U))) :
    ∃ v ∈ Set.Ioo r s, v ≠ u ∧ F v ∈ L := by
  obtain ⟨l,w,hrl,hlu,huw,hws,h⟩ := hcross
  rcases h with ⟨_,hw⟩ | ⟨hl,_⟩
  · obtain ⟨v,hv,hvL⟩ := contact_interval_separator_contact F hF L V U hV hU
      hdis.symm (by rw [union_comm,hcover]) w s hws hw hs
    exact ⟨v,⟨hru.trans (huw.trans hv.1),hv.2⟩,ne_of_gt (huw.trans hv.1),hvL⟩
  · obtain ⟨v,hv,hvL⟩ := contact_interval_separator_contact F hF L U V hU hV hdis
      hcover r l hrl hr hl
    exact ⟨v,⟨hv.1,hv.2.trans (hlu.trans hus)⟩,ne_of_lt (hv.2.trans hlu),hvL⟩

theorem contact_finite_family_minimal_return
    {X : Type*} [TopologicalSpace X]
    (B : C(Interval,X))
    (K : Finset C(Interval,X))
    (hfinite : {t : Interval | ∃ A ∈ K, B t ∈ Set.range A}.Finite)
    (hpair : ∀ A ∈ K, ∀ C ∈ K, A ≠ C → Disjoint (Set.range A) (Set.range C))
    (A₀ : C(Interval,X)) (hA₀ : A₀ ∈ K)
    (hzero : B 0 ∈ Set.range A₀) (hone : B 1 ∈ Set.range A₀) :
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
  have hDone : (1 : ℝ) ∈ D := by
    refine ⟨A₀,hA₀,0,1,by norm_num,hzero,hone,?_⟩
    norm_num
  obtain ⟨d,hd,hmin⟩ := Set.exists_min_image D id hDfinite ⟨1,hDone⟩
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
theorem contact_finite_separating_family_has_clean_return
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
    (hzero : B 0 ∈ Set.range A₀) (hone : B 1 ∈ Set.range A₀) :
    ∃ A ∈ K, ∃ l r : Interval,
      l < r ∧ B l ∈ Set.range A ∧ B r ∈ Set.range A ∧
      ∀ u : Interval, l < u → u < r →
        ∀ C ∈ K, B u ∉ Set.range C := by
  obtain ⟨A,hA,l,r,hlr,hl,hr,hgap,hsingle⟩ :=
    contact_finite_family_minimal_return B K hfinite hpair A₀ hA₀ hzero hone
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

end RegionalEmbeddedFamily
