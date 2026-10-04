import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalCrossingChartSides

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-- Inside the recorded closed support, the whole original anchor is exactly
its horizontal chart axis. -/
theorem contact_chart_whole_axis_iff
    {S : Type} [TopologicalSpace S] {F : Set S}
    {a b : C(Interval, ↥F)} {r s : Interval}
    (C : RegionalIsolatedContactChart F a b r s)
    (y : ↥F) (hy : y.val ∈ C.chart.source)
    (hyQ : C.chart y.val ∈ Plane.closedSquare 0 1) :
    y ∈ Set.range a ↔ C.chart y.val 1 = 0 := by
  constructor
  · intro hya
    have hytrace : y ∈ a '' Set.Icc C.aLeft C.aRight :=
      C.whole_a_trace ▸ (show y ∈ _ ∩ Set.range a from ⟨⟨hy,hyQ⟩,hya⟩)
    obtain ⟨t,ht,rfl⟩ := hytrace
    have hdiam : C.chart (a t).val ∈ {z : Plane | z ∈ Plane.closedSquare 0 1 ∧ z 1 = 0} :=
      C.anchor_diameter ▸ Set.mem_image_of_mem (fun u => C.chart (a u).val) ht
    exact hdiam.2
  · intro hzero
    have hdiam : C.chart y.val ∈
        (fun t : Interval => C.chart (a t).val) '' Set.Icc C.aLeft C.aRight :=
      C.anchor_diameter.symm ▸ (show C.chart y.val ∈ _ from ⟨hyQ,hzero⟩)
    obtain ⟨t,ht,he⟩ := hdiam
    have hat : a t ∈ {y : ↥F | y.val ∈ C.chart.source ∧
        C.chart y.val ∈ Plane.closedSquare 0 1} ∩ Set.range a :=
      C.whole_a_trace.symm ▸ Set.mem_image_of_mem a ht
    exact ⟨t,Subtype.ext (C.chart.injOn hat.1.1 hy he)⟩

/-- Restrict the approved actual chart to the literal region subtype. -/
theorem contact_chart_in_region
    {S : Type} [TopologicalSpace S] {F : Set S}
    {a b : C(Interval, ↥F)} {r s : Interval}
    (C : RegionalIsolatedContactChart F a b r s) :
    ∃ K : OpenPartialHomeomorph ↥F Plane,
      a r ∈ K.source ∧ K (a r) = 0 ∧
      (∀ y ∈ K.source, K y = C.chart y.val) ∧
      ∀ y ∈ K.source, y ∈ Set.range a ↔ K y 1 = 0 := by
  classical
  have har : a r ∈ {y : ↥F | y.val ∈ C.chart.source ∧
      C.chart y.val ∈ Plane.closedSquare 0 1} ∩ Set.range a := by
    rw [C.whole_a_trace]
    exact Set.mem_image_of_mem a ⟨C.a_cuts.2.1.le,C.a_cuts.2.2.1.le⟩
  have hpF : (a r).val ∈ interior F := C.closed_support_interior har.1
  let O : TopologicalSpace.Opens S := ⟨interior F,isOpen_interior⟩
  have hO : Nonempty O := ⟨⟨(a r).val,hpF⟩⟩
  let i : O → ↥F := Set.inclusion (show (O : Set S) ⊆ F from interior_subset)
  have hi : Topology.IsOpenEmbedding i :=
    Topology.IsOpenEmbedding.inclusion interior_subset
      (isOpen_interior.preimage continuous_subtype_val)
  let K₀ := (C.chart.subtypeRestr hO).lift_openEmbedding hi
  have hval (y : ↥F) (hy : y.val ∈ interior F) : K₀ y = C.chart y.val := by
    let z : O := ⟨y.val,hy⟩
    have hz : i z = y := Subtype.ext rfl
    rw [← hz,OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  let Q : Set ↥F := {y | y.val ∈ C.chart.source ∧
      C.chart y.val ∈ Plane.openSquare 0 1}
  have hQopen : IsOpen Q :=
    (C.chart.isOpen_inter_preimage (Plane.isOpen_openSquare 0 1)).preimage continuous_subtype_val
  let K := K₀.restr Q
  have hKsrc : K.source = K₀.source ∩ Q := by
    simp only [K,OpenPartialHomeomorph.restr_source,hQopen.interior_eq]
  have hKval (y : ↥F) (hy : y ∈ K.source) : K y = C.chart y.val := by
    change K₀ y = C.chart y.val
    have hyQ := ((hKsrc ▸ hy).2 : y ∈ Q)
    exact hval y (C.closed_support_interior
      ⟨hyQ.1,Plane.openSquare_subset_closedSquare 0 1 hyQ.2⟩)
  have harK : a r ∈ K.source := by
    rw [hKsrc]
    constructor
    · refine ⟨⟨(a r).val,hpF⟩,?_,rfl⟩
      rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact har.1.1
    · refine ⟨har.1.1,?_⟩
      rw [C.contact_at_origin]
      rw [mem_openSquare_zero_one]
      norm_num [Plane.supNorm]
  refine ⟨K,harK,(hKval _ harK).trans C.contact_at_origin,hKval,?_⟩
  intro y hy
  rw [hKval y hy]
  have hyQ := ((hKsrc ▸ hy).2 : y ∈ Q)
  exact contact_chart_whole_axis_iff C y hyQ.1
    (Plane.openSquare_subset_closedSquare 0 1 hyQ.2)

/-- A covering chart near one point of a lift sees only that lift of a
compact embedded interval. -/
theorem contact_cover_lift_locally_single
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (p : X → Y) (hp : IsCoveringMap p)
    (a : C(Interval,Y)) (ha : Function.Injective a)
    (A : C(Interval,X)) (hA : ∀ t, p (A t) = a t) (r : Interval) :
    ∃ N : Set X, IsOpen N ∧ A r ∈ N ∧
      ∀ z ∈ N, p z ∈ Set.range a ↔ z ∈ Set.range A := by
  obtain ⟨e,her,he⟩ := hp.isLocalHomeomorph (A r)
  let Z := (A ⁻¹' e.source)ᶜ
  have hZ : IsCompact Z := (e.open_source.preimage A.continuous).isClosed_compl.isCompact
  have hclosed : IsClosed (a '' Z) := (hZ.image a.continuous).isClosed
  let N := e.source ∩ p ⁻¹' (a '' Z)ᶜ
  have hN : IsOpen N := e.open_source.inter (hclosed.isOpen_compl.preimage hp.continuous)
  have hrN : A r ∈ N := by
    refine ⟨her,?_⟩
    change p (A r) ∉ a '' Z
    rw [hA]
    rintro ⟨t,ht,hte⟩
    have htr : t = r := ha hte
    exact ht (htr ▸ her)
  refine ⟨N,hN,hrN,?_⟩
  intro z hz
  constructor
  · rintro ⟨t,ht⟩
    have hAt : A t ∈ e.source := by
      by_contra hn
      exact hz.2 ⟨t,hn,ht⟩
    refine ⟨t,e.injOn hAt hz.1 ?_⟩
    rw [← he]
    exact (hA t).trans ht
  · rintro ⟨t,rfl⟩
    exact ⟨t,(hA t).symm⟩

/-- The actual regional crossing signs transfer to any covering lift and
force opposite global sides of a separating lift. -/
theorem regional_crossing_lift_switches_separating_sides
    {S X : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace X]
    {F : Set S} (p : X → ↥F) (hp : IsCoveringMap p)
    (a b : C(Interval, ↥F)) (ha : Topology.IsEmbedding a)
    (A B : C(Interval,X))
    (hAp : ∀ t, p (A t) = a t) (hBp : ∀ t, p (B t) = b t)
    (r s : Interval) (hrs : A r = B s)
    (C : RegionalIsolatedContactChart F a b r s) (hcross : C.OppositeSides)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = (Set.range A)ᶜ)
    (hfrontU : frontier U = Set.range A) (hfrontV : frontier V = Set.range A) :
    ∀ l u : Interval, l < s → s < u →
      ∃ v w : Interval, l < v ∧ v < s ∧ s < w ∧ w < u ∧
        ((B v ∈ U ∧ B w ∈ V) ∨ (B v ∈ V ∧ B w ∈ U)) := by
  classical
  obtain ⟨D,harD,hDz,hDval,hDaxis⟩ := contact_chart_in_region C
  obtain ⟨N,hN,hrN,hNsingle⟩ := contact_cover_lift_locally_single p hp a ha.injective A hAp r
  obtain ⟨e,her,he⟩ := hp.isLocalHomeomorph (A r)
  let K := (e.trans D).restr N
  have hKsrc : K.source = (e.source ∩ e ⁻¹' D.source) ∩ N := by
    simp only [K,OpenPartialHomeomorph.restr_source,hN.interior_eq,
      OpenPartialHomeomorph.trans_source]
  have hKval (z : X) (hz : z ∈ K.source) : K z = C.chart (p z).val := by
    have hzD : p z ∈ D.source := by
      rw [he]
      exact (hKsrc ▸ hz).1.2
    change D (e z) = C.chart (p z).val
    rw [← he]
    exact hDval _ hzD
  have hsK : B s ∈ K.source := by
    rw [← hrs,hKsrc]
    refine ⟨⟨her,?_⟩,hrN⟩
    change e (A r) ∈ D.source
    rw [← he,hAp]
    exact harD
  have hz : K (B s) = 0 := by
    rw [hKval _ hsK,← hrs,hAp,C.contact_at_origin]
  have haxis : ∀ z ∈ K.source, z ∈ Set.range A ↔ K z 1 = 0 := by
    intro z hz
    rw [← hNsingle z (hKsrc ▸ hz).2]
    have hzD : p z ∈ D.source := by rw [he]; exact (hKsrc ▸ hz).1.2
    change p z ∈ Set.range a ↔ D (e z) 1 = 0
    rw [← he]
    exact hDaxis _ hzD
  apply contact_chart_opposite_signs_switch_global_sides B (Set.range A) U V
    hU hV hdis hcover hfrontU hfrontV K s C.bLeft C.bRight
    C.b_cuts.2.1 C.b_cuts.2.2.1 hsK hz haxis
  rcases hcross with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · left
    constructor
    · intro t ht htK
      rw [hKval _ htK,hBp]
      exact hl t ht
    · intro t ht htK
      rw [hKval _ htK,hBp]
      exact hr t ht
  · right
    constructor
    · intro t ht htK
      rw [hKval _ htK,hBp]
      exact hl t ht
    · intro t ht htK
      rw [hKval _ htK,hBp]
      exact hr t ht

end RegionalEmbeddedFamily
