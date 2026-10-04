import CurveComplexGenusTwo.Topology.FrontierCircle.BandUnionProbe
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import CurveComplexGenusTwo.Topology.FrontierCircle.SeamGluingProbe
import CurveComplexGenusTwo.Topology.FrontierCircle.PathGluingProbe

open Set Topology unitInterval
namespace CurveComplex

theorem embedded_band_open_rectangle_interior
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (B : I × BandWidth → S) (hB : IsEmbedding B)
    (t : I) (u : BandWidth)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hu0 : -1 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    B (t, u) ∈ interior (Set.range B) := by
  let f : EuclideanSpace ℝ (Fin 2) → S := fun z =>
    B (projIcc 0 1 zero_le_one (z 0), projIcc (-1) 1 (by norm_num) (z 1))
  let U : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | z 0 ∈ Ioo 0 1 ∧ z 1 ∈ Ioo (-1) 1}
  have hU : IsOpen U := (isOpen_Ioo.preimage (by fun_prop)).inter
    (isOpen_Ioo.preimage (by fun_prop))
  have hf : Continuous f := hB.continuous.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk
      (continuous_projIcc.comp (by fun_prop)))
  have hi : InjOn f U := by
    intro z hz w hw he
    have hh := hB.injective he
    have h0 := congrArg (fun q : I × BandWidth => (q.1 : ℝ)) hh
    have h1 := congrArg (fun q : I × BandWidth => (q.2 : ℝ)) hh
    simp only [projIcc_of_mem zero_le_one ⟨hz.1.1.le, hz.1.2.le⟩,
      projIcc_of_mem zero_le_one ⟨hw.1.1.le, hw.1.2.le⟩] at h0
    simp only [projIcc_of_mem (show (-1 : ℝ) ≤ 1 by norm_num)
        ⟨hz.2.1.le, hz.2.2.le⟩,
      projIcc_of_mem (show (-1 : ℝ) ≤ 1 by norm_num)
        ⟨hw.2.1.le, hw.2.2.le⟩] at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hopen : IsOpen (f '' U) :=
    surface_invariance_of_domain_probe f U hU hf.continuousOn hi
  have hsub : f '' U ⊆ Set.range B := by
    rintro z ⟨w, hw, rfl⟩
    exact Set.mem_range_self _
  apply (hopen.subset_interior_iff.mpr hsub)
  refine ⟨Schoenflies.Plane.mk t u, ⟨⟨ht0, ht1⟩, ⟨hu0, hu1⟩⟩, ?_⟩
  simp [f, projIcc_of_mem zero_le_one t.property,
    projIcc_of_mem (show (-1 : ℝ) ≤ 1 by norm_num) u.property]

#print axioms embedded_band_open_rectangle_interior

theorem frontier_band_point_on_parameter_edge
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (B : I × BandWidth → S) (hB : IsEmbedding B)
    (N : Set S) (hBN : Set.range B ⊆ N)
    (t : I) (u : BandWidth) (hfront : B (t, u) ∈ frontier N) :
    t = 0 ∨ t = 1 ∨ u = ⟨-1, by norm_num⟩ ∨ u = ⟨1, by norm_num⟩ := by
  by_contra h
  push_neg at h
  obtain ⟨ht0, ht1, hu0, hu1⟩ := h
  have ht0' : 0 < (t : ℝ) :=
    lt_of_le_of_ne t.property.1 (by
      intro he
      exact ht0 (Subtype.ext he.symm))
  have ht1' : (t : ℝ) < 1 :=
    lt_of_le_of_ne t.property.2 (by
      intro he
      exact ht1 (Subtype.ext he))
  have hu0' : -1 < (u : ℝ) :=
    lt_of_le_of_ne u.property.1 (by
      intro he
      exact hu0 (Subtype.ext he.symm))
  have hu1' : (u : ℝ) < 1 :=
    lt_of_le_of_ne u.property.2 (by
      intro he
      exact hu1 (Subtype.ext he))
  have hint := embedded_band_open_rectangle_interior B hB t u ht0' ht1' hu0' hu1'
  exact hfront.2 (interior_mono hBN hint)

#print axioms frontier_band_point_on_parameter_edge

theorem compatibleOutsideBands_frontier_subset_parameter_edges
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
    frontier N ⊆
      (Set.range D.square \ D.openSquare) ∪
      {x | ∃ t : I, ∃ u : BandWidth,
        B.first (t, u) = x ∧
          (t = 0 ∨ t = 1 ∨ u = ⟨-1, by norm_num⟩ ∨ u = ⟨1, by norm_num⟩)} ∪
      {x | ∃ t : I, ∃ u : BandWidth,
        B.second (t, u) = x ∧
          (t = 0 ∨ t = 1 ∨ u = ⟨-1, by norm_num⟩ ∨ u = ⟨1, by norm_num⟩)} := by
  let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
  have hcompact : IsCompact N := (compatibleOutsideBands_compact_connected_cover_probe D B).1
  have hclosed : IsClosed N := hcompact.isClosed
  have hOpenSub : D.openSquare ⊆ N := by
    intro x hx
    rw [D.openSquare_eq] at hx
    exact Or.inl (Or.inl (Set.image_subset_range _ _ hx))
  have hfirst : Set.range B.first ⊆ N := fun _ hx => Or.inl (Or.inr hx)
  have hsecond : Set.range B.second ⊆ N := fun _ hx => Or.inr hx
  dsimp only
  intro x hx
  have hxN : x ∈ N := by
    have hc := frontier_subset_closure hx
    change x ∈ closure N at hc
    simpa only [hclosed.closure_eq] using hc
  rcases hxN with (hsquare | hfirst') | hsecond'
  · refine Or.inl (Or.inl ⟨hsquare, ?_⟩)
    intro hopen
    exact hx.2 ((D.openSquare_open.subset_interior_iff.mpr hOpenSub) hopen)
  · obtain ⟨p, rfl⟩ := hfirst'
    refine Or.inl (Or.inr ⟨p.1, p.2, rfl, ?_⟩)
    exact frontier_band_point_on_parameter_edge B.first B.first_embedded N hfirst
      p.1 p.2 hx
  · obtain ⟨p, rfl⟩ := hsecond'
    refine Or.inr ⟨p.1, p.2, rfl, ?_⟩
    exact frontier_band_point_on_parameter_edge B.second B.second_embedded N hsecond
      p.1 p.2 hx

#print axioms compatibleOutsideBands_frontier_subset_parameter_edges

theorem embedded_band_lateral_frontier
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (B : I × BandWidth → S) (hB : IsEmbedding B)
    (t : I) (u : BandWidth)
    (hu : (u : ℝ) = -1 ∨ (u : ℝ) = 1) :
    B (t, u) ∈ frontier (Set.range B) := by
  let K : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | z 0 ∈ Icc (0 : ℝ) 1 ∧ z 1 ∈ Icc (-1 : ℝ) 1}
  let e : I × BandWidth → EuclideanSpace ℝ (Fin 2) :=
    fun p => Schoenflies.Plane.mk p.1 p.2
  have he : Continuous e := by fun_prop
  have hRange : Set.range e = K := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1.property, p.2.property⟩
    · intro hz
      refine ⟨(⟨z 0, hz.1⟩, ⟨z 1, hz.2⟩), ?_⟩
      ext i
      fin_cases i <;> rfl
  have hK : IsCompact K := by
    rw [← hRange]
    exact isCompact_range he
  let f : K → S := fun z =>
    B (⟨z.val 0, z.property.1⟩, ⟨z.val 1, z.property.2⟩)
  have hfC : Continuous f := by
    fun_prop
  have hfI : Function.Injective f := by
    intro z w h
    have hh := hB.injective h
    apply Subtype.ext
    ext i
    fin_cases i
    · exact congrArg (fun p : I × BandWidth => (p.1 : ℝ)) hh
    · exact congrArg (fun p : I × BandWidth => (p.2 : ℝ)) hh
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hf : IsEmbedding f := (hfC.isClosedEmbedding hfI).isEmbedding
  have hRangeF : Set.range f = Set.range B := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact Set.mem_range_self _
    · rintro ⟨p, rfl⟩
      refine ⟨⟨e p, ?_⟩, ?_⟩
      · rw [← hRange]
        exact Set.mem_range_self p
      · rfl
  let z : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk t u
  have hz : z ∈ K := ⟨t.property, u.property⟩
  have hKclosed : IsClosed K := hK.isClosed
  have hzFront : z ∈ frontier K := by
    rw [hKclosed.frontier_eq]
    refine ⟨hz, ?_⟩
    intro hi
    have hsub : K ⊆ (fun z : EuclideanSpace ℝ (Fin 2) => z 1) ⁻¹'
        Icc (-1 : ℝ) 1 := fun _ hw => hw.2
    have hpre := interior_mono hsub hi
    have hInt := (PiLp.isOpenMap_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1).interior_preimage_subset_preimage_interior hpre
    simp only [interior_Icc, mem_preimage, mem_Ioo] at hInt
    rcases hu with hu | hu <;> simp [z, hu] at hInt
  have hfront := embedded_compact_planar_region_frontier_probe K hK f hf
  rw [← hRangeF, ← hfront]
  refine ⟨⟨z, hz⟩, hzFront, ?_⟩
  rfl

#print axioms embedded_band_lateral_frontier

theorem mem_frontier_union_of_not_mem_closed
    {S : Type*} [TopologicalSpace S] {A C : Set S}
    (hC : IsClosed C) {x : S} (hxC : x ∉ C)
    (hxA : x ∈ frontier A) : x ∈ frontier (A ∪ C) := by
  refine ⟨closure_mono Set.subset_union_left hxA.1, ?_⟩
  intro hi
  have hlocal : x ∈ interior ((A ∪ C) ∩ Cᶜ) := by
    rw [interior_inter, hC.isOpen_compl.interior_eq]
    exact ⟨hi, hxC⟩
  have hsubset : (A ∪ C) ∩ Cᶜ ⊆ A := by
    rintro y ⟨hy, hyC⟩
    rcases hy with hy | hy
    · exact hy
    · exact (hyC hy).elim
  exact hxA.2 (interior_mono hsubset hlocal)

theorem compatibleOutsideBands_first_lateral_frontier
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) (t : I) (u : BandWidth)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hu : (u : ℝ) = -1 ∨ (u : ℝ) = 1) :
    B.first (t, u) ∈ frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) := by
  have hnotSquare : B.first (t, u) ∉ Set.range D.square := by
    intro h
    have hmeet : B.first (t, u) ∈
        Set.range B.first ∩ Set.range D.square :=
      ⟨Set.mem_range_self _, h⟩
    rw [B.first_square] at hmeet
    rcases hmeet with ⟨v, hv⟩ | ⟨v, hv⟩
    · have hp := B.first_embedded.injective (hv.symm.trans (B.first_bottom v).symm)
      exact ht0 (congrArg Prod.fst hp)
    · have hp := B.first_embedded.injective (hv.symm.trans (B.first_top v).symm)
      exact ht1 (congrArg Prod.fst hp)
  have hnotSecond : B.first (t, u) ∉ Set.range B.second :=
    fun h => Set.disjoint_left.mp B.bands_disjoint (Set.mem_range_self _) h
  have hCclosed : IsClosed (Set.range D.square ∪ Set.range B.second) :=
    (isCompact_range D.square_embedded.continuous).isClosed.union
      (isCompact_range B.second_embedded.continuous).isClosed
  have heq : Set.range B.first ∪
      (Set.range D.square ∪ Set.range B.second) =
      Set.range D.square ∪ Set.range B.first ∪ Set.range B.second := by
    ext x
    simp only [Set.mem_union]
    tauto
  rw [← heq]
  apply mem_frontier_union_of_not_mem_closed hCclosed
  · exact fun h => h.elim hnotSquare hnotSecond
  · exact embedded_band_lateral_frontier B.first B.first_embedded t u hu

#print axioms compatibleOutsideBands_first_lateral_frontier

theorem compatibleOutsideBands_second_lateral_frontier
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) (t : I) (u : BandWidth)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hu : (u : ℝ) = -1 ∨ (u : ℝ) = 1) :
    B.second (t, u) ∈ frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) := by
  have hnotSquare : B.second (t, u) ∉ Set.range D.square := by
    intro h
    have hmeet : B.second (t, u) ∈
        Set.range B.second ∩ Set.range D.square :=
      ⟨Set.mem_range_self _, h⟩
    rw [B.second_square] at hmeet
    rcases hmeet with ⟨v, hv⟩ | ⟨v, hv⟩
    · have hp := B.second_embedded.injective (hv.symm.trans (B.second_left v).symm)
      exact ht0 (congrArg Prod.fst hp)
    · have hp := B.second_embedded.injective (hv.symm.trans (B.second_right v).symm)
      exact ht1 (congrArg Prod.fst hp)
  have hnotFirst : B.second (t, u) ∉ Set.range B.first :=
    fun h => Set.disjoint_left.mp B.bands_disjoint h (Set.mem_range_self _)
  have hCclosed : IsClosed (Set.range D.square ∪ Set.range B.first) :=
    (isCompact_range D.square_embedded.continuous).isClosed.union
      (isCompact_range B.first_embedded.continuous).isClosed
  have heq : Set.range B.second ∪
      (Set.range D.square ∪ Set.range B.first) =
      Set.range D.square ∪ Set.range B.first ∪ Set.range B.second := by
    ext x
    simp only [Set.mem_union]
    tauto
  rw [← heq]
  apply mem_frontier_union_of_not_mem_closed hCclosed
  · exact fun h => h.elim hnotSquare hnotFirst
  · exact embedded_band_lateral_frontier B.second B.second_embedded t u hu

#print axioms compatibleOutsideBands_second_lateral_frontier

theorem embedded_crossing_square_frontier
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (r : ℝ) (D : Metric.closedBall ((0, 0) : ℝ × ℝ) r → S)
    (hD : IsEmbedding D)
    (z : Metric.closedBall ((0, 0) : ℝ × ℝ) r)
    (hz : (z : ℝ × ℝ) ∈ frontier (Metric.closedBall ((0, 0) : ℝ × ℝ) r)) :
    D z ∈ frontier (Set.range D) := by
  let e : (ℝ × ℝ) ≃ₜ EuclideanSpace ℝ (Fin 2) := {
    toFun := fun p => Schoenflies.Plane.mk p.1 p.2
    invFun := fun q => (q 0, q 1)
    left_inv := by intro p; rfl
    right_inv := by
      intro q
      ext i
      fin_cases i <;> rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let K : Set (EuclideanSpace ℝ (Fin 2)) :=
    {q | e.symm q ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) r}
  have hKimage : K = e '' Metric.closedBall ((0, 0) : ℝ × ℝ) r := by
    ext q
    constructor
    · intro hq
      exact ⟨e.symm q, hq, e.apply_symm_apply q⟩
    · rintro ⟨p, hp, rfl⟩
      change e.symm (e p) ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) r
      simpa using hp
  have hK : IsCompact K := by
    rw [hKimage]
    exact (isCompact_closedBall ((0, 0) : ℝ × ℝ) r).image e.continuous
  let f : K → S := fun q => D ⟨e.symm q, q.property⟩
  have hfC : Continuous f := by
    have hcoord : Continuous (fun q : K => e.symm q) :=
      e.symm.continuous.comp continuous_subtype_val
    exact hD.continuous.comp (hcoord.subtype_mk (fun q => q.property))
  have hfI : Function.Injective f := by
    intro q w h
    have hh := hD.injective h
    apply Subtype.ext
    have he := congrArg (fun p : Metric.closedBall ((0, 0) : ℝ × ℝ) r => (p : ℝ × ℝ)) hh
    exact e.symm.injective he
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hf : IsEmbedding f := (hfC.isClosedEmbedding hfI).isEmbedding
  have hRangeF : Set.range f = Set.range D := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact Set.mem_range_self _
    · rintro ⟨p, rfl⟩
      refine ⟨⟨e p, ?_⟩, ?_⟩
      · change e.symm (e p) ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) r
        simpa using p.property
      · rfl
  have hzK : e z ∈ K := by
    change e.symm (e z) ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) r
    simpa using z.property
  have hzFrontK : e z ∈ frontier K := by
    rw [hKimage, ← e.image_frontier]
    exact ⟨z, hz, rfl⟩
  have hfront := embedded_compact_planar_region_frontier_probe K hK f hf
  rw [← hRangeF, ← hfront]
  refine ⟨⟨e z, hzK⟩, hzFrontK, ?_⟩
  rfl

#print axioms embedded_crossing_square_frontier

theorem compatibleOutsideBands_exposed_square_frontier
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D)
    (z : Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius)
    (hz : (z : ℝ × ℝ) ∈
      frontier (Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius))
    (hfirst : D.square z ∉ Set.range B.first)
    (hsecond : D.square z ∉ Set.range B.second) :
    D.square z ∈ frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) := by
  have hCclosed : IsClosed (Set.range B.first ∪ Set.range B.second) :=
    (isCompact_range B.first_embedded.continuous).isClosed.union
      (isCompact_range B.second_embedded.continuous).isClosed
  have heq : Set.range D.square ∪
      (Set.range B.first ∪ Set.range B.second) =
      Set.range D.square ∪ Set.range B.first ∪ Set.range B.second := by
    rw [Set.union_assoc]
  rw [← heq]
  apply mem_frontier_union_of_not_mem_closed hCclosed
  · exact fun h => h.elim hfirst hsecond
  · exact embedded_crossing_square_frontier D.radius D.square D.square_embedded z hz

#print axioms compatibleOutsideBands_exposed_square_frontier

theorem closed_contains_band_side_endpoints
    {S : Type*} [TopologicalSpace S]
    (F : I → S) (hF : Continuous F) (C : Set S) (hC : IsClosed C)
    (hinner : ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → F t ∈ C) :
    ∀ t : I, F t ∈ C := by
  let U : Set I := {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
  have hImage : ((↑) : I → ℝ) '' U = Ioo (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      exact ⟨⟨x, ⟨hx.1.le, hx.2.le⟩⟩, hx, rfl⟩
  have hDense : Dense U := Subtype.dense_iff.mpr (by
    intro x hx
    rw [hImage, closure_Ioo (by norm_num)]
    exact hx)
  have hPreClosed : IsClosed (F ⁻¹' C) := hC.preimage hF
  have hSub : U ⊆ F ⁻¹' C := by
    intro t ht
    exact hinner t ht.1 ht.2
  have hClosure : closure U ⊆ F ⁻¹' C := closure_minimal hSub hPreClosed
  intro t
  exact hClosure (hDense t)

theorem compatibleOutsideBands_first_lateral_frontier_all
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) (t : I) (u : BandWidth)
    (hu : (u : ℝ) = -1 ∨ (u : ℝ) = 1) :
    B.first (t, u) ∈ frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) := by
  let F : I → S := fun t => B.first (t, u)
  have hF : Continuous F :=
    B.first_embedded.continuous.comp (continuous_id.prodMk continuous_const)
  apply closed_contains_band_side_endpoints F hF _ isClosed_frontier
    (fun s hs0 hs1 => ?_) t
  apply compatibleOutsideBands_first_lateral_frontier D B s u
  · intro he
    have hh := congrArg Subtype.val he
    dsimp at hh
    linarith
  · intro he
    have hh := congrArg Subtype.val he
    dsimp at hh
    linarith
  · exact hu

theorem compatibleOutsideBands_second_lateral_frontier_all
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) (t : I) (u : BandWidth)
    (hu : (u : ℝ) = -1 ∨ (u : ℝ) = 1) :
    B.second (t, u) ∈ frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) := by
  let F : I → S := fun t => B.second (t, u)
  have hF : Continuous F :=
    B.second_embedded.continuous.comp (continuous_id.prodMk continuous_const)
  apply closed_contains_band_side_endpoints F hF _ isClosed_frontier
    (fun s hs0 hs1 => ?_) t
  apply compatibleOutsideBands_second_lateral_frontier D B s u
  · intro he
    have hh := congrArg Subtype.val he
    dsimp at hh
    linarith
  · intro he
    have hh := congrArg Subtype.val he
    dsimp at hh
    linarith
  · exact hu

#print axioms compatibleOutsideBands_first_lateral_frontier_all
#print axioms compatibleOutsideBands_second_lateral_frontier_all

theorem attached_band_zero_port_interior
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : I × BandWidth → S) (hB : IsEmbedding B) (i j : Fin 4)
    (h0 : ∀ t, B (0, t) = D.square (squarePort D.radius D.radius_pos i t))
    (h1 : ∀ t, B (1, t) = D.square (squarePort D.radius D.radius_pos j t))
    (hmeet : Set.range B ∩ Set.range D.square =
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos i t)) ∪
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos j t)))
    (u : BandWidth) (hu0 : -1 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    B (0, u) ∈ interior (Set.range D.square ∪ Set.range B) := by
  let L : BandWidth × I → S := fun z =>
    D.ends i (z.1, ⟨-(z.2 : ℝ), by
      constructor <;> linarith [z.2.property.1, z.2.property.2]⟩)
  let R : BandWidth × I → S := fun z =>
    B (⟨(z.2 : ℝ) / 2, by
      constructor <;> linarith [z.2.property.1, z.2.property.2]⟩, z.1)
  have hLC : Continuous L := (D.ends_embedded i).continuous.comp
    (continuous_fst.prodMk
      (((continuous_subtype_val.comp continuous_snd).neg).subtype_mk _))
  have hRC : Continuous R := hB.continuous.comp
    ((((continuous_subtype_val.comp continuous_snd).div_const 2).subtype_mk _).prodMk
      continuous_fst)
  have hLI : Function.Injective L := by
    intro z w he
    have hh := (D.ends_embedded i).injective he
    apply Prod.ext
    · exact congrArg (fun x : EndRectangle => x.1) hh
    · apply Subtype.ext
      have hv := congrArg (fun x : EndRectangle => (x.2 : ℝ)) hh
      dsimp at hv
      exact neg_injective hv
  have hRI : Function.Injective R := by
    intro z w he
    have hh := hB.injective he
    apply Prod.ext
    · exact congrArg Prod.snd hh
    · apply Subtype.ext
      have hv := congrArg (fun x : I × BandWidth => (x.1 : ℝ)) hh
      dsimp at hv
      linarith
  have hLR (t : BandWidth) : L (t, 0) = R (t, 0) := by
    change D.ends i (t, ⟨-(0 : I), _⟩) = B (⟨(0 : I) / 2, _⟩, t)
    simpa using (D.ends_seam i t).trans (h0 t).symm
  have hLsub : Set.range L ⊆ Set.range D.square := by
    rintro z ⟨w, rfl⟩
    apply (D.ends_square i _).mpr
    change -(w.2 : ℝ) ≤ 0
    exact neg_nonpos.mpr w.2.property.1
  have hRsub : Set.range R ⊆ Set.range B := by
    rintro z ⟨w, rfl⟩
    exact Set.mem_range_self _
  have hLRmeet : Set.range L ∩ Set.range R =
      Set.range (fun t => L (t, 0)) := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨z, rfl⟩, w, he⟩
      have hx : L z ∈ Set.range B ∩ Set.range D.square :=
        ⟨hRsub ⟨w, he⟩, hLsub (Set.mem_range_self z)⟩
      rw [hmeet] at hx
      rcases hx with ⟨v, hv⟩ | ⟨v, hv⟩
      · have he' : L z = D.ends i (v, ⟨0, by norm_num⟩) :=
          hv.symm.trans (D.ends_seam i v).symm
        have hh := (D.ends_embedded i).injective he'
        have hz0 := congrArg (fun x : EndRectangle => (x.2 : ℝ)) hh
        dsimp at hz0
        have hz : z.2 = 0 := Subtype.ext (neg_eq_zero.mp hz0)
        refine ⟨z.1, ?_⟩
        rw [← hz]
      · have hb : R w = B (1, v) := he.trans (hv.symm.trans (h1 v).symm)
        have hh := hB.injective hb
        have hw := congrArg (fun x : I × BandWidth => (x.1 : ℝ)) hh
        dsimp at hw
        norm_num at hw
        exfalso
        linarith [w.2.property.2]
    · rintro x ⟨t, rfl⟩
      exact ⟨Set.mem_range_self _, ⟨(t, 0), (hLR t).symm⟩⟩
  have hin := glued_half_rectangles_seam_interior_probe L R
    (hLC.isClosedEmbedding hLI).isEmbedding
    (hRC.isClosedEmbedding hRI).isEmbedding
    hLR hLRmeet u hu0 hu1
  have hsub : Set.range L ∪ Set.range R ⊆
      Set.range D.square ∪ Set.range B := Set.union_subset_union hLsub hRsub
  have hfinal := interior_mono hsub hin
  have he : L (u, 0) = B (0, u) := by
    simpa [R] using hLR u
  rwa [he] at hfinal

#print axioms attached_band_zero_port_interior

theorem attached_band_one_port_interior
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : I × BandWidth → S) (hB : IsEmbedding B) (i j : Fin 4)
    (h0 : ∀ t, B (0, t) = D.square (squarePort D.radius D.radius_pos i t))
    (h1 : ∀ t, B (1, t) = D.square (squarePort D.radius D.radius_pos j t))
    (hmeet : Set.range B ∩ Set.range D.square =
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos i t)) ∪
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos j t)))
    (u : BandWidth) (hu0 : -1 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    B (1, u) ∈ interior (Set.range D.square ∪ Set.range B) := by
  let e : (I × BandWidth) ≃ₜ (I × BandWidth) :=
    unitInterval.symmHomeomorph.prodCongr (Homeomorph.refl _)
  let C : I × BandWidth → S := B ∘ e
  have hC : IsEmbedding C := hB.comp e.isEmbedding
  have hrange : Set.range C = Set.range B := by
    change Set.range (B ∘ e) = _
    rw [Set.range_comp, e.surjective.range_eq, Set.image_univ]
  have hC0 (t) : C (0, t) = D.square (squarePort D.radius D.radius_pos j t) := by
    simpa [C, e] using h1 t
  have hC1 (t) : C (1, t) = D.square (squarePort D.radius D.radius_pos i t) := by
    simpa [C, e] using h0 t
  have hCm : Set.range C ∩ Set.range D.square =
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos j t)) ∪
      Set.range (fun t => D.square (squarePort D.radius D.radius_pos i t)) := by
    rw [hrange, hmeet, Set.union_comm]
  have hh := attached_band_zero_port_interior D C hC j i hC0 hC1 hCm u hu0 hu1
  rw [hrange] at hh
  simpa [C, e] using hh

#print axioms attached_band_one_port_interior

theorem compatibleOutsideBands_four_open_ports_interior
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) (u : BandWidth)
    (hu0 : -1 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
    B.first (0, u) ∈ interior N ∧ B.first (1, u) ∈ interior N ∧
      B.second (0, u) ∈ interior N ∧ B.second (1, u) ∈ interior N := by
  have hfirst : Set.range D.square ∪ Set.range B.first ⊆
      Set.range D.square ∪ Set.range B.first ∪ Set.range B.second :=
    Set.subset_union_left
  have hsecond : Set.range D.square ∪ Set.range B.second ⊆
      Set.range D.square ∪ Set.range B.first ∪ Set.range B.second := by
    intro x hx
    rcases hx with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  constructor
  · exact interior_mono hfirst
      (attached_band_zero_port_interior D B.first B.first_embedded 2 0
        B.first_bottom B.first_top B.first_square u hu0 hu1)
  constructor
  · exact interior_mono hfirst
      (attached_band_one_port_interior D B.first B.first_embedded 2 0
        B.first_bottom B.first_top B.first_square u hu0 hu1)
  constructor
  · exact interior_mono hsecond
      (attached_band_zero_port_interior D B.second B.second_embedded 3 1
        B.second_left B.second_right B.second_square u hu0 hu1)
  · exact interior_mono hsecond
      (attached_band_one_port_interior D B.second B.second_embedded 3 1
        B.second_left B.second_right B.second_square u hu0 hu1)

#print axioms compatibleOutsideBands_four_open_ports_interior

def bandLateralSides {S : Type*} [TopologicalSpace S]
    (B : I × BandWidth → S) : Set S :=
  Set.range (fun t : I => B (t, ⟨-1, by norm_num⟩)) ∪
    Set.range (fun t : I => B (t, ⟨1, by norm_num⟩))

theorem compatibleOutsideBands_first_frontier_mem_lateral
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) {x : S}
    (hx : x ∈ frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second))
    (hfirst : x ∈ Set.range B.first) : x ∈ bandLateralSides B.first := by
  obtain ⟨p, rfl⟩ := hfirst
  have hNfirst : Set.range B.first ⊆
      Set.range D.square ∪ Set.range B.first ∪ Set.range B.second :=
    fun _ h => Or.inl (Or.inr h)
  have hedge := frontier_band_point_on_parameter_edge B.first B.first_embedded _
    hNfirst p.1 p.2 hx
  by_cases hlow : p.2 = ⟨-1, by norm_num⟩
  · exact Or.inl ⟨p.1, by
      change B.first (p.1, ⟨-1, by norm_num⟩) = B.first (p.1, p.2)
      rw [hlow]⟩
  by_cases hhigh : p.2 = ⟨1, by norm_num⟩
  · exact Or.inr ⟨p.1, by
      change B.first (p.1, ⟨1, by norm_num⟩) = B.first (p.1, p.2)
      rw [hhigh]⟩
  have hu0 : -1 < (p.2 : ℝ) := lt_of_le_of_ne p.2.property.1 (by
    intro he
    exact hlow (Subtype.ext he.symm))
  have hu1 : (p.2 : ℝ) < 1 := lt_of_le_of_ne p.2.property.2 (by
    intro he
    exact hhigh (Subtype.ext he))
  have hports := compatibleOutsideBands_four_open_ports_interior D B p.2 hu0 hu1
  change B.first (p.1, p.2) ∈ frontier
    (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) at hx
  dsimp only at hports
  rcases hedge with ht0 | ht1 | hu | hu
  · rw [ht0] at hx
    exact (hx.2 hports.1).elim
  · rw [ht1] at hx
    exact (hx.2 hports.2.1).elim
  · exact (hlow hu).elim
  · exact (hhigh hu).elim

theorem compatibleOutsideBands_second_frontier_mem_lateral
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) {x : S}
    (hx : x ∈ frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second))
    (hsecond : x ∈ Set.range B.second) : x ∈ bandLateralSides B.second := by
  obtain ⟨p, rfl⟩ := hsecond
  have hNsecond : Set.range B.second ⊆
      Set.range D.square ∪ Set.range B.first ∪ Set.range B.second :=
    fun _ h => Or.inr h
  have hedge := frontier_band_point_on_parameter_edge B.second B.second_embedded _
    hNsecond p.1 p.2 hx
  by_cases hlow : p.2 = ⟨-1, by norm_num⟩
  · exact Or.inl ⟨p.1, by
      change B.second (p.1, ⟨-1, by norm_num⟩) = B.second (p.1, p.2)
      rw [hlow]⟩
  by_cases hhigh : p.2 = ⟨1, by norm_num⟩
  · exact Or.inr ⟨p.1, by
      change B.second (p.1, ⟨1, by norm_num⟩) = B.second (p.1, p.2)
      rw [hhigh]⟩
  have hu0 : -1 < (p.2 : ℝ) := lt_of_le_of_ne p.2.property.1 (by
    intro he
    exact hlow (Subtype.ext he.symm))
  have hu1 : (p.2 : ℝ) < 1 := lt_of_le_of_ne p.2.property.2 (by
    intro he
    exact hhigh (Subtype.ext he))
  have hports := compatibleOutsideBands_four_open_ports_interior D B p.2 hu0 hu1
  change B.second (p.1, p.2) ∈ frontier
    (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) at hx
  dsimp only at hports
  rcases hedge with ht0 | ht1 | hu | hu
  · rw [ht0] at hx
    exact (hx.2 hports.2.2.1).elim
  · rw [ht1] at hx
    exact (hx.2 hports.2.2.2).elim
  · exact (hlow hu).elim
  · exact (hhigh hu).elim

#print axioms compatibleOutsideBands_first_frontier_mem_lateral
#print axioms compatibleOutsideBands_second_frontier_mem_lateral

theorem compatibleOutsideBands_square_frontier_parameter
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D)
    (z : Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius)
    (hz : D.square z ∈ frontier
      (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second)) :
    (z : ℝ × ℝ) ∈
      frontier (Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius) := by
  have hOpenSub : D.openSquare ⊆
      Set.range D.square ∪ Set.range B.first ∪ Set.range B.second := by
    intro x hx
    rw [D.openSquare_eq] at hx
    exact Or.inl (Or.inl (Set.image_subset_range _ _ hx))
  have hnotOpen : D.square z ∉ D.openSquare := by
    intro h
    exact hz.2 ((D.openSquare_open.subset_interior_iff.mpr hOpenSub) h)
  have hnotBall : (z : ℝ × ℝ) ∉ Metric.ball (0, 0) D.radius := by
    intro h
    apply hnotOpen
    rw [D.openSquare_eq]
    exact ⟨z, h, rfl⟩
  have hdistGe : D.radius ≤ dist (z : ℝ × ℝ) (0, 0) := by
    exact le_of_not_gt (by simpa only [Metric.mem_ball] using hnotBall)
  have heq : dist (z : ℝ × ℝ) (0, 0) = D.radius :=
    le_antisymm z.property hdistGe
  rw [frontier_closedBall _ (ne_of_gt D.radius_pos)]
  exact heq

#print axioms compatibleOutsideBands_square_frontier_parameter

def exposedSquareFrontier {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) : Set S :=
  {x | ∃ z : Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius,
    D.square z = x ∧
      (z : ℝ × ℝ) ∈ frontier (Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius) ∧
      x ∉ Set.range B.first ∧ x ∉ Set.range B.second}

theorem compatibleOutsideBands_frontier_eq_exposed_square_union_laterals
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
    frontier N = exposedSquareFrontier D B ∪
      bandLateralSides B.first ∪ bandLateralSides B.second := by
  let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
  have hcompact : IsCompact N := (compatibleOutsideBands_compact_connected_cover_probe D B).1
  have hclosed : IsClosed N := hcompact.isClosed
  have hfirst : bandLateralSides B.first ⊆ frontier N := by
    rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact compatibleOutsideBands_first_lateral_frontier_all D B t _ (Or.inl rfl)
    · exact compatibleOutsideBands_first_lateral_frontier_all D B t _ (Or.inr rfl)
  have hsecond : bandLateralSides B.second ⊆ frontier N := by
    rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact compatibleOutsideBands_second_lateral_frontier_all D B t _ (Or.inl rfl)
    · exact compatibleOutsideBands_second_lateral_frontier_all D B t _ (Or.inr rfl)
  dsimp only
  ext x
  change (x ∈ frontier N) ↔
    ((x ∈ exposedSquareFrontier D B ∨ x ∈ bandLateralSides B.first) ∨
      x ∈ bandLateralSides B.second)
  constructor
  · intro hx
    have hxN : x ∈ N := by
      have hc := frontier_subset_closure hx
      change x ∈ closure N at hc
      simpa only [hclosed.closure_eq] using hc
    rcases hxN with (hsquare | hband) | hband
    · by_cases hb1 : x ∈ Set.range B.first
      · exact Or.inl (Or.inr
          (compatibleOutsideBands_first_frontier_mem_lateral D B hx hb1))
      by_cases hb2 : x ∈ Set.range B.second
      · exact Or.inr
          (compatibleOutsideBands_second_frontier_mem_lateral D B hx hb2)
      obtain ⟨z, rfl⟩ := hsquare
      exact Or.inl (Or.inl ⟨z, rfl,
        compatibleOutsideBands_square_frontier_parameter D B z hx, hb1, hb2⟩)
    · exact Or.inl (Or.inr
        (compatibleOutsideBands_first_frontier_mem_lateral D B hx hband))
    · exact Or.inr
        (compatibleOutsideBands_second_frontier_mem_lateral D B hx hband)
  · rintro ((⟨z, rfl, hz, hb1, hb2⟩ | hb1) | hb2)
    · exact compatibleOutsideBands_exposed_square_frontier D B z hz hb1 hb2
    · exact hfirst hb1
    · exact hsecond hb2

#print axioms compatibleOutsideBands_frontier_eq_exposed_square_union_laterals

noncomputable def crossingSquareSegment (r : ℝ)
    (p q : Metric.closedBall ((0, 0) : ℝ × ℝ) r) : Path p q := by
  let γ : Path (p : ℝ × ℝ) (q : ℝ × ℝ) :=
    Path.segment (p : ℝ × ℝ) (q : ℝ × ℝ)
  have hsub : Set.range γ ⊆ Metric.closedBall ((0, 0) : ℝ × ℝ) r := by
    change Set.range (Path.segment (p : ℝ × ℝ) (q : ℝ × ℝ)) ⊆ _
    rw [Path.range_segment]
    exact (convex_closedBall _ _).segment_subset p.property q.property
  exact {
    toFun := fun t => ⟨γ t, hsub (Set.mem_range_self t)⟩
    continuous_toFun := γ.continuous.subtype_mk _
    source' := by apply Subtype.ext; simp [γ]
    target' := by apply Subtype.ext; simp [γ] }

#print axioms crossingSquareSegment

theorem crossingSquareSegment_embedded {r : ℝ}
    (p q : Metric.closedBall ((0, 0) : ℝ × ℝ) r) (hpq : p ≠ q) :
    IsEmbedding (crossingSquareSegment r p q) := by
  have hpq' : (p : ℝ × ℝ) ≠ (q : ℝ × ℝ) :=
    fun h => hpq (Subtype.ext h)
  have hinj : Function.Injective (crossingSquareSegment r p q) := by
    intro t u he
    apply Path.segment_injective_of_ne hpq'
    exact congrArg Subtype.val he
  exact ((crossingSquareSegment r p q).continuous.isClosedEmbedding hinj).isEmbedding

theorem crossingSquareSegment_second_const {r : ℝ}
    (p q : Metric.closedBall ((0, 0) : ℝ × ℝ) r)
    (h : (p : ℝ × ℝ).2 = (q : ℝ × ℝ).2) (t : I) :
    ((crossingSquareSegment r p q t : Metric.closedBall ((0, 0) : ℝ × ℝ) r) :
      ℝ × ℝ).2 = (p : ℝ × ℝ).2 := by
  change (AffineMap.lineMap (p : ℝ × ℝ) (q : ℝ × ℝ) (t : ℝ)).2 = _
  simp only [AffineMap.lineMap_apply_module, Prod.snd_add]
  change (1 - (t : ℝ)) * (p : ℝ × ℝ).2 + (t : ℝ) * (q : ℝ × ℝ).2 = _
  rw [← h]
  ring

theorem crossingSquareSegment_first_const {r : ℝ}
    (p q : Metric.closedBall ((0, 0) : ℝ × ℝ) r)
    (h : (p : ℝ × ℝ).1 = (q : ℝ × ℝ).1) (t : I) :
    ((crossingSquareSegment r p q t : Metric.closedBall ((0, 0) : ℝ × ℝ) r) :
      ℝ × ℝ).1 = (p : ℝ × ℝ).1 := by
  change (AffineMap.lineMap (p : ℝ × ℝ) (q : ℝ × ℝ) (t : ℝ)).1 = _
  simp only [AffineMap.lineMap_apply_module, Prod.fst_add]
  change (1 - (t : ℝ)) * (p : ℝ × ℝ).1 + (t : ℝ) * (q : ℝ × ℝ).1 = _
  rw [← h]
  ring

theorem crossingSquareSegments_orthogonal_intersection {r : ℝ}
    (p c q : Metric.closedBall ((0, 0) : ℝ × ℝ) r)
    (hpc : (p : ℝ × ℝ).2 = (c : ℝ × ℝ).2)
    (hcq : (c : ℝ × ℝ).1 = (q : ℝ × ℝ).1) :
    Set.range (crossingSquareSegment r p c) ∩
      Set.range (crossingSquareSegment r c q) = {c} := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, u, hu⟩
    have hy := crossingSquareSegment_second_const p c hpc t
    have hx := crossingSquareSegment_first_const c q hcq u
    have hx' : ((crossingSquareSegment r p c t :
        Metric.closedBall ((0, 0) : ℝ × ℝ) r) : ℝ × ℝ).1 = (c : ℝ × ℝ).1 := by
      rw [← hu]
      exact hx
    apply Subtype.ext
    exact Prod.ext hx' (hy.trans hpc)
  · intro hx
    have hc : x = c := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨⟨1, (crossingSquareSegment r p c).target⟩,
      ⟨0, (crossingSquareSegment r c q).source⟩⟩

theorem crossingSquareSegments_orthogonal_intersection_reverse {r : ℝ}
    (p c q : Metric.closedBall ((0, 0) : ℝ × ℝ) r)
    (hpc : (p : ℝ × ℝ).1 = (c : ℝ × ℝ).1)
    (hcq : (c : ℝ × ℝ).2 = (q : ℝ × ℝ).2) :
    Set.range (crossingSquareSegment r p c) ∩
      Set.range (crossingSquareSegment r c q) = {c} := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, u, hu⟩
    have hx := crossingSquareSegment_first_const p c hpc t
    have hy := crossingSquareSegment_second_const c q hcq u
    have hy' : ((crossingSquareSegment r p c t :
        Metric.closedBall ((0, 0) : ℝ × ℝ) r) : ℝ × ℝ).2 = (c : ℝ × ℝ).2 := by
      rw [← hu]
      exact hy
    apply Subtype.ext
    exact Prod.ext (hx.trans hpc) hy'
  · intro hx
    have hc : x = c := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨⟨1, (crossingSquareSegment r p c).target⟩,
      ⟨0, (crossingSquareSegment r c q).source⟩⟩

#print axioms crossingSquareSegment_embedded
#print axioms crossingSquareSegments_orthogonal_intersection

def crossingSquareCorner (r : ℝ) (hr : 0 < r) (i : Fin 4) :
    Metric.closedBall ((0, 0) : ℝ × ℝ) r :=
  ⟨match i with
    | 0 => (r, r)
    | 1 => (r, -r)
    | 2 => (-r, -r)
    | 3 => (-r, r), by
    fin_cases i <;>
      simp [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def,
        Real.norm_eq_abs, abs_of_pos hr, abs_of_neg (neg_neg_of_pos hr)]⟩

#print axioms crossingSquareCorner

noncomputable def squareGap01 {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    Path
      (D.square (squarePort D.radius D.radius_pos 0 ⟨1, by norm_num⟩))
      (D.square (squarePort D.radius D.radius_pos 1 ⟨1, by norm_num⟩)) :=
  ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 0 ⟨1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 0)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 0)
      (squarePort D.radius D.radius_pos 1 ⟨1, by norm_num⟩))).map
    D.square_embedded.continuous

noncomputable def squareGap30 {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    Path
      (D.square (squarePort D.radius D.radius_pos 3 ⟨1, by norm_num⟩))
      (D.square (squarePort D.radius D.radius_pos 0 ⟨-1, by norm_num⟩)) :=
  ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 3 ⟨1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 3)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 3)
      (squarePort D.radius D.radius_pos 0 ⟨-1, by norm_num⟩))).map
    D.square_embedded.continuous

noncomputable def squareGap23 {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    Path
      (D.square (squarePort D.radius D.radius_pos 2 ⟨-1, by norm_num⟩))
      (D.square (squarePort D.radius D.radius_pos 3 ⟨-1, by norm_num⟩)) :=
  ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 2 ⟨-1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 2)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 2)
      (squarePort D.radius D.radius_pos 3 ⟨-1, by norm_num⟩))).map
    D.square_embedded.continuous

noncomputable def squareGap12 {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    Path
      (D.square (squarePort D.radius D.radius_pos 1 ⟨-1, by norm_num⟩))
      (D.square (squarePort D.radius D.radius_pos 2 ⟨1, by norm_num⟩)) :=
  ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 1 ⟨-1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 1)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 1)
      (squarePort D.radius D.radius_pos 2 ⟨1, by norm_num⟩))).map
    D.square_embedded.continuous

noncomputable def bandSidePath {S : Type} [TopologicalSpace S]
    (F : I × BandWidth → S) (hF : IsEmbedding F) (u : BandWidth) :
    Path (F (0, u)) (F (1, u)) :=
  { toFun := fun t => F (t, u)
    continuous_toFun := hF.continuous.comp
      (continuous_id.prodMk continuous_const)
    source' := rfl
    target' := rfl }

noncomputable def boundarySecondPlusReverse {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    Path
      (D.square (squarePort D.radius D.radius_pos 1 ⟨1, by norm_num⟩))
      (D.square (squarePort D.radius D.radius_pos 3 ⟨1, by norm_num⟩)) :=
  ((bandSidePath B.second B.second_embedded ⟨1, by norm_num⟩).symm).cast
    (B.second_right _).symm (B.second_left _).symm

noncomputable def boundaryFirstMinusReverse {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    Path
      (D.square (squarePort D.radius D.radius_pos 0 ⟨-1, by norm_num⟩))
      (D.square (squarePort D.radius D.radius_pos 2 ⟨-1, by norm_num⟩)) :=
  ((bandSidePath B.first B.first_embedded ⟨-1, by norm_num⟩).symm).cast
    (B.first_top _).symm (B.first_bottom _).symm

noncomputable def boundarySecondMinus {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    Path
      (D.square (squarePort D.radius D.radius_pos 3 ⟨-1, by norm_num⟩))
      (D.square (squarePort D.radius D.radius_pos 1 ⟨-1, by norm_num⟩)) :=
  (bandSidePath B.second B.second_embedded ⟨-1, by norm_num⟩).cast
    (B.second_left _).symm (B.second_right _).symm

noncomputable def boundaryFirstPlus {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    Path
      (D.square (squarePort D.radius D.radius_pos 2 ⟨1, by norm_num⟩))
      (D.square (squarePort D.radius D.radius_pos 0 ⟨1, by norm_num⟩)) :=
  (bandSidePath B.first B.first_embedded ⟨1, by norm_num⟩).cast
    (B.first_bottom _).symm (B.first_top _).symm

noncomputable def compatibleBoundaryLoop {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    Path
      (D.square (squarePort D.radius D.radius_pos 0 ⟨1, by norm_num⟩))
      (D.square (squarePort D.radius D.radius_pos 0 ⟨1, by norm_num⟩)) :=
  (((((((squareGap01 D).trans (boundarySecondPlusReverse D B)).trans
    (squareGap30 D)).trans (boundaryFirstMinusReverse D B)).trans
    (squareGap23 D)).trans (boundarySecondMinus D B)).trans
    (squareGap12 D)).trans (boundaryFirstPlus D B)

theorem bandSidePath_embedded {S : Type} [TopologicalSpace S] [T2Space S]
    (F : I × BandWidth → S) (hF : IsEmbedding F) (u : BandWidth) :
    IsEmbedding (bandSidePath F hF u) := by
  apply ((bandSidePath F hF u).continuous.isClosedEmbedding ?_).isEmbedding
  intro t v he
  exact congrArg Prod.fst (hF.injective he)

theorem boundarySecondPlusReverse_embedded {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    IsEmbedding (boundarySecondPlusReverse D B) := by
  change IsEmbedding ((bandSidePath B.second B.second_embedded
    ⟨1, by norm_num⟩) ∘ unitInterval.symm)
  exact (bandSidePath_embedded B.second B.second_embedded
    ⟨1, by norm_num⟩).comp unitInterval.symmHomeomorph.isEmbedding

theorem boundaryFirstMinusReverse_embedded {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    IsEmbedding (boundaryFirstMinusReverse D B) := by
  change IsEmbedding ((bandSidePath B.first B.first_embedded
    ⟨-1, by norm_num⟩) ∘ unitInterval.symm)
  exact (bandSidePath_embedded B.first B.first_embedded
    ⟨-1, by norm_num⟩).comp unitInterval.symmHomeomorph.isEmbedding

theorem boundarySecondMinus_embedded {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    IsEmbedding (boundarySecondMinus D B) := by
  simpa only [boundarySecondMinus, Path.cast_coe] using
    bandSidePath_embedded B.second B.second_embedded ⟨-1, by norm_num⟩

theorem boundaryFirstPlus_embedded {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    IsEmbedding (boundaryFirstPlus D B) := by
  simpa only [boundaryFirstPlus, Path.cast_coe] using
    bandSidePath_embedded B.first B.first_embedded ⟨1, by norm_num⟩

#print axioms boundarySecondPlusReverse_embedded
#print axioms boundaryFirstMinusReverse_embedded
#print axioms boundarySecondMinus_embedded
#print axioms boundaryFirstPlus_embedded

theorem bandSidePath_range {S : Type} [TopologicalSpace S]
    (F : I × BandWidth → S) (hF : IsEmbedding F) (u : BandWidth) :
    Set.range (bandSidePath F hF u) = Set.range (fun t : I => F (t, u)) := rfl

theorem boundarySecondPlusReverse_range {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    Set.range (boundarySecondPlusReverse D B) =
      Set.range (fun t : I => B.second (t, ⟨1, by norm_num⟩)) := by
  simp only [boundarySecondPlusReverse, Path.cast_coe, Path.symm_range,
    bandSidePath_range]

theorem boundaryFirstMinusReverse_range {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    Set.range (boundaryFirstMinusReverse D B) =
      Set.range (fun t : I => B.first (t, ⟨-1, by norm_num⟩)) := by
  simp only [boundaryFirstMinusReverse, Path.cast_coe, Path.symm_range,
    bandSidePath_range]

theorem boundarySecondMinus_range {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    Set.range (boundarySecondMinus D B) =
      Set.range (fun t : I => B.second (t, ⟨-1, by norm_num⟩)) := by
  simp only [boundarySecondMinus, Path.cast_coe, bandSidePath_range]

theorem boundaryFirstPlus_range {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    Set.range (boundaryFirstPlus D B) =
      Set.range (fun t : I => B.first (t, ⟨1, by norm_num⟩)) := by
  simp only [boundaryFirstPlus, Path.cast_coe, bandSidePath_range]

theorem compatibleBoundaryLoop_range {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    Set.range (compatibleBoundaryLoop D B) =
      Set.range (squareGap01 D) ∪ Set.range (squareGap30 D) ∪
      Set.range (squareGap23 D) ∪ Set.range (squareGap12 D) ∪
      bandLateralSides B.first ∪ bandLateralSides B.second := by
  simp only [compatibleBoundaryLoop, Path.trans_range,
    boundarySecondPlusReverse_range, boundaryFirstMinusReverse_range,
    boundarySecondMinus_range, boundaryFirstPlus_range, bandLateralSides]
  ext x
  simp only [Set.mem_union]
  tauto

theorem squareGap01_embedded {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    IsEmbedding (squareGap01 D) := by
  let p := squarePort D.radius D.radius_pos 0 ⟨1, by norm_num⟩
  let c := crossingSquareCorner D.radius D.radius_pos 0
  let q := squarePort D.radius D.radius_pos 1 ⟨1, by norm_num⟩
  have hpc : p ≠ c := by
    intro he
    have h := congrArg (fun z : Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius =>
      (z : ℝ × ℝ).1) he
    dsimp [p, c, squarePort, crossingEndRectangle, crossingSquareCorner] at h
    linarith [D.radius_pos]
  have hcq : c ≠ q := by
    intro he
    have h := congrArg (fun z : Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius =>
      (z : ℝ × ℝ).2) he
    dsimp [p, q, c, squarePort, crossingEndRectangle, crossingSquareCorner] at h
    linarith [D.radius_pos]
  have hy : (p : ℝ × ℝ).2 = (c : ℝ × ℝ).2 := by
    simp [p, c, squarePort, crossingEndRectangle, crossingSquareCorner]
  have hx : (c : ℝ × ℝ).1 = (q : ℝ × ℝ).1 := by
    simp [q, c, squarePort, crossingEndRectangle, crossingSquareCorner]
  have hinner : IsEmbedding
      ((crossingSquareSegment D.radius p c).trans
        (crossingSquareSegment D.radius c q)) :=
    isEmbedding_path_trans_of_inter_singleton_probe _ _
      (crossingSquareSegment_embedded p c hpc)
      (crossingSquareSegment_embedded c q hcq)
      (crossingSquareSegments_orthogonal_intersection p c q hy hx)
  exact D.square_embedded.comp hinner

theorem squareGap23_embedded {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    IsEmbedding (squareGap23 D) := by
  let p := squarePort D.radius D.radius_pos 2 ⟨-1, by norm_num⟩
  let c := crossingSquareCorner D.radius D.radius_pos 2
  let q := squarePort D.radius D.radius_pos 3 ⟨-1, by norm_num⟩
  have hpc : p ≠ c := by
    intro he
    have h := congrArg (fun z : Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius =>
      (z : ℝ × ℝ).1) he
    dsimp [p, c, squarePort, crossingEndRectangle, crossingSquareCorner] at h
    linarith [D.radius_pos]
  have hcq : c ≠ q := by
    intro he
    have h := congrArg (fun z : Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius =>
      (z : ℝ × ℝ).2) he
    dsimp [p, q, c, squarePort, crossingEndRectangle, crossingSquareCorner] at h
    linarith [D.radius_pos]
  have hy : (p : ℝ × ℝ).2 = (c : ℝ × ℝ).2 := by
    simp [p, c, squarePort, crossingEndRectangle, crossingSquareCorner]
  have hx : (c : ℝ × ℝ).1 = (q : ℝ × ℝ).1 := by
    simp [q, c, squarePort, crossingEndRectangle, crossingSquareCorner]
  have hinner : IsEmbedding
      ((crossingSquareSegment D.radius p c).trans
        (crossingSquareSegment D.radius c q)) :=
    isEmbedding_path_trans_of_inter_singleton_probe _ _
      (crossingSquareSegment_embedded p c hpc)
      (crossingSquareSegment_embedded c q hcq)
      (crossingSquareSegments_orthogonal_intersection p c q hy hx)
  exact D.square_embedded.comp hinner

theorem squareGap30_embedded {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    IsEmbedding (squareGap30 D) := by
  let p := squarePort D.radius D.radius_pos 3 ⟨1, by norm_num⟩
  let c := crossingSquareCorner D.radius D.radius_pos 3
  let q := squarePort D.radius D.radius_pos 0 ⟨-1, by norm_num⟩
  have hpc : p ≠ c := by
    intro he
    have h := congrArg (fun z : Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius =>
      (z : ℝ × ℝ).2) he
    dsimp [p, c, squarePort, crossingEndRectangle, crossingSquareCorner] at h
    linarith [D.radius_pos]
  have hcq : c ≠ q := by
    intro he
    have h := congrArg (fun z : Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius =>
      (z : ℝ × ℝ).1) he
    dsimp [p, q, c, squarePort, crossingEndRectangle, crossingSquareCorner] at h
    linarith [D.radius_pos]
  have hx : (p : ℝ × ℝ).1 = (c : ℝ × ℝ).1 := by
    simp [p, c, squarePort, crossingEndRectangle, crossingSquareCorner]
  have hy : (c : ℝ × ℝ).2 = (q : ℝ × ℝ).2 := by
    simp [q, c, squarePort, crossingEndRectangle, crossingSquareCorner]
  have hinner : IsEmbedding
      ((crossingSquareSegment D.radius p c).trans
        (crossingSquareSegment D.radius c q)) :=
    isEmbedding_path_trans_of_inter_singleton_probe _ _
      (crossingSquareSegment_embedded p c hpc)
      (crossingSquareSegment_embedded c q hcq)
      (crossingSquareSegments_orthogonal_intersection_reverse p c q hx hy)
  exact D.square_embedded.comp hinner

theorem squareGap12_embedded {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    IsEmbedding (squareGap12 D) := by
  let p := squarePort D.radius D.radius_pos 1 ⟨-1, by norm_num⟩
  let c := crossingSquareCorner D.radius D.radius_pos 1
  let q := squarePort D.radius D.radius_pos 2 ⟨1, by norm_num⟩
  have hpc : p ≠ c := by
    intro he
    have h := congrArg (fun z : Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius =>
      (z : ℝ × ℝ).2) he
    dsimp [p, c, squarePort, crossingEndRectangle, crossingSquareCorner] at h
    linarith [D.radius_pos]
  have hcq : c ≠ q := by
    intro he
    have h := congrArg (fun z : Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius =>
      (z : ℝ × ℝ).1) he
    dsimp [p, q, c, squarePort, crossingEndRectangle, crossingSquareCorner] at h
    linarith [D.radius_pos]
  have hx : (p : ℝ × ℝ).1 = (c : ℝ × ℝ).1 := by
    simp [p, c, squarePort, crossingEndRectangle, crossingSquareCorner]
  have hy : (c : ℝ × ℝ).2 = (q : ℝ × ℝ).2 := by
    simp [q, c, squarePort, crossingEndRectangle, crossingSquareCorner]
  have hinner : IsEmbedding
      ((crossingSquareSegment D.radius p c).trans
        (crossingSquareSegment D.radius c q)) :=
    isEmbedding_path_trans_of_inter_singleton_probe _ _
      (crossingSquareSegment_embedded p c hpc)
      (crossingSquareSegment_embedded c q hcq)
      (crossingSquareSegments_orthogonal_intersection_reverse p c q hx hy)
  exact D.square_embedded.comp hinner

#print axioms squareGap23_embedded
#print axioms squareGap30_embedded
#print axioms squareGap12_embedded

#print axioms squareGap01_embedded

theorem band_lateral_sides_disjoint {S : Type} [TopologicalSpace S]
    (F : I × BandWidth → S) (hF : IsEmbedding F) :
    Disjoint
      (Set.range (fun t : I => F (t, ⟨-1, by norm_num⟩)))
      (Set.range (fun t : I => F (t, ⟨1, by norm_num⟩))) := by
  rw [Set.disjoint_left]
  rintro x ⟨t, rfl⟩ ⟨u, he⟩
  have hh := hF.injective he.symm
  have hu := congrArg Prod.snd hh
  have hv := congrArg Subtype.val hu
  norm_num at hv

theorem compatibleOutsideBands_laterals_disjoint
    {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    Disjoint (bandLateralSides B.first) (bandLateralSides B.second) := by
  apply Set.disjoint_of_subset
    (show bandLateralSides B.first ⊆ Set.range B.first from by
      rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩) <;> exact Set.mem_range_self _)
    (show bandLateralSides B.second ⊆ Set.range B.second from by
      rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩) <;> exact Set.mem_range_self _)
    B.bands_disjoint

#print axioms band_lateral_sides_disjoint
#print axioms compatibleOutsideBands_laterals_disjoint

#print axioms bandSidePath_embedded
#print axioms boundarySecondPlusReverse_range
#print axioms compatibleBoundaryLoop_range

end CurveComplex
