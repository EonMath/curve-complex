import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.BoundaryAmbientTransport

namespace CoherentEndpointMotion
open CurveComplex Set Topology Schoenflies

theorem embedded_strip_open_subband
    {X : Type*} [TopologicalSpace X]
    (E : C(Interval × Interval,X)) (hE : IsEmbedding E)
    (hopen : IsOpen (E '' {z | z.2 ∈ Ioo (0 : Interval) 1}))
    (p q : Interval) (hp : 0 < p) (hq : q < 1) :
    IsOpen (E '' {z | z.2 ∈ Ioo p q}) := by
  have hW : IsOpen {z : Interval × Interval | z.2 ∈ Ioo p q} :=
    isOpen_Ioo.preimage continuous_snd
  obtain ⟨O,hO,himage⟩ := hE.isInducing.image_eq_isOpen_inter_range hW
  have heq : E '' {z | z.2 ∈ Ioo p q} =
      O ∩ E '' {z | z.2 ∈ Ioo (0 : Interval) 1} := by
    apply Set.Subset.antisymm
    · rintro x hx
      have hxO := (himage ▸ hx).1
      obtain ⟨z,hz,rfl⟩ := hx
      exact ⟨hxO,⟨z,⟨hp.trans hz.1,hz.2.trans hq⟩,rfl⟩⟩
    · rintro x ⟨hx,z,hz,rfl⟩
      rw [himage]
      exact ⟨hx,Set.mem_range_self z⟩
  rw [heq]
  exact hO.inter hopen

/-- An essential arc in a distinct original ambient class cannot enter the
closed band between two interior rails that it avoids. Unlike a whole-strip
clearance premise, this only uses disjointness from the two prescribed arcs. -/
theorem essential_distinct_arc_clears_between_interior_rails
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B : Set X) (E : C(Interval × Interval,X)) (hE : IsEmbedding E)
    (hopen : IsOpen (E '' {z | z.2 ∈ Ioo (0 : Interval) 1}))
    (hB : ∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (p q : Interval) (hp : p ∈ Ioo (0 : Interval) 1)
    (hq : q ∈ Ioo (0 : Interval) 1) (hpq : p < q)
    (a : C(Interval,X)) (ha : IsEmbedding a)
    (haends : a 0 ∈ B ∧ a 1 ∈ B)
    (haInterior : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (hessential : ¬ ∃ c : C(Interval,X), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : Plane) 1,X), IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range a ∪ range c)
    (hdistinct : ¬ ∃ H : AmbientIsotopy X,
      (∀ t, (fun x => H.map (t,x)) '' B = B) ∧
      H.finalMap '' range (fun s : Interval => E (s,p)) = range a)
    (hsidep : Disjoint (range a) (range (fun s : Interval => E (s,p))))
    (hsideq : Disjoint (range a) (range (fun s : Interval => E (s,q)))) :
    Disjoint (range a) (E '' {z | z.2 ∈ Icc p q}) := by
  let U : Set X := E '' {z | z.2 ∈ Ioo p q}
  let C : Set X := E '' {z | z.2 ∈ Icc p q}
  have hU : IsOpen U := embedded_strip_open_subband E hE hopen p q hp.1 hq.2
  have hC : IsClosed C := by
    have hc : IsClosed {z : Interval × Interval | z.2 ∈ Icc p q} :=
      isClosed_Icc.preimage continuous_snd
    exact (hc.isCompact.image E.continuous).isClosed
  have hUC : U ⊆ C := Set.image_mono (fun _ hz => Ioo_subset_Icc_self hz)
  have hcover : range a ⊆ U ∪ Cᶜ := by
    intro x hx
    by_cases hxC : x ∈ C
    · obtain ⟨z,hz,rfl⟩ := hxC
      left
      refine ⟨z,⟨?_,?_⟩,rfl⟩
      · apply lt_of_le_of_ne hz.1
        intro he
        exact Set.disjoint_left.mp hsidep hx
          ⟨z.1,congrArg E (Prod.ext rfl he)⟩
      · apply lt_of_le_of_ne hz.2
        intro he
        exact Set.disjoint_left.mp hsideq hx
          ⟨z.1,congrArg E (Prod.ext rfl he.symm)⟩
    · exact Or.inr hxC
  have hor : range a ⊆ U ∨ range a ⊆ Cᶜ :=
    (isPreconnected_range a.continuous).subset_or_subset hU hC.isOpen_compl
      (disjoint_compl_right.mono_left hUC) hcover
  have hout : range a ⊆ Cᶜ := hor.resolve_left (fun hin => hdistinct
    (essential_arc_inside_strip_is_in_rail_class B E hE hopen hB a ha haends
      haInterior hessential (by
        rintro x hx
        obtain ⟨z,hz,rfl⟩ := hin hx
        exact ⟨z,⟨hp.1.trans hz.1,hz.2.trans hq.2⟩,rfl⟩) p hp))
  exact Set.disjoint_left.mpr (fun x hx hc => hout hx hc)

/-- Compactness expands a cleared closed rail band slightly inside a given
open set. This is the margin needed for a supported endpoint-moving movie. -/
theorem compact_strip_band_has_wider_band_in_open
    {X : Type*} [TopologicalSpace X]
    (E : C(Interval × Interval,X)) (U : Set X) (hU : IsOpen U)
    (p q : Interval) (hp : 0 < p) (hq : q < 1) (hpq : p ≤ q)
    (hband : E '' {z | z.2 ∈ Icc p q} ⊆ U) :
    ∃ l r : Interval, 0 < l ∧ l < p ∧ q < r ∧ r < 1 ∧
      E '' {z | z.2 ∈ Icc l r} ⊆ U := by
  have hpre : IsOpen (E ⁻¹' U) := hU.preimage E.continuous
  have hp' : (0 : ℝ) < p := hp
  have hq' : (q : ℝ) < 1 := hq
  have hbase : (univ : Set Interval) ×ˢ Icc p q ⊆ E ⁻¹' U := by
    rintro ⟨s,w⟩ ⟨_,hw⟩
    exact hband ⟨(s,w),hw,rfl⟩
  obtain ⟨A,W,hA,hW,hUA,hpqW,hAW⟩ := generalized_tube_lemma
    isCompact_univ isCompact_Icc hpre hbase
  let clip : ℝ → Interval := Set.projIcc 0 1 zero_le_one
  have hclip (w : Interval) : clip (w : ℝ) = w := by
    apply Subtype.ext
    simp only [clip,Set.projIcc_of_mem _ w.property]
  have hpc : (p : ℝ) ∈ clip ⁻¹' W := by
    change clip (p:ℝ) ∈ W
    rw [hclip]
    exact hpqW ⟨le_rfl,hpq⟩
  have hqc : (q : ℝ) ∈ clip ⁻¹' W := by
    change clip (q:ℝ) ∈ W
    rw [hclip]
    exact hpqW ⟨hpq,le_rfl⟩
  obtain ⟨δp,hδp,hδpW⟩ := Metric.mem_nhds_iff.mp
    ((hW.preimage continuous_projIcc).mem_nhds hpc)
  obtain ⟨δq,hδq,hδqW⟩ := Metric.mem_nhds_iff.mp
    ((hW.preimage continuous_projIcc).mem_nhds hqc)
  let εp : ℝ := min δp (p : ℝ) / 2
  let εq : ℝ := min δq (1-(q : ℝ)) / 2
  have hεp : 0 < εp := by dsimp [εp]; positivity
  have hεq : 0 < εq := by dsimp [εq]; positivity
  have hεpp : εp < (p : ℝ) := by
    have h := min_le_right δp (p : ℝ)
    dsimp [εp]; linarith
  have hεpδ : εp < δp := by
    have h := min_le_left δp (p : ℝ)
    dsimp [εp]; linarith
  have hεqq : εq < 1-(q : ℝ) := by
    have h := min_le_right δq (1-(q : ℝ))
    dsimp [εq]; linarith
  have hεqδ : εq < δq := by
    have h := min_le_left δq (1-(q : ℝ))
    dsimp [εq]; linarith
  let l : Interval := ⟨(p : ℝ)-εp,⟨by linarith,by linarith [p.property.2]⟩⟩
  let r : Interval := ⟨(q : ℝ)+εq,⟨by linarith [q.property.1],by linarith⟩⟩
  refine ⟨l,r,by change 0 < (p:ℝ)-εp; linarith,
    by change (p:ℝ)-εp < p; linarith,
    by change (q:ℝ) < (q:ℝ)+εq; linarith,
    by change (q:ℝ)+εq < 1; linarith,?_⟩
  rintro x ⟨z,hz,rfl⟩
  apply hAW ⟨hUA trivial,?_⟩
  by_cases hzp : z.2 < p
  · have hmem : (z.2 : ℝ) ∈ Metric.ball (p : ℝ) δp := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      have hz' : (p:ℝ)-εp ≤ (z.2:ℝ) := hz.1
      have hzp' : (z.2:ℝ) < p := hzp
      constructor <;> linarith
    have hh : clip (z.2:ℝ) ∈ W := hδpW hmem
    rwa [hclip] at hh
  · by_cases hzq : q < z.2
    · have hmem : (z.2 : ℝ) ∈ Metric.ball (q : ℝ) δq := by
        rw [Metric.mem_ball,Real.dist_eq,abs_lt]
        have hz' : (z.2:ℝ) ≤ (q:ℝ)+εq := hz.2
        have hzq' : (q:ℝ) < z.2 := hzq
        constructor <;> linarith
      have hh : clip (z.2:ℝ) ∈ W := hδqW hmem
      rwa [hclip] at hh
    · exact hpqW ⟨le_of_not_gt hzp,le_of_not_gt hzq⟩

/-- An interval point motion supported in a strictly smaller open interval.
The two prescribed points may move freely inside that interval. -/
theorem interval_point_motion_supported_between
    (l r p q : Interval) (hl : 0 < l) (hr : r < 1)
    (hp : p ∈ Ioo l r) (hq : q ∈ Ioo l r) :
    ∃ L : AmbientIsotopy Interval, L.finalMap p = q ∧
      ∀ t w, w ∉ Ioo l r → L.map (t,w) = w := by
  have hlr : (l : ℝ) < r := hp.1.trans hp.2
  have hdiff : 0 < (r : ℝ)-(l : ℝ) := sub_pos.mpr hlr
  let f : C(Interval,Interval) := ⟨fun s =>
    ⟨(l : ℝ)+((r : ℝ)-(l : ℝ))*(s : ℝ),by
      constructor
      · nlinarith [l.property.1,s.property.1]
      · nlinarith [r.property.2,s.property.2]⟩,by fun_prop⟩
  have hf : IsEmbedding f := (f.continuous.isClosedEmbedding (by
    intro s t he
    apply Subtype.ext
    have he := congrArg Subtype.val he
    change (l:ℝ)+((r:ℝ)-(l:ℝ))*(s:ℝ) =
      (l:ℝ)+((r:ℝ)-(l:ℝ))*(t:ℝ) at he
    nlinarith)).isEmbedding
  have coord (w : Interval) (hw : w ∈ Ioo l r) :
      ∃ v : Interval, v ∈ Ioo (0 : Interval) 1 ∧ f v = w := by
    have hw0 : (0 : ℝ) < ((w:ℝ)-(l:ℝ))/((r:ℝ)-(l:ℝ)) :=
      div_pos (sub_pos.mpr hw.1) hdiff
    have hw1 : ((w:ℝ)-(l:ℝ))/((r:ℝ)-(l:ℝ)) < 1 := by
      apply (div_lt_one hdiff).mpr
      have hw' : (w:ℝ) < r := hw.2
      linarith
    refine ⟨⟨((w:ℝ)-(l:ℝ))/((r:ℝ)-(l:ℝ)),⟨hw0.le,hw1.le⟩⟩,
      ⟨hw0,hw1⟩,Subtype.ext ?_⟩
    change (l:ℝ)+((r:ℝ)-(l:ℝ))*
      (((w:ℝ)-(l:ℝ))/((r:ℝ)-(l:ℝ))) = (w:ℝ)
    rw [mul_div_cancel₀ _ hdiff.ne']
    ring
  have himage : f '' Ioo (0 : Interval) 1 = Ioo l r := by
    apply Set.Subset.antisymm
    · rintro _ ⟨v,hv,rfl⟩
      have hv0 : (0:ℝ) < v := hv.1
      have hv1 : (v:ℝ) < 1 := hv.2
      change (l:ℝ) < (l:ℝ)+((r:ℝ)-(l:ℝ))*(v:ℝ) ∧
        (l:ℝ)+((r:ℝ)-(l:ℝ))*(v:ℝ) < r
      constructor <;> nlinarith
    · intro w hw
      obtain ⟨v,hv,he⟩ := coord w hw
      exact ⟨v,hv,he⟩
  obtain ⟨p',hp',hfp⟩ := coord p hp
  obtain ⟨q',hq',hfq⟩ := coord q hq
  obtain ⟨K,hKend,hKpq,_⟩ := interval_point_isotopy p' q' hp' hq'
  have hKfix (t w) (hw : w ∉ Ioo (0 : Interval) 1) : K.map (t,w) = w := by
    by_cases h0 : w = 0
    · simpa only [h0] using (hKend t).1
    · have h1 : w = 1 := le_antisymm le_top (le_of_not_gt
        (fun h => hw ⟨bot_lt_iff_ne_bot.mpr h0,h⟩))
      simpa only [h1] using (hKend t).2
  obtain ⟨L,hLf,hLfix⟩ := embedded_cell_isotopy_extend f hf (Ioo (0 : Interval) 1)
    (himage.symm ▸ isOpen_Ioo) K hKfix
  refine ⟨L,?_,?_⟩
  · rw [← hfp]
    change L.map (1,f p') = q
    rw [hLf]
    change f (K.finalMap p') = q
    rw [hKpq,hfq]
  · simpa only [himage] using hLfix

/-- Move the two interior rails through a supplied cleared closed band.
Compactness supplies the support margin; the original graph is fixed at
every time, including its boundary endpoints. -/
theorem embedded_strip_rail_motion_avoiding_closed_graph
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B P : Set X) (hP : IsClosed P)
    (E : C(Interval × Interval,X)) (hE : IsEmbedding E)
    (hopen : IsOpen (E '' {z | z.2 ∈ Ioo (0 : Interval) 1}))
    (hB : ∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (p q : Interval) (hp : p ∈ Ioo (0 : Interval) 1)
    (hq : q ∈ Ioo (0 : Interval) 1) (hpq : p ≤ q)
    (hclear : Disjoint P (E '' {z | z.2 ∈ Icc p q})) :
    ∃ H : AmbientIsotopy X,
      (∀ t, (fun x => H.map (t,x)) '' B = B) ∧
      (∀ s, H.finalMap (E (s,p)) = E (s,q)) ∧
      ∀ t x, x ∈ P → H.map (t,x) = x := by
  obtain ⟨l,r,hl,hlp,hqr,hr,hband⟩ := compact_strip_band_has_wider_band_in_open
    E Pᶜ hP.isOpen_compl p q hp.1 hq.2 hpq
    (fun x hx hpx => Set.disjoint_left.mp hclear hpx hx)
  obtain ⟨L,hLpq,hLfix⟩ := interval_point_motion_supported_between l r p q hl hr
    ⟨hlp,hpq.trans_lt hqr⟩ ⟨hlp.trans_le hpq,hqr⟩
  let K : AmbientIsotopy (Interval × Interval) := {
    map := ⟨fun z => (z.2.1,L.map (z.1,z.2.2)),
      continuous_snd.fst.prodMk (L.map.continuous.comp
        (continuous_fst.prodMk continuous_snd.snd))⟩
    homeomorphism_at := by
      intro t
      obtain ⟨k,hk⟩ := L.homeomorphism_at t
      exact ⟨(Homeomorph.refl Interval).prodCongr k,fun _ => Prod.ext rfl (hk _)⟩
    at_zero := by intro z; exact Prod.ext rfl (L.at_zero _) }
  have hKfix (t : Interval) (z : Interval × Interval)
      (hz : z ∉ {z | z.2 ∈ Ioo (0 : Interval) 1}) : K.map (t,z) = z := by
    refine Prod.ext rfl (hLfix t z.2 ?_)
    exact fun h => hz ⟨hl.trans h.1,h.2.trans hr⟩
  obtain ⟨H,hHE,hHfix⟩ := embedded_cell_isotopy_extend E hE
    {z | z.2 ∈ Ioo (0 : Interval) 1} hopen K hKfix
  refine ⟨H,?_,?_,?_⟩
  · intro t
    have hmem (x : X) : H.map (t,x) ∈ B ↔ x ∈ B := by
      by_cases hx : x ∈ range E
      · obtain ⟨z,rfl⟩ := hx
        rw [hHE,hB,hB]
        rfl
      · rw [hHfix t x (fun hu => hx (Set.image_subset_range E _ hu))]
    apply Set.Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact (hmem x).mpr hx
    · intro y hy
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      refine ⟨e.symm y,?_,?_⟩
      · apply (hmem _).mp
        rw [← he,e.apply_symm_apply]
        exact hy
      · change H.map (t,e.symm y) = y
        rw [← he,e.apply_symm_apply]
  · intro s
    change H.map (1,E (s,p)) = E (s,q)
    rw [hHE]
    change E (s,L.finalMap p) = E (s,q)
    rw [hLpq]
  · intro t x hx
    by_cases hxE : x ∈ range E
    · obtain ⟨z,rfl⟩ := hxE
      rw [hHE]
      apply congrArg E
      refine Prod.ext rfl (hLfix t z.2 ?_)
      intro hz
      exact hband ⟨z,⟨hz.1.le,hz.2.le⟩,rfl⟩ hx
    · exact hHfix t x (fun hu => hxE (Set.image_subset_range E _ hu))

/-- Terminal simultaneous-family consumer: the graph is cleared from the
band using essentiality and original class-distinctness, then the supported
rail movie fixes the entire finite graph. No graph-clearance certificate is
an input. The actual terminal strip is still geometric data to be produced. -/
theorem terminal_parallel_rails_preserve_distinct_essential_family
    {X : Type} [TopologicalSpace X] [T2Space X]
    {J : Type} [Fintype J]
    (B : Set X) (E : C(Interval × Interval,X)) (hE : IsEmbedding E)
    (hopen : IsOpen (E '' {z | z.2 ∈ Ioo (0 : Interval) 1}))
    (hB : ∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (p q : Interval) (hp : p ∈ Ioo (0 : Interval) 1)
    (hq : q ∈ Ioo (0 : Interval) 1) (hpq : p < q)
    (c : J → C(Interval,X)) (hc : ∀ j, IsEmbedding (c j))
    (hcends : ∀ j, c j 0 ∈ B ∧ c j 1 ∈ B)
    (hcInterior : ∀ j t, t ∈ Ioo (0 : Interval) 1 → c j t ∉ B)
    (hessential : ∀ j, ¬ ∃ w : C(Interval,X), IsEmbedding w ∧ (∀ t, w t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : Plane) 1,X), IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range (c j) ∪ range w)
    (hdistinct : ∀ j, ¬ ∃ H : AmbientIsotopy X,
      (∀ t, (fun x => H.map (t,x)) '' B = B) ∧
      H.finalMap '' range (fun s : Interval => E (s,p)) = range (c j))
    (hsidep : ∀ j, Disjoint (range (c j)) (range (fun s : Interval => E (s,p))))
    (hsideq : ∀ j, Disjoint (range (c j)) (range (fun s : Interval => E (s,q)))) :
    ∃ H : AmbientIsotopy X,
      (∀ t, (fun x => H.map (t,x)) '' B = B) ∧
      (∀ s, H.finalMap (E (s,p)) = E (s,q)) ∧
      ∀ t j s, H.map (t,c j s) = c j s := by
  let P : Set X := ⋃ j, range (c j)
  have hP : IsClosed P := isClosed_iUnion_of_finite
    (fun j => (isCompact_range (c j).continuous).isClosed)
  have hclear : Disjoint P (E '' {z | z.2 ∈ Icc p q}) := by
    apply Set.disjoint_left.mpr
    intro x hx hxband
    obtain ⟨j,hxj⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp
      (essential_distinct_arc_clears_between_interior_rails B E hE hopen hB
        p q hp hq hpq (c j) (hc j) (hcends j) (hcInterior j) (hessential j)
        (hdistinct j) (hsidep j) (hsideq j)) hxj hxband
  obtain ⟨H,hHB,hHpq,hHfix⟩ := embedded_strip_rail_motion_avoiding_closed_graph
    B P hP E hE hopen hB p q hp hq hpq.le hclear
  exact ⟨H,hHB,hHpq,fun t j s => hHfix t (c j s)
    (Set.mem_iUnion.mpr ⟨j,Set.mem_range_self s⟩)⟩

end CoherentEndpointMotion
