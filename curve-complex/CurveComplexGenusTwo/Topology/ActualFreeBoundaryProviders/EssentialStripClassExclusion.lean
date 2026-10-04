import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeStripCrosscutMotion
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.EssentialArcDiskExclusion
import ClassificationOfSurfaces.Moise.Brouwer

open Set Topology CurveComplex Schoenflies

namespace CoherentEndpointMotion

/-- The compact rectangle carrier is the range of a literal embedded unit disk. -/
theorem embedded_rectangle_unit_disk_carrier
    {X : Type*} [TopologicalSpace X]
    (E : C(Interval × Interval, X)) (hE : IsEmbedding E) :
    ∃ d : C(Metric.closedBall (0 : Plane) 1,X),
      IsEmbedding d ∧ Set.range d = Set.range E := by
  obtain ⟨r,hr⟩ := rectanglePoint_homeomorph
  obtain ⟨h,hi,hcl,hfront⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (Plane.convex_closedSquare 0 1)
    (by rw [Plane.interior_closedSquare]; exact ⟨0,by simp [Plane.openSquare,Plane.supNorm]⟩)
    (Plane.isBounded_closedSquare 0 1)
  have hcl' : h '' Plane.closedSquare 0 1 = Metric.closedBall (0 : Plane) 1 := by
    simpa only [(Plane.isClosed_closedSquare 0 1).closure_eq] using hcl
  let q : Plane.closedSquare 0 1 ≃ₜ Metric.closedBall (0 : Plane) 1 :=
    (h.image (Plane.closedSquare 0 1)).trans (Homeomorph.setCongr hcl')
  let k := q.symm.trans r.symm
  let d : C(Metric.closedBall (0 : Plane) 1,X) :=
    ⟨fun z => E (k z),E.continuous.comp k.continuous⟩
  refine ⟨d,hE.comp k.isEmbedding,?_⟩
  change Set.range (E ∘ k) = Set.range E
  exact k.surjective.range_comp E

/-- In a boundary-attached rectangle, an essential proper arc cannot have both
endpoints on the same end edge. The contradiction is an actual disk in X. -/
theorem essential_rectangle_arc_cannot_have_same_end
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B : Set X) (E : C(Interval × Interval,X)) (hE : IsEmbedding E)
    (hB : ∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (a : C(Interval,X)) (ha : IsEmbedding a)
    (haInterior : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (hessential : ¬ ∃ b : C(Interval,X), IsEmbedding b ∧ (∀ t, b t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : Plane) 1,X), IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = Set.range a ∪ Set.range b)
    (haE : Set.range a ⊆ Set.range E)
    (u : Interval) (hu : u = 0 ∨ u = 1)
    (h0 : a 0 ∈ Set.range (fun w : Interval => E (u,w)))
    (h1 : a 1 ∈ Set.range (fun w : Interval => E (u,w))) : False := by
  obtain ⟨d,hd,hdE⟩ := embedded_rectangle_unit_disk_carrier E hE
  let w : C(Interval,X) := ⟨fun v => E (u,v),
    E.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hw : IsEmbedding w := (w.continuous.isClosedEmbedding (by
    intro s t he
    exact congrArg Prod.snd (hE.injective he))).isEmbedding
  have hwB (v : Interval) : w v ∈ B := (hB (u,v)).mpr hu
  have hwD : Set.range w ⊆ Set.range d := by
    rw [hdE]
    rintro z ⟨v,rfl⟩
    exact Set.mem_range_self (u,v)
  exact hessential (proper_arc_in_boundary_attached_disk_is_boundary_parallel
    B a ha haInterior d hd (hdE ▸ haE) w hw hwB hwD h0 h1)

/-- An essential proper arc wholly inside a boundary-attached strip belongs
to the original boundary-preserving ambient class of every interior rail. -/
theorem essential_arc_inside_strip_is_in_rail_class
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B : Set X) (E : C(Interval × Interval,X)) (hE : IsEmbedding E)
    (hopen : IsOpen (E '' {z | z.2 ∈ Ioo (0 : Interval) 1}))
    (hB : ∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (a : C(Interval,X)) (ha : IsEmbedding a)
    (haends : a 0 ∈ B ∧ a 1 ∈ B)
    (haInterior : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (hessential : ¬ ∃ b : C(Interval,X), IsEmbedding b ∧ (∀ t, b t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : Plane) 1,X), IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = Set.range a ∪ Set.range b)
    (haU : Set.range a ⊆ E '' {z | z.2 ∈ Ioo (0 : Interval) 1})
    (p : Interval) (hp : p ∈ Ioo (0 : Interval) 1) :
    ∃ H : AmbientIsotopy X,
      (∀ t, (fun x => H.map (t,x)) '' B = B) ∧
      H.finalMap '' Set.range (fun s : Interval => E (s,p)) = Set.range a := by
  have haE : Set.range a ⊆ Set.range E := haU.trans (Set.image_subset_range E _)
  let e := hE.toHomeomorph
  let c : C(Interval,Interval × Interval) :=
    ⟨fun t => e.symm ⟨a t,haE (Set.mem_range_self t)⟩,
      e.symm.continuous.comp (a.continuous.subtype_mk _)⟩
  have hEc (t : Interval) : E (c t) = a t :=
    congrArg Subtype.val (e.apply_symm_apply ⟨a t,haE (Set.mem_range_self t)⟩)
  have hc : IsEmbedding c := (c.continuous.isClosedEmbedding (by
    intro s t he
    apply ha.injective
    exact (hEc s).symm.trans ((congrArg E he).trans (hEc t)))).isEmbedding
  have hcwidth (t : Interval) : (c t).2 ∈ Ioo (0 : Interval) 1 := by
    obtain ⟨z,hz,he⟩ := haU (Set.mem_range_self t)
    have hec : c t = z := hE.injective ((hEc t).trans he.symm)
    exact hec ▸ hz
  have hcmid (t : Interval) (ht : t ∈ Ioo (0 : Interval) 1) :
      (c t).1 ∈ Ioo (0 : Interval) 1 := by
    have hnot : ¬ ((c t).1 = 0 ∨ (c t).1 = 1) := by
      rw [← hB,hEc]
      exact haInterior t ht
    exact ⟨bot_lt_iff_ne_bot.mpr (fun h => hnot (Or.inl h)),
      lt_top_iff_ne_top.mpr (fun h => hnot (Or.inr h))⟩
  have hc0 : (c 0).1 = 0 ∨ (c 0).1 = 1 :=
    (hB _).mp ((hEc 0).symm ▸ haends.1)
  have hc1 : (c 1).1 = 0 ∨ (c 1).1 = 1 :=
    (hB _).mp ((hEc 1).symm ▸ haends.2)
  have hdiff : (c 0).1 ≠ (c 1).1 := by
    intro he
    apply essential_rectangle_arc_cannot_have_same_end B E hE hB a ha haInterior
      hessential haE (c 0).1 hc0
    · exact ⟨(c 0).2,hEc 0⟩
    · refine ⟨(c 1).2,?_⟩
      rw [he]
      exact hEc 1
  have run (d : C(Interval,Interval × Interval)) (hd : IsEmbedding d)
      (hd0 : (d 0).1 = 0) (hd1 : (d 1).1 = 1)
      (hdwidth : ∀ t, (d t).2 ∈ Ioo (0 : Interval) 1)
      (hdmid : ∀ t ∈ Ioo (0 : Interval) 1, (d t).1 ∈ Ioo (0 : Interval) 1)
      (hdrange : Set.range (E.comp d) = Set.range a) :
      ∃ H : AmbientIsotopy X,
        (∀ t, (fun x => H.map (t,x)) '' B = B) ∧
        H.finalMap '' Set.range (fun s : Interval => E (s,p)) = Set.range a := by
    obtain ⟨H,hHB,hHrange,hHfix⟩ := embedded_strip_free_crosscut_ambient_motion B E hE
      hopen hB d hd hd0 hd1 (hdwidth 0) (hdwidth 1)
      (fun t ht => ⟨hdmid t ht,hdwidth t⟩) p hp
    exact ⟨H,hHB,hHrange.trans hdrange⟩
  rcases hc0 with hc0 | hc0
  · have hc1 : (c 1).1 = 1 := hc1.resolve_left (fun h => hdiff (hc0.trans h.symm))
    apply run c hc hc0 hc1 hcwidth hcmid
    have heq : E.comp c = a := by ext t; exact hEc t
    rw [heq]
  · have hc1 : (c 1).1 = 0 := hc1.resolve_right (fun h => hdiff (hc0.trans h.symm))
    let r : C(Interval,Interval) := ⟨unitInterval.symm,unitInterval.continuous_symm⟩
    let d := c.comp r
    have hdrange : Set.range (E.comp d) = Set.range a := by
      change Set.range ((E ∘ c) ∘ unitInterval.symm) = Set.range a
      rw [unitInterval.symm_bijective.surjective.range_comp]
      have heq : E ∘ c = a := funext hEc
      rw [heq]
    apply run d (hc.comp unitInterval.symmHomeomorph.isEmbedding)
      (by simpa [d,r,unitInterval.symm_zero] using hc1)
      (by simpa [d,r,unitInterval.symm_one] using hc0)
      (fun t => hcwidth _) ?_ hdrange
    intro t ht
    apply hcmid
    change 0 < unitInterval.symm t ∧ unitInterval.symm t < 1
    constructor
    · change 0 < (1 - (t:ℝ))
      exact sub_pos.mpr ht.2
    · change (1 - (t:ℝ)) < 1
      linarith [show (0:ℝ) < (t:ℝ) from ht.1]

#print axioms embedded_rectangle_unit_disk_carrier
#print axioms essential_rectangle_arc_cannot_have_same_end
#print axioms essential_arc_inside_strip_is_in_rail_class

/-- Class-distinct essential proper arcs cannot enter a boundary-attached
strip when they avoid its two rail sides. The clearance follows from the
original ambient class relation, rather than a fixed-endpoint relation. -/
theorem distinct_class_essential_arc_clears_strip_carrier
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B : Set X) (E : C(Interval × Interval,X)) (hE : IsEmbedding E)
    (hopen : IsOpen (E '' {z | z.2 ∈ Ioo (0 : Interval) 1}))
    (hB : ∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (a : C(Interval,X)) (ha : IsEmbedding a)
    (haends : a 0 ∈ B ∧ a 1 ∈ B)
    (haInterior : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (hessential : ¬ ∃ b : C(Interval,X), IsEmbedding b ∧ (∀ t, b t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : Plane) 1,X), IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = Set.range a ∪ Set.range b)
    (p : Interval) (hp : p ∈ Ioo (0 : Interval) 1)
    (hdistinct : ¬ ∃ H : AmbientIsotopy X,
      (∀ t, (fun x => H.map (t,x)) '' B = B) ∧
      H.finalMap '' Set.range (fun s : Interval => E (s,p)) = Set.range a)
    (hside0 : Disjoint (Set.range a) (Set.range (fun s : Interval => E (s,0))))
    (hside1 : Disjoint (Set.range a) (Set.range (fun s : Interval => E (s,1)))) :
    Disjoint (Set.range a) (Set.range E) := by
  let U : Set X := E '' {z | z.2 ∈ Ioo (0 : Interval) 1}
  let C : Set X := Set.range E
  have hC : IsClosed C := (isCompact_range E.continuous).isClosed
  have hcover : Set.range a ⊆ U ∪ Cᶜ := by
    intro x hx
    by_cases hxC : x ∈ C
    · obtain ⟨z,rfl⟩ := hxC
      left
      refine ⟨z,?_,rfl⟩
      constructor
      · apply bot_lt_iff_ne_bot.mpr
        intro hz
        exact Set.disjoint_left.mp hside0 hx ⟨z.1,
          congrArg E (show (z.1,(0 : Interval)) = z from Prod.ext rfl hz.symm)⟩
      · apply lt_top_iff_ne_top.mpr
        intro hz
        exact Set.disjoint_left.mp hside1 hx ⟨z.1,
          congrArg E (show (z.1,(1 : Interval)) = z from Prod.ext rfl hz.symm)⟩
    · exact Or.inr hxC
  have hconnected : IsPreconnected (Set.range a) := isPreconnected_range a.continuous
  have hor : Set.range a ⊆ U ∨ Set.range a ⊆ Cᶜ :=
    hconnected.subset_or_subset hopen hC.isOpen_compl
      (disjoint_compl_right.mono_left (Set.image_subset_range E _)) hcover
  have hout : Set.range a ⊆ Cᶜ := hor.resolve_left (fun hin =>
    hdistinct (essential_arc_inside_strip_is_in_rail_class B E hE hopen hB a ha
      haends haInterior hessential hin p hp))
  exact Set.disjoint_left.mpr (fun x hx hc => hout hx hc)

#print axioms distinct_class_essential_arc_clears_strip_carrier

end CoherentEndpointMotion
