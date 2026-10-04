import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeCancellationBookkeepingScaffolds
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.OriginalDiskCandidateConfinement
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeSelectedBigonFacts
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedSideEndpointMarks

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A literal confined endpoint candidate. Interior mark-freeness is
deliberately not a field: the opposite endpoint may still be inside. -/
structure RelativeEndpointDiskCandidate (M : HyperellipticModel E S)
    (a b : NonLoopArc M) (N : ArcNeighborhood a) where
  contact : S
  contact_crossing : contact ∈ ArcSurgery.crossings M a.toEssential b.toEssential
  firstSide : C(Interval,S)
  secondSide : C(Interval,S)
  first_embedded : IsEmbedding firstSide
  second_embedded : IsEmbedding secondSide
  first_zero : firstSide 0 = a.val.map 0
  second_zero : secondSide 0 = a.val.map 0
  first_one : firstSide 1 = contact
  second_one : secondSide 1 = contact
  first_on_arc : range firstSide ⊆ a.image
  second_on_arc : range secondSide ⊆ b.image
  sides_inter : range firstSide ∩ range secondSide = {a.val.map 0,contact}
  disk : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S)
  disk_embedded : IsEmbedding disk
  boundary_eq : disk '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
    range firstSide ∪ range secondSide
  disk_inside : range disk ⊆ interior N.closedSet

theorem relative_oriented_finite_contacts_produce_endpoint_disk_candidate
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hstart : a.val.map 0 = b.val.map 0)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty) :
    Nonempty (RelativeEndpointDiskCandidate M a b N) := by
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨r,s,hr0,hr1,hs0,hs1,hmeet,hclean⟩ :=
    relative_finite_contact_produces_clean_endpoint_prefixes M a b hstart hfinite hpositive
  let scale (v t : Interval) : Interval := ⟨t.val*v.val,by
    constructor
    · exact mul_nonneg t.property.1 v.property.1
    · nlinarith [t.property.1,t.property.2,v.property.1,v.property.2]⟩
  have hcont (v : Interval) : Continuous (scale v) :=
    (continuous_subtype_val.mul continuous_const).subtype_mk _
  have hzero (v : Interval) : scale v 0 = 0 := Subtype.ext (by simp [scale])
  have hone (v : Interval) : scale v 1 = v := Subtype.ext (by simp [scale])
  have hle (v t : Interval) : scale v t ≤ v := by
    change t.val*v.val ≤ v.val
    nlinarith [t.property.1,t.property.2,v.property.1]
  have hi (v : Interval) (hv : 0 < v) : Function.Injective (scale v) := by
    intro t u he
    apply Subtype.ext
    exact mul_right_cancel₀ (ne_of_gt (show 0 < v.val from hv)) (congrArg Subtype.val he)
  let f : C(Interval,S) := ⟨a.val.map ∘ scale r,a.val.continuous.comp (hcont r)⟩
  let g : C(Interval,S) := ⟨b.val.map ∘ scale s,b.val.continuous.comp (hcont s)⟩
  have hf0 : f 0 = a.val.map 0 := congrArg a.val.map (hzero r)
  have hg0 : g 0 = a.val.map 0 := (congrArg b.val.map (hzero s)).trans hstart.symm
  have hf1 : f 1 = a.val.map r := congrArg a.val.map (hone r)
  have hg1 : g 1 = a.val.map r := (congrArg b.val.map (hone s)).trans hmeet.symm
  have hfi : Function.Injective f := a.injective.comp (hi r hr0)
  have hgi : Function.Injective g := b.injective.comp (hi s hs0)
  have hcross (u v : Interval) (he : f u = g v) :
      (u=0 ∧ v=0) ∨ (u=1 ∧ v=1) := by
    rcases hclean (scale r u) (scale s v) (hle r u) (hle s v) he with h | h
    · exact Or.inl ⟨hi r hr0 (h.1.trans (hzero r).symm),hi s hs0 (h.2.trans (hzero s).symm)⟩
    · exact Or.inr ⟨hi r hr0 (h.1.trans (hone r).symm),hi s hs0 (h.2.trans (hone s).symm)⟩
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f g hfi hgi
    (hf0.trans hg0.symm) (hf1.trans hg1.symm) hcross
  have hfa : range f ⊆ a.image := by rintro x ⟨t,rfl⟩; exact mem_range_self _
  have hgb : range g ⊆ b.image := by rintro x ⟨t,rfl⟩; exact mem_range_self _
  have hcN : c.image ⊆ interior N.closedSet := by
    rw [hc]
    exact union_subset (hfa.trans N.arc_inside) (hgb.trans hb)
  obtain ⟨d,hd,hdb,hdN⟩ := relative_jordan_candidate_bounds_original_interior_disk M a N c hcN
  have hrnot : a.val.map r ∉ M.cover.branch := by
    intro hm
    rcases a.val.marked_only_at_ends r hm with h0 | h1
    · exact (ne_of_gt hr0) h0
    · exact (ne_of_lt hr1) h1
  have hcontact : a.val.map r ∈ ArcSurgery.crossings M a.toEssential b.toEssential :=
    ⟨⟨mem_range_self r,hrnot⟩,⟨s,hmeet.symm⟩,hrnot⟩
  have hsides : range f ∩ range g = {a.val.map 0,a.val.map r} := by
    ext x
    constructor
    · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
      rcases hcross t u (ht.trans hu.symm) with ⟨ht0,_⟩ | ⟨ht1,_⟩
      · exact Or.inl (ht.symm.trans ((congrArg f ht0).trans hf0))
      · exact Or.inr (ht.symm.trans ((congrArg f ht1).trans hf1))
    · intro hx
      rcases mem_insert_iff.mp hx with hx | hx
      · exact hx ▸ ⟨⟨0,hf0⟩,⟨0,hg0⟩⟩
      · exact mem_singleton_iff.mp hx ▸ ⟨⟨1,hf1⟩,⟨1,hg1⟩⟩
  exact ⟨{
    contact := a.val.map r,contact_crossing := hcontact,
    firstSide := f,secondSide := g,
    first_embedded := (f.continuous.isClosedEmbedding hfi).isEmbedding,
    second_embedded := (g.continuous.isClosedEmbedding hgi).isEmbedding,
    first_zero := hf0,second_zero := hg0,first_one := hf1,second_one := hg1,
    first_on_arc := hfa,second_on_arc := hgb,sides_inter := hsides,
    disk := d,disk_embedded := hd,boundary_eq := hdb.trans hc,disk_inside := hdN }⟩

theorem relative_endpoint_candidate_other_endpoint_outside_produces_marked_bigon
    (M : HyperellipticModel E S) (a b : NonLoopArc M) (N : ArcNeighborhood a)
    (C : RelativeEndpointDiskCandidate M a b N) (hout : a.val.map 1 ∉ range C.disk) :
    ∃ B : ActualMarkedTwoSideDisk M a.toEssential b.toEssential,
      range B.disk ⊆ interior N.closedSet ∧
      B.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential := by
  have hmarks : ∀ x ∈ range C.disk, x ∈ M.cover.branch →
      x ∈ ({a.val.map 0,C.contact}:Set S) := by
    intro x hx hxmark
    have hend : x ∈ ({a.val.map 0,a.val.map 1}:Set S) :=
      N.marked_inside ▸ (show x ∈ (M.cover.branch:Set S) ∩ N.closedSet from
        ⟨hxmark,interior_subset (C.disk_inside hx)⟩)
    rcases mem_insert_iff.mp hend with he | he
    · exact Or.inl he
    · exact False.elim (hout (mem_singleton_iff.mp he ▸ hx))
  exact ⟨{
    firstCorner := a.val.map 0,secondCorner := C.contact,
    firstSide := C.firstSide,secondSide := C.secondSide,
    first_embedded := C.first_embedded,second_embedded := C.second_embedded,
    first_zero := C.first_zero,second_zero := C.second_zero,
    first_one := C.first_one,second_one := C.second_one,
    first_on_curve := C.first_on_arc,second_on_curve := C.second_on_arc,
    sides_inter := C.sides_inter,disk := C.disk,disk_embedded := C.disk_embedded,
    boundary_eq := C.boundary_eq,marks_are_corners := hmarks },C.disk_inside,C.contact_crossing⟩

theorem relative_finite_contacts_produce_original_endpoint_disk_candidate
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1})
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty) :
    Nonempty (RelativeEndpointDiskCandidate M a b N) := by
  have ha0 : a.val.map 0 ∈ ({b.val.map 0,b.val.map 1}:Set S) := by
    rw [← hends]
    exact Set.mem_insert _ _
  rcases mem_insert_iff.mp ha0 with hstart | hlast
  · exact relative_oriented_finite_contacts_produce_endpoint_disk_candidate M a b N hb
      hstart hfinite hpositive
  · have hlast' : a.val.map 0 = b.val.map 1 := mem_singleton_iff.mp hlast
    obtain ⟨d,hd0,hd1,hdim⟩ := actual_nonloop_reversed_representative M b.toEssential b.property
    have hdne : d.val.map 0 ≠ d.val.map 1 := by rw [hd0,hd1]; exact b.property.symm
    let b' : NonLoopArc M := ⟨d.val,hdne⟩
    have him : b'.image = b.image := hdim
    have hc : ArcSurgery.crossings M a.toEssential b'.toEssential =
        ArcSurgery.crossings M a.toEssential b.toEssential := by
      change (a.image \ (M.cover.branch:Set S)) ∩ (b'.image \ (M.cover.branch:Set S)) = _
      rw [him]
      rfl
    obtain ⟨C⟩ := relative_oriented_finite_contacts_produce_endpoint_disk_candidate M a b' N
      (him.symm ▸ hb) (hlast'.trans hd0.symm) (hc.symm ▸ hfinite) (hc.symm ▸ hpositive)
    exact ⟨{
      contact := C.contact,contact_crossing := hc ▸ C.contact_crossing,
      firstSide := C.firstSide,secondSide := C.secondSide,
      first_embedded := C.first_embedded,second_embedded := C.second_embedded,
      first_zero := C.first_zero,second_zero := C.second_zero,
      first_one := C.first_one,second_one := C.second_one,
      first_on_arc := C.first_on_arc,second_on_arc := him ▸ C.second_on_arc,
      sides_inter := C.sides_inter,disk := C.disk,disk_embedded := C.disk_embedded,
      boundary_eq := C.boundary_eq,disk_inside := C.disk_inside }⟩

theorem relative_endpoint_disk_candidate_opposite_endpoint_not_on_boundary
    (M : HyperellipticModel E S) (a b : NonLoopArc M) (N : ArcNeighborhood a)
    (C : RelativeEndpointDiskCandidate M a b N) :
    a.val.map 1 ∉ C.disk '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
  let : T2Space S := M.sphere.symm.t2Space
  have hside (c : NonLoopArc M) (f : C(Interval,S)) (hf : IsEmbedding f)
      (hfc : range f ⊆ c.image) (hf0 : f 0 = a.val.map 0) (hf1 : f 1 = C.contact)
      (t : Interval) (ht : f t = a.val.map 1) : False := by
    let A : C(Interval,S) := ⟨c.val.map,c.val.continuous⟩
    obtain ⟨v,hv⟩ := hfc (mem_range_self t)
    have hvmark : c.val.map v ∈ M.cover.branch := hv.trans ht ▸ a.val.end_marked
    have he : f t = A 0 ∨ f t = A 1 := by
      rcases c.val.marked_only_at_ends v hvmark with hv0 | hv1
      · exact Or.inl (hv.symm.trans (congrArg c.val.map hv0))
      · exact Or.inr (hv.symm.trans (congrArg c.val.map hv1))
    rcases actual_embedded_side_source_endpoint A f
      (A.continuous.isClosedEmbedding c.injective).isEmbedding hf hfc t he with ht0 | ht1
    · exact a.property (hf0.symm.trans ((congrArg f ht0).symm.trans ht))
    · have hcontactnot : C.contact ∉ M.cover.branch := C.contact_crossing.1.2
      exact hcontactnot ((hf1.symm.trans ((congrArg f ht1).symm.trans ht)) ▸ a.val.end_marked)
  rw [C.boundary_eq]
  rintro (⟨t,ht⟩ | ⟨t,ht⟩)
  · exact hside a C.firstSide C.first_embedded C.first_on_arc C.first_zero C.first_one t ht
  · exact hside b C.secondSide C.second_embedded C.second_on_arc C.second_zero C.second_one t ht

end CurveComplex.HyperellipticModel
