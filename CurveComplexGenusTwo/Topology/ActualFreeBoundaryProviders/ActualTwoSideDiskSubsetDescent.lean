import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.InteriorRailProtectedMotion
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.RegionalDiskEmptyInterior

namespace CoherentEndpointMotion
open CurveComplex Set Topology Schoenflies

/-- Reuse actual ambient finite-contact disk descent and restrict every
selected point back to the caller's subset. The entire subdisk stays in F;
no regional fixed-endpoint homotopy or new disk-containment premise occurs. -/
theorem actual_two_side_disk_in_subset_has_empty_subdisk
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (B : Set ↥F) (a b : C(Interval,↥F))
    (ha : IsEmbedding a) (hb : IsEmbedding b)
    (haends : a 0 ∈ B ∧ a 1 ∈ B) (hbends : b 0 ∈ B ∧ b 1 ∈ B)
    (hfinite : (range a ∩ range b).Finite)
    (p q : C(Interval,↥F)) (hp : IsEmbedding p) (hq : IsEmbedding q)
    (hpa : range p ⊆ range a) (hqb : range q ⊆ range b)
    (h0 : p 0 = q 0) (h1 : p 1 = q 1)
    (d : C(Metric.closedBall (0 : Plane) 1,↥F)) (hd : IsEmbedding d)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range p ∪ range q)
    (hBfree : Disjoint B (d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})) :
    ∃ (p' q' : C(Interval,↥F)) (e : C(Metric.closedBall (0 : Plane) 1,↥F)),
      IsEmbedding p' ∧ IsEmbedding q' ∧ IsEmbedding e ∧
      range p' ⊆ range a ∧ range q' ⊆ range b ∧
      p' 0 = q' 0 ∧ p' 1 = q' 1 ∧
      e '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range p' ∪ range q' ∧
      range e ⊆ range d ∧
      Disjoint (e '' {z | z.val ∈ Metric.ball (0 : Plane) 1}) (range a ∪ range b) := by
  let lift (c : C(Interval,↥F)) : C(Interval,S) :=
    ⟨fun t => (c t).val,continuous_subtype_val.comp c.continuous⟩
  let dS : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
  have hrange (c : C(Interval,↥F)) : range (lift c) = Subtype.val '' range c := by
    rw [← Set.range_comp]
    rfl
  have hfinS : (range (lift a) ∩ range (lift b)).Finite := by
    rw [hrange a,hrange b,← Set.image_inter Subtype.val_injective]
    exact hfinite.image Subtype.val
  have hbdS : dS '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      range (lift p) ∪ range (lift q) := by
    change (Subtype.val ∘ d) '' _ = _
    rw [Set.image_comp,hboundary,Set.image_union,hrange p,hrange q]
  have hout (c : C(Interval,↥F)) (t : Interval) (ht : c t ∈ B) :
      lift c t ∉ dS '' {z | z.val ∈ Metric.ball (0 : Plane) 1} := by
    rintro ⟨z,hz,he⟩
    exact Set.disjoint_left.mp hBfree ht ⟨z,hz,Subtype.ext he⟩
  let D : RegionalEmbeddedFamily.TwoSideDisk (lift a) (lift b) := {
    first := lift p, second := lift q, disk := dS
    first_embedded := IsEmbedding.subtypeVal.comp hp
    second_embedded := IsEmbedding.subtypeVal.comp hq
    disk_embedded := IsEmbedding.subtypeVal.comp hd
    first_on_a := by rw [hrange p,hrange a]; exact Set.image_mono hpa
    second_on_b := by rw [hrange q,hrange b]; exact Set.image_mono hqb
    zero_eq := congrArg Subtype.val h0
    one_eq := congrArg Subtype.val h1
    boundary_eq := hbdS
    a_zero_out := hout a 0 haends.1
    a_one_out := hout a 1 haends.2
    b_zero_out := hout b 0 hbends.1
    b_one_out := hout b 1 hbends.2 }
  obtain ⟨D',hsub,hempty⟩ := RegionalEmbeddedFamily.regional_two_side_disk_has_empty_arc_interior
    (lift a) (lift b) (IsEmbedding.subtypeVal.comp ha) (IsEmbedding.subtypeVal.comp hb) hfinS D
  have hpF (t : Interval) : D'.first t ∈ F := by
    obtain ⟨s,hs⟩ := D'.first_on_a (Set.mem_range_self t)
    exact hs ▸ (a s).property
  have hqF (t : Interval) : D'.second t ∈ F := by
    obtain ⟨s,hs⟩ := D'.second_on_b (Set.mem_range_self t)
    exact hs ▸ (b s).property
  have heF (z : Metric.closedBall (0 : Plane) 1) : D'.disk z ∈ F := by
    obtain ⟨w,hw⟩ := hsub (Set.mem_range_self z)
    exact hw ▸ (d w).property
  let p' : C(Interval,↥F) := ⟨fun t => ⟨D'.first t,hpF t⟩,D'.first.continuous.subtype_mk _⟩
  let q' : C(Interval,↥F) := ⟨fun t => ⟨D'.second t,hqF t⟩,D'.second.continuous.subtype_mk _⟩
  let e : C(Metric.closedBall (0 : Plane) 1,↥F) :=
    ⟨fun z => ⟨D'.disk z,heF z⟩,D'.disk.continuous.subtype_mk _⟩
  have hp' : IsEmbedding p' := (p'.continuous.isClosedEmbedding (by
    intro s t he
    exact D'.first_embedded.injective (congrArg Subtype.val he))).isEmbedding
  have hq' : IsEmbedding q' := (q'.continuous.isClosedEmbedding (by
    intro s t he
    exact D'.second_embedded.injective (congrArg Subtype.val he))).isEmbedding
  have he' : IsEmbedding e := (e.continuous.isClosedEmbedding (by
    intro s t he
    exact D'.disk_embedded.injective (congrArg Subtype.val he))).isEmbedding
  refine ⟨p',q',e,hp',hq',he',?_,?_,Subtype.ext D'.zero_eq,Subtype.ext D'.one_eq,?_,?_,?_⟩
  · rintro x ⟨t,rfl⟩
    obtain ⟨s,hs⟩ := D'.first_on_a (Set.mem_range_self t)
    exact ⟨s,Subtype.ext hs⟩
  · rintro x ⟨t,rfl⟩
    obtain ⟨s,hs⟩ := D'.second_on_b (Set.mem_range_self t)
    exact ⟨s,Subtype.ext hs⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨z,hz,rfl⟩
      have hx : D'.disk z ∈ range D'.first ∪ range D'.second :=
        D'.boundary_eq ▸ Set.mem_image_of_mem D'.disk hz
      rcases hx with ⟨t,ht⟩ | ⟨t,ht⟩
      · exact Or.inl ⟨t,Subtype.ext ht⟩
      · exact Or.inr ⟨t,Subtype.ext ht⟩
    · rintro x (⟨t,rfl⟩ | ⟨t,rfl⟩)
      · obtain ⟨z,hz,he⟩ := D'.boundary_eq.symm ▸
          (show D'.first t ∈ range D'.first ∪ range D'.second from Or.inl (Set.mem_range_self t))
        exact ⟨z,hz,Subtype.ext he⟩
      · obtain ⟨z,hz,he⟩ := D'.boundary_eq.symm ▸
          (show D'.second t ∈ range D'.first ∪ range D'.second from Or.inr (Set.mem_range_self t))
        exact ⟨z,hz,Subtype.ext he⟩
  · rintro x ⟨z,rfl⟩
    obtain ⟨w,hw⟩ := hsub (Set.mem_range_self z)
    exact ⟨w,Subtype.ext hw⟩
  · apply Set.disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ (⟨s,hs⟩ | ⟨s,hs⟩)
    · exact Set.disjoint_left.mp hempty ⟨z,hz,rfl⟩
        (Or.inl ⟨s,congrArg Subtype.val hs⟩)
    · exact Set.disjoint_left.mp hempty ⟨z,hz,rfl⟩
        (Or.inr ⟨s,congrArg Subtype.val hs⟩)

/-- A continuous arc with an endpoint on B avoids the whole actual disk when
it avoids the disk boundary and B avoids the disk interior. This supplies
ordinary-bigon graph clearance without any arc-essentiality assumption. -/
theorem arc_with_boundary_endpoint_clears_actual_disk
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (B : Set ↥F) (c : C(Interval,↥F)) (hc0 : c 0 ∈ B)
    (d : C(Metric.closedBall (0 : Plane) 1,↥F)) (hd : IsEmbedding d)
    (hBfree : Disjoint B (d '' {z | z.val ∈ Metric.ball (0 : Plane) 1}))
    (hboundary : Disjoint (range c)
      (d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1})) :
    Disjoint (range c) (range d) := by
  let cS : C(Interval,S) :=
    ⟨fun t => (c t).val,continuous_subtype_val.comp c.continuous⟩
  let dS : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
  have hdS : IsEmbedding dS := IsEmbedding.subtypeVal.comp hd
  have hboundaryS : Disjoint (range cS)
      (dS '' {z | z.val ∈ Metric.sphere (0 : Plane) 1}) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨t,rfl⟩ ⟨z,hz,he⟩
    exact Set.disjoint_left.mp hboundary (Set.mem_range_self t) ⟨z,hz,Subtype.ext he⟩
  have houtside : range cS ⊆ (range dS)ᶜ :=
    (RegionalEmbeddedFamily.connected_open_set_avoiding_disk_boundary_dichotomy
      (range cS) (isPreconnected_range cS.continuous) dS hdS hboundaryS).resolve_left (by
        intro hin
        have h0 := hin (Set.mem_range_self (0 : Interval))
        rw [LocalSurgery.embedded_surface_disk_interior_eq dS hdS] at h0
        obtain ⟨z,hz,he⟩ := h0
        exact Set.disjoint_left.mp hBfree hc0 ⟨z,hz,Subtype.ext he⟩)
  apply Set.disjoint_left.mpr
  rintro x ⟨t,rfl⟩ ⟨z,he⟩
  exact houtside (Set.mem_range_self t) ⟨z,congrArg Subtype.val he⟩

/-- Avoidance of the two prescribed old/target arc sides derives whole-disk
clearance of a protected arc. The original B-interior exclusion is the only
boundary condition; graph clearance is a conclusion. -/
theorem actual_ordinary_two_side_disk_clears_protected_arc
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (B : Set ↥F) (a b c : C(Interval,↥F)) (hc0 : c 0 ∈ B)
    (p q : C(Interval,↥F)) (hpa : range p ⊆ range a) (hqb : range q ⊆ range b)
    (d : C(Metric.closedBall (0 : Plane) 1,↥F)) (hd : IsEmbedding d)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range p ∪ range q)
    (hBfree : Disjoint B (d '' {z | z.val ∈ Metric.ball (0 : Plane) 1}))
    (hca : Disjoint (range c) (range a)) (hcb : Disjoint (range c) (range b)) :
    Disjoint (range c) (range d) := by
  apply arc_with_boundary_endpoint_clears_actual_disk F B c hc0 d hd hBfree
  rw [hboundary]
  exact (hca.mono_right hpa).sup_right (hcb.mono_right hqb)

end CoherentEndpointMotion
