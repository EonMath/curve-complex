import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.RegionalDiskSelfIntrusionSubdisk

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

variable {S : Type} [TopologicalSpace S]
  [ChartedSpace Plane S] [ClosedSurface S]

structure TwoSideDisk (a b : C(Interval,S)) where
  first : C(Interval,S)
  second : C(Interval,S)
  disk : C(Metric.closedBall (0 : Plane) 1,S)
  first_embedded : Topology.IsEmbedding first
  second_embedded : Topology.IsEmbedding second
  disk_embedded : Topology.IsEmbedding disk
  first_on_a : Set.range first ⊆ Set.range a
  second_on_b : Set.range second ⊆ Set.range b
  zero_eq : first 0 = second 0
  one_eq : first 1 = second 1
  boundary_eq : disk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
    Set.range first ∪ Set.range second
  a_zero_out : a 0 ∉ disk '' {z | z.val ∈ Metric.ball (0 : Plane) 1}
  a_one_out : a 1 ∉ disk '' {z | z.val ∈ Metric.ball (0 : Plane) 1}
  b_zero_out : b 0 ∉ disk '' {z | z.val ∈ Metric.ball (0 : Plane) 1}
  b_one_out : b 1 ∉ disk '' {z | z.val ∈ Metric.ball (0 : Plane) 1}

private theorem two_side_disk_intrusion_strict_subdisk
    (a b : C(Interval,S))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (D : TwoSideDisk a b)
    (hin : ((Set.range a ∪ Set.range b) ∩
      D.disk '' {z | z.val ∈ Metric.ball (0 : Plane) 1}).Nonempty) :
    ∃ E : TwoSideDisk a b,
      Set.range E.disk ⊆ Set.range D.disk ∧
      ∃ z ∈ ({D.first 0,D.first 1} : Set S), z ∉ Set.range E.disk := by
  obtain ⟨z,hz | hz,hzD⟩ := hin
  · obtain ⟨q,g,e,hq,hg,hqa,hgg,h0,h1,hqi,he,heB,heD,heOpen,hmissing⟩ :=
      regional_two_side_disk_first_intrusion_subdisk a D.first D.second
        ha D.first_embedded D.second_embedded D.first_on_a
        D.zero_eq D.one_eq D.disk D.disk_embedded D.boundary_eq
        D.a_zero_out D.a_one_out ⟨z,hz,hzD⟩
    let E : TwoSideDisk a b := {
      first := q, second := g, disk := e
      first_embedded := hq, second_embedded := hg, disk_embedded := he
      first_on_a := hqa, second_on_b := hgg.trans D.second_on_b
      zero_eq := h0, one_eq := h1, boundary_eq := heB
      a_zero_out := fun h => D.a_zero_out (heOpen h)
      a_one_out := fun h => D.a_one_out (heOpen h)
      b_zero_out := fun h => D.b_zero_out (heOpen h)
      b_one_out := fun h => D.b_one_out (heOpen h) }
    exact ⟨E,heD,hmissing⟩
  · obtain ⟨q,g,e,hq,hg,hqb,hgg,h0,h1,hqi,he,heB,heD,heOpen,hmissing⟩ :=
      regional_two_side_disk_first_intrusion_subdisk b D.second D.first
        hb D.second_embedded D.first_embedded D.second_on_b
        D.zero_eq.symm D.one_eq.symm D.disk D.disk_embedded
        (D.boundary_eq.trans (Set.union_comm _ _))
        D.b_zero_out D.b_one_out ⟨z,hz,hzD⟩
    let E : TwoSideDisk a b := {
      first := g, second := q, disk := e
      first_embedded := hg, second_embedded := hq, disk_embedded := he
      first_on_a := hgg.trans D.first_on_a, second_on_b := hqb
      zero_eq := h0.symm, one_eq := h1.symm
      boundary_eq := heB.trans (Set.union_comm _ _)
      a_zero_out := fun h => D.a_zero_out (heOpen h)
      a_one_out := fun h => D.a_one_out (heOpen h)
      b_zero_out := fun h => D.b_zero_out (heOpen h)
      b_one_out := fun h => D.b_one_out (heOpen h) }
    refine ⟨E,heD,?_⟩
    simpa only [D.zero_eq,D.one_eq] using hmissing

/-- Every finite-contact actual two-side disk contains a two-side subdisk whose
    interior avoids both original embedded arcs, with no transversality input. -/
theorem regional_two_side_disk_has_empty_arc_interior
    (a b : C(Interval,S))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (hfinite : (Set.range a ∩ Set.range b).Finite)
    (D : TwoSideDisk a b) :
    ∃ E : TwoSideDisk a b,
      Set.range E.disk ⊆ Set.range D.disk ∧
      Disjoint (E.disk '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
        (Set.range a ∪ Set.range b) := by
  classical
  let C : Set S := Set.range a ∩ Set.range b
  let energy (E : TwoSideDisk a b) : ℕ :=
    (C ∩ Set.range E.disk).ncard
  let P : ℕ → Prop := fun n =>
    ∃ E : TwoSideDisk a b,
      Set.range E.disk ⊆ Set.range D.disk ∧ energy E = n
  have hex : ∃ n, P n := ⟨energy D,D,Set.Subset.rfl,rfl⟩
  obtain ⟨E,hED,henergy⟩ := Nat.find_spec hex
  have hempty : Disjoint
      (E.disk '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
      (Set.range a ∪ Set.range b) := by
    apply Set.disjoint_left.mpr
    intro z hzDisk hzArc
    obtain ⟨F,hFE,⟨w,hwcorner,hwnotF⟩⟩ :=
      two_side_disk_intrusion_strict_subdisk a b ha hb E
        ⟨z,hzArc,hzDisk⟩
    have hwC : w ∈ C := by
      rcases Set.mem_insert_iff.mp hwcorner with hw | hw
      · have hw' : w = E.first 0 := hw
        exact ⟨E.first_on_a ⟨0,hw'.symm⟩,
          E.second_on_b ⟨0,E.zero_eq.symm.trans hw'.symm⟩⟩
      · have hw' : w = E.first 1 := Set.mem_singleton_iff.mp hw
        exact ⟨E.first_on_a ⟨1,hw'.symm⟩,
          E.second_on_b ⟨1,E.one_eq.symm.trans hw'.symm⟩⟩
    have hwE : w ∈ Set.range E.disk :=
      Set.image_subset_range _ _ (E.boundary_eq.symm ▸
        (show w ∈ Set.range E.first ∪ Set.range E.second from
          Or.inl (by
            rcases Set.mem_insert_iff.mp hwcorner with hw | hw
            · exact ⟨0,hw.symm⟩
            · exact ⟨1,(Set.mem_singleton_iff.mp hw).symm⟩)))
    have hlt : energy F < energy E := Set.ncard_lt_ncard
      (Set.ssubset_iff_subset_ne.mpr
        ⟨Set.inter_subset_inter_right C hFE,by
          intro heq
          have hwF : w ∈ C ∩ Set.range F.disk :=
            heq.symm ▸ (show w ∈ C ∩ Set.range E.disk from ⟨hwC,hwE⟩)
          exact hwnotF hwF.2⟩) (hfinite.inter_of_left _)
    exact Nat.find_min hex (hlt.trans_eq henergy)
      ⟨F,hFE.trans hED,rfl⟩
  exact ⟨E,hED,hempty⟩

end RegionalEmbeddedFamily
