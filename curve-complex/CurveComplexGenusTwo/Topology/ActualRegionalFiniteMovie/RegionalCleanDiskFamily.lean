import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalDiskArcLift

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

private abbrev UnitDisk := Metric.closedBall (0 : Plane) 1
private def UnitBoundary : Set UnitDisk :=
  {z | z.val ∈ Metric.sphere (0 : Plane) 1}

theorem clean_disk_gives_aligned_square
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hmeet : ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (d : C(UnitDisk, ↥F)) (hd : Topology.IsEmbedding d)
    (hboundary : d '' UnitBoundary = Set.range a ∪ Set.range b)
    (hinside : ∀ z : UnitDisk,
      z.val ∈ Metric.ball (0 : Plane) 1 → (d z).val ∉ frontier F) :
    ∃ q : C(Plane.closedSquare 0 1, ↥F),
      Topology.IsEmbedding q ∧
      q ⟨cornerNE, squareSweep_left 0 ▸
        squareSweep_in_closedSquare 0 0⟩ = a 0 ∧
      q ⟨cornerSW, squareSweep_right 0 ▸
        squareSweep_in_closedSquare 0 1⟩ = a 1 ∧
      q '' {z : Plane.closedSquare 0 1 |
        z.val ∈ sideTop ∪ sideLeft} = Set.range a ∧
      q '' {z : Plane.closedSquare 0 1 |
        z.val ∈ sideBottom ∪ sideRight} = Set.range b ∧
      (∀ z : Plane.closedSquare 0 1,
        z.val ∈ Plane.openSquare 0 1 → (q z).val ∉ frontier F) := by
  obtain ⟨g, h, hg, hh, hg0, hg1, hcircle, hmeet, hgLift, hhLift⟩ :=
    clean_disk_boundary_pair_planar_lifts d hd a b ha hb h0 h1 hmeet hboundary
  obtain ⟨φ, hφcircle, hφball, hφclosed, hφg, hφh, hφ0, hφ1⟩ :=
    planar_clean_pair_schoenflies_alignment g h hg hh hg0 hg1 hmeet hcircle
  have hkin (z : Plane.closedSquare 0 1) : φ.symm z.val ∈
      Metric.closedBall (0 : Plane) 1 := by
    have hz : z.val ∈ φ '' Metric.closedBall (0 : Plane) 1 := hφclosed.symm ▸ z.property
    obtain ⟨w, hw, hzw⟩ := hz
    exact (φ.symm_apply_apply w ▸ congrArg φ.symm hzw.symm) ▸ hw
  let k : Plane.closedSquare 0 1 → UnitDisk :=
    fun z => ⟨φ.symm z.val, hkin z⟩
  have hkcont : Continuous k :=
    (φ.symm.continuous.comp continuous_subtype_val).subtype_mk _
  have hkemb : Topology.IsEmbedding k := by
    apply Topology.IsEmbedding.of_comp hkcont continuous_subtype_val
    exact φ.symm.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  let q : C(Plane.closedSquare 0 1, ↥F) :=
    ⟨fun z => d (k z), d.continuous.comp hkcont⟩
  have hqemb : Topology.IsEmbedding q := hd.comp hkemb
  have hkpoint (s : Interval) (u : UnitDisk) (hu : u.val = g s) :
      ∀ z : Plane.closedSquare 0 1, z.val = φ (g s) → k z = u := by
    intro z hz
    apply Subtype.ext
    change φ.symm z.val = u.val
    rw [hz, φ.symm_apply_apply]
    exact hu.symm
  have hkpointB (s : Interval) (u : UnitDisk) (hu : u.val = h s) :
      ∀ z : Plane.closedSquare 0 1, z.val = φ (h s) → k z = u := by
    intro z hz
    apply Subtype.ext
    change φ.symm z.val = u.val
    rw [hz, φ.symm_apply_apply]
    exact hu.symm
  have hq0 : q ⟨cornerNE, squareSweep_left 0 ▸
      squareSweep_in_closedSquare 0 0⟩ = a 0 := by
    obtain ⟨u, hu, hud⟩ := hgLift 0
    change d (k ⟨cornerNE, _⟩) = a 0
    rw [hkpoint 0 u hu _ hφ0.symm]
    exact hud
  have hq1 : q ⟨cornerSW, squareSweep_right 0 ▸
      squareSweep_in_closedSquare 0 1⟩ = a 1 := by
    obtain ⟨u, hu, hud⟩ := hgLift 1
    change d (k ⟨cornerSW, _⟩) = a 1
    rw [hkpoint 1 u hu _ hφ1.symm]
    exact hud
  have hqg : q '' {z : Plane.closedSquare 0 1 |
      z.val ∈ sideTop ∪ sideLeft} = Set.range a := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzφ : z.val ∈ φ '' Set.range g := hφg.symm ▸ hz
      obtain ⟨w, ⟨s, rfl⟩, hzw⟩ := hzφ
      obtain ⟨u, hu, hud⟩ := hgLift s
      refine ⟨s, ?_⟩
      change a s = d (k z)
      rw [hkpoint s u hu z hzw.symm]
      exact hud.symm
    · rintro ⟨s, rfl⟩
      have hsSphere : g s ∈ Metric.sphere (0 : Plane) 1 := by
        rw [← hcircle]
        exact Or.inl (Set.mem_range_self s)
      have hsClosed : φ (g s) ∈ Plane.closedSquare 0 1 := by
        rw [← hφclosed]
        exact ⟨g s, Metric.sphere_subset_closedBall hsSphere, rfl⟩
      let z : Plane.closedSquare 0 1 := ⟨φ (g s), hsClosed⟩
      refine ⟨z, ?_, ?_⟩
      · exact hφg ▸ ⟨g s, Set.mem_range_self s, rfl⟩
      · obtain ⟨u, hu, hud⟩ := hgLift s
        change d (k z) = a s
        rw [hkpoint s u hu z rfl]
        exact hud
  have hqh : q '' {z : Plane.closedSquare 0 1 |
      z.val ∈ sideBottom ∪ sideRight} = Set.range b := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzφ : z.val ∈ φ '' Set.range h := hφh.symm ▸ hz
      obtain ⟨w, ⟨s, rfl⟩, hzw⟩ := hzφ
      obtain ⟨u, hu, hud⟩ := hhLift s
      refine ⟨s, ?_⟩
      change b s = d (k z)
      rw [hkpointB s u hu z hzw.symm]
      exact hud.symm
    · rintro ⟨s, rfl⟩
      have hsSphere : h s ∈ Metric.sphere (0 : Plane) 1 := by
        rw [← hcircle]
        exact Or.inr (Set.mem_range_self s)
      have hsClosed : φ (h s) ∈ Plane.closedSquare 0 1 := by
        rw [← hφclosed]
        exact ⟨h s, Metric.sphere_subset_closedBall hsSphere, rfl⟩
      let z : Plane.closedSquare 0 1 := ⟨φ (h s), hsClosed⟩
      refine ⟨z, ?_, ?_⟩
      · exact hφh ▸ ⟨h s, Set.mem_range_self s, rfl⟩
      · obtain ⟨u, hu, hud⟩ := hhLift s
        change d (k z) = b s
        rw [hkpointB s u hu z rfl]
        exact hud
  have hqinside (z : Plane.closedSquare 0 1)
      (hz : z.val ∈ Plane.openSquare 0 1) :
      (q z).val ∉ frontier F := by
    have hzφ : z.val ∈ φ '' Metric.ball (0 : Plane) 1 := hφball.symm ▸ hz
    obtain ⟨w, hw, hzw⟩ := hzφ
    have hkball : (k z).val ∈ Metric.ball (0 : Plane) 1 := by
      change φ.symm z.val ∈ Metric.ball (0 : Plane) 1
      rw [← hzw, φ.symm_apply_apply]
      exact hw
    exact hinside (k z) hkball
  exact ⟨q, hqemb, hq0, hq1, hqg, hqh, hqinside⟩

theorem clean_disk_gives_embedded_family
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hmeet : ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (d : C(UnitDisk, ↥F)) (hd : Topology.IsEmbedding d)
    (hboundary : d '' UnitBoundary = Set.range a ∪ Set.range b)
    (hinside : ∀ z : UnitDisk,
      z.val ∈ Metric.ball (0 : Plane) 1 → (d z).val ∉ frontier F)
    (haClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (a s).val ∉ frontier F)
    (hbClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (b s).val ∉ frontier F) :
    ∃ (V : C(Interval × Interval, ↥F)) (ρ : Interval ≃ₜ Interval),
      ρ 0 = 0 ∧ ρ 1 = 1 ∧
      (∀ s, V (0,s) = a s) ∧ (∀ s, V (1,s) = b (ρ s)) ∧
      (∀ t, Topology.IsEmbedding (fun s => V (t,s))) ∧
      (∀ t, V (t,0) = a 0 ∧ V (t,1) = a 1) ∧
      (∀ t s, s ∈ Set.Ioo (0 : Interval) 1 →
        (V (t,s)).val ∉ frontier F) := by
  obtain ⟨q, hq, hq0, hq1, hqu, hql, hqi⟩ :=
    clean_disk_gives_aligned_square a b ha hb h0 h1 hmeet d hd hboundary hinside
  exact square_disk_family_of_boundary_ranges a b ha hb h0 h1 q hq hq0 hq1
    hqu hql hqi haClear hbClear

theorem clean_homotopic_regional_arcs_embedded_family
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hmeet : ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hhom : Path.Homotopic
      (⟨a, rfl, rfl⟩ : Path (a 0) (a 1))
      (⟨b, h0, h1⟩ : Path (a 0) (a 1)))
    (haClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (a s).val ∉ frontier F)
    (hbClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (b s).val ∉ frontier F) :
    ∃ (V : C(Interval × Interval, ↥F)) (ρ : Interval ≃ₜ Interval),
      ρ 0 = 0 ∧ ρ 1 = 1 ∧
      (∀ s, V (0,s) = a s) ∧ (∀ s, V (1,s) = b (ρ s)) ∧
      (∀ t, Topology.IsEmbedding (fun s => V (t,s))) ∧
      (∀ t, V (t,0) = a 0 ∧ V (t,1) = a 1) ∧
      (∀ t s, s ∈ Set.Ioo (0 : Interval) 1 →
        (V (t,s)).val ∉ frontier F) := by
  obtain ⟨d, hd, hboundary, hinside⟩ :=
    clean_homotopic_regional_arcs_bound_frontier_clear_disk
      S g hg hS F a b ha hb h0 h1 hmeet hhom
  exact clean_disk_gives_embedded_family a b ha hb h0 h1 hmeet d hd hboundary
    hinside haClear hbClear

end RegionalEmbeddedFamily
