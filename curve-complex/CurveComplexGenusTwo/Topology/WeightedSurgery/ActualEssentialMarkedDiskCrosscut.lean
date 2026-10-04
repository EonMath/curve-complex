import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEssentialLoopDiskObstruction
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedBigonObstruction
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskCrosscut

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- An actual essential marked arc, INCLUDING LOOPS, entering a disk with
marked-free INTERIOR produces a genuine embedded crosscut. A boundary endpoint may be marked,
so this construction includes the half-bigon case; closed-disk mark-freeness
is not required. Compact extrema construct the actual parameter subinterval. -/
theorem actual_essential_marked_arc_entering_interior_free_disk_has_crosscut
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : IsEmbedding d)
    (hmarks : Disjoint
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (M.cover.branch : Set S))
    (hin : (a.val.image ∩
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})).Nonempty) :
    ∃ f : C(Interval, S), IsEmbedding f ∧ Set.range f ⊆ a.val.image ∧
      f 0 ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ∧
      f 1 ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ∧
      f '' Set.Ioo (0 : Interval) 1 ⊆
        d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere (by simp only [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3))) 0 (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  letI : ClosedSurface S := {}
  let K : Set S := Set.range d
  let U : Set S := d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
  have hUopen : IsOpen U := LocalSurgery.embedded_surface_disk_interior_isOpen d hd
  have hKclosed : IsClosed K := (isCompact_range d.continuous).isClosed
  have hUK : U ⊆ K := Set.image_subset_range _ _
  let γ : C(Interval, S) := ⟨a.val.map,a.val.continuous⟩
  let realγ := LocalSurgery.realIntervalPath γ
  have hreal (u : Interval) : realγ u.val = γ u := by
    change γ (Set.projIcc 0 1 (by norm_num) u.val) = γ u
    rw [Set.projIcc_of_mem _ u.property]
  have hends : realγ 0 = a.val.map 0 ∧ realγ 1 = a.val.map 1 :=
    ⟨hreal 0,hreal 1⟩
  have hxout0 : a.val.map 0 ∉ U := fun h =>
    disjoint_left.mp hmarks h a.val.start_marked
  have hxout1 : a.val.map 1 ∉ U := fun h =>
    disjoint_left.mp hmarks h a.val.end_marked
  obtain ⟨y,⟨t,ht⟩,hyU⟩ := hin
  have htU : realγ t.val ∈ U := by rw [hreal]; change a.val.map t ∈ U; rw [ht]; exact hyU
  let L := Set.Icc (0 : ℝ) t.val ∩ realγ ⁻¹' Uᶜ
  let R := Set.Icc t.val (1 : ℝ) ∩ realγ ⁻¹' Uᶜ
  have hcomp : IsClosed (realγ ⁻¹' Uᶜ) := hUopen.isClosed_compl.preimage realγ.continuous
  have hLne : L.Nonempty := ⟨0, ⟨le_rfl, t.property.1⟩, by change realγ 0 ∉ U; rw [hends.1]; exact fun h => hxout0 h⟩
  have hRne : R.Nonempty := ⟨1, ⟨t.property.2, le_rfl⟩, by change realγ 1 ∉ U; rw [hends.2]; exact fun h => hxout1 h⟩
  obtain ⟨r, hrmem, hrmax⟩ := (isCompact_Icc.inter_right hcomp).exists_isGreatest hLne
  obtain ⟨s, hsmem, hsmin⟩ := (isCompact_Icc.inter_right hcomp).exists_isLeast hRne
  have hrt : r < t.val := lt_of_le_of_ne hrmem.1.2 (by intro heq; exact hrmem.2 (heq ▸ htU))
  have hts : t.val < s := lt_of_le_of_ne hsmem.1.1 (by intro heq; exact hsmem.2 (heq.symm ▸ htU))
  have hrs : r < s := hrt.trans hts
  have hinside (v : ℝ) (hv : v ∈ Set.Ioo r s) : realγ v ∈ U := by
    by_contra hvout
    by_cases hvt : v ≤ t.val
    · have hm : v ∈ L := ⟨⟨hrmem.1.1.trans hv.1.le, hvt⟩, hvout⟩
      exact (not_lt_of_ge (hrmax hm)) hv.1
    · have hm : v ∈ R := ⟨⟨le_of_not_ge hvt, hv.2.le.trans hsmem.1.2⟩, hvout⟩
      exact (not_lt_of_ge (hsmin hm)) hv.2
  have hclosedPre : IsClosed (realγ ⁻¹' K) := hKclosed.preimage realγ.continuous
  have hIccK : Set.Icc r s ⊆ realγ ⁻¹' K := by
    rw [← closure_Ioo hrs.ne]
    apply hclosedPre.closure_subset_iff.mpr
    exact fun v hv => hUK (hinside v hv)
  have hrK : realγ r ∈ K := hIccK ⟨le_rfl, hrs.le⟩
  have hsK : realγ s ∈ K := hIccK ⟨hrs.le, le_rfl⟩
  have hboundary (v : ℝ) (hvK : realγ v ∈ K) (hvU : realγ v ∉ U) :
      realγ v ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    obtain ⟨u, hu⟩ := hvK
    refine ⟨u, ?_, hu⟩
    have hn : ‖u.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using u.property
    have hnnot : ¬ ‖u.val‖ < 1 := by
      intro h
      exact hvU ⟨u, by change u.val ∈ Metric.ball 0 1; simpa only [Metric.mem_ball, dist_zero_right] using h, hu⟩
    change u.val ∈ Metric.sphere 0 1
    simpa only [Metric.mem_sphere, dist_zero_right] using le_antisymm hn (le_of_not_gt hnnot)
  let affine : Interval → ℝ := fun u => r + (s - r) * u.val
  let f : C(Interval, S) := ⟨realγ ∘ affine, realγ.continuous.comp (by fun_prop)⟩
  have haffine (u : Interval) : affine u ∈ Set.Icc r s := by
    dsimp [affine]
    constructor <;> nlinarith [u.property.1, u.property.2]
  have hfInjective : Function.Injective f := by
    intro u v heq
    let uI : Interval := ⟨affine u, ⟨hrmem.1.1.trans (haffine u).1, (haffine u).2.trans hsmem.1.2⟩⟩
    let vI : Interval := ⟨affine v, ⟨hrmem.1.1.trans (haffine v).1, (haffine v).2.trans hsmem.1.2⟩⟩
    have heq' : γ uI = γ vI := by rw [← hreal uI, ← hreal vI]; exact heq
    have hnoFullLoop (hr0 : r = 0) (hs1 : s = 1)
        (hloop : a.val.map (0 : Interval) = a.val.map (1 : Interval)) : False := by
      apply actual_essential_loop_not_in_interior_free_disk M a hloop d hd hmarks
      rintro z ⟨w,rfl⟩
      have hwK := hIccK (show w.val ∈ Set.Icc r s from by
        rw [hr0,hs1]; exact w.property)
      change realγ w.val ∈ K at hwK
      rwa [hreal w] at hwK
    rcases a.val.injective_except_loop_closure uI vI heq' with hh | hh | hh
    · have hv := congrArg Subtype.val hh
      apply Subtype.ext
      dsimp [uI,vI,affine] at hv
      nlinarith
    · have hu0 : affine u = 0 := congrArg Subtype.val hh.1
      have hv1 : affine v = 1 := congrArg Subtype.val hh.2
      have hr0 : r = 0 := le_antisymm (by linarith [(haffine u).1]) hrmem.1.1
      have hs1 : s = 1 := le_antisymm hsmem.1.2 (by linarith [(haffine v).2])
      have hloop : a.val.map (0 : Interval) = a.val.map (1 : Interval) := by
        change a.val.map uI = a.val.map vI at heq'
        rw [hh.1,hh.2] at heq'
        exact heq'
      exact (hnoFullLoop hr0 hs1 hloop).elim
    · have hu1 : affine u = 1 := congrArg Subtype.val hh.1
      have hv0 : affine v = 0 := congrArg Subtype.val hh.2
      have hr0 : r = 0 := le_antisymm (by linarith [(haffine v).1]) hrmem.1.1
      have hs1 : s = 1 := le_antisymm hsmem.1.2 (by linarith [(haffine u).2])
      have hloop : a.val.map (0 : Interval) = a.val.map (1 : Interval) := by
        change a.val.map uI = a.val.map vI at heq'
        rw [hh.1,hh.2] at heq'
        exact heq'.symm
      exact (hnoFullLoop hr0 hs1 hloop).elim
  refine ⟨f, (f.continuous.isClosedEmbedding hfInjective).isEmbedding, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨u, rfl⟩
    let uI : Interval := ⟨affine u, ⟨hrmem.1.1.trans (haffine u).1, (haffine u).2.trans hsmem.1.2⟩⟩
    exact ⟨uI, (hreal uI).symm⟩
  · change realγ (affine 0) ∈ _
    have h0 : affine 0 = r := by simp [affine]
    rw [h0]
    exact hboundary r hrK hrmem.2
  · change realγ (affine 1) ∈ _
    have h1 : affine 1 = s := by simp [affine]
    rw [h1]
    exact hboundary s hsK hsmem.2
  · rintro y ⟨u, hu, rfl⟩
    apply hinside
    change r < affine u ∧ affine u < s
    have hu0 : 0 < u.val := hu.1
    have hu1 : u.val < 1 := hu.2
    dsimp [affine]
    constructor <;> nlinarith

#print axioms actual_essential_marked_arc_entering_interior_free_disk_has_crosscut
end CurveComplex.HyperellipticModel
