import CurveComplexGenusTwo.Topology.Smoothing.CompatibleEndpointNeighborhoods

open Set Metric
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A compact disk in a prescribed smooth chart lies inside any prescribed
open neighborhood of its center. The chosen topology/atlas is unchanged. -/
theorem coordinate_disk_inside
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (p : S) (U : Set S) (hU : IsOpen U) (hpU : p ∈ U)
    (hsource : U ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    ∃ R : ℝ, 0 < R ∧
      closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).target ∧
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
        closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p) R ⊆ U ∧
      IsCompact ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
        closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p) R) := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) p
  have hImageOpen : IsOpen (e '' U) := e.isOpen_image_of_subset_source hU hsource
  have hpImage : e p ∈ e '' U := ⟨p, hpU, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hImageOpen.mem_nhds hpImage)
  have hclosed : closedBall (e p) (ε / 2) ⊆ e '' U := by
    intro z hz
    apply hball
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  have htarget : closedBall (e p) (ε / 2) ⊆ e.target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hclosed hz
    exact e.map_source (hsource hx)
  refine ⟨ε / 2, by positivity, htarget, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hclosed hz
    change e.symm (e y) ∈ U
    rw [e.left_inv (hsource hy)]
    exact hy
  · exact (isCompact_closedBall (e p) (ε / 2)).image_of_continuousOn (e.symm.continuousOn.mono htarget)

/-- Concrete compact coordinate-disk supports for all actual marked vertices,
pairwise disjoint and avoiding the central/nonincident arc portions. -/
theorem compatible_actual_endpoint_coordinate_disks
    (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
    (ι : Type) [Fintype ι] (a : ι → EssentialMarkedArc M) :
    letI := C.charts
    ∃ R : {p : S // p ∈ M.cover.branch} → ℝ,
      (∀ p, 0 < R p ∧
        closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val) p.val) (R p) ⊆
          (chartAt (EuclideanSpace ℝ (Fin 2)) p.val).target) ∧
      (∀ p, IsCompact ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val).symm ''
        closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val) p.val) (R p))) ∧
      (∀ p q, p ≠ q →
        Disjoint ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val).symm ''
          closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val) p.val) (R p))
          ((chartAt (EuclideanSpace ℝ (Fin 2)) q.val).symm ''
          closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) q.val) q.val) (R q))) ∧
      (∀ p i t, (1 / 4 : ℝ) ≤ (t : Interval).val → t.val ≤ 3 / 4 →
        (a i).val.map t ∉ (chartAt (EuclideanSpace ℝ (Fin 2)) p.val).symm ''
          closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val) p.val) (R p)) ∧
      ∀ p i, (a i).val.map ⟨0, by norm_num⟩ ≠ p.val →
        (a i).val.map ⟨1, by norm_num⟩ ≠ p.val →
        Disjoint (a i).val.image ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val).symm ''
          closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val) p.val) (R p)) := by
  classical
  letI := C.charts
  obtain ⟨U, hU, hdis, hcentral, hnoninc⟩ := compatible_actual_endpoint_neighborhoods M C ι a
  have hdisks (p : {p : S // p ∈ M.cover.branch}) :=
    coordinate_disk_inside p.val (U p) (hU p).1 (hU p).2.1 (hU p).2.2
  choose R hR htarget hsub hcompact using hdisks
  refine ⟨R, fun p => ⟨hR p, htarget p⟩, hcompact, ?_, ?_, ?_⟩
  · intro p q hpq
    exact (hdis p q hpq).mono (hsub p) (hsub q)
  · intro p i t ht0 ht1 hx
    exact hcentral p i t ht0 ht1 (hsub p hx)
  · intro p i hi0 hi1
    exact (hnoninc p i hi0 hi1).mono_right (hsub p)

#print axioms coordinate_disk_inside
#print axioms compatible_actual_endpoint_coordinate_disks
end CurveComplex.HyperellipticModel
