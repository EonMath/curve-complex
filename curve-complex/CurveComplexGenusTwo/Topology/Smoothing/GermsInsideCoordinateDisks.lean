import CurveComplexGenusTwo.Topology.Smoothing.EndpointCoordinateDisks
import CurveComplexGenusTwo.Topology.Smoothing.UniformActualGerms

open Set Metric
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A genuine open interior for the compact coordinate disk. -/
theorem coordinate_disk_interior
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (p : S) (R : ℝ) (hR : 0 < R)
    (htarget : closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).target) :
    IsOpen ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
      ball ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p) R) ∧
    p ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
      ball ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p) R := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) p
  refine ⟨e.isOpen_image_symm_of_subset_target isOpen_ball
    (fun z hz => htarget (ball_subset_closedBall hz)), ?_⟩
  exact ⟨e p, mem_ball_self hR, e.left_inv (mem_chart_source _ p)⟩

/-- One cut simultaneously puts every actual endpoint germ inside its chosen
compact coordinate disk at each of the six marked vertices. -/
theorem uniform_actual_germs_in_coordinate_disks
    (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
    (ι : Type) [Fintype ι] (a : ι → EssentialMarkedArc M)
    (R : {p : S // p ∈ M.cover.branch} → ℝ)
    (hR : ∀ p, 0 < R p)
    (htarget : letI := C.charts; ∀ p,
      closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val) p.val) (R p) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) p.val).target) :
    letI := C.charts
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      ∀ p : {p : S // p ∈ M.cover.branch},
        (∀ i, (a i).val.map ⟨0, by norm_num⟩ = p.val →
          ∀ t : Interval, t.val ≤ r → (a i).val.map t ∈
            (chartAt (EuclideanSpace ℝ (Fin 2)) p.val).symm ''
              closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val) p.val) (R p)) ∧
        (∀ i, (a i).val.map ⟨1, by norm_num⟩ = p.val →
          ∀ t : Interval, 1 - r ≤ t.val → (a i).val.map t ∈
            (chartAt (EuclideanSpace ℝ (Fin 2)) p.val).symm ''
              closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val) p.val) (R p)) := by
  classical
  letI := C.charts
  let P := {p : S // p ∈ M.cover.branch}
  have hex (p : P) := coordinate_disk_interior p.val (R p) (hR p) (htarget p)
  have hcuts (p : P) := uniform_actual_endpoint_germs M ι a p.val _ (hex p).1 (hex p).2
  choose ρ hρ hρhalf hstart hend using hcuts
  have hP : (Finset.univ : Finset P).Nonempty := by
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [M.cover.branch_card]; norm_num : 0 < M.cover.branch.card)
    exact ⟨⟨p, hp⟩, Finset.mem_univ _⟩
  let r := (Finset.univ : Finset P).inf' hP ρ
  have hr : 0 < r := (Finset.lt_inf'_iff hP).mpr (fun p _ => hρ p)
  have hrp (p : P) : r ≤ ρ p := Finset.inf'_le _ (Finset.mem_univ p)
  obtain ⟨p0, hp0⟩ := hP
  refine ⟨r, hr, lt_of_le_of_lt (hrp p0) (hρhalf p0), ?_⟩
  intro p
  constructor
  · intro i hi t ht
    have hmem := hstart p i hi t (le_trans ht (hrp p))
    exact image_mono ball_subset_closedBall hmem
  · intro i hi t ht
    have hmem := hend p i hi t (by linarith [hrp p])
    exact image_mono ball_subset_closedBall hmem

#print axioms coordinate_disk_interior
#print axioms uniform_actual_germs_in_coordinate_disks
end CurveComplex.HyperellipticModel
