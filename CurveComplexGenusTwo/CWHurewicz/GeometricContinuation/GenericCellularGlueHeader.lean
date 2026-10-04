import CurveComplexGenusTwo.CWHurewicz.CWCellularHomotopyGlue
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
open Topology Metric
open scoped Topology.Homotopy
variable {P : Type} [TopologicalSpace P] [T2Space P]
  [Topology.CWComplex (Set.univ : Set P)]
variable {X : Type} [TopologicalSpace X]
theorem compatible_cell_cylinders_extend_homotopy
    (f : C(P, X)) (x₀ : X) (n : ℕ)
    (Hn : ContinuousMap.Homotopy
      ((f).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow P n), P)))
      ((ContinuousMap.const P x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow P n), P))))
    (G : ∀ _i : Topology.CWComplex.cell (Set.univ : Set P) n,
      C(unitInterval × CellDisk n, X))
    (hboundary : ∀ i (b : CellSphere n) (t : unitInterval),
      G i (t, ⟨b.val, sphere_subset_closedBall b.property⟩) =
        Hn (t, attaching n i b))
    (hzero : ∀ i (w : CellDisk n),
      G i (0, w) = f (characteristicToStep n i w).val)
    (hone : ∀ i (w : CellDisk n), G i (1, w) = x₀) :
    ∃ Hnext : ContinuousMap.Homotopy
      ((f).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow P (n + 1)), P)))
      ((ContinuousMap.const P x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow P (n + 1)), P))),
      ∀ (t : unitInterval) (z : ↥(skeletonBelow P n)),
        Hnext (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z) := by
  have hcover (z : ↥(skeletonBelow P (n + 1))) :
      (∃ y : ↥(skeletonBelow P n), skeletonInclusion (Nat.le_succ n) y = z) ∨
      (∃ (i : Topology.CWComplex.cell (Set.univ : Set P) n)
        (w : CellDisk n), characteristicToStep n i w = z) := by
    rcases Set.mem_iUnion.mp z.property with ⟨m, hm⟩
    rcases Set.mem_iUnion.mp hm with ⟨hmn, hm⟩
    rcases Set.mem_iUnion.mp hm with ⟨i, hi⟩
    by_cases hmn' : m < n
    · left
      refine ⟨⟨z.val, Set.mem_iUnion.mpr ⟨m,
        Set.mem_iUnion.mpr ⟨hmn', Set.mem_iUnion.mpr ⟨i, hi⟩⟩⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
    · right
      have hmeq : m = n := by omega
      subst m
      rcases hi with ⟨w, hw, heq⟩
      refine ⟨i, ⟨w, hw⟩, ?_⟩
      apply Subtype.ext
      exact heq
  let F : C(↥(skeletonBelow P n), C(unitInterval, X)) :=
    (⟨fun p : ↥(skeletonBelow P n) × unitInterval => Hn (p.2, p.1),
      Hn.continuous.comp continuous_swap⟩ :
      C(↥(skeletonBelow P n) × unitInterval, X)).curry
  let D : ∀ i : Topology.CWComplex.cell (Set.univ : Set P) n,
      C(CellDisk n, C(unitInterval, X)) := fun i =>
    (⟨fun p : CellDisk n × unitInterval => G i (p.2, p.1),
      (G i).continuous.comp continuous_swap⟩ :
      C(CellDisk n × unitInterval, X)).curry
  have hcompat : ∀ i (b : CellSphere n),
      F (attaching n i b) =
        D i ⟨b.val, sphere_subset_closedBall b.property⟩ := by
    intro i b
    apply ContinuousMap.ext
    intro t
    exact (hboundary i b t).symm
  obtain ⟨h, ⟨hold, hcell⟩, _⟩ :=
    cwStepUniversal_of_t2 n F D hcompat
  let K : C(unitInterval × ↥(skeletonBelow P (n + 1)), X) :=
    ⟨fun p => h p.2 p.1,
      (ContinuousMap.continuous_uncurry_of_continuous h).comp continuous_swap⟩
  have Kold (t : unitInterval) (z : ↥(skeletonBelow P n)) :
      K (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z) := by
    change (h (skeletonInclusion (Nat.le_succ n) z)) t = Hn (t, z)
    simpa [F] using congrFun (congrArg DFunLike.coe (hold z)) t
  have Kcell (t : unitInterval)
      (i : Topology.CWComplex.cell (Set.univ : Set P) n) (w : CellDisk n) :
      K (t, characteristicToStep n i w) = G i (t, w) := by
    change (h (characteristicToStep n i w)) t = G i (t, w)
    simpa [D] using congrFun (congrArg DFunLike.coe (hcell i w)) t
  have Kzero (z : ↥(skeletonBelow P (n + 1))) : K (0, z) = f z.val := by
    rcases hcover z with ⟨y, rfl⟩ | ⟨i, w, rfl⟩
    · rw [Kold]
      exact Hn.apply_zero y
    · rw [Kcell]
      exact hzero i w
  have Kone (z : ↥(skeletonBelow P (n + 1))) : K (1, z) = x₀ := by
    rcases hcover z with ⟨y, rfl⟩ | ⟨i, w, rfl⟩
    · rw [Kold]
      exact Hn.apply_one y
    · rw [Kcell]
      exact hone i w
  exact ⟨⟨K, Kzero, Kone⟩, Kold⟩


end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
