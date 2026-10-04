import ClassificationSchoenflies.PolyhedralDiskNeighborhoods
import Mathlib.Analysis.Normed.Module.Connected

open Set Metric
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace ClassificationSchoenflies

/-- A finite connected escape barrier can be built using compact paths in
the connected open complement of a compact planar set. -/
theorem exists_finite_path_barrier
    {A : Set Plane} (hA : IsCompact A) (hComp : IsConnected Aᶜ)
    (F : Finset Plane) (hF : ∀ x ∈ F, x ∉ A) :
    ∃ R : ℝ, ∃ w : Plane,
      ∃ P : (i : {x : Plane // x ∈ F}) → Path i.val w,
      ∃ U : Set Plane,
      0 < R ∧ A ⊆ ball 0 R ∧ (F : Set Plane) ⊆ ball 0 R ∧
      w ∉ closedBall 0 R ∧
      (∀ i, range (P i) ⊆ Aᶜ) ∧
      (F.Nonempty → IsConnected (⋃ i, range (P i))) ∧
      IsOpen U ∧ A ⊆ U ∧ IsCompact (closure U) ∧
        closure U ⊆ ball 0 R ∧
        closure U ⊆ (⋃ i, range (P i))ᶜ := by
  classical
  obtain ⟨R, hR, hball⟩ :=
    (hA.isBounded.union F.finite_toSet.isBounded).subset_ball_lt 0 (0 : Plane)
  have hASealed : A ⊆ ball 0 R := (Set.subset_union_left).trans hball
  have hFSealed : (F : Set Plane) ⊆ ball 0 R :=
    (Set.subset_union_right).trans hball
  obtain ⟨w, hwNorm⟩ := NormedSpace.exists_lt_norm ℝ Plane R
  have hwClosed : w ∉ closedBall 0 R := by
    simpa [Metric.mem_closedBall] using not_le.mpr hwNorm
  have hwA : w ∉ A := by
    intro hw
    exact hwClosed (ball_subset_closedBall (hASealed hw))
  have hwF : w ∉ F := by
    intro hw
    exact hwClosed (ball_subset_closedBall (hFSealed hw))
  have hPathConnected : IsPathConnected Aᶜ :=
    hA.isClosed.isOpen_compl.isConnected_iff_isPathConnected.mp hComp
  let P : (i : {x : Plane // x ∈ F}) → Path i.val w := fun i =>
    (hPathConnected.joinedIn i.val (hF i.val i.property) w hwA).somePath
  have hP (i : {x : Plane // x ∈ F}) : range (P i) ⊆ Aᶜ := by
    rw [range_subset_iff]
    exact (hPathConnected.joinedIn i.val (hF i.val i.property) w hwA).somePath_mem
  let B : Set Plane := ⋃ i, range (P i)
  have hBconnected : F.Nonempty → IsConnected B := by
    intro hFn
    obtain ⟨x, hx⟩ := hFn
    let i : {x : Plane // x ∈ F} := ⟨x, hx⟩
    have hcommon : (⋂ j, range (P j)).Nonempty := by
      refine ⟨w, Set.mem_iInter.mpr ?_⟩
      intro j
      exact Path.target_mem_range (P j)
    have hpre : IsPreconnected B :=
      isPreconnected_iUnion hcommon (fun j => (isConnected_range (P j).continuous).isPreconnected)
    exact ⟨⟨w, Set.mem_iUnion.mpr ⟨i, Path.target_mem_range (P i)⟩⟩, hpre⟩
  have hBclosed : IsClosed B := by
    exact isClosed_iUnion_of_finite (fun i =>
      (isCompact_range (P i).continuous).isClosed)
  have hAB : A ⊆ Bᶜ := by
    intro z hz hzB
    rcases Set.mem_iUnion.mp hzB with ⟨i, hi⟩
    exact hP i hi hz
  obtain ⟨U, hUopen, hAU, hClosure, hCompact⟩ :=
    exists_open_between_and_isCompact_closure hA
      (isOpen_ball.inter hBclosed.isOpen_compl)
      (Set.subset_inter hASealed hAB)
  exact ⟨R, w, P, U, hR, hASealed, hFSealed, hwClosed,
    hP, hBconnected, hUopen, hAU, hCompact,
    (fun _ hx => (hClosure hx).1), (fun _ hx => (hClosure hx).2)⟩

/-- The exterior of any closed ball containing a Jordan carrier lies in the
unique unbounded complementary region of that carrier. -/
theorem JordanCircle.compl_closedBall_subset_outside
    (J : JordanCircle) {R : ℝ} (hR : 0 ≤ R)
    (hCarrier : J.carrier ⊆ ball 0 R) :
    (closedBall (0 : Plane) R)ᶜ ⊆ J.outside := by
  let E : Set Plane := (closedBall (0 : Plane) R)ᶜ
  have hEconnected : IsConnected E := by
    convert ClassificationJordanCurve.isConnected_compl_closedBall hR using 1
    ext z
    simp [E, Metric.mem_closedBall, dist_zero_right]
  have hESub : E ⊆ J.carrierᶜ := by
    intro z hz hzC
    exact hz (ball_subset_closedBall (hCarrier hzC))
  have hMeet : (E ∩ J.outside).Nonempty := by
    by_contra h
    have hJsub : J.outside ⊆ closedBall (0 : Plane) R := by
      intro z hzJ
      by_contra hzE
      exact h ⟨z, hzE, hzJ⟩
    exact J.outside_unbounded (isBounded_closedBall.subset hJsub)
  obtain ⟨y, hyE, hyOut⟩ := hMeet
  have hComponent : E ⊆ connectedComponentIn J.carrierᶜ y :=
    hEconnected.isPreconnected.subset_connectedComponentIn hyE hESub
  have hEq : connectedComponentIn J.carrierᶜ y = J.outside := by
    change connectedComponentIn J.carrierᶜ y =
      connectedComponentIn J.carrierᶜ J.outsidePoint
    exact (connectedComponentIn_eq hyOut).symm
  rw [hEq] at hComponent
  exact hComponent

/-- The finite mesh theorem produces a polygonal disk around any compact
connected planar set with connected complement, while excluding prescribed
finite marks. The connected escape barrier forces the marks into the exterior
region of the selected outer boundary. -/
theorem exists_polygonalDisk_avoiding_finite
    {A : Set Plane} (hAcompact : IsCompact A) (hAconnected : IsConnected A)
    (hComp : IsConnected Aᶜ)
    (F : Finset Plane) (hF : ∀ x ∈ F, x ∉ A) :
    ∃ Q : PolygonalCircle,
      A ⊆ interior Q.closedRegion ∧
      Disjoint Q.closedRegion (F : Set Plane) := by
  classical
  obtain ⟨R, w, P, U, hR, hABall, hFBall, hwClosed,
    hPavoids, hBconnected, hUopen, hAU, hUcompact, hUBall, hUBarrier⟩ :=
    exists_finite_path_barrier hAcompact hComp F hF
  let N : JordanCircle.FinitePolyhedralNeighborhood A U :=
    Classical.choice (JordanCircle.exists_finitePolyhedralNeighborhood
      hAcompact hUopen hAU)
  obtain ⟨Q, _hFrontier, hQambient, hCoreInside, _hFrame⟩ :=
    N.exists_outerBoundaryPolygonalCircle_of_connected hAconnected
  have hAinside : A ⊆ Q.interiorRegion :=
    (N.core_subset_coreComponent hAconnected).trans hCoreInside
  have hQBall : Q.carrier ⊆ ball 0 R := by
    intro z hz
    exact hUBall (subset_closure (hQambient hz))
  let J : JordanCircle := Q.toJordanCircle
  have hCarrier : J.carrier = Q.carrier := Q.carrier_toJordanCircle
  have hwOutside : w ∈ J.outside := by
    apply J.compl_closedBall_subset_outside hR.le
    · simpa only [hCarrier] using hQBall
    · exact hwClosed
  let B : Set Plane := ⋃ i, range (P i)
  have hBQ : Disjoint B J.carrier := by
    rw [Set.disjoint_left]
    intro z hzB hzCarrier
    have hzU : z ∈ U := hQambient (hCarrier ▸ hzCarrier)
    exact hUBarrier (subset_closure hzU) hzB
  have hAvoid : Disjoint Q.closedRegion (F : Set Plane) := by
    rw [Set.disjoint_left]
    intro x hxRegion hxF
    have hFn : F.Nonempty := ⟨x, hxF⟩
    have hwB : w ∈ B := by
      exact Set.mem_iUnion.mpr ⟨⟨x, hxF⟩, Path.target_mem_range (P ⟨x, hxF⟩)⟩
    have hBcomponent : B ⊆ connectedComponentIn J.carrierᶜ w :=
      (hBconnected hFn).isPreconnected.subset_connectedComponentIn hwB
        (fun z hz => Set.disjoint_left.mp hBQ hz)
    have hxB : x ∈ B :=
      Set.mem_iUnion.mpr ⟨⟨x, hxF⟩, Path.source_mem_range (P ⟨x, hxF⟩)⟩
    have hComponentEq : connectedComponentIn J.carrierᶜ w = J.outside := by
      change connectedComponentIn J.carrierᶜ w =
        connectedComponentIn J.carrierᶜ J.outsidePoint
      exact (connectedComponentIn_eq hwOutside).symm
    have hxOutside : x ∈ J.outside := hComponentEq ▸ hBcomponent hxB
    rw [Q.closedRegion_eq_union] at hxRegion
    rcases hxRegion with hxInside | hxCarrier
    · have hxJinside : x ∈ J.inside := by
        change x ∈ Q.toJordanCircle.inside
        rw [Q.inside_toJordanCircle]
        exact hxInside
      exact Set.disjoint_left.mp J.inside_disjoint_outside hxJinside hxOutside
    · exact J.outside_subset_compl hxOutside (hCarrier ▸ hxCarrier)
  refine ⟨Q, ?_, hAvoid⟩
  rw [Q.interior_closedRegion]
  exact hAinside

end ClassificationSchoenflies
