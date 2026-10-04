import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualUnmarkedCornerAxis
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.CornerInteriorSector
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.VerifiedCarrierBridgeComponents
namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies ArcSurgery CurveComplex.LocalSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

theorem actual_unmarked_disk_corner_endpoint_family
    (M : HyperellipticModel E S) {J : Type} [Fintype J]
    (old : J → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (B : ActualMarkedTwoSideDisk M a b)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image))
    (htab : ∀ p ∈ ArcSurgery.crossings M a b, CrossesInDisk M a b p)
    (hcorners : ∀ j p, p ∈ ({B.firstCorner,B.secondCorner} : Set S) →
      p ∉ M.cover.branch → p ∉ (old j).val.image)
    (p : S) (hpmark : p ∉ M.cover.branch)
    (hpcorner : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W)
 :
    ∃ F : OpenPartialHomeomorph S Plane, ∃ L : C(Interval,S),
      p ∈ F.source ∧ F p=0 ∧ F.source ⊆ W ∧
      Disjoint F.source (M.cover.branch : Set S) ∧
      L 0 ∈ range B.secondSide ∧ L 0 ∉ a.val.image ∧
      (∀ j, L 0 ∉ (old j).val.image) ∧
      ∀ t : Interval, 0 < t.val →
        ∃ f : C(Interval,S), IsEmbedding f ∧ f 0=p ∧ f 1=L t ∧
          range f ⊆ F.source ∧ range f \ {p} ⊆ B.openInterior ∧
          range f ∩ a.val.image={p} ∧ range f ∩ b.val.image={p} ∧
          Disjoint (range f) (M.cover.branch : Set S) ∧
          ∀ j, Disjoint (range f) (old j).val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  letI : ClosedSurface S := {}
  obtain ⟨F,ell,hpF,hFp,hFW,hell,hmarks,hOldSource,hBaxis,hAaxis,hRay⟩ :=
    actual_unmarked_disk_corner_selected_axis M old a b B htab hcorners p hpcorner hpmark W hW hpW
  let O : Set (ℝ × ℝ) := {q | Plane.mk q.1 q.2 ∈ F.target}
  have hO : IsOpen O := F.open_target.preimage (by fun_prop)
  have h0O : (0,0) ∈ O := by
    have hz : Plane.mk (0:ℝ) 0=(0:Plane) := by ext i; fin_cases i <;> rfl
    change Plane.mk 0 0 ∈ F.target
    rw [hz,← hFp]
    exact F.map_source hpF
  obtain ⟨β,hβ,hβball⟩ := Metric.isOpen_iff.mp hO (0,0) h0O
  let R := min β ell / 2
  let κ : ℝ := 1
  have hR : 0 < R := half_pos (lt_min hβ hell)
  have hRβ : R < β := by dsimp [R]; linarith [min_le_left β ell]
  have hRell : R < ell := by dsimp [R]; linarith [min_le_right β ell]
  have hκ : 0 < κ := zero_lt_one
  have hCone (z : Plane) (hx : 0 < z 0) (hxr : z 0 < R)
      (hlo : -κ*z 0 < z 1) (hhi : z 1 < κ*z 0) :
      z ∈ F.target ∧ F.symm z ∉ a.val.image ∧
      (∀ j, F.symm z ∉ (old j).val.image) ∧
      (F.symm z ∈ b.val.image ↔ z 1=0) ∧
      (z 1=0 → F.symm z ∈ range B.secondSide) := by
    have hzO : (z 0,z 1) ∈ O := hβball (by
      change dist (z 0,z 1) ((0:ℝ),0)<β
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,max_lt_iff]
      constructor
      · rw [abs_of_pos hx]; exact hxr.trans hRβ
      · apply abs_lt.mpr
        dsimp [κ] at hlo hhi
        constructor <;> linarith)
    have he : Plane.mk (z 0) (z 1)=z := by ext i; fin_cases i <;> rfl
    have hzT : z ∈ F.target := by
      change Plane.mk (z 0) (z 1) ∈ F.target at hzO
      rwa [he] at hzO
    have hzS := F.map_target hzT
    have hFz := F.right_inv hzT
    refine ⟨hzT,?_,?_,?_,?_⟩
    · intro ha
      have hh := (hAaxis _ hzS).mp ha
      rw [hFz] at hh
      linarith
    · intro j hj
      exact Set.disjoint_left.mp (hOldSource j) hzS hj
    · have hh := hBaxis _ hzS
      rwa [hFz] at hh
    · intro hy
      have hz : z=Plane.mk (z 0) 0 := by ext i; fin_cases i <;> simpa using hy
      rw [hz]
      exact (hRay (z 0) ⟨hx.le,(hxr.trans hRell).le⟩).2
  have hclosed : IsClosed (range B.disk) := (isCompact_range B.disk.continuous).isClosed
  have hregular : range B.disk ⊆ closure (interior (range B.disk)) := by
    rw [CurveComplex.actual_embedded_disk_closure_interior B.disk B.disk_embedded]
  have hfront : frontier (range B.disk) = range B.firstSide ∪ range B.secondSide := by
    rw [hclosed.frontier_eq,embedded_surface_disk_interior_eq B.disk B.disk_embedded,← B.boundary_eq]
    ext p
    constructor
    · rintro ⟨⟨x,rfl⟩,hxnot⟩
      refine ⟨x,?_,rfl⟩
      have hxle : dist x.val (0 : Plane) ≤ 1 := x.property
      have hxge : 1 ≤ dist x.val (0 : Plane) := by
        by_contra hn
        exact hxnot ⟨x,lt_of_not_ge hn,rfl⟩
      exact le_antisymm hxle hxge
    · rintro ⟨x,hx,rfl⟩
      refine ⟨⟨x,rfl⟩,?_⟩
      rintro ⟨y,hy,he⟩
      have hxy := B.disk_embedded.injective he
      subst y
      change dist x.val (0 : Plane) < 1 at hy
      change dist x.val (0 : Plane) = 1 at hx
      linarith
  have hFrontier (z : Plane) (hx : 0 < z 0) (hxr : z 0 < R)
      (hlo : -κ*z 0 < z 1) (hhi : z 1 < κ*z 0) :
      F.symm z ∈ frontier (range B.disk) ↔ z 1=0 := by
    obtain ⟨hzT,haFree,hOldFree,hBaxis,hSideAxis⟩ := hCone z hx hxr hlo hhi
    rw [hfront]
    constructor
    · rintro (hfirst|hsecond)
      · exact False.elim (haFree (B.first_on_curve hfirst))
      · exact hBaxis.mp (B.second_on_curve hsecond)
    · intro hz
      exact Or.inr (hSideAxis hz)
  obtain ⟨τ,hτ,hSector⟩ := CurveComplex.actual_chart_cone_interior_sector F (range B.disk)
    hclosed hregular R κ hR hκ
    (fun z hx hxr hlo hhi => (hCone z hx hxr hlo hhi).1) hFrontier
  obtain ⟨L,hL,hL0,hLS,hPaths⟩ := CurveComplex.actual_interior_corner_endpoint_family
    F (range B.disk) p hpF hFp R κ (R/2) τ hR hκ (half_pos hR) (by linarith) hτ
    (fun z hx hxr hlo hhi => (hCone z hx hxr hlo hhi).1) hSector
  have hBase := hCone (Plane.mk (R/2) 0) (by change 0<R/2; linarith)
    (by change R/2<R; linarith)
    (by change -κ*(R/2)<0; nlinarith [mul_pos hκ hR])
    (by change 0<κ*(R/2); positivity)
  refine ⟨F,L,hpF,hFp,hFW,hmarks,?_,?_,?_,?_⟩
  · rw [hL0]
    exact hBase.2.2.2.2 rfl
  · rw [hL0]
    exact hBase.2.1
  · intro j
    rw [hL0]
    exact hBase.2.2.1 j
  · intro t ht
    obtain ⟨f,hf,hf0,hf1,hfS,hfInside,hfCone,hfCoord⟩ := hPaths t ht
    have hInside : range f \ {p} ⊆ B.openInterior := by
      rw [embedded_surface_disk_interior_eq B.disk B.disk_embedded] at hfInside
      exact hfInside
    have hpA : p ∈ a.val.image := by
      rcases hpcorner with he|he
      · exact B.first_on_curve ⟨0,B.first_zero.trans he.symm⟩
      · exact B.first_on_curve ⟨1,B.first_one.trans he.symm⟩
    have hpB : p ∈ b.val.image := by
      rcases hpcorner with he|he
      · exact B.second_on_curve ⟨0,B.second_zero.trans he.symm⟩
      · exact B.second_on_curve ⟨1,B.second_one.trans he.symm⟩
    have hIntersection (A : Set S) (hpA : p ∈ A) (hAS : A ⊆ a.val.image ∪ b.val.image) :
        range f ∩ A={p} := by
      ext x
      constructor
      · rintro ⟨hx,hA⟩
        apply Set.mem_singleton_iff.mpr
        by_contra hne
        exact Set.disjoint_left.mp hempty (hInside ⟨hx,by simpa using hne⟩) (hAS hA)
      · intro hx
        have he := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨⟨0,hf0⟩,hpA⟩
    exact ⟨f,hf,hf0,hf1,hfS,hInside,
      hIntersection _ hpA Set.subset_union_left,
      hIntersection _ hpB Set.subset_union_right,
      hmarks.mono_left hfS,fun j => (hOldSource j).mono_left hfS⟩
end CurveComplex.HyperellipticModel
