import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedCornerCone
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.CornerInteriorSector
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.VerifiedCarrierBridgeComponents
namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies ArcSurgery CurveComplex.LocalSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

theorem strengthened_actual_marked_disk_corner_endpoint_family
    (M : HyperellipticModel E S) {J : Type} [Fintype J]
    (old : J → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (hOld : ∀ i j, i ≠ j → (ArcSurgery.crossings M (old i) (old j)).Finite)
    (hab : (ArcSurgery.crossings M a b).Finite)
    (ha : ∀ j, (ArcSurgery.crossings M a (old j)).Finite)
    (hb : ∀ j, (ArcSurgery.crossings M b (old j)).Finite)
    (B : ActualMarkedTwoSideDisk M a b)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image))
    (p : S) (hp : p ∈ M.cover.branch)
    (hpcorner : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W)
    (terminal : Bool) (hend : (if terminal then b.val.map 1 else b.val.map 0)=p)
    (s : ℝ) (hs : 0 < s) (hshalf : s < 1/2)
    (hSideGerm : range (b.val.map ∘ endpointGermParameter terminal s hs (by linarith)) ⊆
      range B.secondSide) :
    ∃ F : OpenPartialHomeomorph S Plane, ∃ L : C(Interval,S),
      p ∈ F.source ∧ F p=0 ∧ F.source ⊆ W ∧
      F.source ∩ (M.cover.branch : Set S)={p} ∧
      L 0 ∈ F.source ∧ L 0 ∈ range B.secondSide ∧ L 0 ∉ a.val.image ∧
      (∀ j, L 0 ∉ (old j).val.image) ∧
      ∀ t : Interval, 0 < t.val →
        ∃ f : C(Interval,S), IsEmbedding f ∧ f 0=p ∧ f 1=L t ∧
          range f ⊆ F.source ∧ range f \ {p} ⊆ B.openInterior ∧
          range f ∩ a.val.image={p} ∧ range f ∩ b.val.image={p} ∧
          range f ∩ (M.cover.branch : Set S)={p} ∧
          ∀ j, Disjoint (range f) (arcInterior M (old j)) := by
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
  obtain ⟨F,hpF,hFp,hFW,hmarks,R,κ,hR,hR1,hκ,hκ1,hCone⟩ :=
    actual_marked_corner_cone_from_selected_side_germ M old a b hOld hab ha hb B
      p hp W hW hpW terminal hend s hs hshalf hSideGerm
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
  refine ⟨F,L,hpF,hFp,hFW,hmarks,hLS 0,?_,?_,?_,?_⟩
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
      cases terminal
      · exact ⟨0,hend⟩
      · exact ⟨1,hend⟩
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
    refine ⟨f,hf,hf0,hf1,hfS,hInside,
      hIntersection _ hpA Set.subset_union_left,
      hIntersection _ hpB Set.subset_union_right,?_,?_⟩
    · ext x
      constructor
      · rintro ⟨hx,hm⟩
        exact hmarks ▸ ⟨hfS hx,hm⟩
      · intro hx
        have he := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨⟨0,hf0⟩,hp⟩
    · intro j
      apply Set.disjoint_left.mpr
      rintro x ⟨u,rfl⟩ hOldu
      by_cases hu : u=0
      · subst u
        rw [hf0] at hOldu
        exact hOldu.2 hp
      · have hup : 0 < u.val := lt_of_le_of_ne u.property.1
          (by intro he; exact hu (Subtype.ext he.symm))
        have huC := hfCone u hup
        have hData := hCone (F (f u)) huC.1 huC.2.1 huC.2.2.1 huC.2.2.2
        have hFree := hData.2.2.1 j
        rw [F.left_inv (hfS (Set.mem_range_self u))] at hFree
        exact hFree hOldu.1
end CurveComplex.HyperellipticModel
