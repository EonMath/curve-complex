import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualPlanarArcHeaders
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import ClassificationSchoenflies.PlanarDiskProducer
import ClassificationSchoenflies.TopologicalDiskBoundaryExtension
import CurveComplexGenusTwo.Dictionary.JordanEssentiality
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualMarkedSlitDiscHeaders
import CurveComplexGenusTwo.Topology.ArcCounts.ActualNumericDegree
import CurveComplexGenusTwo.Topology.ArcCounts.ActualLowDegreeAssembly
import CurveComplexGenusTwo.Filtration.Geometry.MarkedArcPrimitives
import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions
open Set Metric
open LeanEval.Topology.ClassificationOfSurfaces.Moise
namespace ClassificationSchoenflies
/-- The actual enclosure construction also avoids a compact connected
barrier, using one genuine escape path rather than finitely many mark paths. -/
theorem exists_polygonalDisk_avoiding_compact_connected
    {A B : Set Schoenflies.Plane} (hAcompact : IsCompact A) (hAconnected : IsConnected A)
    (hComp : IsConnected Aᶜ) (hBcompact : IsCompact B)
    (hBconnected : IsConnected B) (hAB : Disjoint A B) :
    ∃ Q : PolygonalCircle, A ⊆ interior Q.closedRegion ∧ Disjoint Q.closedRegion B := by
  classical
  obtain ⟨R,hR,hball⟩ := (hAcompact.isBounded.union hBcompact.isBounded).subset_ball_lt 0 (0 : Schoenflies.Plane)
  have hABall : A ⊆ ball 0 R := Set.subset_union_left.trans hball
  obtain ⟨w,hwNorm⟩ := NormedSpace.exists_lt_norm ℝ Schoenflies.Plane R
  have hwClosed : w ∉ closedBall 0 R := by
    simpa [Metric.mem_closedBall] using not_le.mpr hwNorm
  have hwA : w ∉ A := fun h => hwClosed (ball_subset_closedBall (hABall h))
  obtain ⟨b,hb⟩ := hBconnected.nonempty
  have hbA : b ∉ A := fun h => Set.disjoint_left.mp hAB h hb
  have hPath : IsPathConnected Aᶜ :=
    hAcompact.isClosed.isOpen_compl.isConnected_iff_isPathConnected.mp hComp
  let P : Path b w := (hPath.joinedIn b hbA w hwA).somePath
  have hP : range P ⊆ Aᶜ := by
    rw [range_subset_iff]
    exact (hPath.joinedIn b hbA w hwA).somePath_mem
  let K := B ∪ range P
  have hKconn : IsConnected K := hBconnected.union ⟨b,hb,Path.source_mem_range P⟩
    (isConnected_range P.continuous)
  have hKcompact : IsCompact K := hBcompact.union (isCompact_range P.continuous)
  have hAK : A ⊆ Kᶜ := by
    intro x hx h
    rcases h with h | h
    · exact Set.disjoint_left.mp hAB hx h
    · exact hP h hx
  obtain ⟨U,hUopen,hAU,hClosure,hCompact⟩ := exists_open_between_and_isCompact_closure
    hAcompact (isOpen_ball.inter hKcompact.isClosed.isOpen_compl) (Set.subset_inter hABall hAK)
  let N : JordanCircle.FinitePolyhedralNeighborhood A U :=
    Classical.choice (JordanCircle.exists_finitePolyhedralNeighborhood hAcompact hUopen hAU)
  obtain ⟨Q,_hFrontier,hQambient,hCoreInside,_hFrame⟩ := N.exists_outerBoundaryPolygonalCircle_of_connected hAconnected
  have hAinside : A ⊆ Q.interiorRegion := (N.core_subset_coreComponent hAconnected).trans hCoreInside
  have hQBall : Q.carrier ⊆ ball 0 R := fun z hz => (hClosure (subset_closure (hQambient hz))).1
  let J : JordanCircle := Q.toJordanCircle
  have hCarrier : J.carrier = Q.carrier := Q.carrier_toJordanCircle
  have hwOutside : w ∈ J.outside := by
    apply J.compl_closedBall_subset_outside hR.le
    · simpa only [hCarrier] using hQBall
    · exact hwClosed
  have hKQ : Disjoint K J.carrier := by
    rw [Set.disjoint_left]
    intro z hzK hzQ
    exact (hClosure (subset_closure (hQambient (hCarrier ▸ hzQ)))).2 hzK
  have hwK : w ∈ K := Or.inr (Path.target_mem_range P)
  have hKcomponent : K ⊆ connectedComponentIn J.carrierᶜ w :=
    hKconn.isPreconnected.subset_connectedComponentIn hwK (fun z hz => Set.disjoint_left.mp hKQ hz)
  have heq : connectedComponentIn J.carrierᶜ w = J.outside := by
    change connectedComponentIn J.carrierᶜ w = connectedComponentIn J.carrierᶜ J.outsidePoint
    exact (connectedComponentIn_eq hwOutside).symm
  have hAvoid : Disjoint Q.closedRegion B := by
    rw [Set.disjoint_left]
    intro x hxRegion hxB
    have hxOutside : x ∈ J.outside := heq ▸ hKcomponent (Or.inl hxB)
    rw [Q.closedRegion_eq_union] at hxRegion
    rcases hxRegion with hxInside | hxCarrier
    · have hxJinside : x ∈ J.inside := by
        change x ∈ Q.toJordanCircle.inside
        rw [Q.inside_toJordanCircle]
        exact hxInside
      exact Set.disjoint_left.mp J.inside_disjoint_outside hxJinside hxOutside
    · exact J.outside_subset_compl hxOutside (hCarrier ▸ hxCarrier)
  refine ⟨Q,?_,hAvoid⟩
  rw [Q.interior_closedRegion]
  exact hAinside
/-- Removing an actual internal nonloop arc from an actual open disc keeps
that disc connected. The plane chart is literal, not a connectivity certificate. -/
theorem open_disc_internal_arc_connected
    {S : Type} [TopologicalSpace S] (U : Set S) (e : Schoenflies.Plane ≃ₜ U)
    (a : unitInterval → S) (ha : Continuous a) (hai : Function.Injective a)
    (hin : Set.range a ⊆ U) : IsConnected (U \ Set.range a) := by
  let b : unitInterval → U := fun t => ⟨a t, hin (Set.mem_range_self t)⟩
  have hb : Continuous b := ha.subtype_mk _
  let g : unitInterval → Schoenflies.Plane := e.symm ∘ b
  have hg : Continuous g := e.symm.continuous.comp hb
  have hgi : Function.Injective g := by
    intro t u h
    apply hai
    exact congrArg Subtype.val (e.symm.injective h)
  let f : ℝ → Schoenflies.Plane := g ∘ Set.projIcc 0 1 zero_le_one
  have hf : Continuous f := hg.comp continuous_projIcc
  have hfi : Set.InjOn f (Set.Icc 0 1) := by
    intro t ht u hu h
    have he := hgi h
    simpa [f, Set.projIcc_of_mem, ht, hu] using congrArg Subtype.val he
  have hA : Schoenflies.IsArc (Set.range g) := by
    refine ⟨f,hf.continuousOn,hfi,?_⟩
    ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨_,rfl⟩
    · rintro ⟨t,rfl⟩
      refine ⟨t,t.property,?_⟩
      simp [f,Set.projIcc_of_mem]
  have hconn := Schoenflies.arc_complement hA
  let F : Schoenflies.Plane → S := fun x => (e x).val
  have hF : Continuous F := continuous_subtype_val.comp e.continuous
  have hEq : F '' (Set.range g)ᶜ = U \ Set.range a := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨(e y).property,?_⟩
      rintro ⟨t,ht⟩
      apply hy
      refine ⟨t,?_⟩
      apply e.injective
      change e (e.symm (b t)) = e y
      rw [e.apply_symm_apply]
      exact Subtype.ext ht
    · rintro ⟨hx,hxa⟩
      refine ⟨e.symm ⟨x,hx⟩,?_,?_⟩
      · rintro ⟨t,ht⟩
        apply hxa
        refine ⟨t,?_⟩
        exact congrArg Subtype.val (e.symm.injective ht)
      · exact congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
  rw [← hEq]
  exact hconn.image F hF.continuousOn


theorem polygonal_disk_diff_internal_arc_connected
    (Q : PolygonalCircle) {a : unitInterval → Schoenflies.Plane}
    (ha : Continuous a) (hai : Function.Injective a)
    (hin : range a ⊆ interior Q.closedRegion) :
    IsConnected (Q.closedRegion \ range a) := by
  obtain ⟨H,hH,_⟩ := PolygonalCircle.exists_diskStraightening Q
  have hi : H '' interior Q.closedRegion = ball (0 : Schoenflies.Plane) 1 := by
    rw [H.image_interior,hH,interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
  let f : interior Q.closedRegion ≃ₜ ball (0 : Schoenflies.Plane) 1 :=
    (H.image _).trans (Homeomorph.setCongr hi)
  let e : Schoenflies.Plane ≃ₜ interior Q.closedRegion := Homeomorph.unitBall.trans f.symm
  have hc : IsConnected (interior Q.closedRegion \ range a) :=
    open_disc_internal_arc_connected _ e a ha hai hin
  have hclosure : closure (interior Q.closedRegion) = Q.closedRegion := by
    apply H.injective.image_injective
    rw [H.image_closure,hi,closure_ball _ (by norm_num : (1 : ℝ) ≠ 0),hH]
  have hcl : Q.closedRegion \ range a ⊆ closure (interior Q.closedRegion \ range a) := by
    intro x hx
    have hh := (isCompact_range ha).isClosed.isOpen_compl.inter_closure
      (show x ∈ (range a)ᶜ ∩ closure (interior Q.closedRegion) from ⟨hx.2,hclosure.symm ▸ hx.1⟩)
    simpa only [Set.inter_comm,Set.diff_eq] using hh
  exact hc.subset_closure (Set.diff_subset_diff_left interior_subset) hcl


open CurveComplex.HyperellipticModel
/-- An actual planar arc disjoint from a compact connected nonseparating
barrier cannot create another complementary component. -/
theorem planar_internal_arc_and_disjoint_barrier_nonseparating
    (a : unitInterval → Schoenflies.Plane) (ha : Continuous a) (hai : Function.Injective a)
    {B : Set Schoenflies.Plane} (hBc : IsCompact B) (hB : IsConnected B)
    (hBcpl : IsConnected Bᶜ) (hdis : Disjoint (range a) B) :
    IsConnected (range a ∪ B)ᶜ := by
  classical
  let g : ℝ → Schoenflies.Plane := a ∘ Set.projIcc 0 1 zero_le_one
  have hg : Continuous g := ha.comp continuous_projIcc
  have hA : Schoenflies.IsArc (range a) := by
    refine ⟨g,hg.continuousOn,?_,?_⟩
    · intro t ht u hu h
      have he := hai h
      simpa [g,Set.projIcc_of_mem,ht,hu] using congrArg Subtype.val he
    · ext y
      constructor
      · rintro ⟨t,ht,rfl⟩
        exact ⟨_,rfl⟩
      · rintro ⟨t,rfl⟩
        refine ⟨t,t.property,?_⟩
        simp [g,Set.projIcc_of_mem]
  obtain ⟨Q,hAQ,hQB⟩ := exists_polygonalDisk_avoiding_compact_connected
    (isCompact_range ha) (isConnected_range ha) (Schoenflies.arc_complement hA) hBc hB hdis
  have hL : IsConnected (Q.closedRegion \ range a) := polygonal_disk_diff_internal_arc_connected Q ha hai hAQ
  let G := range a ∪ B
  have hGc : IsClosed G := (isCompact_range ha).isClosed.union hBc.isClosed
  have hLG : Q.closedRegion \ range a ⊆ Gᶜ := by
    intro x hx
    rintro (hxA | hxB)
    · exact hx.2 hxA
    · exact Set.disjoint_left.mp hQB hx.1 hxB
  obtain ⟨x,hxL⟩ := hL.nonempty
  let W := connectedComponentIn Gᶜ x
  have hW : IsComplementComponent G W := complementComponent_iff_componentIn.mpr ⟨x,hLG hxL,rfl⟩
  have hLW : Q.closedRegion \ range a ⊆ W := hL.isPreconnected.subset_connectedComponentIn hxL hLG
  have hAll : ∀ V, IsComplementComponent G V → V = W := by
    intro V hV
    by_cases hmeet : (V ∩ (Q.closedRegion \ range a)).Nonempty
    · obtain ⟨y,hyV,hyL⟩ := hmeet
      by_contra hne
      exact Set.disjoint_left.mp (complementComponents_disjoint hV hW hne) hyV (hLW hyL)
    · have hVout : V ⊆ (interior Q.closedRegion)ᶜ := by
        intro y hy hinside
        apply hmeet
        exact ⟨y,hy,interior_subset hinside,fun h => hV.2.2.1 hy (Or.inl h)⟩
      have hclout : closure V ⊆ (interior Q.closedRegion)ᶜ :=
        closure_minimal hVout isOpen_interior.isClosed_compl
      have hfrB : frontier V ⊆ B := by
        intro y hy
        rcases complementComponent_frontier_subset hGc hV hy with hyA | hyB
        · exact False.elim (hclout (frontier_subset_closure hy) (hAQ hyA))
        · exact hyB
      have hopen : IsOpen V := complementComponent_open hGc hV
      have hVB : V ⊆ Bᶜ := fun y hy h => hV.2.2.1 hy (Or.inr h)
      have hVeq : V = Bᶜ := by
        apply Set.Subset.antisymm hVB
        apply hBcpl.isPreconnected.subset_of_closure_inter_subset hopen
        · obtain ⟨y,hy⟩ := hV.1
          exact ⟨y,hVB hy,hy⟩
        · intro y hy
          by_contra hyn
          have hyfr : y ∈ frontier V := by rw [hopen.frontier_eq]; exact ⟨hy.1,hyn⟩
          exact hy.2 (hfrB hyfr)
      apply False.elim
      apply hmeet
      refine ⟨x,?_,hxL⟩
      rw [hVeq]
      exact fun h => Set.disjoint_left.mp hQB hxL.1 h
  have hWhole : W = Gᶜ := by
    apply Set.Subset.antisymm hW.2.2.1
    intro y hy
    have hC : IsComplementComponent G (connectedComponentIn Gᶜ y) :=
      complementComponent_iff_componentIn.mpr ⟨y,hy,rfl⟩
    rw [← hAll _ hC]
    exact mem_connectedComponentIn hy
  rw [← hWhole]
  exact hW.2.1

end ClassificationSchoenflies

namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Two actual nonloops meeting only at a common finish/start have connected
sphere complement; the chart puncture is supplied as an actual off-trace point. -/
theorem actual_disjoint_nonloops_complement_connected
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 ≠ a.val.map 1) (hb : b.val.map 0 ≠ b.val.map 1)
    (hmeet : Disjoint a.val.image b.val.image)
    (p : S) (hp : p ∉ a.val.image ∪ b.val.image) :
    IsConnected (a.val.image ∪ b.val.image)ᶜ := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let e := M.puncturedPlane p
  have hpa : p ∉ a.val.image := fun h => hp (Or.inl h)
  have hpb : p ∉ b.val.image := fun h => hp (Or.inr h)
  let ga : Interval → Schoenflies.Plane := fun t => e ⟨a.val.map t,fun h => hpa (h ▸ Set.mem_range_self t)⟩
  let gb : Interval → Schoenflies.Plane := fun t => e ⟨b.val.map t,fun h => hpb (h ▸ Set.mem_range_self t)⟩
  have hA : IsArcBetween (range ga) (ga 0) (ga 1) :=
    actual_nonloop_planar_arc M ⟨a.val,ha⟩ p hpa e
  have hB : IsArcBetween (range gb) (gb 0) (gb 1) :=
    actual_nonloop_planar_arc M ⟨b.val,hb⟩ p hpb e
  have hdis : Disjoint (range ga) (range gb) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t,rfl⟩ ⟨u,hu⟩
    have he : a.val.map t = b.val.map u := congrArg Subtype.val (e.injective hu.symm)
    exact Set.disjoint_left.mp hmeet (Set.mem_range_self t) (he.symm ▸ Set.mem_range_self u)
  have hgA : Continuous ga := e.continuous.comp (a.val.continuous.subtype_mk _)
  have hgAi : Function.Injective ga := by
    intro t u h
    exact NonLoopArc.injective ⟨a.val,ha⟩ (congrArg Subtype.val (e.injective h))
  have hconn := ClassificationSchoenflies.planar_internal_arc_and_disjoint_barrier_nonseparating
    ga hgA hgAi hB.isArc.isCompact hB.isArc.isConnected (Schoenflies.arc_complement hB.isArc) hdis
  let F : Schoenflies.Plane → S := fun x => (e.symm x).val
  have hF : Continuous F := continuous_subtype_val.comp e.symm.continuous
  have heq : F '' (range ga ∪ range gb)ᶜ =
      (a.val.image ∪ b.val.image)ᶜ ∩ {p}ᶜ := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨?_,(e.symm y).property⟩
      rintro (⟨t,ht⟩ | ⟨t,ht⟩)
      · apply hy
        left
        refine ⟨t,?_⟩
        change e _ = y
        rw [show (⟨a.val.map t,_⟩ : {x : S // x ≠ p}) = e.symm y from Subtype.ext ht]
        exact e.apply_symm_apply y
      · apply hy
        right
        refine ⟨t,?_⟩
        change e _ = y
        rw [show (⟨b.val.map t,_⟩ : {x : S // x ≠ p}) = e.symm y from Subtype.ext ht]
        exact e.apply_symm_apply y
    · rintro ⟨hx,hxp⟩
      refine ⟨e ⟨x,hxp⟩,?_,congrArg Subtype.val (e.symm_apply_apply ⟨x,hxp⟩)⟩
      rintro (⟨t,ht⟩ | ⟨t,ht⟩)
      · apply hx
        left
        exact ⟨t,congrArg Subtype.val (e.injective ht)⟩
      · apply hx
        right
        exact ⟨t,congrArg Subtype.val (e.injective ht)⟩
  have hpunct : IsConnected ((a.val.image ∪ b.val.image)ᶜ ∩ {p}ᶜ) := by
    rw [← heq]
    exact hconn.image F hF.continuousOn
  have hsphere : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    apply isConnected_sphere _ _ (by norm_num)
    rw [← Module.finrank_eq_rank]
    norm_num
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp hsphere
  letI : ConnectedSpace S := connectedSpace_iff_univ.mpr (by
    have hi := isConnected_univ.image M.sphere.symm M.sphere.symm.continuous.continuousOn
    simpa only [Set.image_univ,M.sphere.symm.surjective.range_eq] using hi)
  have hdense : Dense ({p}ᶜ : Set S) := by
    apply dense_compl_singleton_iff_not_open.mpr
    intro hopen
    have hsingle : ({p} : Set S) = Set.univ :=
      (show IsClopen ({p} : Set S) from ⟨isClosed_singleton,hopen⟩).eq_univ ⟨p,rfl⟩
    exact hpa ⟨0,Set.mem_singleton_iff.mp (hsingle.symm ▸ Set.mem_univ _)⟩
  have hclosed : IsClosed (a.val.image ∪ b.val.image) :=
    (isCompact_range a.val.continuous).isClosed.union (isCompact_range b.val.continuous).isClosed
  have hcl : (a.val.image ∪ b.val.image)ᶜ ⊆
      closure ((a.val.image ∪ b.val.image)ᶜ ∩ {p}ᶜ) := by
    simpa only [Set.inter_comm] using hdense.open_subset_closure_inter hclosed.isOpen_compl
  exact hpunct.subset_closure Set.inter_subset_left hcl
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies
open scoped Classical
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A genuine nonloop slit issuing from an actual loop has only one incident
complementary face in the literal two-trace subgraph. -/
theorem actual_loop_single_slit_unique_incident_face
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hb : b.val.map 0 ≠ b.val.map 1)
    (hmeet : a.val.image ∩ b.val.image = {b.val.map 0}) :
    ∃ W : Set S, IsComplementComponent (a.val.image ∪ b.val.image) W ∧
      ∀ V, IsComplementComponent (a.val.image ∪ b.val.image) V →
        (frontier V ∩ arcInterior M b).Nonempty → V = W := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  obtain ⟨D⟩ := markedLoop_disc_decomposition_exists M a.val ha
  have hbinj : Function.Injective b.val.map := NonLoopArc.injective ⟨b.val,hb⟩
  have havoid : ∀ t : Interval, t ≠ 0 → b.val.map t ∈ a.val.imageᶜ := by
    intro t ht hta
    have hh : b.val.map t = b.val.map 0 := by
      exact Set.mem_singleton_iff.mp (hmeet ▸ ⟨hta,Set.mem_range_self t⟩)
    exact ht (hbinj hh)
  have h1 : b.val.map 1 ∈ a.val.imageᶜ := havoid 1 (by norm_num)
  let C := connectedComponentIn a.val.imageᶜ (b.val.map 1)
  have hC : IsComplementComponent a.val.image C :=
    complementComponent_iff_componentIn.mpr ⟨b.val.map 1,h1,rfl⟩
  obtain ⟨i,hCi⟩ := (D.all_components C).1 hC
  have hLpre : IsPreconnected (b.val.map '' Set.Ioc (0 : Interval) 1) :=
    isPreconnected_Ioc.image b.val.map b.val.continuous.continuousOn
  have hLsub : b.val.map '' Set.Ioc (0 : Interval) 1 ⊆ a.val.imageᶜ := by
    rintro x ⟨t,ht,rfl⟩
    exact havoid t (ne_of_gt ht.1)
  have hLC : b.val.map '' Set.Ioc (0 : Interval) 1 ⊆ C :=
    hLpre.subset_connectedComponentIn ⟨1,by norm_num,rfl⟩ hLsub
  have hin : ∀ t : Interval, t ≠ 0 → b.val.map t ∈ D.side i := by
    intro t ht
    rw [← hCi]
    apply hLC
    refine ⟨t,?_,rfl⟩
    exact ⟨lt_of_le_of_ne' (show (0 : Interval) ≤ t from t.property.1) ht,t.property.2⟩
  have h0 : b.val.map 0 ∉ D.side i := by
    intro h
    have hz : b.val.map 0 ∈ a.val.image := by
      have hm : b.val.map 0 ∈ a.val.image ∩ b.val.image := by rw [hmeet]; exact Set.mem_singleton _
      exact hm.1
    exact (D.discs i).component.2.2.1 h hz
  let e : Schoenflies.Plane ≃ₜ D.side i := Homeomorph.unitBall.trans (D.discs i).openDisk
  have hWconn : IsConnected (D.side i \ b.val.image) :=
    actual_marked_open_disc_single_slit_connected M (D.side i) (D.discs i).open_side e b h0 hin
  let W := D.side i \ b.val.image
  have hWcomp : IsComplementComponent (a.val.image ∪ b.val.image) W := by
    refine ⟨hWconn.nonempty,hWconn,?_,?_⟩
    · intro x hx h
      rcases h with h | h
      · exact (D.discs i).component.2.2.1 hx.1 h
      · exact hx.2 h
    · intro T hT hWT hTK
      obtain ⟨x,hx⟩ := hWconn.nonempty
      have hTC : T ⊆ connectedComponentIn a.val.imageᶜ x := hT.isPreconnected.subset_connectedComponentIn
        (hWT hx) (fun y hy ha => hTK hy (Or.inl ha))
      have hside : D.side i = connectedComponentIn a.val.imageᶜ x := by
        obtain ⟨w,hw,he⟩ := complementComponent_iff_componentIn.mp (D.discs i).component
        rw [he]
        exact connectedComponentIn_eq (he ▸ hx.1)
      have hTW : T ⊆ W := fun y hy => ⟨hside.symm ▸ hTC hy,fun hb => hTK hy (Or.inr hb)⟩
      exact Set.Subset.antisymm hTW hWT
  refine ⟨W,hWcomp,?_⟩
  intro V hV htouch
  obtain ⟨z,hzfr,hzb⟩ := htouch
  have hzside : z ∈ D.side i := by
    obtain ⟨t,rfl⟩ := hzb.1
    apply hin t
    intro ht
    exact hzb.2 (ht.symm ▸ b.val.start_marked)
  obtain ⟨x,hxside,hxV⟩ := Set.Nonempty.of_closure
    ⟨z,(D.discs i).open_side.inter_closure ⟨hzside,frontier_subset_closure hzfr⟩⟩
  have hxW : x ∈ W := ⟨hxside,fun h => hV.2.2.1 hxV (Or.inr h)⟩
  by_contra hne
  exact Set.disjoint_left.mp (complementComponents_disjoint hV hWcomp hne) hxV hxW

/-- Removing an actual internal nonloop arc from an actual open disc keeps
that disc connected. The plane chart is literal, not a connectivity certificate. -/
theorem actual_open_disc_internal_nonloop_connected
    (M : HyperellipticModel E S) (U : Set S) (e : Schoenflies.Plane ≃ₜ U)
    (a : EssentialMarkedArc M) (ha : a.val.map 0 ≠ a.val.map 1)
    (hin : a.val.image ⊆ U) : IsConnected (U \ a.val.image) := by
  let b : Interval → U := fun t => ⟨a.val.map t, hin (Set.mem_range_self t)⟩
  have hb : Continuous b := a.val.continuous.subtype_mk _
  let g : Interval → Schoenflies.Plane := e.symm ∘ b
  have hg : Continuous g := e.symm.continuous.comp hb
  have hgi : Function.Injective g := by
    intro t u h
    apply NonLoopArc.injective ⟨a.val,ha⟩
    exact congrArg Subtype.val (e.symm.injective h)
  let f : ℝ → Schoenflies.Plane := g ∘ Set.projIcc 0 1 zero_le_one
  have hf : Continuous f := hg.comp continuous_projIcc
  have hfi : Set.InjOn f (Set.Icc 0 1) := by
    intro t ht u hu h
    have he := hgi h
    simpa [f, Set.projIcc_of_mem, ht, hu] using congrArg Subtype.val he
  have hA : Schoenflies.IsArc (Set.range g) := by
    refine ⟨f,hf.continuousOn,hfi,?_⟩
    ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨_,rfl⟩
    · rintro ⟨t,rfl⟩
      refine ⟨t,t.property,?_⟩
      simp [f,Set.projIcc_of_mem]
  have hconn := Schoenflies.arc_complement hA
  let F : Schoenflies.Plane → S := fun x => (e x).val
  have hF : Continuous F := continuous_subtype_val.comp e.continuous
  have hEq : F '' (Set.range g)ᶜ = U \ a.val.image := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨(e y).property,?_⟩
      rintro ⟨t,ht⟩
      apply hy
      refine ⟨t,?_⟩
      apply e.injective
      change e (e.symm (b t)) = e y
      rw [e.apply_symm_apply]
      exact Subtype.ext ht
    · rintro ⟨hx,hxa⟩
      refine ⟨e.symm ⟨x,hx⟩,?_,?_⟩
      · rintro ⟨t,ht⟩
        apply hxa
        refine ⟨t,?_⟩
        exact congrArg Subtype.val (e.symm.injective ht)
      · exact congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
  rw [← hEq]
  exact hconn.image F hF.continuousOn

/-- A genuine nonloop slit issuing from an actual loop has only one incident
complementary face in the literal two-trace subgraph. -/
theorem actual_loop_disjoint_nonloop_unique_incident_face
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hb : b.val.map 0 ≠ b.val.map 1)
    (hmeet : Disjoint a.val.image b.val.image) :
    ∃ W : Set S, IsComplementComponent (a.val.image ∪ b.val.image) W ∧
      ∀ V, IsComplementComponent (a.val.image ∪ b.val.image) V →
        (frontier V ∩ arcInterior M b).Nonempty → V = W := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  obtain ⟨D⟩ := markedLoop_disc_decomposition_exists M a.val ha
  have hbinj : Function.Injective b.val.map := NonLoopArc.injective ⟨b.val,hb⟩
  have havoid : ∀ t : Interval, b.val.map t ∈ a.val.imageᶜ := by
    intro t h
    exact Set.disjoint_left.mp hmeet h (Set.mem_range_self t)
  let C := connectedComponentIn a.val.imageᶜ (b.val.map 1)
  have hC : IsComplementComponent a.val.image C :=
    complementComponent_iff_componentIn.mpr ⟨b.val.map 1,havoid 1,rfl⟩
  obtain ⟨i,hCi⟩ := (D.all_components C).1 hC
  have hLpre : IsPreconnected b.val.image :=
    by simpa [MarkedArc.image] using isPreconnected_univ.image b.val.map b.val.continuous.continuousOn
  have hLsub : b.val.image ⊆ a.val.imageᶜ := by
    rintro x ⟨t,rfl⟩
    exact havoid t
  have hLC : b.val.image ⊆ C :=
    hLpre.subset_connectedComponentIn (Set.mem_range_self 1) hLsub
  have hin : b.val.image ⊆ D.side i := by
    rw [← hCi]
    exact hLC
  let e : Schoenflies.Plane ≃ₜ D.side i := Homeomorph.unitBall.trans (D.discs i).openDisk
  have hWconn : IsConnected (D.side i \ b.val.image) :=
    actual_open_disc_internal_nonloop_connected M (D.side i) e b hb hin
  let W := D.side i \ b.val.image
  have hWcomp : IsComplementComponent (a.val.image ∪ b.val.image) W := by
    refine ⟨hWconn.nonempty,hWconn,?_,?_⟩
    · intro x hx h
      rcases h with h | h
      · exact (D.discs i).component.2.2.1 hx.1 h
      · exact hx.2 h
    · intro T hT hWT hTK
      obtain ⟨x,hx⟩ := hWconn.nonempty
      have hTC : T ⊆ connectedComponentIn a.val.imageᶜ x := hT.isPreconnected.subset_connectedComponentIn
        (hWT hx) (fun y hy ha => hTK hy (Or.inl ha))
      have hside : D.side i = connectedComponentIn a.val.imageᶜ x := by
        obtain ⟨w,hw,he⟩ := complementComponent_iff_componentIn.mp (D.discs i).component
        rw [he]
        exact connectedComponentIn_eq (he ▸ hx.1)
      have hTW : T ⊆ W := fun y hy => ⟨hside.symm ▸ hTC hy,fun hb => hTK hy (Or.inr hb)⟩
      exact Set.Subset.antisymm hTW hWT
  refine ⟨W,hWcomp,?_⟩
  intro V hV htouch
  obtain ⟨z,hzfr,hzb⟩ := htouch
  have hzside : z ∈ D.side i := hin hzb.1
  obtain ⟨x,hxside,hxV⟩ := Set.Nonempty.of_closure
    ⟨z,(D.discs i).open_side.inter_closure ⟨hzside,frontier_subset_closure hzfr⟩⟩
  have hxW : x ∈ W := ⟨hxside,fun h => hV.2.2.1 hxV (Or.inr h)⟩
  by_contra hne
  exact Set.disjoint_left.mp (complementComponents_disjoint hV hWcomp hne) hxV hxW


theorem actual_nonloop_reversed_representative
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : a.val.map 0 ≠ a.val.map 1) :
    ∃ b : EssentialMarkedArc M, b.val.map 0 = a.val.map 1 ∧
      b.val.map 1 = a.val.map 0 ∧ b.val.image = a.val.image := by
  let b : MarkedArc M := {
    map := a.val.map ∘ unitInterval.symm
    continuous := a.val.continuous.comp unitInterval.continuous_symm
    injective_except_loop_closure := by
      intro t u he
      left
      exact unitInterval.symm_involutive.injective (NonLoopArc.injective ⟨a.val,ha⟩ he)
    start_marked := by simpa using a.val.end_marked
    end_marked := by simpa using a.val.start_marked
    marked_only_at_ends := by
      intro t ht
      obtain ht | ht := a.val.marked_only_at_ends (unitInterval.symm t) ht
      · right
        have h := congrArg unitInterval.symm ht
        simpa using h
      · left
        have h := congrArg unitInterval.symm ht
        simpa using h }
  have hb : IsEssentialMarkedArc M b := Or.inl (by
    change a.val.map (unitInterval.symm 0) ≠ a.val.map (unitInterval.symm 1)
    simpa using ha.symm)
  refine ⟨⟨b,hb⟩,?_,?_,?_⟩
  · simp [b]
  · simp [b]
  · ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact Set.mem_range_self _
    · rintro ⟨t,rfl⟩
      refine ⟨unitInterval.symm t,?_⟩
      simp [b]


theorem actual_loop_finish_slit_unique_incident_face
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hb : b.val.map 0 ≠ b.val.map 1)
    (hmeet : a.val.image ∩ b.val.image = {b.val.map 1}) :
    ∃ W : Set S, IsComplementComponent (a.val.image ∪ b.val.image) W ∧
      ∀ V, IsComplementComponent (a.val.image ∪ b.val.image) V →
        (frontier V ∩ arcInterior M b).Nonempty → V = W := by
  obtain ⟨c,hc0,hc1,hcim⟩ := actual_nonloop_reversed_representative M b hb
  have hc : c.val.map 0 ≠ c.val.map 1 := by rw [hc0,hc1]; exact hb.symm
  have hmeet' : a.val.image ∩ c.val.image = {c.val.map 0} := by
    rw [hcim,hc0]; exact hmeet
  obtain ⟨W,hW,hunique⟩ := actual_loop_single_slit_unique_incident_face M a c ha hc hmeet'
  refine ⟨W,by simpa [hcim] using hW,?_⟩
  intro V hV htouch
  apply hunique V
  · simpa [hcim] using hV
  · simpa [arcInterior,hcim] using htouch

noncomputable local instance transferClassDecEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := M.exactEdgeClassDecEq

/-- A full-graph face which is also a boundary-subgraph face retains a second
incident subgraph face for every all-bad edge in that subgraph. -/
theorem actual_boundary_subgraph_second_incident_face
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (K U : Set S) (hK : IsClosed K)
    (hKG : K ⊆ ⋃ v, (r v).val.image)
    (hU : IsComplementComponent (⋃ v, (r v).val.image) U)
    (hUK : IsComplementComponent K U)
    (u : {v // v ∈ sigma}) (huK : (r u).val.image ⊆ K)
    (htouch : (frontier U ∩ arcInterior M (r u)).Nonempty) :
    ∃ W, IsComplementComponent K W ∧ W ≠ U ∧
      (frontier W ∩ arcInterior M (r u)).Nonempty := by
  classical
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  obtain ⟨T,hcard,hT⟩ := actual_bad_edge_exact_incident_faces M r hr hd hbad u
  have hUT : U ∈ T := (hT U).2 ⟨hU,htouch⟩
  obtain ⟨V,hVT,hVU⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) U
  obtain ⟨hV,hcontact⟩ := (hT V).1 hVT
  obtain ⟨x,hxV⟩ := hV.1
  have hxK : x ∈ Kᶜ := fun h => hV.2.2.1 hxV (hKG h)
  let W := connectedComponentIn Kᶜ x
  have hW : IsComplementComponent K W :=
    complementComponent_iff_componentIn.mpr ⟨x,hxK,rfl⟩
  have hVW : V ⊆ W := hV.2.1.isPreconnected.subset_connectedComponentIn hxV
    (fun y hy h => hV.2.2.1 hy (hKG h))
  have hWU : W ≠ U := by
    intro he
    exact Set.disjoint_left.mp (complementComponents_disjoint hV hU hVU) hxV (he ▸ hVW hxV)
  obtain ⟨z,hzV,hzu⟩ := hcontact
  have hzcl : z ∈ closure W := closure_mono hVW (frontier_subset_closure hzV)
  have hznot : z ∉ W := fun h => hW.2.2.1 h (huK hzu.1)
  have hWopen : IsOpen W := by
    obtain ⟨y,hy,he⟩ := complementComponent_iff_componentIn.mp hW
    rw [he]
    exact hK.isOpen_compl.connectedComponentIn
  refine ⟨W,hW,hWU,z,?_,hzu⟩
  rw [frontier, hWopen.interior_eq]
  exact ⟨hzcl,hznot⟩

/-- The actual two-sided all-bad incidence excludes a loop with a single
nonloop slit as the entire frontier support of a full-graph face. -/
theorem actual_full_face_not_loop_single_slit
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (U : Set S) (hU : IsComplementComponent (⋃ v, (r v).val.image) U)
    (i j : {v // v ∈ sigma})
    (hUK : IsComplementComponent ((r i).val.image ∪ (r j).val.image) U)
    (hj : (frontier U ∩ arcInterior M (r j)).Nonempty)
    (hiLoop : (r i).val.map 0 = (r i).val.map 1)
    (hjNonloop : (r j).val.map 0 ≠ (r j).val.map 1)
    (hmeet : (r i).val.image ∩ (r j).val.image = {(r j).val.map 0}) : False := by
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨W,hWK,hunique⟩ := actual_loop_single_slit_unique_incident_face M
    (r i) (r j) hiLoop hjNonloop hmeet
  have hUeq : U = W := hunique U hUK hj
  obtain ⟨V,hVK,hVU,hVcontact⟩ := actual_boundary_subgraph_second_incident_face
    M r hr hd hbad ((r i).val.image ∪ (r j).val.image) U
    ((isCompact_range (r i).val.continuous).isClosed.union (isCompact_range (r j).val.continuous).isClosed)
    (Set.union_subset (Set.subset_iUnion (fun v => (r v).val.image) i)
      (Set.subset_iUnion (fun v => (r v).val.image) j)) hU hUK j
    Set.subset_union_right hj
  exact hVU ((hunique V hVK hVcontact).trans hUeq.symm)

/-- The actual two-sided all-bad incidence excludes a loop with a single
nonloop slit as the entire frontier support of a full-graph face. -/
theorem actual_full_face_not_disjoint_loop_nonloop
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (U : Set S) (hU : IsComplementComponent (⋃ v, (r v).val.image) U)
    (i j : {v // v ∈ sigma})
    (hUK : IsComplementComponent ((r i).val.image ∪ (r j).val.image) U)
    (hj : (frontier U ∩ arcInterior M (r j)).Nonempty)
    (hiLoop : (r i).val.map 0 = (r i).val.map 1)
    (hjNonloop : (r j).val.map 0 ≠ (r j).val.map 1)
    (hmeet : Disjoint (r i).val.image (r j).val.image) : False := by
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨W,hWK,hunique⟩ := actual_loop_disjoint_nonloop_unique_incident_face M
    (r i) (r j) hiLoop hjNonloop hmeet
  have hUeq : U = W := hunique U hUK hj
  obtain ⟨V,hVK,hVU,hVcontact⟩ := actual_boundary_subgraph_second_incident_face
    M r hr hd hbad ((r i).val.image ∪ (r j).val.image) U
    ((isCompact_range (r i).val.continuous).isClosed.union (isCompact_range (r j).val.continuous).isClosed)
    (Set.union_subset (Set.subset_iUnion (fun v => (r v).val.image) i)
      (Set.subset_iUnion (fun v => (r v).val.image) j)) hU hUK j
    Set.subset_union_right hj
  exact hVU ((hunique V hVK hVcontact).trans hUeq.symm)

theorem actual_full_face_not_loop_finish_slit
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (U : Set S) (hU : IsComplementComponent (⋃ v, (r v).val.image) U)
    (i j : {v // v ∈ sigma})
    (hUK : IsComplementComponent ((r i).val.image ∪ (r j).val.image) U)
    (hj : (frontier U ∩ arcInterior M (r j)).Nonempty)
    (hiLoop : (r i).val.map 0 = (r i).val.map 1)
    (hjNonloop : (r j).val.map 0 ≠ (r j).val.map 1)
    (hmeet : (r i).val.image ∩ (r j).val.image = {(r j).val.map 1}) : False := by
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨W,hWK,hunique⟩ := actual_loop_finish_slit_unique_incident_face M
    (r i) (r j) hiLoop hjNonloop hmeet
  have hUeq : U = W := hunique U hUK hj
  obtain ⟨V,hVK,hVU,hVcontact⟩ := actual_boundary_subgraph_second_incident_face
    M r hr hd hbad ((r i).val.image ∪ (r j).val.image) U
    ((isCompact_range (r i).val.continuous).isClosed.union (isCompact_range (r j).val.continuous).isClosed)
    (Set.union_subset (Set.subset_iUnion (fun v => (r v).val.image) i)
      (Set.subset_iUnion (fun v => (r v).val.image) j)) hU hUK j
    Set.subset_union_right hj
  exact hVU ((hunique V hVK hVcontact).trans hUeq.symm)


/-- Mixed loop/nonloop supports cannot bound an actual all-bad full-graph
face. This handles both endpoint orientations and disjoint traces. -/
theorem actual_full_face_not_mixed_two_trace
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (U : Set S) (hU : IsComplementComponent (⋃ v, (r v).val.image) U)
    (i j : {v // v ∈ sigma}) (hij : i ≠ j)
    (hUK : IsComplementComponent ((r i).val.image ∪ (r j).val.image) U)
    (hj : (frontier U ∩ arcInterior M (r j)).Nonempty)
    (hiLoop : (r i).val.map 0 = (r i).val.map 1)
    (hjNonloop : (r j).val.map 0 ≠ (r j).val.map 1) : False := by
  classical
  have he : (r i).val.image ∩ (r j).val.image =
      ((markedArcEndset (r i).val : Set S) ∩ (markedArcEndset (r j).val : Set S)) :=
    markedArc_disjoint_interiors_inter_image _ _ (hd i j hij)
  have hemem : ∀ x, x ∈ (r i).val.image ∩ (r j).val.image ↔
      x = (r i).val.map 0 ∧ (x = (r j).val.map 0 ∨ x = (r j).val.map 1) := by
    intro x
    rw [he]
    simp [markedArcEndset,hiLoop]
  by_cases h0 : (r i).val.map 0 = (r j).val.map 0
  · have hmeet : (r i).val.image ∩ (r j).val.image = {(r j).val.map 0} := by
      ext x
      rw [hemem]
      simp only [h0,Set.mem_singleton_iff]
      tauto
    exact actual_full_face_not_loop_single_slit M r hr hd hbad U hU i j hUK hj
      hiLoop hjNonloop hmeet
  · by_cases h1 : (r i).val.map 0 = (r j).val.map 1
    · have hmeet : (r i).val.image ∩ (r j).val.image = {(r j).val.map 1} := by
        ext x
        rw [hemem]
        simp only [h1,Set.mem_singleton_iff]
        tauto
      exact actual_full_face_not_loop_finish_slit M r hr hd hbad U hU i j hUK hj
        hiLoop hjNonloop hmeet
    · have hdis : Disjoint (r i).val.image (r j).val.image := by
        apply Set.disjoint_left.mpr
        intro x hxi hxj
        obtain ⟨hxi,hxj⟩ := (hemem x).mp ⟨hxi,hxj⟩
        rcases hxj with hxj | hxj
        · exact h0 (hxi.symm.trans hxj)
        · exact h1 (hxi.symm.trans hxj)
      exact actual_full_face_not_disjoint_loop_nonloop M r hr hd hbad U hU i j hUK hj
        hiLoop hjNonloop hdis

/-- Two actual nonloops meeting only at a common finish/start have connected
sphere complement; the chart puncture is supplied as an actual off-trace point. -/
theorem actual_one_endpoint_nonloops_complement_connected
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 ≠ a.val.map 1) (hb : b.val.map 0 ≠ b.val.map 1)
    (hab : a.val.map 1 = b.val.map 0)
    (hmeet : a.val.image ∩ b.val.image = {a.val.map 1})
    (p : S) (hp : p ∉ a.val.image ∪ b.val.image) :
    IsConnected (a.val.image ∪ b.val.image)ᶜ := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let e := M.puncturedPlane p
  have hpa : p ∉ a.val.image := fun h => hp (Or.inl h)
  have hpb : p ∉ b.val.image := fun h => hp (Or.inr h)
  let ga : Interval → Schoenflies.Plane := fun t => e ⟨a.val.map t,fun h => hpa (h ▸ Set.mem_range_self t)⟩
  let gb : Interval → Schoenflies.Plane := fun t => e ⟨b.val.map t,fun h => hpb (h ▸ Set.mem_range_self t)⟩
  have hA : IsArcBetween (range ga) (ga 0) (ga 1) :=
    actual_nonloop_planar_arc M ⟨a.val,ha⟩ p hpa e
  have hB : IsArcBetween (range gb) (gb 0) (gb 1) :=
    actual_nonloop_planar_arc M ⟨b.val,hb⟩ p hpb e
  have hmid : ga 1 = gb 0 := congrArg e (Subtype.ext hab)
  have hmeet' : ∀ z ∈ range ga, z ∈ range gb → z = ga 1 := by
    rintro z ⟨t,rfl⟩ ⟨u,hu⟩
    have he : a.val.map t = b.val.map u :=
      congrArg Subtype.val (e.injective hu.symm)
    have hz : a.val.map t = a.val.map 1 :=
      Set.mem_singleton_iff.mp (hmeet ▸ ⟨Set.mem_range_self t,he.symm ▸ Set.mem_range_self u⟩)
    exact congrArg e (Subtype.ext hz)
  have hAB : IsArcBetween (range ga ∪ range gb) (ga 0) (gb 1) :=
    hA.concatenate (hmid.symm ▸ hB) hmeet'
  have hconn := Schoenflies.arc_complement hAB.isArc
  let F : Schoenflies.Plane → S := fun x => (e.symm x).val
  have hF : Continuous F := continuous_subtype_val.comp e.symm.continuous
  have heq : F '' (range ga ∪ range gb)ᶜ =
      (a.val.image ∪ b.val.image)ᶜ ∩ {p}ᶜ := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨?_,(e.symm y).property⟩
      rintro (⟨t,ht⟩ | ⟨t,ht⟩)
      · apply hy
        left
        refine ⟨t,?_⟩
        change e _ = y
        rw [show (⟨a.val.map t,_⟩ : {x : S // x ≠ p}) = e.symm y from Subtype.ext ht]
        exact e.apply_symm_apply y
      · apply hy
        right
        refine ⟨t,?_⟩
        change e _ = y
        rw [show (⟨b.val.map t,_⟩ : {x : S // x ≠ p}) = e.symm y from Subtype.ext ht]
        exact e.apply_symm_apply y
    · rintro ⟨hx,hxp⟩
      refine ⟨e ⟨x,hxp⟩,?_,congrArg Subtype.val (e.symm_apply_apply ⟨x,hxp⟩)⟩
      rintro (⟨t,ht⟩ | ⟨t,ht⟩)
      · apply hx
        left
        exact ⟨t,congrArg Subtype.val (e.injective ht)⟩
      · apply hx
        right
        exact ⟨t,congrArg Subtype.val (e.injective ht)⟩
  have hpunct : IsConnected ((a.val.image ∪ b.val.image)ᶜ ∩ {p}ᶜ) := by
    rw [← heq]
    exact hconn.image F hF.continuousOn
  have hsphere : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    apply isConnected_sphere _ _ (by norm_num)
    rw [← Module.finrank_eq_rank]
    norm_num
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp hsphere
  letI : ConnectedSpace S := connectedSpace_iff_univ.mpr (by
    have hi := isConnected_univ.image M.sphere.symm M.sphere.symm.continuous.continuousOn
    simpa only [Set.image_univ,M.sphere.symm.surjective.range_eq] using hi)
  have hdense : Dense ({p}ᶜ : Set S) := by
    apply dense_compl_singleton_iff_not_open.mpr
    intro hopen
    have hsingle : ({p} : Set S) = Set.univ :=
      (show IsClopen ({p} : Set S) from ⟨isClosed_singleton,hopen⟩).eq_univ ⟨p,rfl⟩
    exact hpa ⟨0,Set.mem_singleton_iff.mp (hsingle.symm ▸ Set.mem_univ _)⟩
  have hclosed : IsClosed (a.val.image ∪ b.val.image) :=
    (isCompact_range a.val.continuous).isClosed.union (isCompact_range b.val.continuous).isClosed
  have hcl : (a.val.image ∪ b.val.image)ᶜ ⊆
      closure ((a.val.image ∪ b.val.image)ᶜ ∩ {p}ᶜ) := by
    simpa only [Set.inter_comm] using hdense.open_subset_closure_inter hclosed.isOpen_compl
  exact hpunct.subset_closure Set.inter_subset_left hcl

theorem actual_full_face_not_one_endpoint_nonloops
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (U : Set S) (hU : IsComplementComponent (⋃ v, (r v).val.image) U)
    (i j : {v // v ∈ sigma})
    (hUK : IsComplementComponent ((r i).val.image ∪ (r j).val.image) U)
    (hj : (frontier U ∩ arcInterior M (r j)).Nonempty)
    (ha : (r i).val.map 0 ≠ (r i).val.map 1)
    (hb : (r j).val.map 0 ≠ (r j).val.map 1)
    (hab : (r i).val.map 1 = (r j).val.map 0)
    (hmeet : (r i).val.image ∩ (r j).val.image = {(r i).val.map 1}) : False := by
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨p,hp⟩ := hUK.1
  have hc := actual_one_endpoint_nonloops_complement_connected M (r i) (r j) ha hb hab
    hmeet p (hUK.2.2.1 hp)
  have hUwhole : U = ((r i).val.image ∪ (r j).val.image)ᶜ :=
    (hUK.2.2.2 _ hc (fun x hx => hUK.2.2.1 hx) (fun x hx => hx)).symm
  obtain ⟨W,hW,hWU,hcontact⟩ := actual_boundary_subgraph_second_incident_face M r hr hd hbad
    ((r i).val.image ∪ (r j).val.image) U
    ((isCompact_range (r i).val.continuous).isClosed.union (isCompact_range (r j).val.continuous).isClosed)
    (Set.union_subset (Set.subset_iUnion (fun v => (r v).val.image) i)
      (Set.subset_iUnion (fun v => (r v).val.image) j)) hU hUK j Set.subset_union_right hj
  have hWwhole : W = ((r i).val.image ∪ (r j).val.image)ᶜ :=
    (hW.2.2.2 _ hc (fun x hx => hW.2.2.1 hx) (fun x hx => hx)).symm
  exact hWU (hWwhole.trans hUwhole.symm)


/-- Endpoint orientation is immaterial to the actual single-endpoint
nonloop complement calculation. -/
theorem actual_singleton_intersection_nonloops_connected
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 ≠ a.val.map 1) (hb : b.val.map 0 ≠ b.val.map 1)
    (hd : Disjoint (arcInterior M a) (arcInterior M b))
    (q : S) (hmeet : a.val.image ∩ b.val.image = {q})
    (p : S) (hp : p ∉ a.val.image ∪ b.val.image) :
    IsConnected (a.val.image ∪ b.val.image)ᶜ := by
  classical
  have hq : q ∈ a.val.image ∩ b.val.image := by rw [hmeet]; exact Set.mem_singleton _
  have he := markedArc_disjoint_interiors_inter_image a.val b.val hd
  have hqa : q = a.val.map 0 ∨ q = a.val.map 1 := by
    have h := (he ▸ hq).1
    simpa [markedArcEndset] using h
  have hqb : q = b.val.map 0 ∨ q = b.val.map 1 := by
    have h := (he ▸ hq).2
    simpa [markedArcEndset] using h
  have orientFinish : ∀ (c : EssentialMarkedArc M), c.val.map 0 ≠ c.val.map 1 →
      (q = c.val.map 0 ∨ q = c.val.map 1) →
      ∃ d : EssentialMarkedArc M, d.val.map 0 ≠ d.val.map 1 ∧
        d.val.map 1 = q ∧ d.val.image = c.val.image := by
    intro c hc hq
    rcases hq with hq | hq
    · obtain ⟨d,hd0,hd1,hdim⟩ := actual_nonloop_reversed_representative M c hc
      refine ⟨d,?_,hd1.trans hq.symm,hdim⟩
      rw [hd0,hd1]; exact hc.symm
    · exact ⟨c,hc,hq.symm,rfl⟩
  obtain ⟨a',ha',haq,haim⟩ := orientFinish a ha hqa
  obtain ⟨b',hb',hbq,hbim⟩ := orientFinish b hb hqb
  obtain ⟨c,hc0,hc1,hcim⟩ := actual_nonloop_reversed_representative M b' hb'
  have hc : c.val.map 0 ≠ c.val.map 1 := by rw [hc0,hc1]; exact hb'.symm
  have hac : a'.val.map 1 = c.val.map 0 := haq.trans (hc0.trans hbq).symm
  have hmeet' : a'.val.image ∩ c.val.image = {a'.val.map 1} := by
    rw [haim,hcim,hbim,haq]; exact hmeet
  have hpc : p ∉ a'.val.image ∪ c.val.image := by simpa [haim,hcim,hbim] using hp
  simpa [haim,hcim,hbim] using
    actual_one_endpoint_nonloops_complement_connected M a' c ha' hc hac hmeet' p hpc


/-- The actual two-nonloop subgraph is nonseparating unless both unordered
endpoint sets agree. All connectivity is constructed from literal traces. -/
theorem actual_nonparallel_nonloop_pair_complement_connected
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 ≠ a.val.map 1) (hb : b.val.map 0 ≠ b.val.map 1)
    (hd : Disjoint (arcInterior M a) (arcInterior M b))
    (hne : markedArcEndset a.val ≠ markedArcEndset b.val)
    (p : S) (hp : p ∉ a.val.image ∪ b.val.image) :
    IsConnected (a.val.image ∪ b.val.image)ᶜ := by
  classical
  let A := markedArcEndset a.val
  let B := markedArcEndset b.val
  have hAc : A.card = 2 := by simp [A,markedArcEndset,ha]
  have hBc : B.card = 2 := by simp [B,markedArcEndset,hb]
  have hIc : (A ∩ B).card < 2 := by
    by_contra h
    have hle : 2 ≤ (A ∩ B).card := by omega
    have hIA : A ∩ B = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hIB : A ∩ B = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (hIA.symm.trans hIB)
  have he := markedArc_disjoint_interiors_inter_image a.val b.val hd
  by_cases hI : (A ∩ B).Nonempty
  · have hcard : (A ∩ B).card = 1 := by
      have hpos := Finset.card_pos.mpr hI
      omega
    obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hcard
    have hmeet : a.val.image ∩ b.val.image = {q} := by
      rw [he]
      change (↑A : Set S) ∩ (↑B : Set S) = {q}
      rw [← Finset.coe_inter,hq]
      simp
    exact actual_singleton_intersection_nonloops_connected M a b ha hb hd q hmeet p hp
  · have hdis : Disjoint a.val.image b.val.image := by
      apply Set.disjoint_left.mpr
      intro x hxa hxb
      have hh := he ▸ (show x ∈ a.val.image ∩ b.val.image from ⟨hxa,hxb⟩)
      exact hI ⟨x,Finset.mem_inter.mpr hh⟩
    exact actual_disjoint_nonloops_complement_connected M a b ha hb hdis p hp

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_loop_single_slit_unique_incident_face
namespace CurveComplex.HyperellipticModel
open Set
open scoped Classical
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- An actual loop wholly inside a connected open sphere domain splits it
into exactly two faces. Its basepoint is removed temporarily and restored
inside the literal trace, so no puncture or side certificate is assumed. -/
theorem actual_internal_loop_domain_two_faces
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M)
    (hb : b.val.map 0 = b.val.map 1) (D : Set S)
    (hD : IsOpen D) (hcD : IsConnected D) (hbin : b.val.image ⊆ D) :
    ∃ F : Finset (Set S), F.card = 2 ∧
      ∀ V, IsComplementComponent (Dᶜ ∪ b.val.image) V ↔ V ∈ F := by
  have hc := actual_open_puncture_connected M hD hcD (b.val.map 0)
  have hopen : IsOpen (D \ {b.val.map 0}) := by
    letI : T2Space S := M.sphere.symm.t2Space
    exact hD.sdiff isClosed_singleton
  have hbase : b.val.map 0 ∉ D \ {b.val.map 0} := fun h => h.2 rfl
  have hin : arcInterior M b ⊆ D \ {b.val.map 0} := by
    intro x hx
    refine ⟨hbin hx.1,?_⟩
    intro he
    exact hx.2 (Set.mem_singleton_iff.mp he ▸ b.val.start_marked)
  obtain ⟨F,hcard,hF⟩ := actual_loop_domain_split_faces M b hb hopen hc hbase hin
  have heq : (D \ {b.val.map 0})ᶜ ∪ b.val.image = Dᶜ ∪ b.val.image := by
    ext x
    simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    constructor
    · rintro (hx | hx)
      · by_cases hxD : x ∈ D
        · right
          have he : x = b.val.map 0 := by tauto
          exact he ▸ Set.mem_range_self 0
        · exact Or.inl hxD
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact Or.inl (fun h => hx h.1)
      · exact Or.inr hx
  refine ⟨F,hcard,?_⟩
  intro V
  rw [← heq]
  exact hF V

/-- For disjoint actual loops, one disc of the second loop has closure wholly
inside the disc of the first which contains its trace. -/
theorem actual_disjoint_loop_inner_disc
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1) (hb : b.val.map 0 = b.val.map 1)
    (hdis : Disjoint a.val.image b.val.image) :
    ∃ D L : Set S, IsComplementComponent a.val.image D ∧ IsOpen D ∧
      b.val.image ⊆ D ∧ IsComplementComponent b.val.image L ∧
      IsOpen L ∧ frontier L = b.val.image ∧ closure L ⊆ D := by
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨A⟩ := markedLoop_disc_decomposition_exists M a.val ha
  obtain ⟨B⟩ := markedLoop_disc_decomposition_exists M b.val hb
  have hbavoid : b.val.image ⊆ a.val.imageᶜ := fun x hx h => Set.disjoint_left.mp hdis h hx
  let D := connectedComponentIn a.val.imageᶜ (b.val.map 0)
  have hD : IsComplementComponent a.val.image D := complementComponent_iff_componentIn.mpr
    ⟨b.val.map 0,hbavoid (Set.mem_range_self 0),rfl⟩
  obtain ⟨i,hi⟩ := (A.all_components D).1 hD
  have hbD : b.val.image ⊆ D := (markedArc_image_connected b.val).isPreconnected.subset_connectedComponentIn
    (Set.mem_range_self 0) hbavoid
  have haavoid : a.val.image ⊆ b.val.imageᶜ := fun x hx h => Set.disjoint_left.mp hdis hx h
  let O := connectedComponentIn b.val.imageᶜ (a.val.map 0)
  have hO : IsComplementComponent b.val.image O := complementComponent_iff_componentIn.mpr
    ⟨a.val.map 0,haavoid (Set.mem_range_self 0),rfl⟩
  obtain ⟨j,hj⟩ := (B.all_components O).1 hO
  have haO : a.val.image ⊆ O := (markedArc_image_connected a.val).isPreconnected.subset_connectedComponentIn
    (Set.mem_range_self 0) haavoid
  obtain ⟨k,_,hkj⟩ := Finset.exists_mem_ne (by simp : 1 < (Finset.univ : Finset (Fin 2)).card) j
  have hsideDis : Disjoint (B.side k) (B.side j) := by
    fin_cases k <;> fin_cases j
    · exact False.elim (hkj rfl)
    · exact B.disjoint
    · exact B.disjoint.symm
    · exact False.elim (hkj rfl)
  have hLavoid : B.side k ⊆ a.val.imageᶜ := by
    intro x hx hxa
    exact Set.disjoint_left.mp hsideDis hx (hj ▸ haO hxa)
  have hpcl : b.val.map 0 ∈ closure (B.side k) := frontier_subset_closure
    ((B.discs k).boundary.symm ▸ Set.mem_range_self 0)
  have hDopen : IsOpen D := hi ▸ (A.discs i).open_side
  obtain ⟨x,hxD,hxL⟩ := Set.Nonempty.of_closure
    ⟨b.val.map 0,hDopen.inter_closure ⟨hbD (Set.mem_range_self 0),hpcl⟩⟩
  have hLD : B.side k ⊆ D := by
    have hh := (B.discs k).component.2.1.isPreconnected.subset_connectedComponentIn hxL hLavoid
    have he : connectedComponentIn a.val.imageᶜ x = D := by
      exact (connectedComponentIn_eq hxD).symm
    exact he ▸ hh
  refine ⟨D,B.side k,hD,hDopen,hbD,(B.discs k).component,(B.discs k).open_side,
    (B.discs k).boundary,?_⟩
  rw [(B.discs k).closure_eq]
  exact Set.union_subset hLD hbD

/-- A two-trace face contacting two disjoint loops separates their actual
full-graph components. Exact internal-loop face exhaustion supplies the
separation; no annulus or component-forest premise is assumed. -/
theorem actual_disjoint_loops_face_separates_graph_components
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M) (a b : ι)
    (ha : (r a).val.map 0 = (r a).val.map 1)
    (hb : (r b).val.map 0 = (r b).val.map 1)
    (hdis : Disjoint (r a).val.image (r b).val.image)
    (U : Set S) (hU : IsComplementComponent (⋃ v, (r v).val.image) U)
    (hUK : IsComplementComponent ((r a).val.image ∪ (r b).val.image) U)
    (htA : (frontier U ∩ arcInterior M (r a)).Nonempty)
    (htB : (frontier U ∩ arcInterior M (r b)).Nonempty) :
    connectedComponentIn (⋃ v, (r v).val.image) ((r a).val.map 0) ≠
      connectedComponentIn (⋃ v, (r v).val.image) ((r b).val.map 0) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨D,L,hD,hDopen,hbD,hL,hLopen,hLfr,hLclD⟩ :=
    actual_disjoint_loop_inner_disc M (r a) (r b) ha hb hdis
  have hUL : U ≠ L := by
    intro he
    obtain ⟨z,hzfr,hza⟩ := htA
    have hzB : z ∈ (r b).val.image := hLfr ▸ (he ▸ hzfr)
    exact Set.disjoint_left.mp hdis hza.1 hzB
  have hUD : U ⊆ D := by
    obtain ⟨z,hzfr,hzb⟩ := htB
    obtain ⟨x,hxD,hxU⟩ := Set.Nonempty.of_closure
      ⟨z,hDopen.inter_closure ⟨hbD hzb.1,frontier_subset_closure hzfr⟩⟩
    have havoid : U ⊆ (r a).val.imageᶜ := fun y hy h => hUK.2.2.1 hy (Or.inl h)
    have hh := hUK.2.1.isPreconnected.subset_connectedComponentIn hxU havoid
    obtain ⟨w,hw,he⟩ := complementComponent_iff_componentIn.mp hD
    have hx : x ∈ connectedComponentIn (r a).val.imageᶜ w := he ▸ hxD
    rw [← connectedComponentIn_eq hx,← he] at hh
    exact hh
  have haOut : (r a).val.image ⊆ Dᶜ := fun x hx h => hD.2.2.1 h hx
  have hUlocal : IsComplementComponent (Dᶜ ∪ (r b).val.image) U :=
    complementComponent_of_graph_enlargement hUK (Set.union_subset_union_left _ haOut)
      (Set.disjoint_left.mpr (by
        intro x hx h
        rcases h with h | h
        · exact h (hUD hx)
        · exact hUK.2.2.1 hx (Or.inr h)))
  have hLlocal : IsComplementComponent (Dᶜ ∪ (r b).val.image) L :=
    complementComponent_of_graph_enlargement hL Set.subset_union_right
      (Set.disjoint_left.mpr (by
        intro x hx h
        rcases h with h | h
        · exact h (hLclD (subset_closure hx))
        · exact hL.2.2.1 hx h))
  obtain ⟨F,hcard,hF⟩ := actual_internal_loop_domain_two_faces M (r b) hb D hDopen hD.2.1 hbD
  have hpairsub : {U,L} ⊆ F := by
    intro V hV
    rcases Finset.mem_insert.mp hV with hV | hV
    · exact hV ▸ (hF U).1 hUlocal
    · have he : V = L := Finset.mem_singleton.mp hV
      exact he ▸ (hF L).1 hLlocal
  have hpair : F = {U,L} := (Finset.eq_of_subset_of_card_le hpairsub
    (by simp [hUL,hcard])).symm
  have hcover : D \ (r b).val.image ⊆ U ∪ L := by
    intro x hx
    have hxK : x ∈ (Dᶜ ∪ (r b).val.image)ᶜ := by simpa using hx
    let V := connectedComponentIn (Dᶜ ∪ (r b).val.image)ᶜ x
    have hV : IsComplementComponent (Dᶜ ∪ (r b).val.image) V :=
      complementComponent_iff_componentIn.mpr ⟨x,hxK,rfl⟩
    have hVF := (hF V).1 hV
    rw [hpair] at hVF
    have hxV : x ∈ V := mem_connectedComponentIn hxK
    rcases Finset.mem_insert.mp hVF with he | he
    · exact Or.inl (he ▸ hxV)
    · exact Or.inr (Finset.mem_singleton.mp he ▸ hxV)
  have hGcover : (⋃ v, (r v).val.image) ⊆ closure L ∪ Dᶜ := by
    intro x hxG
    by_cases hxD : x ∈ D
    · left
      by_cases hxb : x ∈ (r b).val.image
      · exact frontier_subset_closure (hLfr.symm ▸ hxb)
      · rcases hcover ⟨hxD,hxb⟩ with hxU | hxL
        · exact False.elim (hU.2.2.1 hxU hxG)
        · exact subset_closure hxL
    · exact Or.inr hxD
  intro hsame
  let C := connectedComponentIn (⋃ v, (r v).val.image) ((r a).val.map 0)
  have haG : (r a).val.map 0 ∈ ⋃ v, (r v).val.image := Set.mem_iUnion.mpr ⟨a,Set.mem_range_self 0⟩
  have hbG : (r b).val.map 0 ∈ ⋃ v, (r v).val.image := Set.mem_iUnion.mpr ⟨b,Set.mem_range_self 0⟩
  have haC : (r a).val.map 0 ∈ C := mem_connectedComponentIn haG
  have hbC : (r b).val.map 0 ∈ C := by
    change (r b).val.map 0 ∈ connectedComponentIn (⋃ v, (r v).val.image) ((r a).val.map 0)
    rw [hsame]
    exact mem_connectedComponentIn hbG
  have hC : IsPreconnected C := (isConnected_connectedComponentIn_iff.mpr haG).isPreconnected
  have hh := isPreconnected_closed_iff.mp hC (closure L) Dᶜ isClosed_closure hDopen.isClosed_compl
    ((connectedComponentIn_subset _ _).trans hGcover)
    ⟨(r b).val.map 0,hbC,frontier_subset_closure (hLfr.symm ▸ Set.mem_range_self 0)⟩
    ⟨(r a).val.map 0,haC,haOut (Set.mem_range_self 0)⟩
  obtain ⟨x,hxC,hxL,hxOut⟩ := hh
  exact hxOut (hLclD hxL)

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set
open scoped Classical
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Two distinct contacting traces supporting the entire frontier of an unmarked
actual full-graph face, with starts in the same actual graph component, are
nonloops with equal unordered endpoint sets or loops with the same basepoint.
Geometric helper for the all-bad case of Lemma 8.5(iv), source §§8–9. -/
theorem actual_unmarked_two_trace_same_component_shape
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (U : Set S)
    (hU : IsComplementComponent (⋃ k, (r k).val.image) U)
    (hfree : ∀ b ∈ M.cover.branch, b ∉ U)
    (i j : {v // v ∈ sigma}) (hij : i ≠ j)
    (hi : (frontier U ∩ arcInterior M (r i)).Nonempty)
    (hj : (frontier U ∩ arcInterior M (r j)).Nonempty)
    (hboundary : frontier U ⊆ (r i).val.image ∪ (r j).val.image)
    (hsame : connectedComponentIn (⋃ k, (r k).val.image) ((r i).val.map 0) =
      connectedComponentIn (⋃ k, (r k).val.image) ((r j).val.map 0)) :
    ((r i).val.map 0 ≠ (r i).val.map 1 ∧
      (r j).val.map 0 ≠ (r j).val.map 1 ∧
      markedArcEndset (r i).val = markedArcEndset (r j).val) ∨
    ((r i).val.map 0 = (r i).val.map 1 ∧
      (r j).val.map 0 = (r j).val.map 1 ∧
      (r i).val.map 0 = (r j).val.map 0) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have hGclosed : IsClosed (⋃ k, (r k).val.image) :=
    isClosed_iUnion_of_finite (fun k => (isCompact_range (r k).val.continuous).isClosed)
  have hUK : IsComplementComponent ((r i).val.image ∪ (r j).val.image) U :=
    actual_face_reduce_to_boundary_subgraph M _ _ U hGclosed
      (Set.union_subset (Set.subset_iUnion (fun k => (r k).val.image) i)
        (Set.subset_iUnion (fun k => (r k).val.image) j)) hU hboundary
  have hbad' : @CurveGenusTwo.Filtration.badVertices (EssentialArcClass M) S
      M.exactEdgeClassDecEq (actualArcLabels M) sigma = sigma := by
    convert hbad using 1 <;> congr 1
    exact Subsingleton.elim _ _
  by_cases ha : (r i).val.map 0 = (r i).val.map 1
  · by_cases hb : (r j).val.map 0 = (r j).val.map 1
    · right
      refine ⟨ha,hb,?_⟩
      by_contra hne
      have hdis : Disjoint (r i).val.image (r j).val.image := by
        apply Set.disjoint_left.mpr
        intro x hxi hxj
        have hh := markedArc_disjoint_interiors_inter_image (r i).val (r j).val (hd i j hij)
        have hx := hh ▸ (show x ∈ (r i).val.image ∩ (r j).val.image from ⟨hxi,hxj⟩)
        have hxi : x = (r i).val.map 0 := by simpa [markedArcEndset,ha] using hx.1
        have hxj : x = (r j).val.map 0 := by simpa [markedArcEndset,hb] using hx.2
        exact hne (hxi.symm.trans hxj)
      exact actual_disjoint_loops_face_separates_graph_components M r i j ha hb hdis U
        hU hUK hi hj hsame
    · exact False.elim (actual_full_face_not_mixed_two_trace M r hr hd hbad' U hU i j hij
        hUK hj ha hb)
  · by_cases hb : (r j).val.map 0 = (r j).val.map 1
    · exact False.elim (actual_full_face_not_mixed_two_trace M r hr hd hbad' U hU j i hij.symm
        (by simpa [Set.union_comm] using hUK) hi hb ha)
    · left
      refine ⟨ha,hb,?_⟩
      by_contra hne
      obtain ⟨p,hpU⟩ := hUK.1
      have hc := actual_nonparallel_nonloop_pair_complement_connected M (r i) (r j) ha hb
        (hd i j hij) hne p (hUK.2.2.1 hpU)
      have hUwhole : U = ((r i).val.image ∪ (r j).val.image)ᶜ :=
        (hUK.2.2.2 _ hc (fun x hx => hUK.2.2.1 hx) (fun x hx => hx)).symm
      obtain ⟨W,hW,hWU,hcontact⟩ := actual_boundary_subgraph_second_incident_face M r hr hd hbad'
        ((r i).val.image ∪ (r j).val.image) U
        ((isCompact_range (r i).val.continuous).isClosed.union (isCompact_range (r j).val.continuous).isClosed)
        (Set.union_subset (Set.subset_iUnion (fun v => (r v).val.image) i)
          (Set.subset_iUnion (fun v => (r v).val.image) j)) hU hUK j Set.subset_union_right hj
      have hWwhole : W = ((r i).val.image ∪ (r j).val.image)ᶜ :=
        (hW.2.2.2 _ hc (fun x hx => hW.2.2.1 hx) (fun x hx => hx)).symm
      exact hWU (hWwhole.trans hUwhole.symm)


end CurveComplex.HyperellipticModel
