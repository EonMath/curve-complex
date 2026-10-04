import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Intersection.SphereRegionTransport
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import Schoenflies.JordanSchoenflies

set_option maxHeartbeats 2000000

noncomputable section
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Produce a marked stereographic puncture outside the WHOLE actual disk;
marks at either corner are allowed. -/
theorem actual_two_side_disk_has_exterior_mark
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (D : ActualMarkedTwoSideDisk M a b) :
    ∃ p ∈ M.cover.branch, p ∉ range D.disk := by
  classical
  have hex : ∃ p ∈ M.cover.branch, p ∉ ({D.firstCorner,D.secondCorner} : Finset S) := by
    by_contra hn
    have hsub : M.cover.branch ⊆ {D.firstCorner,D.secondCorner} := by
      intro p hp
      by_contra hc
      exact hn ⟨p,hp,hc⟩
    have hcard := Finset.card_le_card hsub
    rw [M.cover.branch_card] at hcard
    have htwo : ({D.firstCorner,D.secondCorner} : Finset S).card ≤ 2 := Finset.card_insert_le _ _
    omega
  obtain ⟨p,hp,hn⟩ := hex
  refine ⟨p,hp,fun hpd => hn ?_⟩
  simpa using D.marks_are_corners p hpd hp

private theorem embedded_side_isArcBetween (f : C(Interval,Plane))
    (hf : IsEmbedding f) : IsArcBetween (range f) (f 0) (f 1) := by
  let fc : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
  have hfc : Continuous fc := f.continuous.comp continuous_projIcc
  have he (t : Interval) : fc t = f t := by
    simp [fc,Set.projIcc_of_mem zero_le_one t.property]
  refine ⟨fc,hfc.continuousOn,?_,?_,he 0,he 1⟩
  · intro t ht u hu h
    exact congrArg Subtype.val (hf.injective (by
      simpa only [← he] using h : f ⟨t,ht⟩ = f ⟨u,hu⟩))
  · ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,(he ⟨t,ht⟩).symm⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t,t.property,he t⟩

/-- An actual two-side disk PRODUCES its whole planar bigon chart and exact
open-disk correspondence. No surface chart or enlarged support is assumed;
selected arcs may be loops and corners may be marked or unmarked. -/
theorem actual_two_side_disk_produces_bigon_chart
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (D : ActualMarkedTwoSideDisk M a b) :
    ∃ (f : Plane → S) (A B : Set Plane) (p q : Plane),
      IsOpenEmbedding f ∧ IsArcBetween A p q ∧ IsArcBetween B p q ∧
      A ∪ B = modelCurve ∧
      f '' A = range D.firstSide ∧ f '' B = range D.secondSide ∧
      f p = D.firstCorner ∧ f q = D.secondCorner ∧
      f '' Plane.openSquare 0 1 = D.openInterior := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨v,hvm,hv⟩ := actual_two_side_disk_has_exterior_mark M a b D
  let e := M.puncturedPlane v
  let j : range D.disk → {z : S // z ≠ v} :=
    fun z => ⟨z.val,fun hz => hv (hz ▸ z.property)⟩
  let d : C(Metric.closedBall (0 : Plane) 1,Plane) :=
    ⟨fun x => e ⟨D.disk x,fun h => hv (h ▸ Set.mem_range_self x)⟩,by fun_prop⟩
  have firstDisk (t : Interval) : D.firstSide t ∈ range D.disk := by
    apply image_subset_range D.disk _
    rw [D.boundary_eq]
    exact Or.inl (Set.mem_range_self t)
  have secondDisk (t : Interval) : D.secondSide t ∈ range D.disk := by
    apply image_subset_range D.disk _
    rw [D.boundary_eq]
    exact Or.inr (Set.mem_range_self t)
  let g : C(Interval,Plane) :=
    ⟨fun t => e ⟨D.firstSide t,fun h => hv (h ▸ firstDisk t)⟩,by fun_prop⟩
  let h : C(Interval,Plane) :=
    ⟨fun t => e ⟨D.secondSide t,fun hh => hv (hh ▸ secondDisk t)⟩,by fun_prop⟩
  have hd : IsEmbedding d := (d.continuous.isClosedEmbedding (by
    intro x y hxy
    exact D.disk_embedded.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
  have hg : IsEmbedding g := (g.continuous.isClosedEmbedding (by
    intro x y hxy
    exact D.first_embedded.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
  have hh : IsEmbedding h := (h.continuous.isClosedEmbedding (by
    intro x y hxy
    exact D.second_embedded.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
  have hg0 : g 0 = h 0 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact D.first_zero.trans D.second_zero.symm
  have hg1 : g 1 = h 1 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact D.first_one.trans D.second_one.symm
  have hgA := embedded_side_isArcBetween g hg
  have hhB : IsArcBetween (range h) (g 0) (g 1) := by rw [hg0,hg1]; exact embedded_side_isArcBetween h hh
  have hc : IsJordanCurve (range g ∪ range h) := IsJordanCurve.of_two_arcs hgA hhB.reverse (by
    rintro z ⟨t,ht⟩ ⟨s,hs⟩
    have heq : D.firstSide t = D.secondSide s := congrArg Subtype.val (e.injective (ht.trans hs.symm))
    have hm : D.firstSide t ∈ ({D.firstCorner,D.secondCorner} : Set S) :=
      D.sides_inter ▸ ⟨Set.mem_range_self t,⟨s,heq.symm⟩⟩
    rcases mem_insert_iff.mp hm with hm | hm
    · left
      have ht0 : t=0 := D.first_embedded.injective (hm.trans D.first_zero.symm)
      exact ht.symm.trans (congrArg g ht0)
    · right
      have ht1 : t=1 := D.first_embedded.injective ((mem_singleton_iff.mp hm).trans D.first_one.symm)
      exact ht.symm.trans (congrArg g ht1))
  have hbd : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range g ∪ range h := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hxs : D.disk x ∈ range D.firstSide ∪ range D.secondSide := by
        rw [← D.boundary_eq]
        exact mem_image_of_mem D.disk hx
      rcases hxs with ⟨t,ht⟩ | ⟨t,ht⟩
      · left; refine ⟨t,?_⟩; apply congrArg e; apply Subtype.ext; exact ht
      · right; refine ⟨t,?_⟩; apply congrArg e; apply Subtype.ext; exact ht
    · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
      · have htB : D.firstSide t ∈ D.disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
          rw [D.boundary_eq]; exact Or.inl (Set.mem_range_self t)
        obtain ⟨x,hx,hxt⟩ := htB
        refine ⟨x,hx,?_⟩; apply congrArg e; apply Subtype.ext; exact hxt
      · have htB : D.secondSide t ∈ D.disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
          rw [D.boundary_eq]; exact Or.inr (Set.mem_range_self t)
        obtain ⟨x,hx,hxt⟩ := htB
        refine ⟨x,hx,?_⟩; apply congrArg e; apply Subtype.ext; exact hxt
  have hrange := CurveComplex.embedded_disc_range_eq_closed_inside d hd _ hc hbd
  have hi : d '' {x | x.val ∈ Metric.ball (0 : Plane) 1} = inside (range g ∪ range h) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      rcases hrange ▸ Set.mem_range_self x with hi | hb
      · exact hi
      · obtain ⟨y,hy,hyx⟩ := hbd.symm ▸ hb
        have he := congrArg Subtype.val (hd.injective hyx)
        have hyxS : x.val ∈ Metric.sphere (0 : Plane) 1 := he ▸ hy
        have hnlt : ‖x.val‖ < (1 : ℝ) := by
          change dist x.val 0 < 1 at hx
          simpa only [dist_zero_right] using hx
        have hneq : ‖x.val‖ = (1 : ℝ) := by
          change dist x.val 0 = 1 at hyxS
          simpa only [dist_zero_right] using hyxS
        exact False.elim (ne_of_lt hnlt hneq)
    · intro hz
      have hzR : z ∈ range d := by rw [hrange]; exact Or.inl hz
      obtain ⟨x,hx⟩ := hzR
      refine ⟨x,?_,hx⟩
      have hn : ‖x.val‖ ≤ (1 : ℝ) := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
      have hnb : x.val ∉ Metric.sphere (0 : Plane) 1 := by
        intro hxb
        have hzB : z ∈ range g ∪ range h := by rw [← hbd,← hx]; exact mem_image_of_mem d hxb
        exact Set.disjoint_right.mp (disjoint_curve_inside _) hz hzB
      change dist x.val 0 < 1
      rw [dist_zero_right]
      exact lt_of_le_of_ne hn (by simpa only [Metric.mem_sphere,dist_zero_right] using hnb)
  obtain ⟨ec⟩ := IsJordanCurve.modelCurve_homeomorph hc
  obtain ⟨φ,hφ⟩ := jordan_schoenflies_of_homeomorph isJordanCurve_modelCurve hc ec
  have hφC : φ '' modelCurve = range g ∪ range h := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩; rw [hφ ⟨x,hx⟩]; exact (ec ⟨x,hx⟩).property
    · intro hz
      let x := ec.symm ⟨z,hz⟩
      refine ⟨x.val,x.property,?_⟩
      rw [hφ x]; exact congrArg Subtype.val (ec.apply_symm_apply _)
  have hφI : φ '' Plane.openSquare 0 1 = inside (range g ∪ range h) := by
    rw [← inside_modelCurve]
    simpa only [hφC] using CurveComplex.jordan_inside_homeomorph_image φ modelCurve
  let f : Plane → S := M.planeToSphere v ∘ φ
  let A := φ.symm '' range g
  let B := φ.symm '' range h
  let p := φ.symm (g 0)
  let q := φ.symm (g 1)
  have hcancel (K : Set Plane) : φ '' (φ.symm '' K) = K := by
    ext z; simp
  have hgs (t) : M.planeToSphere v (g t) = D.firstSide t := congrArg Subtype.val (e.symm_apply_apply _)
  have hhs (t) : M.planeToSphere v (h t) = D.secondSide t := congrArg Subtype.val (e.symm_apply_apply _)
  refine ⟨f,A,B,p,q,(M.planeToSphere_isOpenEmbedding v).comp φ.isOpenEmbedding,
    hgA.image_of_injOn (Set.subset_univ _) φ.symm.continuous.continuousOn φ.symm.injective.injOn,
    hhB.image_of_injOn (Set.subset_univ _) φ.symm.continuous.continuousOn φ.symm.injective.injOn,?_,?_,?_,?_,?_,?_⟩
  · change φ.symm '' range g ∪ φ.symm '' range h = modelCurve
    rw [← image_union,← hφC]
    ext z; simp
  · change (M.planeToSphere v ∘ φ) '' (φ.symm '' range g) = _
    rw [image_comp,hcancel,← range_comp]; exact congrArg range (funext hgs)
  · change (M.planeToSphere v ∘ φ) '' (φ.symm '' range h) = _
    rw [image_comp,hcancel,← range_comp]; exact congrArg range (funext hhs)
  · change M.planeToSphere v (φ (φ.symm (g 0))) = _
    rw [φ.apply_symm_apply,hgs,D.first_zero]
  · change M.planeToSphere v (φ (φ.symm (g 1))) = _
    rw [φ.apply_symm_apply,hgs,D.first_one]
  · change (M.planeToSphere v ∘ φ) '' Plane.openSquare 0 1 = _
    rw [image_comp,hφI,← hi,image_image]
    apply Set.image_congr
    intro x hx
    exact congrArg Subtype.val (e.symm_apply_apply _)

#print axioms actual_two_side_disk_has_exterior_mark
#print axioms actual_two_side_disk_produces_bigon_chart
end CurveComplex.HyperellipticModel
