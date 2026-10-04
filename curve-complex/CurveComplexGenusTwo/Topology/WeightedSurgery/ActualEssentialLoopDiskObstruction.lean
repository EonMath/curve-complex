import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualMarkFreeBigonLocalization
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open Set Topology Schoenflies CurveComplex
namespace CurveComplex.HyperellipticModel

theorem actual_curve_of_marked_interval_loop {X : Type*} [TopologicalSpace X] [T2Space X]
    (l : C(Interval, X)) (hend : l 0 = l 1)
    (hcoll : ∀ s t, l s = l t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    ∃ c : Curve X, c.image = Set.range l := by
  let r := AddCircle.EndpointIdent (1 : ℝ) 0
  let j : Icc (0 : ℝ) (0 + 1) → Interval := fun t => ⟨t.val, by simpa using t.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hrespect : ∀ a b, r a b → l (j a) = l (j b) := by
    rintro a b ⟨⟩
    simpa [j] using hend
  let L : Quot r → X := Quot.lift (fun t => l (j t)) hrespect
  have hL : Continuous L := continuous_quot_lift _ (l.continuous.comp hj)
  have hLi : Function.Injective L := by
    intro a b
    induction a using Quot.inductionOn with | h a =>
      induction b using Quot.inductionOn with | h b =>
        intro hab
        rcases hcoll (j a) (j b) hab with he | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · apply congrArg (Quot.mk r)
          exact Subtype.ext (congrArg (fun t : Interval => t.val) he)
        · have ha' : a = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
          have hb' : b = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
          subst a; subst b
          exact Quot.sound AddCircle.EndpointIdent.mk
        · have ha' : a = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
          have hb' : b = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
          subst a; subst b
          exact (Quot.sound AddCircle.EndpointIdent.mk).symm
  let e : Circle ≃ₜ Quot r :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans
      (AddCircle.homeoIccQuot (1 : ℝ) 0)
  let c : Curve X := ⟨L ∘ e, ((hL.comp e.continuous).isClosedEmbedding (hLi.comp e.injective)).isEmbedding⟩
  refine ⟨c, ?_⟩
  change range (L ∘ e) = range l
  rw [e.surjective.range_comp]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quot.inductionOn with | h t =>
      exact ⟨j t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Quot.mk r ⟨t.val, by simpa using t.property⟩, rfl⟩


variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The actual open part of an embedded disk is a complementary component
of its actual parametrized boundary; no component receipt is assumed. -/
theorem actual_embedded_disk_interior_component
    (M : HyperellipticModel E S)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : IsEmbedding d) :
    IsComplementComponent
      (d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
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
  let B : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 1
  let D : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := {x | x.val ∈ B}
  let U := d '' D
  let H := d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
  have hDU : IsConnected D := by
    have he : Subtype.val '' D = B := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩; exact hx
      · intro hz; exact ⟨⟨z,Metric.ball_subset_closedBall hz⟩,hz,rfl⟩
    refine ⟨⟨⟨0,by simp⟩,by simp [D,B]⟩,?_⟩
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    rw [he]
    exact (Metric.isConnected_ball (by norm_num)).isPreconnected
  have hc : IsConnected U := hDU.image d d.continuous.continuousOn
  have ho : IsOpen U := LocalSurgery.embedded_surface_disk_interior_isOpen d hd
  have hfree : U ⊆ Hᶜ := by
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have heq := hd.injective he
    subst y
    have hlt : ‖x.val‖ < 1 := by simpa only [D,B,Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hx
    have he : ‖x.val‖ = 1 := by simpa [Metric.mem_sphere,dist_zero_right] using hy
    linarith
  have hcl : closure U ⊆ range d :=
    closure_minimal (Set.image_subset_range _ _) (isCompact_range d.continuous).isClosed
  have hboundary : closure U \ U ⊆ H := by
    intro z hz
    obtain ⟨x,hx⟩ := hcl hz.1
    refine ⟨x,?_,hx⟩
    have hn : ‖x.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
    have hnnot : ¬ ‖x.val‖ < 1 := by
      intro hl
      exact hz.2 ⟨x,by simpa only [D,B,Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hl,hx⟩
    simpa [Metric.mem_sphere,dist_zero_right] using le_antisymm hn (not_lt.mp hnnot)
  refine ⟨hc.nonempty,hc,hfree,?_⟩
  intro V hV hUV hVH
  apply Set.Subset.antisymm
  · apply hV.isPreconnected.subset_of_closure_inter_subset ho
    · obtain ⟨x,hx⟩ := hc.nonempty
      exact ⟨x,hUV hx,hx⟩
    · intro x hx
      by_contra hn
      exact hVH hx.2 (hboundary ⟨hx.1,hn⟩)
  · exact hUV

/-- An essential marked loop cannot be contained in an ACTUAL embedded disk
with mark-free interior. The boundary is allowed to contain its base mark. -/
theorem actual_essential_loop_not_in_interior_free_disk
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (hloop : a.val.map (0 : Interval) = a.val.map (1 : Interval))
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : IsEmbedding d)
    (hmarks : Disjoint
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (M.cover.branch : Set S)) :
    ¬ a.val.image ⊆ Set.range d := by
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
  intro hain
  obtain ⟨c,hc⟩ := actual_curve_of_marked_interval_loop
    (⟨a.val.map,a.val.continuous⟩ : C(Interval,S)) hloop a.val.injective_except_loop_closure
  obtain ⟨e,he,heb,hesub⟩ := LocalSurgery.curve_in_embedded_disk_bounds_subdisk c d hd
    (hc.trans_subset hain)
  have hU := actual_embedded_disk_interior_component M e he
  rw [heb,hc] at hU
  have heinside :
      e '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
      d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    rw [← LocalSurgery.embedded_surface_disk_interior_eq d hd]
    exact (LocalSurgery.embedded_surface_disk_interior_isOpen e he).subset_interior_iff.mpr
      (fun z hz => hesub (Set.image_subset_range _ _ hz))
  have hess := a.property
  change a.val.map (0 : Interval) ≠ a.val.map (1 : Interval) ∨
    ∀ U, IsComplementComponent a.val.image U → ∃ b, b ∈ M.cover.branch ∧ b ∈ U at hess
  rcases hess with hn | hess
  · exact hn hloop
  · obtain ⟨b,hb,hbU⟩ := hess _ hU
    exact Set.disjoint_left.mp hmarks (heinside hbU) hb

#print axioms actual_curve_of_marked_interval_loop
#print axioms actual_embedded_disk_interior_component
#print axioms actual_essential_loop_not_in_interior_free_disk
end CurveComplex.HyperellipticModel
