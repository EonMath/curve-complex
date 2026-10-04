import Mathlib
import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.Plane
import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Topology.ChartLift
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport

namespace CurveComplex.ArcFinitePosition

/-- A genuine supported endpoint rotation. On the inner half-disk it rotates
by the prescribed angle; the endpoint and disk exterior stay fixed at all times. -/
theorem supported_complex_endpoint_rotation (R θ : ℝ) (hR : 0 < R) :
    ∃ H : AmbientIsotopy ℂ,
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t z, R ≤ ‖z‖ → H.map (t,z) = z) ∧
      (∀ t z, ‖H.map (t,z)‖ = ‖z‖) ∧
      (∀ z, ‖z‖ ≤ R/2 → H.finalMap z = (Circle.exp θ : ℂ) * z) := by
  let cut : ℝ → ℝ := fun r => min 1 (max 0 (2-2*r/R))
  have hcut : Continuous cut := by dsimp [cut]; fun_prop
  let twist : ℝ → ℂ → ℂ := fun a z => (Circle.exp (a * cut ‖z‖) : ℂ) * z
  have hnorm (a : ℝ) (z : ℂ) : ‖twist a z‖ = ‖z‖ := by
    change ‖(Circle.exp (a * cut ‖z‖) : ℂ) * z‖ = ‖z‖
    rw [norm_mul, Circle.norm_coe, one_mul]
  have hcont (a : ℝ) : Continuous (twist a) := by
    exact (Circle.exp.continuous.comp
      (continuous_const.mul (hcut.comp continuous_norm))).subtype_val.mul continuous_id
  have hinv (a : ℝ) (z : ℂ) : twist (-a) (twist a z) = z := by
    change (Circle.exp (-a * cut ‖twist a z‖) : ℂ) *
      ((Circle.exp (a * cut ‖z‖) : ℂ) * z) = z
    rw [hnorm]
    rw [← mul_assoc, ← Circle.coe_mul, ← Circle.exp_add]
    have he : -a * cut ‖z‖ + a * cut ‖z‖ = 0 := by ring
    rw [he]
    simp
  let h (a : ℝ) : ℂ ≃ₜ ℂ := {
    toEquiv := {
      toFun := twist a
      invFun := twist (-a)
      left_inv := hinv a
      right_inv := by intro z; simpa using hinv (-a) z }
    continuous_toFun := hcont a
    continuous_invFun := hcont (-a) }
  let H : AmbientIsotopy ℂ := {
    map := ⟨fun p => twist (p.1.val * θ) p.2, by
      exact (Circle.exp.continuous.comp
        (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
          (hcut.comp (continuous_norm.comp continuous_snd)))).subtype_val.mul continuous_snd⟩
    homeomorphism_at := fun t => ⟨h (t.val * θ), fun _ => rfl⟩
    at_zero := by intro z; simp [twist] }
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro t
    simp [H,twist]
  · intro t z hz
    have hc : cut ‖z‖ = 0 := by
      have hr : 2 - 2*‖z‖/R ≤ 0 := by
        have hdiv : 2 ≤ 2*‖z‖/R := (le_div_iff₀ hR).mpr (by nlinarith)
        linarith
      simp [cut,max_eq_left hr]
    simp [H,twist,hc]
  · intro t z
    exact hnorm _ _
  · intro z hz
    have hc : cut ‖z‖ = 1 := by
      have hr : 1 ≤ 2 - 2*‖z‖/R := by
        have hdiv : 2*‖z‖/R ≤ 1 := (div_le_iff₀ hR).mpr (by nlinarith)
        linarith
      simp [cut,min_eq_left (le_trans hr (le_max_right _ _))]
    simp [AmbientIsotopy.finalMap,H,twist,hc]

end CurveComplex.ArcFinitePosition

namespace CurveComplex.ArcFinitePosition
open Set

/-- A concrete angle avoids any finite list of forbidden endpoint directions. -/
theorem exists_angle_avoiding_finite_complex (F : Finset ℂ) :
    ∃ θ ∈ Icc (0:ℝ) 1, (Circle.exp θ : ℂ) ∉ F := by
  have hi : InjOn (fun θ : ℝ => (Circle.exp θ : ℂ)) (Icc 0 1) := by
    intro x hx y hy he
    apply Circle.exp_injOn_Icc (show (1:ℝ)-0 < 2*Real.pi by
      linarith [Real.pi_gt_three]) hx hy
    exact Subtype.ext he
  have hinf : (Set.range (fun x : Icc (0:ℝ) 1 => (Circle.exp x.val : ℂ))).Infinite := by
    letI : Infinite (Icc (0:ℝ) 1) := Set.Icc.infinite (by norm_num)
    have hi' : Function.Injective (fun x : Icc (0:ℝ) 1 => (Circle.exp x.val : ℂ)) := by
      intro x y h
      exact Subtype.ext (hi x.property y.property h)
    exact Set.infinite_range_of_injective hi'
  by_contra! hn
  apply hinf
  apply F.finite_toSet.subset
  rintro _ ⟨x,rfl⟩
  exact hn x.val x.property

/-- A new radial germ can be rotated away from all directions of a finite old
star. No pairwise-disjointness assumption between the new and old germs is used. -/
theorem finite_star_rotation_direction {J : Type*} [Fintype J]
    (v : ℂ) (hv : v ≠ 0) (w : J → ℂ) (hw : ∀ j, w j ≠ 0) :
    ∃ θ ∈ Icc (0:ℝ) 1,
      ∀ j, Disjoint (segment ℝ (0:ℂ) ((Circle.exp θ : ℂ)*v) \ {0})
        (segment ℝ (0:ℂ) (w j) \ {0}) := by
  classical
  let F : Finset ℂ := Finset.univ.image (fun j =>
    ((‖v‖ / ‖w j‖ : ℝ) : ℂ) * w j / v)
  obtain ⟨θ,hθ,havoid⟩ := exists_angle_avoiding_finite_complex F
  refine ⟨θ,hθ,?_⟩
  intro j
  apply Set.disjoint_left.mpr
  rintro x ⟨hx,hx0⟩ ⟨hy,_⟩
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨t,ht,htx⟩ := hx
  obtain ⟨s,hs,hsx⟩ := hy
  have he : t • ((Circle.exp θ : ℂ)*v) = s • w j := by
    simpa only [AffineMap.lineMap_apply_module,smul_zero,zero_add] using htx.trans hsx.symm
  have ht0 : t ≠ 0 := by
    intro h
    apply hx0
    apply Set.mem_singleton_iff.mpr
    rw [h] at htx
    simpa only [AffineMap.lineMap_apply_module,smul_zero,zero_add,zero_smul] using htx.symm
  have hn : t * ‖v‖ = s * ‖w j‖ := by
    have h := congrArg norm he
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,
      abs_of_nonneg hs.1,norm_mul,Circle.norm_coe,one_mul] using h
  have hnw : ‖w j‖ ≠ 0 := norm_ne_zero_iff.mpr (hw j)
  have hsEq : t * (‖v‖/‖w j‖) = s := by
    rw [← mul_div_assoc, div_eq_iff hnw]
    exact hn
  have hrot : (Circle.exp θ : ℂ)*v = (‖v‖/‖w j‖) • w j := by
    have he' : t • ((Circle.exp θ : ℂ)*v) = t • ((‖v‖/‖w j‖) • w j) := by
      rw [smul_smul,hsEq]
      exact he
    have hc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    exact mul_left_cancel₀ hc (by simpa only [Complex.real_smul] using he')
  have hbad : (Circle.exp θ : ℂ) = ((‖v‖/‖w j‖ : ℝ) : ℂ) * w j / v := by
    apply (eq_div_iff hv).mpr
    simpa only [Complex.real_smul] using hrot
  apply havoid
  rw [hbad]
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩

end CurveComplex.ArcFinitePosition

namespace CurveComplex.ArcFinitePosition
open Set

/-- The supported move actually separates a radial new germ from the finite
old star on its whole prefix, not only at a formal tangent vector. -/
theorem supported_radial_germ_separation {J : Type*} [Fintype J]
    (R : ℝ) (hR : 0 < R) (v : ℂ) (hv : v ≠ 0) (hlen : ‖v‖ ≤ R/2)
    (w : J → ℂ) (hw : ∀ j, w j ≠ 0) :
    ∃ H : AmbientIsotopy ℂ,
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t z, R ≤ ‖z‖ → H.map (t,z) = z) ∧
      (∀ t z, ‖H.map (t,z)‖ = ‖z‖) ∧
      ∀ j, Disjoint ((H.finalMap '' segment ℝ (0:ℂ) v) \ {0})
        (segment ℝ (0:ℂ) (w j) \ {0}) := by
  obtain ⟨θ,_,hdir⟩ := finite_star_rotation_direction v hv w hw
  obtain ⟨H,hzero,hout,hnorm,hinner⟩ := supported_complex_endpoint_rotation R θ hR
  have himage : H.finalMap '' segment ℝ (0:ℂ) v =
      segment ℝ (0:ℂ) ((Circle.exp θ : ℂ)*v) := by
    rw [segment_eq_image_lineMap,segment_eq_image_lineMap]
    ext z
    constructor
    · rintro ⟨x,⟨t,ht,rfl⟩,rfl⟩
      refine ⟨t,ht,?_⟩
      have htlen : ‖AffineMap.lineMap (0:ℂ) v t‖ ≤ R/2 := by
        simp only [AffineMap.lineMap_apply_module,smul_zero,zero_add,norm_smul,
          Real.norm_eq_abs,abs_of_nonneg ht.1]
        exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans hlen
      rw [hinner _ htlen]
      simp only [AffineMap.lineMap_apply_module,smul_zero,zero_add,Complex.real_smul]
      ring
    · rintro ⟨t,ht,rfl⟩
      refine ⟨AffineMap.lineMap (0:ℂ) v t,⟨t,ht,rfl⟩,?_⟩
      have htlen : ‖AffineMap.lineMap (0:ℂ) v t‖ ≤ R/2 := by
        simp only [AffineMap.lineMap_apply_module,smul_zero,zero_add,norm_smul,
          Real.norm_eq_abs,abs_of_nonneg ht.1]
        exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans hlen
      rw [hinner _ htlen]
      simp only [AffineMap.lineMap_apply_module,smul_zero,zero_add,Complex.real_smul]
      ring
  refine ⟨H,hzero,hout,hnorm,?_⟩
  intro j
  rw [himage]
  exact hdir j

end CurveComplex.ArcFinitePosition

namespace CurveComplex.ArcFinitePosition
open Schoenflies

noncomputable def planeComplexLinearEquiv : Plane ≃L[ℝ] ℂ :=
  (((EuclideanSpace.equiv (Fin 2) ℝ).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).trans Complex.equivRealProdCLM.symm)

/-- The supported endpoint rotation in the canonical plane coordinates. -/
theorem supported_plane_endpoint_rotation (o : Plane) (R θ : ℝ) (hR : 0 < R) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t, H.map (t,o) = o) ∧
      (∀ t z, R ≤ ‖planeComplexLinearEquiv (z-o)‖ → H.map (t,z) = z) ∧
      (∀ t z, ‖planeComplexLinearEquiv (H.map (t,z)-o)‖ =
        ‖planeComplexLinearEquiv (z-o)‖) ∧
      (∀ z, ‖planeComplexLinearEquiv (z-o)‖ ≤ R/2 →
        planeComplexLinearEquiv (H.finalMap z-o) =
          (Circle.exp θ : ℂ) * planeComplexLinearEquiv (z-o)) := by
  obtain ⟨G,hzero,hout,hnorm,hinner⟩ := supported_complex_endpoint_rotation R θ hR
  let T : Plane ≃ₜ ℂ := (Homeomorph.addRight (-o)).trans planeComplexLinearEquiv.toHomeomorph
  have hT (z : Plane) : T z = planeComplexLinearEquiv (z-o) := by
    simp [T,sub_eq_add_neg]
  have hTo : T o = 0 := by simp [hT]
  let H : AmbientIsotopy Plane := {
    map := ⟨fun z => T.symm (G.map (z.1,T z.2)),
      T.symm.continuous.comp (G.map.continuous.comp
        (continuous_fst.prodMk (T.continuous.comp continuous_snd)))⟩
    homeomorphism_at := by
      intro t
      obtain ⟨g,hg⟩ := G.homeomorphism_at t
      exact ⟨(T.trans g).trans T.symm,fun x => congrArg T.symm (hg (T x))⟩
    at_zero := by
      intro x
      exact (congrArg T.symm (G.at_zero (T x))).trans (T.symm_apply_apply x) }
  have hcoord (t : Interval) (z : Plane) : T (H.map (t,z)) = G.map (t,T z) :=
    T.apply_symm_apply _
  refine ⟨H,?_,?_,?_,?_⟩
  · intro t
    apply T.injective
    rw [hcoord,hTo,hzero]
  · intro t z hz
    apply T.injective
    rw [hcoord,hout t (T z) (by simpa [hT] using hz)]
  · intro t z
    rw [← hT, hcoord, ← hT]
    exact hnorm t (T z)
  · intro z hz
    rw [← hT, ← hT]
    change T (H.map (1,z)) = (Circle.exp θ : ℂ) * T z
    rw [hcoord]
    exact hinner (T z) (by simpa [hT] using hz)

end CurveComplex.ArcFinitePosition

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies CurveComplex.ArcFinitePosition
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A supported rotation at an actual marked endpoint. Its chart and compact
support are constructed from the sphere model and a prescribed open support.
All marked points are fixed. No position or replacement certificate is input. -/
theorem actual_marked_endpoint_rotation_in_chart
    (M : HyperellipticModel E S) (p : S) (hp : p ∈ M.cover.branch)
    (e0 : OpenPartialHomeomorph S Plane) (hp0 : p ∈ e0.source)
    (θ : ℝ) (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ (e : OpenPartialHomeomorph S Plane) (R : ℝ) (H : AmbientIsotopy S),
      p ∈ e.source ∧ e.source ⊆ W ∧ e.source ⊆ e0.source ∧
      (∀ x, e x = e0 x) ∧ 0 < R ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∉ W → H.map (t,x) = x) ∧
      (∀ t x, x ∈ e.source → H.map (t,x) ∈ e.source) ∧
      (∀ t x, x ∈ e.source →
        ‖planeComplexLinearEquiv (e (H.map (t,x))-e p)‖ =
          ‖planeComplexLinearEquiv (e x-e p)‖) ∧
      (∀ x, x ∈ e.source → ‖planeComplexLinearEquiv (e x-e p)‖ ≤ R/2 →
        planeComplexLinearEquiv (e (H.finalMap x)-e p) =
          (Circle.exp θ : ℂ) * planeComplexLinearEquiv (e x-e p)) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  let otherMarks : Set S := (M.cover.branch : Set S) \ {p}
  let U : Set S := W ∩ otherMarksᶜ
  have hU : IsOpen U := hW.inter (M.cover.branch.finite_toSet.sdiff.isClosed.isOpen_compl)
  have hpU : p ∈ U := ⟨hpW,by simp [otherMarks]⟩
  let e := e0.restr U
  have heSource : e.source = e0.source ∩ U := by
    rw [OpenPartialHomeomorph.restr_source,hU.interior_eq]
  have hpe : p ∈ e.source := heSource.symm ▸ ⟨hp0,hpU⟩
  have heW : e.source ⊆ W := fun x hx => ((heSource.le hx).2).1
  have honly (x : S) (hx : x ∈ e.source) (hm : x ∈ M.cover.branch) : x = p := by
    by_contra hn
    exact ((heSource.le hx).2).2 ⟨hm,by simpa using hn⟩
  let T : Plane ≃ₜ ℂ := (Homeomorph.addRight (-(e p))).trans planeComplexLinearEquiv.toHomeomorph
  have hT (z : Plane) : T z = planeComplexLinearEquiv (z-e p) := by
    simp [T,sub_eq_add_neg]
  have hTo : T (e p) = 0 := by simp [hT]
  have htarget : IsOpen (T '' e.target) := T.isOpenMap _ e.open_target
  have hzero : (0:ℂ) ∈ T '' e.target := ⟨e p,e.map_source hpe,hTo⟩
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (htarget.mem_nhds hzero)
  let R : ℝ := ε/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : closedBall (0:ℂ) R ⊆ T '' e.target := by
    intro z hz
    apply hball
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by dsimp [R]; linarith))
  let C : Set Plane := T.symm '' closedBall (0:ℂ) R
  have hC : IsCompact C := (isCompact_closedBall (0:ℂ) R).image T.symm.continuous
  have hCe : C ⊆ e.target := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨y,hy,he⟩ := hclosed hz
    rw [← he,T.symm_apply_apply]
    exact hy
  have hinC (z : Plane) (hz : ‖planeComplexLinearEquiv (z-e p)‖ ≤ R) : z ∈ C := by
    refine ⟨T z,?_,T.symm_apply_apply z⟩
    simpa only [mem_closedBall_zero_iff,hT] using hz
  obtain ⟨P,hPzero,hPout,hPnorm,hPinner⟩ := supported_plane_endpoint_rotation (e p) R θ hR
  have hPfix : ∀ t z, z ∉ C → P.map (t,z) = z := by
    intro t z hz
    exact hPout t z (le_of_lt (lt_of_not_ge (fun h => hz (hinC z h))))
  obtain ⟨K,H,hK,hH,houtside⟩ := position_surface_chart_lift S e.source e.target
    e.open_source e.toHomeomorphSourceTarget C hC hCe P hPfix
  have hstay (t : Interval) (x : S) (hx : x ∈ e.source) : H.map (t,x) ∈ e.source := by
    rw [hH t ⟨x,hx⟩]
    exact (K.map (t,⟨x,hx⟩)).property
  have hcoord (t : Interval) (x : S) (hx : x ∈ e.source) :
      e (H.map (t,x)) = P.map (t,e x) := by
    rw [hH t ⟨x,hx⟩]
    exact hK t ⟨x,hx⟩
  refine ⟨e,R,H,hpe,heW,(fun _ hx => (heSource.le hx).1),
    (fun _ => rfl),hR,?_,?_,hstay,?_,?_⟩
  · intro t x hm
    by_cases hx : x ∈ e.source
    · have hxp := honly x hx hm
      subst x
      apply e.injOn (hstay t p hpe) hpe
      rw [hcoord t p hpe,hPzero]
    · exact houtside t x hx
  · intro t x hx
    exact houtside t x (fun he => hx (heW he))
  · intro t x hx
    rw [hcoord t x hx]
    exact hPnorm t (e x)
  · intro x hx hlen
    change planeComplexLinearEquiv (e (H.map (1,x))-e p) = _
    rw [hcoord 1 x hx]
    exact hPinner (e x) hlen

/-- The sphere model supplies a chart for the prescribed-chart rotation. -/
theorem actual_marked_endpoint_rotation
    (M : HyperellipticModel E S) (p : S) (hp : p ∈ M.cover.branch)
    (θ : ℝ) (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ (e : OpenPartialHomeomorph S Plane) (R : ℝ) (H : AmbientIsotopy S),
      p ∈ e.source ∧ e.source ⊆ W ∧ 0 < R ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∉ W → H.map (t,x) = x) ∧
      (∀ t x, x ∈ e.source → H.map (t,x) ∈ e.source) ∧
      (∀ t x, x ∈ e.source →
        ‖planeComplexLinearEquiv (e (H.map (t,x))-e p)‖ =
          ‖planeComplexLinearEquiv (e x-e p)‖) ∧
      (∀ x, x ∈ e.source → ‖planeComplexLinearEquiv (e x-e p)‖ ≤ R/2 →
        planeComplexLinearEquiv (e (H.finalMap x)-e p) =
          (Circle.exp θ : ℂ) * planeComplexLinearEquiv (e x-e p)) := by
  classical
  obtain ⟨q,hq,hqp⟩ := Finset.exists_mem_ne (s := M.cover.branch) (by
    rw [M.cover.branch_card]; norm_num) p
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let e0 : OpenPartialHomeomorph S Plane :=
    M.sphere.toOpenPartialHomeomorph.trans (stereographic' 2 (M.sphere q))
  have hp0 : p ∈ e0.source := by
    change p ∈ Set.univ ∩ M.sphere ⁻¹' (stereographic' 2 (M.sphere q)).source
    rw [stereographic'_source]
    exact ⟨mem_univ _,fun he => hqp (M.sphere.injective he).symm⟩
  obtain ⟨e,R,H,hp',hW',_,_,hR,hmarks,hout,hstay,hnorm,hinner⟩ :=
    actual_marked_endpoint_rotation_in_chart M p hp e0 hp0 θ W hW hpW
  exact ⟨e,R,H,hp',hW',hR,hmarks,hout,hstay,hnorm,hinner⟩

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies CurveComplex.ArcFinitePosition
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The endpoint rotation produces an actual class-preserving essential arc,
with ordered marked endpoints retained and the concrete inner rotation formula. -/
theorem actual_endpoint_rotated_representative
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (θ : ℝ) (W : Set S) (hW : IsOpen W) (hpW : a.val.map 0 ∈ W) :
    ∃ (e : OpenPartialHomeomorph S Plane) (R : ℝ) (b : EssentialMarkedArc M),
      a.val.map 0 ∈ e.source ∧ e.source ⊆ W ∧ 0 < R ∧
      Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
      b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
      (∀ t, a.val.map t ∉ W → b.val.map t = a.val.map t) ∧
      (∀ t, a.val.map t ∈ e.source →
        ‖planeComplexLinearEquiv (e (b.val.map t)-e (a.val.map 0))‖ =
          ‖planeComplexLinearEquiv (e (a.val.map t)-e (a.val.map 0))‖) ∧
      (∀ t, a.val.map t ∈ e.source →
        ‖planeComplexLinearEquiv (e (a.val.map t)-e (a.val.map 0))‖ ≤ R/2 →
        planeComplexLinearEquiv (e (b.val.map t)-e (a.val.map 0)) =
          (Circle.exp θ : ℂ) * planeComplexLinearEquiv (e (a.val.map t)-e (a.val.map 0))) := by
  obtain ⟨e,R,H,hpe,heW,hR,hmarks,hout,_,hnorm,hinner⟩ :=
    actual_marked_endpoint_rotation M (a.val.map 0) a.val.start_marked θ W hW hpW
  obtain ⟨h,hh⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hfinal : H.finalMap = h := funext (fun x => (hh x).symm)
  have hfix : ∀ x, x ∈ M.cover.branch → h x = x := by
    intro x hx
    rw [← hfinal]
    exact hmarks ⟨1,by norm_num⟩ x hx
  let b := a.transport h hfix
  have hb (t : Interval) : b.val.map t = H.finalMap (a.val.map t) := by
    change h (a.val.map t) = H.finalMap (a.val.map t)
    rw [hfinal]
  refine ⟨e,R,b,hpe,heW,hR,?_,?_,?_,?_,?_,?_⟩
  · apply Eq.symm
    apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    change H.finalMap '' a.val.image = b.val.image
    rw [hfinal]
    exact (MarkedArc.transport_image a.val h hfix).symm
  · exact hfix _ a.val.start_marked
  · exact hfix _ a.val.end_marked
  · intro t ht
    rw [hb]
    exact hout ⟨1,by norm_num⟩ (a.val.map t) ht
  · intro t ht
    rw [hb]
    exact hnorm ⟨1,by norm_num⟩ (a.val.map t) ht
  · intro t ht hlen
    rw [hb]
    exact hinner (a.val.map t) ht hlen

end CurveComplex.HyperellipticModel
