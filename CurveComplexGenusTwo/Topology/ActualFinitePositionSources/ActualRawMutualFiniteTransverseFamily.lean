import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedBothEndpointClearance
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualMarkedCrossingTransport
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedEndpointClearance
import CurveComplexGenusTwo.Topology.Smoothing.ActualStarNormalizationProof
import CurveComplexGenusTwo.Filtration.Geometry.ActualCompactTimeCrosscutExtraction
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedTrimmedCrosscutAssembly
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteTransverseCrosscutRedrawing
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedPreparedFamilyCover
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedIntervalMesh
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedBothEndpointClearance
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.Smoothing.UniformActualGerms
import CurveComplexGenusTwo.Topology.Smoothing.ActualStarIntersection

set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace CurveComplex.HyperellipticModel
open Set Metric Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem actualRelativeTargetAxisChart
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M)
    (P : Set S) (hPc : IsCompact P) (hbP : Disjoint (arcInterior M b) P)
    (p : S) (hp : p ∉ M.cover.branch) (hpP : p ∉ P) :
    ∃ e : OpenPartialHomeomorph S Plane, ∃ label : Bool,
      p ∈ e.source ∧ Disjoint e.source (M.cover.branch : Set S) ∧
      Disjoint e.source P ∧
      ∀ x ∈ e.source, x ∈ b.val.image ↔ label = true ∧ e x 0 = 0 := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let := (actualSphereSmoothAtlas M).charts
  by_cases hpb : p ∈ b.val.image
  · obtain ⟨τ,hτ⟩ := hpb
    have hτ0 : 0 < τ.val := by
      by_contra hn
      have he : τ = 0 := Subtype.ext (le_antisymm (le_of_not_gt hn) τ.property.1)
      exact hp (hτ ▸ (he ▸ b.val.start_marked))
    have hτ1 : τ.val < 1 := by
      by_contra hn
      have he : τ = 1 := Subtype.ext (le_antisymm τ.property.2 (le_of_not_gt hn))
      exact hp (hτ ▸ (he ▸ b.val.end_marked))
    let α : ℝ := τ.val/2
    let β : ℝ := (τ.val+1)/2
    have hα : 0 < α := by dsimp [α]; linarith
    have hαβ : α < β := by dsimp [α,β]; linarith
    have hβ : β < 1 := by dsimp [β]; linarith
    obtain ⟨e0,_,hcore,_,_,havoid,haxis,_⟩ :=
      actual_isotopy_core_crosscut_chart M b P hPc hbP (AmbientIsotopy.identity S)
        (fun _ _ _ => rfl) α β hα hαβ hβ 0
    have hp0 : p ∈ e0.source := by
      apply hcore
      refine ⟨τ.val,?_,?_⟩
      · dsimp [α,β]; constructor <;> linarith
      · simpa only [Function.comp_apply,Set.projIcc_val,AmbientIsotopy.identity,
          ContinuousMap.coe_mk] using hτ
    let L : Plane ≃ₜ ℝ × ℝ := ((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
    let flip : Plane ≃ₜ Plane := (L.trans (Homeomorph.prodComm ℝ ℝ)).trans L.symm
    let e := e0.trans flip.toOpenPartialHomeomorph
    have hs : e.source = e0.source := by simp [e]
    refine ⟨e,true,hs.symm ▸ hp0,?_,?_,?_⟩
    · apply disjoint_left.mpr
      intro x hx hm
      exact (havoid x (hs ▸ hx)).1 hm
    · apply disjoint_left.mpr
      intro x hx hxP
      exact (havoid x (hs ▸ hx)).2 ⟨x,hxP,rfl⟩
    · intro x hx
      have he : e x 0 = e0 x 1 := rfl
      change x ∈ Set.range b.val.map ↔ true = true ∧ e x 0 = 0
      simpa only [he,eq_self,true_and,AmbientIsotopy.identity,ContinuousMap.coe_mk,
        Set.range_comp,Set.image_id] using haxis x (hs ▸ hx)
  · let forbidden : Set S := b.val.image ∪ ((M.cover.branch : Set S) ∪ P)
    have hc : IsClosed forbidden := (markedArc_image_compact b.val).isClosed.union
      (M.cover.branch.finite_toSet.isClosed.union hPc.isClosed)
    let e := (chartAt Plane p).restr forbiddenᶜ
    have hs : e.source = (chartAt Plane p).source ∩ forbiddenᶜ := by
      rw [OpenPartialHomeomorph.restr_source,hc.isOpen_compl.interior_eq]
    refine ⟨e,false,hs.symm ▸ ⟨mem_chart_source _ _,?_⟩,?_,?_,?_⟩
    · exact fun h => h.elim hpb (fun h => h.elim hp hpP)
    · exact disjoint_left.mpr (fun x hx hm => (hs ▸ hx).2 (Or.inr (Or.inl hm)))
    · exact disjoint_left.mpr (fun x hx hP => (hs ▸ hx).2 (Or.inr (Or.inr hP)))
    · intro x hx
      constructor
      · intro hb
        exact False.elim ((hs ▸ hx).2 (Or.inl hb))
      · rintro ⟨he,_⟩
        exact False.elim (Bool.false_ne_true he)




private theorem actualRelativePointOffTarget
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M)
    (P : Set S) (hPc : IsCompact P) (hbP : Disjoint (arcInterior M b) P)
    (p : S) (hp : p ∉ M.cover.branch) (hpP : p ∉ P)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ H : AmbientIsotopy S,
      H.finalMap p ∉ b.val.image ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
      (∀ t x, x ∈ P → H.map (t,x)=x) ∧
      ∀ t x, x ∉ W → H.map (t,x)=x := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let : CompactSpace S := M.sphere.symm.compactSpace
  by_cases hnone : p ∉ b.val.image
  · exact ⟨AmbientIsotopy.identity S,hnone,fun _ _ _ => rfl,
      fun _ _ _ => rfl,fun _ _ _ => rfl⟩
  have hpi : p ∈ b.val.image := not_not.mp hnone
  obtain ⟨E0,label,hpE0,hmarks,hgraph,hlabel⟩ :=
    actualRelativeTargetAxisChart M b P hPc hbP p hp hpP
  have hlabeli := (hlabel p hpE0).mp hpi
  have hpaxis : E0 p 0 = 0 := hlabeli.2
  let U : Set S := W ∩ (M.cover.branch : Set S)ᶜ
  have hU : IsOpen U := hW.inter M.cover.branch.finite_toSet.isClosed.isOpen_compl
  let e : OpenPartialHomeomorph S Plane :=
    (E0.restr U).trans (Homeomorph.addRight (-(E0 p))).toOpenPartialHomeomorph
  have heSource : e.source = E0.source ∩ U := by
    ext x
    simp [e,hU.interior_eq]
  have hpe : p ∈ e.source := heSource.symm ▸ ⟨hpE0,hpW,hp⟩
  have he (x : S) : e x = E0 x-E0 p := by simp [e,sub_eq_add_neg]
  have hep : e p = 0 := by simp [he]
  have hzero : (0:Plane) ∈ e.target := hep ▸ e.map_source hpe
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hzero)
  let R : ℝ := ε/2
  have hR : 0 < R := by dsimp [R]; positivity
  have htarget : closedBall (0:Plane) R ⊆ e.target := by
    intro z hz
    apply hball
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by dsimp [R]; linarith))
  let unit : Plane := Plane.mk 1 0
  have hunit : ‖unit‖ = 1 := by
    norm_num [unit,EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
  let v : Plane := (R/4) • unit
  have hv : ‖v‖ < R/2 := by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),hunit]
    linarith
  obtain ⟨P,hinner,houter⟩ := CurveComplex.GenusOrientationCandidate.plane_flat_bump_translation R hR v hv
  obtain ⟨K,H,hcoord,hHK,hout⟩ := position_surface_chart_lift S e.source e.target
    e.open_source e.toHomeomorphSourceTarget (closedBall (0:Plane) R)
    (isCompact_closedBall _ _) htarget P houter
  have hstay (t : Interval) : H.map (t,p) ∈ e.source := by
    rw [hHK t ⟨p,hpe⟩]
    exact (K.map (t,⟨p,hpe⟩)).property
  have hmove : e (H.finalMap p) = v := by
    rw [show H.finalMap p = (K.map (⟨1,by norm_num⟩,⟨p,hpe⟩)).val from
      hHK ⟨1,by norm_num⟩ ⟨p,hpe⟩]
    change (e.toHomeomorphSourceTarget (K.map (⟨1,by norm_num⟩,⟨p,hpe⟩))).val = v
    rw [hcoord]
    change P.map (⟨1,by norm_num⟩,e p) = v
    rw [hep,hinner _ _ (by change (0:Plane) ∈ closedBall 0 (R/2); exact mem_closedBall_self (by positivity))]
    simp
  have hmovedaxis : E0 (H.finalMap p) 0 ≠ 0 := by
    have hh := congrArg (fun z : Plane => z 0) hmove
    simp only [he,PiLp.sub_apply,hpaxis,sub_zero] at hh
    have hv0 : v 0 = R/4 := by simp [v,unit,Plane.mk]
    rw [hv0] at hh
    rw [hh]
    positivity
  refine ⟨H,?_,?_,?_,?_⟩
  · intro hm
    have hx0 : H.finalMap p ∈ E0.source := (heSource.le (hstay ⟨1,by norm_num⟩)).1
    exact hmovedaxis ((hlabel (H.finalMap p) hx0).mp hm).2
  · intro t x hm
    exact hout t x (fun hx => (heSource.le hx).2.2 hm)
  · intro t x hxP
    exact hout t x (fun he => disjoint_left.mp hgraph (heSource.le he).1 hxP)
  · intro t x hx
    exact hout t x (fun he => hx (heSource.le he).2.1)



end CurveComplex.HyperellipticModel

namespace CurveComplex.ArcFinitePosition
open Set
private theorem actualFiniteStarsRotationDirection {K J : Type*} [Fintype K] [Fintype J]
    (v : K → ℂ) (hv : ∀ k, v k ≠ 0) (w : J → ℂ) (hw : ∀ j, w j ≠ 0) :
    ∃ θ ∈ Icc (0:ℝ) 1,
      ∀ k j, Disjoint (segment ℝ (0:ℂ) ((Circle.exp θ : ℂ)*v k) \ {0})
        (segment ℝ (0:ℂ) (w j) \ {0}) := by
  classical
  let F : Finset ℂ := Finset.univ.image (fun kj : K × J =>
    ((‖v kj.1‖ / ‖w kj.2‖ : ℝ) : ℂ) * w kj.2 / v kj.1)
  obtain ⟨θ,hθ,havoid⟩ := exists_angle_avoiding_finite_complex F
  refine ⟨θ,hθ,?_⟩
  intro k j
  apply Set.disjoint_left.mpr
  rintro x ⟨hx,hx0⟩ ⟨hy,_⟩
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨t,ht,htx⟩ := hx
  obtain ⟨s,hs,hsx⟩ := hy
  have he : t • ((Circle.exp θ : ℂ)*v k) = s • w j := by
    simpa only [AffineMap.lineMap_apply_module,smul_zero,zero_add] using htx.trans hsx.symm
  have ht0 : t ≠ 0 := by
    intro h
    apply hx0
    apply Set.mem_singleton_iff.mpr
    rw [h] at htx
    simpa only [AffineMap.lineMap_apply_module,smul_zero,zero_add,zero_smul] using htx.symm
  have hn : t * ‖v k‖ = s * ‖w j‖ := by
    have h := congrArg norm he
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,
      abs_of_nonneg hs.1,norm_mul,Circle.norm_coe,one_mul] using h
  have hnw : ‖w j‖ ≠ 0 := norm_ne_zero_iff.mpr (hw j)
  have hsEq : t * (‖v k‖/‖w j‖) = s := by
    rw [← mul_div_assoc, div_eq_iff hnw]
    exact hn
  have hrot : (Circle.exp θ : ℂ)*v k = (‖v k‖/‖w j‖) • w j := by
    have he' : t • ((Circle.exp θ : ℂ)*v k) = t • ((‖v k‖/‖w j‖) • w j) := by
      rw [smul_smul,hsEq]
      exact he
    have hc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    exact mul_left_cancel₀ hc (by simpa only [Complex.real_smul] using he')
  have hbad : (Circle.exp θ : ℂ) = ((‖v k‖/‖w j‖ : ℝ) : ℂ) * w j / v k := by
    apply (eq_div_iff (hv k)).mpr
    simpa only [Complex.real_smul] using hrot
  apply havoid
  rw [hbad]
  exact Finset.mem_image.mpr ⟨(k,j),Finset.mem_univ _,rfl⟩

end CurveComplex.ArcFinitePosition

namespace CurveComplex.HyperellipticModel
open Set Metric Topology Schoenflies CurveComplex.ArcFinitePosition
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem actualLoopGermClearanceFromNormalizedStars
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
    (hloop : a.val.map 0 = a.val.map 1)
    (e0 : OpenPartialHomeomorph S Plane) (hp0 : a.val.map 0 ∈ e0.source)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1/2)
    (w : ι × Bool → Plane)
    (hold : ∀ i b, (if b then (old i).val.map 1 else (old i).val.map 0) = a.val.map 0 →
      w (i,b) ≠ 0 ∧ segment ℝ (e0 (a.val.map 0)) (e0 (a.val.map 0)+w (i,b)) ⊆ e0.target ∧
      range ((old i).val.map ∘ endpointGermParameter b r hr (by linarith)) =
        e0.symm '' segment ℝ (e0 (a.val.map 0)) (e0 (a.val.map 0)+w (i,b)))
    (s : ℝ) (hs : 0 < s) (hshalf : s < 1/2) (v : Bool → Plane)
    (hv : ∀ g, v g ≠ 0)
    (hvtarget : ∀ g, segment ℝ (e0 (a.val.map 0)) (e0 (a.val.map 0)+v g) ⊆ e0.target)
    (hnew : ∀ g, range (a.val.map ∘ endpointGermParameter g s hs (by linarith)) =
      e0.symm '' segment ℝ (e0 (a.val.map 0)) (e0 (a.val.map 0)+v g)) :
    ∃ b : EssentialMarkedArc M, ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
      b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 → t.val ≤ δ ∨ 1-δ ≤ t.val →
        ∀ i, b.val.map t ∉ (old i).val.image := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let p := a.val.map 0
  let J := {j : ι × Bool // (if j.2 then (old j.1).val.map 1 else (old j.1).val.map 0) = p}
  let : Fintype J := Fintype.ofFinite J
  have hvC (g : Bool) : planeComplexLinearEquiv (v g) ≠ 0 :=
    fun he => hv g (planeComplexLinearEquiv.injective (by simpa using he))
  have hwC (j : J) : planeComplexLinearEquiv (w j.val) ≠ 0 := by
    intro he
    exact (hold j.val.1 j.val.2 j.property).1
      (planeComplexLinearEquiv.injective (by simpa using he))
  obtain ⟨θ,_,hsep⟩ := actualFiniteStarsRotationDirection
    (fun g => planeComplexLinearEquiv (v g)) hvC
    (fun j : J => planeComplexLinearEquiv (w j.val)) hwC
  obtain ⟨e,R,H,hpe,_,he0,hee,hR,hmarks,houtside,hstay,_,hinner⟩ :=
    actual_marked_endpoint_rotation_in_chart M p a.val.start_marked e0 hp0 θ
      univ isOpen_univ (mem_univ _)
  obtain ⟨U,hU,hpU,_,hUold⟩ := actual_finite_endpoint_germ_neighborhood M old p
    a.val.start_marked r hr hrhalf e0.source e0.open_source hp0
  obtain ⟨g,hg⟩ := H.homeomorphism_at (1 : Interval)
  have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
  have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
    intro x hx; rw [← hfinal]; exact hmarks 1 x hx
  let b := a.transport g hfix
  have hb (t : Interval) : b.val.map t = H.finalMap (a.val.map t) := by
    change g (a.val.map t) = H.finalMap (a.val.map t); rw [hfinal]
  let core : Set S := e.source ∩ e ⁻¹' {z : Plane | ‖planeComplexLinearEquiv (z-e p)‖ < R/2}
  have hcore : IsOpen core := e.isOpen_inter_preimage (isOpen_lt (by fun_prop) continuous_const)
  have hpcore : p ∈ core := ⟨hpe,by simp only [mem_preimage,mem_ofPred_eq,sub_self,map_zero,norm_zero]; positivity⟩
  let Q : Set Interval := a.val.map ⁻¹' (core ∩ g ⁻¹' U)
  have hQ : IsOpen Q := (hcore.inter (hU.preimage g.continuous)).preimage a.val.continuous
  have hpQ : a.val.map 0 ∈ core ∩ g ⁻¹' U := ⟨hpcore,by
    change g p ∈ U; rw [hfix p a.val.start_marked]; exact hpU⟩
  have h0Q : (0 : Interval) ∈ Q := hpQ
  have h1Q : (1 : Interval) ∈ Q := by change a.val.map 1 ∈ core ∩ g ⁻¹' U; rw [← hloop]; exact hpQ
  obtain ⟨η₀,hη₀,hball₀⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds h0Q)
  obtain ⟨η₁,hη₁,hball₁⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds h1Q)
  let δ : ℝ := min η₀ (min η₁ (min s (1/2))) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδη₀ : δ < η₀ := by have := min_le_left η₀ (min η₁ (min s (1/2))); dsimp [δ]; linarith
  have hδη₁ : δ < η₁ := by have := (min_le_right η₀ (min η₁ (min s (1/2)))).trans (min_le_left η₁ (min s (1/2))); dsimp [δ]; linarith
  have hδs : δ < s := by have := ((min_le_right η₀ (min η₁ (min s (1/2)))).trans (min_le_right η₁ (min s (1/2)))).trans (min_le_left s (1/2)); dsimp [δ]; linarith
  have hδhalf : δ < 1/2 := by have := ((min_le_right η₀ (min η₁ (min s (1/2)))).trans (min_le_right η₁ (min s (1/2)))).trans (min_le_right s (1/2)); dsimp [δ]; linarith
  refine ⟨b,δ,hδ,hδhalf,?_,hfix _ a.val.start_marked,hfix _ a.val.end_marked,?_⟩
  · apply Eq.symm; apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    rw [hfinal]
    exact (MarkedArc.transport_image a.val g hfix).symm
  · intro t ht0 ht1 htδ i hcontact
    have htQ : t ∈ Q := by
      rcases htδ with ht | ht
      · apply hball₀
        rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
        change |t.val-0| < η₀
        rw [sub_zero,abs_of_pos ht0]
        exact ht.trans_lt hδη₀
      · apply hball₁
        rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
        change |t.val-1| < η₁
        rw [abs_of_neg (by linarith),neg_sub]
        linarith
    have hxU : b.val.map t ∈ U := by change g (a.val.map t) ∈ U; exact htQ.2
    obtain ⟨terminal,hincident,hxgerm⟩ := hUold i (b.val.map t) hcontact hxU
    let j : J := ⟨(i,terminal),hincident⟩
    obtain ⟨k,hyNew⟩ : ∃ k : Bool,
        a.val.map t ∈ range (a.val.map ∘ endpointGermParameter k s hs (by linarith)) := by
      rcases htδ with ht | ht
      · let u : Interval := ⟨t.val/s,⟨div_nonneg t.property.1 hs.le,(div_le_one hs).mpr (ht.trans hδs.le)⟩⟩
        refine ⟨false,u,?_⟩
        apply congrArg a.val.map; apply Subtype.ext
        change s*(t.val/s) = t.val
        field_simp
      · let u : Interval := ⟨(1-t.val)/s,⟨div_nonneg (by linarith [t.property.2]) hs.le,(div_le_one hs).mpr (by linarith)⟩⟩
        refine ⟨true,u,?_⟩
        apply congrArg a.val.map; apply Subtype.ext
        change 1-s*((1-t.val)/s) = t.val
        field_simp
        ring
    obtain ⟨z,hz,hzy⟩ := hnew k ▸ hyNew
    have hcoordNew : e0 (a.val.map t) ∈ segment ℝ (e0 p) (e0 p+v k) := by
      rw [← hzy,e0.right_inv (hvtarget k hz)]; exact hz
    have hcoordOld : e0 (b.val.map t) ∈ segment ℝ (e0 p) (e0 p+w (i,terminal)) := by
      obtain ⟨z,hz,hzx⟩ := (hold i terminal hincident).2.2 ▸ hxgerm
      rw [← hzx,e0.right_inv ((hold i terminal hincident).2.1 hz)]; exact hz
    have hxsource : b.val.map t ∈ e.source := by rw [hb]; exact hstay 1 _ htQ.1.1
    have hxne : b.val.map t ≠ p := by
      intro he
      have hm : b.val.map t ∈ M.cover.branch := he.symm ▸ a.val.start_marked
      exact (b.val.marked_only_at_ends t hm).elim
        (fun h => by have hh := congrArg Subtype.val h; change t.val=0 at hh; linarith)
        (fun h => by have hh := congrArg Subtype.val h; change t.val=1 at hh; linarith)
    have hnonzero : planeComplexLinearEquiv (e0 (b.val.map t)-e0 p) ≠ 0 := by
      intro he
      have heq : e0 (b.val.map t) = e0 p := sub_eq_zero.mp
        (planeComplexLinearEquiv.injective (by simpa using he))
      exact hxne (e0.injOn (he0 hxsource) hp0 heq)
    have hrot := hinner (a.val.map t) htQ.1.1 htQ.1.2.le
    rw [← hb,hee,hee,hee] at hrot
    have hnewseg : planeComplexLinearEquiv (e0 (b.val.map t)-e0 p) ∈
        segment ℝ (0:ℂ) ((Circle.exp θ : ℂ)*planeComplexLinearEquiv (v k)) := by
      rw [hrot]
      have hh := complex_offset_mem_segment (e0 p) (v k) (e0 (a.val.map t)) hcoordNew
      rw [segment_eq_image_lineMap] at hh ⊢
      obtain ⟨q,hq,hqe⟩ := hh
      refine ⟨q,hq,?_⟩
      rw [← hqe]
      simp only [AffineMap.lineMap_apply_module,smul_zero,zero_add,Complex.real_smul]
      ring
    have holdseg := complex_offset_mem_segment (e0 p) (w (i,terminal))
      (e0 (b.val.map t)) hcoordOld
    exact Set.disjoint_left.mp (hsep k j) ⟨hnewseg,by simpa using hnonzero⟩
      ⟨holdseg,by simpa using hnonzero⟩


private theorem actualLoopGermClearanceAgainstNormalizedOldStar
    (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
    {ι : Type} [Fintype ι] (old : ι → EssentialMarkedArc M)
    (a : EssentialMarkedArc M) (hloop : a.val.map 0 = a.val.map 1)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1/2)
    (w : ι × Bool → Plane)
    (hold : letI := C.charts
      ∀ i b, (if b then (old i).val.map 1 else (old i).val.map 0) = a.val.map 0 →
      w (i,b) ≠ 0 ∧
      segment ℝ ((chartAt Plane (a.val.map 0)) (a.val.map 0))
        ((chartAt Plane (a.val.map 0)) (a.val.map 0)+w (i,b)) ⊆ (chartAt Plane (a.val.map 0)).target ∧
      Set.range ((old i).val.map ∘ endpointGermParameter b r hr (by linarith)) =
        (chartAt Plane (a.val.map 0)).symm ''
          segment ℝ ((chartAt Plane (a.val.map 0)) (a.val.map 0))
            ((chartAt Plane (a.val.map 0)) (a.val.map 0)+w (i,b)))
 :
    ∃ b : EssentialMarkedArc M, ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
      b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 → t.val ≤ δ ∨ 1-δ ≤ t.val →
        ∀ i, b.val.map t ∉ (old i).val.image := by
  let := C.charts
  obtain ⟨H,s,hs,hshalf,v,hmarks,houtside,hstar⟩ := actual_endpoint_star_normalization M C
    PUnit (fun _ => a) (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
    (a.val.map 0) a.val.start_marked univ isOpen_univ (mem_univ _)
  obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
  have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
    intro x hx; rw [← hfinal]; exact hmarks ⟨1,by norm_num⟩ x hx
  let a1 := a.transport g hfix
  have h10 : a1.val.map 0 = a.val.map 0 := hfix _ a.val.start_marked
  have h11 : a1.val.map 1 = a.val.map 1 := hfix _ a.val.end_marked
  have hclass1 : Quotient.mk (essentialArcSetoid M) a1 = Quotient.mk (essentialArcSetoid M) a := by
    apply Eq.symm; apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    rw [hfinal]
    exact (MarkedArc.transport_image a.val g hfix).symm
  have hloop1 : a1.val.map 0 = a1.val.map 1 := by rw [h10,h11]; exact hloop
  have hstars (k : Bool) := hstar PUnit.unit k (by
    cases k
    · rfl
    · exact hloop.symm)
  have hrange (k : Bool) : range (a1.val.map ∘ endpointGermParameter k s hs (by linarith)) =
      (chartAt Plane (a1.val.map 0)).symm ''
      segment ℝ ((chartAt Plane (a1.val.map 0)) (a1.val.map 0))
        ((chartAt Plane (a1.val.map 0)) (a1.val.map 0)+v (PUnit.unit,k)) := by
    rw [h10]
    change range (g ∘ (a.val.map ∘ endpointGermParameter k s hs _)) = _
    rw [range_comp,← hfinal]
    exact (hstars k).2.2
  obtain ⟨b,δ,hδ,hδhalf,hclass,hb0,hb1,hclear⟩ :=
    actualLoopGermClearanceFromNormalizedStars M old a1 hloop1
      (chartAt Plane (a1.val.map 0)) (mem_chart_source Plane _) r hr hrhalf w
      (by simpa only [h10] using hold) s hs hshalf (fun k => v (PUnit.unit,k))
      (fun k => (hstars k).1) (fun k => by simpa only [h10] using (hstars k).2.1) hrange
  exact ⟨b,δ,hδ,hδhalf,hclass.trans hclass1,hb0.trans h10,hb1.trans h11,hclear⟩

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
open ArcSurgery Set
private theorem actualCrossingsTransportToSpecifiedAnchor
    (M : HyperellipticModel E S) (a b target : EssentialMarkedArc M)
    (h : S ≃ₜ S) (hm : ∀ p, p ∈ M.cover.branch → h p = p)
    (ha : h '' a.val.image = target.val.image) :
    crossings M target (b.transport h hm) = h '' crossings M a b := by
  have hi : arcInterior M (a.transport h hm) = arcInterior M target := by
    change (a.val.transport h hm).image \ (M.cover.branch : Set S) = _
    rw [MarkedArc.transport_image,ha]
    rfl
  have hc := actual_crossings_transport a b h hm
  unfold crossings at hc ⊢
  rw [hi] at hc
  exact hc

private theorem actualCrossingDiskTransportToSpecifiedAnchor
    (M : HyperellipticModel E S) (a b target : EssentialMarkedArc M)
    (h : S ≃ₜ S) (hm : ∀ p, p ∈ M.cover.branch → h p = p)
    (ha : h '' a.val.image = target.val.image)
    (p : S) (hc : CrossesInDisk M a b p) :
    CrossesInDisk M target (b.transport h hm) (h p) := by
  obtain ⟨U,hU,hp,hmark,e,he0,hanchor,hb⟩ := hc
  let eU : U ≃ₜ (h '' U) := h.image U
  have hp' : h p ∈ h '' U := mem_image_of_mem h hp
  let f := eU.symm.trans e
  have hmark' : Disjoint (h '' U) (M.cover.branch : Set S) := by
    apply Set.disjoint_left.mpr
    rintro q ⟨z,hz,rfl⟩ hq
    have heq : h z = z := h.injective (hm (h z) hq)
    exact Set.disjoint_left.mp hmark hz (heq ▸ hq)
  refine ⟨h '' U,h.isOpenMap U hU,hp',hmark',f,?_,?_,?_⟩
  · have he : eU.symm ⟨h p,hp'⟩ = ⟨p,hp⟩ := by
      apply Subtype.ext
      exact h.symm_apply_apply p
    simpa only [f,Homeomorph.trans_apply,he] using he0
  · intro q
    let y := eU.symm q
    have hy : y.val = h.symm q.val := rfl
    have hmem : q.val ∈ h '' a.val.image ↔ y.val ∈ a.val.image := by
      rw [hy]
      exact Set.mem_image_iff_of_inverse h.symm_apply_apply h.apply_symm_apply
    rw [ha] at hmem
    exact hmem.trans (hanchor y)
  · intro q
    let y := eU.symm q
    have hy : y.val = h.symm q.val := rfl
    change q.val ∈ (b.val.transport h hm).image ↔ _
    rw [MarkedArc.transport_image]
    have hmem : q.val ∈ h '' b.val.image ↔ y.val ∈ b.val.image := by
      rw [hy]
      exact Set.mem_image_iff_of_inverse h.symm_apply_apply h.apply_symm_apply
    exact hmem.trans (hb y)


noncomputable local instance rawMinimumSeedDecidableEq (M : HyperellipticModel E S) : DecidableEq (EssentialArcClass M) := Classical.decEq _
open ArcSurgery Set Metric Topology Schoenflies CurveComplex.FiniteStarGeometry
theorem actual_raw_mutual_finite_transverse_family
(M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
(F : Finset (EssentialArcClass M)) :
  ∃ r : {v // v ∈ F} → EssentialMarkedArc M,
    (∀ v, ArcSurgery.vertex M (r v) = v.val) ∧
    (∀ v, (ArcSurgery.crossings M anchor (r v)).Finite ∧
      ∀ p ∈ ArcSurgery.crossings M anchor (r v),
        ArcSurgery.CrossesInDisk M anchor (r v) p) ∧
    (∀ v w, v ≠ w → (ArcSurgery.crossings M (r v) (r w)).Finite ∧
      ∀ p ∈ ArcSurgery.crossings M (r v) (r w),
        ArcSurgery.CrossesInDisk M (r v) (r w) p) := by
  classical
  have hEndpointGerms {ι : Type} [Fintype ι]
      (old : ι → EssentialMarkedArc M)
      (hfinite : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
      (p : S) (hp : p ∈ M.cover.branch)
      (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
      ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrhalf : r < 1/2,
      (∀ v : ι × Bool,
        (if v.2 then (old v.1).val.map 1 else (old v.1).val.map 0)=p →
        ∀ t, (old v.1).val.map (endpointGermParameter v.2 r hr (by linarith) t) ∈ W) ∧
      ∀ v w : ι × Bool, v ≠ w →
        (if v.2 then (old v.1).val.map 1 else (old v.1).val.map 0)=p →
        (if w.2 then (old w.1).val.map 1 else (old w.1).val.map 0)=p →
        Set.range ((old v.1).val.map ∘ endpointGermParameter v.2 r hr (by linarith)) ∩
          Set.range ((old w.1).val.map ∘ endpointGermParameter w.2 r hr (by linarith)) = {p} := by
    letI : T2Space S := M.sphere.symm.t2Space
    let contacts : Set S := ⋃ i, ⋃ j, if i=j then ∅ else crossings M (old i) (old j)
    have hc : contacts.Finite := by
      apply Set.finite_iUnion
      intro i
      apply Set.finite_iUnion
      intro j
      split
      · exact Set.finite_empty
      · exact hfinite i j ‹i ≠ j›
    have hpc : p ∉ contacts := by
      intro h
      obtain ⟨i,j,h⟩ := Set.mem_iUnion₂.mp h
      split at h
      · exact Set.notMem_empty p h
      · exact h.1.2 hp
    obtain ⟨r,hr,hrhalf,hstarts,hends⟩ :=
      uniform_actual_endpoint_germs M ι old p (contactsᶜ ∩ W)
        (hc.isClosed.isOpen_compl.inter hW) ⟨hpc,hpW⟩
    have hr1 : r < 1 := by linarith
    let germ (v : ι × Bool) := (old v.1).val.map ∘ endpointGermParameter v.2 r hr hr1
    have hzero (v : ι × Bool)
        (hv : (if v.2 then (old v.1).val.map 1 else (old v.1).val.map 0)=p) :
        germ v 0=p := by
      cases hb : v.2 <;> simpa [germ,endpointGermParameter,hb] using hv
    have hlocal (v : ι × Bool)
        (hv : (if v.2 then (old v.1).val.map 1 else (old v.1).val.map 0)=p)
        (t : Interval) : germ v t ∈ contactsᶜ ∩ W := by
      cases hb : v.2
      · apply hstarts v.1 (by simpa [hb] using hv)
        rw [hb]
        change r*t.val ≤ r
        nlinarith [t.property.2]
      · apply hends v.1 (by simpa [hb] using hv)
        rw [hb]
        change 1-r ≤ 1-r*t.val
        nlinarith [t.property.2]
    have hoff (v : ι × Bool)
        (hv : (if v.2 then (old v.1).val.map 1 else (old v.1).val.map 0)=p)
        (t : Interval) : germ v t ∉ contacts := (hlocal v hv t).1
    have hmarked (v : ι × Bool) (t : Interval)
        (hm : germ v t ∈ M.cover.branch) : t=0 := by
      obtain ht | ht := (old v.1).val.marked_only_at_ends
        (endpointGermParameter v.2 r hr hr1 t) hm
      · have hh := congrArg Subtype.val ht
        apply Subtype.ext
        change t.val=0
        cases hb : v.2 <;> simp [endpointGermParameter,hb,ne_of_gt hr] at hh <;>
          first | exact congrArg Subtype.val hh | nlinarith [t.property.1,t.property.2]
      · have hh := congrArg Subtype.val ht
        apply Subtype.ext
        change t.val=0
        cases hb : v.2 <;> simp [endpointGermParameter,hb,ne_of_gt hr] at hh <;>
          first | exact congrArg Subtype.val hh | nlinarith [t.property.1,t.property.2]
    refine ⟨r,hr,hrhalf,(fun v hv t => (hlocal v hv t).2),?_⟩
    intro v w hvw hv hw
    by_cases he : v.1=w.1
    · have hb : v.2 ≠ w.2 := fun hh => hvw (Prod.ext he hh)
      let solo : Unit → EssentialMarkedArc M := fun _ => old v.1
      have hdsolo : ∀ i j : Unit, i ≠ j → Disjoint (arcInterior M (solo i)) (arcInterior M (solo j)) := by
        intro i j hij
        exact (hij (Subsingleton.elim _ _)).elim
      have hs := actual_normalized_star_intersection M solo hdsolo p r hr hrhalf
        ((),v.2) ((),w.2) (fun hh => hb (congrArg (fun z : Unit × Bool => z.2) hh))
        (by simpa [solo,germ,endpointGermParameter] using hzero v hv)
        (by simpa [solo,germ,endpointGermParameter,he] using hzero w hw)
      simpa only [solo,he] using hs
    · ext x
      constructor
      · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
        have heq : germ v t = germ w u := ht.trans hu.symm
        by_cases hm : germ v t ∈ M.cover.branch
        · change germ v t=x at ht
          rw [hmarked v t hm,hzero v hv] at ht
          exact Set.mem_singleton_iff.mpr ht.symm
        · have hcontact : germ v t ∈ crossings M (old v.1) (old w.1) := by
            refine ⟨⟨?_,hm⟩,?_,hm⟩
            · exact ⟨endpointGermParameter v.2 r hr hr1 t,rfl⟩
            · exact ⟨endpointGermParameter w.2 r hr hr1 u,heq.symm⟩
          exact False.elim (hoff v hv t (Set.mem_iUnion₂.mpr ⟨v.1,w.1,by simpa [he] using hcontact⟩))
      · intro hx
        have hx' := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨⟨0,hzero v hv⟩,⟨0,hzero w hw⟩⟩
  have hPreparedAwayContacts {ι : Type} [Fintype ι]
      (old : ι → EssentialMarkedArc M) (p : S)
      (hp : p ∉ M.cover.branch)
      (hpc : p ∉ ⋃ i, ⋃ j, if i=j then ∅ else crossings M (old i) (old j)) :
      ∃ e : OpenPartialHomeomorph S Schoenflies.Plane,
        p ∈ e.source ∧ Disjoint e.source (M.cover.branch : Set S) ∧
        ∃ label : Option ι, (∀ j, label=some j → p ∈ (old j).val.image) ∧ ∀ j x, x ∈ e.source →
          (x ∈ (old j).val.image ↔ label=some j ∧ e x 0=0) := by
    letI : T2Space S := M.sphere.symm.t2Space
    letI := (actualSphereSmoothAtlas M).charts
    by_cases hex : ∃ i, p ∈ (old i).val.image
    · obtain ⟨i,hpi⟩ := hex
      obtain ⟨e0,label0,hp0,hm0,_,haxis⟩ := actualRelativeTargetAxisChart
        M (old i) ∅ isCompact_empty (Set.disjoint_empty _) p hp (Set.notMem_empty _)
      have hl : label0=true := ((haxis p hp0).mp hpi).1
      let others : Set S := ⋃ j : {j : ι // j ≠ i}, (old j.val).val.image
      have hoc : IsCompact others := markedFamily_graph_compact
        (fun j : {j : ι // j ≠ i} => (old j.val).val)
      have hpo : p ∉ others := by
        intro h
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
        apply hpc
        exact Set.mem_iUnion₂.mpr ⟨i,j.val,by
          simpa [Ne.symm j.property] using (show p ∈ crossings M (old i) (old j.val) from
            ⟨⟨hpi,hp⟩,hj,hp⟩)⟩
      let e := e0.restr othersᶜ
      have hs : e.source=e0.source ∩ othersᶜ := by
        rw [OpenPartialHomeomorph.restr_source,hoc.isClosed.isOpen_compl.interior_eq]
      refine ⟨e,hs.symm ▸ ⟨hp0,hpo⟩,hm0.mono_left (fun _ hx => (hs ▸ hx).1),some i,?_,?_⟩
      · intro j hj
        have he : i=j := Option.some.inj hj
        simpa [← he] using hpi
      · intro j x hx
        have hx0 := (hs ▸ hx).1
        by_cases hij : i=j
        · subst j
          change x ∈ (old i).val.image ↔ some i=some i ∧ e0 x 0=0
          simpa only [Option.some.injEq,eq_self,true_and,hl] using haxis x hx0
        · have hxnot : x ∉ (old j).val.image := fun h =>
            (hs ▸ hx).2 (Set.mem_iUnion.mpr ⟨⟨j,Ne.symm hij⟩,h⟩)
          simp only [Option.some.injEq,hij,false_and,iff_false]
          exact hxnot
    · let forbidden : Set S := (⋃ j, (old j).val.image) ∪ (M.cover.branch : Set S)
      have hc : IsClosed forbidden :=
        (markedFamily_graph_compact (fun j => (old j).val)).isClosed.union
          M.cover.branch.finite_toSet.isClosed
      let e := (chartAt Schoenflies.Plane p).restr forbiddenᶜ
      have hs : e.source=(chartAt Schoenflies.Plane p).source ∩ forbiddenᶜ := by
        rw [OpenPartialHomeomorph.restr_source,hc.isOpen_compl.interior_eq]
      have hpf : p ∉ forbidden := by
        rintro (h | h)
        · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
          exact hex ⟨j,hj⟩
        · exact hp h
      refine ⟨e,hs.symm ▸ ⟨mem_chart_source _ _,hpf⟩,?_,none,(by intro j hj; cases hj),?_⟩
      · exact Set.disjoint_left.mpr (fun x hx hm => (hs ▸ hx).2 (Or.inr hm))
      · intro j x hx
        constructor
        · intro hj
          exact False.elim ((hs ▸ hx).2 (Or.inl (Set.mem_iUnion.mpr ⟨j,hj⟩)))
        · rintro ⟨h,_⟩
          cases h
  have hAvoidFiniteNodes (a : EssentialMarkedArc M) (P : Finset S)
      (hPmark : ∀ p ∈ P, p ∉ M.cover.branch)
      (R : Set S) (hR : IsClosed R) (hPR : ∀ p ∈ P, p ∉ R) :
      ∃ b : EssentialMarkedArc M, ArcSurgery.vertex M b=ArcSurgery.vertex M a ∧
        (∀ t, a.val.map t ∈ R → b.val.map t=a.val.map t) ∧
        ∀ p ∈ P, p ∉ b.val.image := by
    letI : T2Space S := M.sphere.symm.t2Space
    induction P using Finset.induction_on with
    | empty => exact ⟨a,rfl,(fun _ _ => rfl),by simp⟩
    | @insert p P hpP ih =>
      obtain ⟨b,hb,hbR,hbP⟩ := ih
        (fun q hq => hPmark q (Finset.mem_insert_of_mem hq))
        (fun q hq => hPR q (Finset.mem_insert_of_mem hq))
      let forbidden : Set S := ((P : Set S) ∪ (M.cover.branch : Set S)) ∪ R
      have hforb : IsClosed forbidden := (P.finite_toSet.isClosed.union M.cover.branch.finite_toSet.isClosed).union hR
      have hpf : p ∉ forbidden := fun h => h.elim
        (fun h => h.elim hpP (hPmark p (Finset.mem_insert_self _ _)))
        (hPR p (Finset.mem_insert_self _ _))
      obtain ⟨H,hmove,hmarks,_,houtside⟩ := actualRelativePointOffTarget M b ∅
        isCompact_empty (Set.disjoint_empty _) p (hPmark p (Finset.mem_insert_self _ _))
        (Set.notMem_empty _) forbiddenᶜ hforb.isOpen_compl hpf
      obtain ⟨g,hg⟩ := H.homeomorphism_at 1
      have hfinal : H.finalMap=g := funext (fun x => (hg x).symm)
      have hfix : ∀ x, x ∈ M.cover.branch → g x=x := by
        intro x hx
        rw [← hfinal]
        exact hmarks 1 x hx
      have hsymmfix : ∀ x, x ∈ M.cover.branch → g.symm x=x := by
        intro x hx
        apply g.injective
        rw [g.apply_symm_apply,hfix x hx]
      let c := b.transport g.symm hsymmfix
      have hcimage : c.val.image=g.symm '' b.val.image := MarkedArc.transport_image b.val g.symm hsymmfix
      have hcclass : ArcSurgery.vertex M c=ArcSurgery.vertex M b := by
        apply Quotient.sound
        refine ⟨H,hmarks,?_⟩
        rw [hfinal,hcimage,Set.image_image]
        simp only [Function.comp_def,Homeomorph.apply_symm_apply,Set.image_id']
      refine ⟨c,hcclass.trans hb,?_,?_⟩
      · intro t ht
        change g.symm (b.val.map t)=a.val.map t
        rw [hbR t ht]
        apply g.injective
        rw [g.apply_symm_apply]
        symm
        rw [← hfinal]
        apply houtside
        exact fun h => h (Or.inr ht)
      · intro q hq
        rw [hcimage]
        rintro ⟨x,hx,he⟩
        have hxg : x=g q := by
          rw [← he,g.apply_symm_apply]
        rcases Finset.mem_insert.mp hq with rfl | hqP
        · apply hmove
          rw [hfinal,← hxg]
          exact hx
        · have hqfix : g q=q := by
            rw [← hfinal]
            apply houtside
            exact fun h => h (Or.inl (Or.inl hqP))
          exact hbP q hqP (by simpa [hxg,hqfix] using hx)
  have hFiniteContactEndpointStar
      (C : SphereSmoothAtlas S)
      {ι : Type} [Fintype ι] (a : ι → EssentialMarkedArc M)
      (hfinite : ∀ i j, i ≠ j → (crossings M (a i) (a j)).Finite)
      (p : S) (hp : p ∈ M.cover.branch)
      (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
      letI := C.charts
      ∃ (H : AmbientIsotopy S) (r : ℝ) (hr : 0 < r) (hrhalf : r < 1 / 2)
        (v : ι × Bool → EuclideanSpace ℝ (Fin 2)),
        (∀ t b, b ∈ M.cover.branch → H.map (t, b) = b) ∧
        (∀ t x, x ∉ W → H.map (t, x) = x) ∧
        ∀ (i : ι) (terminal : Bool),
          (if terminal then (a i).val.map ⟨1, by norm_num⟩
            else (a i).val.map ⟨0, by norm_num⟩) = p →
          v (i, terminal) ≠ 0 ∧
          (segment ℝ ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p)
            ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p + v (i, terminal)) ⊆
            (chartAt (EuclideanSpace ℝ (Fin 2)) p).target) ∧
          H.finalMap '' Set.range ((a i).val.map ∘
            endpointGermParameter terminal r hr (by linarith)) =
            (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
              segment ℝ ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p)
                ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p + v (i, terminal)) := by
    classical
    letI := C.charts
    letI : T2Space S := M.sphere.symm.t2Space
    letI : CompactSpace S := M.sphere.symm.compactSpace
    have pointedIsotopy (o : Plane) (R : ℝ) (hR : 0 < R) (F : Plane ≃ₜ Plane)
        (hFo : F o = o) (hfix : ∀ x, x ∉ ball o R → F x = x) :
        ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
          (∀ t, H.map (t,o) = o) ∧ ∀ t x, x ∉ ball o R → H.map (t,x) = x := by
      have zero (R : ℝ) (hR : 0 < R) (F : Plane ≃ₜ Plane)
          (hFfix : ∀ x, R ≤ ‖x‖ → F x = x) (hFzero : F 0 = 0) :
          ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
            (∀ t x, R ≤ ‖x‖ → H.map (t,x) = x) ∧ ∀ t, H.map (t,0) = 0 := by
        have hFbound (x : Plane) (hx : ‖x‖ ≤ R) : ‖F x‖ ≤ R := by
          by_contra hn
          have heq : F x = x := F.injective (hFfix (F x) (le_of_not_ge hn))
          exact hn (by rw [heq]; exact hx)
        have hdisp (x : Plane) : ‖F x - x‖ ≤ 2 * R := by
          by_cases hx : ‖x‖ ≤ R
          · exact (norm_sub_le _ _).trans (by linarith [hFbound x hx])
          · rw [hFfix x (le_of_not_ge hx), sub_self, norm_zero]
            linarith
        let G : Interval × Plane → Plane := fun z =>
          if (z.1 : ℝ) = 0 then z.2 else (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2)
        have hGbound (z : Interval × Plane) :
            dist (G z) z.2 ≤ (2 * R) * (z.1 : ℝ) := by
          by_cases ht : (z.1 : ℝ) = 0
          · simp only [G, ht, ite_true, dist_self, mul_zero, le_refl]
          · dsimp only [G]
            rw [if_neg ht, dist_eq_norm]
            have heq : (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2) - z.2 =
                (z.1 : ℝ) • (F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2) := by
              rw [smul_sub, smul_smul, mul_inv_cancel₀ ht, one_smul]
            rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg z.1.property.1]
            calc
              (z.1 : ℝ) * ‖F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2‖ ≤
                  (z.1 : ℝ) * (2 * R) :=
                mul_le_mul_of_nonneg_left (hdisp _) z.1.property.1
              _ = (2 * R) * (z.1 : ℝ) := mul_comm _ _
        have hGc : Continuous G := by
          rw [continuous_iff_continuousAt]
          intro z
          by_cases ht : (z.1 : ℝ) = 0
          · have hGz : G z = z.2 := by simp only [G, ht, ite_true]
            change Filter.Tendsto G (nhds z) (nhds (G z))
            rw [hGz, tendsto_iff_dist_tendsto_zero]
            have hlim : Filter.Tendsto
                (fun w : Interval × Plane => (2 * R) * (w.1 : ℝ) + dist w.2 z.2)
                (nhds z) (nhds 0) := by
              have hc : Continuous (fun w : Interval × Plane =>
                  (2 * R) * (w.1 : ℝ) + dist w.2 z.2) := by fun_prop
              simpa only [ContinuousAt, ht, mul_zero, dist_self, add_zero] using hc.continuousAt (x := z)
            exact squeeze_zero (fun w => dist_nonneg) (fun w =>
              (dist_triangle (G w) w.2 z.2).trans (add_le_add (hGbound w) le_rfl)) hlim
          · have hc : ContinuousAt
                (fun w : Interval × Plane => (w.1 : ℝ) • F ((w.1 : ℝ)⁻¹ • w.2)) z := by
              fun_prop (disch := assumption)
            apply hc.congr_of_eventuallyEq
            have hevent : ∀ᶠ w : Interval × Plane in nhds z, (w.1 : ℝ) ≠ 0 :=
              (continuous_subtype_val.comp continuous_fst).continuousAt.eventually_ne ht
            exact hevent.mono (fun w hw => if_neg hw)
        refine ⟨{ map := ⟨G, hGc⟩, homeomorphism_at := ?_, at_zero := ?_ }, ?_, ?_, ?_⟩
        · intro t
          by_cases ht : (t : ℝ) = 0
          · exact ⟨Homeomorph.refl _, fun x => by
              change x = G (t, x)
              simp only [G, ht, ite_true]⟩
          · let u : ℝˣ := Units.mk0 (t : ℝ) ht
            let e := ((Homeomorph.smul u⁻¹).trans F).trans (Homeomorph.smul u)
            refine ⟨e, ?_⟩
            intro x
            change (t : ℝ) • F ((t : ℝ)⁻¹ • x) = G (t, x)
            dsimp only [G]
            rw [if_neg ht]
        · intro x
          simp [G]
        · funext x
          simp [AmbientIsotopy.finalMap, G]
        · intro t x hx
          change G (t, x) = x
          by_cases ht : (t : ℝ) = 0
          · simp only [G, ht, ite_true]
          · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
            have hlarge : R ≤ ‖(t : ℝ)⁻¹ • x‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), inv_mul_eq_div]
              apply (le_div_iff₀ htpos).mpr
              nlinarith [t.property.2]
            simp only [G, if_neg ht, hFfix _ hlarge, smul_smul, mul_inv_cancel₀ ht, one_smul]
        · intro t
          change G (t,0) = 0
          by_cases ht : (t:ℝ) = 0
          · simp only [G,ht,ite_true]
          · simp only [G,if_neg ht,smul_zero,hFzero]
      have conjugate {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
          (e : X ≃ₜ Y) (H : AmbientIsotopy Y) :
          ∃ K : AmbientIsotopy X, ∀ t x, K.map (t,x) = e.symm (H.map (t,e x)) := by
        refine ⟨{ map := ⟨fun z => e.symm (H.map (z.1,e z.2)),
          e.symm.continuous.comp (H.map.continuous.comp
            (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩,
                  homeomorphism_at := ?_, at_zero := ?_ },fun _ _ => rfl⟩
        · intro t
          obtain ⟨h,hh⟩ := H.homeomorphism_at t
          exact ⟨(e.trans h).trans e.symm,fun x => congrArg e.symm (hh (e x))⟩
        · intro x
          change e.symm (H.map (⟨0,by norm_num⟩,e x)) = x
          rw [H.at_zero,e.symm_apply_apply]
      let E : Plane ≃ₜ Plane := Homeomorph.addLeft (-o)
      have hEo : E o = 0 := by simp [E]
      have hEinv : E.symm 0 = o := by
        apply E.injective
        rw [E.apply_symm_apply,hEo]
      have hdist : ∀ x, dist (E x) 0 = dist x o := by
        intro x
        simp [E,dist_eq_norm,sub_eq_add_neg,add_comm]
      let A : Plane ≃ₜ Plane := (E.symm.trans F).trans E
      have hA0 : A 0 = 0 := by
        change E (F (E.symm 0)) = 0
        rw [hEinv,hFo,hEo]
      have hAfix : ∀ x, R ≤ ‖x‖ → A x = x := by
        intro x hx
        have hxout : E.symm x ∉ ball o R := by
          have hh := hdist (E.symm x)
          rw [E.apply_symm_apply,dist_zero_right] at hh
          simp only [mem_ball]
          exact not_lt.mpr (hh ▸ hx)
        change E (F (E.symm x)) = x
        rw [hfix _ hxout,E.apply_symm_apply]
      obtain ⟨H,hHF,hHfix,hH0⟩ := zero R hR A hAfix hA0
      obtain ⟨K,hK⟩ := conjugate E H
      refine ⟨K,?_,?_,?_⟩
      · funext x
        change K.map (⟨1,by norm_num⟩,x) = F x
        rw [hK]
        change E.symm (H.finalMap (E x)) = F x
        rw [hHF]
        change E.symm (E (F (E.symm (E x)))) = F x
        rw [E.symm_apply_apply,E.symm_apply_apply]
      · intro t
        rw [hK,hEo,hH0,hEinv]
      · intro t x hx
        rw [hK]
        have hxnorm : R ≤ ‖E x‖ := by
          have hh := hdist x
          rw [dist_zero_right] at hh
          exact not_lt.mp (by simpa only [mem_ball,← hh] using hx)
        rw [hHfix t _ hxnorm,E.symm_apply_apply]
    have nested (γ : I → Plane) (hγ : Topology.IsClosedEmbedding γ)
        (o : Plane) (hstart : γ zeroI = o) (H : Plane ≃ₜ Plane) (hH : H o = o)
        (c d : I) (hd : 0 < d.val) (hdc : d.val ≤ c.val) (v : Plane) (hv : v ≠ 0)
        (hrad : H '' armPrefix (fun _ : Unit => γ) () c = segment ℝ o (o+v)) :
        H '' armPrefix (fun _ : Unit => γ) () d = segment ℝ o (H (γ d)) ∧ H (γ d) ≠ o := by
      let k : I → I := fun t => ⟨d.val*t.val,by
        constructor
        · exact mul_nonneg d.property.1 t.property.1
        · nlinarith [d.property.1,d.property.2,t.property.1,t.property.2]⟩
      let η : Path o (H (γ d)) := {
        toFun := H ∘ γ ∘ k
        continuous_toFun := H.continuous.comp (hγ.continuous.comp (by fun_prop))
        source' := by simpa [k] using (congrArg H hstart).trans hH
        target' := by simp [k] }
      have hη : Function.Injective η := by
        intro t u he
        have hh := congrArg Subtype.val (hγ.injective (H.injective he))
        change d.val*t.val = d.val*u.val at hh
        exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hd) hh)
      have himage : range η = H '' armPrefix (fun _ : Unit => γ) () d := by
        ext x
        constructor
        · rintro ⟨t,rfl⟩
          exact ⟨γ (k t),⟨k t,by change d.val*t.val ≤ d.val; nlinarith [d.property.1,t.property.2],rfl⟩,rfl⟩
        · rintro ⟨_,⟨t,ht,rfl⟩,rfl⟩
          let u : I := ⟨t.val/d.val,⟨div_nonneg t.property.1 hd.le,(div_le_one hd).mpr ht⟩⟩
          refine ⟨u,?_⟩
          change H (γ (k u)) = H (γ t)
          congr 2
          apply Subtype.ext
          change d.val*(t.val/d.val) = t.val
          field_simp
      have hA : IsArcBetween (range η) o (H (γ d)) := by
        refine ⟨η.extend,η.continuous_extend.continuousOn,?_,?_,η.extend_zero,η.extend_one⟩
        · intro s hs t ht he
          rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
          exact congrArg Subtype.val (hη he)
        · exact η.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))
      have hneq : H (γ d) ≠ o := by
        intro he
        have hdz : d = zeroI := hγ.injective ((H.injective (he.trans hH.symm)).trans hstart.symm)
        have hh : d.val = 0 := congrArg Subtype.val hdz
        linarith
      have hvend : o ≠ o+v := by
        intro he
        apply hv
        have hh := congrArg (fun x => x-o) he
        simpa only [sub_self,add_sub_cancel_left] using hh.symm
      have hC := isArcBetween_segment hvend
      have hAC : range η ⊆ segment ℝ o (o+v) := by
        rw [himage,← hrad]
        apply image_mono
        apply image_mono
        intro t ht
        exact ht.trans hdc
      have hqC : H (γ d) ∈ segment ℝ o (o+v) := by
        rw [← hrad]
        exact ⟨γ d,⟨d,hdc,rfl⟩,rfl⟩
      have hBC : segment ℝ o (H (γ d)) ⊆ segment ℝ o (o+v) :=
        (convex_segment o (o+v)).segment_subset (left_mem_segment ℝ o (o+v)) hqC
      exact ⟨himage.symm.trans (hA.eq_of_subset_arc (isArcBetween_segment hneq.symm) hC hAC hBC),hneq⟩
    obtain ⟨U,hU,hpU,hUchart,hmarks,hcentral,hnoninc,rOld,hrOld,hrOldHalf,hOldGerms⟩ :=
      actual_endpoint_star_in_smooth_chart M C ι a p hp
    let D := U ∩ W
    have hD : IsOpen D := hU.inter hW
    have hpD : p ∈ D := ⟨hpU,hpW⟩
    let e := chartAt Plane p
    have hDchart : D ⊆ e.source := fun x hx => hUchart hx.1
    obtain ⟨R,hR,htarget,hdiskD,hcompact⟩ := coordinate_disk_inside p D hD hpD hDchart
    obtain ⟨r₀,hr₀,hr₀half,hgermSource,hgermMeet⟩ := hEndpointGerms a hfinite p hp D hD hpD
    have hr₀1 : r₀ < 1 := by linarith
    let α : ι × Bool → Interval → S := fun x =>
      (a x.1).val.map ∘ endpointGermParameter x.2 r₀ hr₀ hr₀1
    let J := {x : ι × Bool // α x CurveComplex.FiniteStarGeometry.zeroI = p}
    let γ : J → Interval → Plane := fun j => e ∘ α j.val
    have hsource : ∀ (j : J) (t : Interval), α j.val t ∈ e.source := by
      intro j t
      apply hDchart
      apply hgermSource j.val
      cases hb : j.val.2 <;> simpa [α,endpointGermParameter,CurveComplex.FiniteStarGeometry.zeroI,hb] using j.property
    have hγ : ∀ j : J, Topology.IsClosedEmbedding (γ j) := by
      intro j
      have hα := actual_endpoint_germ_embedding M (a j.val.1) j.val.2 r₀ hr₀ hr₀1
      have hc : Continuous (γ j) := continuousOn_univ.mp
        (e.continuousOn.comp hα.continuous.continuousOn (fun t _ => hsource j t))
      apply hc.isClosedEmbedding
      intro s t he
      exact hα.injective (e.injOn (hsource j s) (hsource j t) he)
    have hstart : ∀ j : J, γ j CurveComplex.FiniteStarGeometry.zeroI = e p := by
      intro j
      change e (α j.val CurveComplex.FiniteStarGeometry.zeroI) = e p
      rw [j.property]
    have hmeet : ∀ i j : J, i ≠ j → range (γ i) ∩ range (γ j) = {e p} := by
      intro i j hij
      have hij' : i.val ≠ j.val := fun he => hij (Subtype.ext he)
      have hreal := hgermMeet i.val j.val hij' (by cases hb : i.val.2 <;> simpa [α,endpointGermParameter,CurveComplex.FiniteStarGeometry.zeroI,hb] using i.property)
        (by cases hb : j.val.2 <;> simpa [α,endpointGermParameter,CurveComplex.FiniteStarGeometry.zeroI,hb] using j.property)
      ext x
      constructor
      · rintro ⟨⟨s,hs⟩,⟨t,ht⟩⟩
        have he : α i.val s = α j.val t := e.injOn (hsource i s) (hsource j t) (hs.trans ht.symm)
        have hz : α i.val s = p := by
          have hh : α i.val s ∈ range (α i.val) ∩ range (α j.val) := ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩
          rw [hreal] at hh
          exact hh
        exact mem_singleton_iff.mpr (hs.symm.trans (congrArg e hz))
      · intro hx
        have hx' : x = e p := hx
        subst x
        exact ⟨⟨CurveComplex.FiniteStarGeometry.zeroI,hstart i⟩,
          ⟨CurveComplex.FiniteStarGeometry.zeroI,hstart j⟩⟩
    obtain ⟨star⟩ := CurveComplex.FiniteStarGeometry.finite_actual_star_radialization γ (e p)
      hγ hstart hmeet (ball (e p) R) isOpen_ball (by simpa using hR)
    have hsupportTarget : closedBall (e p) star.supportRadius ⊆ e.target := by
      intro z hz
      exact htarget (ball_subset_closedBall (star.support_subset hz))
    obtain ⟨P,hPfinal,hPcenter,hPoutside⟩ := pointedIsotopy (e p) star.supportRadius star.support_pos
      star.H star.fixes_center star.fixes_exterior
    have hPclosed : ∀ t z, z ∉ closedBall (e p) star.supportRadius → P.map (t,z) = z := by
      intro t z hz
      exact hPoutside t z (fun hh => hz (ball_subset_closedBall hh))
    obtain ⟨K,G,hcoord,hGU,hGoutside⟩ := position_surface_chart_lift S e.source e.target
      e.open_source e.toHomeomorphSourceTarget (closedBall (e p) star.supportRadius)
      (isCompact_closedBall _ _) hsupportTarget P hPclosed
    have hcoord' (t : Interval) (x : e.source) :
        e (K.map (t,x)) = P.map (t,e x) := by
      simpa only [OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe] using hcoord t x
    have hGpoint (t : Interval) (x : S) (hx : x ∈ e.source) :
        G.map (t,x) = e.symm (P.map (t,e x)) := by
      rw [hGU t ⟨x,hx⟩,← hcoord' t ⟨x,hx⟩]
      exact (e.left_inv (K.map (t,⟨x,hx⟩)).property).symm
    have hGoutD : ∀ t x, x ∉ D → G.map (t,x) = x := by
      intro t x hxD
      by_cases hx : x ∈ e.source
      · have hzout : e x ∉ closedBall (e p) star.supportRadius := by
          intro hz
          have hzin : e x ∈ closedBall (e p) R := ball_subset_closedBall (star.support_subset hz)
          have hxD' : e.symm (e x) ∈ D := hdiskD ⟨e x,hzin,rfl⟩
          rw [e.left_inv hx] at hxD'
          exact hxD hxD'
        rw [hGpoint t x hx,hPclosed t (e x) hzout,e.left_inv hx]
      · exact hGoutside t x hx
    have hGcenter : ∀ t, G.map (t,p) = p := by
      intro t
      rw [hGpoint t p (mem_chart_source Plane p),hPcenter,e.left_inv (mem_chart_source Plane p)]
    have hGmarks : ∀ t b, b ∈ M.cover.branch → G.map (t,b) = b := by
      intro t b hb
      by_cases hbp : b = p
      · subst b; exact hGcenter t
      · apply hGoutD
        intro hbD
        exact hbp (hmarks b hb hbD.1)
    have small (s : Finset J) : ∃ d : ℝ, 0 < d ∧ d < 1 ∧ ∀ j ∈ s, d < (star.cut j).val := by
      induction s using Finset.induction_on with
      | empty => exact ⟨1/2,by norm_num,by norm_num,by simp⟩
      | @insert j s hj ih =>
        obtain ⟨d,hd,hd1,hds⟩ := ih
        refine ⟨min d ((star.cut j).val/2),lt_min hd (half_pos (star.cut_pos j)),
          (min_le_left _ _).trans_lt hd1,?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with he|hi
        · subst i
          exact (min_le_right _ _).trans_lt (by linarith [star.cut_pos j])
        · exact (min_le_left _ _).trans_lt (hds i hi)
    obtain ⟨d,hd,hd1,hds⟩ := small Finset.univ
    let q : Interval := ⟨d,⟨hd.le,hd1.le⟩⟩
    let r := r₀*d
    have hr : 0 < r := mul_pos hr₀ hd
    have hrhalf : r < 1/2 := by
      have hh : r₀*d < r₀ := by nlinarith
      exact hh.trans hr₀half
    let v : ι × Bool → Plane := fun x =>
      if hx : α x CurveComplex.FiniteStarGeometry.zeroI = p then
        star.H (γ ⟨x,hx⟩ q) - e p else 0
    have hTargetPreserved : ∀ z ∈ e.target, star.H z ∈ e.target := by
      intro z hz
      by_contra hn
      have hout : star.H z ∉ ball (e p) star.supportRadius := by
        intro hh
        exact hn (hsupportTarget (ball_subset_closedBall hh))
      have he : star.H z = z := star.H.injective (star.fixes_exterior _ hout)
      exact hn (he.symm ▸ hz)
    refine ⟨G,r,hr,hrhalf,v,hGmarks,?_,?_⟩
    · intro t x hx
      exact hGoutD t x (fun hh => hx hh.2)
    · intro i terminal hi
      have hx : α (i,terminal) CurveComplex.FiniteStarGeometry.zeroI = p := by
        cases terminal <;> simpa [α,endpointGermParameter,CurveComplex.FiniteStarGeometry.zeroI] using hi
      let j : J := ⟨(i,terminal),hx⟩
      have hv : v (i,terminal) = star.H (γ j q) - e p := by simp only [v,dif_pos hx]; rfl
      have hend : e p + v (i,terminal) = star.H (γ j q) := by rw [hv]; abel
      obtain ⟨hsmall,hne⟩ := nested (γ j) (hγ j) (e p) (hstart j) star.H star.fixes_center
        (star.cut j) q hd (hds j (Finset.mem_univ j)).le (star.vector j) (star.vector_nonzero j)
        (by simpa only [CurveComplex.FiniteStarGeometry.armPrefix] using star.prefix_image j)
      refine ⟨by rw [hv]; exact sub_ne_zero.mpr hne,?_,?_⟩
      · rw [hend,← hsmall]
        rintro z ⟨_,⟨t,ht,rfl⟩,rfl⟩
        exact hTargetPreserved _ (e.map_source (hsource j t))
      · let k : Interval → Interval := fun t => ⟨d*t.val,by
          constructor
          · exact mul_nonneg hd.le t.property.1
          · nlinarith [t.property.2]⟩
        have hkRange : range k = {t : Interval | t.val ≤ d} := by
          ext t
          constructor
          · rintro ⟨u,rfl⟩
            change d*u.val ≤ d
            nlinarith [u.property.2]
          · intro ht
            let u : Interval := ⟨t.val/d,⟨div_nonneg t.property.1 hd.le,(div_le_one hd).mpr ht⟩⟩
            refine ⟨u,?_⟩
            apply Subtype.ext
            change d*(t.val/d) = t.val
            field_simp
        have hparam : (a i).val.map ∘ endpointGermParameter terminal r hr (by linarith) = α j.val ∘ k := by
          funext t
          change (a i).val.map _ = (a i).val.map _
          congr 1
          apply Subtype.ext
          cases terminal <;> dsimp [endpointGermParameter,α,k,r,j] <;> ring
        rw [hparam,range_comp,hkRange,hend]
        have hEq : EqOn G.finalMap (e.symm ∘ star.H ∘ e) (α j.val '' {t : Interval | t.val ≤ d}) := by
          rintro x ⟨t,ht,rfl⟩
          change G.map (⟨1,by norm_num⟩,α j.val t) = _
          rw [hGpoint _ _ (hsource j t)]
          change e.symm (P.finalMap (γ j t)) = e.symm (star.H (γ j t))
          rw [hPfinal]
        rw [hEq.image_eq,image_comp,image_comp]
        have hγimage : e '' (α j.val '' {t : Interval | t.val ≤ d}) =
            CurveComplex.FiniteStarGeometry.armPrefix (fun _ : Unit => γ j) () q := by
          exact (image_comp e (α j.val) {t : Interval | t.val ≤ d}).symm
        rw [hγimage,hsmall]
  have hFiniteContactInitialClearance
      (C : SphereSmoothAtlas S) {ι : Type} [Fintype ι]
      (old : ι → EssentialMarkedArc M)
      (hfinite : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
      (a : EssentialMarkedArc M) :
      ∃ H : AmbientIsotopy S,
        (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
        ∃ g : S ≃ₜ S, ∃ hfix : ∀ x, x ∈ M.cover.branch → g x=x,
          H.finalMap=g ∧ ∃ b : EssentialMarkedArc M, ∃ δ : ℝ,
          0 < δ ∧ δ < 1/2 ∧ vertex M b=vertex M a ∧
          b.val.map 0=a.val.map 0 ∧ b.val.map 1=a.val.map 1 ∧
          ∀ t : Interval, 0 < t.val → t.val ≤ δ →
            ∀ i, b.val.map t ∉ ((old i).transport g hfix).val.image := by
    letI := C.charts
    obtain ⟨H,r,hr,hrhalf,w,hmarks,_,hstar⟩ := hFiniteContactEndpointStar C old hfinite (a.val.map 0) a.val.start_marked Set.univ isOpen_univ (Set.mem_univ _)
    obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
    have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
    have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
      intro x hx; rw [← hfinal]; exact hmarks ⟨1,by norm_num⟩ x hx
    let old' := fun i => (old i).transport g hfix
    let a1 := a.transport g hfix
    have h10 : a1.val.map 0 = a.val.map 0 := hfix _ a.val.start_marked
    have h11 : a1.val.map 1 = a.val.map 1 := hfix _ a.val.end_marked
    have hclass (c : EssentialMarkedArc M) :
        Quotient.mk (essentialArcSetoid M) (c.transport g hfix) = Quotient.mk (essentialArcSetoid M) c := by
      apply Eq.symm; apply Quotient.sound
      refine ⟨H,hmarks,?_⟩
      rw [hfinal]
      exact (MarkedArc.transport_image c.val g hfix).symm
    have hold : ∀ i b, (if b then (old' i).val.map 1 else (old' i).val.map 0) = a1.val.map 0 →
        w (i,b) ≠ 0 ∧
        segment ℝ ((chartAt Plane (a1.val.map 0)) (a1.val.map 0))
          ((chartAt Plane (a1.val.map 0)) (a1.val.map 0)+w (i,b)) ⊆ (chartAt Plane (a1.val.map 0)).target ∧
        Set.range ((old' i).val.map ∘ endpointGermParameter b r hr (by linarith)) =
          (chartAt Plane (a1.val.map 0)).symm ''
            segment ℝ ((chartAt Plane (a1.val.map 0)) (a1.val.map 0))
              ((chartAt Plane (a1.val.map 0)) (a1.val.map 0)+w (i,b)) := by
      intro i b hb
      have he : (if b then (old i).val.map 1 else (old i).val.map 0) = a.val.map 0 := by
        have h0 : (old' i).val.map 0 = (old i).val.map 0 := hfix _ (old i).val.start_marked
        have h1 : (old' i).val.map 1 = (old i).val.map 1 := hfix _ (old i).val.end_marked
        simpa only [h0,h1,h10] using hb
      obtain ⟨hw,hwt,hwr⟩ := hstar i b he
      refine ⟨hw,by simpa only [h10] using hwt,?_⟩
      rw [h10]
      change Set.range (g ∘ ((old i).val.map ∘ endpointGermParameter b r hr _)) = _
      rw [Set.range_comp,← hfinal]
      exact hwr
    obtain ⟨b,δ,hδ,hδhalf,hbclass,hb0,hb1,_,hclear⟩ :=
      actual_initial_germ_clearance_against_normalized_old_star M C old' a1
        r hr hrhalf w hold Set.univ isOpen_univ (Set.mem_univ _)
    exact ⟨H,hmarks,g,hfix,hfinal,b,δ,hδ,hδhalf,
      hbclass.trans (hclass a),hb0.trans h10,hb1.trans h11,hclear⟩
  have hFiniteContactNonloopBothClearance
      (C : SphereSmoothAtlas S) {ι : Type} [Fintype ι]
      (old : ι → EssentialMarkedArc M)
      (hfinite : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
      (a : EssentialMarkedArc M) (hne : a.val.map 0 ≠ a.val.map 1) :
      ∃ H : AmbientIsotopy S,
        (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
        ∃ g : S ≃ₜ S, ∃ hfix : ∀ x, x ∈ M.cover.branch → g x=x,
          H.finalMap=g ∧ ∃ b : EssentialMarkedArc M, ∃ δ : ℝ,
          0 < δ ∧ δ < 1/2 ∧ vertex M b=vertex M a ∧
          b.val.map 0=a.val.map 0 ∧ b.val.map 1=a.val.map 1 ∧
          ∀ t : Interval, 0 < t.val → t.val < 1 → t.val ≤ δ ∨ 1-δ ≤ t.val →
            ∀ i, b.val.map t ∉ ((old i).transport g hfix).val.image := by
    classical
    letI := C.charts
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨H0,hmarks0,g0,hfix0,hfinal0,b0,δ0,hδ0,hδ0half,hclassB0,hb00,hb01,hclear0⟩ :=
      hFiniteContactInitialClearance C old hfinite a
    let old0 := fun i => (old i).transport g0 hfix0
    have hfinite0 : ∀ i j, i ≠ j → (crossings M (old0 i) (old0 j)).Finite := by
      intro i j hij
      rw [actual_crossings_transport (old i) (old j) g0 hfix0]
      exact (hfinite i j hij).image g0
    obtain ⟨H,r,hr,hrhalf,w,hmarks,_,hstar⟩ := hFiniteContactEndpointStar C old0 hfinite0
      (b0.val.map 1) b0.val.end_marked Set.univ isOpen_univ (Set.mem_univ _)
    obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
    have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
    have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
      intro x hx; rw [← hfinal]; exact hmarks ⟨1,by norm_num⟩ x hx
    let old1 := fun i => (old0 i).transport g hfix
    let a1 := b0.transport g hfix
    have h10 : a1.val.map 0 = b0.val.map 0 := hfix _ b0.val.start_marked
    have h11 : a1.val.map 1 = b0.val.map 1 := hfix _ b0.val.end_marked
    have hclass (c : EssentialMarkedArc M) :
        Quotient.mk (essentialArcSetoid M) (c.transport g hfix) = Quotient.mk (essentialArcSetoid M) c := by
      apply Eq.symm; apply Quotient.sound
      refine ⟨H,hmarks,?_⟩
      rw [hfinal]
      exact (MarkedArc.transport_image c.val g hfix).symm
    have hne1 : a1.val.map 0 ≠ a1.val.map 1 := by rw [h10,h11,hb00,hb01]; exact hne
    have hclear1 (t : Interval) (ht0 : 0 < (t:ℝ)) (htδ : (t:ℝ) ≤ δ0) (i : ι) :
        a1.val.map t ∉ (old1 i).val.image := by
      intro hx
      change a1.val.map t ∈ ((old0 i).val.transport g hfix).image at hx
      rw [MarkedArc.transport_image] at hx
      obtain ⟨x,hx,he⟩ := hx
      have he' : x = b0.val.map t := g.injective he
      exact hclear0 t ht0 htδ i (he' ▸ hx)
    let prefixCarrier : Set S := a1.val.map '' {t : Interval | (t:ℝ) ≤ δ0}
    have hprefixCarrier : IsClosed prefixCarrier :=
      ((isClosed_le continuous_subtype_val continuous_const).isCompact.image a1.val.continuous).isClosed
    have hend : a1.val.map 1 ∉ prefixCarrier := by
      rintro ⟨t,ht,he⟩
      rcases a1.val.injective_except_loop_closure t 1 he with hh | ⟨h0,h1⟩ | ⟨h1,h0⟩
      · subst t; change (1:ℝ) ≤ δ0 at ht; linarith
      · subst t; exact hne1 he
      · have hh := congrArg Subtype.val h0
        norm_num at hh
    let W : Set S := prefixCarrierᶜ
    have hW : IsOpen W := hprefixCarrier.isOpen_compl
    have hold : ∀ i b, (if b then (old1 i).val.map 1 else (old1 i).val.map 0) = a1.reverse.val.map 0 →
        w (i,b) ≠ 0 ∧
        segment ℝ ((chartAt Plane (a1.reverse.val.map 0)) (a1.reverse.val.map 0))
          ((chartAt Plane (a1.reverse.val.map 0)) (a1.reverse.val.map 0)+w (i,b)) ⊆
            (chartAt Plane (a1.reverse.val.map 0)).target ∧
        Set.range ((old1 i).val.map ∘ endpointGermParameter b r hr (by linarith)) =
          (chartAt Plane (a1.reverse.val.map 0)).symm ''
            segment ℝ ((chartAt Plane (a1.reverse.val.map 0)) (a1.reverse.val.map 0))
              ((chartAt Plane (a1.reverse.val.map 0)) (a1.reverse.val.map 0)+w (i,b)) := by
      intro i b hb
      have hp : a1.reverse.val.map 0 = b0.val.map 1 := by simp [h11]
      have he : (if b then (old0 i).val.map 1 else (old0 i).val.map 0) = b0.val.map 1 := by
        have h0 : (old1 i).val.map 0 = (old0 i).val.map 0 := hfix _ (old0 i).val.start_marked
        have h1 : (old1 i).val.map 1 = (old0 i).val.map 1 := hfix _ (old0 i).val.end_marked
        simpa only [h0,h1,hp] using hb
      obtain ⟨hw,hwt,hwr⟩ := hstar i b he
      refine ⟨hw,by simpa only [hp] using hwt,?_⟩
      rw [hp]
      change Set.range (g ∘ ((old0 i).val.map ∘ endpointGermParameter b r hr _)) = _
      rw [Set.range_comp,← hfinal]
      exact hwr
    obtain ⟨z,δ1,hδ1,hδ1half,hzclass,hz0,hz1,hzout,hzclear⟩ :=
      actual_initial_germ_clearance_against_normalized_old_star M C old1 a1.reverse
        r hr hrhalf w hold W hW (by simpa [W] using hend)
    let δ : ℝ := min δ0 δ1
    have hδ : 0 < δ := lt_min hδ0 hδ1
    have hδhalf : δ < 1/2 := (min_le_left _ _).trans_lt hδ0half
    let G := H0.compose H
    have hGmarks : ∀ t x, x ∈ M.cover.branch → G.map (t,x)=x := by
      intro t x hx
      change H.map (t,H0.map (t,x))=x
      rw [hmarks0 t x hx,hmarks t x hx]
    let gTotal := g0.trans g
    have hGfix : ∀ x, x ∈ M.cover.branch → gTotal x=x := by
      intro x hx
      change g (g0 x)=x
      rw [hfix0 x hx,hfix x hx]
    have hGfinal : G.finalMap=gTotal := by
      ext x
      change H.finalMap (H0.finalMap x)=g (g0 x)
      rw [hfinal0,hfinal]
    refine ⟨G,hGmarks,gTotal,hGfix,hGfinal,z.reverse,δ,hδ,hδhalf,?_,?_,?_,?_⟩
    · exact z.reverse_class.trans (hzclass.trans (a1.reverse_class.trans ((hclass b0).trans hclassB0)))
    · simpa only [EssentialMarkedArc.reverse_map,unitInterval.symm_zero] using
        hz1.trans (by simpa using h10.trans hb00)
    · simpa only [EssentialMarkedArc.reverse_map,unitInterval.symm_one] using
        hz0.trans (by simpa using h11.trans hb01)
    · intro t ht0 ht1 hcol i
      change z.val.map (unitInterval.symm t) ∉ (old1 i).val.image
      rcases hcol with hstart | hendcol
      · have htδ0 : (t:ℝ) ≤ δ0 := hstart.trans (min_le_left _ _)
        have houtside : a1.reverse.val.map (unitInterval.symm t) ∉ W := by
          change a1.val.map (unitInterval.symm (unitInterval.symm t)) ∉ prefixCarrierᶜ
          rw [unitInterval.symm_symm]
          exact fun hh => hh ⟨t,htδ0,rfl⟩
        rw [hzout _ houtside]
        simpa only [EssentialMarkedArc.reverse_map,unitInterval.symm_symm] using hclear1 t ht0 htδ0 i
      · apply hzclear
        · change 0 < 1-(t:ℝ); linarith
        · change 1-(t:ℝ) ≤ δ1
          have := min_le_right δ0 δ1
          dsimp [δ] at hendcol
          linarith
  have hFiniteContactLoopBothClearance
      (C : SphereSmoothAtlas S) {ι : Type} [Fintype ι]
      (old : ι → EssentialMarkedArc M)
      (hfinite : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
      (a : EssentialMarkedArc M) (hloop : a.val.map 0=a.val.map 1) :
      ∃ H : AmbientIsotopy S,
        (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
        ∃ g : S ≃ₜ S, ∃ hfix : ∀ x, x ∈ M.cover.branch → g x=x,
          H.finalMap=g ∧ ∃ b : EssentialMarkedArc M, ∃ δ : ℝ,
          0 < δ ∧ δ < 1/2 ∧ vertex M b=vertex M a ∧
          b.val.map 0=a.val.map 0 ∧ b.val.map 1=a.val.map 1 ∧
          ∀ t : Interval, 0 < t.val → t.val < 1 → t.val ≤ δ ∨ 1-δ ≤ t.val →
            ∀ i, b.val.map t ∉ ((old i).transport g hfix).val.image := by
    let := C.charts
    obtain ⟨H,r,hr,hrhalf,w,hmarks,_,hstar⟩ := hFiniteContactEndpointStar C old hfinite (a.val.map 0) a.val.start_marked Set.univ isOpen_univ (Set.mem_univ _)
    obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
    have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
    have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
      intro x hx; rw [← hfinal]; exact hmarks ⟨1,by norm_num⟩ x hx
    let old' := fun i => (old i).transport g hfix
    let a1 := a.transport g hfix
    have h10 : a1.val.map 0 = a.val.map 0 := hfix _ a.val.start_marked
    have h11 : a1.val.map 1 = a.val.map 1 := hfix _ a.val.end_marked
    have hclass (c : EssentialMarkedArc M) :
        Quotient.mk (essentialArcSetoid M) (c.transport g hfix) = Quotient.mk (essentialArcSetoid M) c := by
      apply Eq.symm; apply Quotient.sound
      refine ⟨H,hmarks,?_⟩
      rw [hfinal]
      exact (MarkedArc.transport_image c.val g hfix).symm
    have hold : ∀ i b, (if b then (old' i).val.map 1 else (old' i).val.map 0) = a1.val.map 0 →
        w (i,b) ≠ 0 ∧
        segment ℝ ((chartAt Plane (a1.val.map 0)) (a1.val.map 0))
          ((chartAt Plane (a1.val.map 0)) (a1.val.map 0)+w (i,b)) ⊆ (chartAt Plane (a1.val.map 0)).target ∧
        Set.range ((old' i).val.map ∘ endpointGermParameter b r hr (by linarith)) =
          (chartAt Plane (a1.val.map 0)).symm ''
            segment ℝ ((chartAt Plane (a1.val.map 0)) (a1.val.map 0))
              ((chartAt Plane (a1.val.map 0)) (a1.val.map 0)+w (i,b)) := by
      intro i b hb
      have he : (if b then (old i).val.map 1 else (old i).val.map 0) = a.val.map 0 := by
        have h0 : (old' i).val.map 0 = (old i).val.map 0 := hfix _ (old i).val.start_marked
        have h1 : (old' i).val.map 1 = (old i).val.map 1 := hfix _ (old i).val.end_marked
        simpa only [h0,h1,h10] using hb
      obtain ⟨hw,hwt,hwr⟩ := hstar i b he
      refine ⟨hw,by simpa only [h10] using hwt,?_⟩
      rw [h10]
      change Set.range (g ∘ ((old i).val.map ∘ endpointGermParameter b r hr _)) = _
      rw [Set.range_comp,← hfinal]
      exact hwr
    have hloop1 : a1.val.map 0 = a1.val.map 1 := by rw [h10,h11]; exact hloop
    obtain ⟨b,δ,hδ,hδhalf,hbclass,hb0,hb1,hclear⟩ :=
      actualLoopGermClearanceAgainstNormalizedOldStar M C old' a1 hloop1 r hr hrhalf w hold
    exact ⟨H,hmarks,g,hfix,hfinal,b,δ,hδ,hδhalf,
      hbclass.trans (hclass a),hb0.trans h10,hb1.trans h11,hclear⟩
  have hFiniteContactAllArcBothClearance
      (C : SphereSmoothAtlas S) {ι : Type} [Fintype ι]
      (old : ι → EssentialMarkedArc M)
      (hfinite : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
      (a : EssentialMarkedArc M) :
      ∃ H : AmbientIsotopy S,
        (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
        ∃ g : S ≃ₜ S, ∃ hfix : ∀ x, x ∈ M.cover.branch → g x=x,
          H.finalMap=g ∧ ∃ b : EssentialMarkedArc M, ∃ δ : ℝ,
          0 < δ ∧ δ < 1/2 ∧ vertex M b=vertex M a ∧
          b.val.map 0=a.val.map 0 ∧ b.val.map 1=a.val.map 1 ∧
          ∀ t : Interval, 0 < t.val → t.val < 1 → t.val ≤ δ ∨ 1-δ ≤ t.val →
            ∀ i, b.val.map t ∉ ((old i).transport g hfix).val.image := by
    by_cases hloop : a.val.map 0=a.val.map 1
    · exact hFiniteContactLoopBothClearance C old hfinite a hloop
    · exact hFiniteContactNonloopBothClearance C old hfinite a hloop
  have hOuterPreparedAwayContacts {ι : Type} [Fintype ι]
      (old : ι → EssentialMarkedArc M) (O : Set S) (hOc : IsCompact O)
      (hOldO : ∀ i, Disjoint (arcInterior M (old i)) O)
      (p : S) (hp : p ∉ M.cover.branch)
      (hpc : p ∉ ⋃ i, ⋃ j, if i=j then ∅ else crossings M (old i) (old j)) :
      ∃ e : OpenPartialHomeomorph S Plane,
        p ∈ e.source ∧ Disjoint e.source (M.cover.branch : Set S) ∧
        ∃ label : Option ι,
          (∀ j, label=some j → Disjoint (closure e.source) O) ∧
          ∀ j x, x ∈ e.source →
            (x ∈ (old j).val.image ↔ label=some j ∧ e x 0=0) := by
    letI : T2Space S := M.sphere.symm.t2Space
    letI : CompactSpace S := M.sphere.symm.compactSpace
    obtain ⟨e0,hp0,hm0,label,hinc,haxis⟩ := hPreparedAwayContacts old p hp hpc
    cases hl : label with
    | none =>
      exact ⟨e0,hp0,hm0,none,(by intro j hj; cases hj),by simpa [hl] using haxis⟩
    | some i =>
      have hpO : p ∉ O := fun ho => Set.disjoint_left.mp (hOldO i) ⟨hinc i hl,hp⟩ ho
      have hnear : e0.source ∩ Oᶜ ∈ nhds p :=
        (e0.open_source.inter hOc.isClosed.isOpen_compl).mem_nhds ⟨hp0,hpO⟩
      obtain ⟨C,hC,hCc,hCe⟩ := exists_mem_nhds_isClosed_subset hnear
      let e := e0.restr (interior C)
      have hs : e.source=e0.source ∩ interior C := by
        simp only [e,OpenPartialHomeomorph.restr_source,interior_interior]
      have hsub : e.source ⊆ C := fun x hx => interior_subset (hs ▸ hx).2
      have hcl : closure e.source ⊆ C := hCc.closure_subset_iff.mpr hsub
      refine ⟨e,hs.symm ▸ ⟨hp0,mem_interior_iff_mem_nhds.mpr hC⟩,
        hm0.mono_left (fun _ hx => (hs ▸ hx).1),some i,?_,?_⟩
      · intro j hj
        exact Set.disjoint_left.mpr (fun x hx ho => (hCe (hcl hx)).2 ho)
      · intro j x hx
        change x ∈ (old j).val.image ↔ some i=some j ∧ e0 x 0=0
        simpa only [hl] using haxis j x (hs ▸ hx).1
  have hFiniteContactOuterCollaredMesh {ι : Type} [Fintype ι]
      (old : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
      (hNodeFree : ∀ p ∈ ⋃ i, ⋃ j, if i=j then ∅ else crossings M (old i) (old j),
        p ∉ a.val.image)
      (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1/2)
      (hoff : ∀ t : Interval, 0 < t.val → t.val < 1 → t.val ≤ δ ∨ 1-δ ≤ t.val →
        ∀ i, a.val.map t ∉ (old i).val.image) :
      ∃ η : C(Interval,S),
        (∀ t, η t = a.val.map ⟨δ/2+(1-δ)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩) ∧
        IsClosedEmbedding η ∧ ∃ n : ℕ, ∃ hn : 0 < n,
        ∃ e : Fin n → OpenPartialHomeomorph S Plane, ∃ label : Fin n → Option ι,
          (∀ k, Disjoint (e k).source (M.cover.branch : Set S)) ∧
          (∀ k j x, x ∈ (e k).source →
            (x ∈ (old j).val.image ↔ label k=some j ∧ e k x 0=0)) ∧
          (∀ k j, label k=some j → Disjoint (closure (e k).source)
            (a.val.map '' {t : Interval | t.val≤δ ∨ 1-δ≤t.val})) ∧
          ∀ k t, (k.val:ℝ)/n≤t.val → t.val≤(k.val+1:ℝ)/n → η t∈(e k).source := by
    letI : T2Space S := M.sphere.symm.t2Space
    let O : Set S := a.val.map '' {t : Interval | t.val≤δ ∨ 1-δ≤t.val}
    have hOc : IsCompact O :=
      ((isClosed_le continuous_subtype_val continuous_const).union
        (isClosed_le continuous_const continuous_subtype_val)).isCompact.image a.val.continuous
    have hOldO (i : ι) : Disjoint (arcInterior M (old i)) O := by
      apply Set.disjoint_left.mpr
      rintro p hp ⟨t,ht,rfl⟩
      have ht0 : 0 < t.val := by
        by_contra hn
        have he : t=0 := Subtype.ext (le_antisymm (le_of_not_gt hn) t.property.1)
        exact hp.2 (he ▸ a.val.start_marked)
      have ht1 : t.val < 1 := by
        by_contra hn
        have he : t=1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt hn))
        exact hp.2 (he ▸ a.val.end_marked)
      exact hoff t ht0 ht1 ht i hp.1
    let η : C(Interval,S) := ⟨fun t => a.val.map
      ⟨δ/2+(1-δ)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩,
      a.val.continuous.comp (by fun_prop)⟩
    have hi : IsClosedEmbedding η := η.continuous.isClosedEmbedding (by
      intro t u he
      rcases a.val.injective_except_loop_closure _ _ he with he|he|he
      · have hh := congrArg Subtype.val he
        exact Subtype.ext (by change δ/2+(1-δ)*t.val=δ/2+(1-δ)*u.val at hh; nlinarith)
      · have hh := congrArg Subtype.val he.1
        change δ/2+(1-δ)*t.val=0 at hh
        nlinarith [t.property.1,t.property.2]
      · have hh := congrArg Subtype.val he.1
        change δ/2+(1-δ)*t.val=1 at hh
        nlinarith [t.property.1,t.property.2])
    have hm (t : Interval) : η t ∉ M.cover.branch := by
      intro ht
      rcases a.val.marked_only_at_ends _ ht with he|he
      · have hh := congrArg Subtype.val he
        change δ/2+(1-δ)*t.val=0 at hh
        nlinarith [t.property.1,t.property.2]
      · have hh := congrArg Subtype.val he
        change δ/2+(1-δ)*t.val=1 at hh
        nlinarith [t.property.1,t.property.2]
    have hnc (t : Interval) : η t ∉ ⋃ i, ⋃ j,
        if i=j then ∅ else crossings M (old i) (old j) := by
      intro hn
      exact hNodeFree (η t) hn ⟨⟨δ/2+(1-δ)*t.val,by constructor <;>
        nlinarith [t.property.1,t.property.2]⟩,rfl⟩
    have hlocal (t : Interval) := hOuterPreparedAwayContacts old O hOc hOldO (η t) (hm t) (hnc t)
    choose e hpoint hmarks label houter haxis using hlocal
    obtain ⟨n,hn,choice,hsub⟩ := CurveComplex.position_interval_subdivision η
      (fun t => (e t).source) (fun t => (e t).open_source) (fun t => ⟨t,hpoint t⟩)
    exact ⟨η,fun _ => rfl,hi,n,hn,fun k => e (choice k),fun k => label (choice k),
      fun k => hmarks (choice k),fun k => haxis (choice k),fun k => houter (choice k),hsub⟩
  have hPointOffFiniteSystem {ι : Type} [Fintype ι]
      (old : ι → EssentialMarkedArc M) (p : S) (hp : p ∉ M.cover.branch)
      (hpc : p ∉ ⋃ i, ⋃ j, if i=j then ∅ else crossings M (old i) (old j))
      (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
      ∃ H : AmbientIsotopy S,
        (∀ j, H.finalMap p ∉ (old j).val.image) ∧
        (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
        ∀ t x, x ∉ W → H.map (t,x)=x := by
    by_cases hnone : ∀ j, p ∉ (old j).val.image
    · exact ⟨AmbientIsotopy.identity S,hnone,(fun _ _ _ => rfl),fun _ _ _ => rfl⟩
    push_neg at hnone
    obtain ⟨i,hpi⟩ := hnone
    obtain ⟨e,hpe,hm,label,_,haxis⟩ := hPreparedAwayContacts old p hp hpc
    have hi : label=some i := ((haxis i p hpe).mp hpi).1
    obtain ⟨H,hmove,hmarks,_,hfix⟩ := actualRelativePointOffTarget M (old i) ∅
      isCompact_empty (Set.disjoint_empty _) p hp (Set.notMem_empty _)
      (W ∩ e.source) (hW.inter e.open_source) ⟨hpW,hpe⟩
    have hstay : H.finalMap p ∈ W ∩ e.source := by
      by_contra hn
      obtain ⟨g,hg⟩ := H.homeomorphism_at 1
      have hh : g (H.finalMap p)=g p := by
        rw [hg,hg]
        exact hfix 1 _ hn
      have he : H.finalMap p=p := g.injective hh
      exact hn (he.symm ▸ ⟨hpW,hpe⟩)
    refine ⟨H,?_,hmarks,?_⟩
    · intro j hj
      have hjlabel := ((haxis j (H.finalMap p) hstay.2).mp hj).1
      have hij : i=j := Option.some.inj (hi.symm.trans hjlabel)
      subst j
      exact hmove hj
    · intro t x hx
      exact hfix t x (fun h => hx h.1)
  have hFiniteSystemLocalizedSeamRepair
      {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
      (old : ι → EssentialMarkedArc M) (P : Set S) (hPc : IsCompact P)
      (hOldP : ∀ j, Disjoint (arcInterior M (old j)) P)
      (p : κ → S) (hpi : Function.Injective p)
      (hpmark : ∀ k, p k ∉ M.cover.branch)
      (hpnode : ∀ k, p k ∉ ⋃ i, ⋃ j, if i=j then ∅ else crossings M (old i) (old j))
      (arc : μ → C(Interval,S)) (e : μ → OpenPartialHomeomorph S Plane)
      (hchart : ∀ i, Set.range (arc i) ⊆ (e i).source)
      (W : κ → Set S) (hW : ∀ k, IsOpen (W k)) (hpW : ∀ k, p k ∈ W k) :
      ∃ U : κ → Set S, ∃ H : AmbientIsotopy S,
        (∀ k, IsOpen (U k)) ∧ (∀ k, p k ∈ U k) ∧
        (∀ k, U k ⊆ W k) ∧ (∀ k l, k ≠ l → Disjoint (U k) (U l)) ∧
        (∀ k j, H.finalMap (p k) ∉ (old j).val.image) ∧
        (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
        (∀ t x, x ∈ P → H.map (t,x)=x) ∧
        (∀ t x, x ∉ ⋃ k, U k → H.map (t,x)=x) ∧
        (∀ i t, (fun x => H.map (t,x)) '' Set.range (arc i) ⊆ (e i).source) ∧
        ∀ t k x, x∈U k → H.map (t,x)∈U k := by
    classical
    let : T2Space S := M.sphere.symm.t2Space
    have hclosed (i : μ) : IsClosed (Set.range (arc i)) :=
      (isCompact_range (arc i).continuous).isClosed
    let V : κ → μ → Set S := fun k i =>
      if p k ∈ Set.range (arc i) then (e i).source else (Set.range (arc i))ᶜ
    have hVopen (k i) : IsOpen (V k i) := by
      dsimp [V]; split
      · exact (e i).open_source
      · exact (hclosed i).isOpen_compl
    have hpV (k i) : p k ∈ V k i := by
      dsimp [V]; split
      · rename_i hi; exact hchart i hi
      · assumption
    obtain ⟨D,hD,hDdis⟩ := (Set.finite_range p).t2_separation
    let U : κ → Set S := fun k => W k ∩ (D (p k) ∩ ⋂ i, V k i)
    have hU (k) : IsOpen (U k) :=
      (hW k).inter ((hD (p k)).2.inter (isOpen_iInter_of_finite (hVopen k)))
    have hpU (k) : p k ∈ U k :=
      ⟨hpW k,(hD (p k)).1,Set.mem_iInter.mpr (hpV k)⟩
    have hdis (k l) (hkl : k ≠ l) : Disjoint (U k) (U l) :=
      (hDdis (Set.mem_range_self k) (Set.mem_range_self l)
        (fun hh => hkl (hpi hh))).mono (fun _ hx => hx.2.1) (fun _ hx => hx.2.1)
    have hmove (k) : ∃ H : AmbientIsotopy S,
        (∀ j, H.finalMap (p k) ∉ (old j).val.image) ∧
        (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
        (∀ t x, x ∈ P → H.map (t,x)=x) ∧
        ∀ t x, x ∉ U k → H.map (t,x)=x := by
      by_cases hk : p k ∈ P
      · refine ⟨AmbientIsotopy.identity S,?_,(fun _ _ _ => rfl),(fun _ _ _ => rfl),fun _ _ _ => rfl⟩
        intro j hj
        exact Set.disjoint_left.mp (hOldP j) ⟨hj,hpmark k⟩ hk
      · obtain ⟨H,hoff,hmarks,hfix⟩ := hPointOffFiniteSystem old (p k) (hpmark k) (hpnode k)
          (U k ∩ Pᶜ) ((hU k).inter hPc.isClosed.isOpen_compl) ⟨hpU k,hk⟩
        exact ⟨H,hoff,hmarks,(fun t x hx => hfix t x (fun h => h.2 hx)),
          fun t x hx => hfix t x (fun h => hx h.1)⟩
    choose moves hoff hmarks hgraph hfix using hmove
    obtain ⟨H,hout,hinside⟩ := finite_supported_patch_assembly U hdis moves hfix
    have hstay (t : Interval) (k : κ) (x : S) (hx : x ∈ U k) : H.map (t,x) ∈ U k := by
      rw [hinside k t x hx]
      by_contra hn
      obtain ⟨g,hg⟩ := (moves k).homeomorphism_at t
      have hfixed : (moves k).map (t,(moves k).map (t,x)) = (moves k).map (t,x) :=
        hfix k t _ hn
      have heq : (moves k).map (t,x) = x := g.injective (by simpa only [hg] using hfixed)
      exact hn (heq.symm ▸ hx)
    refine ⟨U,H,hU,hpU,(fun _ => inter_subset_left),hdis,?_,?_,?_,hout,?_,?_⟩
    · intro k j
      change H.map (⟨1,by norm_num⟩,p k) ∉ _
      rw [hinside k ⟨1,by norm_num⟩ (p k) (hpU k)]
      exact hoff k j
    · intro t x hx
      by_cases hi : x ∈ ⋃ k, U k
      · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hi
        rw [hinside k t x hk]; exact hmarks k t x hx
      · exact hout t x hi
    · intro t x hx
      by_cases hi : x ∈ ⋃ k, U k
      · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hi
        rw [hinside k t x hk]; exact hgraph k t x hx
      · exact hout t x hi
    · intro i t y hy
      obtain ⟨x,hx,rfl⟩ := hy
      by_cases hi : x ∈ ⋃ k, U k
      · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hi
        have hpC : p k ∈ Set.range (arc i) := by
          by_contra hn
          have hv := Set.mem_iInter.mp hk.2.2 i
          exact (show x ∉ Set.range (arc i) by simpa only [V,ite_eq_right hn,Set.mem_compl_iff] using hv) hx
        have hv := Set.mem_iInter.mp (hstay t k x hk).2.2 i
        simpa only [V,ite_eq_left hpC] using hv
      · change H.map (t,x) ∈ (e i).source
        rw [hout t x hi]; exact hchart i hx
  
  
    · intro t k x hx
      exact hstay t k x hx
  
  
  have hFiniteContactPreparedWholeMesh
      (C : SphereSmoothAtlas S) {ι : Type} [Fintype ι]
      (old : ι → EssentialMarkedArc M)
      (hfinite : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
      (a : EssentialMarkedArc M) :
      ∃ H : AmbientIsotopy S,
        (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
        ∃ g : S ≃ₜ S, ∃ hfix : ∀ x, x ∈ M.cover.branch → g x=x,
          H.finalMap=g ∧ ∃ b : EssentialMarkedArc M, vertex M b=vertex M a ∧
          ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ hδhalf : δ < 1/2,
          (∀ t : Interval, 0 < t.val → t.val < 1 → t.val ≤ δ ∨ 1-δ ≤ t.val →
            ∀ j, b.val.map t ∉ ((old j).transport g hfix).val.image) ∧
          ∃ η : C(Interval,S),
            (∀ t, η t = b.val.map ⟨δ+(1-2*δ)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩) ∧
            IsClosedEmbedding η ∧ ∃ n : ℕ, ∃ hn : 0 < n,
            ∃ e : Fin n → OpenPartialHomeomorph S Plane, ∃ label : Fin n → Option ι,
              (∀ k, Disjoint (e k).source (M.cover.branch : Set S)) ∧
              (∀ k j x, x ∈ (e k).source →
                (x ∈ ((old j).transport g hfix).val.image ↔ label k=some j ∧ e k x 0=0)) ∧
              (∀ k t, η (CurveComplex.ArcFinitePosition.intervalMeshParameter n hn k t) ∈ (e k).source) ∧
              ∀ k j, η (CurveComplex.ArcFinitePosition.intervalMeshParameter n hn k 0) ∉ ((old j).transport g hfix).val.image ∧
                η (CurveComplex.ArcFinitePosition.intervalMeshParameter n hn k 1) ∉ ((old j).transport g hfix).val.image := by
    classical
    let : T2Space S := M.sphere.symm.t2Space
    obtain ⟨H,hHm,g,hgfix,hfinal,b0,δ,hδ,hδhalf,hb0,hb00,hb01,hoff0⟩ :=
      hFiniteContactAllArcBothClearance C old hfinite a
    let old' : ι → EssentialMarkedArc M := fun i => (old i).transport g hgfix
    let nodes : Set S := ⋃ i, ⋃ j, if i=j then ∅ else crossings M (old' i) (old' j)
    have hnodes : nodes.Finite := by
      apply Set.finite_iUnion
      intro i
      apply Set.finite_iUnion
      intro j
      split
      · exact Set.finite_empty
      · rw [actual_crossings_transport (old i) (old j) g hgfix]
        exact (hfinite i j ‹i ≠ j›).image g
    let R : Set S := b0.val.map '' {t : Interval | t.val≤δ ∨ 1-δ≤t.val}
    have hRc : IsCompact R :=
      ((isClosed_le continuous_subtype_val continuous_const).union
        (isClosed_le continuous_const continuous_subtype_val)).isCompact.image b0.val.continuous
    have hnodesMark (p : S) (hp : p ∈ nodes) : p ∉ M.cover.branch := by
      obtain ⟨i,j,hp⟩ := Set.mem_iUnion₂.mp hp
      split at hp
      · exact (Set.notMem_empty _ hp).elim
      · exact hp.1.2
    have hnodesR (p : S) (hp : p ∈ nodes) : p ∉ R := by
      obtain ⟨i,j,hp⟩ := Set.mem_iUnion₂.mp hp
      split at hp
      · exact (Set.notMem_empty _ hp).elim
      · rintro ⟨t,ht,he⟩
        have htm : b0.val.map t ∉ M.cover.branch := he ▸ hp.1.2
        have ht0 : 0 < t.val := by
          by_contra hn
          have he0 : t=0 := Subtype.ext (le_antisymm (le_of_not_gt hn) t.property.1)
          exact htm (he0 ▸ b0.val.start_marked)
        have ht1 : t.val < 1 := by
          by_contra hn
          have he1 : t=1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt hn))
          exact htm (he1 ▸ b0.val.end_marked)
        exact hoff0 t ht0 ht1 ht i (he ▸ hp.1.1)
    obtain ⟨b,hbclass,hbR,hbNodes⟩ := hAvoidFiniteNodes b0 hnodes.toFinset
      (fun p hp => hnodesMark p (hnodes.mem_toFinset.mp hp)) R hRc.isClosed
      (fun p hp => hnodesR p (hnodes.mem_toFinset.mp hp))
    have hb : vertex M b=vertex M a := hbclass.trans hb0
    have hoff : ∀ t : Interval, 0 < t.val → t.val < 1 → t.val≤δ ∨ 1-δ≤t.val →
        ∀ i, b.val.map t ∉ (old' i).val.image := by
      intro t ht0 ht1 ht i
      rw [hbR t ⟨t,ht,rfl⟩]
      exact hoff0 t ht0 ht1 ht i
    have hNodeFree : ∀ p ∈ nodes, p ∉ b.val.image :=
      fun p hp => hbNodes p (hnodes.mem_toFinset.mpr hp)
    obtain ⟨η,hη,hi,n,hn,e,label,hemarks,haxis,hclosed,hsub⟩ :=
      hFiniteContactOuterCollaredMesh old' b hNodeFree δ hδ hδhalf hoff
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    let grid : Fin (n+1) → Interval := fun k => ⟨k.val/n,by
      constructor
      · positivity
      · apply (div_le_one hnR).mpr
        have hk : k.val≤n := by omega
        exact_mod_cast hk⟩
    let p : Fin (n+1) → S := η ∘ grid
    have hpi : Function.Injective p := by
      intro i j he
      have hh := congrArg Subtype.val (hi.injective he)
      have he' : (i.val:ℝ)=(j.val:ℝ) := (div_left_inj' hnR.ne').mp hh
      apply Fin.ext
      exact_mod_cast he'
    have hpm (k : Fin (n+1)) : p k ∉ M.cover.branch := by
      intro hm
      rw [show p k=η (grid k) from rfl,hη] at hm
      rcases b.val.marked_only_at_ends _ hm with he|he
      · have hh := congrArg Subtype.val he
        change δ/2+(1-δ)*(grid k).val=0 at hh
        nlinarith [(grid k).property.1,(grid k).property.2]
      · have hh := congrArg Subtype.val he
        change δ/2+(1-δ)*(grid k).val=1 at hh
        nlinarith [(grid k).property.1,(grid k).property.2]
    let O : Set S := b.val.map '' {t : Interval | t.val≤δ ∨ 1-δ≤t.val}
    have hOc : IsCompact O :=
      ((isClosed_le continuous_subtype_val continuous_const).union
        (isClosed_le continuous_const continuous_subtype_val)).isCompact.image b.val.continuous
    have hOldO (i : ι) : Disjoint (arcInterior M (old' i)) O := by
      apply Set.disjoint_left.mpr
      rintro p hp ⟨t,ht,rfl⟩
      have ht0 : 0 < t.val := by
        by_contra hn
        have he : t=0 := Subtype.ext (le_antisymm (le_of_not_gt hn) t.property.1)
        exact hp.2 (he ▸ b.val.start_marked)
      have ht1 : t.val < 1 := by
        by_contra hn
        have he : t=1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt hn))
        exact hp.2 (he ▸ b.val.end_marked)
      exact hoff t ht0 ht1 ht i hp.1
    let arc : Fin n → C(Interval,S) := fun k =>
      ⟨η ∘ CurveComplex.ArcFinitePosition.intervalMeshParameter n hn k,
        η.continuous.comp (CurveComplex.ArcFinitePosition.intervalMeshParameter_continuous n hn k)⟩
    have hchart (k : Fin n) : range (arc k) ⊆ (e k).source := by
      rintro x ⟨t,rfl⟩
      apply hsub k
      · apply (div_le_div_iff_of_pos_right hnR).mpr
        linarith [t.property.1]
      · apply (div_le_div_iff_of_pos_right hnR).mpr
        linarith [t.property.2]
    have hpnode (k : Fin (n+1)) : p k ∉ nodes := by
      intro hp
      apply hNodeFree (p k) hp
      exact ⟨⟨δ/2+(1-δ)*(grid k).val,by constructor <;>
        nlinarith [(grid k).property.1,(grid k).property.2]⟩,by exact hη (grid k) |>.symm⟩
    obtain ⟨U,K,_,_,_,_,hends,hKm,hKfixO,_,hstay,_⟩ := hFiniteSystemLocalizedSeamRepair
      old' O hOc hOldO p hpi hpm hpnode arc e hchart
      (fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.mem_univ _)
    obtain ⟨k,hk⟩ := K.homeomorphism_at (1 : Interval)
    have hfix : ∀ x, x ∈ M.cover.branch → k x=x := fun x hx => (hk x).trans (hKm 1 x hx)
    let c := b.transport k hfix
    have hclass : ArcSurgery.vertex M c = ArcSurgery.vertex M b := by
      apply Eq.symm; apply Quotient.sound
      refine ⟨K,hKm,?_⟩
      change K.finalMap '' b.val.image = (b.val.transport k hfix).image
      rw [MarkedArc.transport_image]
      congr 1
      funext x
      exact (hk x).symm
    let d : ℝ := δ/2
    have hd : 0 < d := by dsimp [d]; positivity
    have hdhalf : d < 1/2 := by dsimp [d]; linarith
    let ζ : C(Interval,S) := ⟨k ∘ η,k.continuous.comp η.continuous⟩
    have hζliteral (t : Interval) : ζ t = c.val.map
        ⟨d+(1-2*d)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩ := by
      change k (η t) = k _
      rw [hη]
      apply congrArg k; apply congrArg b.val.map; apply Subtype.ext
      dsimp [d]
      ring
    have hζchart (i : Fin n) (t : Interval) :
        ζ (CurveComplex.ArcFinitePosition.intervalMeshParameter n hn i t) ∈ (e i).source := by
      change k (η _) ∈ _
      rw [hk]
      exact hstay i 1 ⟨η _,⟨t,rfl⟩,rfl⟩
    have hseams (i : Fin n) :
        ∀ j, ζ (CurveComplex.ArcFinitePosition.intervalMeshParameter n hn i 0) ∉ (old' j).val.image ∧
        ζ (CurveComplex.ArcFinitePosition.intervalMeshParameter n hn i 1) ∉ (old' j).val.image := by
      intro j
      have he0 : CurveComplex.ArcFinitePosition.intervalMeshParameter n hn i 0=grid ⟨i.val,by omega⟩ := by
        apply Subtype.ext
        simp [CurveComplex.ArcFinitePosition.intervalMeshParameter,grid]
      have he1 : CurveComplex.ArcFinitePosition.intervalMeshParameter n hn i 1=grid ⟨i.val+1,by omega⟩ := by
        apply Subtype.ext
        simp [CurveComplex.ArcFinitePosition.intervalMeshParameter,grid]
      change k (η _) ∉ _ ∧ k (η _) ∉ _
      rw [hk,hk,he0,he1]
      exact ⟨hends _ j,hends _ j⟩
    refine ⟨H,hHm,g,hgfix,hfinal,c,hclass.trans hb,d,hd,hdhalf,?_,ζ,hζliteral,?_,
      n,hn,e,label,hemarks,haxis,hζchart,hseams⟩
    · intro t ht0 ht1 houter j
      change k (b.val.map t) ∉ (old' j).val.image
      rw [hk]
      have hto : t.val≤δ ∨ 1-δ≤t.val := by
        rcases houter with ht|ht
        · left; dsimp [d] at ht; linarith
        · right; dsimp [d] at ht; linarith
      rw [hKfixO 1 _ ⟨t,hto,rfl⟩]
      exact hoff t ht0 ht1 hto j
    · exact ζ.continuous.isClosedEmbedding (k.injective.comp hi.injective)
  have hFixedFiniteTransverseInsertion {ι : Type} [Fintype ι]
      (old : ι → EssentialMarkedArc M)
      (hfinite : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
      (a : EssentialMarkedArc M) :
      ∃ b : EssentialMarkedArc M, vertex M b=vertex M a ∧
        ∀ i, (crossings M (old i) b).Finite ∧
          ∀ p ∈ crossings M (old i) b, CrossesInDisk M (old i) b p := by
    obtain ⟨H,hHm,g,hgfix,hfinal,a1,hclassA,δ,hδ,hδhalf,hclear,
      η,hη,hi,n,hn,e,label,hemarks,hlabel,hchart,hends⟩ :=
      hFiniteContactPreparedWholeMesh (actualSphereSmoothAtlas M) old hfinite a
    let old' : ι → EssentialMarkedArc M := fun i => (old i).transport g hgfix
    have hlu : δ < 1-δ := by linarith
    have hu : 1-δ < 1 := by linarith
    have hη' (t : Interval) : η t = a1.val.map
        ⟨δ+((1-δ)-δ)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩ := by
      rw [hη]
      apply congrArg a1.val.map; apply Subtype.ext
      change δ+(1-2*δ)*(t:ℝ) = δ+((1-δ)-δ)*(t:ℝ)
      ring
    obtain ⟨α,β,F,hbounds,hFsub,hFdis,hFmarks,hFsq,hFends,hFflat,hFexact,hFoff,houtside⟩ :=
      actual_trimmed_marked_crosscut_assembly M old' a1 δ (1-δ) hδ hlu hu η hη'
        hi.injective n hn e hemarks hchart hends hclear
    have hcentral (k : Fin n) :
        (a1.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) ⊆ (F k).source := by
      intro x hx
      rw [← hFexact k] at hx
      exact hx.1.1
    obtain ⟨d,hdclass,hcontacts⟩ := actual_finite_transverse_crosscut_redrawing M old' a1
      e F label α β hbounds hFsub hFdis hFmarks hFsq hcentral hFends hFflat hFexact
      hlabel hFoff houtside
    have hginvfix : ∀ x, x ∈ M.cover.branch → g.symm x=x := by
      intro x hx
      apply g.injective
      rw [g.apply_symm_apply,hgfix x hx]
    let b := d.transport g.symm hginvfix
    have hbclass : vertex M b=vertex M d := by
      apply Quotient.sound
      refine ⟨H,hHm,?_⟩
      change H.finalMap '' (d.val.transport g.symm hginvfix).image = d.val.image
      rw [hfinal,MarkedArc.transport_image,Set.image_image]
      simp only [Function.comp_def,Homeomorph.apply_symm_apply,Set.image_id']
    have himage (i : ι) : g.symm '' (old' i).val.image=(old i).val.image := by
      change g.symm '' ((old i).val.transport g hgfix).image=_
      rw [MarkedArc.transport_image,Set.image_image]
      simp only [Function.comp_def,Homeomorph.symm_apply_apply,Set.image_id']
    refine ⟨b,hbclass.trans (hdclass.trans hclassA),?_⟩
    intro i
    have hsub : crossings M (old' i) d ⊆ arcInterior M d ∩ (old' i).val.image :=
      fun p hp => ⟨hp.2,hp.1.1⟩
    have hcross : crossings M (old i) b=g.symm '' crossings M (old' i) d :=
      actualCrossingsTransportToSpecifiedAnchor M (old' i) d (old i) g.symm hginvfix (himage i)
    constructor
    · rw [hcross]
      exact ((hcontacts i).1.subset hsub).image g.symm
    · intro p hp
      rw [hcross] at hp
      obtain ⟨q,hq,rfl⟩ := hp
      exact actualCrossingDiskTransportToSpecifiedAnchor M (old' i) d (old i)
        g.symm hginvfix (himage i) q ((hcontacts i).2 q (hsub hq))
  have hSymm (a b : EssentialMarkedArc M) (p : S)
      (hc : CrossesInDisk M a b p) : CrossesInDisk M b a p := by
    obtain ⟨U,hU,hp,hmark,e,he0,ha,hb⟩ := hc
    let Q := {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}
    let swap : Q ≃ₜ Q := (Homeomorph.prodComm ℝ ℝ).subtype (fun _ => and_comm)
    refine ⟨U,hU,hp,hmark,e.trans swap,?_,?_,?_⟩
    · change ((e ⟨p,hp⟩).val.2,(e ⟨p,hp⟩).val.1)=(0,0)
      rw [he0]
    · exact hb
    · exact ha
  have hReverse (a b : EssentialMarkedArc M)
      (h : (crossings M a b).Finite ∧ ∀ p ∈ crossings M a b, CrossesInDisk M a b p) :
      (crossings M b a).Finite ∧ ∀ p ∈ crossings M b a, CrossesInDisk M b a p := by
    have he : crossings M b a=crossings M a b := Set.inter_comm _ _
    exact ⟨he ▸ h.1,fun p hp => hSymm a b p (h.2 p (he ▸ hp))⟩
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨fun v => False.elim (Finset.notMem_empty v.val v.property),?_,?_,?_⟩
    · intro v; exact False.elim (Finset.notMem_empty v.val v.property)
    · intro v; exact False.elim (Finset.notMem_empty v.val v.property)
    · intro v; exact False.elim (Finset.notMem_empty v.val v.property)
  | @insert v F hv ih =>
    obtain ⟨r,hr,hanchor,hmutual⟩ := ih
    let old : Option {u // u ∈ F} → EssentialMarkedArc M := fun i =>
      match i with | none => anchor | some u => r u
    have hf : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite := by
      intro i j hij
      cases i with
      | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some w => exact (hanchor w).1
      | some u =>
        cases j with
        | none => exact (hReverse anchor (r u) (hanchor u)).1
        | some w => exact (hmutual u w (fun he => hij (congrArg some he))).1
    obtain ⟨a,ha⟩ := Quotient.exists_rep v
    obtain ⟨b,hb,hnew⟩ := hFixedFiniteTransverseInsertion old hf a
    have hbv : vertex M b=v := hb.trans ha
    let newv : {u // u ∈ insert v F} := ⟨v,Finset.mem_insert_self _ _⟩
    have hmem (u : {u // u ∈ insert v F}) (hu : u ≠ newv) : u.val ∈ F := by
      apply (Finset.mem_insert.mp u.property).resolve_left
      intro he
      exact hu (Subtype.ext he)
    let lift (u : {u // u ∈ insert v F}) (hu : u ≠ newv) : {u // u ∈ F} := ⟨u.val,hmem u hu⟩
    let r' : {u // u ∈ insert v F} → EssentialMarkedArc M :=
      fun u => if hu : u=newv then b else r (lift u hu)
    have hrnew : r' newv=b := by simp [r']
    have hrold (u : {u // u ∈ insert v F}) (hu : u ≠ newv) : r' u=r (lift u hu) := by
      simp [r',hu]
    refine ⟨r',?_,?_,?_⟩
    · intro u
      by_cases hu : u=newv
      · subst u; rw [hrnew]; exact hbv
      · rw [hrold u hu]; exact hr (lift u hu)
    · intro u
      by_cases hu : u=newv
      · subst u; rw [hrnew]; exact hnew none
      · rw [hrold u hu]; exact hanchor (lift u hu)
    · intro u w huw
      by_cases hu : u=newv
      · subst u
        have hw : w ≠ newv := fun he => huw he.symm
        rw [hrnew,hrold w hw]
        exact hReverse (r (lift w hw)) b (hnew (some (lift w hw)))
      · by_cases hw : w=newv
        · subst w
          rw [hrnew,hrold u hu]
          exact hnew (some (lift u hu))
        · rw [hrold u hu,hrold w hw]
          apply hmutual
          intro he
          apply huw
          apply Subtype.ext
          change u.val=w.val
          exact congrArg (fun z : {z // z ∈ F} => z.val) he
end CurveComplex.HyperellipticModel
