import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import CurveComplexGenusTwo.Topology.RestrictedLink.SquareMarkedIsotopyHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.PlanarBoundaryRadialArcHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.PlanarHalfArcCompletionHeaders
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import CurveComplexGenusTwo.Topology.RestrictedLink.PlanarHalfArcSlitConnectedHeaders
import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualLinkArcFaceEndpointHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualObjectEndpointUniformHeaders
import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
import Schoenflies.JordanClosed
import CurveComplexGenusTwo.Topology.RestrictedLink.HomeomorphismComponentHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.RegionComponentHeaders
import CurveComplexGenusTwo.Dependencies.SpherePort
import CurveComplexGenusTwo.Topology.CompletedJordan
import CurveComplexGenusTwo.Topology.ArcStraightening
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Convex.Topology
import CurveComplexGenusTwo.Topology.Extraction
import Schoenflies.Subarc
import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import Schoenflies.MatchedArc
import Schoenflies.Topology
import CurveComplexGenusTwo.Topology.CrosscutFull
import CurveComplexGenusTwo.Topology.CrosscutIsotopy
import Mathlib.Analysis.Convex.Basic
import CurveComplexGenusTwo.Topology.ChartLift
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualOneMarkDiscClassHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualOneMarkSpokeAvoidanceHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualSimplexInsertHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.RestrictedLinkLabelsHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualArcFaceLocalizationHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.RestrictedLinkHeaders
namespace CurveComplex.HyperellipticModel
open Schoenflies Metric Set unitInterval CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance twoMarkAlignedRestrictedLinkDecidableEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
open scoped Classical
set_option maxHeartbeats 24000000
/-- Two-mark case of source Lemmas 10.6 and 10.8. Fixed apex class,
arbitrary original restricted-link simplex, literal original support alignment. -/
theorem actual_two_mark_aligned_restricted_link (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (τ : Finset (EssentialArcClass M)) (hτ : τ ∈ actualRestrictedLink M T)
    (r : {w // w ∈ T.val ∪ τ} → EssentialMarkedArc M)
    (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
    (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hrestrict : ∀ w, r ⟨w.val,Finset.mem_union_left _ w.property⟩ = rT w)
    (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M T.val)
    (U : Set S) (hOU : IsComplementComponent (actualObjectTrace M rT O) U)
    (hUG : IsComplementComponent (⋃ w, (rT w).val.image) U)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (C : Set Plane) (q0 q1 : Plane) (hC : IsJordanCurve C)
    (hU : U = f '' inside C) (hq0 : q0 ∈ inside C) (hq1 : q1 ∈ inside C)
    (hne : q0 ≠ q1)
    (a : EssentialMarkedArc M) (ha0 : a.val.map 0 = f q0) (ha1 : a.val.map 1 = f q1)
    (haIn : a.val.image ⊆ U)
    (hmarks : ∀ z ∈ inside C, f z ∈ M.cover.branch → z = q0 ∨ z = q1) :
    insert (Quotient.mk (essentialArcSetoid M) a) τ ∈ actualRestrictedLink M T := by
  classical
  have disc {C : Set Plane} (hC : IsJordanCurve C) : Nonempty (Plane ≃ₜ inside C) := by
    have straight {C : Set Plane} (hC : IsJordanCurve C) :
      ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
    
      classical
      have outsideComponent {C : Set Plane} (hC : IsJordanCurve C) :
          IsComplementComponent C (outside C) := by
        have hs := jordan_curve_theorem hC
        refine ⟨hs.isConnected_outside.nonempty, hs.isConnected_outside, outside_subset_compl, ?_⟩
        intro V hV hsub hVc
        apply Set.Subset.antisymm
        · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_outside
          · obtain ⟨x, hx⟩ := hs.isConnected_outside.nonempty
            exact ⟨x, hsub hx, hx⟩
          · intro x hx
            rw [(IsRegionOf.outside C).closure_eq hs] at hx
            rcases hx.1 with hi | hc
            · exact hi
            · exact False.elim (hVc hx.2 hc)
        · exact hsub
      obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
      obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
      have him : F '' C = modelCurve := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [hF ⟨y, hy⟩]
          exact (e ⟨y, hy⟩).property
        · intro hx
          let y := e.symm ⟨x, hx⟩
          refine ⟨y.val, y.property, ?_⟩
          rw [hF y]
          exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
      have hc := homeomorphism_complement_component F (jordan_inside_complement_component hC)
      rw [him] at hc
      have hi := jordan_inside_complement_component isJordanCurve_modelCurve
      have ho := outsideComponent isJordanCurve_modelCurve
      obtain ⟨x, hx⟩ := hc.1
      have hxin : x ∈ inside modelCurve ∪ outside modelCurve :=
        (inside_union_outside modelCurve).symm ▸ hc.2.2.1 hx
      have heinside : F '' inside C = inside modelCurve := by
        rcases hxin with hxI | hxO
        · by_contra hn
          exact Set.disjoint_left.mp (complementComponents_disjoint hc hi hn) hx hxI
        · have heoutside : F '' inside C = outside modelCurve := by
            by_contra hn
            exact Set.disjoint_left.mp (complementComponents_disjoint hc ho hn) hx hxO
          have hs := jordan_curve_theorem hC
          have hk : IsCompact (closure (inside C)) :=
            Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
          have hb : Bornology.IsBounded (F '' inside C) :=
            (hk.image F.continuous).isBounded.subset (image_mono subset_closure)
          exact False.elim ((jordan_curve_theorem isJordanCurve_modelCurve).not_isBounded_outside
            (heoutside ▸ hb))
      exact ⟨F, him, heinside.trans inside_modelCurve⟩
    have square : Nonempty (Plane ≃ₜ Plane.openSquare 0 1) := by
    
      let H : Plane ≃ₜ (Fin 2 → ℝ) := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
      let B : (Fin 2 → ℝ) ≃ₜ Metric.ball (0 : Fin 2 → ℝ) 1 := Homeomorph.unitBall
      let K : Metric.ball (0 : Fin 2 → ℝ) 1 ≃ₜ Plane.openSquare 0 1 :=
        H.symm.subtype (fun x => by
          simp only [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
          change (∀ i : Fin 2, ‖x i‖ < 1) ↔ (H.symm x).supDist 0 < 1
          simp [Schoenflies.Plane.supDist, Schoenflies.Plane.supNorm, Fin.forall_fin_two, H, EuclideanSpace.equiv,
            PiLp.toLp_apply, Real.norm_eq_abs])
      exact ⟨(H.trans B).trans K⟩
    obtain ⟨F, _, hFI⟩ := straight hC
    obtain ⟨H⟩ := square
    let R : inside C ≃ₜ Plane.openSquare 0 1 :=
      (F.isEmbedding.homeomorphImage (inside C)).trans (Homeomorph.setCongr hFI)
    exact ⟨H.trans R.symm⟩
  have properCut {J : Set Plane} {p q : Plane} (hJ : IsJordanCurve J)
      (hp : p ∈ J) (hq : q ∈ J) (hpq : p ≠ q) :
      ∃ P : Set Plane, IsArcBetween P p q ∧ P \ {p,q} ⊆ inside J := by
    obtain ⟨z,hz⟩ := (jordan_curve_theorem hJ).isConnected_inside.nonempty
    obtain ⟨A,hA,hAi⟩ := planar_boundary_radial_arc hJ hp hz
    obtain ⟨B,hB,hAB,hBi⟩ := planar_half_arc_completion hJ hA hp hq
      (fun he => hpq he.symm) hAi
    have hP : IsArcBetween (A ∪ B) p q := hA.concatenate hB (by
      intro v hvA hvB
      exact Set.mem_singleton_iff.mp (hAB ▸ (show v ∈ A ∩ B from ⟨hvA,hvB⟩)))
    refine ⟨A ∪ B,hP,?_⟩
    intro v hv
    rcases hv.1 with hvA | hvB
    · exact hAi ⟨hvA,by
        intro he
        exact hv.2 (Or.inl (Set.mem_singleton_iff.mp he))⟩
    · exact hBi ⟨hvB,by
        intro he
        exact hv.2 (Or.inr he)⟩
  have fourStarJoin {D A0 A1 B0 B1 : Set Plane} {x y p q : Plane}
      (hD : IsJordanCurve D)
      (hA0 : IsArcBetween A0 x p) (hA1 : IsArcBetween A1 p y)
      (hB0 : IsArcBetween B0 x q) (hB1 : IsArcBetween B1 q y)
      (hAmeet : A0 ∩ A1 = {p}) (hBmeet : B0 ∩ B1 = {q})
      (hSides : (A0 ∪ A1) ∩ (B0 ∪ B1) = {x,y})
      (hClosed : (A0 ∪ A1) ∪ (B0 ∪ B1) ⊆ inside D ∪ D)
      (hp : p ∈ inside D) (hq : q ∈ inside D) (hpq : p ≠ q) :
      ∃ P : Set Plane, IsArcBetween P p q ∧ P ⊆ inside D ∧
        P \ {p,q} ⊆ ((A0 ∪ A1) ∪ (B0 ∪ B1))ᶜ := by
    have left : IsArcBetween (A0 ∪ A1) x y := hA0.concatenate hA1 (by
      intro z hz0 hz1
      exact Set.mem_singleton_iff.mp (hAmeet ▸ (show z ∈ A0 ∩ A1 from ⟨hz0,hz1⟩)))
    have right : IsArcBetween (B0 ∪ B1) x y := hB0.concatenate hB1 (by
      intro z hz0 hz1
      exact Set.mem_singleton_iff.mp (hBmeet ▸ (show z ∈ B0 ∩ B1 from ⟨hz0,hz1⟩)))
    let J := (A0 ∪ A1) ∪ (B0 ∪ B1)
    have hJ : IsJordanCurve J := by
      apply isJordanCurve_union left right
      intro z hzLeft hzRight
      have hz : z ∈ ({x,y} : Set Plane) :=
        hSides ▸ (show z ∈ (A0 ∪ A1) ∩ (B0 ∪ B1) from ⟨hzLeft,hzRight⟩)
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hz
    have insideSub : inside J ⊆ inside D :=
      CurveComplex.jordan_inside_mono_of_boundary_subset_closed_inside
        (jordan_curve_theorem hD) (jordan_curve_theorem hJ) hClosed
    have hpJ : p ∈ J := Or.inl (Or.inl hA0.right_mem)
    have hqJ : q ∈ J := Or.inr (Or.inl hB0.right_mem)
    obtain ⟨P,hP,hPi⟩ := properCut hJ hpJ hqJ hpq
    refine ⟨P,hP,?_,?_⟩
    · intro z hz
      by_cases hzp : z = p
      · exact hzp ▸ hp
      by_cases hzq : z = q
      · exact hzq ▸ hq
      apply insideSub
      apply hPi
      refine ⟨hz,?_⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      exact not_or.mpr ⟨hzp,hzq⟩
    · intro z hz
      exact inside_subset_compl (hPi hz)
  have tipJoin {D B : Set Plane} {x p q : Plane}
      (hD : IsJordanCurve D) (hB : IsArcBetween B x p) (hx : x ∈ D)
      (hp : p ∈ inside D) (hq : q ∈ inside D) (hpq : p ≠ q)
      (hinB : B \ {x} ⊆ inside D) (hqB : q ∉ B) :
      ∃ P : Set Plane, IsArcBetween P p q ∧ P ⊆ inside D ∧ P ∩ B = {p} := by
    have small {A U : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
        (hU : IsOpen U) (ha : a ∈ U) :
        ∃ B : Set Plane, ∃ c : Plane,
          IsArcBetween B a c ∧ B ⊆ A ∧ B ⊆ U := by
      obtain ⟨f,hf,hi,himage,hf0,hf1⟩ := hA
      let g : ℝ → Plane := fun t => f (projIcc 0 1 zero_le_one t)
      have hg : Continuous g := (continuousOn_iff_continuous_restrict.mp hf).comp continuous_projIcc
      have hg0 : g 0 = a := by simp [g,projIcc_of_mem zero_le_one (by norm_num : (0:ℝ) ∈ Icc 0 1),hf0]
      have hn : g ⁻¹' U ∈ nhds (0:ℝ) := hg.continuousAt.preimage_mem_nhds (hg0.symm ▸ hU.mem_nhds ha)
      obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
      let d := min (ε/2) (1/2:ℝ)
      have hd : 0 < d := lt_min (by linarith) (by norm_num)
      have hd1 : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
      have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hdmem : d ∈ I := ⟨hd.le,hd1⟩
      have hsubI : uIcc (0:ℝ) d ⊆ I := uIcc_subset_I (by norm_num) hdmem
      refine ⟨f '' uIcc (0:ℝ) d,f d,?_,?_,?_⟩
      · simpa only [hf0] using isArcBetween_subarc_of_injOn_I hf hi (by norm_num) hdmem (ne_of_lt hd)
      · rw [← himage]
        exact image_mono hsubI
      · rintro y ⟨t,ht,rfl⟩
        have htc := hsubI ht
        have ht' : 0 ≤ t ∧ t ≤ d := by simpa [uIcc_of_le hd.le] using ht
        have hbt : t ∈ Metric.ball (0:ℝ) ε := by
          rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht'.1]
          exact lt_of_le_of_lt ht'.2 hdε
        have hm := hball hbt
        change g t ∈ U at hm
        simpa only [g,projIcc_of_mem zero_le_one htc] using hm
    obtain ⟨E,u,hE,hu,hEavoid⟩ := endpoint_access_of_isArcBetween hB.reverse
    obtain ⟨E',v,hE',hEsub,hEin⟩ := small hE
      (jordan_curve_theorem hD).isOpen_inside hp
    have hEavoid' : E' \ {p} ⊆ Bᶜ := by
      intro z hz
      exact hEavoid ⟨hEsub hz.1,hz.2⟩
    have hvne : v ≠ p := hE'.ne.symm
    have hvIn : v ∈ inside D \ B :=
      ⟨hEin hE'.right_mem,hEavoid' ⟨hE'.right_mem,by simpa using hvne⟩⟩
    have hconn := planar_half_arc_slit_connected hD hB hx hinB
    have hopen : IsOpen (inside D \ B) :=
      (jordan_curve_theorem hD).isOpen_inside.sdiff hB.isArc.isCompact.isClosed
    have route : ∃ P : Set Plane,
        IsArcBetween P p q ∧ P ⊆ inside D ∧ P \ {p} ⊆ Bᶜ := by
      by_cases hvq : v = q
      · exact ⟨E',hvq ▸ hE',hEin,hEavoid'⟩
      · obtain ⟨R,hRsub,hRpoly,hR⟩ := exists_simple_arc_of_isPreconnected hopen
          hconn.isPreconnected hvIn ⟨hq,hqB⟩ hvq
        obtain ⟨P,hPsub,hP⟩ := exists_arc_in_union_of_arcs hE' hR hpq
        refine ⟨P,hP,?_,?_⟩
        · intro z hz
          rcases hPsub hz with hzE | hzR
          · exact hEin hzE
          · exact (hRsub hzR).1
        · intro z hz
          rcases hPsub hz.1 with hzE | hzR
          · exact hEavoid' ⟨hzE,hz.2⟩
          · exact (hRsub hzR).2
    obtain ⟨P,hP,hPin,hPavoid⟩ := route
    refine ⟨P,hP,hPin,?_⟩
    apply Subset.antisymm
    · intro z hz
      by_contra hzp
      exact hPavoid ⟨hz.1,hzp⟩ hz.2
    · rintro z rfl
      exact ⟨hP.left_mem,hB.right_mem⟩
  have hdiscU : Nonempty (Plane ≃ₜ U) := by
    obtain ⟨H⟩ := disc hC
    exact ⟨(H.trans (hf.isEmbedding.homeomorphImage (inside C))).trans
      (Homeomorph.setCongr hU.symm)⟩
  let v := Quotient.mk (essentialArcSetoid M) a
  by_cases hvτ : v ∈ τ
  · change insert v τ ∈ actualRestrictedLink M T
    simpa only [Finset.insert_eq_of_mem hvτ] using hτ
  have hrT : ∀ w, Quotient.mk (essentialArcSetoid M) (rT w) = w.val := by
    intro w
    rw [← hrestrict w]
    exact hr _
  have hq0U : f q0 ∈ U := hU.symm ▸ mem_image_of_mem f hq0
  have hq1U : f q1 ∈ U := hU.symm ▸ mem_image_of_mem f hq1
  have hfn : f q0 ≠ f q1 := fun he => hne (hf.injective he)
  have ends : markedArcEndset a.val = {f q0, f q1} := by
    change ({a.val.map 0, a.val.map 1} : Finset S) = _
    rw [ha0, ha1]
  have vend : classEndpoints M v = {f q0, f q1} :=
    (markedArcEndset_eq_classEndpoints M a).symm.trans ends
  have noT : ∀ w ∈ T.val, f q0 ∉ classEndpoints M w := by
    intro w hw hqEnd
    have he : markedArcEndset (rT ⟨w,hw⟩).val = classEndpoints M w :=
      (markedArcEndset_eq_classEndpoints M (rT ⟨w,hw⟩)).trans
        (congrArg (classEndpoints M) (hrT ⟨w,hw⟩))
    rw [← he] at hqEnd
    have hqImage : f q0 ∈ (rT ⟨w,hw⟩).val.image := by
      have he' : f q0 ∈ (markedArcEndset (rT ⟨w,hw⟩).val : Set S) := hqEnd
      rw [← markedArc_image_inter_branch] at he'
      exact he'.1
    exact hUG.2.2.1 hq0U (mem_iUnion.mpr ⟨⟨w,hw⟩,hqImage⟩)
  have hvT : v ∉ T.val := by
    intro hv
    exact noT v hv (by rw [vend]; simp)
  have nonloopv : ¬ (actualArcLabels M).isLoop v := by
    change (classEndpoints M v).card ≠ 1
    rw [vend]
    simp [hfn]
  -- Original face localization; this limits the residual geometry to a finite star.
  have faceLabels : ∃ wO ∈ T.val,
      (∀ z ∈ frontier U, z ∈ M.cover.branch → z ∈ classEndpoints M wO) ∧
      ∀ (b : EssentialMarkedArc M) (w : EssentialArcClass M),
      w ∈ τ → Quotient.mk (essentialArcSetoid M) b = w →
      (∀ z, Disjoint (arcInterior M b) (arcInterior M (rT z))) →
      (arcInterior M b ∩ U).Nonempty →
      (({f q0,f q1} : Finset S) ∩ classEndpoints M w).Nonempty ∧
        classEndpoints M w ⊆ {f q0,f q1} ∪ classEndpoints M wO := by
    letI : T2Space S := M.sphere.symm.t2Space
    letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
    have marks (z : S) (hz : z ∈ U) (hb : z ∈ M.cover.branch) :
        z ∈ ({f q0,f q1} : Finset S) := by
      rw [hU] at hz
      obtain ⟨t,ht,rfl⟩ := hz
      rcases hmarks t ht hb with he | he <;> simp [he]
    obtain ⟨wO,hwO,hu⟩ := actual_object_endpoint_labels_uniform M T.val O hO
    have hopen := complementComponent_open (actualObjectTrace_compact M rT O).isClosed hOU
    have hfront := complementComponent_frontier_subset (actualObjectTrace_compact M rT O).isClosed hOU
    have boundary (z : S) (hz : z ∈ frontier U) (hb : z ∈ M.cover.branch) :
        z ∈ classEndpoints M wO := by
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hfront hz)
      obtain ⟨hjO,hzj⟩ := Set.mem_iUnion.mp hj
      have hend : z ∈ (markedArcEndset (rT j).val : Set S) := by
        rw [← markedArc_image_inter_branch]
        exact ⟨hzj,hb⟩
      have he : markedArcEndset (rT j).val = classEndpoints M j.val :=
        (markedArcEndset_eq_classEndpoints M (rT j)).trans
          (congrArg (classEndpoints M) (hrT j))
      rw [he,hu j.val hjO] at hend
      exact hend
    refine ⟨wO,hwO,boundary,?_⟩
    intro b w hw hbw hdT hit
    obtain ⟨hint,hcl,hend⟩ := actual_link_arc_face_has_interior_endpoint
      M p T τ hτ rT hrT O hO U hOU hUG b w hw hbw hdT hit
    have label : markedArcEndset b.val = classEndpoints M w :=
      (markedArcEndset_eq_classEndpoints M b).trans (congrArg (classEndpoints M) hbw)
    have endpoint (z : S) (hz : z ∈ b.val.image) (hb : z ∈ M.cover.branch) :
        z ∈ ({f q0,f q1} : Finset S) ∪ classEndpoints M wO := by
      by_cases hin : z ∈ U
      · exact Finset.mem_union.mpr (Or.inl (marks z hin hb))
      · apply Finset.mem_union.mpr
        apply Or.inr
        apply boundary z ?_ hb
        rw [hopen.frontier_eq]
        exact ⟨hcl hz,hin⟩
    constructor
    · rw [← label]
      rcases hend with h0 | h1
      · refine ⟨b.val.map 0,Finset.mem_inter.mpr ⟨marks _ h0 b.val.start_marked,?_⟩⟩
        simp [markedArcEndset]
      · refine ⟨b.val.map 1,Finset.mem_inter.mpr ⟨marks _ h1 b.val.end_marked,?_⟩⟩
        simp [markedArcEndset]
    · rw [← label]
      intro z hz
      simp only [markedArcEndset,Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact endpoint _ ⟨0,rfl⟩ b.val.start_marked
      · exact endpoint _ ⟨1,rfl⟩ b.val.end_marked
  have labelUnique : ∀ w ∈ τ, ∀ z ∈ τ,
      classEndpoints M w = classEndpoints M z → w = z := by
    intro w hw z hz he
    by_contra hneW
    have hfresh := actualRestrictedLink_fresh_labels M p T τ hτ
    exact hfresh.2 w hw z (Finset.mem_union_right _ hz) (fun he => hneW he.symm)
      (hfresh.1 z hz) he.symm
  have pairCandidates (u0 u1 x y s t : S) (hst : s ≠ t)
      (h0 : s = u0 ∨ s = u1 ∨ s = x ∨ s = y)
      (h1 : t = u0 ∨ t = u1 ∨ t = x ∨ t = y)
      (hit : s = u0 ∨ s = u1 ∨ t = u0 ∨ t = u1) :
      ({s,t} : Finset S) ∈
        ({ {u0,u1}, {u0,x}, {u0,y}, {u1,x}, {u1,y} } : Finset (Finset S)) := by
    rcases hit with he | he | he | he
    · subst s
      rcases h1 with he | he | he | he <;> subst t <;> simp_all [Finset.pair_comm]
    · subst s
      rcases h1 with he | he | he | he <;> subst t <;> simp_all [Finset.pair_comm]
    · subst t
      rcases h0 with he | he | he | he <;> subst s <;> simp_all [Finset.pair_comm]
    · subst t
      rcases h0 with he | he | he | he <;> subst s <;> simp_all [Finset.pair_comm]
  have faceFive : ∃ (x y : S) (H : Finset {w // w ∈ τ}),
      H = Finset.univ.filter (fun w =>
        (arcInterior M (r ⟨w.val,Finset.mem_union_right _ w.property⟩) ∩ U).Nonempty) ∧
      x ∈ M.cover.branch ∧ y ∈ M.cover.branch ∧ x ∉ U ∧ y ∉ U ∧ H.card ≤ 5 ∧
      ∀ w ∈ H, classEndpoints M w.val ∈
        ({ {f q0,f q1}, {f q0,x}, {f q0,y}, {f q1,x}, {f q1,y} } : Finset (Finset S)) := by
    obtain ⟨wO,hwO,hboundary,hlabels⟩ := faceLabels
    let x := (rT ⟨wO,hwO⟩).val.map 0
    let y := (rT ⟨wO,hwO⟩).val.map 1
    have hF : classEndpoints M wO = {x,y} :=
      (congrArg (classEndpoints M) (hrT ⟨wO,hwO⟩)).symm.trans
        (markedArcEndset_eq_classEndpoints M (rT ⟨wO,hwO⟩)).symm
    let liftτ : {w // w ∈ τ} → {w // w ∈ T.val ∪ τ} :=
      fun w => ⟨w.val,Finset.mem_union_right _ w.property⟩
    let rτ : {w // w ∈ τ} → EssentialMarkedArc M := fun w => r (liftτ w)
    let H := Finset.univ.filter (fun w : {w // w ∈ τ} => (arcInterior M (rτ w) ∩ U).Nonempty)
    let L : {w // w ∈ τ} → Finset S := fun w => classEndpoints M w.val
    let P : Finset (Finset S) := {{f q0,f q1}, {f q0,x}, {f q0,y}, {f q1,x}, {f q1,y}}
    have members : ∀ w ∈ H, L w ∈ P := by
      intro w hw
      have hit : (arcInterior M (rτ w) ∩ U).Nonempty := (Finset.mem_filter.mp hw).2
      have hdb : ∀ z, Disjoint (arcInterior M (rτ w)) (arcInterior M (rT z)) := by
        intro z
        rw [← hrestrict z]
        apply hd
        intro he
        have hz : w.val = z.val := congrArg Subtype.val he
        exact Finset.disjoint_left.mp hτ.1 z.property (hz ▸ w.property)
      have hrw : Quotient.mk (essentialArcSetoid M) (rτ w) = w.val := hr (liftτ w)
      obtain ⟨hint,hsub⟩ := hlabels (rτ w) w.val w.property hrw hdb hit
      rw [hF] at hsub
      let s0 := (rτ w).val.map 0
      let s1 := (rτ w).val.map 1
      have hends : classEndpoints M w.val = {s0,s1} :=
        (congrArg (classEndpoints M) hrw).symm.trans
          (markedArcEndset_eq_classEndpoints M (rτ w)).symm
      have hn : s0 ≠ s1 := by
        have hc := (actualArcLabels M).nonloop_endpoint_card w.val
          ((actualRestrictedLink_fresh_labels M p T τ hτ).1 w.val w.property)
        change (classEndpoints M w.val).card = 2 at hc
        rw [hends] at hc
        intro he
        rw [he] at hc
        simp at hc
      have hs0 : s0 = f q0 ∨ s0 = f q1 ∨ s0 = x ∨ s0 = y := by
        have hm := hsub (by rw [hends]; simp : s0 ∈ classEndpoints M w.val)
        simpa only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,or_assoc] using hm
      have hs1 : s1 = f q0 ∨ s1 = f q1 ∨ s1 = x ∨ s1 = y := by
        have hm := hsub (by rw [hends]; simp : s1 ∈ classEndpoints M w.val)
        simpa only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,or_assoc] using hm
      have hhit : s0 = f q0 ∨ s0 = f q1 ∨ s1 = f q0 ∨ s1 = f q1 := by
        obtain ⟨z,hz⟩ := hint
        rcases Finset.mem_inter.mp hz with ⟨hzQ,hzEnd⟩
        rw [hends] at hzEnd
        simp only [Finset.mem_insert,Finset.mem_singleton] at hzQ hzEnd
        rcases hzQ with hq | hq
        · rcases hzEnd with he | he
          · exact Or.inl (he.symm.trans hq)
          · exact Or.inr (Or.inr (Or.inl (he.symm.trans hq)))
        · rcases hzEnd with he | he
          · exact Or.inr (Or.inl (he.symm.trans hq))
          · exact Or.inr (Or.inr (Or.inr (he.symm.trans hq)))
      change classEndpoints M w.val ∈ P
      rw [hends]
      exact pairCandidates (f q0) (f q1) x y s0 s1 hn hs0 hs1 hhit
    have inj : Set.InjOn L (H : Set {w // w ∈ τ}) := by
      intro w hw z hz he
      apply Subtype.ext
      exact labelUnique w.val w.property z.val z.property he
    have sub : H.image L ⊆ P := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      exact members w hw
    have hPcard : P.card ≤ 5 := by
      have h1 := Finset.card_insert_le ({f q0,f q1} : Finset S)
        ({ {f q0,x}, {f q0,y}, {f q1,x}, {f q1,y} } : Finset (Finset S))
      have h2 := Finset.card_insert_le ({f q0,x} : Finset S)
        ({ {f q0,y}, {f q1,x}, {f q1,y} } : Finset (Finset S))
      have h3 := Finset.card_insert_le ({f q0,y} : Finset S)
        ({ {f q1,x}, {f q1,y} } : Finset (Finset S))
      have h4 := Finset.card_insert_le ({f q1,x} : Finset S)
        ({ {f q1,y} } : Finset (Finset S))
      simp only [Finset.card_singleton] at h4
      dsimp only [P]
      omega
    have hHcard : H.card ≤ 5 := by
      calc
        H.card = (H.image L).card := (Finset.card_image_of_injOn inj).symm
        _ ≤ P.card := Finset.card_le_card sub
        _ ≤ 5 := hPcard
    have hxout : x ∉ U := by
      intro hxU
      exact hUG.2.2.1 hxU (Set.mem_iUnion.mpr
        ⟨⟨wO,hwO⟩,⟨0,rfl⟩⟩)
    have hyout : y ∉ U := by
      intro hyU
      exact hUG.2.2.1 hyU (Set.mem_iUnion.mpr
        ⟨⟨wO,hwO⟩,⟨1,rfl⟩⟩)
    exact ⟨x,y,H,rfl,(rT ⟨wO,hwO⟩).val.start_marked,
      (rT ⟨wO,hwO⟩).val.end_marked,hxout,hyout,hHcard,members⟩
  have contained (b : EssentialMarkedArc M)
      (hbEnds : markedArcEndset b.val = {f q0,f q1})
      (hdb : ∀ z, Disjoint (arcInterior M b) (arcInterior M (rT z))) :
      b.val.image ⊆ U := by
    letI : T2Space S := M.sphere.symm.t2Space
    letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
    have hopen : IsOpen U := by
      rw [hU]
      exact hf.isOpenMap _ (jordan_curve_theorem hC).isOpen_inside
    have h0 : b.val.map 0 ∈ U := by
      have h0 : b.val.map 0 ∈ markedArcEndset b.val := by simp [markedArcEndset]
      rw [hbEnds] at h0
      rcases Finset.mem_insert.mp h0 with he | he
      · exact he ▸ hq0U
      · exact (Finset.mem_singleton.mp he) ▸ hq1U
    have h1 : b.val.map 1 ∈ U := by
      have h1 : b.val.map 1 ∈ markedArcEndset b.val := by simp [markedArcEndset]
      rw [hbEnds] at h1
      rcases Finset.mem_insert.mp h1 with he | he
      · exact he ▸ hq0U
      · exact (Finset.mem_singleton.mp he) ▸ hq1U
    obtain ⟨W,hW,hi,hcl⟩ := actual_arc_face_localization M rT b hdb
    have heq : W = U := by
      by_contra hneq
      have hdis := complementComponents_disjoint hW hUG hneq
      have hsub : W ⊆ Uᶜ := fun z hz hzu => Set.disjoint_left.mp hdis hz hzu
      have hcsub : closure W ⊆ Uᶜ := closure_minimal hsub hopen.isClosed_compl
      exact hcsub (hcl ⟨0,rfl⟩) h0
    rw [heq] at hi
    rintro z ⟨t,rfl⟩
    by_cases hb : b.val.map t ∈ M.cover.branch
    · rcases b.val.marked_only_at_ends t hb with ht | ht
      · have he : t = (0 : Interval) := Subtype.ext (congrArg Subtype.val ht)
        simpa only [he] using h0
      · have he : t = (1 : Interval) := Subtype.ext (congrArg Subtype.val ht)
        simpa only [he] using h1
    · exact hi ⟨⟨t,rfl⟩,hb⟩
  have coordinates (b : EssentialMarkedArc M)
      (hbn : b.val.map 0 ≠ b.val.map 1) (himage : b.val.image ⊆ range f) :
      ∃ (B : Set Plane) (u v : Plane), IsArcBetween B u v ∧
        f '' B = b.val.image ∧ f u = b.val.map 0 ∧ f v = b.val.map 1 := by
    let n : NonLoopArc M := ⟨b.val,hbn⟩
    let e : Plane ≃ₜ range f := hf.isEmbedding.toHomeomorph
    let k : Interval → range f := fun t => ⟨b.val.map t,himage ⟨t,rfl⟩⟩
    let g : Interval → Plane := e.symm ∘ k
    have gc : Continuous g := e.symm.continuous.comp (b.val.continuous.subtype_mk _)
    have gi : Function.Injective g := by
      intro t u h
      apply n.injective
      exact congrArg Subtype.val (e.symm.injective h)
    let l : ℝ → Plane := fun t => g (projIcc 0 1 (by norm_num) t)
    have lc : Continuous l := gc.comp continuous_projIcc
    have harc : IsArcBetween (range g) (g 0) (g 1) := by
      refine ⟨l,lc.continuousOn,?_,?_,?_,?_⟩
      · intro t ht u hu h
        have he := gi h
        rw [projIcc_of_mem (by norm_num) ht,projIcc_of_mem (by norm_num) hu] at he
        exact congrArg Subtype.val he
      · ext z
        constructor
        · rintro ⟨t,ht,rfl⟩
          exact ⟨projIcc 0 1 (by norm_num) t,rfl⟩
        · rintro ⟨t,rfl⟩
          refine ⟨t.val,t.property,?_⟩
          dsimp [l]
          rw [projIcc_of_mem (by norm_num) t.property]
      · simp [l,projIcc_of_mem (by norm_num) (by norm_num : (0:ℝ) ∈ Icc 0 1)]
      · simp [l,projIcc_of_mem (by norm_num) (by norm_num : (1:ℝ) ∈ Icc 0 1)]
    have fg (t : Interval) : f (g t) = b.val.map t := by
      exact congrArg Subtype.val (e.apply_symm_apply (k t))
    refine ⟨range g,g 0,g 1,harc,?_,fg 0,fg 1⟩
    ext z
    constructor
    · rintro ⟨w,⟨t,rfl⟩,rfl⟩
      exact ⟨t,(fg t).symm⟩
    · rintro ⟨t,rfl⟩
      exact ⟨g t,⟨t,rfl⟩,fg t⟩
  have spokeCoordinates (b : EssentialMarkedArc M) (q : Plane) (s : S)
      (hq : q ∈ inside C) (hs : s ∉ U)
      (hbEnds : markedArcEndset b.val = {f q,s})
      (hbIn : arcInterior M b ⊆ U) (hbCl : b.val.image ⊆ closure U) :
      ∃ (B : Set Plane) (x : Plane), IsArcBetween B x q ∧ x ∈ C ∧
        b.val.image = f '' B ∧ B \ {x} ⊆ inside C ∧ f x = s := by
    letI : T2Space S := M.sphere.symm.t2Space
    have hqU : f q ∈ U := hU.symm ▸ mem_image_of_mem f hq
    have hqs : f q ≠ s := fun he => hs (he ▸ hqU)
    have hbn : b.val.map 0 ≠ b.val.map 1 := by
      intro he
      have hc := congrArg Finset.card hbEnds
      change ({b.val.map 0,b.val.map 1} : Finset S).card = ({f q,s} : Finset S).card at hc
      rw [he] at hc
      simp [hqs] at hc
    have hsep := jordan_curve_theorem hC
    have hk : IsCompact (closure (inside C)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hsep.isBounded_inside.closure
    have hcl : closure U ⊆ f '' closure (inside C) := by
      rw [hU]
      exact closure_minimal (image_mono subset_closure) (hk.image hf.continuous).isClosed
    have himage : b.val.image ⊆ range f := by
      intro z hz
      obtain ⟨t,ht,hzt⟩ := hcl (hbCl hz)
      exact ⟨t,hzt⟩
    obtain ⟨B,u,v,hB,hBi,hu,hv⟩ := coordinates b hbn himage
    have hpair : ({f u,f v} : Finset S) = {s,f q} := by
      rw [hu,hv]
      exact hbEnds.trans (Finset.pair_comm _ _)
    have hpairSet := congrArg (fun d : Finset S => (d : Set S)) hpair
    simp only [Finset.coe_insert,Finset.coe_singleton] at hpairSet
    have produce (x : Plane) (hArc : IsArcBetween B x q) (hx : f x = s) :
        x ∈ C ∧ B \ {x} ⊆ inside C := by
      have hxout : x ∉ inside C := by
        intro hin
        exact hs (hx ▸ (hU.symm ▸ mem_image_of_mem f hin))
      have hxcl : x ∈ closure (inside C) := by
        have hfx : f x ∈ b.val.image := hBi ▸ mem_image_of_mem f hArc.left_mem
        obtain ⟨t,ht,he⟩ := hcl (hbCl hfx)
        exact hf.injective he ▸ ht
      have hxC : x ∈ C := by
        rw [(IsRegionOf.inside C).closure_eq hsep] at hxcl
        exact hxcl.resolve_left hxout
      refine ⟨hxC,?_⟩
      intro z hz
      have hfz : f z ∈ b.val.image := hBi ▸ mem_image_of_mem f hz.1
      by_cases hb : f z ∈ M.cover.branch
      · have he : f z ∈ (markedArcEndset b.val : Set S) := by
          rw [← markedArc_image_inter_branch]
          exact ⟨hfz,hb⟩
        rw [hbEnds] at he
        rcases Finset.mem_insert.mp he with he | he
        · exact hf.injective he ▸ hq
        · exact False.elim (hz.2 (mem_singleton_iff.mpr
            (hf.injective ((Finset.mem_singleton.mp he).trans hx.symm))))
      · obtain ⟨t,ht,he⟩ := hU ▸ hbIn ⟨hfz,hb⟩
        exact hf.injective he ▸ ht
    rcases pair_eq_pair_iff.mp hpairSet with ⟨hx,hv'⟩ | ⟨hu',hx⟩
    · have hArc : IsArcBetween B u q := by simpa only [hf.injective hv'] using hB
      obtain ⟨huC,hBin⟩ := produce u hArc hx
      exact ⟨B,u,hArc,huC,hBi.symm,hBin,hx⟩
    · have hArc : IsArcBetween B v q := by simpa only [hf.injective hu'] using hB.reverse
      obtain ⟨hvC,hBin⟩ := produce v hArc hx
      exact ⟨B,v,hArc,hvC,hBi.symm,hBin,hx⟩
  have liftPair (P : Set Plane) (hP : IsArcBetween P q0 q1) (hPi : P ⊆ inside C) :
      ∃ b : EssentialMarkedArc M, b.val.map 0 = f q0 ∧ b.val.map 1 = f q1 ∧
        b.val.image = f '' P ∧ b.val.image ⊆ U := by
    obtain ⟨g,hg,hgi,hgP,hg0,hg1⟩ := hP
    let k : Interval → S := fun t => f (g t.val)
    have hk0 : k 0 = f q0 := by simp [k,hg0]
    have hk1 : k 1 = f q1 := by simp [k,hg1]
    have hki : Function.Injective k := by
      intro t u he
      exact Subtype.ext (hgi t.property u.property (hf.injective he))
    have hkin (t : Interval) : g t.val ∈ P := hgP ▸ mem_image_of_mem g t.property
    let b : MarkedArc M := {
      map := k
      continuous := hf.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hg)
      injective_except_loop_closure := fun t u he => Or.inl (hki he)
      start_marked := hk0 ▸ (ha0 ▸ a.val.start_marked)
      end_marked := hk1 ▸ (ha1 ▸ a.val.end_marked)
      marked_only_at_ends := by
        intro t ht
        rcases hmarks (g t.val) (hPi (hkin t)) ht with ht | ht
        · exact Or.inl (hki (by simp only [k,ht,hg0]))
        · exact Or.inr (hki (by simp only [k,ht,hg1])) }
    have hbe : IsEssentialMarkedArc M b := Or.inl (by
      change k 0 ≠ k 1
      rw [hk0,hk1]
      exact fun he => hne (hf.injective he))
    refine ⟨⟨b,hbe⟩,hk0,hk1,?_,?_⟩
    · ext z
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨g t.val,hkin t,rfl⟩
      · rintro ⟨t,ht,rfl⟩
        obtain ⟨u,hu,rfl⟩ := hgP.symm ▸ ht
        exact ⟨⟨u,hu⟩,rfl⟩
    · rintro z ⟨t,rfl⟩
      exact hU.symm ▸ mem_image_of_mem f (hPi (hkin t))
  have singleSpoke (b : EssentialMarkedArc M) (s : S) (hs : s ∉ U)
      (hbEnds : markedArcEndset b.val = {f q0,s} ∨ markedArcEndset b.val = {f q1,s})
      (hbIn : arcInterior M b ⊆ U) (hbCl : b.val.image ⊆ closure U) :
      ∃ c : EssentialMarkedArc M, markedArcEndset c.val = {f q0,f q1} ∧
        c.val.image ⊆ U ∧ Disjoint (arcInterior M c) (arcInterior M b) := by
    have produce (q t : Plane) (hq : q ∈ inside C) (ht : t ∈ inside C)
        (hqBranch : f q ∈ M.cover.branch) (htBranch : f t ∈ M.cover.branch)
        (hqt : q ≠ t) (hend : markedArcEndset b.val = {f q,s}) :
        ∃ P : Set Plane, IsArcBetween P q t ∧ P ⊆ inside C ∧
          ∀ z ∈ P, f z ∉ M.cover.branch → f z ∉ b.val.image := by
      obtain ⟨B,x,hB,hx,himage,hBin,hxs⟩ := spokeCoordinates b q s hq hs hend hbIn hbCl
      have htB : t ∉ B := by
        intro htB
        have hft : f t ∈ (markedArcEndset b.val : Set S) := by
          rw [← markedArc_image_inter_branch]
          exact ⟨himage.symm ▸ mem_image_of_mem f htB,htBranch⟩
        rw [hend] at hft
        rcases Finset.mem_insert.mp hft with he | he
        · exact hqt (hf.injective he).symm
        · exact hs ((Finset.mem_singleton.mp he) ▸ (hU.symm ▸ mem_image_of_mem f ht))
      obtain ⟨P,hP,hPin,hPB⟩ := tipJoin hC hB hx hq ht hqt hBin htB
      refine ⟨P,hP,hPin,?_⟩
      intro z hz hn hzb
      obtain ⟨w,hw,he⟩ := himage ▸ hzb
      have hzB : z ∈ B := hf.injective he ▸ hw
      have hzq : z = q := mem_singleton_iff.mp (hPB ▸ (show z ∈ P ∩ B from ⟨hz,hzB⟩))
      exact hn (hzq ▸ hqBranch)
    have finish (P : Set Plane) (hP : IsArcBetween P q0 q1) (hPin : P ⊆ inside C)
        (avoid : ∀ z ∈ P, f z ∉ M.cover.branch → f z ∉ b.val.image) :
        ∃ c : EssentialMarkedArc M, markedArcEndset c.val = {f q0,f q1} ∧
          c.val.image ⊆ U ∧ Disjoint (arcInterior M c) (arcInterior M b) := by
      obtain ⟨c,hc0,hc1,hcImage,hcU⟩ := liftPair P hP hPin
      refine ⟨c,?_,hcU,Set.disjoint_left.mpr ?_⟩
      · change ({c.val.map (0 : Interval),c.val.map (1 : Interval)} : Finset S) = _
        rw [hc0,hc1]
      · intro z hzc hzb
        obtain ⟨t,ht,rfl⟩ := hcImage ▸ hzc.1
        exact avoid t ht hzc.2 hzb.1
    rcases hbEnds with hend | hend
    · obtain ⟨P,hP,hPin,havoid⟩ := produce q0 q1 hq0 hq1
        (ha0 ▸ a.val.start_marked) (ha1 ▸ a.val.end_marked) hne hend
      exact finish P hP hPin havoid
    · obtain ⟨P,hP,hPin,havoid⟩ := produce q1 q0 hq1 hq0
        (ha1 ▸ a.val.end_marked) (ha0 ▸ a.val.start_marked) hne.symm hend
      exact finish P hP.reverse hPin havoid
  have coordinateIntersection (b c : EssentialMarkedArc M) (A B : Set Plane)
      (ha : b.val.image = f '' A) (hb : c.val.image = f '' B)
      (hdis : Disjoint (arcInterior M b) (arcInterior M c)) :
      A ∩ B = f ⁻¹' ((markedArcEndset b.val : Set S) ∩ (markedArcEndset c.val : Set S)) := by
    ext z
    constructor
    · rintro ⟨hzA,hzB⟩
      have hza : f z ∈ b.val.image := ha.symm ▸ mem_image_of_mem f hzA
      have hzb : f z ∈ c.val.image := hb.symm ▸ mem_image_of_mem f hzB
      have hzBranch : f z ∈ M.cover.branch := by
        by_contra hn
        exact Set.disjoint_left.mp hdis ⟨hza,hn⟩ ⟨hzb,hn⟩
      constructor
      · rw [← markedArc_image_inter_branch]
        exact ⟨hza,hzBranch⟩
      · rw [← markedArc_image_inter_branch]
        exact ⟨hzb,hzBranch⟩
    · rintro ⟨hza,hzb⟩
      rw [← markedArc_image_inter_branch] at hza hzb
      constructor
      · exact hf.injective.mem_set_image.mp (ha ▸ hza.1)
      · exact hf.injective.mem_set_image.mp (hb ▸ hzb.1)
  have fourActualSpokes (b00 b01 b10 b11 : EssentialMarkedArc M) (s t : S)
      (hst : s ≠ t) (hs : s ∉ U) (ht : t ∉ U)
      (h00 : markedArcEndset b00.val = {f q0,s})
      (h01 : markedArcEndset b01.val = {f q0,t})
      (h10 : markedArcEndset b10.val = {f q1,s})
      (h11 : markedArcEndset b11.val = {f q1,t})
      (hi00 : arcInterior M b00 ⊆ U) (hc00 : b00.val.image ⊆ closure U)
      (hi01 : arcInterior M b01 ⊆ U) (hc01 : b01.val.image ⊆ closure U)
      (hi10 : arcInterior M b10 ⊆ U) (hc10 : b10.val.image ⊆ closure U)
      (hi11 : arcInterior M b11 ⊆ U) (hc11 : b11.val.image ⊆ closure U)
      (hd00_01 : Disjoint (arcInterior M b00) (arcInterior M b01))
      (hd00_10 : Disjoint (arcInterior M b00) (arcInterior M b10))
      (hd00_11 : Disjoint (arcInterior M b00) (arcInterior M b11))
      (hd01_10 : Disjoint (arcInterior M b01) (arcInterior M b10))
      (hd01_11 : Disjoint (arcInterior M b01) (arcInterior M b11))
      (hd10_11 : Disjoint (arcInterior M b10) (arcInterior M b11)) :
      ∃ c : EssentialMarkedArc M, markedArcEndset c.val = {f q0,f q1} ∧
        c.val.image ⊆ U ∧ ∀ b : EssentialMarkedArc M,
          b = b00 ∨ b = b01 ∨ b = b10 ∨ b = b11 →
          Disjoint (arcInterior M c) (arcInterior M b) := by
    obtain ⟨A0,x,hA0,hx,him00,hin00,hfx⟩ := spokeCoordinates b00 q0 s hq0 hs h00 hi00 hc00
    obtain ⟨A1,y,hA1,hy,him01,hin01,hfy⟩ := spokeCoordinates b01 q0 t hq0 ht h01 hi01 hc01
    obtain ⟨B0,x',hB0,_,him10,hin10,hfx'⟩ := spokeCoordinates b10 q1 s hq1 hs h10 hi10 hc10
    obtain ⟨B1,y',hB1,_,him11,hin11,hfy'⟩ := spokeCoordinates b11 q1 t hq1 ht h11 hi11 hc11
    have hex : x' = x := hf.injective (hfx'.trans hfx.symm)
    have hey : y' = y := hf.injective (hfy'.trans hfy.symm)
    subst x'; subst y'
    have hq0U : f q0 ∈ U := hU.symm ▸ mem_image_of_mem f hq0
    have hq1U : f q1 ∈ U := hU.symm ▸ mem_image_of_mem f hq1
    have sameTip (b c : EssentialMarkedArc M) (A B : Set Plane) (q : Plane)
        (hb : b.val.image = f '' A) (hc : c.val.image = f '' B)
        (he0 : markedArcEndset b.val = {f q,s}) (he1 : markedArcEndset c.val = {f q,t})
        (hdis : Disjoint (arcInterior M b) (arcInterior M c)) : A ∩ B = {q} := by
      rw [coordinateIntersection b c A B hb hc hdis,he0,he1]
      ext z
      simp only [Set.mem_preimage,Finset.coe_insert,Finset.coe_singleton,
        Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff]
      constructor
      · rintro ⟨he0,he1⟩
        rcases he0 with he0 | he0
        · exact hf.injective he0
        · rcases he1 with he1 | he1
          · exact hf.injective he1
          · exact False.elim (hst (he0.symm.trans he1))
      · rintro rfl
        exact ⟨Or.inl rfl,Or.inl rfl⟩
    have meetA : A0 ∩ A1 = {q0} := sameTip b00 b01 A0 A1 q0 him00 him01 h00 h01 hd00_01
    have meetB : B0 ∩ B1 = {q1} := sameTip b10 b11 B0 B1 q1 him10 him11 h10 h11 hd10_11
    have crossTip (b c : EssentialMarkedArc M) (A B : Set Plane) (s₀ s₁ : S)
        (hb : b.val.image = f '' A) (hc : c.val.image = f '' B)
        (he0 : markedArcEndset b.val = {f q0,s₀}) (he1 : markedArcEndset c.val = {f q1,s₁})
        (h₀ : s₀ = s ∨ s₀ = t) (h₁ : s₁ = s ∨ s₁ = t)
        (hdis : Disjoint (arcInterior M b) (arcInterior M c)) :
        A ∩ B ⊆ {x,y} := by
      intro z hz
      have he := coordinateIntersection b c A B hb hc hdis ▸ hz
      rw [he0,he1] at he
      simp only [Set.mem_preimage,Finset.coe_insert,Finset.coe_singleton,
        Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff] at he
      rcases he with ⟨he0,he1⟩
      rcases he0 with he0 | he0
      · rcases he1 with he1 | he1
        · exact False.elim (hne (hf.injective (he0.symm.trans he1)))
        · have hfq : f q0 = s₁ := he0.symm.trans he1
          rcases h₁ with rfl | rfl
          · exact False.elim (hs (hfq ▸ hq0U))
          · exact False.elim (ht (hfq ▸ hq0U))
      · rcases h₀ with rfl | rfl
        · exact Or.inl (hf.injective (he0.trans hfx.symm))
        · exact Or.inr (hf.injective (he0.trans hfy.symm))
    have sides : (A0 ∪ A1) ∩ (B0 ∪ B1) = {x,y} := by
      apply Subset.antisymm
      · rintro z ⟨hzA,hzB⟩
        rcases hzA with hzA | hzA <;> rcases hzB with hzB | hzB
        · exact crossTip b00 b10 A0 B0 s s him00 him10 h00 h10 (Or.inl rfl) (Or.inl rfl) hd00_10 ⟨hzA,hzB⟩
        · exact crossTip b00 b11 A0 B1 s t him00 him11 h00 h11 (Or.inl rfl) (Or.inr rfl) hd00_11 ⟨hzA,hzB⟩
        · exact crossTip b01 b10 A1 B0 t s him01 him10 h01 h10 (Or.inr rfl) (Or.inl rfl) hd01_10 ⟨hzA,hzB⟩
        · exact crossTip b01 b11 A1 B1 t t him01 him11 h01 h11 (Or.inr rfl) (Or.inr rfl) hd01_11 ⟨hzA,hzB⟩
      · intro z hz
        rcases hz with rfl | hz
        · exact ⟨Or.inl hA0.left_mem,Or.inl hB0.left_mem⟩
        · have he : z = y := Set.mem_singleton_iff.mp hz
          subst z
          exact ⟨Or.inr hA1.left_mem,Or.inr hB1.left_mem⟩
    have closedSub : (A0 ∪ A1) ∪ (B0 ∪ B1) ⊆ inside C ∪ C := by
      have part (A : Set Plane) (u : Plane) (hu : u ∈ C)
          (hin : A \ {u} ⊆ inside C) : A ⊆ inside C ∪ C := by
        intro z hz
        by_cases he : z = u
        · exact Or.inr (he ▸ hu)
        · exact Or.inl (hin ⟨hz,he⟩)
      exact Set.union_subset (Set.union_subset (part A0 x hx hin00) (part A1 y hy hin01))
        (Set.union_subset (part B0 x hx hin10) (part B1 y hy hin11))
    obtain ⟨P,hP,hPin,havoid⟩ := fourStarJoin hC hA0 hA1.reverse hB0 hB1.reverse
      meetA meetB sides closedSub hq0 hq1 hne
    obtain ⟨c,hc0,hc1,hcImage,hcU⟩ := liftPair P hP hPin
    refine ⟨c,?_,hcU,?_⟩
    · change ({c.val.map (0 : Interval),c.val.map (1 : Interval)} : Finset S) = _
      rw [hc0,hc1]
    · intro b hb
      apply Set.disjoint_left.mpr
      intro z hzc hzb
      obtain ⟨v,hv,rfl⟩ := hcImage ▸ hzc.1
      have hvEnds : v ∉ ({q0,q1} : Set Plane) := by
        intro he
        rcases he with rfl | he
        · exact hzc.2 (ha0 ▸ a.val.start_marked)
        · exact hzc.2 ((Set.mem_singleton_iff.mp he) ▸ (ha1 ▸ a.val.end_marked))
      apply havoid ⟨hv,hvEnds⟩
      rcases hb with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (hf.injective.mem_set_image.mp (him00 ▸ hzb.1)))
      · exact Or.inl (Or.inr (hf.injective.mem_set_image.mp (him01 ▸ hzb.1)))
      · exact Or.inr (Or.inl (hf.injective.mem_set_image.mp (him10 ▸ hzb.1)))
      · exact Or.inr (Or.inr (hf.injective.mem_set_image.mp (him11 ▸ hzb.1)))
  have sideDisc {D X : Set Plane} {x y q : Plane}
      (hD : IsJordanCurve D) (hX : IsArcBetween X x y) (hx : x ∈ D) (hy : y ∈ D)
      (hXi : X \ {x,y} ⊆ inside D) (hq : q ∈ inside D) (hqX : q ∉ X) :
      ∃ J : Set Plane, IsJordanCurve J ∧ X ⊆ J ∧ J ⊆ D ∪ X ∧
        q ∈ inside J ∧ inside J ⊆ inside D := by
    obtain ⟨R₁,R₂,hcut⟩ := exists_isCutPair hD hx hy hX.ne
    have hclass := general_crosscut_arbitrary_of_endpoints hD hX hcut hXi
    have hqSide : q ∈ inside (R₁ ∪ X) ∪ inside (R₂ ∪ X) :=
      hclass.1 ▸ (show q ∈ inside D \ X from ⟨hq,hqX⟩)
    have produce (R : Set Plane) (hR : IsArcBetween R x y) (hRD : R ⊆ D)
        (hqJ : q ∈ inside (R ∪ X)) (hin : inside (R ∪ X) ⊆ inside D \ X) :
        ∃ J : Set Plane, IsJordanCurve J ∧ X ⊆ J ∧ J ⊆ D ∪ X ∧
          q ∈ inside J ∧ inside J ⊆ inside D := by
      have hJ : IsJordanCurve (R ∪ X) := by
        apply isJordanCurve_union hR hX
        intro z hzR hzX
        by_contra hn
        have hzEnds : z ∉ ({x,y} : Set Plane) := by simpa using hn
        exact inside_subset_compl (hXi ⟨hzX,hzEnds⟩) (hRD hzR)
      refine ⟨R ∪ X,hJ,Set.subset_union_right,?_,hqJ,fun z hz => (hin hz).1⟩
      exact Set.union_subset (fun z hz => Or.inl (hRD hz)) (fun z hz => Or.inr hz)
    rcases hqSide with hqSide | hqSide
    · apply produce R₁ hcut.fst hcut.fst_subset hqSide
      intro z hz
      exact hclass.1.symm ▸ (Or.inl hz)
    · apply produce R₂ hcut.snd hcut.snd_subset hqSide
      intro z hz
      exact hclass.1.symm ▸ (Or.inr hz)
  have twoFanJoin {D A0 A1 : Set Plane} {x y p q : Plane}
      (hD : IsJordanCurve D) (hA0 : IsArcBetween A0 x p) (hA1 : IsArcBetween A1 p y)
      (hx : x ∈ D) (hy : y ∈ D) (hp : p ∈ inside D) (hq : q ∈ inside D)
      (hmeet : A0 ∩ A1 = {p})
      (hA0i : A0 \ {x} ⊆ inside D) (hA1i : A1 \ {y} ⊆ inside D)
      (hqX : q ∉ A0 ∪ A1) :
      ∃ P : Set Plane, IsArcBetween P p q ∧ P ⊆ inside D ∧
        P \ {p} ⊆ (A0 ∪ A1)ᶜ := by
    have hX : IsArcBetween (A0 ∪ A1) x y := hA0.concatenate hA1 (by
      intro z hzA0 hzA1
      exact Set.mem_singleton_iff.mp (hmeet ▸ (show z ∈ A0 ∩ A1 from ⟨hzA0,hzA1⟩)))
    have hXi : (A0 ∪ A1) \ {x,y} ⊆ inside D := by
      intro z hz
      rcases hz.1 with hz0 | hz1
      · exact hA0i ⟨hz0,fun he => hz.2 (Or.inl (Set.mem_singleton_iff.mp he))⟩
      · exact hA1i ⟨hz1,fun he => hz.2 (Or.inr he)⟩
    obtain ⟨J,hJ,hXJ,_,hqJ,hin⟩ := sideDisc hD hX hx hy hXi hq hqX
    have hpJ : p ∈ J := hXJ (Or.inl hA0.right_mem)
    obtain ⟨P,hP,hPi⟩ := planar_boundary_radial_arc hJ hpJ hqJ
    refine ⟨P,hP,?_,?_⟩
    · intro z hz
      by_cases he : z = p
      · exact he ▸ hp
      · exact hin (hPi ⟨hz,he⟩)
    · intro z hz hzx
      exact inside_subset_compl (hPi hz) (hXJ hzx)
  have threeFanJoin {D A0 A1 B : Set Plane} {x y p q : Plane}
      (hD : IsJordanCurve D) (hA0 : IsArcBetween A0 x p) (hA1 : IsArcBetween A1 p y)
      (hB : IsArcBetween B x q) (hx : x ∈ D) (hy : y ∈ D)
      (hp : p ∈ inside D) (hq : q ∈ inside D) (hpq : p ≠ q)
      (hmeet : A0 ∩ A1 = {p})
      (hA0i : A0 \ {x} ⊆ inside D) (hA1i : A1 \ {y} ⊆ inside D)
      (hBi : B \ {x} ⊆ inside D) (hBX : B ∩ (A0 ∪ A1) = {x}) :
      ∃ P : Set Plane, IsArcBetween P p q ∧ P ⊆ inside D ∧
        P \ {p,q} ⊆ ((A0 ∪ A1) ∪ B)ᶜ := by
    have hX : IsArcBetween (A0 ∪ A1) x y := hA0.concatenate hA1 (by
      intro z hzA0 hzA1
      exact Set.mem_singleton_iff.mp (hmeet ▸ (show z ∈ A0 ∩ A1 from ⟨hzA0,hzA1⟩)))
    have hXi : (A0 ∪ A1) \ {x,y} ⊆ inside D := by
      intro z hz
      rcases hz.1 with hz0 | hz1
      · exact hA0i ⟨hz0,fun he => hz.2 (Or.inl (Set.mem_singleton_iff.mp he))⟩
      · exact hA1i ⟨hz1,fun he => hz.2 (Or.inr he)⟩
    have hqX : q ∉ A0 ∪ A1 := by
      intro hqx
      have hqx' : q = x := Set.mem_singleton_iff.mp (hBX ▸ (show q ∈ B ∩ (A0 ∪ A1) from ⟨hB.right_mem,hqx⟩))
      exact inside_subset_compl hq (hqx' ▸ hx)
    obtain ⟨J,hJ,hXJ,hJDX,hqJ,hin⟩ := sideDisc hD hX hx hy hXi hq hqX
    have hxJ : x ∈ J := hXJ hX.left_mem
    have hyJ : y ∈ J := hXJ hX.right_mem
    have hBxconn : IsPreconnected (B \ {x}) := by
      apply hB.isPreconnected_diff.subset_closure
      · intro z hz
        exact ⟨hz.1,fun he => hz.2 (Or.inl (Set.mem_singleton_iff.mp he))⟩
      · intro z hz
        by_cases he : z = q
        · exact he ▸ hB.right_mem_closure_diff
        · exact subset_closure ⟨hz.1,by
            simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
            exact not_or.mpr ⟨hz.2,he⟩⟩
    have hBinJ : B \ {x} ⊆ inside J := by
      apply hBxconn.subset_of_closure_inter_subset (jordan_curve_theorem hJ).isOpen_inside
      · refine ⟨q,⟨hB.right_mem,?_⟩,hqJ⟩
        exact fun he => hB.ne (Set.mem_singleton_iff.mp he).symm
      · intro z hz
        rw [(IsRegionOf.inside J).closure_eq (jordan_curve_theorem hJ)] at hz
        rcases hz.1 with hzI | hzJ
        · exact hzI
        · rcases hJDX hzJ with hzD | hzX
          · exact False.elim (inside_subset_compl (hBi hz.2) hzD)
          · have he : z = x := Set.mem_singleton_iff.mp (hBX ▸ (show z ∈ B ∩ (A0 ∪ A1) from ⟨hz.2.1,hzX⟩))
            exact False.elim (hz.2.2 (Set.mem_singleton_iff.mpr he))
    obtain ⟨R,hR,hBR,hRi⟩ := planar_half_arc_completion hJ hB hxJ hyJ
      (fun he => hX.ne he.symm) hBinJ
    have hBRarc : IsArcBetween (B ∪ R) x y := hB.concatenate hR (by
      intro z hzB hzR
      exact Set.mem_singleton_iff.mp (hBR ▸ (show z ∈ B ∩ R from ⟨hzB,hzR⟩)))
    have hSides : (A0 ∪ A1) ∩ (B ∪ R) = {x,y} := by
      apply Subset.antisymm
      · rintro z ⟨hzX,hzBR⟩
        rcases hzBR with hzB | hzR
        · exact Or.inl (Set.mem_singleton_iff.mp (hBX ▸ (show z ∈ B ∩ (A0 ∪ A1) from ⟨hzB,hzX⟩)))
        · by_cases he : z = y
          · exact Or.inr (Set.mem_singleton_iff.mpr he)
          · exact False.elim (inside_subset_compl (hRi ⟨hzR,he⟩) (hXJ hzX))
      · intro z hz
        rcases hz with rfl | he
        · exact ⟨hX.left_mem,Or.inl hB.left_mem⟩
        · have he' : z = y := Set.mem_singleton_iff.mp he
          subst z
          exact ⟨hX.right_mem,Or.inr hR.right_mem⟩
    have closedSub : (A0 ∪ A1) ∪ (B ∪ R) ⊆ inside D ∪ D := by
      have part (A : Set Plane) (u : Plane) (hu : u ∈ D)
          (hi : A \ {u} ⊆ inside D) : A ⊆ inside D ∪ D := by
        intro z hz
        by_cases he : z = u
        · exact Or.inr (he ▸ hu)
        · exact Or.inl (hi ⟨hz,he⟩)
      exact Set.union_subset (Set.union_subset (part A0 x hx hA0i) (part A1 y hy hA1i))
        (Set.union_subset (part B x hx hBi) (part R y hy (hRi.trans hin)))
    obtain ⟨P,hP,hPin,havoid⟩ := fourStarJoin hD hA0 hA1 hB hR hmeet hBR hSides
      closedSub hp hq hpq
    refine ⟨P,hP,hPin,?_⟩
    intro z hz hzg
    exact havoid hz (hzg.elim Or.inl (fun hb => Or.inr (Or.inl hb)))
  have actualFanCoordinates (b0 b1 : EssentialMarkedArc M) (p : Plane) (s t : S)
      (hp : p ∈ inside C) (hst : s ≠ t) (hs : s ∉ U) (ht : t ∉ U)
      (he0 : markedArcEndset b0.val = {f p,s}) (he1 : markedArcEndset b1.val = {f p,t})
      (hi0 : arcInterior M b0 ⊆ U) (hc0 : b0.val.image ⊆ closure U)
      (hi1 : arcInterior M b1 ⊆ U) (hc1 : b1.val.image ⊆ closure U)
      (hdis : Disjoint (arcInterior M b0) (arcInterior M b1)) :
      ∃ (A0 A1 : Set Plane) (x y : Plane),
        IsArcBetween A0 x p ∧ IsArcBetween A1 y p ∧ x ∈ C ∧ y ∈ C ∧
        b0.val.image = f '' A0 ∧ b1.val.image = f '' A1 ∧
        A0 \ {x} ⊆ inside C ∧ A1 \ {y} ⊆ inside C ∧ f x = s ∧ f y = t ∧
        A0 ∩ A1 = {p} := by
    obtain ⟨A0,x,hA0,hx,him0,hin0,hfx⟩ := spokeCoordinates b0 p s hp hs he0 hi0 hc0
    obtain ⟨A1,y,hA1,hy,him1,hin1,hfy⟩ := spokeCoordinates b1 p t hp ht he1 hi1 hc1
    refine ⟨A0,A1,x,y,hA0,hA1,hx,hy,him0,him1,hin0,hin1,hfx,hfy,?_⟩
    rw [coordinateIntersection b0 b1 A0 A1 him0 him1 hdis,he0,he1]
    ext z
    simp only [Set.mem_preimage,Finset.coe_insert,Finset.coe_singleton,
      Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz0,hz1⟩
      rcases hz0 with hz0 | hz0
      · exact hf.injective hz0
      · rcases hz1 with hz1 | hz1
        · exact hf.injective hz1
        · exact False.elim (hst (hz0.symm.trans hz1))
    · rintro rfl
      exact ⟨Or.inl rfl,Or.inl rfl⟩
  have markNotSpoke (b : EssentialMarkedArc M) (B : Set Plane) (p q : Plane) (s : S)
      (hb : b.val.image = f '' B) (hend : markedArcEndset b.val = {f p,s})
      (hq : q ∈ inside C) (hqB : f q ∈ M.cover.branch) (hpq : p ≠ q) (hs : s ∉ U) : q ∉ B := by
    intro hqIn
    have hqEnd : f q ∈ (markedArcEndset b.val : Set S) := by
      rw [← markedArc_image_inter_branch]
      exact ⟨hb.symm ▸ mem_image_of_mem f hqIn,hqB⟩
    rw [hend] at hqEnd
    rcases Finset.mem_insert.mp hqEnd with he | he
    · exact hpq (hf.injective he).symm
    · exact hs ((Finset.mem_singleton.mp he) ▸ (hU.symm ▸ mem_image_of_mem f hq))
  have actualTwoFan (b0 b1 : EssentialMarkedArc M) (s t : S)
      (hst : s ≠ t) (hs : s ∉ U) (ht : t ∉ U)
      (he0 : markedArcEndset b0.val = {f q0,s}) (he1 : markedArcEndset b1.val = {f q0,t})
      (hi0 : arcInterior M b0 ⊆ U) (hc0 : b0.val.image ⊆ closure U)
      (hi1 : arcInterior M b1 ⊆ U) (hc1 : b1.val.image ⊆ closure U)
      (hdis : Disjoint (arcInterior M b0) (arcInterior M b1)) :
      ∃ c : EssentialMarkedArc M, markedArcEndset c.val = {f q0,f q1} ∧
        c.val.image ⊆ U ∧ Disjoint (arcInterior M c) (arcInterior M b0) ∧
          Disjoint (arcInterior M c) (arcInterior M b1) := by
    obtain ⟨A0,A1,x,y,hA0,hA1,hx,hy,him0,him1,hin0,hin1,hfx,hfy,hmeet⟩ :=
      actualFanCoordinates b0 b1 q0 s t hq0 hst hs ht he0 he1 hi0 hc0 hi1 hc1 hdis
    have hq1B : f q1 ∈ M.cover.branch := ha1 ▸ a.val.end_marked
    have hqX : q1 ∉ A0 ∪ A1 := by
      intro hqX
      rcases hqX with hqX | hqX
      · exact markNotSpoke b0 A0 q0 q1 s him0 he0 hq1 hq1B hne hs hqX
      · exact markNotSpoke b1 A1 q0 q1 t him1 he1 hq1 hq1B hne ht hqX
    obtain ⟨P,hP,hPi,havoid⟩ := twoFanJoin hC hA0 hA1.reverse hx hy hq0 hq1 hmeet hin0 hin1 hqX
    obtain ⟨c,hc0,hc1,hcImage,hcU⟩ := liftPair P hP hPi
    have avoid (b : EssentialMarkedArc M) (B : Set Plane) (him : b.val.image = f '' B)
        (hsub : B ⊆ A0 ∪ A1) : Disjoint (arcInterior M c) (arcInterior M b) := by
      apply Set.disjoint_left.mpr
      intro z hzc hzb
      obtain ⟨v,hv,rfl⟩ := hcImage ▸ hzc.1
      have hv0 : v ∉ ({q0} : Set Plane) := by
        intro he
        exact hzc.2 ((Set.mem_singleton_iff.mp he) ▸ (ha0 ▸ a.val.start_marked))
      exact havoid ⟨hv,hv0⟩ (hsub (hf.injective.mem_set_image.mp (him ▸ hzb.1)))
    refine ⟨c,?_,hcU,avoid b0 A0 him0 Set.subset_union_left,avoid b1 A1 him1 Set.subset_union_right⟩
    change ({c.val.map (0 : Interval),c.val.map (1 : Interval)} : Finset S) = _
    rw [hc0,hc1]
  have actualThreeFan (b0 b1 b2 : EssentialMarkedArc M) (s t : S)
      (hst : s ≠ t) (hs : s ∉ U) (ht : t ∉ U)
      (he0 : markedArcEndset b0.val = {f q0,s}) (he1 : markedArcEndset b1.val = {f q0,t})
      (he2 : markedArcEndset b2.val = {f q1,s})
      (hi0 : arcInterior M b0 ⊆ U) (hc0 : b0.val.image ⊆ closure U)
      (hi1 : arcInterior M b1 ⊆ U) (hc1 : b1.val.image ⊆ closure U)
      (hi2 : arcInterior M b2 ⊆ U) (hc2 : b2.val.image ⊆ closure U)
      (hd01 : Disjoint (arcInterior M b0) (arcInterior M b1))
      (hd02 : Disjoint (arcInterior M b0) (arcInterior M b2))
      (hd12 : Disjoint (arcInterior M b1) (arcInterior M b2)) :
      ∃ c : EssentialMarkedArc M, markedArcEndset c.val = {f q0,f q1} ∧
        c.val.image ⊆ U ∧ Disjoint (arcInterior M c) (arcInterior M b0) ∧
          Disjoint (arcInterior M c) (arcInterior M b1) ∧
          Disjoint (arcInterior M c) (arcInterior M b2) := by
    obtain ⟨A0,A1,x,y,hA0,hA1,hx,hy,him0,him1,hin0,hin1,hfx,hfy,hmeet⟩ :=
      actualFanCoordinates b0 b1 q0 s t hq0 hst hs ht he0 he1 hi0 hc0 hi1 hc1 hd01
    obtain ⟨B,x',hB,_,him2,hin2,hfx'⟩ := spokeCoordinates b2 q1 s hq1 hs he2 hi2 hc2
    have hex : x' = x := hf.injective (hfx'.trans hfx.symm)
    subst x'
    have hq1U : f q1 ∈ U := hU.symm ▸ mem_image_of_mem f hq1
    have cross (b : EssentialMarkedArc M) (A : Set Plane) (u : S)
        (heA : markedArcEndset b.val = {f q0,u}) (himA : b.val.image = f '' A)
        (hu : u ∉ U) (hdA : Disjoint (arcInterior M b) (arcInterior M b2)) :
        B ∩ A ⊆ {x} := by
      intro z hz
      have he := coordinateIntersection b2 b B A him2 himA hdA.symm ▸ hz
      rw [he2,heA] at he
      simp only [Set.mem_preimage,Finset.coe_insert,Finset.coe_singleton,
        Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff] at he
      rcases he with ⟨heB,heA⟩
      rcases heB with heB | heB
      · rcases heA with heA | heA
        · exact False.elim (hne (hf.injective (heA.symm.trans heB)))
        · exact False.elim (hu ((heB.symm.trans heA) ▸ hq1U))
      · exact hf.injective (heB.trans hfx.symm)
    have hBX : B ∩ (A0 ∪ A1) = {x} := by
      apply Subset.antisymm
      · rintro z ⟨hzB,hzA⟩
        rcases hzA with hzA | hzA
        · exact cross b0 A0 s he0 him0 hs hd02 ⟨hzB,hzA⟩
        · exact cross b1 A1 t he1 him1 ht hd12 ⟨hzB,hzA⟩
      · rintro z rfl
        exact ⟨hB.left_mem,Or.inl hA0.left_mem⟩
    obtain ⟨P,hP,hPi,havoid⟩ := threeFanJoin hC hA0 hA1.reverse hB hx hy hq0 hq1 hne
      hmeet hin0 hin1 hin2 hBX
    obtain ⟨c,hc0,hc1,hcImage,hcU⟩ := liftPair P hP hPi
    have avoid (b : EssentialMarkedArc M) (A : Set Plane) (him : b.val.image = f '' A)
        (hsub : A ⊆ (A0 ∪ A1) ∪ B) : Disjoint (arcInterior M c) (arcInterior M b) := by
      apply Set.disjoint_left.mpr
      intro z hzc hzb
      obtain ⟨v,hv,rfl⟩ := hcImage ▸ hzc.1
      have hvEnds : v ∉ ({q0,q1} : Set Plane) := by
        intro he
        rcases he with rfl | he
        · exact hzc.2 (ha0 ▸ a.val.start_marked)
        · exact hzc.2 ((Set.mem_singleton_iff.mp he) ▸ (ha1 ▸ a.val.end_marked))
      exact havoid ⟨hv,hvEnds⟩ (hsub (hf.injective.mem_set_image.mp (him ▸ hzb.1)))
    refine ⟨c,?_,hcU,avoid b0 A0 him0 ?_,avoid b1 A1 him1 ?_,avoid b2 B him2 Set.subset_union_right⟩
    · change ({c.val.map (0 : Interval),c.val.map (1 : Interval)} : Finset S) = _
      rw [hc0,hc1]
    · exact Set.subset_union_of_subset_left Set.subset_union_left _
    · exact Set.subset_union_of_subset_left Set.subset_union_right _
  have actualThreeFanOther (b0 b1 b2 : EssentialMarkedArc M) (s t : S)
      (hst : s ≠ t) (hs : s ∉ U) (ht : t ∉ U)
      (he0 : markedArcEndset b0.val = {f q1,s}) (he1 : markedArcEndset b1.val = {f q1,t})
      (he2 : markedArcEndset b2.val = {f q0,s})
      (hi0 : arcInterior M b0 ⊆ U) (hc0 : b0.val.image ⊆ closure U)
      (hi1 : arcInterior M b1 ⊆ U) (hc1 : b1.val.image ⊆ closure U)
      (hi2 : arcInterior M b2 ⊆ U) (hc2 : b2.val.image ⊆ closure U)
      (hd01 : Disjoint (arcInterior M b0) (arcInterior M b1))
      (hd02 : Disjoint (arcInterior M b0) (arcInterior M b2))
      (hd12 : Disjoint (arcInterior M b1) (arcInterior M b2)) :
      ∃ c : EssentialMarkedArc M, markedArcEndset c.val = {f q1,f q0} ∧
        c.val.image ⊆ U ∧ Disjoint (arcInterior M c) (arcInterior M b0) ∧
          Disjoint (arcInterior M c) (arcInterior M b1) ∧
          Disjoint (arcInterior M c) (arcInterior M b2) := by
    obtain ⟨A0,A1,x,y,hA0,hA1,hx,hy,him0,him1,hin0,hin1,hfx,hfy,hmeet⟩ :=
      actualFanCoordinates b0 b1 q1 s t hq1 hst hs ht he0 he1 hi0 hc0 hi1 hc1 hd01
    obtain ⟨B,x',hB,_,him2,hin2,hfx'⟩ := spokeCoordinates b2 q0 s hq0 hs he2 hi2 hc2
    have hex : x' = x := hf.injective (hfx'.trans hfx.symm)
    subst x'
    have hq1U : f q0 ∈ U := hU.symm ▸ mem_image_of_mem f hq0
    have cross (b : EssentialMarkedArc M) (A : Set Plane) (u : S)
        (heA : markedArcEndset b.val = {f q1,u}) (himA : b.val.image = f '' A)
        (hu : u ∉ U) (hdA : Disjoint (arcInterior M b) (arcInterior M b2)) :
        B ∩ A ⊆ {x} := by
      intro z hz
      have he := coordinateIntersection b2 b B A him2 himA hdA.symm ▸ hz
      rw [he2,heA] at he
      simp only [Set.mem_preimage,Finset.coe_insert,Finset.coe_singleton,
        Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff] at he
      rcases he with ⟨heB,heA⟩
      rcases heB with heB | heB
      · rcases heA with heA | heA
        · exact False.elim ((hne.symm) (hf.injective (heA.symm.trans heB)))
        · exact False.elim (hu ((heB.symm.trans heA) ▸ hq1U))
      · exact hf.injective (heB.trans hfx.symm)
    have hBX : B ∩ (A0 ∪ A1) = {x} := by
      apply Subset.antisymm
      · rintro z ⟨hzB,hzA⟩
        rcases hzA with hzA | hzA
        · exact cross b0 A0 s he0 him0 hs hd02 ⟨hzB,hzA⟩
        · exact cross b1 A1 t he1 him1 ht hd12 ⟨hzB,hzA⟩
      · rintro z rfl
        exact ⟨hB.left_mem,Or.inl hA0.left_mem⟩
    obtain ⟨P,hP,hPi,havoid⟩ := threeFanJoin hC hA0 hA1.reverse hB hx hy hq1 hq0 (hne.symm)
      hmeet hin0 hin1 hin2 hBX
    obtain ⟨c,hc1,hc0,hcImage,hcU⟩ := liftPair P hP.reverse hPi
    have avoid (b : EssentialMarkedArc M) (A : Set Plane) (him : b.val.image = f '' A)
        (hsub : A ⊆ (A0 ∪ A1) ∪ B) : Disjoint (arcInterior M c) (arcInterior M b) := by
      apply Set.disjoint_left.mpr
      intro z hzc hzb
      obtain ⟨v,hv,rfl⟩ := hcImage ▸ hzc.1
      have hvEnds : v ∉ ({q1,q0} : Set Plane) := by
        intro he
        rcases he with rfl | he
        · exact hzc.2 (ha1 ▸ a.val.end_marked)
        · exact hzc.2 ((Set.mem_singleton_iff.mp he) ▸ (ha0 ▸ a.val.start_marked))
      exact havoid ⟨hv,hvEnds⟩ (hsub (hf.injective.mem_set_image.mp (him ▸ hzb.1)))
    refine ⟨c,?_,hcU,avoid b0 A0 him0 ?_,avoid b1 A1 him1 ?_,avoid b2 B him2 Set.subset_union_right⟩
    · change ({c.val.map (0 : Interval),c.val.map (1 : Interval)} : Finset S) = _
      rw [hc0,hc1]
      exact Finset.pair_comm _ _
    · exact Set.subset_union_of_subset_left Set.subset_union_left _
    · exact Set.subset_union_of_subset_left Set.subset_union_right _
  have actualTwoFanOther (b0 b1 : EssentialMarkedArc M) (s t : S)
      (hst : s ≠ t) (hs : s ∉ U) (ht : t ∉ U)
      (he0 : markedArcEndset b0.val = {f q1,s}) (he1 : markedArcEndset b1.val = {f q1,t})
      (hi0 : arcInterior M b0 ⊆ U) (hc0 : b0.val.image ⊆ closure U)
      (hi1 : arcInterior M b1 ⊆ U) (hc1 : b1.val.image ⊆ closure U)
      (hdis : Disjoint (arcInterior M b0) (arcInterior M b1)) :
      ∃ c : EssentialMarkedArc M, markedArcEndset c.val = {f q1,f q0} ∧
        c.val.image ⊆ U ∧ Disjoint (arcInterior M c) (arcInterior M b0) ∧
          Disjoint (arcInterior M c) (arcInterior M b1) := by
    obtain ⟨A0,A1,x,y,hA0,hA1,hx,hy,him0,him1,hin0,hin1,hfx,hfy,hmeet⟩ :=
      actualFanCoordinates b0 b1 q1 s t hq1 hst hs ht he0 he1 hi0 hc0 hi1 hc1 hdis
    have hq1B : f q0 ∈ M.cover.branch := ha0 ▸ a.val.start_marked
    have hqX : q0 ∉ A0 ∪ A1 := by
      intro hqX
      rcases hqX with hqX | hqX
      · exact markNotSpoke b0 A0 q1 q0 s him0 he0 hq0 hq1B (hne.symm) hs hqX
      · exact markNotSpoke b1 A1 q1 q0 t him1 he1 hq0 hq1B (hne.symm) ht hqX
    obtain ⟨P,hP,hPi,havoid⟩ := twoFanJoin hC hA0 hA1.reverse hx hy hq1 hq0 hmeet hin0 hin1 hqX
    obtain ⟨c,hc1,hc0,hcImage,hcU⟩ := liftPair P hP.reverse hPi
    have avoid (b : EssentialMarkedArc M) (B : Set Plane) (him : b.val.image = f '' B)
        (hsub : B ⊆ A0 ∪ A1) : Disjoint (arcInterior M c) (arcInterior M b) := by
      apply Set.disjoint_left.mpr
      intro z hzc hzb
      obtain ⟨v,hv,rfl⟩ := hcImage ▸ hzc.1
      have hv0 : v ∉ ({q1} : Set Plane) := by
        intro he
        exact hzc.2 ((Set.mem_singleton_iff.mp he) ▸ (ha1 ▸ a.val.end_marked))
      exact havoid ⟨hv,hv0⟩ (hsub (hf.injective.mem_set_image.mp (him ▸ hzb.1)))
    refine ⟨c,?_,hcU,avoid b0 A0 him0 Set.subset_union_left,avoid b1 A1 him1 Set.subset_union_right⟩
    change ({c.val.map (0 : Interval),c.val.map (1 : Interval)} : Finset S) = _
    rw [hc0,hc1]
    exact Finset.pair_comm _ _
  -- Obligation 1: arbitrary original arcs in this two-mark disc have one class.
  have twoMarkClass (b : EssentialMarkedArc M)
      (hbEnds : markedArcEndset b.val = {f q0,f q1}) (hbU : b.val.image ⊆ U) :
      Quotient.mk (essentialArcSetoid M) b = v := by
    letI : T2Space S := M.sphere.symm.t2Space
    letI : CompactSpace S := M.sphere.symm.compactSpace
    have form (b : EssentialMarkedArc M)
        (hbEnds : markedArcEndset b.val = {f q0,f q1}) (hbU : b.val.image ⊆ U) :
        ∃ B : Set Plane, IsArcBetween B q0 q1 ∧ b.val.image = f '' B ∧ B ⊆ inside C := by
      have hbn : b.val.map 0 ≠ b.val.map 1 := by
        intro he
        have hc := congrArg Finset.card hbEnds
        change ({b.val.map 0,b.val.map 1} : Finset S).card = ({f q0,f q1} : Finset S).card at hc
        rw [he] at hc
        simp [hfn] at hc
      have himage : b.val.image ⊆ range f := by
        intro z hz
        obtain ⟨t,ht,he⟩ := hU ▸ hbU hz
        exact ⟨t,he⟩
      obtain ⟨B,u,w,hB,himage,hu,hw⟩ := coordinates b hbn himage
      have hepair : ({f u,f w} : Finset S) = {f q0,f q1} := by rw [hu,hw]; exact hbEnds
      have heset := congrArg (fun d : Finset S => (d : Set S)) hepair
      simp only [Finset.coe_insert,Finset.coe_singleton] at heset
      have hArc : IsArcBetween B q0 q1 := by
        rcases Set.pair_eq_pair_iff.mp heset with ⟨he0,he1⟩ | ⟨he0,he1⟩
        · simpa only [hf.injective he0,hf.injective he1] using hB
        · simpa only [hf.injective he0,hf.injective he1] using hB.reverse
      refine ⟨B,hArc,himage.symm,?_⟩
      intro z hz
      have hfz : f z ∈ b.val.image := himage ▸ mem_image_of_mem f hz
      obtain ⟨t,ht,he⟩ := hU ▸ hbU hfz
      exact hf.injective he ▸ ht
    obtain ⟨A,hA,haImage,hAi⟩ := form b hbEnds hbU
    obtain ⟨B,hB,hbImage,hBi⟩ := form a ends haIn
    have planarInteriorPair {D A B : Set Plane} {p q : Plane}
        (hD : IsJordanCurve D) (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
        (hp : p ∈ inside D) (hq : q ∈ inside D)
        (hAi : A ⊆ inside D) (hBi : B ⊆ inside D) :
        ∃ H : CurveComplex.AmbientIsotopy Plane,
          H.finalMap '' A = B ∧
          (∀ t z, z ∉ inside D → H.map (t,z) = z) ∧
          (∀ t, H.map (t,p) = p) ∧ (∀ t, H.map (t,q) = q) := by
      as_aux_lemma =>
        classical
        have disc {C : Set Plane} (hC : IsJordanCurve C) : Nonempty (Plane ≃ₜ inside C) := by
          have straight {C : Set Plane} (hC : IsJordanCurve C) :
            ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
        
            classical
            have outsideComponent {C : Set Plane} (hC : IsJordanCurve C) :
                IsComplementComponent C (outside C) := by
              have hs := jordan_curve_theorem hC
              refine ⟨hs.isConnected_outside.nonempty, hs.isConnected_outside, outside_subset_compl, ?_⟩
              intro V hV hsub hVc
              apply Set.Subset.antisymm
              · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_outside
                · obtain ⟨x, hx⟩ := hs.isConnected_outside.nonempty
                  exact ⟨x, hsub hx, hx⟩
                · intro x hx
                  rw [(IsRegionOf.outside C).closure_eq hs] at hx
                  rcases hx.1 with hi | hc
                  · exact hi
                  · exact False.elim (hVc hx.2 hc)
              · exact hsub
            obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
            obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
            have him : F '' C = modelCurve := by
              ext x
              constructor
              · rintro ⟨y, hy, rfl⟩
                rw [hF ⟨y, hy⟩]
                exact (e ⟨y, hy⟩).property
              · intro hx
                let y := e.symm ⟨x, hx⟩
                refine ⟨y.val, y.property, ?_⟩
                rw [hF y]
                exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
            have hc := homeomorphism_complement_component F (jordan_inside_complement_component hC)
            rw [him] at hc
            have hi := jordan_inside_complement_component isJordanCurve_modelCurve
            have ho := outsideComponent isJordanCurve_modelCurve
            obtain ⟨x, hx⟩ := hc.1
            have hxin : x ∈ inside modelCurve ∪ outside modelCurve :=
              (inside_union_outside modelCurve).symm ▸ hc.2.2.1 hx
            have heinside : F '' inside C = inside modelCurve := by
              rcases hxin with hxI | hxO
              · by_contra hn
                exact Set.disjoint_left.mp (complementComponents_disjoint hc hi hn) hx hxI
              · have heoutside : F '' inside C = outside modelCurve := by
                  by_contra hn
                  exact Set.disjoint_left.mp (complementComponents_disjoint hc ho hn) hx hxO
                have hs := jordan_curve_theorem hC
                have hk : IsCompact (closure (inside C)) :=
                  Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
                have hb : Bornology.IsBounded (F '' inside C) :=
                  (hk.image F.continuous).isBounded.subset (image_mono subset_closure)
                exact False.elim ((jordan_curve_theorem isJordanCurve_modelCurve).not_isBounded_outside
                  (heoutside ▸ hb))
            exact ⟨F, him, heinside.trans inside_modelCurve⟩
          have square : Nonempty (Plane ≃ₜ Plane.openSquare 0 1) := by
        
            let H : Plane ≃ₜ (Fin 2 → ℝ) := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
            let B : (Fin 2 → ℝ) ≃ₜ Metric.ball (0 : Fin 2 → ℝ) 1 := Homeomorph.unitBall
            let K : Metric.ball (0 : Fin 2 → ℝ) 1 ≃ₜ Plane.openSquare 0 1 :=
              H.symm.subtype (fun x => by
                simp only [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
                change (∀ i : Fin 2, ‖x i‖ < 1) ↔ (H.symm x).supDist 0 < 1
                simp [Schoenflies.Plane.supDist, Schoenflies.Plane.supNorm, Fin.forall_fin_two, H, EuclideanSpace.equiv,
                  PiLp.toLp_apply, Real.norm_eq_abs])
            exact ⟨(H.trans B).trans K⟩
          obtain ⟨F, _, hFI⟩ := straight hC
          obtain ⟨H⟩ := square
          let R : inside C ≃ₜ Plane.openSquare 0 1 :=
            (F.isEmbedding.homeomorphImage (inside C)).trans (Homeomorph.setCongr hFI)
          exact ⟨H.trans R.symm⟩
        have straight {C : Set Plane} (hC : IsJordanCurve C) :
          ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
      
          classical
          have outsideComponent {C : Set Plane} (hC : IsJordanCurve C) :
              IsComplementComponent C (outside C) := by
            have hs := jordan_curve_theorem hC
            refine ⟨hs.isConnected_outside.nonempty, hs.isConnected_outside, outside_subset_compl, ?_⟩
            intro V hV hsub hVc
            apply Set.Subset.antisymm
            · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_outside
              · obtain ⟨x, hx⟩ := hs.isConnected_outside.nonempty
                exact ⟨x, hsub hx, hx⟩
              · intro x hx
                rw [(IsRegionOf.outside C).closure_eq hs] at hx
                rcases hx.1 with hi | hc
                · exact hi
                · exact False.elim (hVc hx.2 hc)
            · exact hsub
          obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
          obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
          have him : F '' C = modelCurve := by
            ext x
            constructor
            · rintro ⟨y, hy, rfl⟩
              rw [hF ⟨y, hy⟩]
              exact (e ⟨y, hy⟩).property
            · intro hx
              let y := e.symm ⟨x, hx⟩
              refine ⟨y.val, y.property, ?_⟩
              rw [hF y]
              exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
          have hc := homeomorphism_complement_component F (jordan_inside_complement_component hC)
          rw [him] at hc
          have hi := jordan_inside_complement_component isJordanCurve_modelCurve
          have ho := outsideComponent isJordanCurve_modelCurve
          obtain ⟨x, hx⟩ := hc.1
          have hxin : x ∈ inside modelCurve ∪ outside modelCurve :=
            (inside_union_outside modelCurve).symm ▸ hc.2.2.1 hx
          have heinside : F '' inside C = inside modelCurve := by
            rcases hxin with hxI | hxO
            · by_contra hn
              exact Set.disjoint_left.mp (complementComponents_disjoint hc hi hn) hx hxI
            · have heoutside : F '' inside C = outside modelCurve := by
                by_contra hn
                exact Set.disjoint_left.mp (complementComponents_disjoint hc ho hn) hx hxO
              have hs := jordan_curve_theorem hC
              have hk : IsCompact (closure (inside C)) :=
                Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
              have hb : Bornology.IsBounded (F '' inside C) :=
                (hk.image F.continuous).isBounded.subset (image_mono subset_closure)
              exact False.elim ((jordan_curve_theorem isJordanCurve_modelCurve).not_isBounded_outside
                (heoutside ▸ hb))
          exact ⟨F, him, heinside.trans inside_modelCurve⟩
        have conjugate {X Y : Type}
            [TopologicalSpace X] [TopologicalSpace Y]
            (e : X ≃ₜ Y) (H : AmbientIsotopy Y) :
            ∃ K : AmbientIsotopy X,
              ∀ t x, K.map (t, x) = e.symm (H.map (t, e x)) := by
          refine ⟨{ map := ⟨fun z => e.symm (H.map (z.1, e z.2)),
              e.symm.continuous.comp (H.map.continuous.comp
                (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩,
                    homeomorphism_at := ?_, at_zero := ?_ }, fun t x => rfl⟩
          · intro t
            obtain ⟨h, hh⟩ := H.homeomorphism_at t
            exact ⟨(e.trans h).trans e.symm, fun x => congrArg e.symm (hh (e x))⟩
          · intro x
            change e.symm (H.map (⟨0, by norm_num⟩, e x)) = x
            rw [H.at_zero, e.symm_apply_apply]

        have extend {S : Type} [TopologicalSpace S]
            (U K : Set S) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
            (H : AmbientIsotopy U)
            (hfix : ∀ t (x : U), x.val ∉ K → (H.map (t, x) : S) = x.val) :
            ∃ G : AmbientIsotopy S,
              (∀ t (x : U), G.map (t, x.val) = (H.map (t, x) : S)) ∧
              (∀ t x, x ∉ K → G.map (t, x) = x) := by
          classical
          let F : Interval × S → S := fun z =>
            if hx : z.2 ∈ U then (H.map (z.1, ⟨z.2, hx⟩) : S) else z.2
          have hFU (t : Interval) (x : U) : F (t, x.val) = (H.map (t, x) : S) := by
            simp only [F, dif_pos x.property]
          have hFK (t : Interval) (x : S) (hx : x ∉ K) : F (t, x) = x := by
            dsimp [F]
            split_ifs with h
            · exact hfix t ⟨x, h⟩ hx
            · rfl
          have hcontU : ContinuousOn F {z | z.2 ∈ U} := by
            apply continuousOn_iff_continuous_domRestrict.mpr
            have hh : Continuous (fun z : {z : Interval × S | z.2 ∈ U} =>
                (H.map (z.val.1, ⟨z.val.2, z.property⟩) : S)) :=
              continuous_subtype_val.comp (H.map.continuous.comp
                ((continuous_fst.comp continuous_subtype_val).prodMk
                  ((continuous_snd.comp continuous_subtype_val).subtype_mk _)))
            have hsame : ({z : Interval × S | z.2 ∈ U}.domRestrict F) =
                (fun z : {z : Interval × S | z.2 ∈ U} =>
                  (H.map (z.val.1, ⟨z.val.2, z.property⟩) : S)) := by
              funext z
              exact hFU z.val.1 ⟨z.val.2, z.property⟩
            rw [hsame]
            exact hh
          have hcontK : ContinuousOn F {z | z.2 ∉ K} := by
            apply continuous_snd.continuousOn.congr
            intro z hz
            exact hFK z.1 z.2 hz
          have hcont : Continuous F := by
            rw [continuous_iff_continuousAt]
            intro z
            by_cases hz : z.2 ∈ U
            · exact hcontU.continuousAt ((hU.preimage continuous_snd).mem_nhds hz)
            · exact hcontK.continuousAt
                ((hK.isOpen_compl.preimage continuous_snd).mem_nhds (fun hk => hz (hKU hk)))
          have hmem (t : Interval) (x : S) : F (t, x) ∈ U ↔ x ∈ U := by
            by_cases hx : x ∈ U
            · rw [hFU t ⟨x, hx⟩]
              exact iff_of_true (H.map (t, ⟨x, hx⟩)).property hx
            · simp only [F, dif_neg hx, hx]
          refine ⟨{ map := ⟨F, hcont⟩, homeomorphism_at := ?_, at_zero := ?_ }, hFU, hFK⟩
          · intro t
            obtain ⟨e, he⟩ := H.homeomorphism_at t
            let inv : S → S := fun y => if hy : y ∈ U then (e.symm ⟨y,hy⟩ : S) else y
            have hiU (x : U) : inv x.val = (e.symm x : S) := by simp [inv,x.property]
            have hefix (x : U) (hx : x.val ∉ K) : e x = x := by
              apply Subtype.ext
              rw [he]
              exact hfix t x hx
            have hiK (x : S) (hx : x ∉ K) : inv x = x := by
              by_cases hu : x ∈ U
              · rw [hiU ⟨x,hu⟩]
                have hef := hefix ⟨x,hu⟩ hx
                have hh := congrArg e.symm hef
                rw [e.symm_apply_apply] at hh
                exact congrArg Subtype.val hh.symm
              · simp [inv,hu]
            have hicU : ContinuousOn inv U := by
              rw [continuousOn_iff_continuous_domRestrict]
              exact (continuous_subtype_val.comp e.symm.continuous).congr (fun x => (hiU x).symm)
            have hicK : ContinuousOn inv Kᶜ :=
              continuous_id.continuousOn.congr (fun x hx => hiK x hx)
            have hic : Continuous inv := by
              rw [continuous_iff_continuousAt]
              intro x
              by_cases hx : x ∈ U
              · exact hicU.continuousAt (hU.mem_nhds hx)
              · exact hicK.continuousAt (hK.isOpen_compl.mem_nhds (fun hk => hx (hKU hk)))
            refine ⟨{ toFun := fun x => F (t,x)
                      invFun := inv
                      left_inv := ?_
                      right_inv := ?_
                      continuous_toFun := hcont.comp (continuous_const.prodMk continuous_id)
                      continuous_invFun := hic }, fun _ => rfl⟩
            · intro x
              change inv (F (t,x)) = x
              by_cases hx : x ∈ U
              · rw [hFU t ⟨x,hx⟩]
                have hm := (H.map (t,⟨x,hx⟩)).property
                change inv (H.map (t,⟨x,hx⟩)).val = x
                rw [hiU]
                have hh : H.map (t,⟨x,hx⟩) = e ⟨x,hx⟩ := (he ⟨x,hx⟩).symm
                rw [hh,e.symm_apply_apply]
              · have hf : F (t,x) = x := by simp [F,hx]
                rw [hf]
                simp [inv,hx]
            · intro y
              change F (t,inv y) = y
              by_cases hy : y ∈ U
              · rw [hiU ⟨y,hy⟩,hFU]
                rw [← he,e.apply_symm_apply]
              · have hi : inv y = y := by simp [inv,hy]
                rw [hi]
                simp [F,hy]
          · intro x
            dsimp [F]
            split_ifs with hx
            · exact congrArg Subtype.val (H.at_zero ⟨x, hx⟩)
            · rfl

        have onePoint {A B : Set Plane} {p q : Plane}
            (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
            (hAi : A ⊆ Plane.openSquare 0 1) (hBi : B ⊆ Plane.openSquare 0 1) :
            ∃ H : AmbientIsotopy Plane, H.finalMap '' A = B ∧
              (∀ t z, z ∉ Plane.openSquare 0 1 → H.map (t,z) = z) ∧
              (∀ t, H.map (t,p) = p) ∧ H.finalMap q = q := by
          classical
          have properIso {A B : Set Plane} {x p y : Plane}
              (hA : IsArcBetween A x p) (hB : IsArcBetween B x p)
              (hx : x ∈ modelCurve) (hy : y ∈ modelCurve) (hyx : y ≠ x)
              (hp : p ∈ Plane.openSquare 0 1)
              (hAi : A \ {x} ⊆ Plane.openSquare 0 1)
              (hBi : B \ {x} ⊆ Plane.openSquare 0 1)
              (h : ArcHomeo A B x p x p) :
              ∃ H : AmbientIsotopy Plane,
                EqOn H.finalMap h.toFun A ∧
                (∀ t z, z ∉ Plane.openSquare 0 1 → H.map (t,z) = z) ∧
                (∀ t, H.map (t,p) = p) := by
            classical
            have completion {C A : Set Plane} {x q y : Plane} (hC : IsJordanCurve C)
                (hA : IsArcBetween A x q) (hx : x ∈ C) (hy : y ∈ C) (hyx : y ≠ x)
                (hinA : A \ {x} ⊆ inside C) :
                ∃ B : Set Plane, IsArcBetween B q y ∧ A ∩ B = {q} ∧ B \ {y} ⊆ inside C := by
              classical
              have slit {C A : Set Plane} {x q : Plane} (hC : IsJordanCurve C)
                  (hA : IsArcBetween A x q) (hx : x ∈ C) (hinA : A \ {x} ⊆ inside C) :
                  IsConnected (inside C \ A) := by
                classical
                have slit {S : Type} [TopologicalSpace S] [T2Space S]
                    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
                    (a : Interval → S) (ha : Continuous a) (hai : Function.Injective a)
                    (h0 : a 0 ∉ range f) (hin : ∀ t : Interval, t ≠ 0 → a t ∈ range f)
                    (x : Plane) (hx : f x ∉ range a) :
                    IsConnected (range f \ range a) := by
                  classical
                  have collapse {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
                      (f : X → Y) (hf : Topology.IsOpenEmbedding f) :
                      ∃ g : Y → OnePoint X, Continuous g ∧
                        (∀ x, g (f x) = (x : OnePoint X)) ∧
                        (∀ y, y ∉ range f → g y = OnePoint.infty) := by
                    classical
                    let H := hf.isEmbedding.toHomeomorph
                    let g : Y → OnePoint X := fun y => if h : y ∈ range f then
                      ((H.symm ⟨y,h⟩ : X) : OnePoint X) else OnePoint.infty
                    have hg (x : X) : g (f x) = (x : OnePoint X) := by
                      simp [g,H]
                    have hout (y : Y) (hy : y ∉ range f) : g y = OnePoint.infty := by
                      dsimp only [g]
                      rw [dif_neg hy]
                    refine ⟨g,?_,hg,hout⟩
                    apply continuous_def.mpr
                    intro A hA
                    by_cases hInf : OnePoint.infty ∈ A
                    · let K : Set X := ((↑) : X → OnePoint X) ⁻¹' Aᶜ
                      have hK : IsClosed K ∧ IsCompact K := by
                        exact (OnePoint.isOpen_iff_of_mem hInf).mp hA
                      have he : g ⁻¹' A = (f '' K)ᶜ := by
                        ext y
                        by_cases hy : y ∈ range f
                        · obtain ⟨x,rfl⟩ := hy
                          rw [mem_preimage,hg,mem_compl_iff,hf.injective.mem_set_image]
                          simp [K]
                        · rw [mem_preimage,hout y hy]
                          constructor
                          · intro _ hmem; exact hy (image_subset_range f K hmem)
                          · intro _; exact hInf
                      rw [he]
                      exact (hK.2.image hf.continuous).isClosed.isOpen_compl
                    · have ho : IsOpen (((↑) : X → OnePoint X) ⁻¹' A) :=
                        (OnePoint.isOpen_iff_of_notMem hInf).mp hA
                      have he : g ⁻¹' A = f '' (((↑) : X → OnePoint X) ⁻¹' A) := by
                        ext y
                        by_cases hy : y ∈ range f
                        · obtain ⟨x,rfl⟩ := hy
                          rw [mem_preimage,hg,hf.injective.mem_set_image]
                          rfl
                        · rw [mem_preimage,hout y hy]
                          constructor
                          · exact fun h => False.elim (hInf h)
                          · exact fun h => False.elim (hy (image_subset_range f _ h))
                      rw [he]
                      exact hf.isOpenMap _ ho
                  have complement {S : Type} [TopologicalSpace S] (esphere : S ≃ₜ CurveComplex.SpherePort.Sphere)
                      (α : Interval → S) (hc : Continuous α) (hi : Function.Injective α)
                      (p : S) (hp : p ∉ (Set.range α)) : IsConnected ((Set.range α))ᶜ := by
                    classical
                    letI : T2Space S := esphere.symm.t2Space
                    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
                    let e : OpenPartialHomeomorph S Schoenflies.Plane :=
                      esphere.toOpenPartialHomeomorph.trans (stereographic' 2 (esphere p))
                    have hsource : e.source = {p}ᶜ := by
                      ext x
                      simp [e, OpenPartialHomeomorph.trans_source]
                    have htarget : e.target = Set.univ := by
                      simp [e, OpenPartialHomeomorph.trans_target]
                    have hain : ∀ t : Interval, α t ∈ e.source := by
                      intro t
                      rw [hsource]
                      intro ht
                      apply hp
                      exact Set.mem_singleton_iff.mp ht ▸ (show α t ∈ (Set.range α) from ⟨t, rfl⟩)
                    let g : Interval → Schoenflies.Plane := e ∘ α
                    have hg : Continuous g :=
                      e.continuousOn.comp_continuous hc hain
                    have hgi : Function.Injective g := by
                      intro t u h
                      have heq := e.injOn (hain t) (hain u) h
                      exact hi heq
                    let f : ℝ → Schoenflies.Plane := g ∘ Set.projIcc 0 1 zero_le_one
                    have hf : Continuous f := hg.comp continuous_projIcc
                    have hfi : Set.InjOn f (Set.Icc 0 1) := by
                      intro t ht u hu h
                      have h := hgi h
                      simpa [f, Set.projIcc_of_mem, ht, hu] using congrArg Subtype.val h
                    have hA : Schoenflies.IsArc (Set.range g) := by
                      refine ⟨f, hf.continuousOn, hfi, ?_⟩
                      ext y
                      constructor
                      · rintro ⟨t, ht, rfl⟩
                        exact ⟨_, rfl⟩
                      · rintro ⟨t, rfl⟩
                        refine ⟨t, t.property, ?_⟩
                        simp [f, Set.projIcc_of_mem]
                    have hconn := Schoenflies.arc_complement hA
                    have hsymm : Continuous e.symm := by
                      exact continuousOn_univ.mp (htarget ▸ e.continuousOn_symm)
                    have himage : e.symm '' (Set.range g)ᶜ = (Set.range α)ᶜ ∩ {p}ᶜ := by
                      ext x
                      constructor
                      · rintro ⟨y, hy, rfl⟩
                        have hys : e.symm y ∈ e.source := e.map_target (htarget ▸ Set.mem_univ y)
                        refine ⟨?_, hsource ▸ hys⟩
                        rintro ⟨t, ht⟩
                        apply hy
                        refine ⟨t, ?_⟩
                        change e (α t) = y
                        rw [ht]
                        exact e.right_inv (htarget ▸ Set.mem_univ y)
                      · rintro ⟨hx, hxp⟩
                        have hxs : x ∈ e.source := hsource.symm ▸ hxp
                        refine ⟨e x, ?_, e.left_inv hxs⟩
                        rintro ⟨t, ht⟩
                        exact hx ⟨t, e.injOn (hain t) hxs ht⟩
                    have hpunct : IsConnected ((Set.range α)ᶜ ∩ {p}ᶜ) := by
                      rw [← himage]
                      exact hconn.image e.symm hsymm.continuousOn
                    have hsphere : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
                      apply isConnected_sphere _ _ (by norm_num)
                      rw [← Module.finrank_eq_rank]
                      norm_num
                    letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
                      isConnected_iff_connectedSpace.mp hsphere
                    letI : ConnectedSpace S := connectedSpace_iff_univ.mpr (by
                      have hi := isConnected_univ.image esphere.symm esphere.symm.continuous.continuousOn
                      simpa only [Set.image_univ, esphere.symm.surjective.range_eq] using hi)
                    have hdense : Dense ({p}ᶜ : Set S) := by
                      apply dense_compl_singleton_iff_not_open.mpr
                      intro hopen
                      have hsingle : ({p} : Set S) = Set.univ :=
                        (show IsClopen ({p} : Set S) from ⟨isClosed_singleton, hopen⟩).eq_univ ⟨p, rfl⟩
                      have hends : α ⟨0, by norm_num⟩ = p := by
                        exact Set.mem_singleton_iff.mp (hsingle.symm ▸ Set.mem_univ _)
                      exact hp ⟨_, hends⟩
                    have hclosed : IsClosed (Set.range α) := by
                      exact (isCompact_range hc).isClosed
                    have hcl : (Set.range α)ᶜ ⊆ closure ((Set.range α)ᶜ ∩ {p}ᶜ) := by
                      simpa only [Set.inter_comm] using hdense.open_subset_closure_inter hclosed.isOpen_compl
                    exact hpunct.subset_closure Set.inter_subset_left hcl
                
                
                  obtain ⟨g,hgc,hg,hout⟩ := collapse f hf
                  let b : Interval → OnePoint Plane := g ∘ a
                  have hb0 : b 0 = OnePoint.infty := hout _ h0
                  have hbpos (t : Interval) (ht : t ≠ 0) : ∃ y : Plane, a t = f y ∧ b t = (y : OnePoint Plane) := by
                    obtain ⟨y,hy⟩ := hin t ht
                    exact ⟨y,hy.symm,by change g (a t) = _; rw [← hy,hg]⟩
                  have hbi : Function.Injective b := by
                    intro t u he
                    by_cases ht : t = 0
                    · by_cases hu : u = 0
                      · exact ht.trans hu.symm
                      · obtain ⟨y,hy,hby⟩ := hbpos u hu
                        rw [ht,hb0,hby] at he
                        exact False.elim (OnePoint.infty_ne_coe y he)
                    · by_cases hu : u = 0
                      · obtain ⟨y,hy,hby⟩ := hbpos t ht
                        rw [hu,hb0,hby] at he
                        exact False.elim (OnePoint.coe_ne_infty y he)
                      · obtain ⟨y,hy,hby⟩ := hbpos t ht
                        obtain ⟨z,hz,hbz⟩ := hbpos u hu
                        rw [hby,hbz] at he
                        have hyz := OnePoint.coe_injective he
                        apply hai
                        rw [hy,hz,hyz]
                  have hxb : (x : OnePoint Plane) ∉ range b := by
                    rintro ⟨t,ht⟩
                    by_cases ht0 : t = 0
                    · rw [ht0,hb0] at ht
                      exact OnePoint.infty_ne_coe x ht
                    · obtain ⟨y,hy,hby⟩ := hbpos t ht0
                      rw [hby] at ht
                      have hyx := OnePoint.coe_injective ht
                      exact hx ⟨t,hy.trans (congrArg f hyx)⟩
                  let H : OnePoint Plane ≃ₜ CurveComplex.SpherePort.Sphere :=
                    onePointEquivSphereOfFinrankEq (by simp)
                  have hc := complement H b (hgc.comp ha) hbi (x : OnePoint Plane) hxb
                  let K : Set Plane := {y | (y : OnePoint Plane) ∉ range b}
                  have hKimage : ((↑) : Plane → OnePoint Plane) '' K = (range b)ᶜ := by
                    ext y
                    constructor
                    · rintro ⟨z,hz,rfl⟩
                      exact hz
                    · intro hy
                      cases y using OnePoint.rec with
                      | infty => exact False.elim (hy ⟨0,hb0⟩)
                      | coe z => exact ⟨z,hy,rfl⟩
                  have hcK : IsConnected K := by
                    rw [← hKimage] at hc
                    exact ⟨Set.image_nonempty.mp hc.nonempty,
                      OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp hc.isPreconnected⟩
                  have htarget : f '' K = range f \ range a := by
                    ext y
                    constructor
                    · rintro ⟨z,hz,rfl⟩
                      refine ⟨⟨z,rfl⟩,?_⟩
                      rintro ⟨t,ht⟩
                      apply hz
                      refine ⟨t,?_⟩
                      change g (a t) = (z : OnePoint Plane)
                      rw [ht,hg]
                    · rintro ⟨⟨z,rfl⟩,hn⟩
                      refine ⟨z,?_,rfl⟩
                      rintro ⟨t,ht⟩
                      by_cases ht0 : t = 0
                      · rw [ht0,hb0] at ht
                        exact OnePoint.infty_ne_coe z ht
                      · obtain ⟨u,hu,hbu⟩ := hbpos t ht0
                        rw [hbu] at ht
                        exact hn ⟨t,hu.trans (congrArg f (OnePoint.coe_injective ht))⟩
                  rw [← htarget]
                  exact hcK.image f hf.continuous.continuousOn
                have disc {C : Set Plane} (hC : IsJordanCurve C) : Nonempty (Plane ≃ₜ inside C) := by
                  have straight {C : Set Plane} (hC : IsJordanCurve C) :
                    ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
                
                    classical
                    have outsideComponent {C : Set Plane} (hC : IsJordanCurve C) :
                        IsComplementComponent C (outside C) := by
                      have hs := jordan_curve_theorem hC
                      refine ⟨hs.isConnected_outside.nonempty, hs.isConnected_outside, outside_subset_compl, ?_⟩
                      intro V hV hsub hVc
                      apply Set.Subset.antisymm
                      · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_outside
                        · obtain ⟨x, hx⟩ := hs.isConnected_outside.nonempty
                          exact ⟨x, hsub hx, hx⟩
                        · intro x hx
                          rw [(IsRegionOf.outside C).closure_eq hs] at hx
                          rcases hx.1 with hi | hc
                          · exact hi
                          · exact False.elim (hVc hx.2 hc)
                      · exact hsub
                    obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
                    obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
                    have him : F '' C = modelCurve := by
                      ext x
                      constructor
                      · rintro ⟨y, hy, rfl⟩
                        rw [hF ⟨y, hy⟩]
                        exact (e ⟨y, hy⟩).property
                      · intro hx
                        let y := e.symm ⟨x, hx⟩
                        refine ⟨y.val, y.property, ?_⟩
                        rw [hF y]
                        exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
                    have hc := homeomorphism_complement_component F (jordan_inside_complement_component hC)
                    rw [him] at hc
                    have hi := jordan_inside_complement_component isJordanCurve_modelCurve
                    have ho := outsideComponent isJordanCurve_modelCurve
                    obtain ⟨x, hx⟩ := hc.1
                    have hxin : x ∈ inside modelCurve ∪ outside modelCurve :=
                      (inside_union_outside modelCurve).symm ▸ hc.2.2.1 hx
                    have heinside : F '' inside C = inside modelCurve := by
                      rcases hxin with hxI | hxO
                      · by_contra hn
                        exact Set.disjoint_left.mp (complementComponents_disjoint hc hi hn) hx hxI
                      · have heoutside : F '' inside C = outside modelCurve := by
                          by_contra hn
                          exact Set.disjoint_left.mp (complementComponents_disjoint hc ho hn) hx hxO
                        have hs := jordan_curve_theorem hC
                        have hk : IsCompact (closure (inside C)) :=
                          Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
                        have hb : Bornology.IsBounded (F '' inside C) :=
                          (hk.image F.continuous).isBounded.subset (image_mono subset_closure)
                        exact False.elim ((jordan_curve_theorem isJordanCurve_modelCurve).not_isBounded_outside
                          (heoutside ▸ hb))
                    exact ⟨F, him, heinside.trans inside_modelCurve⟩
                  have square : Nonempty (Plane ≃ₜ Plane.openSquare 0 1) := by
                
                    let H : Plane ≃ₜ (Fin 2 → ℝ) := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
                    let B : (Fin 2 → ℝ) ≃ₜ Metric.ball (0 : Fin 2 → ℝ) 1 := Homeomorph.unitBall
                    let K : Metric.ball (0 : Fin 2 → ℝ) 1 ≃ₜ Plane.openSquare 0 1 :=
                      H.symm.subtype (fun x => by
                        simp only [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
                        change (∀ i : Fin 2, ‖x i‖ < 1) ↔ (H.symm x).supDist 0 < 1
                        simp [Schoenflies.Plane.supDist, Schoenflies.Plane.supNorm, Fin.forall_fin_two, H, EuclideanSpace.equiv,
                          PiLp.toLp_apply, Real.norm_eq_abs])
                    exact ⟨(H.trans B).trans K⟩
                  obtain ⟨F, _, hFI⟩ := straight hC
                  obtain ⟨H⟩ := square
                  let R : inside C ≃ₜ Plane.openSquare 0 1 :=
                    (F.isEmbedding.homeomorphImage (inside C)).trans (Homeomorph.setCongr hFI)
                  exact ⟨H.trans R.symm⟩
                have hAkeep := hA
                obtain ⟨k,hkc,hki,hkim,hk0,hk1⟩ := hA
                let a : Interval → Plane := fun t => k t.val
                have hac : Continuous a := continuousOn_iff_continuous_restrict.mp hkc
                have hai : Function.Injective a := by
                  intro t u he
                  exact Subtype.ext (hki t.property u.property he)
                have ha0 : a 0 = x := hk0
                have haImage : range a = A := by
                  rw [← hkim]
                  ext y
                  constructor
                  · rintro ⟨t,rfl⟩; exact ⟨t.val,t.property,rfl⟩
                  · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,rfl⟩
                have h0 : a 0 ∉ inside C := by rw [ha0]; exact fun h => inside_subset_compl h hx
                have hin : ∀ t : Interval, t ≠ 0 → a t ∈ inside C := by
                  intro t ht
                  apply hinA
                  refine ⟨haImage ▸ mem_range_self t,?_⟩
                  intro he
                  have he : a t = x := Set.mem_singleton_iff.mp he
                  exact ht (hai (he.trans ha0.symm))
                obtain ⟨Q,hQ,hmeet,hJ⟩ := exists_jordan_completion_of_isArcBetween hAkeep
                have hsep := jordan_curve_theorem hJ
                have hndJ : IsNowhereDense (Q ∪ A) := by
                  rw [← hsep.frontier_inside]
                  change interior (closure (frontier (inside (Q ∪ A)))) = ∅
                  rw [isClosed_frontier.closure_eq, ← frontier_compl]
                  exact interior_frontier hsep.isOpen_inside.isClosed_compl
                have hndA := hndJ.mono (Set.subset_union_right : A ⊆ Q ∪ A)
                have hDopen := (jordan_curve_theorem hC).isOpen_inside
                obtain ⟨z,hz,hzA⟩ : ∃ z ∈ inside C, z ∉ A := by
                  by_contra hn
                  push_neg at hn
                  have hs : inside C ⊆ closure A := fun z hz => subset_closure (hn z hz)
                  have hi : inside C ⊆ interior (closure A) := hDopen.interior_eq ▸ interior_mono hs
                  obtain ⟨z,hz⟩ := (jordan_curve_theorem hC).isConnected_inside.nonempty
                  rw [show interior (closure A) = ∅ from hndA] at hi
                  exact hi hz
                obtain ⟨H⟩ := disc hC
                let f : Plane → Plane := fun z => (H z).val
                have hf : Topology.IsOpenEmbedding f := hDopen.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding
                have hrange : range f = inside C := by
                  ext y
                  constructor
                  · rintro ⟨t,rfl⟩; exact (H t).property
                  · intro hy
                    exact ⟨H.symm ⟨y,hy⟩,congrArg Subtype.val (H.apply_symm_apply ⟨y,hy⟩)⟩
                let u := H.symm ⟨z,hz⟩
                have hfu : f u = z := congrArg Subtype.val (H.apply_symm_apply ⟨z,hz⟩)
                have hc := slit f hf a hac hai (hrange.symm ▸ h0)
                  (fun t ht => hrange.symm ▸ hin t ht) u (by rw [hfu,haImage]; exact hzA)
                simpa only [hrange,haImage] using hc
              have radial {C : Set Plane} (hC : IsJordanCurve C) {x q : Plane}
                  (hx : x ∈ C) (hq : q ∈ inside C) :
                  ∃ A : Set Plane, IsArcBetween A x q ∧ A \ {x} ⊆ inside C := by
                classical
                have chart {C : Set Plane} (hC : IsJordanCurve C) :
                    ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
                  classical
                  have outsideComponent {C : Set Plane} (hC : IsJordanCurve C) :
                      IsComplementComponent C (outside C) := by
                    have hs := jordan_curve_theorem hC
                    refine ⟨hs.isConnected_outside.nonempty, hs.isConnected_outside, outside_subset_compl, ?_⟩
                    intro V hV hsub hVc
                    apply Set.Subset.antisymm
                    · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_outside
                      · obtain ⟨x, hx⟩ := hs.isConnected_outside.nonempty
                        exact ⟨x, hsub hx, hx⟩
                      · intro x hx
                        rw [(IsRegionOf.outside C).closure_eq hs] at hx
                        rcases hx.1 with hi | hc
                        · exact hi
                        · exact False.elim (hVc hx.2 hc)
                    · exact hsub
                  obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
                  obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
                  have him : F '' C = modelCurve := by
                    ext x
                    constructor
                    · rintro ⟨y, hy, rfl⟩
                      rw [hF ⟨y, hy⟩]
                      exact (e ⟨y, hy⟩).property
                    · intro hx
                      let y := e.symm ⟨x, hx⟩
                      refine ⟨y.val, y.property, ?_⟩
                      rw [hF y]
                      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
                  have hc := homeomorphism_complement_component F (jordan_inside_complement_component hC)
                  rw [him] at hc
                  have hi := jordan_inside_complement_component isJordanCurve_modelCurve
                  have ho := outsideComponent isJordanCurve_modelCurve
                  obtain ⟨x, hx⟩ := hc.1
                  have hxin : x ∈ inside modelCurve ∪ outside modelCurve :=
                    (inside_union_outside modelCurve).symm ▸ hc.2.2.1 hx
                  have heinside : F '' inside C = inside modelCurve := by
                    rcases hxin with hxI | hxO
                    · by_contra hn
                      exact Set.disjoint_left.mp (complementComponents_disjoint hc hi hn) hx hxI
                    · have heoutside : F '' inside C = outside modelCurve := by
                        by_contra hn
                        exact Set.disjoint_left.mp (complementComponents_disjoint hc ho hn) hx hxO
                      have hs := jordan_curve_theorem hC
                      have hk : IsCompact (closure (inside C)) :=
                        Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
                      have hb : Bornology.IsBounded (F '' inside C) :=
                        (hk.image F.continuous).isBounded.subset (image_mono subset_closure)
                      exact False.elim ((jordan_curve_theorem isJordanCurve_modelCurve).not_isBounded_outside
                        (heoutside ▸ hb))
                  exact ⟨F, him, heinside.trans inside_modelCurve⟩
                obtain ⟨F,himage,hin⟩ := chart hC
                have hFx : F x ∈ modelCurve := himage ▸ mem_image_of_mem F hx
                have hFq : F q ∈ Plane.openSquare 0 1 := hin ▸ mem_image_of_mem F hq
                have hxy : F x ≠ F q := by
                  intro he
                  have h1 : Plane.supNorm (F x) = 1 := hFx
                  have h2 : Plane.supNorm (F q) < 1 := mem_openSquare_zero_one.mp hFq
                  rw [he] at h1
                  linarith
                let l : ℝ → Plane := fun t => F x + t • (F q - F x)
                have hl : l = AffineMap.lineMap (F x) (F q) := by
                  ext t
                  simp [l,AffineMap.lineMap_apply_module]
                  <;> ring
                have hli : Function.Injective l := hl ▸ AffineMap.lineMap_injective ℝ hxy
                have hinside (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : l t ∈ Plane.openSquare 0 1 := by
                  have h := (Plane.convex_closedSquare 0 1).add_smul_sub_mem_interior
                    (modelCurve_subset_closedSquare hFx)
                    (show F q ∈ interior (Plane.closedSquare 0 1) by rw [interior_closedSquare_zero_one]; exact hFq) ht
                  rwa [interior_closedSquare_zero_one] at h
                let a : ℝ → Plane := fun t => F.symm (l t)
                have hac : Continuous a := F.symm.continuous.comp (by dsimp [l]; fun_prop)
                have hai : Function.Injective a := F.symm.injective.comp hli
                have ha0 : a 0 = x := by simp [a,l]
                have ha1 : a 1 = q := by simp [a,l]
                refine ⟨a '' I,⟨a,hac.continuousOn,hai.injOn,rfl,ha0,ha1⟩,?_⟩
                rintro z ⟨⟨t,ht,rfl⟩,hn⟩
                have ht0 : t ≠ 0 := by
                  intro he
                  apply hn
                  simp [he,ha0]
                have hti : t ∈ Ioc (0:ℝ) 1 := ⟨lt_of_le_of_ne' ht.1 ht0,ht.2⟩
                have hh : l t ∈ F '' inside C := hin.symm ▸ hinside t hti
                obtain ⟨z,hz,he⟩ := hh
                change F.symm (l t) ∈ inside C
                simpa [← he] using hz
              have small {A U : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
                  (hU : IsOpen U) (ha : a ∈ U) :
                  ∃ B : Set Plane, ∃ c : Plane,
                    IsArcBetween B a c ∧ B ⊆ A ∧ B ⊆ U := by
                obtain ⟨f,hf,hi,himage,hf0,hf1⟩ := hA
                let g : ℝ → Plane := fun t => f (projIcc 0 1 zero_le_one t)
                have hg : Continuous g := (continuousOn_iff_continuous_restrict.mp hf).comp continuous_projIcc
                have hg0 : g 0 = a := by simp [g,projIcc_of_mem zero_le_one (by norm_num : (0:ℝ) ∈ Icc 0 1),hf0]
                have hn : g ⁻¹' U ∈ nhds (0:ℝ) := hg.continuousAt.preimage_mem_nhds (hg0.symm ▸ hU.mem_nhds ha)
                obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
                let d := min (ε/2) (1/2:ℝ)
                have hd : 0 < d := lt_min (by linarith) (by norm_num)
                have hd1 : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
                have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
                have hdmem : d ∈ I := ⟨hd.le,hd1⟩
                have hsubI : uIcc (0:ℝ) d ⊆ I := uIcc_subset_I (by norm_num) hdmem
                refine ⟨f '' uIcc (0:ℝ) d,f d,?_,?_,?_⟩
                · simpa only [hf0] using isArcBetween_subarc_of_injOn_I hf hi (by norm_num) hdmem (ne_of_lt hd)
                · rw [← himage]
                  exact image_mono hsubI
                · rintro y ⟨t,ht,rfl⟩
                  have htc := hsubI ht
                  have ht' : 0 ≤ t ∧ t ≤ d := by simpa [uIcc_of_le hd.le] using ht
                  have hbt : t ∈ Metric.ball (0:ℝ) ε := by
                    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht'.1]
                    exact lt_of_le_of_lt ht'.2 hdε
                  have hm := hball hbt
                  change g t ∈ U at hm
                  simpa only [g,projIcc_of_mem zero_le_one htc] using hm
              have access {A U : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
                  (hU : IsOpen U) (ha : a ∈ U) :
                  ∃ B : Set Plane, ∃ c : Plane,
                    IsArcBetween B a c ∧ B ⊆ U ∧ c ∉ A ∧ B \ {a} ⊆ Aᶜ := by
                have small {A U : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
                    (hU : IsOpen U) (ha : a ∈ U) :
                    ∃ B : Set Plane, ∃ c : Plane,
                      IsArcBetween B a c ∧ B ⊆ A ∧ B ⊆ U := by
                  obtain ⟨f,hf,hi,himage,hf0,hf1⟩ := hA
                  let g : ℝ → Plane := fun t => f (projIcc 0 1 zero_le_one t)
                  have hg : Continuous g := (continuousOn_iff_continuous_restrict.mp hf).comp continuous_projIcc
                  have hg0 : g 0 = a := by simp [g,projIcc_of_mem zero_le_one (by norm_num : (0:ℝ) ∈ Icc 0 1),hf0]
                  have hn : g ⁻¹' U ∈ nhds (0:ℝ) := hg.continuousAt.preimage_mem_nhds (hg0.symm ▸ hU.mem_nhds ha)
                  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
                  let d := min (ε/2) (1/2:ℝ)
                  have hd : 0 < d := lt_min (by linarith) (by norm_num)
                  have hd1 : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
                  have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
                  have hdmem : d ∈ I := ⟨hd.le,hd1⟩
                  have hsubI : uIcc (0:ℝ) d ⊆ I := uIcc_subset_I (by norm_num) hdmem
                  refine ⟨f '' uIcc (0:ℝ) d,f d,?_,?_,?_⟩
                  · simpa only [hf0] using isArcBetween_subarc_of_injOn_I hf hi (by norm_num) hdmem (ne_of_lt hd)
                  · rw [← himage]
                    exact image_mono hsubI
                  · rintro y ⟨t,ht,rfl⟩
                    have htc := hsubI ht
                    have ht' : 0 ≤ t ∧ t ≤ d := by simpa [uIcc_of_le hd.le] using ht
                    have hbt : t ∈ Metric.ball (0:ℝ) ε := by
                      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht'.1]
                      exact lt_of_le_of_lt ht'.2 hdε
                    have hm := hball hbt
                    change g t ∈ U at hm
                    simpa only [g,projIcc_of_mem zero_le_one htc] using hm
                obtain ⟨E,u,hE,hu,havoid⟩ := endpoint_access_of_isArcBetween hA
                obtain ⟨B,c,hB,hBE,hBU⟩ := small hE hU ha
                refine ⟨B,c,hB,hBU,?_,?_⟩
                · exact havoid ⟨hBE hB.right_mem,fun he => hB.ne (Set.mem_singleton_iff.mp he).symm⟩
                · intro x hx
                  exact havoid ⟨hBE hx.1,hx.2⟩
              have hqD : q ∈ inside C := hinA ⟨hA.right_mem,fun he => hA.ne (Set.mem_singleton_iff.mp he).symm⟩
              have hyA : y ∉ A := by
                intro hya
                have hyD := hinA ⟨hya,fun he => hyx (Set.mem_singleton_iff.mp he)⟩
                exact inside_subset_compl hyD hy
              have hyq : y ≠ q := fun he => inside_subset_compl hqD (he ▸ hy)
              have hDopen := (jordan_curve_theorem hC).isOpen_inside
              obtain ⟨R,hR,hRinside⟩ := radial hC hy hqD
              obtain ⟨Y,u,hY,hYR,hYavoid⟩ := small hR hA.isArc.isClosed.isOpen_compl hyA
              have huD : u ∈ inside C := hRinside ⟨hYR hY.right_mem,
                fun he => hY.ne (Set.mem_singleton_iff.mp he).symm⟩
              have huA : u ∉ A := hYavoid hY.right_mem
              obtain ⟨Q,v,hQ,hQD,hvA,hQavoid⟩ := access hA.reverse hDopen hqD
              have hvD : v ∈ inside C := hQD hQ.right_mem
              have hslit : IsConnected (inside C \ A) := slit hC hA hx hinA
              have hopen : IsOpen (inside C \ A) := hDopen.sdiff hA.isArc.isClosed
              have hjoin : ∃ B : Set Plane, IsArcBetween B y q ∧
                  B \ {q} ⊆ Aᶜ ∧ B \ {y} ⊆ inside C := by
                by_cases huv : u = v
                · obtain ⟨B,hBsub,hB⟩ := exists_arc_in_union_of_arcs hY (huv ▸ hQ.reverse) hyq
                  refine ⟨B,hB,?_,?_⟩
                  · intro z hz
                    rcases hBsub hz.1 with hzY | hzQ
                    · exact hYavoid hzY
                    · exact hQavoid ⟨hzQ,hz.2⟩
                  · intro z hz
                    rcases hBsub hz.1 with hzY | hzQ
                    · exact hRinside ⟨hYR hzY,hz.2⟩
                    · exact hQD hzQ
                · obtain ⟨P,hPsub,hPpoly,hP⟩ := exists_simple_arc_of_isPreconnected hopen hslit.isPreconnected
                    ⟨huD,huA⟩ ⟨hvD,hvA⟩ huv
                  have hyv : y ≠ v := fun he => inside_subset_compl hvD (he ▸ hy)
                  obtain ⟨Z,hZsub,hZ⟩ := exists_arc_in_union_of_arcs hY hP hyv
                  obtain ⟨B,hBsub,hB⟩ := exists_arc_in_union_of_arcs hZ hQ.reverse hyq
                  refine ⟨B,hB,?_,?_⟩
                  · intro z hz
                    rcases hBsub hz.1 with hzZ | hzQ
                    · rcases hZsub hzZ with hzY | hzP
                      · exact hYavoid hzY
                      · exact (hPsub hzP).2
                    · exact hQavoid ⟨hzQ,hz.2⟩
                  · intro z hz
                    rcases hBsub hz.1 with hzZ | hzQ
                    · rcases hZsub hzZ with hzY | hzP
                      · exact hRinside ⟨hYR hzY,hz.2⟩
                      · exact (hPsub hzP).1
                    · exact hQD hzQ
              obtain ⟨B,hB,havoid,hBD⟩ := hjoin
              refine ⟨B,hB.reverse,?_,hBD⟩
              apply Set.Subset.antisymm
              · intro z hz
                by_contra hn
                exact havoid ⟨hz.2,hn⟩ hz.1
              · rintro z hz
                have he : z = q := Set.mem_singleton_iff.mp hz
                subst z
                exact ⟨hA.right_mem,hB.right_mem⟩
            have glue {A P B Q : Set Plane} {a q b c r d : Plane}
                (hA : IsArcBetween A a q) (hP : IsArcBetween P q b)
                (hB : IsArcBetween B c r) (hQ : IsArcBetween Q r d)
                (hsrc : A ∩ P = {q}) (htgt : B ∩ Q = {r})
                (eA : ArcHomeo A B a q c r) :
                ∃ h : ArcHomeo (A ∪ P) (B ∪ Q) a b c d,
                  h.toFun q = r ∧ h.toFun '' A = B ∧ EqOn h.toFun eA.toFun A := by
              classical
              obtain ⟨eP⟩ := exists_arcHomeo hP hQ
              let f : Plane → Plane := fun x => if x ∈ A then eA.toFun x else eP.toFun x
              let g : Plane → Plane := fun x => if x ∈ B then eA.invFun x else eP.invFun x
              have fA : ∀ x ∈ A, f x = eA.toFun x := by intro x hx; simp only [f,if_pos hx]
              have fP : ∀ x ∈ P, f x = eP.toFun x := by
                intro x hx
                by_cases ha : x ∈ A
                · have he : x = q := by simpa only [mem_singleton_iff] using (show x ∈ ({q} : Set Plane) from hsrc ▸ (show x ∈ A ∩ P from ⟨ha,hx⟩))
                  subst x
                  simp [f, hA.right_mem, eA.map_right, eP.map_left]
                · simp [f, ha]
              have gB : ∀ x ∈ B, g x = eA.invFun x := by intro x hx; simp only [g,if_pos hx]
              have gQ : ∀ x ∈ Q, g x = eP.invFun x := by
                intro x hx
                by_cases hb : x ∈ B
                · have he : x = r := by simpa only [mem_singleton_iff] using (show x ∈ ({r} : Set Plane) from htgt ▸ (show x ∈ B ∩ Q from ⟨hb,hx⟩))
                  subst x
                  have ea : eA.invFun r = q := (congrArg eA.invFun eA.map_right.symm).trans (eA.leftInvOn hA.right_mem)
                  have ep : eP.invFun r = q := (congrArg eP.invFun eP.map_left.symm).trans (eP.leftInvOn hP.left_mem)
                  simp [g, hB.right_mem, ea, ep]
                · simp [g, hb]
              have fc : ContinuousOn f (A ∪ P) :=
                Plane.continuousOn_union_of_isClosed hA.isArc.isCompact.isClosed hP.isArc.isCompact.isClosed
                  (eA.continuousOn_toFun.congr fA) (eP.continuousOn_toFun.congr fP)
              have gc : ContinuousOn g (B ∪ Q) :=
                Plane.continuousOn_union_of_isClosed hB.isArc.isCompact.isClosed hQ.isArc.isCompact.isClosed
                  (eA.continuousOn_invFun.congr gB) (eP.continuousOn_invFun.congr gQ)
              have li : LeftInvOn g f (A ∪ P) := by
                intro x hx
                rcases hx with ha | hp
                · rw [fA x ha, gB _ (eA.mapsTo ha)]; exact eA.leftInvOn ha
                · rw [fP x hp, gQ _ (eP.mapsTo hp)]; exact eP.leftInvOn hp
              have ri : RightInvOn g f (B ∪ Q) := by
                intro x hx
                rcases hx with hb | hq
                · rw [gB x hb, fA _ (eA.mapsTo_invFun hb)]; exact eA.rightInvOn hb
                · rw [gQ x hq, fP _ (eP.mapsTo_invFun hq)]; exact eP.rightInvOn hq
              have imA : f '' A = B := by
                calc
                  f '' A = eA.toFun '' A := image_congr fA
                  _ = B := eA.image_eq
              have imP : f '' P = Q := by
                calc
                  f '' P = eP.toFun '' P := image_congr fP
                  _ = Q := eP.image_eq
              refine ⟨{ toFun := f
                        invFun := g
                        continuousOn_toFun := fc
                        continuousOn_invFun := gc
                        leftInvOn := li
                        rightInvOn := ri
                        image_eq := ?_
                        map_left := ?_
                        map_right := ?_ }, ?_, imA, fA⟩
              · rw [image_union, imA, imP]
              · exact (fA _ hA.left_mem).trans eA.map_left
              · exact (fP _ hP.right_mem).trans eP.map_right
              · exact (fA _ hA.right_mem).trans eA.map_right
            have prescribed
                (A B : Set Plane) (a b : Plane)
                (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
                (h : ArcHomeo A B a b a b)
                (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
                (hAi : A \ {a, b} ⊆ Plane.openSquare 0 1)
                (hBi : B \ {a, b} ⊆ Plane.openSquare 0 1) :
                ∃ F : Plane ≃ₜ Plane,
                  F '' A = B ∧ (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) ∧
                  EqOn F h.toFun A := by
              classical
              obtain ⟨R₁, R₂, hcut⟩ := exists_isCutPair isJordanCurve_modelCurve ha hb hA.ne
              obtain ⟨F₁, G₁, h₁, hF₁fixed, hF₁arc, hF₁image⟩ :=
                exists_closed_subdisk_homeomorph_fixing_arc hcut.fst hA hB
                  (model_boundary_arc_meet_crosscut hcut.fst hcut.fst_subset hA hAi)
                  (model_boundary_arc_meet_crosscut hcut.fst hcut.fst_subset hB hBi) h
              obtain ⟨F₂, G₂, h₂, hF₂fixed, hF₂arc, hF₂image⟩ :=
                exists_closed_subdisk_homeomorph_fixing_arc hcut.snd hA hB
                  (model_boundary_arc_meet_crosscut hcut.snd hcut.snd_subset hA hAi)
                  (model_boundary_arc_meet_crosscut hcut.snd hcut.snd_subset hB hBi) h
              have closed {R P : Set Plane} {a b : Plane}
                  (hR : IsArcBetween R a b) (hP : IsArcBetween P a b)
                  (hRP : R ∩ P = {a,b}) : IsClosed ((R ∪ P) ∪ inside (R ∪ P)) := by
                have hJ : IsJordanCurve (R ∪ P) := by
                  apply isJordanCurve_union hR hP
                  intro x hxR hxP
                  have hx : x ∈ ({a,b} : Set Plane) := hRP ▸ ⟨hxR,hxP⟩
                  simpa using hx
                exact isClosed_union_inside (jordan_curve_theorem hJ)
              let D₁ : Set Plane := (R₁ ∪ A) ∪ inside (R₁ ∪ A)
              let D₂ : Set Plane := (R₂ ∪ A) ∪ inside (R₂ ∪ A)
              let E₁ : Set Plane := (R₁ ∪ B) ∪ inside (R₁ ∪ B)
              let E₂ : Set Plane := (R₂ ∪ B) ∪ inside (R₂ ∪ B)
              let S : Set Plane := Plane.closedSquare 0 1
              have hpartA : D₁ ∪ D₂ = S ∧ D₁ ∩ D₂ = A :=
                square_crosscut_subdisk_partition hA hcut hAi
              have hpartB : E₁ ∪ E₂ = S ∧ E₁ ∩ E₂ = B :=
                square_crosscut_subdisk_partition hB hcut hBi
              have hR₁A := model_boundary_arc_meet_crosscut hcut.fst
                hcut.fst_subset hA hAi
              have hR₂A := model_boundary_arc_meet_crosscut hcut.snd
                hcut.snd_subset hA hAi
              have hR₁B := model_boundary_arc_meet_crosscut hcut.fst
                hcut.fst_subset hB hBi
              have hR₂B := model_boundary_arc_meet_crosscut hcut.snd
                hcut.snd_subset hB hBi
              have hD₁ : IsClosed D₁ := closed hcut.fst hA hR₁A
              have hD₂ : IsClosed D₂ := closed hcut.snd hA hR₂A
              have hE₁ : IsClosed E₁ := closed hcut.fst hB hR₁B
              have hE₂ : IsClosed E₂ := closed hcut.snd hB hR₂B
              have hagree : ∀ x ∈ D₁ ∩ D₂, F₁ x = F₂ x := by
                intro x hx
                have hxA : x ∈ A := hpartA.2 ▸ hx
                rw [hF₁arc x hxA, hF₂arc x hxA]
              have himageOverlap : F₁ '' (D₁ ∩ D₂) = E₁ ∩ E₂ := by
                rw [hpartA.2, hpartB.2]
                exact hF₁image
              obtain ⟨F, G, hFG, hFD₁, hFD₂⟩ :=
                glue_closed_homeoOn hD₁ hD₂ hE₁ hE₂ h₁ h₂ hagree himageOverlap
              have hFGS : IsHomeoOn F G S S := by
                simpa only [hpartA.1, hpartB.1] using hFG
              let E : S ≃ S := {
                toFun := fun x => ⟨F x, hFGS.mapsTo x.property⟩
                invFun := fun y => ⟨G y, hFGS.mapsTo_inv y.property⟩
                left_inv := by
                  intro x
                  apply Subtype.ext
                  exact hFGS.invOn.1 x.property
                right_inv := by
                  intro y
                  apply Subtype.ext
                  exact hFGS.invOn.2 y.property }
              let e : S ≃ₜ S := {
                toEquiv := E
                continuous_toFun := hFGS.continuousOn.domRestrict.subtype_mk _
                continuous_invFun := hFGS.continuousOn_inv.domRestrict.subtype_mk _ }
              have hboundary : ∀ x : S, (x : Plane) ∈ modelCurve → e x = x := by
                intro x hxC
                have hxR : (x : Plane) ∈ R₁ ∪ R₂ := hcut.union_eq.symm ▸ hxC
                apply Subtype.ext
                rcases hxR with hxR₁ | hxR₂
                · exact (hFD₁ x (Or.inl (Or.inl hxR₁))).trans (hF₁fixed x hxR₁)
                · exact (hFD₂ x (Or.inl (Or.inl hxR₂))).trans (hF₂fixed x hxR₂)
              have hFA : F '' A = B := by
                have hEq : EqOn F F₁ A := by
                  intro x hxA
                  exact hFD₁ x (Or.inl (Or.inr hxA))
                exact hEq.image_eq.trans hF₁image
              have hAclosed : A ⊆ S := crosscut_subset_closedSquare ha hb hAi
              have hBclosed : B ⊆ S := crosscut_subset_closedSquare ha hb hBi
              have heImage : e '' {x : S | (x : Plane) ∈ A} =
                  {x : S | (x : Plane) ∈ B} := by
                ext y
                constructor
                · rintro ⟨x, hxA, rfl⟩
                  have hxB : F x ∈ B := by
                    rw [← hFA]
                    exact ⟨x, hxA, rfl⟩
                  exact hxB
                · intro hyB
                  have hyImage : (y : Plane) ∈ F '' A := by rw [hFA]; exact hyB
                  obtain ⟨x, hxA, hxy⟩ := hyImage
                  refine ⟨⟨x, hAclosed hxA⟩, hxA, ?_⟩
                  apply Subtype.ext
                  exact hxy
              have hSU : Plane.openSquare 0 1 ⊆ S := by
                intro x hx
                exact mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hx).le
              have hfix : ∀ x : S, (x : Plane) ∉ Plane.openSquare 0 1 → e x = x := by
                intro x hx
                apply hboundary
                rw [modelCurve_eq_frontier, (Plane.isClosed_closedSquare 0 1).frontier_eq,
                  interior_closedSquare_zero_one]
                exact ⟨x.property, hx⟩
              let K := extendClosedHomeomorph S (Plane.openSquare 0 1)
                (Plane.isClosed_closedSquare 0 1) (Plane.isOpen_openSquare 0 1) hSU e hfix
              have kOn : ∀ x ∈ A, K x = h.toFun x := by
                intro x hx
                have hxS : x ∈ S := hAclosed hx
                have hk : K x = F x := by
                  change (if hx : x ∈ S then (e ⟨x,hx⟩ : Plane) else x) = F x
                  rw [dif_pos hxS]
                  rfl
                exact hk.trans ((hFD₁ x (Or.inl (Or.inr hx))).trans (hF₁arc x hx))
              refine ⟨K, ?_, ?_, kOn⟩
              · exact (image_congr kOn).trans h.image_eq
              · intro x hx
                exact extendClosedHomeomorph_apply_outside S (Plane.openSquare 0 1)
                  (Plane.isClosed_closedSquare 0 1) (Plane.isOpen_openSquare 0 1) hSU e hfix x hx
            obtain ⟨P,hP,hAP,hPi⟩ := completion isJordanCurve_modelCurve hA hx hy hyx
              (by simpa only [inside_modelCurve] using hAi)
            obtain ⟨Q,hQ,hBQ,hQi⟩ := completion isJordanCurve_modelCurve hB hx hy hyx
              (by simpa only [inside_modelCurve] using hBi)
            obtain ⟨g,hgp,hgA,hgOn⟩ := glue hA hP hB hQ hAP hBQ h
            have hU : IsArcBetween (A∪P) x y := hA.concatenate hP (by
              intro z hzA hzP
              simpa using (show z ∈ ({p}:Set Plane) from hAP ▸ ⟨hzA,hzP⟩))
            have hV : IsArcBetween (B∪Q) x y := hB.concatenate hQ (by
              intro z hzB hzQ
              simpa using (show z ∈ ({p}:Set Plane) from hBQ ▸ ⟨hzB,hzQ⟩))
            have hUi : (A∪P) \ {x,y} ⊆ Plane.openSquare 0 1 := by
              intro z hz
              rcases hz.1 with hzA | hzP
              · exact hAi ⟨hzA,fun he => hz.2 (Or.inl (mem_singleton_iff.mp he))⟩
              · exact inside_modelCurve ▸ hPi ⟨hzP,fun he => hz.2 (Or.inr (mem_singleton_iff.mp he))⟩
            have hVi : (B∪Q) \ {x,y} ⊆ Plane.openSquare 0 1 := by
              intro z hz
              rcases hz.1 with hzB | hzQ
              · exact hBi ⟨hzB,fun he => hz.2 (Or.inl (mem_singleton_iff.mp he))⟩
              · exact inside_modelCurve ▸ hQi ⟨hzQ,fun he => hz.2 (Or.inr (mem_singleton_iff.mp he))⟩
            obtain ⟨F,hFG,hFout,hFon⟩ := prescribed (A∪P) (B∪Q) x y hU hV g hx hy hUi hVi
            have hFp : F p = p := (hFon (Or.inl hA.right_mem)).trans hgp
            obtain ⟨H,hHfinal,hHout,hHp⟩ := square_marked_supported_isotopy F p hp hFp hFout
            refine ⟨H,?_,hHout,hHp⟩
            rw [hHfinal]
            intro z hz
            exact (hFon (Or.inl hz)).trans (hgOn hz)
          have tail {C A : Set Plane} {p q x : Plane}
              (hC : IsJordanCurve C) (hA : IsArcBetween A p q)
              (hAi : A ⊆ inside C) (hx : x ∈ C) :
              ∃ P : Set Plane, IsArcBetween P q x ∧
                A ∩ P = {q} ∧ P \ {x} ⊆ inside C := by
            classical
            have slit {C A : Set Plane} (hC : IsJordanCurve C) (hA : IsArc A)
                (hAC : A ⊆ inside C) : IsConnected (inside C \ A) := by
              classical
              have chart {C : Set Plane} (hC : IsJordanCurve C) : Nonempty (Plane ≃ₜ inside C) := by
                have straight {C : Set Plane} (hC : IsJordanCurve C) :
                  ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
              
                  classical
                  have outsideComponent {C : Set Plane} (hC : IsJordanCurve C) :
                      IsComplementComponent C (outside C) := by
                    have hs := jordan_curve_theorem hC
                    refine ⟨hs.isConnected_outside.nonempty, hs.isConnected_outside, outside_subset_compl, ?_⟩
                    intro V hV hsub hVc
                    apply Set.Subset.antisymm
                    · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_outside
                      · obtain ⟨x, hx⟩ := hs.isConnected_outside.nonempty
                        exact ⟨x, hsub hx, hx⟩
                      · intro x hx
                        rw [(IsRegionOf.outside C).closure_eq hs] at hx
                        rcases hx.1 with hi | hc
                        · exact hi
                        · exact False.elim (hVc hx.2 hc)
                    · exact hsub
                  obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
                  obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
                  have him : F '' C = modelCurve := by
                    ext x
                    constructor
                    · rintro ⟨y, hy, rfl⟩
                      rw [hF ⟨y, hy⟩]
                      exact (e ⟨y, hy⟩).property
                    · intro hx
                      let y := e.symm ⟨x, hx⟩
                      refine ⟨y.val, y.property, ?_⟩
                      rw [hF y]
                      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
                  have hc := homeomorphism_complement_component F (jordan_inside_complement_component hC)
                  rw [him] at hc
                  have hi := jordan_inside_complement_component isJordanCurve_modelCurve
                  have ho := outsideComponent isJordanCurve_modelCurve
                  obtain ⟨x, hx⟩ := hc.1
                  have hxin : x ∈ inside modelCurve ∪ outside modelCurve :=
                    (inside_union_outside modelCurve).symm ▸ hc.2.2.1 hx
                  have heinside : F '' inside C = inside modelCurve := by
                    rcases hxin with hxI | hxO
                    · by_contra hn
                      exact Set.disjoint_left.mp (complementComponents_disjoint hc hi hn) hx hxI
                    · have heoutside : F '' inside C = outside modelCurve := by
                        by_contra hn
                        exact Set.disjoint_left.mp (complementComponents_disjoint hc ho hn) hx hxO
                      have hs := jordan_curve_theorem hC
                      have hk : IsCompact (closure (inside C)) :=
                        Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
                      have hb : Bornology.IsBounded (F '' inside C) :=
                        (hk.image F.continuous).isBounded.subset (image_mono subset_closure)
                      exact False.elim ((jordan_curve_theorem isJordanCurve_modelCurve).not_isBounded_outside
                        (heoutside ▸ hb))
                  exact ⟨F, him, heinside.trans inside_modelCurve⟩
                have square : Nonempty (Plane ≃ₜ Plane.openSquare 0 1) := by
              
                  let H : Plane ≃ₜ (Fin 2 → ℝ) := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
                  let B : (Fin 2 → ℝ) ≃ₜ Metric.ball (0 : Fin 2 → ℝ) 1 := Homeomorph.unitBall
                  let K : Metric.ball (0 : Fin 2 → ℝ) 1 ≃ₜ Plane.openSquare 0 1 :=
                    H.symm.subtype (fun x => by
                      simp only [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
                      change (∀ i : Fin 2, ‖x i‖ < 1) ↔ (H.symm x).supDist 0 < 1
                      simp [Schoenflies.Plane.supDist, Schoenflies.Plane.supNorm, Fin.forall_fin_two, H, EuclideanSpace.equiv,
                        PiLp.toLp_apply, Real.norm_eq_abs])
                  exact ⟨(H.trans B).trans K⟩
                obtain ⟨F, _, hFI⟩ := straight hC
                obtain ⟨H⟩ := square
                let R : inside C ≃ₜ Plane.openSquare 0 1 :=
                  (F.isEmbedding.homeomorphImage (inside C)).trans (Homeomorph.setCongr hFI)
                exact ⟨H.trans R.symm⟩
              obtain ⟨e⟩ := chart hC
              obtain ⟨g,hg,hgi,hgA⟩ := hA
              let γ : Set.Icc (0 : ℝ) 1 → Plane := fun t => e.symm ⟨g t,hAC (hgA ▸ mem_image_of_mem g t.property)⟩
              have hγ : Continuous γ := e.symm.continuous.comp (hg.restrict.subtype_mk _)
              have hγi : Function.Injective γ := by
                intro t u h
                have he := congrArg (fun z => (e z).val) h
                have hgu : g t = g u := by simpa [γ] using he
                exact Subtype.ext (hgi t.property u.property hgu)
              let l : ℝ → Plane := γ ∘ Set.projIcc 0 1 zero_le_one
              have hl : Continuous l := hγ.comp continuous_projIcc
              have hli : Set.InjOn l (Set.Icc 0 1) := by
                intro t ht u hu h
                have h := hγi h
                simpa [l, Set.projIcc_of_mem, ht, hu] using congrArg Subtype.val h
              have hArc : IsArc (Set.range γ) := by
                refine ⟨l,hl.continuousOn,hli,?_⟩
                ext z
                constructor
                · rintro ⟨t,ht,rfl⟩
                  exact ⟨_,rfl⟩
                · rintro ⟨t,rfl⟩
                  refine ⟨t,t.property,?_⟩
                  simp [l,Set.projIcc_of_mem]
              let f : Plane → Plane := fun z => (e z).val
              have hf : Continuous f := continuous_subtype_val.comp e.continuous
              have him : f '' (Set.range γ)ᶜ = inside C \ A := by
                ext z
                constructor
                · rintro ⟨y,hy,rfl⟩
                  refine ⟨(e y).property,?_⟩
                  intro ha
                  obtain ⟨t,ht,hgt⟩ := hgA.symm ▸ ha
                  apply hy
                  refine ⟨⟨t,ht⟩,?_⟩
                  apply e.injective
                  apply Subtype.ext
                  simpa [γ,f] using hgt
                · rintro ⟨hz,hza⟩
                  refine ⟨e.symm ⟨z,hz⟩,?_,?_⟩
                  · rintro ⟨t,ht⟩
                    apply hza
                    rw [← hgA]
                    refine ⟨t,t.property,?_⟩
                    have he := congrArg (fun y => (e y).val) ht
                    simpa [γ] using he
                  · exact congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)
              rw [← him]
              exact (Schoenflies.arc_complement hArc).image f hf.continuousOn
            have radial {C : Set Plane} (hC : IsJordanCurve C) {p q : Plane}
                (hx : p ∈ C) (hq : q ∈ inside C) :
                ∃ A : Set Plane, IsArcBetween A p q ∧ A \ {p} ⊆ inside C := by
              classical
              have chart {C : Set Plane} (hC : IsJordanCurve C) :
                  ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
                classical
                have outsideComponent {C : Set Plane} (hC : IsJordanCurve C) :
                    IsComplementComponent C (outside C) := by
                  have hs := jordan_curve_theorem hC
                  refine ⟨hs.isConnected_outside.nonempty, hs.isConnected_outside, outside_subset_compl, ?_⟩
                  intro V hV hsub hVc
                  apply Set.Subset.antisymm
                  · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_outside
                    · obtain ⟨p, hx⟩ := hs.isConnected_outside.nonempty
                      exact ⟨p, hsub hx, hx⟩
                    · intro p hx
                      rw [(IsRegionOf.outside C).closure_eq hs] at hx
                      rcases hx.1 with hi | hc
                      · exact hi
                      · exact False.elim (hVc hx.2 hc)
                  · exact hsub
                obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
                obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
                have him : F '' C = modelCurve := by
                  ext p
                  constructor
                  · rintro ⟨x, hy, rfl⟩
                    rw [hF ⟨x, hy⟩]
                    exact (e ⟨x, hy⟩).property
                  · intro hx
                    let x := e.symm ⟨p, hx⟩
                    refine ⟨x.val, x.property, ?_⟩
                    rw [hF x]
                    exact congrArg Subtype.val (e.apply_symm_apply ⟨p, hx⟩)
                have hc := homeomorphism_complement_component F (jordan_inside_complement_component hC)
                rw [him] at hc
                have hi := jordan_inside_complement_component isJordanCurve_modelCurve
                have ho := outsideComponent isJordanCurve_modelCurve
                obtain ⟨p, hx⟩ := hc.1
                have hxin : p ∈ inside modelCurve ∪ outside modelCurve :=
                  (inside_union_outside modelCurve).symm ▸ hc.2.2.1 hx
                have heinside : F '' inside C = inside modelCurve := by
                  rcases hxin with hxI | hxO
                  · by_contra hn
                    exact Set.disjoint_left.mp (complementComponents_disjoint hc hi hn) hx hxI
                  · have heoutside : F '' inside C = outside modelCurve := by
                      by_contra hn
                      exact Set.disjoint_left.mp (complementComponents_disjoint hc ho hn) hx hxO
                    have hs := jordan_curve_theorem hC
                    have hk : IsCompact (closure (inside C)) :=
                      Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
                    have hb : Bornology.IsBounded (F '' inside C) :=
                      (hk.image F.continuous).isBounded.subset (image_mono subset_closure)
                    exact False.elim ((jordan_curve_theorem isJordanCurve_modelCurve).not_isBounded_outside
                      (heoutside ▸ hb))
                exact ⟨F, him, heinside.trans inside_modelCurve⟩
              obtain ⟨F,himage,hin⟩ := chart hC
              have hFx : F p ∈ modelCurve := himage ▸ mem_image_of_mem F hx
              have hFq : F q ∈ Plane.openSquare 0 1 := hin ▸ mem_image_of_mem F hq
              have hxy : F p ≠ F q := by
                intro he
                have h1 : Plane.supNorm (F p) = 1 := hFx
                have h2 : Plane.supNorm (F q) < 1 := mem_openSquare_zero_one.mp hFq
                rw [he] at h1
                linarith
              let l : ℝ → Plane := fun t => F p + t • (F q - F p)
              have hl : l = AffineMap.lineMap (F p) (F q) := by
                ext t
                simp [l,AffineMap.lineMap_apply_module]
                <;> ring
              have hli : Function.Injective l := hl ▸ AffineMap.lineMap_injective ℝ hxy
              have hinside (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : l t ∈ Plane.openSquare 0 1 := by
                have h := (Plane.convex_closedSquare 0 1).add_smul_sub_mem_interior
                  (modelCurve_subset_closedSquare hFx)
                  (show F q ∈ interior (Plane.closedSquare 0 1) by rw [interior_closedSquare_zero_one]; exact hFq) ht
                rwa [interior_closedSquare_zero_one] at h
              let a : ℝ → Plane := fun t => F.symm (l t)
              have hac : Continuous a := F.symm.continuous.comp (by dsimp [l]; fun_prop)
              have hai : Function.Injective a := F.symm.injective.comp hli
              have ha0 : a 0 = p := by simp [a,l]
              have ha1 : a 1 = q := by simp [a,l]
              refine ⟨a '' I,⟨a,hac.continuousOn,hai.injOn,rfl,ha0,ha1⟩,?_⟩
              rintro z ⟨⟨t,ht,rfl⟩,hn⟩
              have ht0 : t ≠ 0 := by
                intro he
                apply hn
                simp [he,ha0]
              have hti : t ∈ Ioc (0:ℝ) 1 := ⟨lt_of_le_of_ne' ht.1 ht0,ht.2⟩
              have hh : l t ∈ F '' inside C := hin.symm ▸ hinside t hti
              obtain ⟨z,hz,he⟩ := hh
              change F.symm (l t) ∈ inside C
              simpa [← he] using hz
            have small {A U : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
                (hU : IsOpen U) (ha : a ∈ U) :
                ∃ B : Set Plane, ∃ c : Plane,
                  IsArcBetween B a c ∧ B ⊆ A ∧ B ⊆ U := by
              obtain ⟨f,hf,hi,himage,hf0,hf1⟩ := hA
              let g : ℝ → Plane := fun t => f (projIcc 0 1 zero_le_one t)
              have hg : Continuous g := (continuousOn_iff_continuous_restrict.mp hf).comp continuous_projIcc
              have hg0 : g 0 = a := by simp [g,projIcc_of_mem zero_le_one (by norm_num : (0:ℝ) ∈ Icc 0 1),hf0]
              have hn : g ⁻¹' U ∈ nhds (0:ℝ) := hg.continuousAt.preimage_mem_nhds (hg0.symm ▸ hU.mem_nhds ha)
              obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
              let d := min (ε/2) (1/2:ℝ)
              have hd : 0 < d := lt_min (by linarith) (by norm_num)
              have hd1 : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
              have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
              have hdmem : d ∈ I := ⟨hd.le,hd1⟩
              have hsubI : uIcc (0:ℝ) d ⊆ I := uIcc_subset_I (by norm_num) hdmem
              refine ⟨f '' uIcc (0:ℝ) d,f d,?_,?_,?_⟩
              · simpa only [hf0] using isArcBetween_subarc_of_injOn_I hf hi (by norm_num) hdmem (ne_of_lt hd)
              · rw [← himage]
                exact image_mono hsubI
              · rintro x ⟨t,ht,rfl⟩
                have htc := hsubI ht
                have ht' : 0 ≤ t ∧ t ≤ d := by simpa [uIcc_of_le hd.le] using ht
                have hbt : t ∈ Metric.ball (0:ℝ) ε := by
                  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht'.1]
                  exact lt_of_le_of_lt ht'.2 hdε
                have hm := hball hbt
                change g t ∈ U at hm
                simpa only [g,projIcc_of_mem zero_le_one htc] using hm
            have access {A U : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
                (hU : IsOpen U) (ha : a ∈ U) :
                ∃ B : Set Plane, ∃ c : Plane,
                  IsArcBetween B a c ∧ B ⊆ U ∧ c ∉ A ∧ B \ {a} ⊆ Aᶜ := by
              have small {A U : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
                  (hU : IsOpen U) (ha : a ∈ U) :
                  ∃ B : Set Plane, ∃ c : Plane,
                    IsArcBetween B a c ∧ B ⊆ A ∧ B ⊆ U := by
                obtain ⟨f,hf,hi,himage,hf0,hf1⟩ := hA
                let g : ℝ → Plane := fun t => f (projIcc 0 1 zero_le_one t)
                have hg : Continuous g := (continuousOn_iff_continuous_restrict.mp hf).comp continuous_projIcc
                have hg0 : g 0 = a := by simp [g,projIcc_of_mem zero_le_one (by norm_num : (0:ℝ) ∈ Icc 0 1),hf0]
                have hn : g ⁻¹' U ∈ nhds (0:ℝ) := hg.continuousAt.preimage_mem_nhds (hg0.symm ▸ hU.mem_nhds ha)
                obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
                let d := min (ε/2) (1/2:ℝ)
                have hd : 0 < d := lt_min (by linarith) (by norm_num)
                have hd1 : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
                have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
                have hdmem : d ∈ I := ⟨hd.le,hd1⟩
                have hsubI : uIcc (0:ℝ) d ⊆ I := uIcc_subset_I (by norm_num) hdmem
                refine ⟨f '' uIcc (0:ℝ) d,f d,?_,?_,?_⟩
                · simpa only [hf0] using isArcBetween_subarc_of_injOn_I hf hi (by norm_num) hdmem (ne_of_lt hd)
                · rw [← himage]
                  exact image_mono hsubI
                · rintro x ⟨t,ht,rfl⟩
                  have htc := hsubI ht
                  have ht' : 0 ≤ t ∧ t ≤ d := by simpa [uIcc_of_le hd.le] using ht
                  have hbt : t ∈ Metric.ball (0:ℝ) ε := by
                    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht'.1]
                    exact lt_of_le_of_lt ht'.2 hdε
                  have hm := hball hbt
                  change g t ∈ U at hm
                  simpa only [g,projIcc_of_mem zero_le_one htc] using hm
              obtain ⟨E,u,hE,hu,havoid⟩ := endpoint_access_of_isArcBetween hA
              obtain ⟨B,c,hB,hBE,hBU⟩ := small hE hU ha
              refine ⟨B,c,hB,hBU,?_,?_⟩
              · exact havoid ⟨hBE hB.right_mem,fun he => hB.ne (Set.mem_singleton_iff.mp he).symm⟩
              · intro p hx
                exact havoid ⟨hBE hx.1,hx.2⟩
            have hqD : q ∈ inside C := hAi hA.right_mem
            have hyA : x ∉ A := by
              intro hxA
              exact inside_subset_compl (hAi hxA) hx
            have hyq : x ≠ q := fun he => inside_subset_compl hqD (he ▸ hx)
            have hDopen := (jordan_curve_theorem hC).isOpen_inside
            obtain ⟨R,hR,hRinside⟩ := radial hC hx hqD
            obtain ⟨Y,u,hY,hYR,hYavoid⟩ := small hR hA.isArc.isClosed.isOpen_compl hyA
            have huD : u ∈ inside C := hRinside ⟨hYR hY.right_mem,
              fun he => hY.ne (Set.mem_singleton_iff.mp he).symm⟩
            have huA : u ∉ A := hYavoid hY.right_mem
            obtain ⟨Q,v,hQ,hQD,hvA,hQavoid⟩ := access hA.reverse hDopen hqD
            have hvD : v ∈ inside C := hQD hQ.right_mem
            have hslit : IsConnected (inside C \ A) := slit hC hA.isArc hAi
            have hopen : IsOpen (inside C \ A) := hDopen.sdiff hA.isArc.isClosed
            have hjoin : ∃ B : Set Plane, IsArcBetween B x q ∧
                B \ {q} ⊆ Aᶜ ∧ B \ {x} ⊆ inside C := by
              by_cases huv : u = v
              · obtain ⟨B,hBsub,hB⟩ := exists_arc_in_union_of_arcs hY (huv ▸ hQ.reverse) hyq
                refine ⟨B,hB,?_,?_⟩
                · intro z hz
                  rcases hBsub hz.1 with hzY | hzQ
                  · exact hYavoid hzY
                  · exact hQavoid ⟨hzQ,hz.2⟩
                · intro z hz
                  rcases hBsub hz.1 with hzY | hzQ
                  · exact hRinside ⟨hYR hzY,hz.2⟩
                  · exact hQD hzQ
              · obtain ⟨P,hPsub,hPpoly,hP⟩ := exists_simple_arc_of_isPreconnected hopen hslit.isPreconnected
                  ⟨huD,huA⟩ ⟨hvD,hvA⟩ huv
                have hyv : x ≠ v := fun he => inside_subset_compl hvD (he ▸ hx)
                obtain ⟨Z,hZsub,hZ⟩ := exists_arc_in_union_of_arcs hY hP hyv
                obtain ⟨B,hBsub,hB⟩ := exists_arc_in_union_of_arcs hZ hQ.reverse hyq
                refine ⟨B,hB,?_,?_⟩
                · intro z hz
                  rcases hBsub hz.1 with hzZ | hzQ
                  · rcases hZsub hzZ with hzY | hzP
                    · exact hYavoid hzY
                    · exact (hPsub hzP).2
                  · exact hQavoid ⟨hzQ,hz.2⟩
                · intro z hz
                  rcases hBsub hz.1 with hzZ | hzQ
                  · rcases hZsub hzZ with hzY | hzP
                    · exact hRinside ⟨hYR hzY,hz.2⟩
                    · exact (hPsub hzP).1
                  · exact hQD hzQ
            obtain ⟨B,hB,havoid,hBD⟩ := hjoin
            refine ⟨B,hB.reverse,?_,hBD⟩
            apply Set.Subset.antisymm
            · intro z hz
              by_contra hn
              exact havoid ⟨hz.2,hn⟩ hz.1
            · rintro z hz
              have he : z = q := Set.mem_singleton_iff.mp hz
              subst z
              exact ⟨hA.right_mem,hB.right_mem⟩
          have glue {A P B Q : Set Plane} {a q b c r d : Plane}
              (hA : IsArcBetween A a q) (hP : IsArcBetween P q b)
              (hB : IsArcBetween B c r) (hQ : IsArcBetween Q r d)
              (hsrc : A ∩ P = {q}) (htgt : B ∩ Q = {r})
              (eA : ArcHomeo A B a q c r) :
              ∃ h : ArcHomeo (A ∪ P) (B ∪ Q) a b c d,
                h.toFun q = r ∧ h.toFun '' A = B ∧ EqOn h.toFun eA.toFun A ∧ h.toFun '' P = Q := by
            classical
            obtain ⟨eP⟩ := exists_arcHomeo hP hQ
            let f : Plane → Plane := fun x => if x ∈ A then eA.toFun x else eP.toFun x
            let g : Plane → Plane := fun x => if x ∈ B then eA.invFun x else eP.invFun x
            have fA : ∀ x ∈ A, f x = eA.toFun x := by intro x hx; simp only [f,if_pos hx]
            have fP : ∀ x ∈ P, f x = eP.toFun x := by
              intro x hx
              by_cases ha : x ∈ A
              · have he : x = q := by simpa only [mem_singleton_iff] using (show x ∈ ({q} : Set Plane) from hsrc ▸ (show x ∈ A ∩ P from ⟨ha,hx⟩))
                subst x
                simp [f, hA.right_mem, eA.map_right, eP.map_left]
              · simp [f, ha]
            have gB : ∀ x ∈ B, g x = eA.invFun x := by intro x hx; simp only [g,if_pos hx]
            have gQ : ∀ x ∈ Q, g x = eP.invFun x := by
              intro x hx
              by_cases hb : x ∈ B
              · have he : x = r := by simpa only [mem_singleton_iff] using (show x ∈ ({r} : Set Plane) from htgt ▸ (show x ∈ B ∩ Q from ⟨hb,hx⟩))
                subst x
                have ea : eA.invFun r = q := (congrArg eA.invFun eA.map_right.symm).trans (eA.leftInvOn hA.right_mem)
                have ep : eP.invFun r = q := (congrArg eP.invFun eP.map_left.symm).trans (eP.leftInvOn hP.left_mem)
                simp [g, hB.right_mem, ea, ep]
              · simp [g, hb]
            have fc : ContinuousOn f (A ∪ P) :=
              Plane.continuousOn_union_of_isClosed hA.isArc.isCompact.isClosed hP.isArc.isCompact.isClosed
                (eA.continuousOn_toFun.congr fA) (eP.continuousOn_toFun.congr fP)
            have gc : ContinuousOn g (B ∪ Q) :=
              Plane.continuousOn_union_of_isClosed hB.isArc.isCompact.isClosed hQ.isArc.isCompact.isClosed
                (eA.continuousOn_invFun.congr gB) (eP.continuousOn_invFun.congr gQ)
            have li : LeftInvOn g f (A ∪ P) := by
              intro x hx
              rcases hx with ha | hp
              · rw [fA x ha, gB _ (eA.mapsTo ha)]; exact eA.leftInvOn ha
              · rw [fP x hp, gQ _ (eP.mapsTo hp)]; exact eP.leftInvOn hp
            have ri : RightInvOn g f (B ∪ Q) := by
              intro x hx
              rcases hx with hb | hq
              · rw [gB x hb, fA _ (eA.mapsTo_invFun hb)]; exact eA.rightInvOn hb
              · rw [gQ x hq, fP _ (eP.mapsTo_invFun hq)]; exact eP.rightInvOn hq
            have imA : f '' A = B := by
              calc
                f '' A = eA.toFun '' A := image_congr fA
                _ = B := eA.image_eq
            have imP : f '' P = Q := by
              calc
                f '' P = eP.toFun '' P := image_congr fP
                _ = Q := eP.image_eq
            refine ⟨{ toFun := f
                      invFun := g
                      continuousOn_toFun := fc
                      continuousOn_invFun := gc
                      leftInvOn := li
                      rightInvOn := ri
                      image_eq := ?_
                      map_left := ?_
                      map_right := ?_ }, ?_, imA, fA, imP⟩
            · rw [image_union, imA, imP]
            · exact (fA _ hA.left_mem).trans eA.map_left
            · exact (fP _ hP.right_mem).trans eP.map_right
            · exact (fA _ hA.right_mem).trans eA.map_right
          let x := cornerNE
          let y := cornerSW
          have hx : x ∈ modelCurve := cornerNE_mem_modelCurve
          have hy : y ∈ modelCurve := by
            norm_num [y,modelCurve,cornerSW,Plane.mk,Plane.supNorm]
          have hyx : y ≠ x := isArcBetween_upperSides.ne.symm
          have hp : p ∈ Plane.openSquare 0 1 := hAi hA.left_mem
          obtain ⟨P,hP,hAP,hPi⟩ := tail isJordanCurve_modelCurve hA
            (by simpa only [inside_modelCurve] using hAi) hx
          obtain ⟨Q,hQ,hBQ,hQi⟩ := tail isJordanCurve_modelCurve hB
            (by simpa only [inside_modelCurve] using hBi) hx
          have hPA : P ∩ A = {q} := by rw [inter_comm,hAP]
          have hQB : Q ∩ B = {q} := by rw [inter_comm,hBQ]
          have hU : IsArcBetween (P∪A) x p := hP.reverse.concatenate hA.reverse (by
            intro z hzP hzA
            simpa using (show z ∈ ({q}:Set Plane) from hPA ▸ ⟨hzP,hzA⟩))
          have hV : IsArcBetween (Q∪B) x p := hQ.reverse.concatenate hB.reverse (by
            intro z hzQ hzB
            simpa using (show z ∈ ({q}:Set Plane) from hQB ▸ ⟨hzQ,hzB⟩))
          obtain ⟨eP⟩ := exists_arcHomeo hP.reverse hQ.reverse
          obtain ⟨g,hgq,hgP,hgOn,hgA⟩ := glue hP.reverse hA.reverse hQ.reverse hB.reverse hPA hQB eP
          have hUi : (P∪A) \ {x} ⊆ Plane.openSquare 0 1 := by
            rintro z ⟨hz,hn⟩
            rcases hz with hzP | hzA
            · simpa only [inside_modelCurve] using hPi ⟨hzP,hn⟩
            · exact hAi hzA
          have hVi : (Q∪B) \ {x} ⊆ Plane.openSquare 0 1 := by
            rintro z ⟨hz,hn⟩
            rcases hz with hzQ | hzB
            · simpa only [inside_modelCurve] using hQi ⟨hzQ,hn⟩
            · exact hBi hzB
          obtain ⟨H,hHOn,hHout,hHp⟩ := properIso hU hV hx hy hyx hp hUi hVi g
          refine ⟨H,?_,hHout,hHp,?_⟩
          · exact (image_congr (fun z hz => hHOn (Or.inr hz))).trans hgA
          · exact (hHOn (Or.inr hA.right_mem)).trans hgq
        have trackCorrection (γ : C(Interval,ℂ)) (q : ℂ) (L R : ℝ)
            (hq : q ≠ 0) (hγ : ∀t,γ t ≠ 0)
            (hγ0 : γ 0 = q) (hγ1 : γ 1 = q)
            (hLR : L<R) (htrack : ∀t, ‖γ t‖ ≤ L) :
            ∃ J : AmbientIsotopy ℂ,
              (∀ t, J.map (t,0) = 0) ∧
              (∀ t, J.map (t,γ t) = q) ∧
              (∀ z, ‖z‖ ≤ L → J.finalMap z = z) ∧
              (∀ t z, R ≤ ‖z‖ → J.map (t,z) = z) := by
          classical
          have logLift (γ : C(Interval, ℂ)) (q : ℂ) (hq : q ≠ 0)
              (hγ : ∀ t, γ t ≠ 0) (hzero : γ 0 = q) :
              ∃ L : C(Interval, ℂ), L 0 = 0 ∧ ∀ t, Complex.exp (L t) = q / γ t := by
            let δ : C(Interval, {z : ℂ // z ≠ 0}) :=
              ⟨fun t => ⟨q / γ t, div_ne_zero hq (hγ t)⟩,
                (continuous_const.div γ.continuous hγ).subtype_mk _⟩
            have hd : δ 0 = ⟨Complex.exp 0, Complex.exp_ne_zero 0⟩ := by
              apply Subtype.ext
              simp [δ,hzero,hq]
            obtain ⟨L,hL,hL0⟩ := Complex.isCoveringMap_exp.exists_path_lifts δ 0 hd
            refine ⟨L,hL0,?_⟩
            intro t
            exact congrArg Subtype.val (congrFun hL t)

          have angular (θ : C(Interval, ℝ)) (χ : C(ℝ, ℝ))
              (hθ0 : θ 0 = 0) (R L : ℝ)
              (hout : ∀ r, R ≤ r → χ r = 0)
              (hin : ∀ r, r ≤ L → χ r = 1)
              (hθ1 : Complex.exp ((θ 1 : ℂ) * Complex.I) = 1) :
              ∃ H : AmbientIsotopy ℂ,
                (∀ t z, H.map (t,z) = Complex.exp (((θ t * χ ‖z‖ : ℝ) : ℂ) * Complex.I) * z) ∧
                (∀ t, H.map (t,0) = 0) ∧
                (∀ t z, R ≤ ‖z‖ → H.map (t,z) = z) ∧
                (∀ z, ‖z‖ ≤ L → H.finalMap z = z) := by
            let f : Interval × ℂ → ℂ := fun w =>
              Complex.exp (((θ w.1 * χ ‖w.2‖ : ℝ) : ℂ) * Complex.I) * w.2
            let g : Interval × ℂ → ℂ := fun w =>
              Complex.exp (-(((θ w.1 * χ ‖w.2‖ : ℝ) : ℂ) * Complex.I)) * w.2
            have hn (a : ℝ) : ‖Complex.exp ((a : ℂ) * Complex.I)‖ = 1 := by
              rw [Complex.norm_exp]
              simp
            have hfn (t : Interval) (z : ℂ) : ‖f (t,z)‖ = ‖z‖ := by
              dsimp [f]
              rw [norm_mul,hn,one_mul]
            have hgn (t : Interval) (z : ℂ) : ‖g (t,z)‖ = ‖z‖ := by
              dsimp [g]
              rw [norm_mul,Complex.norm_exp]
              simp
            have hgf (t : Interval) (z : ℂ) : g (t,f (t,z)) = z := by
              dsimp only [g]
              rw [hfn]
              dsimp only [f]
              rw [← mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,one_mul]
            have hfg (t : Interval) (z : ℂ) : f (t,g (t,z)) = z := by
              dsimp only [f]
              rw [hgn]
              dsimp only [g]
              rw [← mul_assoc,← Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul]
            have hfc : Continuous f := by dsimp [f]; fun_prop
            have hgc : Continuous g := by dsimp [g]; fun_prop
            let H : AmbientIsotopy ℂ := {
              map := ⟨f,hfc⟩
              homeomorphism_at := fun t => ⟨{
                toFun := fun z => f (t,z)
                invFun := fun z => g (t,z)
                left_inv := hgf t
                right_inv := hfg t
                continuous_toFun := hfc.comp (continuous_const.prodMk continuous_id)
                continuous_invFun := hgc.comp (continuous_const.prodMk continuous_id)},fun _ => rfl⟩
              at_zero := by intro z; simp [f,hθ0] }
            refine ⟨H,fun _ _ => rfl,?_,?_,?_⟩
            · intro t
              simp [H,f]
            · intro t z hz
              change f (t,z) = z
              simp [f,hout _ hz]
            · intro z hz
              change f (1,z) = z
              simp [f,hin _ hz,hθ1]
          have radial (a : C(Interval, ℝ)) (b R : ℝ)
              (ha : ∀ t, 0 < a t ∧ a t < R) (hb : 0 < b) (hbR : b < R)
              (hzero : a 0 = b) (hone : a 1 = b) :
              ∃ H : AmbientIsotopy ℂ,
                (∀ t, H.map (t,0) = 0) ∧
                (∀ t z, R ≤ ‖z‖ → H.map (t,z) = z) ∧
                (∀ z, H.finalMap z = z) ∧
                (∀ t z, ‖z‖ = a t → H.map (t,z) = (b / a t) • z) := by
            let c : ℝ → ℝ → ℝ → ℝ := fun s v u =>
              if u ≤ R then
                (v + (max s u - s) * (R-v) / (R-s)) / max s u
              else 1
            have low (s v u : ℝ) (hs : 0 < s) (hsR : s < R) (hu : u ≤ s) :
                c s v u = v/s := by
              simp [c,if_pos (hu.trans hsR.le),max_eq_left hu]
            have mid (s v u : ℝ) (hu : s < u) (huR : u ≤ R) :
                c s v u = (v+(u-s)*(R-v)/(R-s))/u := by
              simp [c,huR,max_eq_right hu.le]
            have high (s v u : ℝ) (hu : R < u) : c s v u = 1 := by
              simp [c,not_le.mpr hu]
            have positive (s v u : ℝ) (hs : 0<s) (hsR : s<R)
                (hv : 0<v) (hvR : v<R) (hu : 0≤u) : 0 < c s v u := by
              by_cases hlow : u ≤ s
              · rw [low s v u hs hsR hlow]; positivity
              · have hsu : s<u := lt_of_not_ge hlow
                by_cases hmid : u ≤ R
                · rw [mid s v u hsu hmid]
                  exact div_pos (by positivity) (hs.trans hsu)
                · rw [high s v u (lt_of_not_ge hmid)]; norm_num
            have refl (s u : ℝ) (hs : 0<s) (hsR : s<R) : c s s u = 1 := by
              by_cases hu : u ≤ s
              · rw [low s s u hs hsR hu,div_self hs.ne']
              · have hsu : s<u := lt_of_not_ge hu
                by_cases huR : u≤R
                · rw [mid s s u hsu huR]
                  field_simp [(hs.trans hsu).ne', (sub_pos.mpr hsR).ne']
                  ring
                · rw [high s s u (lt_of_not_ge huR)]
            have inv (s v u : ℝ) (hs : 0<s) (hsR : s<R)
                (hv : 0<v) (hvR : v<R) (hu : 0≤u) :
                c v s (c s v u * u) * c s v u = 1 := by
              by_cases hlow : u ≤ s
              · rw [low s v u hs hsR hlow]
                have hle : v/s*u ≤ v := by
                  rw [div_mul_eq_mul_div]
                  apply (div_le_iff₀ hs).mpr
                  nlinarith
                rw [low v s (v/s*u) hv hvR hle]
                field_simp [hs.ne',hv.ne']
              · have hsu : s<u := lt_of_not_ge hlow
                by_cases hmid : u≤R
                · rw [mid s v u hsu hmid]
                  let w := v+(u-s)*(R-v)/(R-s)
                  have hw : (v+(u-s)*(R-v)/(R-s))/u*u = w := by
                    exact div_mul_cancel₀ _ (hs.trans hsu).ne'
                  rw [hw]
                  have hvw : v<w := by
                    dsimp [w]
                    have := div_pos (mul_pos (sub_pos.mpr hsu) (sub_pos.mpr hvR)) (sub_pos.mpr hsR)
                    linarith
                  have hwR : w≤R := by
                    dsimp [w]
                    have h := (div_le_iff₀ (sub_pos.mpr hsR)).mpr
                      (show (u-s)*(R-v) ≤ (R-v)*(R-s) by nlinarith)
                    linarith
                  rw [mid v s w hvw hwR]
                  have hnum : s+(w-v)*(R-s)/(R-v) = u := by
                    dsimp [w]
                    field_simp [(sub_pos.mpr hsR).ne',(sub_pos.mpr hvR).ne']
                    ring
                  change (s+(w-v)*(R-s)/(R-v))/w * (w/u) = 1
                  rw [hnum]
                  field_simp [(hv.trans hvw).ne',(hs.trans hsu).ne']
                · rw [high s v u (lt_of_not_ge hmid),one_mul,
                    high v s u (lt_of_not_ge hmid),mul_one]
            have joint (a : C(Interval,ℝ)) (b : ℝ)
                (ha : ∀t,0<a t ∧ a t<R) :
                Continuous (fun w : Interval × ℂ => c (a w.1) b ‖w.2‖) := by
              have hca : Continuous (fun w : Interval × ℂ => a w.1) := a.continuous.comp continuous_fst
              have hcn : Continuous (fun w : Interval × ℂ => ‖w.2‖) := continuous_norm.comp continuous_snd
              have hm := hca.max hcn
              have hc : Continuous (fun w : Interval × ℂ =>
                  (b+(max (a w.1) ‖w.2‖-a w.1)*(R-b)/(R-a w.1)) /
                    max (a w.1) ‖w.2‖) :=
                (continuous_const.add (((hm.sub hca).mul continuous_const).div
                  (continuous_const.sub hca) (fun w => (sub_pos.mpr (ha _).2).ne'))).div hm
                  (fun w => (lt_of_lt_of_le (ha _).1 (le_max_left _ _)).ne')
              exact hc.if_le continuous_const (continuous_norm.comp continuous_snd) continuous_const (by
                intro w hw
                have he : max (a w.1) ‖w.2‖ = R := by rw [hw,max_eq_right (ha _).2.le]
                rw [he]
                field_simp [(sub_pos.mpr (ha w.1).2).ne',((ha w.1).1.trans (ha w.1).2).ne']
                ring)
            let f : Interval × ℂ → ℂ := fun w => c (a w.1) b ‖w.2‖ • w.2
            let g : Interval × ℂ → ℂ := fun w => c b (a w.1) ‖w.2‖ • w.2
            have hc : Continuous (fun w : Interval × ℂ => c b (a w.1) ‖w.2‖) := by
              have hca : Continuous (fun w : Interval × ℂ => a w.1) := a.continuous.comp continuous_fst
              have hcn : Continuous (fun w : Interval × ℂ => ‖w.2‖) := continuous_norm.comp continuous_snd
              have hm : Continuous (fun w : Interval × ℂ => max b ‖w.2‖) := continuous_const.max hcn
              have hc' : Continuous (fun w : Interval × ℂ =>
                  (a w.1+(max b ‖w.2‖-b)*(R-a w.1)/(R-b)) / max b ‖w.2‖) :=
                (hca.add (((hm.sub continuous_const).mul (continuous_const.sub hca)).div_const _)).div hm
                  (fun w => (lt_of_lt_of_le hb (le_max_left _ _)).ne')
              exact hc'.if_le continuous_const (continuous_norm.comp continuous_snd) continuous_const (by
                intro w hw
                have he : max b ‖w.2‖ = R := by rw [hw,max_eq_right hbR.le]
                rw [he]
                field_simp [(sub_pos.mpr hbR).ne',(hb.trans hbR).ne']
                ring)
            have hfc : Continuous f := (joint a b ha).smul continuous_snd
            have hgc : Continuous g := hc.smul continuous_snd
            have gf (t : Interval) (z : ℂ) : g (t,f (t,z)) = z := by
              change c b (a t) ‖c (a t) b ‖z‖ • z‖ • (c (a t) b ‖z‖ • z) = z
              rw [norm_smul,Real.norm_eq_abs,abs_of_pos (positive _ _ _ (ha t).1 (ha t).2 hb hbR (norm_nonneg z)),smul_smul,
                inv _ _ _ (ha t).1 (ha t).2 hb hbR (norm_nonneg z),one_smul]
            have fg (t : Interval) (z : ℂ) : f (t,g (t,z)) = z := by
              change c (a t) b ‖c b (a t) ‖z‖ • z‖ • (c b (a t) ‖z‖ • z) = z
              rw [norm_smul,Real.norm_eq_abs,abs_of_pos (positive _ _ _ hb hbR (ha t).1 (ha t).2 (norm_nonneg z)),smul_smul,
                inv _ _ _ hb hbR (ha t).1 (ha t).2 (norm_nonneg z),one_smul]
            let H : AmbientIsotopy ℂ := {
              map := ⟨f,hfc⟩
              homeomorphism_at := fun t => ⟨{
                toFun := fun z => f (t,z)
                invFun := fun z => g (t,z)
                left_inv := gf t
                right_inv := fg t
                continuous_toFun := hfc.comp (continuous_const.prodMk continuous_id)
                continuous_invFun := hgc.comp (continuous_const.prodMk continuous_id)},fun _ => rfl⟩
              at_zero := by
                intro z
                change c (a 0) b ‖z‖ • z = z
                rw [hzero,refl b ‖z‖ hb hbR,one_smul] }
            refine ⟨H,?_,?_,?_,?_⟩
            · intro t
              change c (a t) b ‖(0:ℂ)‖ • (0:ℂ) = 0
              exact smul_zero _
            · intro t z hz
              change c (a t) b ‖z‖ • z = z
              rcases eq_or_lt_of_le hz with hz | hz
              · rw [← hz]
                simp only [c,if_pos (le_refl R),max_eq_right (ha t).2.le]
                have he : b+(R-a t)*(R-b)/(R-a t) = R := by
                  field_simp [(sub_pos.mpr (ha t).2).ne']; ring
                rw [he,div_self (hb.trans hbR).ne',one_smul]
              · rw [high _ _ _ hz,one_smul]
            · intro z
              change c (a 1) b ‖z‖ • z = z
              rw [hone,refl b ‖z‖ hb hbR,one_smul]
            · intro t z hz
              change c (a t) b ‖z‖ • z = _
              rw [low _ _ _ (ha t).1 (ha t).2 hz.le]
          obtain ⟨ℓ,hℓ0,hℓ⟩ := logLift γ q hq hγ hγ0
          let θ : C(Interval,ℝ) := ⟨fun t => (ℓ t).im, Complex.continuous_im.comp ℓ.continuous⟩
          let a : C(Interval,ℝ) := ⟨fun t => ‖γ t‖,continuous_norm.comp γ.continuous⟩
          let b := ‖q‖
          have hb : 0 < b := norm_pos_iff.mpr hq
          have hbL : b ≤ L := by
            change ‖q‖ ≤ L
            rw [← hγ0]
            exact htrack 0
          have hbR : b < R := hbL.trans_lt hLR
          have ha (t : Interval) : 0<a t ∧ a t<R :=
            ⟨norm_pos_iff.mpr (hγ t),(htrack t).trans_lt hLR⟩
          have hθ0 : θ 0 = 0 := by simp [θ,hℓ0]
          have hs (t : Interval) : Real.exp (ℓ t).re = b/a t := by
            change Real.exp (ℓ t).re = ‖q‖ / ‖γ t‖
            simpa only [Complex.norm_exp,norm_div] using congrArg norm (hℓ t)
          have decomp (z : ℂ) : Complex.exp z =
              (Real.exp z.re : ℂ)*Complex.exp ((z.im : ℂ)*Complex.I) := by
            rw [Complex.ofReal_exp,← Complex.exp_add,Complex.re_add_im]
          have hθ1 : Complex.exp ((θ 1 : ℂ)*Complex.I) = 1 := by
            have hnorm : Real.exp (ℓ 1).re = 1 := by
              rw [hs]
              change ‖q‖ / ‖γ 1‖ = 1
              rw [hγ1,div_self (norm_ne_zero_iff.mpr hq)]
            have he : Complex.exp (ℓ 1) = 1 := by rw [hℓ,hγ1,div_self hq]
            rw [decomp,hnorm,Complex.ofReal_one,one_mul] at he
            exact he
          let χ : C(ℝ,ℝ) := ⟨fun r => min 1 (max 0 ((R-r)/(R-L))),by fun_prop⟩
          have hout (r : ℝ) (hr : R≤r) : χ r = 0 := by
            have hdiv : (R-r)/(R-L) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
              (sub_nonpos.mpr hr) (sub_pos.mpr hLR).le
            simp [χ,max_eq_left hdiv]
          have hin (r : ℝ) (hr : r≤L) : χ r = 1 := by
            have hdiv : 1≤(R-r)/(R-L) := (le_div_iff₀ (sub_pos.mpr hLR)).mpr (by linarith)
            dsimp [χ]
            rw [max_eq_right (zero_le_one.trans hdiv),min_eq_left hdiv]
          obtain ⟨P,hP,hP0,hPout,hPfinal⟩ := angular θ χ hθ0 R L hout hin hθ1
          obtain ⟨Q,hQ0,hQout,hQfinal,hQ⟩ := radial a b R ha hb hbR
            (by simp [a,b,hγ0]) (by simp [a,b,hγ1])
          let J := Q.compose P
          have hcorrect (t : Interval) : P.map (t,Q.map (t,γ t)) = q := by
            rw [hQ t (γ t) rfl,hP]
            have hn : ‖(b/a t) • γ t‖ = b := by
              rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hb (ha t).1)]
              change b/a t * a t = b
              exact div_mul_cancel₀ _ (ha t).1.ne'
            rw [hn,hin b hbL,mul_one]
            rw [Complex.real_smul]
            change Complex.exp (((ℓ t).im : ℂ)*Complex.I) * (((b/a t : ℝ) : ℂ)*γ t) = q
            have he : Complex.exp (((ℓ t).im : ℂ)*Complex.I)*((b/a t : ℝ) : ℂ) = Complex.exp (ℓ t) := by
              rw [decomp (ℓ t),hs,mul_comm]
            rw [← mul_assoc,he,hℓ,div_mul_cancel₀ _ (hγ t)]
          refine ⟨J,?_,hcorrect,?_,?_⟩
          · intro t
            change P.map (t,Q.map (t,0)) = 0
            rw [hQ0,hP0]
          · intro z hz
            change P.finalMap (Q.finalMap z) = z
            rw [hQfinal]
            exact hPfinal z hz
          · intro t z hz
            change P.map (t,Q.map (t,z)) = z
            rw [hQout t z hz,hPout t z hz]
        have squareBoth {A B : Set Plane} {p q : Plane}
            (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
            (hAi : A ⊆ Plane.openSquare 0 1) (hBi : B ⊆ Plane.openSquare 0 1) :
            ∃ H : AmbientIsotopy Plane, H.finalMap '' A = B ∧
              (∀ t z, z ∉ Plane.openSquare 0 1 → H.map (t,z) = z) ∧
              (∀ t, H.map (t,p) = p) ∧ (∀ t, H.map (t,q) = q) := by
          obtain ⟨H,hHA,hHout,hHp,hHq⟩ := onePoint hA hB hAi hBi
          let U := Plane.openSquare 0 1
          have hp : p ∈ U := hAi hA.left_mem
          have hq : q ∈ U := hAi hA.right_mem
          have hin (t : Interval) (x : U) : H.map (t,x.val) ∈ U := by
            by_contra hn
            obtain ⟨e,he⟩ := H.homeomorphism_at t
            have hh : H.map (t,H.map (t,x.val)) = H.map (t,x.val) := hHout t _ hn
            have hx : H.map (t,x.val) = x.val := e.injective (by simpa only [he] using hh)
            exact hn (hx.symm ▸ x.property)
          obtain ⟨d⟩ := disc isJordanCurve_modelCurve
          let dU : Plane ≃ₜ U := d.trans (Homeomorph.setCongr inside_modelCurve)
          let CP : ℂ ≃ₜ Plane := Complex.equivRealProdCLM.toHomeomorph |>.trans
            (Homeomorph.finTwoArrow (X := ℝ)).symm |>.trans
              (EuclideanSpace.equiv (Fin 2) ℝ).symm.toHomeomorph
          let e0 : U ≃ₜ ℂ := dU.symm.trans CP.symm
          let o : ℂ := e0 ⟨p,hp⟩
          let shift : ℂ ≃ₜ ℂ := {
            toFun := fun z => z-o
            invFun := fun z => z+o
            left_inv := by intro z; simp
            right_inv := by intro z; simp
            continuous_toFun := continuous_id.sub continuous_const
            continuous_invFun := continuous_id.add continuous_const }
          let e : U ≃ₜ ℂ := e0.trans shift
          have ep : e ⟨p,hp⟩ = 0 := by simp [e,shift,o]
          let q' := e ⟨q,hq⟩
          have hq' : q' ≠ 0 := by
            intro he
            have hh : (⟨q,hq⟩ : U) = ⟨p,hp⟩ := e.injective (he.trans ep.symm)
            exact hA.ne (congrArg Subtype.val hh).symm
          let γ : C(Interval,ℂ) := ⟨fun t => e ⟨H.map (t,q),hin t ⟨q,hq⟩⟩,
            e.continuous.comp ((H.map.continuous.comp
              (continuous_id.prodMk continuous_const)).subtype_mk _)⟩
          have hγ (t : Interval) : γ t ≠ 0 := by
            intro heq
            have he : (⟨H.map (t,q),hin t ⟨q,hq⟩⟩ : U) = ⟨p,hp⟩ :=
              e.injective (heq.trans ep.symm)
            obtain ⟨h,hh⟩ := H.homeomorphism_at t
            have hval : H.map (t,q) = p := congrArg Subtype.val he
            have hqp : q=p := h.injective (by rw [hh,hh,hHp]; exact hval)
            exact hA.ne hqp.symm
          have hγ0 : γ 0 = q' := by apply congrArg e; apply Subtype.ext; exact H.at_zero q
          have hγ1 : γ 1 = q' := by apply congrArg e; apply Subtype.ext; exact hHq
          obtain ⟨b,hbc,hbi,hBimage,hb0,hb1⟩ := hB
          let β : C(Interval,ℂ) := ⟨fun t => e ⟨b t.val,hBi (hBimage ▸ ⟨t.val,t.property,rfl⟩)⟩,
            e.continuous.comp ((continuousOn_iff_continuous_restrict.mp hbc).subtype_mk _)⟩
          have hcompact : IsCompact (range γ ∪ range β) :=
            (isCompact_range γ.continuous).union (isCompact_range β.continuous)
          obtain ⟨L,hL⟩ := Metric.isBounded_iff_subset_ball (0:ℂ) |>.mp hcompact.isBounded
          have htrack (t : Interval) : ‖γ t‖ ≤ L := by
            have hl := hL (Or.inl (mem_range_self t))
            exact (show ‖γ t‖ < L by simpa using hl).le
          have hBbound (z : U) (hz : z.val ∈ B) : ‖e z‖ ≤ L := by
            obtain ⟨t,ht,he⟩ := hBimage.symm ▸ hz
            have hβ : β ⟨t,ht⟩ = e z := by apply congrArg e; apply Subtype.ext; exact he
            have hl := hL (Or.inr (mem_range_self (⟨t,ht⟩ : Interval)))
            rw [hβ] at hl
            exact (show ‖e z‖ < L by simpa using hl).le
          let R := L+1
          obtain ⟨J,hJ0,hJq,hJfinal,hJout⟩ := trackCorrection γ q' L R hq' hγ hγ0 hγ1
            (by dsimp [R]; linarith) htrack
          obtain ⟨K,hKcoord⟩ := conjugate e J
          let j : ℂ → Plane := fun z => (e.symm z).val
          let V : Set Plane := j '' Metric.closedBall 0 R
          have hj : Continuous j := continuous_subtype_val.comp e.symm.continuous
          have hV : IsClosed V := ((isCompact_closedBall (0:ℂ) R).image hj).isClosed
          have hVU : V ⊆ U := by rintro z ⟨w,hw,rfl⟩; exact (e.symm w).property
          have hKfix : ∀ t (z : U), z.val ∉ V → (K.map (t,z) : Plane) = z.val := by
            intro t z hz
            have hnorm : R ≤ ‖e z‖ := by
              by_contra hn
              apply hz
              refine ⟨e z,?_,?_⟩
              · simpa using (le_of_lt (lt_of_not_ge hn))
              · exact congrArg Subtype.val (e.symm_apply_apply z)
            rw [hKcoord,hJout t (e z) hnorm,e.symm_apply_apply]
          obtain ⟨G,hGcoord,hGfix⟩ := extend U V (Plane.isOpen_openSquare 0 1) hV hVU K hKfix
          have hGout : ∀ t z, z ∉ U → G.map (t,z) = z := by
            intro t z hz
            exact hGfix t z (fun hv => hz (hVU hv))
          have hGp (t : Interval) : G.map (t,p) = p := by
            rw [hGcoord t ⟨p,hp⟩,hKcoord,ep,hJ0]
            have he : e.symm 0 = ⟨p,hp⟩ := by rw [← ep,e.symm_apply_apply]
            exact congrArg Subtype.val he
          have hGq (t : Interval) : G.map (t,H.map (t,q)) = q := by
            rw [hGcoord t ⟨H.map (t,q),hin t ⟨q,hq⟩⟩,hKcoord]
            change (e.symm (J.map (t,γ t)) : Plane) = q
            rw [hJq]
            exact congrArg Subtype.val (e.symm_apply_apply ⟨q,hq⟩)
          have hGB (z : Plane) (hz : z ∈ B) : G.finalMap z = z := by
            have hzu : z ∈ U := hBi hz
            change G.map (1,z) = z
            rw [hGcoord 1 ⟨z,hzu⟩,hKcoord]
            change (e.symm (J.finalMap (e ⟨z,hzu⟩)) : Plane) = z
            rw [hJfinal _ (hBbound ⟨z,hzu⟩ hz),e.symm_apply_apply]
          let F := H.compose G
          refine ⟨F,?_,?_,?_,hGq⟩
          · change (G.finalMap ∘ H.finalMap) '' A = B
            have him : (G.finalMap ∘ H.finalMap) '' A = G.finalMap '' (H.finalMap '' A) := by
              rw [image_image]; rfl
            rw [him,hHA]
            exact (image_congr hGB).trans (image_id B)
          · intro t z hz
            change G.map (t,H.map (t,z)) = z
            rw [hHout t z hz,hGout t z hz]
          · intro t
            change G.map (t,H.map (t,p)) = p
            rw [hHp,hGp]
        obtain ⟨F,hFD,hFI⟩ := straight hD
        have hFA : IsArcBetween (F '' A) (F p) (F q) :=
          hA.image_of_injOn (subset_univ _) F.continuous.continuousOn F.injective.injOn
        have hFB : IsArcBetween (F '' B) (F p) (F q) :=
          hB.image_of_injOn (subset_univ _) F.continuous.continuousOn F.injective.injOn
        have hFAi : F '' A ⊆ Plane.openSquare 0 1 := hFI ▸ image_mono hAi
        have hFBi : F '' B ⊆ Plane.openSquare 0 1 := hFI ▸ image_mono hBi
        obtain ⟨H,hHA,hHout,hHp,hHq⟩ := squareBoth hFA hFB hFAi hFBi
        obtain ⟨K,hK⟩ := conjugate F H
        have hfinal : K.finalMap = F.symm ∘ H.finalMap ∘ F := funext (hK 1)
        have hInv (X : Set Plane) : F.symm '' (F '' X) = X := by
          rw [image_image]
          change (F.symm ∘ F) '' X = X
          have he : F.symm ∘ F = id := funext F.symm_apply_apply
          rw [he,image_id]
        refine ⟨K,?_,?_,?_,?_⟩
        · rw [hfinal]
          have he : (F.symm ∘ H.finalMap ∘ F) '' A = F.symm '' (H.finalMap '' (F '' A)) := by
            rw [image_image,image_image]; rfl
          rw [he,hHA,hInv]
        · intro t z hz
          rw [hK]
          have hout : F z ∉ Plane.openSquare 0 1 := by
            intro hin
            obtain ⟨u,hu,he⟩ := hFI.symm ▸ hin
            exact hz (F.injective he ▸ hu)
          rw [hHout t (F z) hout,F.symm_apply_apply]
        · intro t; rw [hK,hHp,F.symm_apply_apply]
        · intro t; rw [hK,hHq,F.symm_apply_apply]
    obtain ⟨H,hHA,hout,hp,hq⟩ := planarInteriorPair hC hA hB hq0 hq1 hAi hBi
    let J : Plane ≃ₜ range f := hf.isEmbedding.toHomeomorph
    let e : range f ≃ₜ (univ : Set Plane) := J.symm.trans (Homeomorph.Set.univ Plane).symm
    have he (u : range f) : (e u : Plane) = J.symm u := rfl
    have hJ (u : range f) : f (J.symm u) = u.val := congrArg Subtype.val (J.apply_symm_apply u)
    let Kclosed := closure (inside C)
    have hKcompact : IsCompact Kclosed :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure
        (jordan_curve_theorem hC).isBounded_inside.closure
    have hfix : ∀ t z, z ∉ Kclosed → H.map (t,z) = z := by
      intro t z hz
      exact hout t z (fun hin => hz (subset_closure hin))
    obtain ⟨K,G,hcoord,hGU,hGout⟩ := CurveComplex.position_surface_chart_lift S (range f) univ
      hf.isOpenMap.isOpen_range e Kclosed hKcompact (subset_univ _) H hfix
    apply Quotient.sound
    refine ⟨G,?_,?_⟩
    · intro t z hz
      by_cases hrange : z ∈ range f
      · let u : range f := ⟨z,hrange⟩
        have hK : K.map (t,u) = u := by
          apply e.injective
          apply Subtype.ext
          have hc := hcoord t u
          have hfixed : H.map (t,(e u : Plane)) = (e u : Plane) := by
            by_cases hin : (e u : Plane) ∈ inside C
            · have hm : f (e u : Plane) ∈ M.cover.branch := by rw [he,hJ]; exact hz
              rcases hmarks _ hin hm with hz0 | hz1
              · rw [hz0,hp]
              · rw [hz1,hq]
            · exact hout t _ hin
          exact hc.trans hfixed
        exact (hGU t u).trans (congrArg Subtype.val hK)
      · exact hGout t z hrange
    · rw [haImage,hbImage]
      ext z
      constructor
      · rintro ⟨w,⟨t,ht,rfl⟩,hw⟩
        let u : range f := J t
        refine ⟨(e (K.finalMap u) : Plane),?_,?_⟩
        · have hc := hcoord (1 : Interval) u
          change (e (K.finalMap u) : Plane) = H.finalMap (e u : Plane) at hc
          have heu : (e u : Plane) = t := by simp [he,u]
          rw [hc,heu]
          exact hHA ▸ mem_image_of_mem H.finalMap ht
        · rw [he,hJ]
          exact (hGU (1 : Interval) u).symm.trans hw
      · rintro ⟨t,ht,rfl⟩
        obtain ⟨z,hz,hzt⟩ := (show t ∈ H.finalMap '' A from hHA.symm ▸ ht)
        let u : range f := J z
        let v : range f := J t
        have heu : (e u : Plane) = z := by simp [he,u]
        have hev : (e v : Plane) = t := by simp [he,v]
        have hKv : K.finalMap u = v := by
          apply e.injective
          apply Subtype.ext
          have hc := hcoord (1 : Interval) u
          change (e (K.finalMap u) : Plane) = H.finalMap (e u : Plane) at hc
          rw [hc,heu,hzt,hev]
        refine ⟨f z,mem_image_of_mem f hz,?_⟩
        change G.map ((1 : Interval),u.val) = v.val
        rw [hGU]
        exact congrArg Subtype.val hKv
  have noInteriorPair : ∀ w ∈ τ, classEndpoints M w ≠ {f q0,f q1} := by
    intro w hw he
    let b := r ⟨w,Finset.mem_union_right _ hw⟩
    have hbw : Quotient.mk (essentialArcSetoid M) b = w := hr _
    have hbEnds : markedArcEndset b.val = {f q0,f q1} :=
      ((markedArcEndset_eq_classEndpoints M b).trans
        (congrArg (classEndpoints M) hbw)).trans he
    have hdT : ∀ z, Disjoint (arcInterior M b) (arcInterior M (rT z)) := by
      intro z
      rw [← hrestrict z]
      apply hd
      intro hz
      have hzw : w = z.val := congrArg Subtype.val hz
      exact Finset.disjoint_left.mp hτ.1 z.property (hzw ▸ hw)
    have hwv : w = v := hbw.symm.trans (twoMarkClass b hbEnds (contained b hbEnds hdT))
    exact hvτ (hwv ▸ hw)
  have faceFour : ∃ (x y : S) (H : Finset {w // w ∈ τ}),
      H = Finset.univ.filter (fun w =>
        (arcInterior M (r ⟨w.val,Finset.mem_union_right _ w.property⟩) ∩ U).Nonempty) ∧
      x ∈ M.cover.branch ∧ y ∈ M.cover.branch ∧ x ∉ U ∧ y ∉ U ∧ H.card ≤ 4 ∧
      ∀ w ∈ H, classEndpoints M w.val ∈
        ({ {f q0,x}, {f q0,y}, {f q1,x}, {f q1,y} } : Finset (Finset S)) := by
    obtain ⟨x,y,H,hH,hxB,hyB,hxout,hyout,hcard,hmembers⟩ := faceFive
    let P : Finset (Finset S) := {{f q0,x}, {f q0,y}, {f q1,x}, {f q1,y}}
    let L : {w // w ∈ τ} → Finset S := fun w => classEndpoints M w.val
    have members : ∀ w ∈ H, L w ∈ P := by
      intro w hw
      have hm := hmembers w hw
      exact (Finset.mem_insert.mp hm).resolve_left (noInteriorPair w.val w.property)
    have sub : H.image L ⊆ P := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      exact members w hw
    have inj : Set.InjOn L (H : Set {w // w ∈ τ}) := by
      intro w hw z hz he
      exact Subtype.ext (labelUnique w.val w.property z.val z.property he)
    have hPcard : P.card ≤ 4 := by
      have h1 := Finset.card_insert_le ({f q0,x} : Finset S)
        ({ {f q0,y}, {f q1,x}, {f q1,y} } : Finset (Finset S))
      have h2 := Finset.card_insert_le ({f q0,y} : Finset S)
        ({ {f q1,x}, {f q1,y} } : Finset (Finset S))
      have h3 := Finset.card_insert_le ({f q1,x} : Finset S)
        ({ {f q1,y} } : Finset (Finset S))
      simp only [Finset.card_singleton] at h3
      dsimp only [P]
      omega
    have hHcard : H.card ≤ 4 := by
      calc
        H.card = (H.image L).card := (Finset.card_image_of_injOn inj).symm
        _ ≤ P.card := Finset.card_le_card sub
        _ ≤ 4 := hPcard
    exact ⟨x,y,H,hH,hxB,hyB,hxout,hyout,hHcard,members⟩
  have hsimplex : IsArcSimplex M (insert v (T.val ∪ τ)) := by
    have old : IsArcSimplex M (T.val ∪ τ) := ⟨r,hr,hd⟩
    by_cases hv : v ∈ T.val ∪ τ
    · simpa only [Finset.insert_eq_of_mem hv] using old
    obtain ⟨x,y,H,hH,hxB,hyB,hxout,hyout,hHcard,hmembers⟩ := faceFour
    -- Obligation 2 now involves only at most FOUR original face spokes.
    obtain ⟨b,hbEnds,hbU,hdbH⟩ : ∃ b : EssentialMarkedArc M,
        markedArcEndset b.val = {f q0,f q1} ∧ b.val.image ⊆ U ∧
        ∀ w ∈ H, Disjoint (arcInterior M b)
          (arcInterior M (r ⟨w.val,Finset.mem_union_right _ w.property⟩)) := by
      by_cases hHempty : H = ∅
      · refine ⟨a,ends,haIn,?_⟩
        intro w hw
        rw [hHempty] at hw
        simpa using hw
      · by_cases hHone : H.card = 1
        · obtain ⟨w,hwEq⟩ := Finset.card_eq_one.mp hHone
          have hwH : w ∈ H := hwEq.symm ▸ Finset.mem_singleton_self w
          let b₀ := r ⟨w.val,Finset.mem_union_right _ w.property⟩
          have hb₀Class : Quotient.mk (essentialArcSetoid M) b₀ = w.val := hr _
          have hdT : ∀ z, Disjoint (arcInterior M b₀) (arcInterior M (rT z)) := by
            intro z
            rw [← hrestrict z]
            apply hd
            intro he
            have hz : w.val = z.val := congrArg Subtype.val he
            exact Finset.disjoint_left.mp hτ.1 z.property (hz ▸ w.property)
          have hit : (arcInterior M b₀ ∩ U).Nonempty := by
            have hwHit := hwH
            rw [hH] at hwHit
            exact (Finset.mem_filter.mp hwHit).2
          obtain ⟨hbIn,hbCl,_⟩ := actual_link_arc_face_has_interior_endpoint
            M p T τ hτ rT hrT O hO U hOU hUG b₀ w.val w.property hb₀Class hdT hit
          have hlabel : markedArcEndset b₀.val = classEndpoints M w.val :=
            (markedArcEndset_eq_classEndpoints M b₀).trans
              (congrArg (classEndpoints M) hb₀Class)
          have hfinish (s : S) (hs : s ∉ U)
              (hend : markedArcEndset b₀.val = {f q0,s} ∨
                markedArcEndset b₀.val = {f q1,s}) :
              ∃ b : EssentialMarkedArc M,
                markedArcEndset b.val = {f q0,f q1} ∧ b.val.image ⊆ U ∧
                ∀ z ∈ H, Disjoint (arcInterior M b)
                  (arcInterior M (r ⟨z.val,Finset.mem_union_right _ z.property⟩)) := by
            obtain ⟨b,hbEnds,hbU,hdb⟩ := singleSpoke b₀ s hs hend hbIn hbCl
            refine ⟨b,hbEnds,hbU,?_⟩
            intro z hz
            rw [hwEq] at hz
            have hzw : z = w := Finset.mem_singleton.mp hz
            simpa only [hzw] using hdb
          have hm := hmembers w hwH
          simp only [Finset.mem_insert,Finset.mem_singleton] at hm
          rcases hm with he | he | he | he
          · exact hfinish x hxout (Or.inl (hlabel.trans he))
          · exact hfinish y hyout (Or.inl (hlabel.trans he))
          · exact hfinish x hxout (Or.inr (hlabel.trans he))
          · exact hfinish y hyout (Or.inr (hlabel.trans he))
        · by_cases hHfour : H.card = 4
          · let L : {w // w ∈ τ} → Finset S := fun w => classEndpoints M w.val
            let P : Finset (Finset S) := {{f q0,x},{f q0,y},{f q1,x},{f q1,y}}
            have sub : H.image L ⊆ P := by
              intro z hz
              obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
              exact hmembers w hw
            have inj : Set.InjOn L (H : Set {w // w ∈ τ}) := by
              intro w hw z hz he
              exact Subtype.ext (labelUnique w.val w.property z.val z.property he)
            have hcardP : P.card ≤ 4 := by
              have h1 := Finset.card_insert_le ({f q0,x} : Finset S)
                ({ {f q0,y}, {f q1,x}, {f q1,y} } : Finset (Finset S))
              have h2 := Finset.card_insert_le ({f q0,y} : Finset S)
                ({ {f q1,x}, {f q1,y} } : Finset (Finset S))
              have h3 := Finset.card_insert_le ({f q1,x} : Finset S)
                ({ {f q1,y} } : Finset (Finset S))
              simp only [Finset.card_singleton] at h3
              dsimp only [P]
              omega
            have hcardIm : (H.image L).card = 4 := by
              rw [Finset.card_image_of_injOn inj,hHfour]
            have imEq : H.image L = P :=
              Finset.eq_of_subset_of_card_le sub (by omega)
            have hxy : x ≠ y := by
              intro he
              have hsmall : P.card ≤ 2 := by
                dsimp only [P]
                rw [he]
                simp only [Finset.insert_idem]
                have h := Finset.card_insert_le ({f q0,y} : Finset S)
                  ({ {f q1,y} } : Finset (Finset S))
                simpa using h
              have hc := congrArg Finset.card imEq
              omega
            obtain ⟨w00,hw00,hl00⟩ := Finset.mem_image.mp
              (imEq.symm ▸ (show ({f q0,x} : Finset S) ∈ P by simp [P]))
            obtain ⟨w01,hw01,hl01⟩ := Finset.mem_image.mp
              (imEq.symm ▸ (show ({f q0,y} : Finset S) ∈ P by simp [P]))
            obtain ⟨w10,hw10,hl10⟩ := Finset.mem_image.mp
              (imEq.symm ▸ (show ({f q1,x} : Finset S) ∈ P by simp [P]))
            obtain ⟨w11,hw11,hl11⟩ := Finset.mem_image.mp
              (imEq.symm ▸ (show ({f q1,y} : Finset S) ∈ P by simp [P]))
            let rτ : {w // w ∈ τ} → EssentialMarkedArc M :=
              fun w => r ⟨w.val,Finset.mem_union_right _ w.property⟩
            have endpoint (w : {w // w ∈ τ}) : markedArcEndset (rτ w).val = L w :=
              (markedArcEndset_eq_classEndpoints M (rτ w)).trans
                (congrArg (classEndpoints M) (hr _))
            have localize (w : {w // w ∈ τ}) (hw : w ∈ H) :
                arcInterior M (rτ w) ⊆ U ∧ (rτ w).val.image ⊆ closure U := by
              have hdT : ∀ z, Disjoint (arcInterior M (rτ w)) (arcInterior M (rT z)) := by
                intro z
                rw [← hrestrict z]
                apply hd
                intro he
                have hz : w.val = z.val := congrArg Subtype.val he
                exact Finset.disjoint_left.mp hτ.1 z.property (hz ▸ w.property)
              have hit : (arcInterior M (rτ w) ∩ U).Nonempty := by
                rw [hH] at hw
                exact (Finset.mem_filter.mp hw).2
              obtain ⟨hi,hc,_⟩ := actual_link_arc_face_has_interior_endpoint
                M p T τ hτ rT hrT O hO U hOU hUG (rτ w) w.val w.property (hr _) hdT hit
              exact ⟨hi,hc⟩
            have labelPair (q r : S) (u v : S) (hq : q ∈ U) (hr : r ∈ U)
                (hu : u ∉ U) (hv : v ∉ U)
                (he : ({q,u} : Finset S) = {r,v}) : q = r ∧ u = v := by
              have hs := congrArg (fun d : Finset S => (d : Set S)) he
              simp only [Finset.coe_insert,Finset.coe_singleton] at hs
              rcases Set.pair_eq_pair_iff.mp hs with h | h
              · exact h
              · exact False.elim (hv (h.1 ▸ hq))
            have disjointPair (w z : {w // w ∈ τ}) (hwz : L w ≠ L z) :
                Disjoint (arcInterior M (rτ w)) (arcInterior M (rτ z)) := by
              apply hd
              intro he
              exact hwz (congrArg (fun k => classEndpoints M k.val) he)
            have d00_01 := disjointPair w00 w01 (by
              rw [hl00,hl01]
              intro he
              exact hxy (labelPair _ _ _ _ hq0U hq0U hxout hyout he).2)
            have d10_11 := disjointPair w10 w11 (by
              rw [hl10,hl11]
              intro he
              exact hxy (labelPair _ _ _ _ hq1U hq1U hxout hyout he).2)
            have differentTips (u v : S) (hu : u ∉ U) (hv : v ∉ U) :
                ({f q0,u} : Finset S) ≠ {f q1,v} := by
              intro he
              exact hfn (labelPair _ _ _ _ hq0U hq1U hu hv he).1
            obtain ⟨i00,c00⟩ := localize w00 hw00
            obtain ⟨i01,c01⟩ := localize w01 hw01
            obtain ⟨i10,c10⟩ := localize w10 hw10
            obtain ⟨i11,c11⟩ := localize w11 hw11
            obtain ⟨b,hbEnds,hbU,hab⟩ := fourActualSpokes (rτ w00) (rτ w01) (rτ w10) (rτ w11)
              x y hxy hxout hyout ((endpoint w00).trans hl00) ((endpoint w01).trans hl01)
              ((endpoint w10).trans hl10) ((endpoint w11).trans hl11)
              i00 c00 i01 c01 i10 c10 i11 c11 d00_01
              (disjointPair w00 w10 (by rw [hl00,hl10]; exact differentTips x x hxout hxout))
              (disjointPair w00 w11 (by rw [hl00,hl11]; exact differentTips x y hxout hyout))
              (disjointPair w01 w10 (by rw [hl01,hl10]; exact differentTips y x hyout hxout))
              (disjointPair w01 w11 (by rw [hl01,hl11]; exact differentTips y y hyout hyout)) d10_11
            refine ⟨b,hbEnds,hbU,?_⟩
            intro w hw
            apply hab
            have hm := hmembers w hw
            simp only [Finset.mem_insert,Finset.mem_singleton] at hm
            rcases hm with he | he | he | he
            · have hew : w = w00 := Subtype.ext (labelUnique w.val w.property w00.val w00.property (he.trans hl00.symm))
              exact Or.inl (congrArg rτ hew)
            · have hew : w = w01 := Subtype.ext (labelUnique w.val w.property w01.val w01.property (he.trans hl01.symm))
              exact Or.inr (Or.inl (congrArg rτ hew))
            · have hew : w = w10 := Subtype.ext (labelUnique w.val w.property w10.val w10.property (he.trans hl10.symm))
              exact Or.inr (Or.inr (Or.inl (congrArg rτ hew)))
            · have hew : w = w11 := Subtype.ext (labelUnique w.val w.property w11.val w11.property (he.trans hl11.symm))
              exact Or.inr (Or.inr (Or.inr (congrArg rτ hew)))
          · by_cases hHthree : H.card = 3
            · let L : {w // w ∈ τ} → Finset S := fun w => classEndpoints M w.val
              let P : Finset (Finset S) := {{f q0,x},{f q0,y},{f q1,x},{f q1,y}}
              have sub : H.image L ⊆ P := by
                intro z hz
                obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
                exact hmembers w hw
              have inj : Set.InjOn L (H : Set {w // w ∈ τ}) := by
                intro w hw z hz he
                exact Subtype.ext (labelUnique w.val w.property z.val z.property he)
              have hcIm : (H.image L).card = 3 := by rw [Finset.card_image_of_injOn inj,hHthree]
              have heFilter : H.image L = P.filter (fun K => K ∈ H.image L) := by
                ext K
                simp only [Finset.mem_filter]
                exact ⟨fun hK => ⟨sub hK,hK⟩,fun hK => hK.2⟩
              have hxy : x ≠ y := by
                intro he
                have hsub2 : H.image L ⊆ ({ {f q0,y},{f q1,y} } : Finset (Finset S)) := by
                  intro K hK
                  have hm := sub hK
                  dsimp only [P] at hm
                  simpa [he] using hm
                have hle := Finset.card_le_card hsub2
                have hsmall := Finset.card_insert_le ({f q0,y} : Finset S)
                  ({ {f q1,y} } : Finset (Finset S))
                simp only [Finset.card_singleton] at hsmall
                omega
              have labelPair (q r : S) (u v : S) (hq : q ∈ U) (hr : r ∈ U)
                  (hu : u ∉ U) (hv : v ∉ U)
                  (he : ({q,u} : Finset S) = {r,v}) : q = r ∧ u = v := by
                have hs := congrArg (fun d : Finset S => (d : Set S)) he
                simp only [Finset.coe_insert,Finset.coe_singleton] at hs
                rcases Set.pair_eq_pair_iff.mp hs with h | h
                · exact h
                · exact False.elim (hv (h.1 ▸ hq))
              have ne00_01 : ({f q0,x} : Finset S) ≠ {f q0,y} :=
                fun he => hxy (labelPair _ _ _ _ hq0U hq0U hxout hyout he).2
              have ne10_11 : ({f q1,x} : Finset S) ≠ {f q1,y} :=
                fun he => hxy (labelPair _ _ _ _ hq1U hq1U hxout hyout he).2
              have differentTips (u v : S) (hu : u ∉ U) (hv : v ∉ U) :
                  ({f q0,u} : Finset S) ≠ {f q1,v} := by
                intro he
                exact hfn (labelPair _ _ _ _ hq0U hq1U hu hv he).1
              have ne00_10 := differentTips x x hxout hxout
              have ne00_11 := differentTips x y hxout hyout
              have ne01_10 := differentTips y x hyout hxout
              have ne01_11 := differentTips y y hyout hyout
              have choose :
                  (({f q0,x} : Finset S) ∈ H.image L ∧ {f q0,y} ∈ H.image L ∧ {f q1,x} ∈ H.image L) ∨
                  (({f q0,y} : Finset S) ∈ H.image L ∧ {f q0,x} ∈ H.image L ∧ {f q1,y} ∈ H.image L) ∨
                  (({f q1,x} : Finset S) ∈ H.image L ∧ {f q1,y} ∈ H.image L ∧ {f q0,x} ∈ H.image L) ∨
                  (({f q1,y} : Finset S) ∈ H.image L ∧ {f q1,x} ∈ H.image L ∧ {f q0,y} ∈ H.image L) := by
                by_cases h00 : ({f q0,x} : Finset S) ∈ H.image L <;>
                  by_cases h01 : ({f q0,y} : Finset S) ∈ H.image L <;>
                  by_cases h10 : ({f q1,x} : Finset S) ∈ H.image L <;>
                  by_cases h11 : ({f q1,y} : Finset S) ∈ H.image L
                all_goals first
                  | exact Or.inl ⟨h00,h01,h10⟩
                  | exact Or.inr (Or.inl ⟨h01,h00,h11⟩)
                  | exact Or.inr (Or.inr (Or.inl ⟨h10,h11,h00⟩))
                  | exact Or.inr (Or.inr (Or.inr ⟨h11,h10,h01⟩))
                  | rw [heFilter] at hcIm
                    simp only [P,Finset.filter_insert,Finset.filter_singleton,h00,h01,h10,h11,
                      ite_true,ite_false] at hcIm
                    simp [ne00_01,ne10_11,ne00_10,ne00_11,ne01_10,ne01_11,
                      Ne.symm ne00_01,Ne.symm ne10_11,Ne.symm ne00_10,
                      Ne.symm ne00_11,Ne.symm ne01_10,Ne.symm ne01_11] at hcIm
              let rτ : {w // w ∈ τ} → EssentialMarkedArc M :=
                fun w => r ⟨w.val,Finset.mem_union_right _ w.property⟩
              have endpoint (w : {w // w ∈ τ}) : markedArcEndset (rτ w).val = L w :=
                (markedArcEndset_eq_classEndpoints M (rτ w)).trans (congrArg (classEndpoints M) (hr _))
              have localize (w : {w // w ∈ τ}) (hw : w ∈ H) :
                  arcInterior M (rτ w) ⊆ U ∧ (rτ w).val.image ⊆ closure U := by
                have hdT : ∀ z, Disjoint (arcInterior M (rτ w)) (arcInterior M (rT z)) := by
                  intro z
                  rw [← hrestrict z]
                  apply hd
                  intro he
                  have hz : w.val = z.val := congrArg Subtype.val he
                  exact Finset.disjoint_left.mp hτ.1 z.property (hz ▸ w.property)
                have hit : (arcInterior M (rτ w) ∩ U).Nonempty := by
                  rw [hH] at hw
                  exact (Finset.mem_filter.mp hw).2
                obtain ⟨hi,hc,_⟩ := actual_link_arc_face_has_interior_endpoint
                  M p T τ hτ rT hrT O hO U hOU hUG (rτ w) w.val w.property (hr _) hdT hit
                exact ⟨hi,hc⟩
              have disjointPair (w z : {w // w ∈ τ}) (hwz : L w ≠ L z) :
                  Disjoint (arcInterior M (rτ w)) (arcInterior M (rτ z)) := by
                apply hd
                intro he
                exact hwz (congrArg (fun k => classEndpoints M k.val) he)
              have finish (w0 w1 w2 : {w // w ∈ τ}) (hw0 : w0 ∈ H) (hw1 : w1 ∈ H) (hw2 : w2 ∈ H)
                  (hn01 : L w0 ≠ L w1) (hn02 : L w0 ≠ L w2) (hn12 : L w1 ≠ L w2)
                  (b : EssentialMarkedArc M) (hbEnds : markedArcEndset b.val = {f q0,f q1}) (hbU : b.val.image ⊆ U)
                  (hd0 : Disjoint (arcInterior M b) (arcInterior M (rτ w0)))
                  (hd1 : Disjoint (arcInterior M b) (arcInterior M (rτ w1)))
                  (hd2 : Disjoint (arcInterior M b) (arcInterior M (rτ w2))) :
                  ∃ b : EssentialMarkedArc M, markedArcEndset b.val = {f q0,f q1} ∧ b.val.image ⊆ U ∧
                    ∀ w ∈ H, Disjoint (arcInterior M b)
                      (arcInterior M (r ⟨w.val,Finset.mem_union_right _ w.property⟩)) := by
                have hn01w : w0 ≠ w1 := fun he => hn01 (congrArg L he)
                have hn02w : w0 ≠ w2 := fun he => hn02 (congrArg L he)
                have hn12w : w1 ≠ w2 := fun he => hn12 (congrArg L he)
                have hcard : ({w0,w1,w2} : Finset {w // w ∈ τ}).card = 3 := by simp [hn01w,hn02w,hn12w]
                have hsub : ({w0,w1,w2} : Finset {w // w ∈ τ}) ⊆ H := by
                  intro w hw
                  simp only [Finset.mem_insert,Finset.mem_singleton] at hw
                  rcases hw with rfl | rfl | rfl <;> assumption
                have heH : ({w0,w1,w2} : Finset {w // w ∈ τ}) = H :=
                  Finset.eq_of_subset_of_card_le hsub (by omega)
                refine ⟨b,hbEnds,hbU,?_⟩
                intro w hw
                rw [← heH] at hw
                simp only [Finset.mem_insert,Finset.mem_singleton] at hw
                rcases hw with rfl | rfl | rfl
                · exact hd0
                · exact hd1
                · exact hd2
              have primary (s t : S) (hs : s ∉ U) (ht : t ∉ U) (hst : s ≠ t)
                  (h0 : ({f q0,s} : Finset S) ∈ H.image L)
                  (h1 : ({f q0,t} : Finset S) ∈ H.image L)
                  (h2 : ({f q1,s} : Finset S) ∈ H.image L) :
                  ∃ b : EssentialMarkedArc M, markedArcEndset b.val = {f q0,f q1} ∧ b.val.image ⊆ U ∧
                    ∀ w ∈ H, Disjoint (arcInterior M b)
                      (arcInterior M (r ⟨w.val,Finset.mem_union_right _ w.property⟩)) := by
                obtain ⟨w0,hw0,he0⟩ := Finset.mem_image.mp h0
                obtain ⟨w1,hw1,he1⟩ := Finset.mem_image.mp h1
                obtain ⟨w2,hw2,he2⟩ := Finset.mem_image.mp h2
                have hn01 : L w0 ≠ L w1 := by
                  rw [he0,he1]
                  exact fun he => hst (labelPair _ _ _ _ hq0U hq0U hs ht he).2
                have hn02 : L w0 ≠ L w2 := by rw [he0,he2]; exact differentTips s s hs hs
                have hn12 : L w1 ≠ L w2 := by rw [he1,he2]; exact differentTips t s ht hs
                obtain ⟨i0,c0⟩ := localize w0 hw0
                obtain ⟨i1,c1⟩ := localize w1 hw1
                obtain ⟨i2,c2⟩ := localize w2 hw2
                obtain ⟨b,hbEnds,hbU,hd0,hd1,hd2⟩ := actualThreeFan (rτ w0) (rτ w1) (rτ w2) s t hst hs ht
                  ((endpoint w0).trans he0) ((endpoint w1).trans he1) ((endpoint w2).trans he2)
                  i0 c0 i1 c1 i2 c2 (disjointPair w0 w1 hn01) (disjointPair w0 w2 hn02) (disjointPair w1 w2 hn12)
                exact finish w0 w1 w2 hw0 hw1 hw2 hn01 hn02 hn12 b hbEnds hbU hd0 hd1 hd2
              have secondary (s t : S) (hs : s ∉ U) (ht : t ∉ U) (hst : s ≠ t)
                  (h0 : ({f q1,s} : Finset S) ∈ H.image L)
                  (h1 : ({f q1,t} : Finset S) ∈ H.image L)
                  (h2 : ({f q0,s} : Finset S) ∈ H.image L) :
                  ∃ b : EssentialMarkedArc M, markedArcEndset b.val = {f q0,f q1} ∧ b.val.image ⊆ U ∧
                    ∀ w ∈ H, Disjoint (arcInterior M b)
                      (arcInterior M (r ⟨w.val,Finset.mem_union_right _ w.property⟩)) := by
                obtain ⟨w0,hw0,he0⟩ := Finset.mem_image.mp h0
                obtain ⟨w1,hw1,he1⟩ := Finset.mem_image.mp h1
                obtain ⟨w2,hw2,he2⟩ := Finset.mem_image.mp h2
                have hn01 : L w0 ≠ L w1 := by
                  rw [he0,he1]
                  exact fun he => hst (labelPair _ _ _ _ hq1U hq1U hs ht he).2
                have hn02 : L w0 ≠ L w2 := by rw [he0,he2]; exact (differentTips s s hs hs).symm
                have hn12 : L w1 ≠ L w2 := by rw [he1,he2]; exact (differentTips s t hs ht).symm
                obtain ⟨i0,c0⟩ := localize w0 hw0
                obtain ⟨i1,c1⟩ := localize w1 hw1
                obtain ⟨i2,c2⟩ := localize w2 hw2
                obtain ⟨b,hbEnds,hbU,hd0,hd1,hd2⟩ := actualThreeFanOther (rτ w0) (rτ w1) (rτ w2) s t hst hs ht
                  ((endpoint w0).trans he0) ((endpoint w1).trans he1) ((endpoint w2).trans he2)
                  i0 c0 i1 c1 i2 c2 (disjointPair w0 w1 hn01) (disjointPair w0 w2 hn02) (disjointPair w1 w2 hn12)
                rw [Finset.pair_comm (f q1) (f q0)] at hbEnds
                exact finish w0 w1 w2 hw0 hw1 hw2 hn01 hn02 hn12 b hbEnds hbU hd0 hd1 hd2
              rcases choose with h | h | h | h
              · exact primary x y hxout hyout hxy h.1 h.2.1 h.2.2
              · exact primary y x hyout hxout hxy.symm h.1 h.2.1 h.2.2
              · exact secondary x y hxout hyout hxy h.1 h.2.1 h.2.2
              · exact secondary y x hyout hxout hxy.symm h.1 h.2.1 h.2.2
            · have hHtwo : H.card = 2 := by
                have hpos : H.card ≠ 0 := fun he => hHempty (Finset.card_eq_zero.mp he)
                omega
              let L : {w // w ∈ τ} → Finset S := fun w => classEndpoints M w.val
              let rτ : {w // w ∈ τ} → EssentialMarkedArc M :=
                fun w => r ⟨w.val,Finset.mem_union_right _ w.property⟩
              have endpoint (w : {w // w ∈ τ}) : markedArcEndset (rτ w).val = L w :=
                (markedArcEndset_eq_classEndpoints M (rτ w)).trans (congrArg (classEndpoints M) (hr _))
              have localize (w : {w // w ∈ τ}) (hw : w ∈ H) :
                  arcInterior M (rτ w) ⊆ U ∧ (rτ w).val.image ⊆ closure U := by
                have hdT : ∀ z, Disjoint (arcInterior M (rτ w)) (arcInterior M (rT z)) := by
                  intro z
                  rw [← hrestrict z]
                  apply hd
                  intro he
                  have hz : w.val = z.val := congrArg Subtype.val he
                  exact Finset.disjoint_left.mp hτ.1 z.property (hz ▸ w.property)
                have hit : (arcInterior M (rτ w) ∩ U).Nonempty := by
                  rw [hH] at hw
                  exact (Finset.mem_filter.mp hw).2
                obtain ⟨hi,hc,_⟩ := actual_link_arc_face_has_interior_endpoint
                  M p T τ hτ rT hrT O hO U hOU hUG (rτ w) w.val w.property (hr _) hdT hit
                exact ⟨hi,hc⟩
              have finish (w0 w1 : {w // w ∈ τ}) (hw0 : w0 ∈ H) (hw1 : w1 ∈ H) (hn : L w0 ≠ L w1)
                  (b : EssentialMarkedArc M) (hbEnds : markedArcEndset b.val = {f q0,f q1}) (hbU : b.val.image ⊆ U)
                  (hd0 : Disjoint (arcInterior M b) (arcInterior M (rτ w0)))
                  (hd1 : Disjoint (arcInterior M b) (arcInterior M (rτ w1))) :
                  ∃ b : EssentialMarkedArc M, markedArcEndset b.val = {f q0,f q1} ∧ b.val.image ⊆ U ∧
                    ∀ w ∈ H, Disjoint (arcInterior M b)
                      (arcInterior M (r ⟨w.val,Finset.mem_union_right _ w.property⟩)) := by
                have hnw : w0 ≠ w1 := fun he => hn (congrArg L he)
                have hcard : ({w0,w1} : Finset {w // w ∈ τ}).card = 2 := by simp [hnw]
                have hsub : ({w0,w1} : Finset {w // w ∈ τ}) ⊆ H := by
                  intro w hw
                  rcases Finset.mem_insert.mp hw with rfl | hw
                  · exact hw0
                  · exact Finset.mem_singleton.mp hw ▸ hw1
                have heH : ({w0,w1} : Finset {w // w ∈ τ}) = H :=
                  Finset.eq_of_subset_of_card_le hsub (by omega)
                refine ⟨b,hbEnds,hbU,?_⟩
                intro w hw
                rw [← heH] at hw
                rcases Finset.mem_insert.mp hw with rfl | hw
                · exact hd0
                · exact Finset.mem_singleton.mp hw ▸ hd1
              have labelsDistinct (q : Plane) (hq : q ∈ inside C) (hxy : x ≠ y) :
                  ({f q,x} : Finset S) ≠ {f q,y} := by
                intro he
                have hs := congrArg (fun d : Finset S => (d : Set S)) he
                simp only [Finset.coe_insert,Finset.coe_singleton] at hs
                rcases Set.pair_eq_pair_iff.mp hs with h | h
                · exact hxy h.2
                · exact hyout (h.1 ▸ (hU.symm ▸ mem_image_of_mem f hq))
              have disjointPair (w z : {w // w ∈ τ}) (hwz : L w ≠ L z) :
                  Disjoint (arcInterior M (rτ w)) (arcInterior M (rτ z)) := by
                apply hd
                intro he
                exact hwz (congrArg (fun k => classEndpoints M k.val) he)
              by_cases hSame0 : x ≠ y ∧ ({f q0,x} : Finset S) ∈ H.image L ∧ {f q0,y} ∈ H.image L
              · obtain ⟨hxy,h0,h1⟩ := hSame0
                obtain ⟨w0,hw0,he0⟩ := Finset.mem_image.mp h0
                obtain ⟨w1,hw1,he1⟩ := Finset.mem_image.mp h1
                have hn : L w0 ≠ L w1 := by rw [he0,he1]; exact labelsDistinct q0 hq0 hxy
                obtain ⟨i0,c0⟩ := localize w0 hw0
                obtain ⟨i1,c1⟩ := localize w1 hw1
                obtain ⟨b,hbEnds,hbU,hd0,hd1⟩ := actualTwoFan (rτ w0) (rτ w1) x y hxy hxout hyout
                  ((endpoint w0).trans he0) ((endpoint w1).trans he1) i0 c0 i1 c1 (disjointPair w0 w1 hn)
                exact finish w0 w1 hw0 hw1 hn b hbEnds hbU hd0 hd1
              · by_cases hSame1 : x ≠ y ∧ ({f q1,x} : Finset S) ∈ H.image L ∧ {f q1,y} ∈ H.image L
                · obtain ⟨hxy,h0,h1⟩ := hSame1
                  obtain ⟨w0,hw0,he0⟩ := Finset.mem_image.mp h0
                  obtain ⟨w1,hw1,he1⟩ := Finset.mem_image.mp h1
                  have hn : L w0 ≠ L w1 := by rw [he0,he1]; exact labelsDistinct q1 hq1 hxy
                  obtain ⟨i0,c0⟩ := localize w0 hw0
                  obtain ⟨i1,c1⟩ := localize w1 hw1
                  obtain ⟨b,hbEnds,hbU,hd0,hd1⟩ := actualTwoFanOther (rτ w0) (rτ w1) x y hxy hxout hyout
                    ((endpoint w0).trans he0) ((endpoint w1).trans he1) i0 c0 i1 c1 (disjointPair w0 w1 hn)
                  rw [Finset.pair_comm (f q1) (f q0)] at hbEnds
                  exact finish w0 w1 hw0 hw1 hn b hbEnds hbU hd0 hd1
                ·
                  have twoDistinctSpokes {D A B : Set Plane} {x y p q : Plane}
                      (hD : IsJordanCurve D) (hA : IsArcBetween A x p) (hB : IsArcBetween B y q)
                      (hx : x ∈ D) (hy : y ∈ D) (hp : p ∈ inside D) (hq : q ∈ inside D)
                      (hpq : p ≠ q) (hAi : A \ {x} ⊆ inside D) (hBi : B \ {y} ⊆ inside D)
                      (hAB : A ∩ B ⊆ {x,y}) :
                      ∃ P : Set Plane, IsArcBetween P p q ∧ P ⊆ inside D ∧
                        P \ {p,q} ⊆ (A ∪ B)ᶜ := by
                    have collapse {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
                        (f : X → Y) (hf : Topology.IsOpenEmbedding f) :
                        ∃ g : Y → OnePoint X, Continuous g ∧
                          (∀ x, g (f x) = (x : OnePoint X)) ∧
                          (∀ y, y ∉ range f → g y = OnePoint.infty) := by
                      classical
                      let H := hf.isEmbedding.toHomeomorph
                      let g : Y → OnePoint X := fun y => if h : y ∈ range f then
                        ((H.symm ⟨y,h⟩ : X) : OnePoint X) else OnePoint.infty
                      have hg (x : X) : g (f x) = (x : OnePoint X) := by
                        simp [g,H]
                      have hout (y : Y) (hy : y ∉ range f) : g y = OnePoint.infty := by
                        dsimp only [g]
                        rw [dif_neg hy]
                      refine ⟨g,?_,hg,hout⟩
                      apply continuous_def.mpr
                      intro A hA
                      by_cases hInf : OnePoint.infty ∈ A
                      · let K : Set X := ((↑) : X → OnePoint X) ⁻¹' Aᶜ
                        have hK : IsClosed K ∧ IsCompact K := by
                          exact (OnePoint.isOpen_iff_of_mem hInf).mp hA
                        have he : g ⁻¹' A = (f '' K)ᶜ := by
                          ext y
                          by_cases hy : y ∈ range f
                          · obtain ⟨x,rfl⟩ := hy
                            rw [mem_preimage,hg,mem_compl_iff,hf.injective.mem_set_image]
                            simp [K]
                          · rw [mem_preimage,hout y hy]
                            constructor
                            · intro _ hmem; exact hy (image_subset_range f K hmem)
                            · intro _; exact hInf
                        rw [he]
                        exact (hK.2.image hf.continuous).isClosed.isOpen_compl
                      · have ho : IsOpen (((↑) : X → OnePoint X) ⁻¹' A) :=
                          (OnePoint.isOpen_iff_of_notMem hInf).mp hA
                        have he : g ⁻¹' A = f '' (((↑) : X → OnePoint X) ⁻¹' A) := by
                          ext y
                          by_cases hy : y ∈ range f
                          · obtain ⟨x,rfl⟩ := hy
                            rw [mem_preimage,hg,hf.injective.mem_set_image]
                            rfl
                          · rw [mem_preimage,hout y hy]
                            constructor
                            · exact fun h => False.elim (hInf h)
                            · exact fun h => False.elim (hy (image_subset_range f _ h))
                        rw [he]
                        exact hf.isOpenMap _ ho
                    have small {A U : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
                        (hU : IsOpen U) (ha : a ∈ U) :
                        ∃ B : Set Plane, ∃ c : Plane,
                          IsArcBetween B a c ∧ B ⊆ A ∧ B ⊆ U := by
                      obtain ⟨f,hf,hi,himage,hf0,hf1⟩ := hA
                      let g : ℝ → Plane := fun t => f (projIcc 0 1 zero_le_one t)
                      have hg : Continuous g := (continuousOn_iff_continuous_restrict.mp hf).comp continuous_projIcc
                      have hg0 : g 0 = a := by simp [g,projIcc_of_mem zero_le_one (by norm_num : (0:ℝ) ∈ Icc 0 1),hf0]
                      have hn : g ⁻¹' U ∈ nhds (0:ℝ) := hg.continuousAt.preimage_mem_nhds (hg0.symm ▸ hU.mem_nhds ha)
                      obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
                      let d := min (ε/2) (1/2:ℝ)
                      have hd : 0 < d := lt_min (by linarith) (by norm_num)
                      have hd1 : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
                      have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
                      have hdmem : d ∈ I := ⟨hd.le,hd1⟩
                      have hsubI : uIcc (0:ℝ) d ⊆ I := uIcc_subset_I (by norm_num) hdmem
                      refine ⟨f '' uIcc (0:ℝ) d,f d,?_,?_,?_⟩
                      · simpa only [hf0] using isArcBetween_subarc_of_injOn_I hf hi (by norm_num) hdmem (ne_of_lt hd)
                      · rw [← himage]
                        exact image_mono hsubI
                      · rintro y ⟨t,ht,rfl⟩
                        have htc := hsubI ht
                        have ht' : 0 ≤ t ∧ t ≤ d := by simpa [uIcc_of_le hd.le] using ht
                        have hbt : t ∈ Metric.ball (0:ℝ) ε := by
                          rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht'.1]
                          exact lt_of_le_of_lt ht'.2 hdε
                        have hm := hball hbt
                        change g t ∈ U at hm
                        simpa only [g,projIcc_of_mem zero_le_one htc] using hm
                    have parameter {K : Set Plane} {u v : Plane} (hK : IsArcBetween K u v) :
                        ∃ α : Interval → Plane, Continuous α ∧ Function.Injective α ∧
                          range α = K ∧ α 0 = u ∧ α 1 = v := by
                      obtain ⟨α,hc,hi,himage,h0,h1⟩ := hK
                      refine ⟨fun t => α t.val,continuousOn_iff_continuous_domRestrict.mp hc,?_,?_,h0,h1⟩
                      · intro t u he
                        exact Subtype.ext (hi t.property u.property he)
                      · ext z
                        constructor
                        · rintro ⟨t,rfl⟩
                          exact himage ▸ mem_image_of_mem α t.property
                        · intro hz
                          obtain ⟨t,ht,rfl⟩ := himage.symm ▸ hz
                          exact ⟨⟨t,ht⟩,rfl⟩
                    have planarArc (α : Interval → Plane) (hc : Continuous α) (hi : Function.Injective α) :
                        IsArcBetween (range α) (α 0) (α 1) := by
                      let l : ℝ → Plane := α ∘ projIcc 0 1 zero_le_one
                      have hl : Continuous l := hc.comp continuous_projIcc
                      refine ⟨l,hl.continuousOn,?_,?_,?_,?_⟩
                      · intro t ht u hu he
                        have h := hi he
                        simpa only [projIcc_of_mem zero_le_one ht,projIcc_of_mem zero_le_one hu] using congrArg Subtype.val h
                      · ext z
                        constructor
                        · rintro ⟨t,ht,rfl⟩
                          exact ⟨projIcc 0 1 zero_le_one t,rfl⟩
                        · rintro ⟨t,rfl⟩
                          refine ⟨t.val,t.property,?_⟩
                          simp only [l,Function.comp_apply,projIcc_of_mem zero_le_one t.property]
                      · simp [l]
                      · simp [l]
                    have sphereComplement {Z : Type} [TopologicalSpace Z]
                        (esphere : Z ≃ₜ CurveComplex.SpherePort.Sphere)
                        (α β : Interval → Z) (hαc : Continuous α) (hβc : Continuous β)
                        (hαi : Function.Injective α) (hβi : Function.Injective β)
                        (hstart : β 0 = α 0) (htips : α 1 ≠ β 1)
                        (hmeet : range α ∩ range β = {α 0})
                        (v : Z) (hv : v ∉ range α ∪ range β) :
                        IsConnected ((range α ∪ range β)ᶜ) := by
                      letI : T2Space Z := esphere.symm.t2Space
                      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
                      let e : OpenPartialHomeomorph Z Plane :=
                        esphere.toOpenPartialHomeomorph.trans (stereographic' 2 (esphere v))
                      have hsource : e.source = {v}ᶜ := by
                        ext z
                        simp [e,OpenPartialHomeomorph.trans_source]
                      have htarget : e.target = univ := by simp [e,OpenPartialHomeomorph.trans_target]
                      have hαin (t : Interval) : α t ∈ e.source := by
                        rw [hsource]
                        intro he
                        exact hv (Or.inl ⟨t,Set.mem_singleton_iff.mp he⟩)
                      have hβin (t : Interval) : β t ∈ e.source := by
                        rw [hsource]
                        intro he
                        exact hv (Or.inr ⟨t,Set.mem_singleton_iff.mp he⟩)
                      let a : Interval → Plane := e ∘ α
                      let b : Interval → Plane := e ∘ β
                      have hac : Continuous a := e.continuousOn.comp_continuous hαc hαin
                      have hbc : Continuous b := e.continuousOn.comp_continuous hβc hβin
                      have hai : Function.Injective a := fun t u he => hαi (e.injOn (hαin t) (hαin u) he)
                      have hbi : Function.Injective b := fun t u he => hβi (e.injOn (hβin t) (hβin u) he)
                      have hab0 : b 0 = a 0 := congrArg e hstart
                      have hends : a 1 ≠ b 1 := fun he => htips (e.injOn (hαin 1) (hβin 1) he)
                      have hArc : IsArcBetween (range a ∪ range b) (a 1) (b 1) := by
                        apply (planarArc a hac hai).reverse.concatenate (hab0 ▸ planarArc b hbc hbi)
                        intro z hzA hzB
                        obtain ⟨t,ht⟩ := hzA
                        obtain ⟨u,hu⟩ := hzB
                        have htu : α t = β u := e.injOn (hαin t) (hβin u) (ht.trans hu.symm)
                        have ht0 : α t = α 0 := Set.mem_singleton_iff.mp
                          (hmeet ▸ (show α t ∈ range α ∩ range β from ⟨⟨t,rfl⟩,⟨u,htu.symm⟩⟩))
                        exact ht.symm.trans (congrArg e ht0)
                      have hconn := Schoenflies.arc_complement hArc.isArc
                      have hsymm : Continuous e.symm := continuousOn_univ.mp (htarget ▸ e.continuousOn_symm)
                      have himage : e.symm '' (range a ∪ range b)ᶜ = (range α ∪ range β)ᶜ ∩ {v}ᶜ := by
                        ext z
                        constructor
                        · rintro ⟨w,hw,rfl⟩
                          have hws : e.symm w ∈ e.source := e.map_target (htarget ▸ Set.mem_univ w)
                          refine ⟨?_,hsource ▸ hws⟩
                          intro hm
                          rcases hm with ⟨t,ht⟩ | ⟨t,ht⟩
                          · apply hw
                            exact Or.inl ⟨t,by change e (α t) = w; rw [ht]; exact e.right_inv (htarget ▸ Set.mem_univ w)⟩
                          · apply hw
                            exact Or.inr ⟨t,by change e (β t) = w; rw [ht]; exact e.right_inv (htarget ▸ Set.mem_univ w)⟩
                        · rintro ⟨hz,hzv⟩
                          have hzs : z ∈ e.source := hsource.symm ▸ hzv
                          refine ⟨e z,?_,e.left_inv hzs⟩
                          intro hm
                          rcases hm with ⟨t,ht⟩ | ⟨t,ht⟩
                          · exact hz (Or.inl ⟨t,e.injOn (hαin t) hzs ht⟩)
                          · exact hz (Or.inr ⟨t,e.injOn (hβin t) hzs ht⟩)
                      have hpunct : IsConnected ((range α ∪ range β)ᶜ ∩ {v}ᶜ) := by
                        rw [← himage]
                        exact hconn.image e.symm hsymm.continuousOn
                      have hsphere : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
                        apply isConnected_sphere _ _ (by norm_num)
                        rw [← Module.finrank_eq_rank]
                        norm_num
                      letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
                        isConnected_iff_connectedSpace.mp hsphere
                      letI : ConnectedSpace Z := connectedSpace_iff_univ.mpr (by
                        have hi := isConnected_univ.image esphere.symm esphere.symm.continuous.continuousOn
                        simpa only [Set.image_univ,esphere.symm.surjective.range_eq] using hi)
                      have hdense : Dense ({v}ᶜ : Set Z) := by
                        apply dense_compl_singleton_iff_not_open.mpr
                        intro hopen
                        have hs : ({v} : Set Z) = univ :=
                          (show IsClopen ({v} : Set Z) from ⟨isClosed_singleton,hopen⟩).eq_univ ⟨v,rfl⟩
                        have he : α 0 = v := Set.mem_singleton_iff.mp (hs.symm ▸ Set.mem_univ _)
                        exact hv (Or.inl ⟨0,he⟩)
                      have hclosed : IsClosed (range α ∪ range β) :=
                        (isCompact_range hαc).isClosed.union (isCompact_range hβc).isClosed
                      have hcl : (range α ∪ range β)ᶜ ⊆ closure ((range α ∪ range β)ᶜ ∩ {v}ᶜ) := by
                        simpa only [Set.inter_comm] using hdense.open_subset_closure_inter hclosed.isOpen_compl
                      exact hpunct.subset_closure Set.inter_subset_left hcl
                    have hpB : p ∉ B := by
                      intro hpB
                      have he := hAB ⟨hA.right_mem,hpB⟩
                      rcases he with he | he
                      · exact inside_subset_compl hp (he ▸ hx)
                      · exact inside_subset_compl hp ((Set.mem_singleton_iff.mp he) ▸ hy)
                    have hqA : q ∉ A := by
                      intro hqA
                      have he := hAB ⟨hqA,hB.right_mem⟩
                      rcases he with he | he
                      · exact inside_subset_compl hq (he ▸ hx)
                      · exact inside_subset_compl hq ((Set.mem_singleton_iff.mp he) ▸ hy)
                    obtain ⟨E,u,hE,_,hEavoid⟩ := endpoint_access_of_isArcBetween hA.reverse
                    obtain ⟨E₀,u₀,hE₀,hEsub,hEopen⟩ := small hE
                      ((jordan_curve_theorem hD).isOpen_inside.inter hB.isArc.isCompact.isClosed.isOpen_compl) ⟨hp,hpB⟩
                    obtain ⟨F,w,hF,_,hFavoid⟩ := endpoint_access_of_isArcBetween hB.reverse
                    obtain ⟨F₀,w₀,hF₀,hFsub,hFopen⟩ := small hF
                      ((jordan_curve_theorem hD).isOpen_inside.inter hA.isArc.isCompact.isClosed.isOpen_compl) ⟨hq,hqA⟩
                    have hEavoid₀ : E₀ \ {p} ⊆ Aᶜ := fun z hz => hEavoid ⟨hEsub hz.1,hz.2⟩
                    have hFavoid₀ : F₀ \ {q} ⊆ Bᶜ := fun z hz => hFavoid ⟨hFsub hz.1,hz.2⟩
                    have huΩ : u₀ ∈ inside D \ (A ∪ B) :=
                      ⟨(hEopen hE₀.right_mem).1,fun he => he.elim
                        (hEavoid₀ ⟨hE₀.right_mem,by simpa using hE₀.ne.symm⟩) (hEopen hE₀.right_mem).2⟩
                    have hwΩ : w₀ ∈ inside D \ (A ∪ B) :=
                      ⟨(hFopen hF₀.right_mem).1,fun he => he.elim
                        (hFopen hF₀.right_mem).2 (hFavoid₀ ⟨hF₀.right_mem,by simpa using hF₀.ne.symm⟩)⟩
                    obtain ⟨e⟩ := disc hD
                    let fD : Plane → Plane := fun z => (e z).val
                    have hfD : Topology.IsOpenEmbedding fD :=
                      (jordan_curve_theorem hD).isOpen_inside.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
                    have hrange : range fD = inside D := by
                      ext z
                      constructor
                      · rintro ⟨w,rfl⟩
                        exact (e w).property
                      · intro hz
                        exact ⟨e.symm ⟨z,hz⟩,congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)⟩
                    obtain ⟨g,hgc,hg,hgout⟩ := collapse fD hfD
                    have insideCoe (z : Plane) (hz : z ∈ inside D) :
                        ∃ w : Plane, fD w = z ∧ g z = (w : OnePoint Plane) := by
                      obtain ⟨w,hw⟩ := hrange.symm ▸ hz
                      exact ⟨w,hw,hw ▸ hg w⟩
                    have gInsideInjective {z w : Plane} (hz : z ∈ inside D) (hw : w ∈ inside D)
                        (he : g z = g w) : z = w := by
                      obtain ⟨v,hv,hgv⟩ := insideCoe z hz
                      obtain ⟨u,hu,hgu⟩ := insideCoe w hw
                      rw [hgv,hgu] at he
                      exact hv.symm.trans ((congrArg fD (OnePoint.coe_injective he)).trans hu)
                    have halfCollapse (K : Set Plane) (x p : Plane) (hK : IsArcBetween K x p)
                        (hx : x ∈ D) (hKi : K \ {x} ⊆ inside D) :
                        ∃ α : Interval → OnePoint Plane, Continuous α ∧ Function.Injective α ∧
                          range α = g '' K ∧ α 0 = OnePoint.infty ∧ α 1 = g p := by
                      obtain ⟨a,hac,hai,haK,ha0,ha1⟩ := parameter hK
                      let b : Interval → OnePoint Plane := g ∘ a
                      have hb0 : b 0 = OnePoint.infty := by
                        change g (a 0) = _
                        rw [ha0]
                        apply hgout
                        rw [hrange]
                        exact fun hin => inside_subset_compl hin hx
                      have hpos (t : Interval) (ht : t ≠ 0) : a t ∈ inside D :=
                        hKi ⟨haK ▸ ⟨t,rfl⟩,fun he => ht (hai ((Set.mem_singleton_iff.mp he).trans ha0.symm))⟩
                      have hbi : Function.Injective b := by
                        intro t u he
                        by_cases ht : t = 0
                        · by_cases hu : u = 0
                          · exact ht.trans hu.symm
                          · obtain ⟨w,hw,hgw⟩ := insideCoe (a u) (hpos u hu)
                            rw [ht,hb0] at he
                            exact False.elim (OnePoint.infty_ne_coe w (he.trans hgw))
                        · by_cases hu : u = 0
                          · obtain ⟨w,hw,hgw⟩ := insideCoe (a t) (hpos t ht)
                            rw [hu,hb0] at he
                            exact False.elim (OnePoint.coe_ne_infty w (hgw.symm.trans he))
                          · exact hai (gInsideInjective (hpos t ht) (hpos u hu) he)
                      refine ⟨b,hgc.comp hac,hbi,?_,hb0,?_⟩
                      · rw [← haK]
                        exact Set.range_comp g a
                      · exact congrArg g ha1
                    obtain ⟨α,hαc,hαi,hαK,hα0,hα1⟩ := halfCollapse A x p hA hx hAi
                    obtain ⟨β,hβc,hβi,hβK,hβ0,hβ1⟩ := halfCollapse B y q hB hy hBi
                    have meetSphere : range α ∩ range β = {OnePoint.infty} := by
                      apply Set.Subset.antisymm
                      · intro z hz
                        by_cases he : z = OnePoint.infty
                        · exact he
                        · rw [hαK,hβK] at hz
                          obtain ⟨v,hv,hgv⟩ := hz.1
                          obtain ⟨w,hw,hgw⟩ := hz.2
                          have hvx : v ≠ x := by
                            intro hvx
                            have hvout : v ∉ range fD := by rw [hrange,hvx]; exact fun hin => inside_subset_compl hin hx
                            exact he (hgv.symm.trans (hgout v hvout))
                          have hwy : w ≠ y := by
                            intro hwy
                            have hwout : w ∉ range fD := by rw [hrange,hwy]; exact fun hin => inside_subset_compl hin hy
                            exact he (hgw.symm.trans (hgout w hwout))
                          have hvI := hAi ⟨hv,hvx⟩
                          have hwI := hBi ⟨hw,hwy⟩
                          have hvw : v = w := gInsideInjective hvI hwI (hgv.trans hgw.symm)
                          have hvAB := hAB ⟨hv,hvw.symm ▸ hw⟩
                          rcases hvAB with hvAB | hvAB
                          · exact False.elim (inside_subset_compl hvI (hvAB ▸ hx))
                          · exact False.elim (inside_subset_compl hvI ((Set.mem_singleton_iff.mp hvAB) ▸ hy))
                      · rintro z rfl
                        exact ⟨⟨0,hα0⟩,⟨0,hβ0⟩⟩
                    have guAvoid : g u₀ ∉ range α ∪ range β := by
                      intro he
                      rw [hαK,hβK] at he
                      rcases he with ⟨v,hv,he⟩ | ⟨v,hv,he⟩
                      all_goals
                        have hvIn : v ∈ inside D := by
                          first
                          | apply hAi; refine ⟨hv,?_⟩
                          | apply hBi; refine ⟨hv,?_⟩
                          intro hvEnd
                          obtain ⟨w,hw,hgw⟩ := insideCoe u₀ huΩ.1
                          have hvInf : g v = OnePoint.infty := by
                            apply hgout
                            rw [hrange]
                            first
                            | exact fun hin => inside_subset_compl hin (hvEnd ▸ hx)
                            | exact fun hin => inside_subset_compl hin (hvEnd ▸ hy)
                          exact OnePoint.infty_ne_coe w (hvInf.symm.trans (he.trans hgw))
                        have hveq : v = u₀ := gInsideInjective hvIn huΩ.1 he
                        apply huΩ.2
                        first
                        | exact Or.inl (hveq ▸ hv)
                        | exact Or.inr (hveq ▸ hv)
                    let eSphere : OnePoint Plane ≃ₜ CurveComplex.SpherePort.Sphere := onePointEquivSphereOfFinrankEq (by simp)
                    have htips : α 1 ≠ β 1 := by
                      rw [hα1,hβ1]
                      exact fun he => hpq (gInsideInjective hp hq he)
                    have hconnSphere := sphereComplement eSphere α β hαc hβc hαi hβi
                      (hβ0.trans hα0.symm) htips (hα0.symm ▸ meetSphere) (g u₀) guAvoid
                    let K : Set Plane := {z | (z : OnePoint Plane) ∉ range α ∪ range β}
                    have hKimage : ((↑) : Plane → OnePoint Plane) '' K = (range α ∪ range β)ᶜ := by
                      ext z
                      constructor
                      · rintro ⟨w,hw,rfl⟩
                        exact hw
                      · intro hz
                        cases z using OnePoint.rec with
                        | infty => exact False.elim (hz (Or.inl ⟨0,hα0⟩))
                        | coe w => exact ⟨w,hz,rfl⟩
                    have hKconn : IsConnected K := by
                      rw [← hKimage] at hconnSphere
                      exact ⟨Set.image_nonempty.mp hconnSphere.nonempty,
                        OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp hconnSphere.isPreconnected⟩
                    have htarget : fD '' K = inside D \ (A ∪ B) := by
                      ext z
                      constructor
                      · rintro ⟨w,hw,rfl⟩
                        refine ⟨hrange ▸ ⟨w,rfl⟩,?_⟩
                        intro hzAB
                        apply hw
                        rw [hαK,hβK,← hg w]
                        exact hzAB.elim (fun hzA => Or.inl ⟨fD w,hzA,rfl⟩) (fun hzB => Or.inr ⟨fD w,hzB,rfl⟩)
                      · rintro ⟨hz,hzAB⟩
                        obtain ⟨w,hw,hgw⟩ := insideCoe z hz
                        refine ⟨w,?_,hw⟩
                        intro he
                        rw [hαK,hβK] at he
                        rcases he with ⟨v,hv,he⟩ | ⟨v,hv,he⟩
                        all_goals
                          have he' : g v = g z := he.trans hgw.symm
                          have hvIn : v ∈ inside D := by
                            first
                            | apply hAi; refine ⟨hv,?_⟩
                            | apply hBi; refine ⟨hv,?_⟩
                            intro hvEnd
                            have hvInf : g v = OnePoint.infty := by
                              apply hgout
                              rw [hrange]
                              first
                              | exact fun hin => inside_subset_compl hin (hvEnd ▸ hx)
                              | exact fun hin => inside_subset_compl hin (hvEnd ▸ hy)
                            exact OnePoint.infty_ne_coe w (hvInf.symm.trans he)
                          have hvz : v = z := gInsideInjective hvIn hz he'
                          apply hzAB
                          first
                          | exact Or.inl (hvz ▸ hv)
                          | exact Or.inr (hvz ▸ hv)
                    have hconn : IsConnected (inside D \ (A ∪ B)) := by
                      rw [← htarget]
                      exact hKconn.image fD hfD.continuous.continuousOn
                    have hopen : IsOpen (inside D \ (A ∪ B)) :=
                      (jordan_curve_theorem hD).isOpen_inside.sdiff (hA.isArc.isCompact.union hB.isArc.isCompact).isClosed
                    have route : ∃ P : Set Plane, IsArcBetween P p q ∧ P ⊆ E₀ ∪ F₀ ∪ (inside D \ (A ∪ B)) := by
                      by_cases he : u₀ = w₀
                      · obtain ⟨P,hsub,hP⟩ := exists_arc_in_union_of_arcs hE₀ (he.symm ▸ hF₀.reverse) hpq
                        exact ⟨P,hP,fun z hz => Or.inl (hsub hz)⟩
                      · obtain ⟨R,hRsub,_,hR⟩ := exists_simple_arc_of_isPreconnected hopen hconn.isPreconnected huΩ hwΩ he
                        have hpw : p ≠ w₀ := by
                          intro he
                          exact hwΩ.2 (Or.inl (he ▸ hA.right_mem))
                        obtain ⟨P₀,hP₀sub,hP₀⟩ := exists_arc_in_union_of_arcs hE₀ hR hpw
                        obtain ⟨P,hPsub,hP⟩ := exists_arc_in_union_of_arcs hP₀ hF₀.reverse hpq
                        refine ⟨P,hP,?_⟩
                        intro z hz
                        rcases hPsub hz with hz0 | hzF
                        · rcases hP₀sub hz0 with hzE | hzR
                          · exact Or.inl (Or.inl hzE)
                          · exact Or.inr (hRsub hzR)
                        · exact Or.inl (Or.inr hzF)
                    obtain ⟨P,hP,hPsub⟩ := route
                    refine ⟨P,hP,?_,?_⟩
                    · intro z hz
                      rcases hPsub hz with (hzE | hzF) | hzΩ
                      · exact (hEopen hzE).1
                      · exact (hFopen hzF).1
                      · exact hzΩ.1
                    · intro z hz hzAB
                      rcases hPsub hz.1 with (hzE | hzF) | hzΩ
                      · rcases hzAB with hzA | hzB
                        · exact hEavoid₀ ⟨hzE,fun he => hz.2 (Or.inl (Set.mem_singleton_iff.mp he))⟩ hzA
                        · exact (hEopen hzE).2 hzB
                      · rcases hzAB with hzA | hzB
                        · exact (hFopen hzF).2 hzA
                        · exact hFavoid₀ ⟨hzF,fun he => hz.2 (Or.inr he)⟩ hzB
                      · exact hzΩ.2 hzAB
                  have actualTwoDistinct (b0 b1 : EssentialMarkedArc M) (s t : S)
                      (hs : s ∉ U) (ht : t ∉ U)
                      (he0 : markedArcEndset b0.val = {f q0,s}) (he1 : markedArcEndset b1.val = {f q1,t})
                      (hi0 : arcInterior M b0 ⊆ U) (hc0 : b0.val.image ⊆ closure U)
                      (hi1 : arcInterior M b1 ⊆ U) (hc1 : b1.val.image ⊆ closure U)
                      (hd01 : Disjoint (arcInterior M b0) (arcInterior M b1)) :
                      ∃ c : EssentialMarkedArc M, markedArcEndset c.val = {f q0,f q1} ∧
                        c.val.image ⊆ U ∧ Disjoint (arcInterior M c) (arcInterior M b0) ∧
                          Disjoint (arcInterior M c) (arcInterior M b1) := by
                    obtain ⟨A,xA,hA,hxA,him0,hin0,hfxA⟩ := spokeCoordinates b0 q0 s hq0 hs he0 hi0 hc0
                    obtain ⟨B,xB,hB,hxB,him1,hin1,hfxB⟩ := spokeCoordinates b1 q1 t hq1 ht he1 hi1 hc1
                    have meet : A ∩ B ⊆ {xA,xB} := by
                      intro z hz
                      have he := coordinateIntersection b0 b1 A B him0 him1 hd01 ▸ hz
                      rw [he0,he1] at he
                      simp only [Set.mem_preimage,Finset.coe_insert,Finset.coe_singleton,
                        Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff] at he
                      rcases he with ⟨he0,he1⟩
                      rcases he0 with he0 | he0
                      · rcases he1 with he1 | he1
                        · exact False.elim (hne (hf.injective (he0.symm.trans he1)))
                        · exact False.elim (ht ((he0.symm.trans he1) ▸ hq0U))
                      · exact Or.inl (hf.injective (he0.trans hfxA.symm))
                    obtain ⟨P,hP,hPi,havoid⟩ := twoDistinctSpokes hC hA hB hxA hxB hq0 hq1 hne hin0 hin1 meet
                    obtain ⟨c,hc0,hc1,hcImage,hcU⟩ := liftPair P hP hPi
                    have avoid (b : EssentialMarkedArc M) (D : Set Plane) (him : b.val.image = f '' D)
                        (hsub : D ⊆ A ∪ B) : Disjoint (arcInterior M c) (arcInterior M b) := by
                      apply Set.disjoint_left.mpr
                      intro z hzc hzb
                      obtain ⟨v,hv,rfl⟩ := hcImage ▸ hzc.1
                      have hvEnds : v ∉ ({q0,q1} : Set Plane) := by
                        intro he
                        rcases he with rfl | he
                        · exact hzc.2 (ha0 ▸ a.val.start_marked)
                        · exact hzc.2 ((Set.mem_singleton_iff.mp he) ▸ (ha1 ▸ a.val.end_marked))
                      exact havoid ⟨hv,hvEnds⟩ (hsub (hf.injective.mem_set_image.mp (him ▸ hzb.1)))
                    refine ⟨c,?_,hcU,avoid b0 A him0 Set.subset_union_left,avoid b1 B him1 Set.subset_union_right⟩
                    change ({c.val.map (0 : Interval),c.val.map (1 : Interval)} : Finset S) = _
                    rw [hc0,hc1]
                  obtain ⟨w0,w1,hwne,hHeq⟩ := Finset.card_eq_two.mp hHtwo
                  have hw0 : w0 ∈ H := hHeq.symm ▸ Finset.mem_insert_self _ _
                  have hw1 : w1 ∈ H := hHeq.symm ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
                  have hnlabels : L w0 ≠ L w1 := by
                    intro he
                    exact hwne (Subtype.ext (labelUnique w0.val w0.property w1.val w1.property he))
                  have primary (w z : {w // w ∈ τ}) (hw : w ∈ H) (hz : z ∈ H)
                      (s t : S) (hs : s ∉ U) (ht : t ∉ U)
                      (he0 : L w = {f q0,s}) (he1 : L z = {f q1,t})
                      (hn : L w ≠ L z) :
                      ∃ b : EssentialMarkedArc M, markedArcEndset b.val = {f q0,f q1} ∧ b.val.image ⊆ U ∧
                        ∀ w ∈ H, Disjoint (arcInterior M b)
                          (arcInterior M (r ⟨w.val,Finset.mem_union_right _ w.property⟩)) := by
                    obtain ⟨iw,cw⟩ := localize w hw
                    obtain ⟨iz,cz⟩ := localize z hz
                    obtain ⟨b,hbEnds,hbU,hdw,hdz⟩ := actualTwoDistinct (rτ w) (rτ z) s t hs ht
                      ((endpoint w).trans he0) ((endpoint z).trans he1) iw cw iz cz (disjointPair w z hn)
                    exact finish w z hw hz hn b hbEnds hbU hdw hdz
                  have hm0 := hmembers w0 hw0
                  have hm1 := hmembers w1 hw1
                  simp only [Finset.mem_insert,Finset.mem_singleton] at hm0 hm1
                  rcases hm0 with he0 | he0 | he0 | he0 <;> rcases hm1 with he1 | he1 | he1 | he1
                  · exact False.elim (hnlabels (he0.trans he1.symm))
                  · have hxy : x ≠ y := by
                      intro he
                      apply hnlabels
                      change classEndpoints M w0.val = classEndpoints M w1.val
                      rw [he0,he1,he]
                    exact False.elim (hSame0 ⟨hxy,Finset.mem_image.mpr ⟨w0,hw0,he0⟩,
                      Finset.mem_image.mpr ⟨w1,hw1,he1⟩⟩)
                  · exact primary w0 w1 hw0 hw1 x x hxout hxout he0 he1 hnlabels
                  · exact primary w0 w1 hw0 hw1 x y hxout hyout he0 he1 hnlabels
                  · have hxy : x ≠ y := by
                      intro he
                      apply hnlabels
                      change classEndpoints M w0.val = classEndpoints M w1.val
                      rw [he0,he1,he]
                    exact False.elim (hSame0 ⟨hxy,Finset.mem_image.mpr ⟨w1,hw1,he1⟩,
                      Finset.mem_image.mpr ⟨w0,hw0,he0⟩⟩)
                  · exact False.elim (hnlabels (he0.trans he1.symm))
                  · exact primary w0 w1 hw0 hw1 y x hyout hxout he0 he1 hnlabels
                  · exact primary w0 w1 hw0 hw1 y y hyout hyout he0 he1 hnlabels
                  · exact primary w1 w0 hw1 hw0 x x hxout hxout he1 he0 hnlabels.symm
                  · exact primary w1 w0 hw1 hw0 y x hyout hxout he1 he0 hnlabels.symm
                  · exact False.elim (hnlabels (he0.trans he1.symm))
                  · have hxy : x ≠ y := by
                      intro he
                      apply hnlabels
                      change classEndpoints M w0.val = classEndpoints M w1.val
                      rw [he0,he1,he]
                    exact False.elim (hSame1 ⟨hxy,Finset.mem_image.mpr ⟨w0,hw0,he0⟩,
                      Finset.mem_image.mpr ⟨w1,hw1,he1⟩⟩)
                  · exact primary w1 w0 hw1 hw0 x y hxout hyout he1 he0 hnlabels.symm
                  · exact primary w1 w0 hw1 hw0 y y hyout hyout he1 he0 hnlabels.symm
                  · have hxy : x ≠ y := by
                      intro he
                      apply hnlabels
                      change classEndpoints M w0.val = classEndpoints M w1.val
                      rw [he0,he1,he]
                    exact False.elim (hSame1 ⟨hxy,Finset.mem_image.mpr ⟨w1,hw1,he1⟩,
                      Finset.mem_image.mpr ⟨w0,hw0,he0⟩⟩)
                  · exact False.elim (hnlabels (he0.trans he1.symm))
    have hdb : ∀ w, Disjoint (arcInterior M b) (arcInterior M (r w)) := by
      intro w
      rcases Finset.mem_union.mp w.property with hwT | hwτ
      · have he : r w = rT ⟨w.val,hwT⟩ := hrestrict ⟨w.val,hwT⟩
        rw [he]
        apply Set.disjoint_left.mpr
        intro z hzb hzr
        exact hUG.2.2.1 (hbU hzb.1)
          (Set.mem_iUnion.mpr ⟨⟨w.val,hwT⟩,hzr.1⟩)
      · let wτ : {w // w ∈ τ} := ⟨w.val,hwτ⟩
        by_cases hit : (arcInterior M (r w) ∩ U).Nonempty
        · have hwH : wτ ∈ H := by
            rw [hH]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
          exact hdbH wτ hwH
        · apply Set.disjoint_left.mpr
          intro z hzb hzr
          exact hit ⟨z,hzr,hbU hzb.1⟩
    have hbv := twoMarkClass b hbEnds hbU
    have hins := actual_simplex_insert_disjoint_representative M (T.val ∪ τ) r hr hd b hdb
    simpa only [hbv] using hins
  have fresh : ∀ w ∈ T.val ∪ τ, w ≠ v → ¬ (actualArcLabels M).isLoop w →
      classEndpoints M w ≠ classEndpoints M v := by
    intro w hw hneq hnl he
    have hqEnd : f q0 ∈ classEndpoints M w := by rw [he,vend]; simp
    rcases Finset.mem_union.mp hw with hwT | hwτ
    · exact noT w hwT hqEnd
    · let b := r ⟨w,hw⟩
      have hbw : Quotient.mk (essentialArcSetoid M) b = w := hr ⟨w,hw⟩
      have hbEnds : markedArcEndset b.val = {f q0,f q1} :=
        ((markedArcEndset_eq_classEndpoints M b).trans
          (congrArg (classEndpoints M) hbw)).trans (he.trans vend)
      have hdT : ∀ z, Disjoint (arcInterior M b) (arcInterior M (rT z)) := by
        intro z
        rw [← hrestrict z]
        apply hd
        intro h
        have hz : w = z.val := congrArg Subtype.val h
        exact Finset.disjoint_left.mp hτ.1 z.property (hz ▸ hwτ)
      exact hneq ((twoMarkClass b hbEnds (contained b hbEnds hdT)).symm.trans hbw).symm
  have hunion : T.val ∪ insert v τ = insert v (T.val ∪ τ) := by
    ext w
    simp only [Finset.mem_union,Finset.mem_insert]
    tauto
  change Disjoint T.val (insert v τ) ∧ T.val ∪ insert v τ ∈ actualA M ∧
    badVertices (actualArcLabels M) (T.val ∪ insert v τ) = T.val
  refine ⟨Finset.disjoint_insert_right.mpr ⟨hvT,hτ.1⟩,?_,?_⟩
  · rw [hunion]
    exact hsimplex
  · rw [hunion,badVertices_insert_fresh_endpoint (actualArcLabels M)
        (T.val ∪ τ) v nonloopv fresh]
    exact hτ.2.2

end CurveComplex.HyperellipticModel
