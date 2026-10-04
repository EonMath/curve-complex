import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Dictionary.ArcGeometry
import CurveComplexGenusTwo.Dictionary.OneBranchDiscBoundary
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import CurveComplexGenusTwo.Foundations.PlanarDiscRecognition
import CurveComplexGenusTwo.Dictionary.JordanDiscHelper
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import CurveComplexGenusTwo.Intersection.SphereRegionTransport
import CurveComplexGenusTwo.Foundations.PlanarSquareDiscWitness
import ClassificationOfSurfaces.Moise.Brouwer
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Schoenflies.JordanClosed
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import Schoenflies.Plane
import Schoenflies.SimpleArc
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped Manifold
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain

open Set Topology
set_option linter.style.haveILetI false


open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
/-- A region containing an essential curve is not a topological open disk. -/
theorem region_not_plane_of_essential_curve (U : Set E) (c : EssentialCurve E)
    (hcU : c.val.image ⊆ U) : ¬ Nonempty (U ≃ₜ Schoenflies.Plane) := by
  rintro ⟨h⟩
  let r : Circle → U := fun t => ⟨c.val.map t, hcU (Set.mem_range_self t)⟩
  have hr : Continuous r := c.val.embedded.continuous.subtype_mk _
  have hri : IsEmbedding r := by
    apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    exact c.val.embedded
  let d : Curve Schoenflies.Plane :=
    ⟨h ∘ r, h.isEmbedding.comp hri⟩
  have hd : BoundsDisc d := jordan_curve_bounds_disc d
    (isJordanCurve_range_of_isEmbedding_circle
      ⟨d.map, d.embedded.continuous⟩ d.embedded)
  obtain ⟨f, hf, hboundary⟩ := hd
  let g : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, E) :=
    ⟨fun t => (h.symm (f t) : E), continuous_subtype_val.comp
      (h.symm.continuous.comp f.continuous)⟩
  apply c.property
  refine ⟨g, Topology.IsEmbedding.subtypeVal.comp (h.symm.isEmbedding.comp hf), ?_⟩
  change (Subtype.val ∘ h.symm ∘ f) '' _ = c.val.image
  rw [Set.image_comp, Set.image_comp, hboundary]
  change Subtype.val '' (h.symm '' Set.range (h ∘ r)) = Set.range c.val.map
  rw [Set.range_comp]
  have hh : h.symm '' (h '' Set.range r) = Set.range r := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, hzx⟩
      have heq : z = x := by simpa only [h.symm_apply_apply] using hzx
      exact heq ▸ hz
    · intro hx
      exact ⟨h x, ⟨x, hx, rfl⟩, h.symm_apply_apply x⟩
  rw [hh]
  change Subtype.val '' Set.range r = Set.range c.val.map
  rw [← Set.range_comp]
  rfl
/-- An open connected downstairs region with at least two marks contains a non-loop marked arc. -/
theorem nonloop_arc_inside_marked_region (U : Set S)
    (hU : IsOpen U) (hUc : IsConnected U)
    (p q : S) (hp : p ∈ M.cover.branch) (hq : q ∈ M.cover.branch)
    (hpU : p ∈ U) (hqU : q ∈ U) (hpq : p ≠ q) :
    ∃ a : NonLoopArc M, a.image ⊆ U := by
  classical
  have htrim (f : C(Interval, S)) (hfi : Function.Injective f)
      (hstart : f 0 ∈ M.cover.branch) (hend : f 1 ∈ M.cover.branch)
      (hfU : Set.range f ⊆ U) : ∃ a : NonLoopArc M, a.image ⊆ U := by
        as_aux_lemma =>
      classical
      let K : Set Interval := f ⁻¹' (M.cover.branch : Set S) \ {0}
      have hKfinite : K.Finite :=
        ((M.cover.branch.finite_toSet).preimage hfi.injOn).sdiff
      have hKnonempty : K.Nonempty := ⟨1, hend, by norm_num⟩
      let ks := hKfinite.toFinset
      have hksne : ks.Nonempty := by simpa [ks] using hKnonempty
      let b : Interval := ks.min' hksne
      have hbK : b ∈ K := by
        exact hKfinite.mem_toFinset.mp (Finset.min'_mem ks hksne)
      have hb0 : (0 : ℝ) < (b : ℝ) := by
        have hbne : b ≠ 0 := hbK.2
        have hbvalne : (b : ℝ) ≠ 0 := by
          intro he
          exact hbne (Subtype.ext he)
        exact lt_of_le_of_ne b.property.1 hbvalne.symm
      let k : Interval → Interval := fun t => ⟨(t : ℝ) * (b : ℝ), by
        constructor
        · exact mul_nonneg t.property.1 b.property.1
        · exact (mul_le_mul_of_nonneg_right t.property.2 b.property.1).trans (by simpa using b.property.2)⟩
      have hkcont : Continuous k :=
        (continuous_subtype_val.mul continuous_const).subtype_mk _
      have hk0 : k 0 = 0 := Subtype.ext (by simp [k])
      have hk1 : k 1 = b := Subtype.ext (by simp [k])
      have hki : Function.Injective k := by
        intro t u htu
        apply Subtype.ext
        have hval := congrArg Subtype.val htu
        exact mul_right_cancel₀ (ne_of_gt hb0) hval
      have hmarked : ∀ t, f (k t) ∈ M.cover.branch → t = 0 ∨ t = 1 := by
        intro t ht
        by_cases hzero : t = 0
        · exact Or.inl hzero
        · right
          have hktne : k t ≠ 0 := by
            intro he
            exact hzero (hki (he.trans hk0.symm))
          have hktK : k t ∈ K := ⟨ht, hktne⟩
          have hmin : b ≤ k t := Finset.min'_le ks (k t)
            (hKfinite.mem_toFinset.mpr hktK)
          apply Subtype.ext
          have hmin' : (b : ℝ) ≤ (t : ℝ) * (b : ℝ) := hmin
          have ht1 := t.property.2
          have htle : (1 : ℝ) ≤ (t : ℝ) := by
            apply (mul_le_mul_iff_left₀ hb0).mp
            simpa using hmin'
          exact le_antisymm ht1 htle
      let a : MarkedArc M := {
        map := fun t => f (k t)
        continuous := f.continuous.comp hkcont
        injective_except_loop_closure := by
          intro t u h
          exact Or.inl (hki (hfi h))
        start_marked := by change f (k 0) ∈ M.cover.branch; rw [hk0]; exact hstart
        end_marked := by change f (k 1) ∈ M.cover.branch; rw [hk1]; exact hbK.1
        marked_only_at_ends := hmarked }
      have haneq : a.map 0 ≠ a.map 1 := by
        intro he
        have hk := hki (hfi he)
        exact (by norm_num : (0 : Interval) ≠ 1) hk
      refine ⟨⟨a, haneq⟩, ?_⟩
      rintro x ⟨t, rfl⟩
      exact hfU ⟨k t, rfl⟩
  have hpuncture : ∃ b : S, b ≠ p ∧ b ≠ q ∧ (b ∉ U ∨ U = Set.univ) := by
    by_cases he : ∃ b, b ∉ U
    · obtain ⟨b, hb⟩ := he
      exact ⟨b, fun h => hb (h ▸ hpU), fun h => hb (h ▸ hqU), Or.inl hb⟩
    · have huall : U = Set.univ := Set.eq_univ_of_forall (by
        intro x
        by_contra hx
        exact he ⟨x, hx⟩)
      have hex : ∃ b ∈ M.cover.branch, b ≠ p ∧ b ≠ q := by
        by_contra hn
        have hsub : M.cover.branch ⊆ ({p, q} : Finset S) := by
          intro b hb
          by_cases hbp : b = p
          · simp [hbp]
          · have hbq : b = q := by
              by_contra hbq
              exact hn ⟨b, hb, hbp, hbq⟩
            simp [hbq]
        have hcard := Finset.card_le_card hsub
        have hpair : ({p, q} : Finset S).card ≤ 2 :=
          (Finset.card_insert_le _ _).trans (by simp)
        rw [M.cover.branch_card] at hcard
        omega
      obtain ⟨b, hb, hbp, hbq⟩ := hex
      exact ⟨b, hbp, hbq, Or.inr huall⟩
  obtain ⟨b, hbp, hbq, hb⟩ := hpuncture
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let e := stereographic' 2 (M.sphere b)
  let W : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    e.source ∩ M.sphere '' U
  let Ω : Set Schoenflies.Plane := e '' W
  have hWopen : IsOpen W := e.open_source.inter (M.sphere.isOpenMap U hU)
  have hΩopen : IsOpen Ω := e.isOpen_image_of_subset_source hWopen Set.inter_subset_left
  have hsource (x : S) : M.sphere x ∈ e.source ↔ x ≠ b := by
    simp [e, M.sphere.injective.eq_iff]
  have hΩconn : IsPreconnected Ω := by
    rcases hb with hb | huall
    · have hWeq : W = M.sphere '' U := by
        apply Set.inter_eq_right.mpr
        rintro _ ⟨x, hx, rfl⟩
        exact (hsource x).mpr (fun he => hb (he ▸ hx))
      have hc : IsConnected W := by
        rw [hWeq]
        exact hUc.image M.sphere M.sphere.continuous.continuousOn
      exact hc.isPreconnected.image e (e.continuousOn.mono Set.inter_subset_left)
    · have hWeq : W = e.source := by simp [W, huall, M.sphere.surjective.range_eq]
      have hΩeq : Ω = Set.univ := by
        dsimp [Ω]
        rw [hWeq, e.image_source_eq_target]
        simp [e]
      rw [hΩeq]
      exact isPreconnected_univ
  have hpΩ : e (M.sphere p) ∈ Ω :=
    ⟨M.sphere p, ⟨(hsource p).mpr hbp.symm, ⟨p, hpU, rfl⟩⟩, rfl⟩
  have hqΩ : e (M.sphere q) ∈ Ω :=
    ⟨M.sphere q, ⟨(hsource q).mpr hbq.symm, ⟨q, hqU, rfl⟩⟩, rfl⟩
  have hpqΩ : e (M.sphere p) ≠ e (M.sphere q) := by
    intro he
    exact hpq (M.sphere.injective (e.injOn
      ((hsource p).mpr hbp.symm) ((hsource q).mpr hbq.symm) he))
  obtain ⟨A, hAsub, _, g, hgcont, hginj, hgimage, hg0, hg1⟩ :=
    Schoenflies.exists_simple_arc_of_isPreconnected hΩopen hΩconn hpΩ hqΩ hpqΩ
  have hgΩ (t : Interval) : g t ∈ Ω := hAsub (hgimage ▸ ⟨t, t.property, rfl⟩)
  have hgTarget (t : Interval) : g t ∈ e.target := by simp [e]
  let f : C(Interval, S) := ⟨fun t => M.sphere.symm (e.symm (g t)),
    M.sphere.symm.continuous.comp (e.symm.continuousOn.comp_continuous
      (continuousOn_iff_continuous_domRestrict.mp hgcont) hgTarget)⟩
  have hfi : Function.Injective f := by
    intro t u htu
    apply Subtype.ext
    apply hginj t.property u.property
    exact e.symm.injOn (hgTarget t) (hgTarget u) (M.sphere.symm.injective htu)
  have hf0 : f 0 = p := by
    change M.sphere.symm (e.symm (g 0)) = p
    rw [hg0, e.left_inv ((hsource p).mpr hbp.symm), M.sphere.symm_apply_apply]
  have hf1 : f 1 = q := by
    change M.sphere.symm (e.symm (g 1)) = q
    rw [hg1, e.left_inv ((hsource q).mpr hbq.symm), M.sphere.symm_apply_apply]
  have hfU : Set.range f ⊆ U := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨z, ⟨hzsrc, x, hxU, hxz⟩, hzg⟩ := hgΩ t
    have hback : e.symm (g t) = z := by rw [← hzg, e.left_inv hzsrc]
    change M.sphere.symm (e.symm (g t)) ∈ U
    rw [hback, ← hxz, M.sphere.symm_apply_apply]
    exact hxU
  apply htrim f hfi
  · rw [hf0]; exact hp
  · rw [hf1]; exact hq
  · exact hfU
end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.region_not_plane_of_essential_curve

#print axioms CurveComplex.HyperellipticModel.nonloop_arc_inside_marked_region


open Set Topology
open scoped Manifold
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain
set_option linter.style.haveILetI false
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
theorem circle33_preimage_essential (M : HyperellipticModel E S)
    (a : Circle33 M) (c : Curve E)
    (hc : c.image = M.cover.projection ⁻¹' a.val.image) : Essential c := by
  classical
  have hdisc (c : Curve E) (hc : BoundsDisc c) (U V : Set E)
      (hU : IsOpen U) (hV : IsOpen V)
      (hUc : IsConnected U) (hVc : IsConnected V)
      (hUV : Disjoint U V) (hUVcover : U ∪ V = c.imageᶜ) :
      Nonempty (U ≃ₜ Schoenflies.Plane) ∨ Nonempty (V ≃ₜ Schoenflies.Plane) := by
        as_aux_lemma =>
      classical
      letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
      obtain ⟨f, hf, hboundary⟩ := hc
      let P := EuclideanSpace ℝ (Fin 2)
      let B := Metric.closedBall (0 : P) 1
      let O := Metric.ball (0 : P) 1
      let A : Set B := {x | (x : P) ∈ O}
      let C : Set B := {x | (x : P) ∈ Metric.sphere (0 : P) 1}
      have hfnot : ¬ Function.Surjective f := by
        intro hsurj
        let h : B ≃ₜ E := IsHomeomorph.homeomorph f
          (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hf, hsurj⟩)
        obtain ⟨p, hp⟩ := NormedSpace.sphere_nonempty (E := P).mpr
          (show (0 : ℝ) ≤ 1 by norm_num)
        let pB : B := ⟨p, Metric.sphere_subset_closedBall hp⟩
        let e := chartAt P (h pB)
        let g : e.target → P := fun y => (h.symm (e.symm y) : P)
        have hgcont : Continuous g := continuous_subtype_val.comp
          (h.symm.continuous.comp
            (e.symm.continuousOn.comp_continuous continuous_subtype_val
              (fun y => y.property)))
        have hginj : Function.Injective g := by
          intro y z hyz
          have hhs : h.symm (e.symm y) = h.symm (e.symm z) := Subtype.ext hyz
          exact Subtype.ext (e.symm.injOn y.property z.property (h.symm.injective hhs))
        have hopen : IsOpen (Set.range g) :=
          isOpen_range_of_isOpen_of_continuous_injective
            (modelWithCornersSelf ℝ P) e.open_target g hgcont hginj
        have hpim : p ∈ Set.range g := by
          refine ⟨⟨e (h pB), e.map_source (mem_chart_source P (h pB))⟩, ?_⟩
          dsimp [g]
          rw [e.left_inv (mem_chart_source P (h pB)), h.symm_apply_apply]
        have hsub : Set.range g ⊆ B := by
          rintro _ ⟨y, rfl⟩
          exact (h.symm (e.symm y)).property
        have hpint : p ∈ interior B := (hopen.subset_interior_iff.mpr hsub) hpim
        rw [interior_closedBall (0 : P) (by norm_num : (1 : ℝ) ≠ 0)] at hpint
        exact (ne_of_lt hpint) hp
      simp only [Function.Surjective, not_forall, not_exists] at hfnot
      obtain ⟨x, hx⟩ := hfnot
      have hnV : (Set.range f)ᶜ.Nonempty := ⟨x, by rintro ⟨y, hy⟩; exact hx y hy⟩
      have hopenV : IsOpen (Set.range f)ᶜ :=
        (isCompact_range f.continuous).isClosed.isOpen_compl
      let g : O → E := fun x => f ⟨x, Metric.ball_subset_closedBall x.property⟩
      have hgcont : Continuous g := f.continuous.comp
        (continuous_subtype_val.subtype_mk _)
      have hginj : Function.Injective g := by
        intro x y hxy
        have heq : (⟨x, Metric.ball_subset_closedBall x.property⟩ : B) =
            ⟨y, Metric.ball_subset_closedBall y.property⟩ := hf.injective hxy
        exact Subtype.ext (congrArg (fun z : B => (z : P)) heq)
      have hgim : Set.range g = f '' A := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨⟨x, Metric.ball_subset_closedBall x.property⟩, x.property, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl⟩
      have hopenU : IsOpen (f '' A) := by
        rw [← hgim]
        exact isOpen_range_of_isOpen_of_continuous_injective
          (modelWithCornersSelf ℝ P) Metric.isOpen_ball g hgcont hginj
      have hnU : (f '' A).Nonempty := by
        refine ⟨f ⟨0, by simp [B]⟩, ⟨0, by simp [B]⟩, ?_, rfl⟩
        change dist (0 : P) 0 < 1
        simp
      have hdisj : Disjoint (f '' A) (Set.range f)ᶜ := by
        apply Set.disjoint_left.mpr
        rintro _ ⟨y, hy, rfl⟩ hx
        exact hx ⟨y, rfl⟩
      have hAcompl : f '' A ⊆ c.imageᶜ := by
        rintro _ ⟨y, hy, rfl⟩ hcy
        rw [← hboundary] at hcy
        obtain ⟨z, hz, hfz⟩ := hcy
        have hzy : z = y := hf.injective hfz
        subst z
        exact (ne_of_lt hy) hz
      have hBcompl : (Set.range f)ᶜ ⊆ c.imageᶜ := by
        intro y hy hcy
        rw [← hboundary] at hcy
        obtain ⟨z, hz, hfz⟩ := hcy
        exact hy ⟨z, hfz⟩
      have hcover : c.imageᶜ ⊆ f '' A ∪ (Set.range f)ᶜ := by
        intro y hy
        by_cases hr : y ∈ Set.range f
        · obtain ⟨z, rfl⟩ := hr
          left
          refine ⟨z, ?_, rfl⟩
          have hne : (z : P) ∉ Metric.sphere (0 : P) 1 := by
            intro hz
            exact hy (hboundary ▸ Set.mem_image_of_mem f hz)
          have hzle := z.property
          change dist (z : P) 0 ≤ 1 at hzle
          change dist (z : P) 0 < 1
          exact lt_of_le_of_ne hzle hne
        · exact Or.inr hr
      letI : ConnectedSpace O := (Homeomorph.unitBall (E := P)).surjective.connectedSpace
        (Homeomorph.unitBall (E := P)).continuous
      have hAc : IsConnected (f '' A) := by
        rw [← hgim]
        exact isConnected_range hgcont
      have hAsub : f '' A ⊆ U ∪ V := by rw [hUVcover]; exact hAcompl
      have hUs : U ⊆ f '' A ∪ (Set.range f)ᶜ := by
        intro x hx
        exact hcover (hUVcover ▸ Or.inl hx)
      have hVs : V ⊆ f '' A ∪ (Set.range f)ᶜ := by
        intro x hx
        exact hcover (hUVcover ▸ Or.inr hx)
      have hgiembed : IsEmbedding g := by
        apply hf.comp
        apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
        exact Topology.IsEmbedding.subtypeVal
      have hplane : (f '' A) ≃ₜ P :=
        (Homeomorph.setCongr hgim.symm).trans
          (hgiembed.toHomeomorph.symm.trans (Homeomorph.unitBall (E := P)).symm)
      rcases hAc.isPreconnected.subset_or_subset hU hV hUV hAsub with hAU | hAV
      · have hUA : U ⊆ f '' A := by
          rcases hUc.isPreconnected.subset_or_subset hopenU hopenV hdisj hUs with h | h
          · exact h
          · obtain ⟨y, hy⟩ := hnU
            exact False.elim (Set.disjoint_left.mp hdisj hy (h (hAU hy)))
        exact Or.inl ⟨(Homeomorph.setCongr (Set.Subset.antisymm hUA hAU)).trans hplane⟩
      · have hVA : V ⊆ f '' A := by
          rcases hVc.isPreconnected.subset_or_subset hopenU hopenV hdisj hVs with h | h
          · exact h
          · obtain ⟨y, hy⟩ := hnU
            exact False.elim (Set.disjoint_left.mp hdisj hy (h (hAV hy)))
        exact Or.inr ⟨(Homeomorph.setCongr (Set.Subset.antisymm hVA hAV)).trans hplane⟩
  have hconnpre (D : Set S) (hD : IsConnected D) (b : S)
      (hb : b ∈ M.cover.branch) (hbD : b ∈ D) :
      IsConnected (M.cover.projection ⁻¹' D) := by
        as_aux_lemma =>
      letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
      letI : T2Space S := M.sphere.symm.t2Space
      have hopen : IsOpenMap M.cover.projection := by
          letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
          letI : T2Space S := M.sphere.symm.t2Space
          have hcl : IsClosedMap M.cover.projection := M.cover.projection_continuous.isClosedMap
          have hq := hcl.isQuotientMap M.cover.projection_continuous M.cover.projection_surjective
          intro U hU
          rw [← hq.isCoinducing.isOpen_preimage]
          have heq : M.cover.projection ⁻¹' (M.cover.projection '' U) =
              U ∪ M.cover.deck ⁻¹' U := by
            ext x
            constructor
            · rintro ⟨y, hy, hxy⟩
              rcases (M.cover.fiber_pair x y).mp hxy.symm with h | h
              · exact Or.inl (h ▸ hy)
              · exact Or.inr (by change M.cover.deck x ∈ U; simpa only [h] using hy)
            · rintro (hx | hx)
              · exact ⟨x, hx, rfl⟩
              · exact ⟨M.cover.deck x, hx, M.cover.projection_deck x⟩
          rw [heq]
          exact hU.union (hU.preimage M.cover.deck.continuous)
      have hclosed : IsClosedMap M.cover.projection :=
        M.cover.projection_continuous.isClosedMap
      let f := D.restrictPreimage M.cover.projection
      have hfopen : IsOpenMap f := hopen.restrictPreimage D
      have hfclosed : IsClosedMap f := hclosed.restrictPreimage D
      letI : ConnectedSpace D := isConnected_iff_connectedSpace.mp hD
      obtain ⟨w, hw, huniq⟩ := M.cover.branch_fiber_unique hb
      have hwD : w ∈ M.cover.projection ⁻¹' D := by change M.cover.projection w ∈ D; rw [hw]; exact hbD
      letI : Nonempty (M.cover.projection ⁻¹' D) := ⟨⟨w, hwD⟩⟩
      apply isConnected_iff_connectedSpace.mpr
      apply connectedSpace_iff_univ.mpr
      refine ⟨Set.univ_nonempty, ?_⟩
      by_contra h
      obtain ⟨U, V, hU, hV, hnU, hnV, hd, huv⟩ :=
        isClopen_univ.not_isPreconnected_iff.mp h
      have hUi : f '' U = Set.univ :=
        IsClopen.eq_univ ⟨hfclosed U hU.isClosed, hfopen U hU.isOpen⟩ (hnU.image f)
      have hVi : f '' V = Set.univ :=
        IsClopen.eq_univ ⟨hfclosed V hV.isClosed, hfopen V hV.isOpen⟩ (hnV.image f)
      obtain ⟨u, hu, hueq⟩ := (hUi.symm ▸ Set.mem_univ (⟨b, hbD⟩ : D))
      obtain ⟨v, hv, hveq⟩ := (hVi.symm ▸ Set.mem_univ (⟨b, hbD⟩ : D))
      have huval : (u : E) = w := huniq u.val (congrArg Subtype.val hueq)
      have hvval : (v : E) = w := huniq v.val (congrArg Subtype.val hveq)
      have huv' : u = v := Subtype.ext (huval.trans hvval.symm)
      exact Set.disjoint_left.mp hd hu (huv' ▸ hv)
  have hside (D : Set S) (hDo : IsOpen D) (hDc : IsConnected D)
      (hcard : (M.cover.branch.filter (· ∈ D)).card = 3) :
      IsConnected (M.cover.projection ⁻¹' D) ∧
        ¬ Nonempty ((M.cover.projection ⁻¹' D) ≃ₜ Schoenflies.Plane) := by
    let F := M.cover.branch.filter (· ∈ D)
    have hFcard : F.card = 3 := hcard
    obtain ⟨p, hpF⟩ := Finset.card_pos.mp (show 0 < F.card by omega)
    obtain ⟨q, hqF, hqp⟩ := Finset.exists_mem_ne (show 1 < F.card by omega) p
    obtain ⟨hpB, hpD⟩ := Finset.mem_filter.mp hpF
    obtain ⟨hqB, hqD⟩ := Finset.mem_filter.mp hqF
    have hpreconn := hconnpre D hDc p hpB hpD
    obtain ⟨b, hbD⟩ := M.nonloop_arc_inside_marked_region D hDo hDc
      p q hpB hqB hpD hqD hqp.symm
    let e : EssentialCurve E :=
      ⟨(M.nonloop_arc_preimage_curve b).choose,
        M.nonloop_arc_preimage_essential b _ (M.nonloop_arc_preimage_curve b).choose_spec⟩
    have hesub : e.val.image ⊆ M.cover.projection ⁻¹' D := by
      change (M.nonloop_arc_preimage_curve b).choose.image ⊆ _
      rw [(M.nonloop_arc_preimage_curve b).choose_spec]
      exact Set.preimage_mono hbD
    exact ⟨hpreconn, region_not_plane_of_essential_curve _ e hesub⟩
  obtain ⟨U, V, hU, hV, hUc, hVc, _, _, hd, huv, hcardU, hcardV⟩ := a.property
  obtain ⟨hpreU, hnodiscU⟩ := hside U hU hUc hcardU
  obtain ⟨hpreV, hnodiscV⟩ := hside V hV hVc hcardV
  intro hcdisc
  have hprecover : (M.cover.projection ⁻¹' U) ∪ (M.cover.projection ⁻¹' V) = c.imageᶜ := by
    rw [← Set.preimage_union, huv, Set.preimage_compl, ← hc]
  rcases hdisc c hcdisc
    (M.cover.projection ⁻¹' U) (M.cover.projection ⁻¹' V)
    (hU.preimage M.cover.projection_continuous)
    (hV.preimage M.cover.projection_continuous)
    hpreU hpreV (hd.preimage M.cover.projection) hprecover with h | h
  · exact hnodiscU h
  · exact hnodiscV h
end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.circle33_preimage_essential
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
set_option maxHeartbeats 16000000
set_option linter.style.haveILetI false
/-- Source Lemma 4.2(ii): the full preimage is an essential simple closed curve. -/
theorem circle33_preimage_essential_curve (a : Circle33 M) :
    ∃ c : EssentialCurve E,
      c.val.image = M.cover.projection ⁻¹' a.val.image := by
  have hOdd (M : HyperellipticModel E S) (a : Circle33 M) :
      ∃ β : C(Interval,S), β 0 = β 1 ∧
        (∀ s t, β s = β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
        Set.range β = a.val.image ∧
        ∀ γ : C(Interval,E), (∀ t, M.cover.projection (γ t) = β t) →
          γ 1 = M.cover.deck (γ 0) := by
            as_aux_lemma =>
      have hSource (a : Circle33 M) :
          let R := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
          ∃ f : C(R,S), ∃ lo hi : Fin 3 → ℝ × ℝ,
            ∃ F : Fin 3 → C(Metric.closedBall (0 : Schoenflies.Plane) 1,S),
            ∃ m : Fin 3 → Metric.closedBall (0 : Schoenflies.Plane) 1,
              IsEmbedding f ∧ f '' {z : R | z.val ∈ frontier R} = a.val.image ∧
              (∀ i, (lo i).1 < (hi i).1 ∧ (lo i).2 < (hi i).2) ∧
    
            ((∃ k l : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),(k,(-1 : ℝ)),(l,(-1 : ℝ))] ∧ hi = ![(k,(1 : ℝ)),(l,(1 : ℝ)),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < l ∧ l < (1 : ℝ)) ∨
             (∃ k h : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),(k,(-1 : ℝ)),(k,h)] ∧ hi = ![(k,(1 : ℝ)),((1 : ℝ),h),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < (1 : ℝ) ∧ (-1 : ℝ) < h ∧ h < (1 : ℝ)) ∨
             (∃ k h : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),((-1 : ℝ),h),(k,(-1 : ℝ))] ∧ hi = ![(k,h),(k,(1 : ℝ)),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < (1 : ℝ) ∧ (-1 : ℝ) < h ∧ h < (1 : ℝ)) ∨
             (∃ k l : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),((-1 : ℝ),k),((-1 : ℝ),l)] ∧ hi = ![((1 : ℝ),k),((1 : ℝ),l),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < l ∧ l < (1 : ℝ))) ∧
              (∀ i, IsEmbedding (F i) ∧ ‖(m i).val‖ < 1 ∧
                (∀ z, F i z ∈ M.cover.branch ↔ z = m i) ∧
                F i '' {z | ‖z.val‖ = 1} = f '' {z : R | z.val ∈
                  frontier (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)}) := by
                    as_aux_lemma =>
          have hDiscTree (a : Circle33 M) :
            let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
              (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                (EuclideanSpace.equiv (Fin 2) ℝ).symm
            let K := e '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
            ∃ f : C(K,S), ∃ lo hi : Fin 3 → ℝ × ℝ,
              ∃ F : Fin 3 → C(Metric.closedBall (0 : Schoenflies.Plane) 1,S),
              ∃ m : Fin 3 → Metric.closedBall (0 : Schoenflies.Plane) 1,
                IsEmbedding f ∧ f '' {z : K | z.val ∈ frontier K} = a.val.image ∧
                (∀ i, (lo i).1 < (hi i).1 ∧ (lo i).2 < (hi i).2) ∧
                ((e '' (Icc (lo 0).1 (hi 0).1 ×ˢ Icc (lo 0).2 (hi 0).2)) ∪
                  (e '' (Icc (lo 1).1 (hi 1).1 ×ˢ Icc (lo 1).2 (hi 1).2))) ∪
                  (e '' (Icc (lo 2).1 (hi 2).1 ×ˢ Icc (lo 2).2 (hi 2).2)) = K ∧
              ((∃ k l : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),(k,(-1 : ℝ)),(l,(-1 : ℝ))] ∧ hi = ![(k,(1 : ℝ)),(l,(1 : ℝ)),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < l ∧ l < (1 : ℝ)) ∨
               (∃ k h : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),(k,(-1 : ℝ)),(k,h)] ∧ hi = ![(k,(1 : ℝ)),((1 : ℝ),h),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < (1 : ℝ) ∧ (-1 : ℝ) < h ∧ h < (1 : ℝ)) ∨
               (∃ k h : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),((-1 : ℝ),h),(k,(-1 : ℝ))] ∧ hi = ![(k,h),(k,(1 : ℝ)),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < (1 : ℝ) ∧ (-1 : ℝ) < h ∧ h < (1 : ℝ)) ∨
               (∃ k l : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),((-1 : ℝ),k),((-1 : ℝ),l)] ∧ hi = ![((1 : ℝ),k),((1 : ℝ),l),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < l ∧ l < (1 : ℝ))) ∧
                (∀ i, IsEmbedding (F i) ∧ ‖(m i).val‖ < 1 ∧
                  (∀ z, F i z ∈ M.cover.branch ↔ z = m i) ∧
                  F i '' {z | ‖z.val‖ = 1} = f '' {z : K | z.val ∈
                    frontier (e '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2))}) := by
                      as_aux_lemma =>
              have hCells (a : Circle33 M) :
                let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                    (EuclideanSpace.equiv (Fin 2) ℝ).symm
                let K := e '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
                ∃ f : C(K,S), ∃ p lo hi : Fin 3 → ℝ × ℝ,
                  IsEmbedding f ∧ f '' {z : K | z.val ∈ frontier K} = a.val.image ∧
                  (∀ i, (lo i).1 < (hi i).1 ∧ (lo i).2 < (hi i).2) ∧
                  ((e '' (Icc (lo 0).1 (hi 0).1 ×ˢ Icc (lo 0).2 (hi 0).2)) ∪
                    (e '' (Icc (lo 1).1 (hi 1).1 ×ˢ Icc (lo 1).2 (hi 1).2))) ∪
                    (e '' (Icc (lo 2).1 (hi 2).1 ×ˢ Icc (lo 2).2 (hi 2).2)) = K ∧
                  ((∃ k l : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),(k,(-1 : ℝ)),(l,(-1 : ℝ))] ∧ hi = ![(k,(1 : ℝ)),(l,(1 : ℝ)),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < l ∧ l < (1 : ℝ)) ∨
                   (∃ k h : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),(k,(-1 : ℝ)),(k,h)] ∧ hi = ![(k,(1 : ℝ)),((1 : ℝ),h),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < (1 : ℝ) ∧ (-1 : ℝ) < h ∧ h < (1 : ℝ)) ∨
                   (∃ k h : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),((-1 : ℝ),h),(k,(-1 : ℝ))] ∧ hi = ![(k,h),(k,(1 : ℝ)),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < (1 : ℝ) ∧ (-1 : ℝ) < h ∧ h < (1 : ℝ)) ∨
                   (∃ k l : ℝ, lo = ![((-1 : ℝ),(-1 : ℝ)),((-1 : ℝ),k),((-1 : ℝ),l)] ∧ hi = ![((1 : ℝ),k),((1 : ℝ),l),((1 : ℝ),(1 : ℝ))] ∧ (-1 : ℝ) < k ∧ k < l ∧ l < (1 : ℝ))) ∧
                  (∀ i, ∃ hsub : (e '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)) ⊆ K,
                    ∃ fc : C(e '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2),S),
                      IsEmbedding fc ∧ (∀ z, fc z = f ⟨z.val,hsub z.property⟩) ∧
                      ∃ m, m.val = e (p i) ∧ m.val ∈ interior (e '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)) ∧
                        (∀ z, fc z ∈ M.cover.branch ↔ z = m)) := by
                          as_aux_lemma =>
                  have hSquare (a : Circle33 M) : (by
                  classical
                  exact
                    let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                        (EuclideanSpace.equiv (Fin 2) ℝ).symm
                    let K := e '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
                    ∃ f : C(K, S), IsEmbedding f ∧
                      (∀ x : K, f x ∈ a.val.image ↔ (x : Schoenflies.Plane) ∈ frontier K) ∧
                      f '' {x : K | (x : Schoenflies.Plane) ∈ frontier K} = a.val.image ∧
                      (M.cover.branch.filter (fun b => b ∈ f '' {x : K | (x : Schoenflies.Plane) ∈ interior K})).card = 3) := by
                    have hdisc (a : Circle33 M) : (by
                    classical
                    exact ∃ f : C(Metric.closedBall (0 : Schoenflies.Plane) 1, S),
                        IsEmbedding f ∧
                        (∀ x, f x ∈ a.val.image ↔ ‖x.val‖ = 1) ∧
                        f '' {x | ‖x.val‖ = 1} = a.val.image ∧
                        (M.cover.branch.filter (fun b => b ∈ f '' {x | ‖x.val‖ < 1})).card = 3) := by
                      classical
                      letI : T2Space S := M.sphere.symm.t2Space
                      obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [M.cover.branch_card]; norm_num)
                      have hpout : p ∉ a.val.image := fun h => Set.disjoint_left.mp a.val.avoids_branch h hp
                      let g : Circle → Schoenflies.Plane := fun z =>
                        M.puncturedPlane p ⟨a.val.curve.map z, fun he => hpout (he ▸ Set.mem_range_self z)⟩
                      have hgcont : Continuous g := (M.puncturedPlane p).continuous.comp
                        (a.val.curve.embedded.continuous.subtype_mk _)
                      have hginj : Function.Injective g := by
                        intro z w h
                        exact a.val.curve.embedded.injective (congrArg Subtype.val ((M.puncturedPlane p).injective h))
                      let C := Set.range g
                      have hC : Schoenflies.IsJordanCurve C := isJordanCurve_range_of_isEmbedding_circle ⟨g, hgcont⟩
                        (hgcont.isClosedEmbedding hginj).isEmbedding
                      let F := M.planeToSphere p
                      have hF := M.planeToSphere_isOpenEmbedding p
                      have hCimage : F '' C = a.val.image := by
                        ext x
                        constructor
                        · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
                          have he : F (g w) = a.val.curve.map w := by
                            exact congrArg Subtype.val ((M.puncturedPlane p).symm_apply_apply _)
                          exact he.symm ▸ Set.mem_range_self w
                        · rintro ⟨w, rfl⟩
                          refine ⟨g w, Set.mem_range_self w, ?_⟩
                          exact congrArg Subtype.val ((M.puncturedPlane p).symm_apply_apply _)
                      have hsep := Schoenflies.jordan_curve_theorem hC
                      let I := F '' Schoenflies.inside C
                      have hIopen : IsOpen I := hF.isOpenMap _ (Schoenflies.isOpen_inside hC.isClosed)
                      have hIconn : IsConnected I := hsep.isConnected_inside.image F hF.continuous.continuousOn
                      have hIavoid : Disjoint I a.val.image := by
                        rw [← hCimage]
                        apply Set.disjoint_left.mpr
                        rintro y ⟨z,hz,rfl⟩ ⟨w,hw,hwz⟩
                        have hzw := hF.injective hwz
                        exact Schoenflies.inside_subset_compl hz (hzw ▸ hw)
                      have hclI : closure I = I ∪ a.val.image := by
                        have hcompact : IsCompact (closure (Schoenflies.inside C)) :=
                          Metric.isCompact_of_isClosed_isBounded isClosed_closure hsep.isBounded_inside.closure
                        have heq : closure I = F '' closure (Schoenflies.inside C) := by
                          apply Set.Subset.antisymm
                          · exact closure_minimal (Set.image_mono subset_closure) (hcompact.image hF.continuous).isClosed
                          · exact image_closure_subset_closure_image hF.continuous
                        rw [heq, (Schoenflies.IsRegionOf.inside C).closure_eq hsep, Set.image_union, hCimage]
                      let J := (closure I)ᶜ
                      have hJopen : IsOpen J := isClosed_closure.isOpen_compl
                      have hIJdisj : Disjoint I J := Set.disjoint_left.mpr (fun _ hi hj => hj (subset_closure hi))
                      have hIJcover : I ∪ J = a.val.imageᶜ := by
                        rw [show J = (I ∪ a.val.image)ᶜ from congrArg compl hclI]
                        ext x
                        have hd : x ∈ I → x ∉ a.val.image := fun hi => Set.disjoint_left.mp hIavoid hi
                        simp only [mem_union, mem_compl_iff]
                        tauto
                      obtain ⟨U,V,hUo,hVo,hUc,hVc,hUn,hVn,hUV,hUVcover,hUcard,hVcard⟩ := a.property
                      have hIsub : I ⊆ U ∪ V := by
                        rw [hUVcover]
                        intro x hx
                        exact Set.disjoint_left.mp hIavoid hx
                      have hUsub : U ⊆ I ∪ J := by
                        rw [hIJcover, ← hUVcover]
                        exact subset_union_left
                      have hVsub : V ⊆ I ∪ J := by
                        rw [hIJcover, ← hUVcover]
                        exact subset_union_right
                      have hIEq : I = U ∨ I = V := by
                        rcases hIconn.isPreconnected.subset_or_subset hUo hVo hUV hIsub with hIU | hIV
                        · left
                          apply Set.Subset.antisymm hIU
                          rcases hUc.isPreconnected.subset_or_subset hIopen hJopen hIJdisj hUsub with hUI | hUJ
                          · exact hUI
                          · obtain ⟨x,hx⟩ := hIconn.nonempty
                            exact False.elim (Set.disjoint_left.mp hIJdisj hx (hUJ (hIU hx)))
                        · right
                          apply Set.Subset.antisymm hIV
                          rcases hVc.isPreconnected.subset_or_subset hIopen hJopen hIJdisj hVsub with hVI | hVJ
                          · exact hVI
                          · obtain ⟨x,hx⟩ := hIconn.nonempty
                            exact False.elim (Set.disjoint_left.mp hIJdisj hx (hVJ (hIV hx)))
                      obtain ⟨d,hdb,hdi⟩ := SpherePort.plane_inside_closed_disc_with_boundary C hC
                      let f : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S) :=
                        ⟨fun x => F (d x).val, hF.continuous.comp (continuous_subtype_val.comp d.continuous)⟩
                      have hf : IsEmbedding f := hF.isEmbedding.comp (IsEmbedding.subtypeVal.comp d.isEmbedding)
                      have hboundary (x) : f x ∈ a.val.image ↔ ‖x.val‖ = 1 := by
                        rw [← hCimage]
                        change F (d x).val ∈ F '' C ↔ _
                        have himage : F (d x).val ∈ F '' C ↔ (d x).val ∈ C := by
                          constructor
                          · rintro ⟨z,hz,he⟩
                            exact hF.injective he ▸ hz
                          · intro hx
                            exact ⟨(d x).val,hx,rfl⟩
                        rw [himage]
                        exact hdb x
                      have hinterior : f '' {x | ‖x.val‖ < 1} = I := by
                        ext y
                        constructor
                        · rintro ⟨x,hx,rfl⟩
                          exact ⟨(d x).val, (hdi x).mpr hx, rfl⟩
                        · rintro ⟨z,hz,rfl⟩
                          let zz : closure (Schoenflies.inside C) := ⟨z, subset_closure hz⟩
                          refine ⟨d.symm zz, ?_, ?_⟩
                          · apply (hdi _).mp
                            simpa [zz] using hz
                          · change F (d (d.symm zz)).val = F z
                            rw [d.apply_symm_apply]
                      refine ⟨f,hf,hboundary,?_,?_⟩
                      · apply Set.Subset.antisymm
                        · rintro y ⟨x,hx,rfl⟩
                          exact (hboundary x).mpr hx
                        · intro y hy
                          have hyC : y ∈ F '' C := hCimage.symm ▸ hy
                          rcases hyC with ⟨z,hz,rfl⟩
                          let zz : closure (Schoenflies.inside C) :=
                            ⟨z, (Schoenflies.IsRegionOf.inside C).subset_closure hsep hz⟩
                          refine ⟨d.symm zz, ?_, ?_⟩
                          · apply (hdb _).mp
                            simpa [zz] using hz
                          · change F (d (d.symm zz)).val = F z
                            rw [d.apply_symm_apply]
                      · rw [hinterior]
                        rcases hIEq with h | h
                        · simpa [h] using hUcard
                        · simpa [h] using hVcard
                    have hrect (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
                      let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                          (EuclideanSpace.equiv (Fin 2) ℝ).symm
                      let K := e '' (Icc a b ×ˢ Icc c d)
                      ∃ h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K,
                        (∀ x, (h x : Schoenflies.Plane) ∈ interior K ↔ ‖x.val‖ < 1) ∧
                        (∀ x, (h x : Schoenflies.Plane) ∈ frontier K ↔ ‖x.val‖ = 1) := by
                          as_aux_lemma =>
                        dsimp only
                        let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                            (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                              (EuclideanSpace.equiv (Fin 2) ℝ).symm
                        let K := e '' (Icc a b ×ˢ Icc c d)
                        change ∃ h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K, _
                        have hcompact : IsCompact K :=
                          (isCompact_Icc.prod isCompact_Icc).image e.continuous
                        have hconvex : Convex ℝ K :=
                          ((convex_Icc a b).prod (convex_Icc c d)).linear_image e.toLinearEquiv.toLinearMap
                        have hne : (interior K).Nonempty := by
                          have hm : ((a + b) / 2, (c + d) / 2) ∈ interior (Icc a b ×ˢ Icc c d) := by
                            rw [interior_prod_eq, interior_Icc, interior_Icc]
                            exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
                          refine ⟨e ((a + b) / 2, (c + d) / 2), ?_⟩
                          change e.toHomeomorph ((a + b) / 2, (c + d) / 2) ∈
                            interior (e.toHomeomorph '' (Icc a b ×ˢ Icc c d))
                          rw [← e.toHomeomorph.image_interior]
                          exact mem_image_of_mem e hm
                        obtain ⟨g, hgi, hgc, hgf⟩ :=
                          exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconvex hne hcompact.isBounded
                        have hgK : g '' K = Metric.closedBall (0 : Schoenflies.Plane) 1 := by
                          simpa [hcompact.isClosed.closure_eq] using hgc
                        let h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K :=
                          (Homeomorph.sets g (by
                            ext x
                            constructor
                            · intro hx
                              rw [← hgK]
                              exact mem_image_of_mem g hx
                            · intro hx
                              rw [← hgK] at hx
                              rcases hx with ⟨y, hy, hxy⟩
                              exact g.injective hxy ▸ hy)).symm
                        refine ⟨h, ?_, ?_⟩
                        · intro x
                          change g.symm x.val ∈ interior K ↔ ‖x.val‖ < 1
                          rw [← mem_ball_zero_iff]
                          constructor
                          · intro hx
                            rw [← hgi]
                            exact ⟨g.symm x.val, hx, g.apply_symm_apply x.val⟩
                          · intro hx
                            rw [← hgi] at hx
                            rcases hx with ⟨y, hy, hyx⟩
                            simpa [← hyx] using hy
                        · intro x
                          change g.symm x.val ∈ frontier K ↔ ‖x.val‖ = 1
                          rw [← dist_zero_right x.val]
                          change g.symm x.val ∈ frontier K ↔ x.val ∈ Metric.sphere (0 : Schoenflies.Plane) 1
                          constructor
                          · intro hx
                            rw [← hgf]
                            exact ⟨g.symm x.val, hx, g.apply_symm_apply x.val⟩
                          · intro hx
                            rw [← hgf] at hx
                            rcases hx with ⟨y, hy, hyx⟩
                            simpa [← hyx] using hy
                    classical
                    dsimp only
                    let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                          (EuclideanSpace.equiv (Fin 2) ℝ).symm
                    let K := e '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
                    obtain ⟨fd,hfd,hdb,hdbrange,hdcard⟩ := hdisc a
                    obtain ⟨h,hi,hb⟩ := hrect (-1) 1 (-1) 1 (by norm_num) (by norm_num)
                    let f : C(K,S) := fd.comp ⟨h.symm, h.symm.continuous⟩
                    have hboundary (z : K) : f z ∈ a.val.image ↔ (z : Schoenflies.Plane) ∈ frontier K := by
                      change fd (h.symm z) ∈ a.val.image ↔ _
                      rw [hdb, ← hb]
                      rw [h.apply_symm_apply]
                    have hbrange : f '' {z : K | (z : Schoenflies.Plane) ∈ frontier K} = a.val.image := by
                      apply Set.Subset.antisymm
                      · rintro y ⟨z,hz,rfl⟩
                        exact (hboundary z).mpr hz
                      · intro y hy
                        rcases (Set.ext_iff.mp hdbrange y).mpr hy with ⟨x,hx,hxy⟩
                        refine ⟨h x,(hb x).mpr hx,?_⟩
                        change fd (h.symm (h x)) = y
                        rw [h.symm_apply_apply]
                        exact hxy
                    have hirange : f '' {z : K | (z : Schoenflies.Plane) ∈ interior K} =
                        fd '' {x | ‖x.val‖ < 1} := by
                      ext y
                      constructor
                      · rintro ⟨z,hz,rfl⟩
                        refine ⟨h.symm z,?_,rfl⟩
                        apply (hi _).mp
                        change ((h (h.symm z)) : Schoenflies.Plane) ∈ interior K
                        rw [h.apply_symm_apply]
                        exact hz
                      · rintro ⟨x,hx,rfl⟩
                        refine ⟨h x,(hi x).mpr hx,?_⟩
                        change fd (h.symm (h x)) = fd x
                        rw [h.symm_apply_apply]
                    refine ⟨f,hfd.comp h.symm.isEmbedding,hboundary,hbrange,?_⟩
                    rw [hirange]
                    exact hdcard
                  have hCoords (a b c d : ℝ) : (by
                  classical
                  exact
                    let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                        (EuclideanSpace.equiv (Fin 2) ℝ).symm
                    let K := e '' (Icc a b ×ˢ Icc c d)
                    ∀ (f : C(K,S)), IsEmbedding f →
                      (∀ z : K, z.val ∈ frontier K → f z ∉ M.cover.branch) →
                      (M.cover.branch.filter (fun b => b ∈ f '' {z : K | z.val ∈ interior K})).card = 3 →
                      ∃ s : Finset (ℝ × ℝ), s.card = 3 ∧
                        (∀ z : K, f z ∈ M.cover.branch ↔ e.symm z.val ∈ s) ∧
                        (∀ z ∈ s, a < z.1 ∧ z.1 < b ∧ c < z.2 ∧ z.2 < d)) := by
                    have hparameters {X : Type} [TopologicalSpace X] (K : Set X) (hK : IsClosed K) (f : C(K,S)) (hf : IsEmbedding f)
                      (hboundary : ∀ z : K, z.val ∈ frontier K → f z ∉ M.cover.branch)
                      (hcard : (by classical exact
                        (M.cover.branch.filter (fun b => b ∈ f '' {z : K | z.val ∈ interior K})).card = 3)) :
                      ∃ s : Finset K, s.card = 3 ∧ (∀ z, f z ∈ M.cover.branch ↔ z ∈ s) ∧
                        (∀ z ∈ s, z.val ∈ interior K) := by
                      classical
                      have hInterior (z : K) (hz : f z ∈ M.cover.branch) : z.val ∈ interior K := by
                        by_contra hnot
                        apply hboundary z _ hz
                        exact ⟨hK.closure_eq.symm ▸ z.property,hnot⟩
                      let s := M.cover.branch.preimage f hf.injective.injOn
                      have hrange : M.cover.branch.filter (fun b => b ∈ Set.range f) =
                          M.cover.branch.filter (fun b => b ∈ f '' {z : K | z.val ∈ interior K}) := by
                        apply Finset.ext
                        intro b
                        simp only [Finset.mem_filter]
                        constructor
                        · rintro ⟨hb,z,rfl⟩
                          exact ⟨hb,z,hInterior z hb,rfl⟩
                        · rintro ⟨hb,z,hz,rfl⟩
                          exact ⟨hb,z,rfl⟩
                      refine ⟨s,?_,?_,?_⟩
                      · rw [Finset.card_preimage,hrange]
                        exact hcard
                      · intro z
                        simp [s]
                      · intro z hz
                        apply hInterior
                        simpa [s] using hz
                    classical
                    dsimp only
                    let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                          (EuclideanSpace.equiv (Fin 2) ℝ).symm
                    let K := e '' (Icc a b ×ˢ Icc c d)
                    change ∀ (f : C(K,S)), _
                    intro f hf hboundary hcard
                    have hKcompact : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image e.continuous
                    obtain ⟨t,htcard,htiff,htInterior⟩ := hparameters K hKcompact.isClosed f hf hboundary hcard
                    let toPair : K → ℝ × ℝ := fun z => e.symm z.val
                    have htoPairinj : Function.Injective toPair := by
                      intro z w h
                      exact Subtype.ext (e.symm.injective h)
                    let s := t.image toPair
                    refine ⟨s,?_,?_,?_⟩
                    · rw [Finset.card_image_of_injective _ htoPairinj]
                      exact htcard
                    · intro z
                      rw [htiff]
                      constructor
                      · intro hz
                        exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
                      · intro hz
                        rcases Finset.mem_image.mp hz with ⟨w,hw,hwe⟩
                        exact htoPairinj hwe ▸ hw
                    · intro z hz
                      rcases Finset.mem_image.mp hz with ⟨w,hw,rfl⟩
                      have hwi := htInterior w hw
                      change w.val ∈ interior (e.toHomeomorph '' (Icc a b ×ˢ Icc c d)) at hwi
                      rw [← e.toHomeomorph.image_interior] at hwi
                      rcases hwi with ⟨v,hv,hvw⟩
                      have hvEq : v = toPair w := by
                        apply e.injective
                        change e v = e (e.symm w.val)
                        rw [e.apply_symm_apply]
                        exact hvw
                      rw [hvEq,interior_prod_eq,interior_Icc,interior_Icc] at hv
                      exact ⟨hv.1.1,hv.1.2,hv.2.1,hv.2.2⟩
                  have hSort (a b c d : ℝ) (s : Finset (ℝ × ℝ)) (hs : s.card = 3)
                    (hbounds : ∀ z ∈ s, a < z.1 ∧ z.1 < b ∧ c < z.2 ∧ z.2 < d) :
                    ∃ p : Fin 3 → ℝ × ℝ, Set.range p = (s : Set (ℝ × ℝ)) ∧
                      toLex (p 0) < toLex (p 1) ∧ toLex (p 1) < toLex (p 2) ∧
                      (∀ i, a < (p i).1 ∧ (p i).1 < b ∧ c < (p i).2 ∧ (p i).2 < d) := by
                    classical
                    let t := s.map toLex.toEmbedding
                    have ht : t.card = 3 := by simpa [t] using hs
                    let e := t.orderEmbOfFin ht
                    let p : Fin 3 → ℝ × ℝ := fun i => ofLex (e i)
                    have hrange : Set.range p = (s : Set (ℝ × ℝ)) := by
                      ext z
                      constructor
                      · rintro ⟨i, rfl⟩
                        have hi := t.orderEmbOfFin_mem ht i
                        rcases Finset.mem_map.mp hi with ⟨w, hw, he⟩
                        have : w = p i := by
                          simpa [p, e] using congrArg ofLex he
                        simpa [← this] using hw
                      · intro hz
                        have htz : toLex z ∈ t := Finset.mem_map.mpr ⟨z, hz, rfl⟩
                        have htrange := t.range_orderEmbOfFin ht
                        change toLex z ∈ (t : Set (Lex (ℝ × ℝ))) at htz
                        rw [← htrange] at htz
                        rcases htz with ⟨i, hi⟩
                        exact ⟨i, by simpa [p, e] using congrArg ofLex hi⟩
                    refine ⟨p,hrange,?_,?_,?_⟩
                    · exact e.strictMono (by decide : (0 : Fin 3) < 1)
                    · exact e.strictMono (by decide : (1 : Fin 3) < 2)
                    · intro i
                      apply hbounds
                      have hpi : p i ∈ Set.range p := Set.mem_range_self i
                      rw [hrange] at hpi
                      exact hpi
                  have hPartition (a b c d : ℝ) (p : Fin 3 → ℝ × ℝ)
                    (h01 : toLex (p 0) < toLex (p 1)) (h12 : toLex (p 1) < toLex (p 2))
                    (hbound : ∀ i, a < (p i).1 ∧ (p i).1 < b ∧ c < (p i).2 ∧ (p i).2 < d) :
                    ∃ lo hi : Fin 3 → ℝ × ℝ,
                      (∀ i, (lo i).1 < (hi i).1 ∧ (lo i).2 < (hi i).2) ∧
                      (∀ i j, p j ∈ Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2 ↔ i = j) ∧
                      (∀ i, (lo i).1 < (p i).1 ∧ (p i).1 < (hi i).1 ∧
                        (lo i).2 < (p i).2 ∧ (p i).2 < (hi i).2) ∧
                      ((Icc (lo 0).1 (hi 0).1 ×ˢ Icc (lo 0).2 (hi 0).2) ∪
                        (Icc (lo 1).1 (hi 1).1 ×ˢ Icc (lo 1).2 (hi 1).2)) ∪
                        (Icc (lo 2).1 (hi 2).1 ×ˢ Icc (lo 2).2 (hi 2).2) = Icc a b ×ˢ Icc c d ∧
                      ((∃ k l : ℝ, lo = ![(a,c),(k,c),(l,c)] ∧ hi = ![(k,d),(l,d),(b,d)] ∧ a < k ∧ k < l ∧ l < b) ∨
                       (∃ k h : ℝ, lo = ![(a,c),(k,c),(k,h)] ∧ hi = ![(k,d),(b,h),(b,d)] ∧ a < k ∧ k < b ∧ c < h ∧ h < d) ∨
                       (∃ k h : ℝ, lo = ![(a,c),(a,h),(k,c)] ∧ hi = ![(k,h),(k,d),(b,d)] ∧ a < k ∧ k < b ∧ c < h ∧ h < d) ∨
                       (∃ k l : ℝ, lo = ![(a,c),(a,k),(a,l)] ∧ hi = ![(b,k),(b,l),(b,d)] ∧ c < k ∧ k < l ∧ l < d)) := by
                         as_aux_lemma =>
                      have hb0 := hbound 0
                      have hb1 := hbound 1
                      have hb2 := hbound 2
                      rw [Prod.Lex.toLex_lt_toLex] at h01 h12
                      rcases h01 with hx01 | ⟨hx01,hy01⟩ <;> rcases h12 with hx12 | ⟨hx12,hy12⟩
                      · let k := ((p 0).1 + (p 1).1) / 2
                        let l := ((p 1).1 + (p 2).1) / 2
                        have hk : (p 0).1 < k ∧ k < (p 1).1 := ⟨by dsimp [k]; linarith, by dsimp [k]; linarith⟩
                        have hl : (p 1).1 < l ∧ l < (p 2).1 := ⟨by dsimp [l]; linarith, by dsimp [l]; linarith⟩
                        refine ⟨![(a,c),(k,c),(l,c)], ![(k,d),(l,d),(b,d)], ?_, ?_, ?_, ?_, ?_⟩
                        · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
                        · intro i j; fin_cases i <;> fin_cases j <;> norm_num <;> simp only [Prod.le_def] <;> grind only
                        · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
                        · change ((Icc a k ×ˢ Icc c d) ∪ (Icc k l ×ˢ Icc c d)) ∪ (Icc l b ×ˢ Icc c d) = _
                          rw [← union_prod, Icc_union_Icc_eq_Icc (by linarith : a ≤ k) (by linarith : k ≤ l),
                            ← union_prod, Icc_union_Icc_eq_Icc (by linarith : a ≤ l) (by linarith : l ≤ b)]
                        · left
                          exact ⟨k,l,rfl,rfl,by linarith,by linarith,by linarith⟩
          
                      · let k := ((p 0).1 + (p 1).1) / 2
                        let h := ((p 1).2 + (p 2).2) / 2
                        have hk : (p 0).1 < k ∧ k < (p 1).1 := ⟨by dsimp [k]; linarith, by dsimp [k]; linarith⟩
                        have hh : (p 1).2 < h ∧ h < (p 2).2 := ⟨by dsimp [h]; linarith, by dsimp [h]; linarith⟩
                        refine ⟨![(a,c),(k,c),(k,h)], ![(k,d),(b,h),(b,d)], ?_, ?_, ?_, ?_, ?_⟩
                        · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
                        · intro i j; fin_cases i <;> fin_cases j <;> norm_num <;> simp only [Prod.le_def] <;> grind only
                        · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
                        · change ((Icc a k ×ˢ Icc c d) ∪ (Icc k b ×ˢ Icc c h)) ∪ (Icc k b ×ˢ Icc h d) = _
                          rw [union_assoc, ← prod_union,
                            Icc_union_Icc_eq_Icc (by linarith : c ≤ h) (by linarith : h ≤ d),
                            ← union_prod, Icc_union_Icc_eq_Icc (by linarith : a ≤ k) (by linarith : k ≤ b)]
                        · right; left
                          exact ⟨k,h,rfl,rfl,by linarith,by linarith,by linarith,by linarith⟩
          
                      · let k := ((p 1).1 + (p 2).1) / 2
                        let h := ((p 0).2 + (p 1).2) / 2
                        have hk : (p 1).1 < k ∧ k < (p 2).1 := ⟨by dsimp [k]; linarith, by dsimp [k]; linarith⟩
                        have hh : (p 0).2 < h ∧ h < (p 1).2 := ⟨by dsimp [h]; linarith, by dsimp [h]; linarith⟩
                        refine ⟨![(a,c),(a,h),(k,c)], ![(k,h),(k,d),(b,d)], ?_, ?_, ?_, ?_, ?_⟩
                        · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
                        · intro i j; fin_cases i <;> fin_cases j <;> norm_num <;> simp only [Prod.le_def] <;> grind only
                        · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
                        · change ((Icc a k ×ˢ Icc c h) ∪ (Icc a k ×ˢ Icc h d)) ∪ (Icc k b ×ˢ Icc c d) = _
                          rw [← prod_union, Icc_union_Icc_eq_Icc (by linarith : c ≤ h) (by linarith : h ≤ d),
                            ← union_prod, Icc_union_Icc_eq_Icc (by linarith : a ≤ k) (by linarith : k ≤ b)]
                        · right; right; left
                          exact ⟨k,h,rfl,rfl,by linarith,by linarith,by linarith,by linarith⟩
          
                      · let k := ((p 0).2 + (p 1).2) / 2
                        let l := ((p 1).2 + (p 2).2) / 2
                        have hk : (p 0).2 < k ∧ k < (p 1).2 := ⟨by dsimp [k]; linarith, by dsimp [k]; linarith⟩
                        have hl : (p 1).2 < l ∧ l < (p 2).2 := ⟨by dsimp [l]; linarith, by dsimp [l]; linarith⟩
                        refine ⟨![(a,c),(a,k),(a,l)], ![(b,k),(b,l),(b,d)], ?_, ?_, ?_, ?_, ?_⟩
                        · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
                        · intro i j; fin_cases i <;> fin_cases j <;> norm_num <;> simp only [Prod.le_def] <;> grind only
                        · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
                        · change ((Icc a b ×ˢ Icc c k) ∪ (Icc a b ×ˢ Icc k l)) ∪ (Icc a b ×ˢ Icc l d) = _
                          rw [← prod_union, Icc_union_Icc_eq_Icc (by linarith : c ≤ k) (by linarith : k ≤ l),
                            ← prod_union, Icc_union_Icc_eq_Icc (by linarith : c ≤ l) (by linarith : l ≤ d)]
          
                        · right; right; right
                          exact ⟨k,l,rfl,rfl,by linarith,by linarith,by linarith⟩
                  have hRestrict {X : Type} [TopologicalSpace X] (K C : Set X) (hCK : C ⊆ K) (hCcompact : IsCompact C)
                    (f : C(K,S)) (hf : IsEmbedding f) (p : Fin 3 → X) (i : Fin 3)
                    (hmarks : ∀ z : K, f z ∈ M.cover.branch ↔ ∃ j, z.val = p j)
                    (hincidence : ∀ j, p j ∈ C ↔ j = i) (hinside : p i ∈ interior C) :
                    ∃ fc : C(C,S), IsEmbedding fc ∧
                      (∀ x : C, fc x = f ⟨x.val,hCK x.property⟩) ∧
                      ∃ m : C, m.val ∈ interior C ∧
                        (∀ x : C, fc x ∈ M.cover.branch ↔ x = m) := by
                    letI : T2Space S := M.sphere.symm.t2Space
                    letI : CompactSpace C := isCompact_iff_compactSpace.mp hCcompact
                    let inc : C → K := fun x => ⟨x.val,hCK x.property⟩
                    have hinccont : Continuous inc := continuous_subtype_val.subtype_mk _
                    let fc : C(C,S) := ⟨f ∘ inc,f.continuous.comp hinccont⟩
                    have hfcinj : Function.Injective fc := hf.injective.comp (by
                      intro x y h
                      exact Subtype.ext (congrArg (fun z : K => z.val) h))
                    let m : C := ⟨p i,(hincidence i).mpr rfl⟩
                    refine ⟨fc,(fc.continuous.isClosedEmbedding hfcinj).isEmbedding,fun _ => rfl,m,hinside,?_⟩
                    intro x
                    change f (inc x) ∈ M.cover.branch ↔ x = m
                    rw [hmarks]
                    constructor
                    · rintro ⟨j,hj⟩
                      have hjC : p j ∈ C := hj ▸ x.property
                      have hji := (hincidence j).mp hjC
                      apply Subtype.ext
                      simpa [inc,m,hji] using hj
                    · intro hx
                      refine ⟨i,?_⟩
                      exact congrArg Subtype.val hx
                  classical
                  dsimp only
                  let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                        (EuclideanSpace.equiv (Fin 2) ℝ).symm
                  let K := e '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
                  obtain ⟨f,hf,hfb,hfbrange,hfcard⟩ := hSquare a
                  have hboundary : ∀ z : K, z.val ∈ frontier K → f z ∉ M.cover.branch := by
                    intro z hz hbranch
                    exact Set.disjoint_left.mp a.val.avoids_branch ((hfb z).mpr hz) hbranch
                  obtain ⟨s,hscard,hsiff,hsinside⟩ := hCoords (-1) 1 (-1) 1 f hf hboundary hfcard
                  obtain ⟨p,hprange,hp01,hp12,hpinside⟩ := hSort (-1) 1 (-1) 1 s hscard hsinside
                  obtain ⟨lo,hi,hdims,hincidence,hpCell,hcover,hshape⟩ := hPartition (-1) 1 (-1) 1 p hp01 hp12 hpinside
                  have hmarks : ∀ z : K, f z ∈ M.cover.branch ↔ ∃ j, z.val = e (p j) := by
                    intro z
                    rw [hsiff]
                    change e.symm z.val ∈ (s : Set (ℝ × ℝ)) ↔ ∃ j, z.val = e (p j)
                    rw [← hprange]
                    constructor
                    · rintro ⟨j,hj⟩
                      refine ⟨j,?_⟩
                      rw [hj,e.apply_symm_apply]
                    · rintro ⟨j,hj⟩
                      refine ⟨j,?_⟩
                      rw [hj,e.symm_apply_apply]
                  have hCellCover : ((e '' (Icc (lo 0).1 (hi 0).1 ×ˢ Icc (lo 0).2 (hi 0).2)) ∪
                      (e '' (Icc (lo 1).1 (hi 1).1 ×ˢ Icc (lo 1).2 (hi 1).2))) ∪
                      (e '' (Icc (lo 2).1 (hi 2).1 ×ˢ Icc (lo 2).2 (hi 2).2)) = K := by
                    rw [← Set.image_union,← Set.image_union,hcover]
                  refine ⟨f,p,lo,hi,hf,hfbrange,hdims,hCellCover,hshape,?_⟩
                  intro i
                  let R := Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2
                  let Cell := e '' R
                  have hRsub : R ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
                    rw [← hcover]
                    fin_cases i
                    · exact Set.Subset.trans Set.subset_union_left Set.subset_union_left
                    · exact Set.Subset.trans Set.subset_union_right Set.subset_union_left
                    · exact Set.subset_union_right
                  have hsub : Cell ⊆ K := Set.image_mono hRsub
                  have hcompact : IsCompact Cell := (isCompact_Icc.prod isCompact_Icc).image e.continuous
                  have hCellIncidence : ∀ j, e (p j) ∈ Cell ↔ j = i := by
                    intro j
                    have hmem : e (p j) ∈ Cell ↔ p j ∈ R := by
                      constructor
                      · rintro ⟨v,hv,he⟩
                        exact e.injective he ▸ hv
                      · intro hj
                        exact ⟨p j,hj,rfl⟩
                    rw [hmem,hincidence]
                    exact eq_comm
                  have hCellInside : e (p i) ∈ interior Cell := by
                    change e.toHomeomorph (p i) ∈ interior (e.toHomeomorph '' R)
                    rw [← e.toHomeomorph.image_interior]
                    refine ⟨p i,?_,rfl⟩
                    change p i ∈ interior (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)
                    rw [interior_prod_eq,interior_Icc,interior_Icc]
                    exact ⟨⟨(hpCell i).1,(hpCell i).2.1⟩,⟨(hpCell i).2.2.1,(hpCell i).2.2.2⟩⟩
                  obtain ⟨fc,hfc,hfcmap,m,hm,hmonly⟩ := hRestrict K Cell hsub hcompact f hf
                    (fun j => e (p j)) i hmarks hCellIncidence hCellInside
                  have hmval : m.val = e (p i) := by
                    have hmbranch : fc m ∈ M.cover.branch := (hmonly m).mpr rfl
                    rw [hfcmap] at hmbranch
                    rcases (hmarks _).mp hmbranch with ⟨j,hj⟩
                    have hji : j = i := (hCellIncidence j).mp (hj ▸ m.property)
                    simpa [hji] using hj
                  exact ⟨hsub,fc,hfc,hfcmap,m,hmval,hm,hmonly⟩
              have hAdapter (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
                let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                    (EuclideanSpace.equiv (Fin 2) ℝ).symm
                let K := e '' (Icc a b ×ˢ Icc c d)
                ∀ (f : C(K,S)), IsEmbedding f →
                ∀ (m : K), m.val ∈ interior K → (∀ z, f z ∈ M.cover.branch ↔ z = m) →
                ∃ fd : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S),
                  ∃ md : Metric.closedBall (0 : Schoenflies.Plane) 1,
                    IsEmbedding fd ∧ ‖md.val‖ < 1 ∧ (∀ z, fd z ∈ M.cover.branch ↔ z = md) ∧
                    fd '' {z | ‖z.val‖ = 1} = f '' {z : K | z.val ∈ frontier K} := by
                      as_aux_lemma =>
                  have hrect (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
                    let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                        (EuclideanSpace.equiv (Fin 2) ℝ).symm
                    let K := e '' (Icc a b ×ˢ Icc c d)
                    ∃ h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K,
                      (∀ x, (h x : Schoenflies.Plane) ∈ interior K ↔ ‖x.val‖ < 1) ∧
                      (∀ x, (h x : Schoenflies.Plane) ∈ frontier K ↔ ‖x.val‖ = 1) := by
                        as_aux_lemma =>
                      dsimp only
                      let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                          (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                            (EuclideanSpace.equiv (Fin 2) ℝ).symm
                      let K := e '' (Icc a b ×ˢ Icc c d)
                      change ∃ h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K, _
                      have hcompact : IsCompact K :=
                        (isCompact_Icc.prod isCompact_Icc).image e.continuous
                      have hconvex : Convex ℝ K :=
                        ((convex_Icc a b).prod (convex_Icc c d)).linear_image e.toLinearEquiv.toLinearMap
                      have hne : (interior K).Nonempty := by
                        have hm : ((a + b) / 2, (c + d) / 2) ∈ interior (Icc a b ×ˢ Icc c d) := by
                          rw [interior_prod_eq, interior_Icc, interior_Icc]
                          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
                        refine ⟨e ((a + b) / 2, (c + d) / 2), ?_⟩
                        change e.toHomeomorph ((a + b) / 2, (c + d) / 2) ∈
                          interior (e.toHomeomorph '' (Icc a b ×ˢ Icc c d))
                        rw [← e.toHomeomorph.image_interior]
                        exact mem_image_of_mem e hm
                      obtain ⟨g, hgi, hgc, hgf⟩ :=
                        exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconvex hne hcompact.isBounded
                      have hgK : g '' K = Metric.closedBall (0 : Schoenflies.Plane) 1 := by
                        simpa [hcompact.isClosed.closure_eq] using hgc
                      let h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K :=
                        (Homeomorph.sets g (by
                          ext x
                          constructor
                          · intro hx
                            rw [← hgK]
                            exact mem_image_of_mem g hx
                          · intro hx
                            rw [← hgK] at hx
                            rcases hx with ⟨y, hy, hxy⟩
                            exact g.injective hxy ▸ hy)).symm
                      refine ⟨h, ?_, ?_⟩
                      · intro x
                        change g.symm x.val ∈ interior K ↔ ‖x.val‖ < 1
                        rw [← mem_ball_zero_iff]
                        constructor
                        · intro hx
                          rw [← hgi]
                          exact ⟨g.symm x.val, hx, g.apply_symm_apply x.val⟩
                        · intro hx
                          rw [← hgi] at hx
                          rcases hx with ⟨y, hy, hyx⟩
                          simpa [← hyx] using hy
                      · intro x
                        change g.symm x.val ∈ frontier K ↔ ‖x.val‖ = 1
                        rw [← dist_zero_right x.val]
                        change g.symm x.val ∈ frontier K ↔ x.val ∈ Metric.sphere (0 : Schoenflies.Plane) 1
                        constructor
                        · intro hx
                          rw [← hgf]
                          exact ⟨g.symm x.val, hx, g.apply_symm_apply x.val⟩
                        · intro hx
                          rw [← hgf] at hx
                          rcases hx with ⟨y, hy, hyx⟩
                          simpa [← hyx] using hy
                  dsimp only
                  let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                        (EuclideanSpace.equiv (Fin 2) ℝ).symm
                  let K := e '' (Icc a b ×ˢ Icc c d)
                  change ∀ (f : C(K,S)), _
                  intro f hf m hm honly
                  obtain ⟨h,hi,hb⟩ := hrect a b c d hab hcd
                  let fd : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S) := f.comp ⟨h,h.continuous⟩
                  let md := h.symm m
                  have hmd : ‖md.val‖ < 1 := by
                    apply (hi md).mp
                    change ((h (h.symm m)) : Schoenflies.Plane) ∈ interior K
                    rw [h.apply_symm_apply]
                    exact hm
                  have hmdonly : ∀ z, fd z ∈ M.cover.branch ↔ z = md := by
                    intro z
                    change f (h z) ∈ M.cover.branch ↔ z = h.symm m
                    rw [honly]
                    exact h.eq_symm_apply.symm
                  refine ⟨fd,md,hf.comp h.isEmbedding,hmd,hmdonly,?_⟩
                  ext y
                  constructor
                  · rintro ⟨z,hz,rfl⟩
                    exact ⟨h z,(hb z).mpr hz,rfl⟩
                  · rintro ⟨z,hz,rfl⟩
                    refine ⟨h.symm z,?_,?_⟩
                    · apply (hb _).mp
                      change ((h (h.symm z)) : Schoenflies.Plane) ∈ frontier K
                      rw [h.apply_symm_apply]
                      exact hz
                    · change f (h (h.symm z)) = f z
                      rw [h.apply_symm_apply]
              classical
              dsimp only
              let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
                  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                    (EuclideanSpace.equiv (Fin 2) ℝ).symm
              let K := e '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
              obtain ⟨f,p,lo,hi,hf,hfbrange,hdims,hcover,hshape,hCellFamily⟩ := hCells a
              choose hsub fc hfc hfcmap mc hmcval hmcinside hmconly using hCellFamily
              have hAdapters (i : Fin 3) := hAdapter (lo i).1 (hi i).1 (lo i).2 (hi i).2
                (hdims i).1 (hdims i).2 (fc i) (hfc i) (mc i) (hmcinside i) (hmconly i)
              choose F m hF hm hFonly hFboundary using hAdapters
              refine ⟨f,lo,hi,F,m,hf,hfbrange,hdims,hcover,hshape,?_⟩
              intro i
              refine ⟨hF i,hm i,hFonly i,?_⟩
              rw [hFboundary]
              let Cell := e '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)
              have hCellcompact : IsCompact Cell := (isCompact_Icc.prod isCompact_Icc).image e.continuous
              have hFrontSub : frontier Cell ⊆ Cell := by
                intro z hz
                exact hCellcompact.isClosed.closure_eq ▸ (frontier_subset_closure hz)
              ext y
              constructor
              · rintro ⟨z,hz,rfl⟩
                refine ⟨⟨z.val,hsub i z.property⟩,hz,?_⟩
                exact (hfcmap i z).symm
              · rintro ⟨z,hz,rfl⟩
                let zc : Cell := ⟨z.val,hFrontSub hz⟩
                refine ⟨zc,hz,?_⟩
                rw [hfcmap]
          have hParameter {X Y S : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]
            (h : X ≃ₜ Y) (R : Set X) (f : C(h '' R,S)) (hf : IsEmbedding f) :
            ∃ F : C(R,S), IsEmbedding F ∧
              (∀ z : R, F z = f ⟨h z.val,⟨z.val,z.property,rfl⟩⟩) ∧
              (∀ A : Set X, f '' {z : h '' R | z.val ∈ h '' A} = F '' {z : R | z.val ∈ A}) := by
            let g : C(R,h '' R) := ⟨fun z => ⟨h z.val,⟨z.val,z.property,rfl⟩⟩,
              (h.continuous.comp continuous_subtype_val).subtype_mk _⟩
            have hg : IsEmbedding g := IsEmbedding.subtypeVal.of_comp_iff.mp
              (h.isEmbedding.comp IsEmbedding.subtypeVal)
            let F := f.comp g
            refine ⟨F,hf.comp hg,fun _ => rfl,?_⟩
            intro A
            ext y
            constructor
            · rintro ⟨z,hz,rfl⟩
              rcases hz with ⟨a,ha,haz⟩
              have haR : a ∈ R := by
                rcases z.property with ⟨r,hr,hrz⟩
                exact h.injective (hrz.trans haz.symm) ▸ hr
              refine ⟨⟨a,haR⟩,ha,?_⟩
              change f (g ⟨a,haR⟩) = f z
              congr 1
              exact Subtype.ext haz
            · rintro ⟨z,hz,rfl⟩
              exact ⟨g z,⟨z.val,hz,rfl⟩,rfl⟩
          dsimp only
          let R := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
          let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
              (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
                (EuclideanSpace.equiv (Fin 2) ℝ).symm
          obtain ⟨fp,lo,hi,F,m,hfp,hfpboundary,hdims,hcover,hshape,hcells⟩ := hDiscTree a
          obtain ⟨f,hf,hfmap,himage⟩ := hParameter e.toHomeomorph R fp hfp
          have hboundary : f '' {z : R | z.val ∈ frontier R} = a.val.image := by
            rw [← himage]
            rw [e.toHomeomorph.image_frontier]
            exact hfpboundary
          refine ⟨f,lo,hi,F,m,hf,hboundary,hdims,hshape,?_⟩
          intro i
          obtain ⟨hFi,hmi,hFonly,hFboundary⟩ := hcells i
          refine ⟨hFi,hmi,hFonly,?_⟩
          rw [hFboundary,← himage]
          rw [e.toHomeomorph.image_frontier]
          rfl
    
      have hTyped (a b c d : ℝ) (hab : a < b) (hcd : c < d)
          (lo hi : Fin 3 → ℝ × ℝ)
          (hshape : ((∃ k l : ℝ, lo = ![(a,c),(k,c),(l,c)] ∧ hi = ![(k,d),(l,d),(b,d)] ∧ a < k ∧ k < l ∧ l < b) ∨
             (∃ k h : ℝ, lo = ![(a,c),(k,c),(k,h)] ∧ hi = ![(k,d),(b,h),(b,d)] ∧ a < k ∧ k < b ∧ c < h ∧ h < d) ∨
             (∃ k h : ℝ, lo = ![(a,c),(a,h),(k,c)] ∧ hi = ![(k,h),(k,d),(b,d)] ∧ a < k ∧ k < b ∧ c < h ∧ h < d) ∨
             (∃ k l : ℝ, lo = ![(a,c),(a,k),(a,l)] ∧ hi = ![(b,k),(b,l),(b,d)] ∧ c < k ∧ k < l ∧ l < d))) :
          let R := Icc a b ×ˢ Icc c d
          ∃ r : Fin 3 → Fin 3, ∃ x y u v : R,
          ∃ P : Path x y, ∃ Q : Path y x, ∃ χ : Path x y,
          ∃ A : Path u v, ∃ B : Path v u, ∃ ξ : Path u v,
            Set.range (fun t => ((P.trans χ.symm) t).val) = frontier (Icc (lo (r 0)).1 (hi (r 0)).1 ×ˢ Icc (lo (r 0)).2 (hi (r 0)).2) ∧
            Set.range (fun t => ((A.trans ξ.symm) t).val) = frontier (Icc (lo (r 1)).1 (hi (r 1)).1 ×ˢ Icc (lo (r 1)).2 (hi (r 1)).2) ∧
            Set.range (fun t => ((ξ.trans B) t).val) = frontier (Icc (lo (r 2)).1 (hi (r 2)).1 ×ˢ Icc (lo (r 2)).2 (hi (r 2)).2) ∧
            Set.range (χ.trans Q) = Set.range (A.trans B) ∧
            Set.range (fun t => ((P.trans Q) t).val) = frontier (Icc a b ×ˢ Icc c d) ∧
            (∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
            (∀ s t, (A.trans ξ.symm) s = (A.trans ξ.symm) t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
            (∀ s t, (ξ.trans B) s = (ξ.trans B) t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
            (∀ s t, (A.trans B) s = (A.trans B) t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
            (∀ s t, (P.trans Q) s = (P.trans Q) t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) := by
              as_aux_lemma =>
          have hTree (a b c d : ℝ) (hab : a < b) (hcd : c < d)
              (lo hi : Fin 3 → ℝ × ℝ)
              (hshape : ((∃ k l : ℝ, lo = ![(a,c),(k,c),(l,c)] ∧ hi = ![(k,d),(l,d),(b,d)] ∧ a < k ∧ k < l ∧ l < b) ∨
                 (∃ k h : ℝ, lo = ![(a,c),(k,c),(k,h)] ∧ hi = ![(k,d),(b,h),(b,d)] ∧ a < k ∧ k < b ∧ c < h ∧ h < d) ∨
                 (∃ k h : ℝ, lo = ![(a,c),(a,h),(k,c)] ∧ hi = ![(k,h),(k,d),(b,d)] ∧ a < k ∧ k < b ∧ c < h ∧ h < d) ∨
                 (∃ k l : ℝ, lo = ![(a,c),(a,k),(a,l)] ∧ hi = ![(b,k),(b,l),(b,d)] ∧ c < k ∧ k < l ∧ l < d))) :
              ∃ r : Fin 3 → Fin 3, ∃ x y u v : ℝ × ℝ,
              ∃ P : Path x y, ∃ Q : Path y x, ∃ χ : Path x y,
              ∃ A : Path u v, ∃ B : Path v u, ∃ ξ : Path u v,
                Set.range (P.trans χ.symm) = frontier (Icc (lo (r 0)).1 (hi (r 0)).1 ×ˢ Icc (lo (r 0)).2 (hi (r 0)).2) ∧
                Set.range (A.trans ξ.symm) = frontier (Icc (lo (r 1)).1 (hi (r 1)).1 ×ˢ Icc (lo (r 1)).2 (hi (r 1)).2) ∧
                Set.range (ξ.trans B) = frontier (Icc (lo (r 2)).1 (hi (r 2)).1 ×ˢ Icc (lo (r 2)).2 (hi (r 2)).2) ∧
                Set.range (χ.trans Q) = Set.range (A.trans B) ∧
                Set.range (P.trans Q) = frontier (Icc a b ×ˢ Icc c d) ∧
                (∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
                (∀ s t, (A.trans ξ.symm) s = (A.trans ξ.symm) t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
                (∀ s t, (ξ.trans B) s = (ξ.trans B) t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
                (∀ s t, (A.trans B) s = (A.trans B) t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
                (∀ s t, (P.trans Q) s = (P.trans Q) t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) := by
                  as_aux_lemma =>
                    clear * - a b c d hab hcd lo hi hshape
                    as_aux_lemma =>
                have hv (a k b c d : ℝ) (hak : a < k) (hkb : k < b) (hcd : c < d) :
                    ∃ P : Path (k,c) (k,d), ∃ Q : Path (k,d) (k,c), ∃ χ : Path (k,c) (k,d),
                      Set.range (P.trans χ.symm) = frontier (Icc a k ×ˢ Icc c d) ∧
                      Set.range (χ.trans Q) = frontier (Icc k b ×ˢ Icc c d) ∧
                      Set.range (P.trans Q) = frontier (Icc a b ×ˢ Icc c d) ∧
                      (∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t →
                        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
                      (∀ s t, (χ.trans Q) s = (χ.trans Q) t →
                        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
                      (∀ s t, (P.trans Q) s = (P.trans Q) t →
                        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) := by
                          as_aux_lemma =>
                            clear * - a k b c d hak hkb hcd
                            as_aux_lemma =>
                      have hpaths (a k b c d : ℝ) (hak : a < k) (hkb : k < b) (hcd : c < d) :
                          ∃ P : Path (k,c) (k,d), ∃ Q : Path (k,d) (k,c), ∃ χ : Path (k,c) (k,d),
                            Function.Injective P ∧ Function.Injective Q ∧ Function.Injective χ ∧
                            Set.range P = {z : ℝ × ℝ | (a ≤ z.1 ∧ z.1 ≤ k ∧ (z.2 = c ∨ z.2 = d)) ∨
                              (z.1 = a ∧ c ≤ z.2 ∧ z.2 ≤ d)} ∧
                            Set.range Q = {z : ℝ × ℝ | (k ≤ z.1 ∧ z.1 ≤ b ∧ (z.2 = c ∨ z.2 = d)) ∨
                              (z.1 = b ∧ c ≤ z.2 ∧ z.2 ≤ d)} ∧
                            Set.range χ = {z : ℝ × ℝ | z.1 = k ∧ c ≤ z.2 ∧ z.2 ≤ d} ∧
                            (∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t →
                              s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
                            (∀ s t, (χ.trans Q) s = (χ.trans Q) t →
                              s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
                            (∀ s t, (P.trans Q) s = (P.trans Q) t →
                              s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) := by
                                as_aux_lemma =>
                                  clear * - a k b c d hak hkb hcd
                                  as_aux_lemma =>
                            have hH (a b y : ℝ) (hab : a < b) :
                              Function.Injective (Path.segment (a, y) (b, y)) ∧
                                Set.range (Path.segment (a, y) (b, y)) = {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ b ∧ z.2 = y} := by
                              have hcoord (t : Interval) : Path.segment (a, y) (b, y) t =
                                  ((1 - (t : ℝ)) * a + (t : ℝ) * b, y) := by
                                simp [Path.segment_apply, AffineMap.lineMap_apply, smul_eq_mul]
                                ring
                              constructor
                              · intro s t h
                                have hh := congrArg Prod.fst h
                                rw [hcoord, hcoord] at hh
                                apply Subtype.ext
                                dsimp at hh
                                nlinarith
                              · ext z
                                constructor
                                · rintro ⟨t, rfl⟩
                                  rw [hcoord]
                                  exact ⟨by nlinarith [t.property.1], by nlinarith [t.property.2], rfl⟩
                                · rintro ⟨ha, hb, hy⟩
                                  let t : Interval := ⟨(z.1 - a) / (b - a), by
                                    constructor
                                    · exact div_nonneg (sub_nonneg.mpr ha) (sub_pos.mpr hab).le
                                    · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith)⟩
                                  refine ⟨t, ?_⟩
                                  rw [hcoord]
                                  apply Prod.ext
                                  · dsimp [t]
                                    field_simp [ne_of_gt (sub_pos.mpr hab)]
                                    ring
                                  · exact hy.symm
                            have hV (x c d : ℝ) (hcd : c < d) :
                              Function.Injective (Path.segment (x, c) (x, d)) ∧
                                Set.range (Path.segment (x, c) (x, d)) = {z : ℝ × ℝ | z.1 = x ∧ c ≤ z.2 ∧ z.2 ≤ d} := by
                              have hcoord (t : Interval) : Path.segment (x, c) (x, d) t =
                                  (x, (1 - (t : ℝ)) * c + (t : ℝ) * d) := by
                                simp [Path.segment_apply, AffineMap.lineMap_apply, smul_eq_mul]
                                ring
                              constructor
                              · intro s t h
                                have hh := congrArg Prod.snd h
                                rw [hcoord, hcoord] at hh
                                apply Subtype.ext
                                dsimp at hh
                                nlinarith
                              · ext z
                                constructor
                                · rintro ⟨t, rfl⟩
                                  rw [hcoord]
                                  exact ⟨rfl, by nlinarith [t.property.1], by nlinarith [t.property.2]⟩
                                · rintro ⟨hx, hc, hd⟩
                                  let t : Interval := ⟨(z.2 - c) / (d - c), by
                                    constructor
                                    · exact div_nonneg (sub_nonneg.mpr hc) (sub_pos.mpr hcd).le
                                    · exact (div_le_one (sub_pos.mpr hcd)).mpr (by linarith)⟩
                                  refine ⟨t, ?_⟩
                                  rw [hcoord]
                                  apply Prod.ext
                                  · exact hx.symm
                                  · dsimp [t]
                                    field_simp [ne_of_gt (sub_pos.mpr hcd)]
                                    ring
                            have hcat {X : Type} [TopologicalSpace X] (a b c : X) (P : Path a b) (Q : Path b c)
                              (hP : Function.Injective P) (hQ : Function.Injective Q)
                              (hset : ∀ z ∈ Set.range P, z ∈ Set.range Q → z = b) :
                              Function.Injective (P.trans Q) := by
                              have hmeet : ∀ s t, P s = Q t → s = 1 ∧ t = 0 := by
                                intro s t h
                                have hb := hset (P s) ⟨s, rfl⟩ ⟨t, h.symm⟩
                                exact ⟨hP (hb.trans P.target.symm), hQ (h.symm.trans (hb.trans Q.source.symm))⟩
                              intro s t h
                              simp only [Path.trans_apply] at h
                              split_ifs at h with hs ht ht
                              · have hh := congrArg Subtype.val (hP h)
                                apply Subtype.ext
                                dsimp at hh
                                linarith
                              · obtain ⟨h1, h0⟩ := hmeet _ _ h
                                apply Subtype.ext
                                have h1 := congrArg Subtype.val h1
                                have h0 := congrArg Subtype.val h0
                                dsimp at h1 h0
                                linarith
                              · obtain ⟨h1, h0⟩ := hmeet _ _ h.symm
                                apply Subtype.ext
                                have h1 := congrArg Subtype.val h1
                                have h0 := congrArg Subtype.val h0
                                dsimp at h1 h0
                                linarith
                              · have hh := congrArg Subtype.val (hQ h)
                                apply Subtype.ext
                                dsimp at hh
                                linarith
                            have hloop {X : Type} [TopologicalSpace X] (a b : X) (P : Path a b) (Q : Path b a)
                              (hP : Function.Injective P) (hQ : Function.Injective Q)
                              (hset : ∀ z ∈ Set.range P, z ∈ Set.range Q → z = a ∨ z = b) :
                              ∀ s t, (P.trans Q) s = (P.trans Q) t →
                                s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
                                  as_aux_lemma =>
                                have hmeet : ∀ s t, P s = Q t → (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
                                  intro s t h
                                  rcases hset (P s) ⟨s, rfl⟩ ⟨t, h.symm⟩ with ha | hb
                                  · exact Or.inl ⟨hP (ha.trans P.source.symm), hQ (h.symm.trans (ha.trans Q.target.symm))⟩
                                  · exact Or.inr ⟨hP (hb.trans P.target.symm), hQ (h.symm.trans (hb.trans Q.source.symm))⟩
                                intro s t h
                                simp only [Path.trans_apply] at h
                                split_ifs at h with hs ht ht
                                · left
                                  have hh := congrArg Subtype.val (hP h)
                                  apply Subtype.ext
                                  dsimp at hh
                                  linarith
                                · rcases hmeet _ _ h with ⟨hs0, ht1⟩ | ⟨hs1, ht0⟩
                                  · right; left
                                    constructor
                                    · apply Subtype.ext
                                      have := congrArg Subtype.val hs0
                                      dsimp at this
                                      change (s : ℝ) = 0
                                      linarith
                                    · apply Subtype.ext
                                      have := congrArg Subtype.val ht1
                                      dsimp at this
                                      change (t : ℝ) = 1
                                      linarith
                                  · left
                                    apply Subtype.ext
                                    have h1 := congrArg Subtype.val hs1
                                    have h0 := congrArg Subtype.val ht0
                                    dsimp at h1 h0
                                    linarith
                                · rcases hmeet _ _ h.symm with ⟨ht0, hs1⟩ | ⟨ht1, hs0⟩
                                  · right; right
                                    constructor
                                    · apply Subtype.ext
                                      have := congrArg Subtype.val hs1
                                      dsimp at this
                                      change (s : ℝ) = 1
                                      linarith
                                    · apply Subtype.ext
                                      have := congrArg Subtype.val ht0
                                      dsimp at this
                                      change (t : ℝ) = 0
                                      linarith
                                  · left
                                    apply Subtype.ext
                                    have h1 := congrArg Subtype.val ht1
                                    have h0 := congrArg Subtype.val hs0
                                    dsimp at h1 h0
                                    linarith
                                · left
                                  have hh := congrArg Subtype.val (hQ h)
                                  apply Subtype.ext
                                  dsimp at hh
                                  linarith
                            let B := (Path.segment (a,c) (k,c)).symm
                            let L := Path.segment (a,c) (a,d)
                            let T := Path.segment (a,d) (k,d)
                            let P := (B.trans L).trans T
                            let U := Path.segment (k,d) (b,d)
                            let R := (Path.segment (b,c) (b,d)).symm
                            let V := (Path.segment (k,c) (b,c)).symm
                            let Q := (U.trans R).trans V
                            let χ := Path.segment (k,c) (k,d)
                            obtain ⟨hBi, hBr⟩ := hH a k c hak
                            obtain ⟨hLi, hLr⟩ := hV a c d hcd
                            obtain ⟨hTi, hTr⟩ := hH a k d hak
                            obtain ⟨hUi, hUr⟩ := hH k b d hkb
                            obtain ⟨hRi, hRr⟩ := hV b c d hcd
                            obtain ⟨hVi, hVr⟩ := hH k b c hkb
                            obtain ⟨hχi, hχr⟩ := hV k c d hcd
                            have hBsr : Set.range B = Set.range (Path.segment (a,c) (k,c)) := Path.symm_range _
                            have hRsr : Set.range R = Set.range (Path.segment (b,c) (b,d)) := Path.symm_range _
                            have hVsr : Set.range V = Set.range (Path.segment (k,c) (b,c)) := Path.symm_range _
                            have hBsi : Function.Injective B := hBi.comp (by
                              intro s t h
                              apply Subtype.ext
                              have h := congrArg Subtype.val h
                              dsimp at h
                              linarith)
                            have hRsi : Function.Injective R := hRi.comp (by
                              intro s t h
                              apply Subtype.ext
                              have h := congrArg Subtype.val h
                              dsimp at h
                              linarith)
                            have hVsi : Function.Injective V := hVi.comp (by
                              intro s t h
                              apply Subtype.ext
                              have h := congrArg Subtype.val h
                              dsimp at h
                              linarith)
                            have hBLi : Function.Injective (B.trans L) := hcat _ _ _ B L hBsi hLi (by
                              intro z hz hz'
                              rw [hBsr, hBr] at hz
                              rw [hLr] at hz'
                              exact Prod.ext hz'.1 hz.2.2)
                            have hPi : Function.Injective P := hcat _ _ _ (B.trans L) T hBLi hTi (by
                              intro z hz hz'
                              rw [Path.trans_range, hBsr, hBr, hLr] at hz
                              rw [hTr] at hz'
                              rcases hz with hz | hz
                              · exact False.elim ((ne_of_lt hcd) (hz.2.2.symm.trans hz'.2.2))
                              · exact Prod.ext hz.1 hz'.2.2)
                            have hURi : Function.Injective (U.trans R) := hcat _ _ _ U R hUi hRsi (by
                              intro z hz hz'
                              rw [hUr] at hz
                              rw [hRsr, hRr] at hz'
                              exact Prod.ext hz'.1 hz.2.2)
                            have hQi : Function.Injective Q := hcat _ _ _ (U.trans R) V hURi hVsi (by
                              intro z hz hz'
                              rw [Path.trans_range, hUr, hRsr, hRr] at hz
                              rw [hVsr, hVr] at hz'
                              rcases hz with hz | hz
                              · exact False.elim ((ne_of_lt hcd) (hz'.2.2.symm.trans hz.2.2))
                              · exact Prod.ext hz.1 hz'.2.2)
                            have hPr : Set.range P = {z : ℝ × ℝ | (a ≤ z.1 ∧ z.1 ≤ k ∧ (z.2 = c ∨ z.2 = d)) ∨
                                (z.1 = a ∧ c ≤ z.2 ∧ z.2 ≤ d)} := by
                              change Set.range ((B.trans L).trans T) = _
                              rw [Path.trans_range, Path.trans_range, hBsr, hBr, hLr, hTr]
                              ext z
                              simp only [mem_union, mem_ofPred_eq]
                              tauto
                            have hQr : Set.range Q = {z : ℝ × ℝ | (k ≤ z.1 ∧ z.1 ≤ b ∧ (z.2 = c ∨ z.2 = d)) ∨
                                (z.1 = b ∧ c ≤ z.2 ∧ z.2 ≤ d)} := by
                              change Set.range ((U.trans R).trans V) = _
                              rw [Path.trans_range, Path.trans_range, hUr, hRsr, hRr, hVsr, hVr]
                              ext z
                              simp only [mem_union, mem_ofPred_eq]
                              tauto
                            have hχsi : Function.Injective χ.symm := hχi.comp (by
                              intro s t h
                              apply Subtype.ext
                              have h := congrArg Subtype.val h
                              dsimp at h
                              linarith)
                            refine ⟨P, Q, χ, hPi, hQi, hχi, hPr, hQr, hχr, ?_, ?_, ?_⟩
                            · apply hloop _ _ P χ.symm hPi hχsi
                              intro z hz hz'
                              rw [hPr] at hz
                              rw [Path.symm_range, hχr] at hz'
                              rcases hz with hz | hz
                              · rcases hz.2.2 with hy | hy
                                · exact Or.inl (Prod.ext hz'.1 hy)
                                · exact Or.inr (Prod.ext hz'.1 hy)
                              · exact False.elim ((ne_of_lt hak) (hz.1.symm.trans hz'.1))
                            · apply hloop _ _ χ Q hχi hQi
                              intro z hz hz'
                              rw [hχr] at hz
                              rw [hQr] at hz'
                              rcases hz' with hz' | hz'
                              · rcases hz'.2.2 with hy | hy
                                · exact Or.inl (Prod.ext hz.1 hy)
                                · exact Or.inr (Prod.ext hz.1 hy)
                              · exact False.elim ((ne_of_lt hkb) (hz.1.symm.trans hz'.1))
                            · apply hloop _ _ P Q hPi hQi
                              intro z hz hz'
                              rw [hPr] at hz
                              rw [hQr] at hz'
                              rcases hz with hz | hz <;> rcases hz' with hz' | hz'
                              · have hx : z.1 = k := le_antisymm hz.2.1 hz'.1
                                rcases hz.2.2 with hy | hy
                                · exact Or.inl (Prod.ext hx hy)
                                · exact Or.inr (Prod.ext hx hy)
                              · exact False.elim (not_le_of_gt hkb (hz'.1 ▸ hz.2.1))
                              · exact False.elim (not_le_of_gt hak (hz.1 ▸ hz'.1))
                              · exact False.elim (ne_of_lt (lt_trans hak hkb) (hz.1.symm.trans hz'.1))
          
                      have hranges (a k b c d : ℝ) (hak : a < k) (hkb : k < b) (hcd : c < d)
                          (P : Path (k,c) (k,d)) (Q : Path (k,d) (k,c)) (χ : Path (k,c) (k,d))
                          (hPr : Set.range P = {z : ℝ × ℝ | (a ≤ z.1 ∧ z.1 ≤ k ∧ (z.2 = c ∨ z.2 = d)) ∨
                            (z.1 = a ∧ c ≤ z.2 ∧ z.2 ≤ d)})
                          (hQr : Set.range Q = {z : ℝ × ℝ | (k ≤ z.1 ∧ z.1 ≤ b ∧ (z.2 = c ∨ z.2 = d)) ∨
                            (z.1 = b ∧ c ≤ z.2 ∧ z.2 ≤ d)})
                          (hχr : Set.range χ = {z : ℝ × ℝ | z.1 = k ∧ c ≤ z.2 ∧ z.2 ≤ d}) :
                          Set.range (P.trans χ.symm) = frontier (Icc a k ×ˢ Icc c d) ∧
                          Set.range (χ.trans Q) = frontier (Icc k b ×ˢ Icc c d) ∧
                          Set.range (P.trans Q) = frontier (Icc a b ×ˢ Icc c d) := by
                        have hfront (u v : ℝ) (huv : u < v) :
                            frontier (Icc u v ×ˢ Icc c d) =
                            {z : ℝ × ℝ | (u ≤ z.1 ∧ z.1 ≤ v ∧ (z.2 = c ∨ z.2 = d)) ∨
                              ((z.1 = u ∨ z.1 = v) ∧ c ≤ z.2 ∧ z.2 ≤ d)} := by
                          rw [frontier_prod_eq, isClosed_Icc.closure_eq, isClosed_Icc.closure_eq,
                            frontier_Icc huv.le, frontier_Icc hcd.le]
                          ext z
                          simp only [mem_union, mem_prod, mem_Icc, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
                          tauto
                        constructor
                        · rw [Path.trans_range, Path.symm_range, hPr, hχr, hfront a k hak]
                          ext z
                          simp only [mem_union, mem_ofPred_eq]
                          tauto
                        constructor
                        · rw [Path.trans_range, hχr, hQr, hfront k b hkb]
                          ext z
                          simp only [mem_union, mem_ofPred_eq]
                          tauto
                        · rw [Path.trans_range, hPr, hQr, hfront a b (lt_trans hak hkb)]
                          ext z
                          simp only [mem_union, mem_ofPred_eq]
                          constructor
                          · rintro ((⟨hx, hk, hy⟩ | ⟨hx, hc, hd⟩) | (⟨hk, hb, hy⟩ | ⟨hx, hc, hd⟩))
                            · exact Or.inl ⟨hx, le_trans hk hkb.le, hy⟩
                            · exact Or.inr ⟨Or.inl hx, hc, hd⟩
                            · exact Or.inl ⟨le_trans hak.le hk, hb, hy⟩
                            · exact Or.inr ⟨Or.inr hx, hc, hd⟩
                          · rintro (⟨ha, hb, hy⟩ | ⟨hx, hc, hd⟩)
                            · rcases le_total z.1 k with hk | hk
                              · exact Or.inl (Or.inl ⟨ha, hk, hy⟩)
                              · exact Or.inr (Or.inl ⟨hk, hb, hy⟩)
                            · rcases hx with hx | hx
                              · exact Or.inl (Or.inr ⟨hx, hc, hd⟩)
                              · exact Or.inr (Or.inr ⟨hx, hc, hd⟩)
          
                      obtain ⟨P,Q,χ,_,_,_,hp,hq,hχ,hleft,hright,houter⟩ := hpaths a k b c d hak hkb hcd
                      obtain ⟨hl,hr,ho⟩ := hranges a k b c d hak hkb hcd P Q χ hp hq hχ
                      exact ⟨P,Q,χ,hl,hr,ho,hleft,hright,houter⟩
        
                have hh (a b c h d : ℝ) (hab : a < b) (hch : c < h) (hhd : h < d) :
                    ∃ P : Path (a,h) (b,h), ∃ Q : Path (b,h) (a,h), ∃ χ : Path (a,h) (b,h),
                      Set.range (P.trans χ.symm) = frontier (Icc a b ×ˢ Icc c h) ∧
                      Set.range (χ.trans Q) = frontier (Icc a b ×ˢ Icc h d) ∧
                      Set.range (P.trans Q) = frontier (Icc a b ×ˢ Icc c d) ∧
                      (∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t →
                        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
                      (∀ s t, (χ.trans Q) s = (χ.trans Q) t →
                        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
                      (∀ s t, (P.trans Q) s = (P.trans Q) t →
                        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) := by
                          as_aux_lemma =>
                            clear * - a b c h d hab hch hhd
                            as_aux_lemma =>
                      have hvertical (a k b c d : ℝ) (hak : a < k) (hkb : k < b) (hcd : c < d) :
                          ∃ P : Path (k,c) (k,d), ∃ Q : Path (k,d) (k,c), ∃ χ : Path (k,c) (k,d),
                            Set.range (P.trans χ.symm) = frontier (Icc a k ×ˢ Icc c d) ∧
                            Set.range (χ.trans Q) = frontier (Icc k b ×ˢ Icc c d) ∧
                            Set.range (P.trans Q) = frontier (Icc a b ×ˢ Icc c d) ∧
                            (∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t →
                              s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
                            (∀ s t, (χ.trans Q) s = (χ.trans Q) t →
                              s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
                            (∀ s t, (P.trans Q) s = (P.trans Q) t →
                              s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) := by
                                as_aux_lemma =>
                                  clear * - a k b c d hak hkb hcd
                                  as_aux_lemma =>
                            have hpaths (a k b c d : ℝ) (hak : a < k) (hkb : k < b) (hcd : c < d) :
                                ∃ P : Path (k,c) (k,d), ∃ Q : Path (k,d) (k,c), ∃ χ : Path (k,c) (k,d),
                                  Function.Injective P ∧ Function.Injective Q ∧ Function.Injective χ ∧
                                  Set.range P = {z : ℝ × ℝ | (a ≤ z.1 ∧ z.1 ≤ k ∧ (z.2 = c ∨ z.2 = d)) ∨
                                    (z.1 = a ∧ c ≤ z.2 ∧ z.2 ≤ d)} ∧
                                  Set.range Q = {z : ℝ × ℝ | (k ≤ z.1 ∧ z.1 ≤ b ∧ (z.2 = c ∨ z.2 = d)) ∨
                                    (z.1 = b ∧ c ≤ z.2 ∧ z.2 ≤ d)} ∧
                                  Set.range χ = {z : ℝ × ℝ | z.1 = k ∧ c ≤ z.2 ∧ z.2 ≤ d} ∧
                                  (∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t →
                                    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
                                  (∀ s t, (χ.trans Q) s = (χ.trans Q) t →
                                    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
                                  (∀ s t, (P.trans Q) s = (P.trans Q) t →
                                    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) := by
                                      as_aux_lemma =>
                                        clear * - a k b c d hak hkb hcd
                                        as_aux_lemma =>
                                  have hH (a b y : ℝ) (hab : a < b) :
                                    Function.Injective (Path.segment (a, y) (b, y)) ∧
                                      Set.range (Path.segment (a, y) (b, y)) = {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ b ∧ z.2 = y} := by
                                    have hcoord (t : Interval) : Path.segment (a, y) (b, y) t =
                                        ((1 - (t : ℝ)) * a + (t : ℝ) * b, y) := by
                                      simp [Path.segment_apply, AffineMap.lineMap_apply, smul_eq_mul]
                                      ring
                                    constructor
                                    · intro s t h
                                      have hh := congrArg Prod.fst h
                                      rw [hcoord, hcoord] at hh
                                      apply Subtype.ext
                                      dsimp at hh
                                      nlinarith
                                    · ext z
                                      constructor
                                      · rintro ⟨t, rfl⟩
                                        rw [hcoord]
                                        exact ⟨by nlinarith [t.property.1], by nlinarith [t.property.2], rfl⟩
                                      · rintro ⟨ha, hb, hy⟩
                                        let t : Interval := ⟨(z.1 - a) / (b - a), by
                                          constructor
                                          · exact div_nonneg (sub_nonneg.mpr ha) (sub_pos.mpr hab).le
                                          · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith)⟩
                                        refine ⟨t, ?_⟩
                                        rw [hcoord]
                                        apply Prod.ext
                                        · dsimp [t]
                                          field_simp [ne_of_gt (sub_pos.mpr hab)]
                                          ring
                                        · exact hy.symm
                                  have hV (x c d : ℝ) (hcd : c < d) :
                                    Function.Injective (Path.segment (x, c) (x, d)) ∧
                                      Set.range (Path.segment (x, c) (x, d)) = {z : ℝ × ℝ | z.1 = x ∧ c ≤ z.2 ∧ z.2 ≤ d} := by
                                    have hcoord (t : Interval) : Path.segment (x, c) (x, d) t =
                                        (x, (1 - (t : ℝ)) * c + (t : ℝ) * d) := by
                                      simp [Path.segment_apply, AffineMap.lineMap_apply, smul_eq_mul]
                                      ring
                                    constructor
                                    · intro s t h
                                      have hh := congrArg Prod.snd h
                                      rw [hcoord, hcoord] at hh
                                      apply Subtype.ext
                                      dsimp at hh
                                      nlinarith
                                    · ext z
                                      constructor
                                      · rintro ⟨t, rfl⟩
                                        rw [hcoord]
                                        exact ⟨rfl, by nlinarith [t.property.1], by nlinarith [t.property.2]⟩
                                      · rintro ⟨hx, hc, hd⟩
                                        let t : Interval := ⟨(z.2 - c) / (d - c), by
                                          constructor
                                          · exact div_nonneg (sub_nonneg.mpr hc) (sub_pos.mpr hcd).le
                                          · exact (div_le_one (sub_pos.mpr hcd)).mpr (by linarith)⟩
                                        refine ⟨t, ?_⟩
                                        rw [hcoord]
                                        apply Prod.ext
                                        · exact hx.symm
                                        · dsimp [t]
                                          field_simp [ne_of_gt (sub_pos.mpr hcd)]
                                          ring
                                  have hcat {X : Type} [TopologicalSpace X] (a b c : X) (P : Path a b) (Q : Path b c)
                                    (hP : Function.Injective P) (hQ : Function.Injective Q)
                                    (hset : ∀ z ∈ Set.range P, z ∈ Set.range Q → z = b) :
                                    Function.Injective (P.trans Q) := by
                                    have hmeet : ∀ s t, P s = Q t → s = 1 ∧ t = 0 := by
                                      intro s t h
                                      have hb := hset (P s) ⟨s, rfl⟩ ⟨t, h.symm⟩
                                      exact ⟨hP (hb.trans P.target.symm), hQ (h.symm.trans (hb.trans Q.source.symm))⟩
                                    intro s t h
                                    simp only [Path.trans_apply] at h
                                    split_ifs at h with hs ht ht
                                    · have hh := congrArg Subtype.val (hP h)
                                      apply Subtype.ext
                                      dsimp at hh
                                      linarith
                                    · obtain ⟨h1, h0⟩ := hmeet _ _ h
                                      apply Subtype.ext
                                      have h1 := congrArg Subtype.val h1
                                      have h0 := congrArg Subtype.val h0
                                      dsimp at h1 h0
                                      linarith
                                    · obtain ⟨h1, h0⟩ := hmeet _ _ h.symm
                                      apply Subtype.ext
                                      have h1 := congrArg Subtype.val h1
                                      have h0 := congrArg Subtype.val h0
                                      dsimp at h1 h0
                                      linarith
                                    · have hh := congrArg Subtype.val (hQ h)
                                      apply Subtype.ext
                                      dsimp at hh
                                      linarith
                                  have hloop {X : Type} [TopologicalSpace X] (a b : X) (P : Path a b) (Q : Path b a)
                                    (hP : Function.Injective P) (hQ : Function.Injective Q)
                                    (hset : ∀ z ∈ Set.range P, z ∈ Set.range Q → z = a ∨ z = b) :
                                    ∀ s t, (P.trans Q) s = (P.trans Q) t →
                                      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
                                        as_aux_lemma =>
                                      have hmeet : ∀ s t, P s = Q t → (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
                                        intro s t h
                                        rcases hset (P s) ⟨s, rfl⟩ ⟨t, h.symm⟩ with ha | hb
                                        · exact Or.inl ⟨hP (ha.trans P.source.symm), hQ (h.symm.trans (ha.trans Q.target.symm))⟩
                                        · exact Or.inr ⟨hP (hb.trans P.target.symm), hQ (h.symm.trans (hb.trans Q.source.symm))⟩
                                      intro s t h
                                      simp only [Path.trans_apply] at h
                                      split_ifs at h with hs ht ht
                                      · left
                                        have hh := congrArg Subtype.val (hP h)
                                        apply Subtype.ext
                                        dsimp at hh
                                        linarith
                                      · rcases hmeet _ _ h with ⟨hs0, ht1⟩ | ⟨hs1, ht0⟩
                                        · right; left
                                          constructor
                                          · apply Subtype.ext
                                            have := congrArg Subtype.val hs0
                                            dsimp at this
                                            change (s : ℝ) = 0
                                            linarith
                                          · apply Subtype.ext
                                            have := congrArg Subtype.val ht1
                                            dsimp at this
                                            change (t : ℝ) = 1
                                            linarith
                                        · left
                                          apply Subtype.ext
                                          have h1 := congrArg Subtype.val hs1
                                          have h0 := congrArg Subtype.val ht0
                                          dsimp at h1 h0
                                          linarith
                                      · rcases hmeet _ _ h.symm with ⟨ht0, hs1⟩ | ⟨ht1, hs0⟩
                                        · right; right
                                          constructor
                                          · apply Subtype.ext
                                            have := congrArg Subtype.val hs1
                                            dsimp at this
                                            change (s : ℝ) = 1
                                            linarith
                                          · apply Subtype.ext
                                            have := congrArg Subtype.val ht0
                                            dsimp at this
                                            change (t : ℝ) = 0
                                            linarith
                                        · left
                                          apply Subtype.ext
                                          have h1 := congrArg Subtype.val ht1
                                          have h0 := congrArg Subtype.val hs0
                                          dsimp at h1 h0
                                          linarith
                                      · left
                                        have hh := congrArg Subtype.val (hQ h)
                                        apply Subtype.ext
                                        dsimp at hh
                                        linarith
                                  let B := (Path.segment (a,c) (k,c)).symm
                                  let L := Path.segment (a,c) (a,d)
                                  let T := Path.segment (a,d) (k,d)
                                  let P := (B.trans L).trans T
                                  let U := Path.segment (k,d) (b,d)
                                  let R := (Path.segment (b,c) (b,d)).symm
                                  let V := (Path.segment (k,c) (b,c)).symm
                                  let Q := (U.trans R).trans V
                                  let χ := Path.segment (k,c) (k,d)
                                  obtain ⟨hBi, hBr⟩ := hH a k c hak
                                  obtain ⟨hLi, hLr⟩ := hV a c d hcd
                                  obtain ⟨hTi, hTr⟩ := hH a k d hak
                                  obtain ⟨hUi, hUr⟩ := hH k b d hkb
                                  obtain ⟨hRi, hRr⟩ := hV b c d hcd
                                  obtain ⟨hVi, hVr⟩ := hH k b c hkb
                                  obtain ⟨hχi, hχr⟩ := hV k c d hcd
                                  have hBsr : Set.range B = Set.range (Path.segment (a,c) (k,c)) := Path.symm_range _
                                  have hRsr : Set.range R = Set.range (Path.segment (b,c) (b,d)) := Path.symm_range _
                                  have hVsr : Set.range V = Set.range (Path.segment (k,c) (b,c)) := Path.symm_range _
                                  have hBsi : Function.Injective B := hBi.comp (by
                                    intro s t h
                                    apply Subtype.ext
                                    have h := congrArg Subtype.val h
                                    dsimp at h
                                    linarith)
                                  have hRsi : Function.Injective R := hRi.comp (by
                                    intro s t h
                                    apply Subtype.ext
                                    have h := congrArg Subtype.val h
                                    dsimp at h
                                    linarith)
                                  have hVsi : Function.Injective V := hVi.comp (by
                                    intro s t h
                                    apply Subtype.ext
                                    have h := congrArg Subtype.val h
                                    dsimp at h
                                    linarith)
                                  have hBLi : Function.Injective (B.trans L) := hcat _ _ _ B L hBsi hLi (by
                                    intro z hz hz'
                                    rw [hBsr, hBr] at hz
                                    rw [hLr] at hz'
                                    exact Prod.ext hz'.1 hz.2.2)
                                  have hPi : Function.Injective P := hcat _ _ _ (B.trans L) T hBLi hTi (by
                                    intro z hz hz'
                                    rw [Path.trans_range, hBsr, hBr, hLr] at hz
                                    rw [hTr] at hz'
                                    rcases hz with hz | hz
                                    · exact False.elim ((ne_of_lt hcd) (hz.2.2.symm.trans hz'.2.2))
                                    · exact Prod.ext hz.1 hz'.2.2)
                                  have hURi : Function.Injective (U.trans R) := hcat _ _ _ U R hUi hRsi (by
                                    intro z hz hz'
                                    rw [hUr] at hz
                                    rw [hRsr, hRr] at hz'
                                    exact Prod.ext hz'.1 hz.2.2)
                                  have hQi : Function.Injective Q := hcat _ _ _ (U.trans R) V hURi hVsi (by
                                    intro z hz hz'
                                    rw [Path.trans_range, hUr, hRsr, hRr] at hz
                                    rw [hVsr, hVr] at hz'
                                    rcases hz with hz | hz
                                    · exact False.elim ((ne_of_lt hcd) (hz'.2.2.symm.trans hz.2.2))
                                    · exact Prod.ext hz.1 hz'.2.2)
                                  have hPr : Set.range P = {z : ℝ × ℝ | (a ≤ z.1 ∧ z.1 ≤ k ∧ (z.2 = c ∨ z.2 = d)) ∨
                                      (z.1 = a ∧ c ≤ z.2 ∧ z.2 ≤ d)} := by
                                    change Set.range ((B.trans L).trans T) = _
                                    rw [Path.trans_range, Path.trans_range, hBsr, hBr, hLr, hTr]
                                    ext z
                                    simp only [mem_union, mem_ofPred_eq]
                                    tauto
                                  have hQr : Set.range Q = {z : ℝ × ℝ | (k ≤ z.1 ∧ z.1 ≤ b ∧ (z.2 = c ∨ z.2 = d)) ∨
                                      (z.1 = b ∧ c ≤ z.2 ∧ z.2 ≤ d)} := by
                                    change Set.range ((U.trans R).trans V) = _
                                    rw [Path.trans_range, Path.trans_range, hUr, hRsr, hRr, hVsr, hVr]
                                    ext z
                                    simp only [mem_union, mem_ofPred_eq]
                                    tauto
                                  have hχsi : Function.Injective χ.symm := hχi.comp (by
                                    intro s t h
                                    apply Subtype.ext
                                    have h := congrArg Subtype.val h
                                    dsimp at h
                                    linarith)
                                  refine ⟨P, Q, χ, hPi, hQi, hχi, hPr, hQr, hχr, ?_, ?_, ?_⟩
                                  · apply hloop _ _ P χ.symm hPi hχsi
                                    intro z hz hz'
                                    rw [hPr] at hz
                                    rw [Path.symm_range, hχr] at hz'
                                    rcases hz with hz | hz
                                    · rcases hz.2.2 with hy | hy
                                      · exact Or.inl (Prod.ext hz'.1 hy)
                                      · exact Or.inr (Prod.ext hz'.1 hy)
                                    · exact False.elim ((ne_of_lt hak) (hz.1.symm.trans hz'.1))
                                  · apply hloop _ _ χ Q hχi hQi
                                    intro z hz hz'
                                    rw [hχr] at hz
                                    rw [hQr] at hz'
                                    rcases hz' with hz' | hz'
                                    · rcases hz'.2.2 with hy | hy
                                      · exact Or.inl (Prod.ext hz.1 hy)
                                      · exact Or.inr (Prod.ext hz.1 hy)
                                    · exact False.elim ((ne_of_lt hkb) (hz.1.symm.trans hz'.1))
                                  · apply hloop _ _ P Q hPi hQi
                                    intro z hz hz'
                                    rw [hPr] at hz
                                    rw [hQr] at hz'
                                    rcases hz with hz | hz <;> rcases hz' with hz' | hz'
                                    · have hx : z.1 = k := le_antisymm hz.2.1 hz'.1
                                      rcases hz.2.2 with hy | hy
                                      · exact Or.inl (Prod.ext hx hy)
                                      · exact Or.inr (Prod.ext hx hy)
                                    · exact False.elim (not_le_of_gt hkb (hz'.1 ▸ hz.2.1))
                                    · exact False.elim (not_le_of_gt hak (hz.1 ▸ hz'.1))
                                    · exact False.elim (ne_of_lt (lt_trans hak hkb) (hz.1.symm.trans hz'.1))
            
                            have hranges (a k b c d : ℝ) (hak : a < k) (hkb : k < b) (hcd : c < d)
                                (P : Path (k,c) (k,d)) (Q : Path (k,d) (k,c)) (χ : Path (k,c) (k,d))
                                (hPr : Set.range P = {z : ℝ × ℝ | (a ≤ z.1 ∧ z.1 ≤ k ∧ (z.2 = c ∨ z.2 = d)) ∨
                                  (z.1 = a ∧ c ≤ z.2 ∧ z.2 ≤ d)})
                                (hQr : Set.range Q = {z : ℝ × ℝ | (k ≤ z.1 ∧ z.1 ≤ b ∧ (z.2 = c ∨ z.2 = d)) ∨
                                  (z.1 = b ∧ c ≤ z.2 ∧ z.2 ≤ d)})
                                (hχr : Set.range χ = {z : ℝ × ℝ | z.1 = k ∧ c ≤ z.2 ∧ z.2 ≤ d}) :
                                Set.range (P.trans χ.symm) = frontier (Icc a k ×ˢ Icc c d) ∧
                                Set.range (χ.trans Q) = frontier (Icc k b ×ˢ Icc c d) ∧
                                Set.range (P.trans Q) = frontier (Icc a b ×ˢ Icc c d) := by
                              have hfront (u v : ℝ) (huv : u < v) :
                                  frontier (Icc u v ×ˢ Icc c d) =
                                  {z : ℝ × ℝ | (u ≤ z.1 ∧ z.1 ≤ v ∧ (z.2 = c ∨ z.2 = d)) ∨
                                    ((z.1 = u ∨ z.1 = v) ∧ c ≤ z.2 ∧ z.2 ≤ d)} := by
                                rw [frontier_prod_eq, isClosed_Icc.closure_eq, isClosed_Icc.closure_eq,
                                  frontier_Icc huv.le, frontier_Icc hcd.le]
                                ext z
                                simp only [mem_union, mem_prod, mem_Icc, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
                                tauto
                              constructor
                              · rw [Path.trans_range, Path.symm_range, hPr, hχr, hfront a k hak]
                                ext z
                                simp only [mem_union, mem_ofPred_eq]
                                tauto
                              constructor
                              · rw [Path.trans_range, hχr, hQr, hfront k b hkb]
                                ext z
                                simp only [mem_union, mem_ofPred_eq]
                                tauto
                              · rw [Path.trans_range, hPr, hQr, hfront a b (lt_trans hak hkb)]
                                ext z
                                simp only [mem_union, mem_ofPred_eq]
                                constructor
                                · rintro ((⟨hx, hk, hy⟩ | ⟨hx, hc, hd⟩) | (⟨hk, hb, hy⟩ | ⟨hx, hc, hd⟩))
                                  · exact Or.inl ⟨hx, le_trans hk hkb.le, hy⟩
                                  · exact Or.inr ⟨Or.inl hx, hc, hd⟩
                                  · exact Or.inl ⟨le_trans hak.le hk, hb, hy⟩
                                  · exact Or.inr ⟨Or.inr hx, hc, hd⟩
                                · rintro (⟨ha, hb, hy⟩ | ⟨hx, hc, hd⟩)
                                  · rcases le_total z.1 k with hk | hk
                                    · exact Or.inl (Or.inl ⟨ha, hk, hy⟩)
                                    · exact Or.inr (Or.inl ⟨hk, hb, hy⟩)
                                  · rcases hx with hx | hx
                                    · exact Or.inl (Or.inr ⟨hx, hc, hd⟩)
                                    · exact Or.inr (Or.inr ⟨hx, hc, hd⟩)
            
                            obtain ⟨P,Q,χ,_,_,_,hp,hq,hχ,hleft,hright,houter⟩ := hpaths a k b c d hak hkb hcd
                            obtain ⟨hl,hr,ho⟩ := hranges a k b c d hak hkb hcd P Q χ hp hq hχ
                            exact ⟨P,Q,χ,hl,hr,ho,hleft,hright,houter⟩
          
                      obtain ⟨P,Q,χ,hl,hr,ho,hcl,hcr,hco⟩ := hvertical c h d a b hch hhd hab
                      have hswap (u v w x : ℝ) : Prod.swap '' frontier (Icc u v ×ˢ Icc w x) =
                          frontier (Icc w x ×ˢ Icc u v) := by
                        change (Homeomorph.prodComm ℝ ℝ) '' frontier _ = _
                        rw [(Homeomorph.prodComm ℝ ℝ).image_frontier]
                        exact congrArg frontier (Set.image_swap_prod (Icc u v) (Icc w x))
                      have hmap (u v : ℝ × ℝ) (γ : Path u v) :
                          Set.range (γ.map continuous_swap) = Prod.swap '' Set.range γ := by
                        exact Set.range_comp Prod.swap γ
                      refine ⟨P.map continuous_swap,Q.map continuous_swap,χ.map continuous_swap,?_,?_,?_,?_,?_,?_⟩
                      · rw [Path.map_symm, ← Path.map_trans, hmap, hl, hswap]
                      · rw [← Path.map_trans, hmap, hr, hswap]
                      · rw [← Path.map_trans, hmap, ho, hswap]
                      · intro s t heq
                        simp only [Path.map_symm, ← Path.map_trans, Path.map_coe, Function.comp_apply] at heq
                        exact hcl s t (Prod.swap_injective heq)
                      · intro s t heq
                        simp only [← Path.map_trans, Path.map_coe, Function.comp_apply] at heq
                        exact hcr s t (Prod.swap_injective heq)
                      · intro s t heq
                        simp only [← Path.map_trans, Path.map_coe, Function.comp_apply] at heq
                        exact hco s t (Prod.swap_injective heq)
        
                have hrev {x : ℝ × ℝ} (γ : Path x x)
                    (hc : ∀ s t, γ s = γ t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) :
                    ∀ s t, γ.symm s = γ.symm t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
                  intro s t he
                  rcases hc _ _ he with he | ⟨hs,ht⟩ | ⟨hs,ht⟩
                  · exact Or.inl (unitInterval.symm_inj.mp he)
                  · right; right
                    constructor
                    · simpa only [unitInterval.symm_symm, unitInterval.symm_zero] using congrArg unitInterval.symm hs
                    · simpa only [unitInterval.symm_symm, unitInterval.symm_one] using congrArg unitInterval.symm ht
                  · right; left
                    constructor
                    · simpa only [unitInterval.symm_symm, unitInterval.symm_one] using congrArg unitInterval.symm hs
                    · simpa only [unitInterval.symm_symm, unitInterval.symm_zero] using congrArg unitInterval.symm ht
                rcases hshape with ⟨k,l,hlo,hhi,hak,hkl,hlb⟩ | ⟨k,h,hlo,hhi,hak,hkb,hch,hhd⟩ |
                  ⟨k,h,hlo,hhi,hak,hkb,hch,hhd⟩ | ⟨k,l,hlo,hhi,hck,hkl,hld⟩
                · subst lo hi
                  obtain ⟨P,Q,χ,hpl,hqr,hpo,hpc,_,hpoc⟩ := hv a k b c d hak (lt_trans hkl hlb) hcd
                  obtain ⟨A,B,ξ,hal,hbr,hao,hac,hbc,haoc⟩ := hv k l b c d hkl hlb hcd
                  refine ⟨id,(k,c),(k,d),(l,c),(l,d),P,Q,χ,A,B,ξ,?_,?_,?_,hqr.trans hao.symm,hpo,hpc,hac,hbc,haoc,hpoc⟩
                  · exact hpl
                  · exact hal
                  · exact hbr
                · subst lo hi
                  obtain ⟨P,Q,χ,hpl,hqr,hpo,hpc,_,hpoc⟩ := hv a k b c d hak hkb hcd
                  obtain ⟨A,B,ξ,hal,hbr,hao,hac,hbc,haoc⟩ := hh k b c h d hkb hch hhd
                  exact ⟨id,(k,c),(k,d),(k,h),(b,h),P,Q,χ,A,B,ξ,hpl,hal,hbr,hqr.trans hao.symm,hpo,hpc,hac,hbc,haoc,hpoc⟩
                · subst lo hi
                  obtain ⟨P,Q,χ,hpl,hqr,hpo,hpc,hqc,hpoc⟩ := hv a k b c d hak hkb hcd
                  obtain ⟨A,B,ξ,hal,hbr,hao,hac,hbc,haoc⟩ := hh a k c h d hak hch hhd
                  refine ⟨![2,0,1],(k,c),(k,d),(a,h),(k,h),Q.symm,P.symm,χ,A,B,ξ,?_,hal,hbr,?_,?_,?_,hac,hbc,haoc,?_⟩
                  · rw [← Path.trans_symm, Path.symm_range]
                    exact hqr
                  · rw [← Path.symm_symm χ, ← Path.trans_symm, Path.symm_range]
                    exact hpl.trans hao.symm
                  · rw [← Path.trans_symm, Path.symm_range]
                    exact hpo
                  · simpa only [Path.trans_symm] using hrev (χ.trans Q) hqc
                  · simpa only [Path.trans_symm] using hrev (P.trans Q) hpoc
                · subst lo hi
                  obtain ⟨P,Q,χ,hpl,hqr,hpo,hpc,_,hpoc⟩ := hh a b c k d hab hck (lt_trans hkl hld)
                  obtain ⟨A,B,ξ,hal,hbr,hao,hac,hbc,haoc⟩ := hh a b k l d hab hkl hld
                  exact ⟨id,(a,k),(b,k),(a,l),(b,l),P,Q,χ,A,B,ξ,hpl,hal,hbr,hqr.trans hao.symm,hpo,hpc,hac,hbc,haoc,hpoc⟩
      
          have hContain (a b c d : ℝ) (lo hi : Fin 3 → ℝ × ℝ)
              (hshape : ((∃ k l : ℝ, lo = ![(a,c),(k,c),(l,c)] ∧ hi = ![(k,d),(l,d),(b,d)] ∧ a < k ∧ k < l ∧ l < b) ∨
                 (∃ k h : ℝ, lo = ![(a,c),(k,c),(k,h)] ∧ hi = ![(k,d),(b,h),(b,d)] ∧ a < k ∧ k < b ∧ c < h ∧ h < d) ∨
                 (∃ k h : ℝ, lo = ![(a,c),(a,h),(k,c)] ∧ hi = ![(k,h),(k,d),(b,d)] ∧ a < k ∧ k < b ∧ c < h ∧ h < d) ∨
                 (∃ k l : ℝ, lo = ![(a,c),(a,k),(a,l)] ∧ hi = ![(b,k),(b,l),(b,d)] ∧ c < k ∧ k < l ∧ l < d))) :
              ∀ i, (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2) ⊆
                (Icc a b ×ˢ Icc c d) := by
            rcases hshape with ⟨k,l,hlo,hhi,hak,hkl,hlb⟩ | ⟨k,h,hlo,hhi,hak,hkb,hch,hhd⟩ |
              ⟨k,h,hlo,hhi,hak,hkb,hch,hhd⟩ | ⟨k,l,hlo,hhi,hck,hkl,hld⟩
            all_goals
              subst lo hi
              intro i
              fin_cases i <;> intro z hz <;>
                simp only [Set.mem_prod,Set.mem_Icc] at hz ⊢ <;>
                dsimp at hz ⊢ <;>
                constructor <;> constructor <;> linarith [hz.1.1,hz.1.2,hz.2.1,hz.2.2]
      
          have hSix {X : Type} [TopologicalSpace X] (R : Set X) {x y u v : X}
              (P : Path x y) (Q : Path y x) (χ : Path x y)
              (A : Path u v) (B : Path v u) (ξ : Path u v)
              (hP : ∀ t, P t ∈ R) (hQ : ∀ t, Q t ∈ R) (hχ : ∀ t, χ t ∈ R)
              (hA : ∀ t, A t ∈ R) (hB : ∀ t, B t ∈ R) (hξ : ∀ t, ξ t ∈ R) :
              ∃ hx : x ∈ R, ∃ hy : y ∈ R, ∃ hu : u ∈ R, ∃ hv : v ∈ R,
              let x' : R := ⟨x,hx⟩
              let y' : R := ⟨y,hy⟩
              let u' : R := ⟨u,hu⟩
              let v' : R := ⟨v,hv⟩
              ∃ P' : Path x' y', ∃ Q' : Path y' x', ∃ χ' : Path x' y',
              ∃ A' : Path u' v', ∃ B' : Path v' u', ∃ ξ' : Path u' v',
                P'.map continuous_subtype_val = P ∧ Q'.map continuous_subtype_val = Q ∧
                χ'.map continuous_subtype_val = χ ∧ A'.map continuous_subtype_val = A ∧
                B'.map continuous_subtype_val = B ∧ ξ'.map continuous_subtype_val = ξ := by
            have hLift {x y : X} (γ : Path x y) (hγ : ∀ t, γ t ∈ R)
                (hx : x ∈ R) (hy : y ∈ R) :
                ∃ δ : Path (⟨x,hx⟩ : R) ⟨y,hy⟩, δ.map continuous_subtype_val = γ := by
              let δ : Path (⟨x,hx⟩ : R) ⟨y,hy⟩ :=
                { toContinuousMap := ⟨fun t => ⟨γ t,hγ t⟩, γ.continuous.subtype_mk hγ⟩
                  source' := Subtype.ext γ.source
                  target' := Subtype.ext γ.target }
              refine ⟨δ, ?_⟩
              apply Path.ext
              funext t
              rfl
            have hx : x ∈ R := by simpa using hP 0
            have hy : y ∈ R := by simpa using hP 1
            have hu : u ∈ R := by simpa using hA 0
            have hv : v ∈ R := by simpa using hA 1
            obtain ⟨P',hP'⟩ := hLift P hP hx hy
            obtain ⟨Q',hQ'⟩ := hLift Q hQ hy hx
            obtain ⟨χ',hχ'⟩ := hLift χ hχ hx hy
            obtain ⟨A',hA'⟩ := hLift A hA hu hv
            obtain ⟨B',hB'⟩ := hLift B hB hv hu
            obtain ⟨ξ',hξ'⟩ := hLift ξ hξ hu hv
            exact ⟨hx,hy,hu,hv,P',Q',χ',A',B',ξ',hP',hQ',hχ',hA',hB',hξ'⟩
      
          let R := Icc a b ×ˢ Icc c d
          obtain ⟨r,x,y,u,v,P,Q,χ,A,B,ξ,hl,h1,h2,hr,ho,hcl,hc1,hc2,hci,hco⟩ := hTree a b c d hab hcd lo hi hshape
          have hc := hContain a b c d lo hi hshape
          have hf (i) : frontier (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2) ⊆ R := by
            have hclosed : IsClosed (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2) := isClosed_Icc.prod isClosed_Icc
            intro z hz
            exact hc i (hclosed.closure_eq ▸ frontier_subset_closure hz)
          have hfR : frontier R ⊆ R := by
            intro z hz
            have hclosed : IsClosed R := isClosed_Icc.prod isClosed_Icc
            exact hclosed.closure_eq ▸ frontier_subset_closure hz
          have hsplit {x y z : ℝ × ℝ} (P : Path x y) (Q : Path y z)
              (hpq : Set.range (P.trans Q) ⊆ R) :
              (∀ t, P t ∈ R) ∧ (∀ t, Q t ∈ R) := by
            constructor
            · intro t; apply hpq; rw [Path.trans_range]; exact Or.inl ⟨t,rfl⟩
            · intro t; apply hpq; rw [Path.trans_range]; exact Or.inr ⟨t,rfl⟩
          obtain ⟨hP,hQ⟩ := hsplit P Q (ho ▸ hfR)
          obtain ⟨_,hχs⟩ := hsplit P χ.symm (hl ▸ hf (r 0))
          have hχ' (t) : χ t ∈ R := by
            have hh := hχs (unitInterval.symm t)
            simpa only [Path.symm_apply,Function.comp_apply,unitInterval.symm_symm] using hh
          have hright : Set.range (χ.trans Q) ⊆ R := by
            rw [Path.trans_range]
            rintro z (⟨t,rfl⟩ | ⟨t,rfl⟩)
            · exact hχ' t
            · exact hQ t
          obtain ⟨hA,hB⟩ := hsplit A B (hr ▸ hright)
          obtain ⟨hξ,_⟩ := hsplit ξ B (h2 ▸ hf (r 2))
          obtain ⟨hx,hy,hu,hv,P',Q',χ',A',B',ξ',hPm,hQm,hχm,hAm,hBm,hξm⟩ :=
            hSix R P Q χ A B ξ hP hQ hχ' hA hB hξ
          have hL : (P'.trans χ'.symm).map continuous_subtype_val = P.trans χ.symm := by
            rw [Path.map_trans,← Path.map_symm,hPm,hχm]
          have h1m : (A'.trans ξ'.symm).map continuous_subtype_val = A.trans ξ.symm := by
            rw [Path.map_trans,← Path.map_symm,hAm,hξm]
          have h2m : (ξ'.trans B').map continuous_subtype_val = ξ.trans B := by
            rw [Path.map_trans,hξm,hBm]
          have hRm : (χ'.trans Q').map continuous_subtype_val = χ.trans Q := by
            rw [Path.map_trans,hχm,hQm]
          have hIm : (A'.trans B').map continuous_subtype_val = A.trans B := by
            rw [Path.map_trans,hAm,hBm]
          have hOm : (P'.trans Q').map continuous_subtype_val = P.trans Q := by
            rw [Path.map_trans,hPm,hQm]
          have hRange {x y : R} (δ : Path x y) (γ : Path x.val y.val)
              (he : δ.map continuous_subtype_val = γ) :
              Set.range (fun t => (δ t).val) = Set.range γ := by
            exact congrArg (fun p : Path x.val y.val => Set.range p) he
          have hColl {x : R} (δ : Path x x) (γ : Path x.val x.val)
              (he : δ.map continuous_subtype_val = γ)
              (hc : ∀ s t, γ s = γ t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) :
              ∀ s t, δ s = δ t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
            intro s t hst
            apply hc s t
            have hh := congrArg Subtype.val hst
            change (δ.map continuous_subtype_val) s = (δ.map continuous_subtype_val) t at hh
            simpa only [he] using hh
          refine ⟨r,⟨x,hx⟩,⟨y,hy⟩,⟨u,hu⟩,⟨v,hv⟩,P',Q',χ',A',B',ξ',
            (hRange _ _ hL).trans hl,(hRange _ _ h1m).trans h1,(hRange _ _ h2m).trans h2,?_,
            (hRange _ _ hOm).trans ho,hColl _ _ hL hcl,hColl _ _ h1m hc1,
            hColl _ _ h2m hc2,hColl _ _ hIm hci,hColl _ _ hOm hco⟩
          ext z
          constructor
          · rintro ⟨t,rfl⟩
            have hh : ((χ'.trans Q') t).val ∈ Set.range (A.trans B) := by
              rw [← hr,← hRange _ _ hRm]
              exact ⟨t,rfl⟩
            rw [← hRange _ _ hIm] at hh
            obtain ⟨s,hs⟩ := hh
            exact ⟨s,Subtype.ext hs⟩
          · rintro ⟨t,rfl⟩
            have hh : ((A'.trans B') t).val ∈ Set.range (χ.trans Q) := by
              rw [hr,← hRange _ _ hIm]
              exact ⟨t,rfl⟩
            rw [← hRange _ _ hRm] at hh
            obtain ⟨s,hs⟩ := hh
            exact ⟨s,Subtype.ext hs⟩
    
      have hRaw (K : Set (ℝ × ℝ)) (f : C(K,S)) (hf : IsEmbedding f)
          (a b c d : K) (P χ : Path a b) (Q : Path b a) (A ξ : Path c d) (B : Path d c)
          (F : Fin 3 → C(Metric.closedBall (0 : Schoenflies.Plane) 1,S))
          (hF : ∀ i, IsEmbedding (F i))
          (m : Fin 3 → Metric.closedBall (0 : Schoenflies.Plane) 1)
          (hm : ∀ i, ‖(m i).val‖ < 1)
          (honly : ∀ i z, F i z ∈ M.cover.branch ↔ z = m i)
          (hcell0 : Set.range (fun t => f ((P.trans χ.symm) t)) = F 0 '' {z | ‖z.val‖ = 1})
          (hcell1 : Set.range (fun t => f ((A.trans ξ.symm) t)) = F 1 '' {z | ‖z.val‖ = 1})
          (hcell2 : Set.range (fun t => f ((ξ.trans B) t)) = F 2 '' {z | ‖z.val‖ = 1})
          (hcoll0 : ∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t →
            s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
          (hcoll1 : ∀ s t, (A.trans ξ.symm) s = (A.trans ξ.symm) t →
            s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
          (hcoll2 : ∀ s t, (ξ.trans B) s = (ξ.trans B) t →
            s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
          (hinnercoll : ∀ s t, (A.trans B) s = (A.trans B) t →
            s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
          (hrightsub : Set.range (χ.trans Q) ⊆ Set.range (A.trans B))
          (γ : C(Interval,E)) (hγπ : ∀ t, M.cover.projection (γ t) = f ((P.trans Q) t)) :
          γ 1 = M.cover.deck (γ 0) := by
            as_aux_lemma =>
          have hThree (a b c d : M.cover.unramifiedBase)
            (P χ : Path a b) (Q : Path b a) (A ξ : Path c d) (B : Path d c)
            (f : Fin 3 → C(Metric.closedBall (0 : Schoenflies.Plane) 1,S))
            (hf : ∀ i, IsEmbedding (f i))
            (m : Fin 3 → Metric.closedBall (0 : Schoenflies.Plane) 1)
            (hm : ∀ i, ‖(m i).val‖ < 1)
            (honly : ∀ i z, f i z ∈ M.cover.branch ↔ z = m i)
            (hcell0 : Set.range (fun t => ((P.trans χ.symm) t).val) = f 0 '' {z | ‖z.val‖ = 1})
            (hcell1 : Set.range (fun t => ((A.trans ξ.symm) t).val) = f 1 '' {z | ‖z.val‖ = 1})
            (hcell2 : Set.range (fun t => ((ξ.trans B) t).val) = f 2 '' {z | ‖z.val‖ = 1})
            (hcoll0 : ∀ s t, ((P.trans χ.symm) s).val = ((P.trans χ.symm) t).val →
              s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
            (hcoll1 : ∀ s t, ((A.trans ξ.symm) s).val = ((A.trans ξ.symm) t).val →
              s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
            (hcoll2 : ∀ s t, ((ξ.trans B) s).val = ((ξ.trans B) t).val →
              s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
            (hinnercoll : ∀ s t, ((A.trans B) s).val = ((A.trans B) t).val →
              s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
            (hrightsub : Set.range (fun t => ((χ.trans Q) t).val) ⊆
              Set.range (fun t => ((A.trans B) t).val))
            (γ : C(Interval,E)) (hγπ : ∀ t, M.cover.projection (γ t) = ((P.trans Q) t).val) :
            γ 1 = M.cover.deck (γ 0) := by
              as_aux_lemma =>
              have hOne (f : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
                (m : Metric.closedBall (0 : Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1)
                (honly : ∀ z, f z ∈ M.cover.branch ↔ z = m)
                (β : C(Interval,S)) (hends : β 0 = β 1)
                (hcoll : ∀ s t, β s = β t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
                (hrange : Set.range β = f '' {z | ‖z.val‖ = 1})
                (γ : C(Interval,E)) (hγπ : ∀ t, M.cover.projection (γ t) = β t) :
                γ 1 = M.cover.deck (γ 0) := by
                let h := hf.toHomeomorph
                have hβrange (t : Interval) : β t ∈ Set.range f := by
                  have ht : β t ∈ Set.range β := Set.mem_range_self t
                  rw [hrange] at ht
                  rcases ht with ⟨z,hz,hzt⟩
                  exact ⟨z,hzt⟩
                let bs : C(Interval,Set.range f) :=
                  ⟨fun t => ⟨β t,hβrange t⟩,β.continuous.subtype_mk hβrange⟩
                let B : C(Interval,Metric.closedBall (0 : Schoenflies.Plane) 1) :=
                  ⟨h.symm ∘ bs,h.symm.continuous.comp bs.continuous⟩
                have hBproj (t) : f (B t) = β t := congrArg Subtype.val (h.apply_symm_apply (bs t))
                have hBends : B 0 = B 1 := hf.injective (by rw [hBproj,hBproj,hends])
                have hBcoll : ∀ s t, B s = B t →
                    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
                  intro s t he
                  apply hcoll s t
                  rw [← hBproj s,← hBproj t,he]
                have hBrange : Set.range B = {z | ‖z.val‖ = 1} := by
                  ext z
                  constructor
                  · rintro ⟨t,rfl⟩
                    have ht : β t ∈ f '' {z | ‖z.val‖ = 1} := hrange ▸ Set.mem_range_self t
                    rcases ht with ⟨w,hw,hwt⟩
                    have he : w = B t := hf.injective (hwt.trans (hBproj t).symm)
                    exact he ▸ hw
                  · intro hz
                    have hfz : f z ∈ Set.range β := by
                      rw [hrange]
                      exact ⟨z,hz,rfl⟩
                    rcases hfz with ⟨t,ht⟩
                    exact ⟨t,hf.injective ((hBproj t).trans ht)⟩
                apply M.one_branch_disc_boundary_sheet_exchange f hf m hm honly B hBends hBcoll hBrange γ
                intro t
                rw [hBproj]
                exact hγπ t
              have hTwo (q : BranchedDoubleCover E S) (a b : q.unramifiedBase)
                (P χ : Path a b) (Q : Path b a)
                (hleft : ∀ γ : C(Interval,E),
                  (∀ t, q.projection (γ t) = ((P.trans χ.symm) t).val) → γ 1 = q.deck (γ 0))
                (hright : ∀ γ : C(Interval,E),
                  (∀ t, q.projection (γ t) = ((χ.trans Q) t).val) → γ 1 = q.deck (γ 0))
                (γ : C(Interval,E)) (hγπ : ∀ t, q.projection (γ t) = ((P.trans Q) t).val) :
                γ 1 = γ 0 := by
                  as_aux_lemma =>
                  have hswap (q : BranchedDoubleCover E S) (a : q.unramifiedBase) (ℓ : Path a a)
                    (hexchange : ∀ γ : C(Interval, E),
                      (∀ t, q.projection (γ t) = (ℓ t).val) → γ 1 = q.deck (γ 0)) :
                    ∀ x : q.unramifiedProjection ⁻¹' {a},
                      (q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk ℓ) x).val.val =
                        q.deck x.val.val := by
                    intro x
                    let g := q.unramified_isCoveringMap.liftPath ℓ.toContinuousMap x.val
                      (ℓ.source.trans x.property.symm)
                    let γ : C(Interval, E) := ⟨fun t => (g t).val,
                      continuous_subtype_val.comp g.continuous⟩
                    have hγπ (t : Interval) : q.projection (γ t) = (ℓ t).val := by
                      have h := congrFun (q.unramified_isCoveringMap.liftPath_lifts
                        ℓ.toContinuousMap x.val (ℓ.source.trans x.property.symm)) t
                      exact congrArg Subtype.val h
                    have hs := hexchange γ hγπ
                    change (g 1).val = q.deck (g 0).val at hs
                    have hzero : g 0 = x.val := q.unramified_isCoveringMap.liftPath_zero ..
                    rw [hzero] at hs
                    exact hs
                  have hcomp (q : BranchedDoubleCover E S) (a b : q.unramifiedBase)
                    (P χ : Path a b) (Q : Path b a) (x : q.unramifiedProjection ⁻¹' {a}) :
                    q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (P.trans Q)) x =
                      q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (χ.trans Q))
                        (q.unramified_isCoveringMap.monodromy
                          (Path.Homotopic.Quotient.mk (P.trans χ.symm)) x) := by
                    have hclass : (Path.Homotopic.Quotient.mk (P.trans χ.symm)).trans
                        (Path.Homotopic.Quotient.mk (χ.trans Q)) =
                        Path.Homotopic.Quotient.mk (P.trans Q) := by
                      simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
                      rw [Path.Homotopic.Quotient.trans_assoc,
                        ← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk χ).symm,
                        Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
                    rw [← hclass]
                    exact q.unramified_isCoveringMap.monodromy_trans_apply _ _ x
                  have hback (q : BranchedDoubleCover E S) (a : q.unramifiedBase) (ℓ : Path a a)
                    (hmon : ∀ x : q.unramifiedProjection ⁻¹' {a},
                      (q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk ℓ) x).val.val =
                        x.val.val)
                    (γ : C(Interval, E)) (hγπ : ∀ t, q.projection (γ t) = (ℓ t).val) :
                    γ 1 = γ 0 := by
                    have hγavoid (t : Interval) : q.projection (γ t) ∉ q.branch := by
                      rw [hγπ]
                      exact (ℓ t).property
                    let Γ : C(Interval, q.unramifiedTotal) :=
                      ⟨fun t => ⟨γ t, hγavoid t⟩, γ.continuous.subtype_mk hγavoid⟩
                    have hΓπ : q.unramifiedProjection ∘ Γ = ℓ := by
                      funext t
                      exact Subtype.ext (hγπ t)
                    let x : q.unramifiedProjection ⁻¹' {a} :=
                      ⟨Γ 0, by
                        change q.unramifiedProjection (Γ 0) = a
                        exact (congrFun hΓπ 0).trans ℓ.source⟩
                    have hΓlift : Γ = q.unramified_isCoveringMap.liftPath ℓ.toContinuousMap x.val
                        (ℓ.source.trans x.property.symm) :=
                      (q.unramified_isCoveringMap.eq_liftPath_iff' (ℓ.source.trans x.property.symm)).mpr
                        ⟨hΓπ, rfl⟩
                    have hs := hmon x
                    change (q.unramified_isCoveringMap.liftPath ℓ.toContinuousMap x.val
                      (ℓ.source.trans x.property.symm) 1).val = γ 0 at hs
                    rw [← hΓlift] at hs
                    exact hs
                  apply hback q a (P.trans Q) _ γ hγπ
                  intro x
                  have hL := hswap q a (P.trans χ.symm) hleft x
                  have hR := hswap q a (χ.trans Q) hright
                    (q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (P.trans χ.symm)) x)
                  rw [hcomp]
                  rw [hR,hL,q.deck_involution]
              have hMixed (q : BranchedDoubleCover E S) (a b : q.unramifiedBase)
                (P χ : Path a b) (Q : Path b a)
                (hleft : ∀ γ : C(Interval,E),
                  (∀ t, q.projection (γ t) = ((P.trans χ.symm) t).val) → γ 1 = q.deck (γ 0))
                (hright : ∀ γ : C(Interval,E),
                  (∀ t, q.projection (γ t) = ((χ.trans Q) t).val) → γ 1 = γ 0)
                (γ : C(Interval,E)) (hγπ : ∀ t, q.projection (γ t) = ((P.trans Q) t).val) :
                γ 1 = q.deck (γ 0) := by
                  as_aux_lemma =>
                  have hswap (q : BranchedDoubleCover E S) (a : q.unramifiedBase) (ℓ : Path a a)
                    (hexchange : ∀ γ : C(Interval, E),
                      (∀ t, q.projection (γ t) = (ℓ t).val) → γ 1 = q.deck (γ 0)) :
                    ∀ x : q.unramifiedProjection ⁻¹' {a},
                      (q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk ℓ) x).val.val =
                        q.deck x.val.val := by
                    intro x
                    let g := q.unramified_isCoveringMap.liftPath ℓ.toContinuousMap x.val
                      (ℓ.source.trans x.property.symm)
                    let γ : C(Interval, E) := ⟨fun t => (g t).val,
                      continuous_subtype_val.comp g.continuous⟩
                    have hγπ (t : Interval) : q.projection (γ t) = (ℓ t).val := by
                      have h := congrFun (q.unramified_isCoveringMap.liftPath_lifts
                        ℓ.toContinuousMap x.val (ℓ.source.trans x.property.symm)) t
                      exact congrArg Subtype.val h
                    have hs := hexchange γ hγπ
                    change (g 1).val = q.deck (g 0).val at hs
                    have hzero : g 0 = x.val := q.unramified_isCoveringMap.liftPath_zero ..
                    rw [hzero] at hs
                    exact hs
                  have hclosed (q : BranchedDoubleCover E S) (a : q.unramifiedBase) (ℓ : Path a a)
                    (hclosed : ∀ γ : C(Interval, E),
                      (∀ t, q.projection (γ t) = (ℓ t).val) → γ 1 = γ 0) :
                    ∀ x : q.unramifiedProjection ⁻¹' {a},
                      q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk ℓ) x = x := by
                    intro x
                    let g := q.unramified_isCoveringMap.liftPath ℓ.toContinuousMap x.val
                      (ℓ.source.trans x.property.symm)
                    let γ : C(Interval, E) := ⟨fun t => (g t).val,
                      continuous_subtype_val.comp g.continuous⟩
                    have hγπ (t : Interval) : q.projection (γ t) = (ℓ t).val := by
                      have h := congrFun (q.unramified_isCoveringMap.liftPath_lifts
                        ℓ.toContinuousMap x.val (ℓ.source.trans x.property.symm)) t
                      exact congrArg Subtype.val h
                    have hs := hclosed γ hγπ
                    change (g 1).val = (g 0).val at hs
                    have hzero : g 0 = x.val := q.unramified_isCoveringMap.liftPath_zero ..
                    rw [hzero] at hs
                    exact Subtype.ext (Subtype.ext hs)
                  have hcomp (q : BranchedDoubleCover E S) (a b : q.unramifiedBase)
                    (P χ : Path a b) (Q : Path b a) (x : q.unramifiedProjection ⁻¹' {a}) :
                    q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (P.trans Q)) x =
                      q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (χ.trans Q))
                        (q.unramified_isCoveringMap.monodromy
                          (Path.Homotopic.Quotient.mk (P.trans χ.symm)) x) := by
                    have hclass : (Path.Homotopic.Quotient.mk (P.trans χ.symm)).trans
                        (Path.Homotopic.Quotient.mk (χ.trans Q)) =
                        Path.Homotopic.Quotient.mk (P.trans Q) := by
                      simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
                      rw [Path.Homotopic.Quotient.trans_assoc,
                        ← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk χ).symm,
                        Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
                    rw [← hclass]
                    exact q.unramified_isCoveringMap.monodromy_trans_apply _ _ x
                  have hback (q : BranchedDoubleCover E S) (a : q.unramifiedBase) (ℓ : Path a a)
                    (hmon : ∀ x : q.unramifiedProjection ⁻¹' {a},
                      (q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk ℓ) x).val.val =
                        q.deck x.val.val)
                    (γ : C(Interval, E)) (hγπ : ∀ t, q.projection (γ t) = (ℓ t).val) :
                    γ 1 = q.deck (γ 0) := by
                    have hγavoid (t : Interval) : q.projection (γ t) ∉ q.branch := by
                      rw [hγπ]
                      exact (ℓ t).property
                    let Γ : C(Interval, q.unramifiedTotal) :=
                      ⟨fun t => ⟨γ t, hγavoid t⟩, γ.continuous.subtype_mk hγavoid⟩
                    have hΓπ : q.unramifiedProjection ∘ Γ = ℓ := by
                      funext t
                      exact Subtype.ext (hγπ t)
                    let x : q.unramifiedProjection ⁻¹' {a} :=
                      ⟨Γ 0, by
                        change q.unramifiedProjection (Γ 0) = a
                        exact (congrFun hΓπ 0).trans ℓ.source⟩
                    have hΓlift : Γ = q.unramified_isCoveringMap.liftPath ℓ.toContinuousMap x.val
                        (ℓ.source.trans x.property.symm) :=
                      (q.unramified_isCoveringMap.eq_liftPath_iff' (ℓ.source.trans x.property.symm)).mpr
                        ⟨hΓπ, rfl⟩
                    have hs := hmon x
                    change (q.unramified_isCoveringMap.liftPath ℓ.toContinuousMap x.val
                      (ℓ.source.trans x.property.symm) 1).val = q.deck (γ 0) at hs
                    rw [← hΓlift] at hs
                    exact hs
                  apply hback q a (P.trans Q) _ γ hγπ
                  intro x
                  have hL := hswap q a (P.trans χ.symm) hleft x
                  have hR := hclosed q a (χ.trans Q) hright
                    (q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (P.trans χ.symm)) x)
                  rw [hcomp,hR]
                  exact hL
              have hTransport (β α : C(Interval, S))
                (hβcoll : ∀ s t, β s = β t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
                (hβavoid : ∀ t, β t ∉ M.cover.branch)
                (g η : C(Interval, E)) (hgπ : ∀ t, M.cover.projection (g t) = β t)
                (hgclosed : g 0 = g 1) (hαrange : Set.range α ⊆ Set.range β)
                (hαends : α 0 = α 1) (hηπ : ∀ t, M.cover.projection (η t) = α t) :
                η 0 = η 1 := by
                letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
                have hfix (t : Interval) : M.cover.deck (g t) ≠ g t := by
                  intro hf
                  have hb := (M.cover.fixed_iff_branch (g t)).mp hf
                  rw [hgπ t] at hb
                  exact hβavoid t hb
                have hd : Disjoint (Set.range g) (M.cover.deck '' Set.range g) := by
                  apply Set.disjoint_left.mpr
                  rintro y ⟨s, rfl⟩ ⟨z, ⟨t, rfl⟩, hst⟩
                  have hb : β s = β t := by
                    rw [← hgπ s, ← hgπ t, ← hst, M.cover.projection_deck]
                  rcases hβcoll s t hb with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · subst s; exact hfix t hst
                  · exact hfix 0 (by simpa only [← hgclosed] using hst)
                  · exact hfix 0 (by simpa only [← hgclosed] using hst)
                have hc1 : IsClosed (Set.range g) := (isCompact_range g.continuous).isClosed
                have hc2 : IsClosed (M.cover.deck '' Set.range g) :=
                  ((isCompact_range g.continuous).image M.cover.deck.continuous).isClosed
                have hsub : Set.range η ⊆ Set.range g ∪ M.cover.deck '' Set.range g := by
                  rintro y ⟨s, rfl⟩
                  obtain ⟨t, ht⟩ := hαrange (Set.mem_range_self s)
                  have hπ : M.cover.projection (g t) = M.cover.projection (η s) :=
                    (hgπ t).trans (ht.trans (hηπ s).symm)
                  rcases (M.cover.fiber_pair (g t) (η s)).mp hπ with he | he
                  · exact Or.inl ⟨t, he.symm⟩
                  · exact Or.inr ⟨g t, Set.mem_range_self t, he.symm⟩
                have hπends : M.cover.projection (η 0) = M.cover.projection (η 1) :=
                  (hηπ 0).trans (hαends.trans (hηπ 1).symm)
                rcases (M.cover.fiber_pair (η 0) (η 1)).mp hπends with he | he
                · exact he.symm
                · have hboth : (Set.range η ∩ Set.range g).Nonempty ∧
                      (Set.range η ∩ M.cover.deck '' Set.range g).Nonempty := by
                    rcases hsub (Set.mem_range_self 0) with h0 | h0
                    · exact ⟨⟨η 0, Set.mem_range_self 0, h0⟩,
                        ⟨η 1, Set.mem_range_self 1, ⟨η 0, h0, he.symm⟩⟩⟩
                    · obtain ⟨z, hz, hz0⟩ := h0
                      have h1 : η 1 = z := by rw [he, ← hz0, M.cover.deck_involution]
                      exact ⟨⟨η 1, Set.mem_range_self 1, h1 ▸ hz⟩,
                        ⟨η 0, Set.mem_range_self 0, ⟨z, hz, hz0⟩⟩⟩
                  obtain ⟨y, hy⟩ := isPreconnected_closed_iff.mp
                    (isConnected_range η.continuous).isPreconnected
                    (Set.range g) (M.cover.deck '' Set.range g) hc1 hc2 hsub hboth.1 hboth.2
                  exact False.elim (Set.disjoint_left.mp hd hy.2.1 hy.2.2)
              let loop0 : C(Interval,S) := ⟨fun t => ((P.trans χ.symm) t).val,
                continuous_subtype_val.comp (P.trans χ.symm).continuous⟩
              let loop1 : C(Interval,S) := ⟨fun t => ((A.trans ξ.symm) t).val,
                continuous_subtype_val.comp (A.trans ξ.symm).continuous⟩
              let loop2 : C(Interval,S) := ⟨fun t => ((ξ.trans B) t).val,
                continuous_subtype_val.comp (ξ.trans B).continuous⟩
              have h0ends : loop0 0 = loop0 1 := congrArg Subtype.val
                ((P.trans χ.symm).source.trans (P.trans χ.symm).target.symm)
              have h1ends : loop1 0 = loop1 1 := congrArg Subtype.val
                ((A.trans ξ.symm).source.trans (A.trans ξ.symm).target.symm)
              have h2ends : loop2 0 = loop2 1 := congrArg Subtype.val
                ((ξ.trans B).source.trans (ξ.trans B).target.symm)
              have hs0 := hOne (f 0) (hf 0) (m 0) (hm 0) (honly 0) loop0 h0ends hcoll0 hcell0
              have hs1 := hOne (f 1) (hf 1) (m 1) (hm 1) (honly 1) loop1 h1ends hcoll1 hcell1
              have hs2 := hOne (f 2) (hf 2) (m 2) (hm 2) (honly 2) loop2 h2ends hcoll2 hcell2
              have hInnerClosed := hTwo M.cover c d A ξ B hs1 hs2
              let β : C(Interval,S) := ⟨fun t => ((A.trans B) t).val,
                continuous_subtype_val.comp (A.trans B).continuous⟩
              let α : C(Interval,S) := ⟨fun t => ((χ.trans Q) t).val,
                continuous_subtype_val.comp (χ.trans Q).continuous⟩
              have hβavoid (t : Interval) : β t ∉ M.cover.branch := ((A.trans B) t).property
              letI : ContractibleSpace Interval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
              letI : LocallyPathConnectedSpace Interval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
              obtain ⟨x,hx⟩ := M.cover.projection_surjective (β 0)
              obtain ⟨g,hg,_⟩ := M.cover.unbranched_cover.existsUnique_continuousMap_lifts β hx hβavoid
              have hgπ (t : Interval) : M.cover.projection (g t) = β t := congrFun hg.2 t
              have hgclosed : g 0 = g 1 := (hInnerClosed g hgπ).symm
              have hαends : α 0 = α 1 := congrArg Subtype.val
                ((χ.trans Q).source.trans (χ.trans Q).target.symm)
              have hRightClosed : ∀ η : C(Interval,E),
                  (∀ t, M.cover.projection (η t) = ((χ.trans Q) t).val) → η 1 = η 0 := by
                intro η hηπ
                exact (hTransport β α hinnercoll hβavoid g η hgπ hgclosed hrightsub hαends hηπ).symm
              exact hMixed M.cover a b P χ Q hs0 hRightClosed γ hγπ
          have hPhi {X : Type} [TopologicalSpace X] (K : Set X) (f : C(K,S)) (hf : IsEmbedding f) :
            ∃ Φ : C({z : K | f z ∉ M.cover.branch},M.cover.unramifiedBase),
              IsEmbedding Φ ∧ (∀ z, (Φ z).val = f z.val) := by
            let Φ : C({z : K | f z ∉ M.cover.branch},M.cover.unramifiedBase) :=
              ⟨fun z => ⟨f z.val,z.property⟩,
                (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
            have hcomp : IsEmbedding (Subtype.val ∘ Φ) := hf.comp IsEmbedding.subtypeVal
            exact ⟨Φ,IsEmbedding.subtypeVal.of_comp_iff.mp hcomp,fun _ => rfl⟩
          have hLift {X : Type} [TopologicalSpace X] (K : Set X) (f : C(K,S)) (a b : K)
            (ha : f a ∉ M.cover.branch) (hb : f b ∉ M.cover.branch)
            (P : Path a b) (hP : ∀ t, f (P t) ∉ M.cover.branch) :
            ∃ Q : Path (⟨a,ha⟩ : {z : K | f z ∉ M.cover.branch}) ⟨b,hb⟩,
              ∀ t, (Q t).val = P t := by
            let r : C(Interval,{z : K | f z ∉ M.cover.branch}) :=
              ⟨fun t => ⟨P t,hP t⟩,P.continuous.subtype_mk hP⟩
            let Q : Path (⟨a,ha⟩ : {z : K | f z ∉ M.cover.branch}) ⟨b,hb⟩ :=
              ⟨r,Subtype.ext P.source,Subtype.ext P.target⟩
            exact ⟨Q,fun _ => rfl⟩
          have hBoundaryAvoid (i : Fin 3) : ∀ y ∈ F i '' {z | ‖z.val‖ = 1}, y ∉ M.cover.branch := by
            rintro y ⟨z,hz,rfl⟩ hy
            have he := (honly i z).mp hy
            have hnorm : ‖(m i).val‖ = 1 := he ▸ hz
            exact (ne_of_lt (hm i)) hnorm
          have hLoopAvoid0 : ∀ z ∈ Set.range (P.trans χ.symm), f z ∉ M.cover.branch := by
            rintro z ⟨t,rfl⟩
            apply hBoundaryAvoid 0
            rw [← hcell0]
            exact Set.mem_range_self t
          have hLoopAvoid1 : ∀ z ∈ Set.range (A.trans ξ.symm), f z ∉ M.cover.branch := by
            rintro z ⟨t,rfl⟩
            apply hBoundaryAvoid 1
            rw [← hcell1]
            exact Set.mem_range_self t
          have hLoopAvoid2 : ∀ z ∈ Set.range (ξ.trans B), f z ∉ M.cover.branch := by
            rintro z ⟨t,rfl⟩
            apply hBoundaryAvoid 2
            rw [← hcell2]
            exact Set.mem_range_self t
          have hPavoid (t) : f (P t) ∉ M.cover.branch := by
            apply hLoopAvoid0
            rw [Path.trans_range]
            exact Or.inl (Set.mem_range_self t)
          have hχavoid (t) : f (χ t) ∉ M.cover.branch := by
            apply hLoopAvoid0
            rw [Path.trans_range,Path.symm_range]
            exact Or.inr (Set.mem_range_self t)
          have hAavoid (t) : f (A t) ∉ M.cover.branch := by
            apply hLoopAvoid1
            rw [Path.trans_range]
            exact Or.inl (Set.mem_range_self t)
          have hξavoid (t) : f (ξ t) ∉ M.cover.branch := by
            apply hLoopAvoid1
            rw [Path.trans_range,Path.symm_range]
            exact Or.inr (Set.mem_range_self t)
          have hBavoid (t) : f (B t) ∉ M.cover.branch := by
            apply hLoopAvoid2
            rw [Path.trans_range]
            exact Or.inr (Set.mem_range_self t)
          have hQavoid (t) : f (Q t) ∉ M.cover.branch := by
            have ht : Q t ∈ Set.range (χ.trans Q) := by
              rw [Path.trans_range]
              exact Or.inr (Set.mem_range_self t)
            have hi := hrightsub ht
            rw [Path.trans_range] at hi
            rcases hi with ⟨u,hu⟩ | ⟨u,hu⟩
            · rw [← hu]
              exact hAavoid u
            · rw [← hu]
              exact hBavoid u
          have ha : f a ∉ M.cover.branch := by simpa only [P.source] using hPavoid 0
          have hb : f b ∉ M.cover.branch := by simpa only [χ.target] using hχavoid 1
          have hc : f c ∉ M.cover.branch := by simpa only [A.source] using hAavoid 0
          have hd : f d ∉ M.cover.branch := by simpa only [ξ.target] using hξavoid 1
          obtain ⟨Φ,hΦ,hΦmap⟩ := hPhi K f hf
          obtain ⟨PG,hPG⟩ := hLift K f a b ha hb P hPavoid
          obtain ⟨χG,hχG⟩ := hLift K f a b ha hb χ hχavoid
          obtain ⟨QG,hQG⟩ := hLift K f b a hb ha Q hQavoid
          obtain ⟨AG,hAG⟩ := hLift K f c d hc hd A hAavoid
          obtain ⟨ξG,hξG⟩ := hLift K f c d hc hd ξ hξavoid
          obtain ⟨BG,hBG⟩ := hLift K f d c hd hc B hBavoid
          let incl : C({z : K | f z ∉ M.cover.branch},K) := ⟨Subtype.val,continuous_subtype_val⟩
          have hPGmap : PG.map incl.continuous = P := by apply Path.ext; funext t; exact hPG t
          have hχGmap : χG.map incl.continuous = χ := by apply Path.ext; funext t; exact hχG t
          have hQGmap : QG.map incl.continuous = Q := by apply Path.ext; funext t; exact hQG t
          have hAGmap : AG.map incl.continuous = A := by apply Path.ext; funext t; exact hAG t
          have hξGmap : ξG.map incl.continuous = ξ := by apply Path.ext; funext t; exact hξG t
          have hBGmap : BG.map incl.continuous = B := by apply Path.ext; funext t; exact hBG t
          have hLoopProjection {u v : {z : K | f z ∉ M.cover.branch}}
              (L : Path u v) (R : Path v u) (t : Interval) :
              (((L.map Φ.continuous).trans (R.map Φ.continuous)) t).val =
              f (((L.map incl.continuous).trans (R.map incl.continuous)) t) := by
            rw [← Path.map_trans,← Path.map_trans]
            exact hΦmap ((L.trans R) t)
          let P' := PG.map Φ.continuous
          let χ' := χG.map Φ.continuous
          let Q' := QG.map Φ.continuous
          let A' := AG.map Φ.continuous
          let ξ' := ξG.map Φ.continuous
          let B' := BG.map Φ.continuous
          have hp0 (t : Interval) : ((P'.trans χ'.symm) t).val = f ((P.trans χ.symm) t) := by
            have h := hLoopProjection PG χG.symm t
            simpa only [← Path.map_symm,hPGmap,hχGmap] using h
          have hp1 (t : Interval) : ((A'.trans ξ'.symm) t).val = f ((A.trans ξ.symm) t) := by
            have h := hLoopProjection AG ξG.symm t
            simpa only [← Path.map_symm,hAGmap,hξGmap] using h
          have hp2 (t : Interval) : ((ξ'.trans B') t).val = f ((ξ.trans B) t) := by
            have h := hLoopProjection ξG BG t
            simpa only [hξGmap,hBGmap] using h
          have hpi (t : Interval) : ((A'.trans B') t).val = f ((A.trans B) t) := by
            have h := hLoopProjection AG BG t
            simpa only [hAGmap,hBGmap] using h
          have hpr (t : Interval) : ((χ'.trans Q') t).val = f ((χ.trans Q) t) := by
            have h := hLoopProjection χG QG t
            simpa only [hχGmap,hQGmap] using h
          have hpo (t : Interval) : ((P'.trans Q') t).val = f ((P.trans Q) t) := by
            have h := hLoopProjection PG QG t
            simpa only [hPGmap,hQGmap] using h
          have hcell0' : Set.range (fun t => ((P'.trans χ'.symm) t).val) = F 0 '' {z | ‖z.val‖ = 1} := by
            simpa only [hp0] using hcell0
          have hcell1' : Set.range (fun t => ((A'.trans ξ'.symm) t).val) = F 1 '' {z | ‖z.val‖ = 1} := by
            simpa only [hp1] using hcell1
          have hcell2' : Set.range (fun t => ((ξ'.trans B') t).val) = F 2 '' {z | ‖z.val‖ = 1} := by
            simpa only [hp2] using hcell2
          refine hThree _ _ _ _ P' χ' Q' A' ξ' B' F hF m hm honly hcell0' hcell1' hcell2' ?_ ?_ ?_ ?_ ?_ γ ?_
          · intro s t he
            rw [hp0,hp0] at he
            exact hcoll0 s t (hf.injective he)
          · intro s t he
            rw [hp1,hp1] at he
            exact hcoll1 s t (hf.injective he)
          · intro s t he
            rw [hp2,hp2] at he
            exact hcoll2 s t (hf.injective he)
          · intro s t he
            rw [hpi,hpi] at he
            exact hinnercoll s t (hf.injective he)
          · rintro y ⟨t,rfl⟩
            obtain ⟨u,hu⟩ := hrightsub (Set.mem_range_self t)
            refine ⟨u,?_⟩
            change ((A'.trans B') u).val = ((χ'.trans Q') t).val
            rw [hpi,hpr,hu]
          · intro t
            rw [hpo]
            exact hγπ t
    
      let R := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
      obtain ⟨f,lo,hi,F,m,hf,hboundary,hpositive,hshape,hF⟩ := hSource a
      obtain ⟨r,x,y,u,v,P,Q,χ,A,B,ξ,hl,h1,h2,hr,ho,hcl,hc1,hc2,hci,hco⟩ :=
        hTyped (-1) 1 (-1) 1 (by norm_num) (by norm_num) lo hi hshape
      have hImage {x y : R} (δ : Path x y) :
          Set.range (fun t => f (δ t)) = f '' {z : R | z.val ∈ Set.range (fun t => (δ t).val)} := by
        ext w
        constructor
        · rintro ⟨t,rfl⟩; exact ⟨δ t,⟨t,rfl⟩,rfl⟩
        · rintro ⟨z,⟨t,ht⟩,rfl⟩; exact ⟨t,congrArg f (Subtype.ext ht)⟩
      let β : C(Interval,S) := f.comp (P.trans Q).toContinuousMap
      have hends : β 0 = β 1 := by
        change f ((P.trans Q) 0) = f ((P.trans Q) 1)
        rw [Path.source,Path.target]
      have hcoll : ∀ s t, β s = β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
        intro s t he
        exact hco s t (hf.injective he)
      have hβrange : Set.range β = a.val.image := by
        change Set.range (fun t => f ((P.trans Q) t)) = _
        rw [hImage,ho]
        exact hboundary
      refine ⟨β,hends,hcoll,hβrange,?_⟩
      intro γ hγπ
      refine hRaw R f hf x y u v P χ Q A ξ B (F ∘ r)
        (fun i => (hF (r i)).1) (m ∘ r) (fun i => (hF (r i)).2.1)
        (fun i => (hF (r i)).2.2.1) ?_ ?_ ?_ hcl hc1 hc2 hci (le_of_eq hr) γ hγπ
      · rw [hImage,hl]; exact (hF (r 0)).2.2.2.symm
      · rw [hImage,h1]; exact (hF (r 1)).2.2.2.symm
      · rw [hImage,h2]; exact (hF (r 2)).2.2.2.symm
  
  have hCurve (a : Circle33 M) (β : C(Interval,S)) (_hends : β 0 = β 1)
      (hcoll : ∀ s t, β s = β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
      (hrange : Set.range β = a.val.image)
      (hswap : ∀ γ : C(Interval,E), (∀ t, M.cover.projection (γ t) = β t) →
        γ 1 = M.cover.deck (γ 0)) :
      ∃ c : Curve E, c.image = M.cover.projection ⁻¹' a.val.image := by
        as_aux_lemma =>
      have hSwap (a : Circle33 M) (β : C(Interval, S))
          (hβrange : Set.range β = a.val.image)
          (hβcoll : ∀ s t : Interval, β s = β t →
            s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
          (γ : C(Interval, E)) (hproj : ∀ t, M.cover.projection (γ t) = β t)
          (hswap : γ 1 = M.cover.deck (γ 0)) :
          ∃ c : Curve E, c.image = M.cover.projection ⁻¹' a.val.image := by
            as_aux_lemma =>
          letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
          let rev : Interval → Interval := fun t => ⟨1 - (t : ℝ), by
            constructor <;> linarith [t.property.1, t.property.2]⟩
          have hrevcont : Continuous rev :=
            (continuous_const.sub continuous_subtype_val).subtype_mk _
          have hrev0 : rev 0 = 1 := Subtype.ext (by norm_num [rev])
          have hrev1 : rev 1 = 0 := Subtype.ext (by norm_num [rev])
          have hrevinv (t : Interval) : rev (rev t) = t := Subtype.ext (by dsimp [rev]; ring)
          have hrevinj : Function.Injective rev := Function.LeftInverse.injective hrevinv
          have hfix (t : Interval) : M.cover.deck (γ t) ≠ γ t := by
            intro hf
            have hb := (M.cover.fixed_iff_branch (γ t)).mp hf
            rw [hproj t] at hb
            have ht : β t ∈ a.val.image := hβrange ▸ Set.mem_range_self t
            exact Set.disjoint_left.mp a.val.avoids_branch ht hb
          have hneq : γ 0 ≠ γ 1 := by
            intro he
            exact hfix 0 (hswap.symm.trans he.symm)
          have hγinj : Function.Injective γ := by
            intro s t hst
            have hb : β s = β t := by rw [← hproj s, ← hproj t, hst]
            rcases hβcoll s t hb with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact h
            · exact False.elim (hneq hst)
            · exact False.elim (hneq hst.symm)
          let g : C(Interval, E) := ⟨fun t => M.cover.deck (γ (rev t)),
            M.cover.deck.continuous.comp (γ.continuous.comp hrevcont)⟩
          have hginj : Function.Injective g := M.cover.deck.injective.comp (hγinj.comp hrevinj)
          have h0 : γ 0 = g 0 := by
            dsimp [g]
            rw [hrev0, hswap, M.cover.deck_involution]
          have h1 : γ 1 = g 1 := by
            dsimp [g]
            rw [hrev1]
            exact hswap
          have hinter : ∀ s t : Interval, γ s = g t →
              (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
            intro s t hst
            have hb : β s = β (rev t) := by
              rw [← hproj s, ← hproj (rev t)]
              rw [hst]
              exact M.cover.projection_deck _
            rcases hβcoll s (rev t) hb with h | ⟨hs, ht⟩ | ⟨hs, ht⟩
            · subst s
              exact False.elim (hfix (rev t) hst.symm)
            · left
              refine ⟨hs, ?_⟩
              have h := congrArg rev ht
              simpa only [hrevinv, hrev1] using h
            · right
              refine ⟨hs, ?_⟩
              have h := congrArg rev ht
              simpa only [hrevinv, hrev0] using h
          obtain ⟨c, hc⟩ := exists_curve_of_two_arcs γ g hγinj hginj h0 h1 hinter
          refine ⟨c, hc.trans ?_⟩
          have hgrange : Set.range g = M.cover.deck '' Set.range γ := by
            change Set.range (M.cover.deck ∘ γ ∘ rev) = _
            rw [← Function.comp_assoc, (Function.Involutive.surjective hrevinv).range_comp,
              Set.range_comp]
          rw [hgrange]
          ext x
          constructor
          · rintro (⟨t, rfl⟩ | ⟨y, ⟨t, rfl⟩, rfl⟩)
            · change M.cover.projection (γ t) ∈ a.val.image
              rw [hproj t]
              exact hβrange ▸ Set.mem_range_self t
            · change M.cover.projection (M.cover.deck (γ t)) ∈ a.val.image
              rw [M.cover.projection_deck, hproj t]
              exact hβrange ▸ Set.mem_range_self t
          · intro hx
            have hx' : M.cover.projection x ∈ Set.range β := hβrange.symm ▸ hx
            obtain ⟨t, ht⟩ := hx'
            have heq : M.cover.projection (γ t) = M.cover.projection x := (hproj t).trans ht
            rcases (M.cover.fiber_pair (γ t) x).mp heq with h | h
            · exact Or.inl ⟨t, h.symm⟩
            · exact Or.inr ⟨γ t, ⟨t, rfl⟩, h.symm⟩
    
      let : ContractibleSpace Interval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
      let : LocallyPathConnectedSpace Interval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
      have havoid (t) : β t ∉ M.cover.branch := by
        have ht : β t ∈ a.val.image := by rw [← hrange]; exact Set.mem_range_self t
        exact Set.disjoint_left.mp a.val.avoids_branch ht
      obtain ⟨x,hx⟩ := M.cover.projection_surjective (β 0)
      obtain ⟨γ,hγ,_⟩ := M.cover.unbranched_cover.existsUnique_continuousMap_lifts β hx havoid
      have hγπ (t) : M.cover.projection (γ t) = β t := congrFun hγ.2 t
      exact hSwap a β hrange hcoll γ hγπ (hswap γ hγπ)
  
  obtain ⟨β,hends,hcoll,hrange,hswap⟩ := hOdd M a
  obtain ⟨c,hc⟩ := hCurve a β hends hcoll hrange hswap
  exact ⟨⟨c,circle33_preimage_essential M a c hc⟩,hc⟩
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.circle33_preimage_essential_curve
