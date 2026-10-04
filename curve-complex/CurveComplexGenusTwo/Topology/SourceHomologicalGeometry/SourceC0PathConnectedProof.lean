import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceClosedSurfaceThetaRetentionCanonicalProof
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceClosedSurfaceBranchPushOffCanonicalProof
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.ActualUnorientedOutsideBands
import CurveComplexGenusTwo.Topology.Orientation.SurfaceTopHomologyDetection
import CurveComplexGenusTwo.Topology.Orientation.SurfaceLocalization
import Mathlib.Topology.Connected.Clopen
import CurveComplexGenusTwo.CWHurewicz.PairNaturality
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import CurveComplexGenusTwo.Topology.PositionExtension.TwistedBandReflection
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.Basic
import CurveComplexGenusTwo.Topology.Orientation.BandSignScaffold
import CurveComplexGenusTwo.Foundations.EdgeReplacementStatements
import CurveComplexGenusTwo.Topology.EdgePathZeroDetour
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.KernelEndpoints
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.ActualMinimumPositionCanonical
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualNonseparatingFinitePaths
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.ActualBandBase
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.ActualBandBoundary

import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceHomologicalThetaRetentionCanonicalProof
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceAmbientIsotopyFundamentalNonzero
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceFundamentalNonzeroEssential
import CurveComplexGenusTwo.Topology.SourceCycleActual.SourceEssentialCurveComplete
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.Basic
import CurveComplexGenusTwo.Foundations.EdgeHomotopy
import CurveComplexGenusTwo.Foundations.RealizationCW

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex
open CategoryTheory CategoryTheory.Limits Set
open CurveComplexGenusTwo.CWHurewicz
open CurveComplex.GenusOrientationCandidate
set_option backward.isDefEq.respectTransparency false

-- Original exact target: actual vertex connectivity assembled; independent finite-loop surgery remains open.
theorem source_c0_pathConnected_allGenus
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) :
    PathConnectedSpace (curveComplexRealization S 0) := by
  classical
  -- The genus context genuinely gives nonzero first integral homology.
  have hH1 : ∃ z : integralHomology S 1, z ≠ 0 := by
    obtain ⟨e⟩ := hS.2.2.2
    let u : Fin (2 * g) → ℤ := fun _ => 1
    refine ⟨e.inv u, ?_⟩
    intro hz
    have hu : u = 0 := by
      calc
        u = e.hom (e.inv u) := (e.toLinearEquiv.apply_symm_apply u).symm
        _ = 0 := by rw [hz, map_zero]
    have hi := congrFun hu (⟨0, by omega⟩ : Fin (2 * g))
    norm_num [u] at hi
  -- Missing source step: turn genus homology into an actual embedded essential circle.
  have hvertex : Nonempty (Vertex S) := by
    obtain ⟨c, hc⟩ := source_essential_curve_exists S g hg hS
    exact ⟨Quotient.mk _ ⟨c, hc⟩⟩
  let : ClosedSurface S := Classical.choice hS.2.1
  have hUnsigned : ∀ {a b : Curve S} (D : OneCrossingBandBase a b),
      Nonempty (UnorientedOutsideBands D) := by
    intro a b D
    exact CurveComplex.exists_actual_unoriented_outside_bands D
  have hUntwisted : ∀ {a b : Curve S} (D : OneCrossingBandBase a b)
      (B : UnorientedOutsideBands D), B.firstFlip = false ∧ B.secondFlip = false := by
    intro a b D B
    classical
    let : ClosedSurface S := Classical.choice hS.2.1
    have obstruction (x : S) (f : C(S,S))
        (hf : ∀ y ∈ ({x}ᶜ : Set S), f y ∈ ({x}ᶜ : Set S))
        (h : ContinuousMap.Homotopic f (ContinuousMap.id S)) :
        pairRelativeHomologyMap ({x}ᶜ : Set S) ({x}ᶜ : Set S) f hf 2 ≠
          -(𝟙 (relativeHomology S ({x}ᶜ : Set S) 2)) := by
      let : ClosedSurface S := Classical.choice hS.2.1
      have injective (S : Type) [TopologicalSpace S]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S] (x : S) :
          Function.Injective (homologyToRelative S ({x}ᶜ : Set S) 2) := by
        have hz (z : H S 2) (hx : homologyToRelative S ({x}ᶜ : Set S) 2 z = 0) : z = 0 := by
          have hc : IsClopen {y : S | homologyToRelative S ({y}ᶜ : Set S) 2 z = 0} :=
            ⟨surface_localization_zero_locus_closed S 2 z,
              homology_localization_zero_locus_open S 2 z⟩
          have he := hc.eq_univ ⟨x, hx⟩
          apply surface_top_homology_detection S z
          intro y
          have hy : y ∈ {y : S | homologyToRelative S ({y}ᶜ : Set S) 2 z = 0} := by
            rw [he]; trivial
          exact hy
        intro a b hab
        have hh : homologyToRelative S ({x}ᶜ : Set S) 2 (a-b) = 0 := by
          rw [map_sub, hab, sub_self]
        exact sub_eq_zero.mp (hz (a-b) hh)
      have fixed
          {S : Type} [TopologicalSpace S] (x : S) (f : C(S, S))
          (hf : ∀ y ∈ ({x}ᶜ : Set S), f y ∈ ({x}ᶜ : Set S))
          (h : ContinuousMap.Homotopic f (ContinuousMap.id S)) :
          homologyToRelative S ({x}ᶜ : Set S) 2 ≫ pairRelativeHomologyMap ({x}ᶜ : Set S) ({x}ᶜ : Set S) f hf 2 =
            homologyToRelative S ({x}ᶜ : Set S) 2 := by
        have hn := pairRelativeHomologyMap_commutes
          ({x}ᶜ : Set S) ({x}ᶜ : Set S) f hf 2
        have hh : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) =
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
            (ModuleCat.of ℤ ℤ)).map (𝟙 (TopCat.of S))) :=
          TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
            h.some (ModuleCat.of ℤ ℤ) 2
        have hid : HomologicalComplex.homologyMap
            (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) 2 =
            𝟙 (integralHomology S 2) := by
          change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) = _
          rw [hh]
          exact CategoryTheory.Functor.map_id _ _
        rw [hid] at hn
        change homologyToRelative S ({x}ᶜ : Set S) 2 ≫ pairRelativeHomologyMap ({x}ᶜ : Set S) ({x}ᶜ : Set S) f hf 2 =
          𝟙 (integralHomology S 2) ≫ homologyToRelative S ({x}ᶜ : Set S) 2 at hn
        simpa only [Category.id_comp] using hn
      intro hnegative
      let : Mono (homologyToRelative S ({x}ᶜ : Set S) 2) :=
        (ModuleCat.mono_iff_injective _).mpr (injective S x)
      obtain ⟨e⟩ := hS.2.2.1
      have he := fixed x f hf h
      rw [hnegative, Preadditive.comp_neg, Category.comp_id] at he
      have hidentity : -(𝟙 (integralHomology S 2)) = 𝟙 (integralHomology S 2) := by
        apply (cancel_mono (homologyToRelative S ({x}ᶜ : Set S) 2)).1
        simpa only [Preadditive.neg_comp, Category.id_comp] using he
      have hinteger : -(𝟙 (ModuleCat.of ℤ ℤ)) = 𝟙 (ModuleCat.of ℤ ℤ) := by
        have hh := congrArg
          (fun q : integralHomology S 2 ⟶ integralHomology S 2 => e.inv ≫ q ≫ e.hom) hidentity
        simpa only [Preadditive.comp_neg, Preadditive.neg_comp, Category.comp_id, Category.id_comp,
          e.inv_hom_id] using hh
      have hone := congrArg
        (fun q : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => q.hom (1 : ℤ)) hinteger
      norm_num at hone
    constructor
    · cases hf : B.firstFlip
      · rfl
      · obtain ⟨x, ⟨W⟩⟩ := first_twisted_band_local_reflection D B hf
        exact False.elim (obstruction x W.map W.preserves W.isotopy W.acts_neg)
    · cases hs : B.secondFlip
      · rfl
      · obtain ⟨x, ⟨W⟩⟩ := second_twisted_band_local_reflection D B hs
        exact False.elim (obstruction x W.map W.preserves W.isotopy W.acts_neg)
  have hbands : ∀ {a b : Curve S} (D : OneCrossingBandBase a b),
      Nonempty (CompatibleOutsideBands D) := by
    intro a b D
    obtain ⟨B⟩ := hUnsigned D
    obtain ⟨hf, hs⟩ := hUntwisted D B
    refine ⟨{
      first := B.first
      second := B.second
      first_embedded := B.first_embedded
      second_embedded := B.second_embedded
      first_center := B.first_center
      second_center := B.second_center
      first_bottom := B.first_bottom
      first_top := ?_
      second_left := B.second_left
      second_right := ?_
      bands_disjoint := B.bands_disjoint
      first_square := B.first_square
      second_square := B.second_square }⟩
    · intro w
      simpa only [hf, flipBandWidth, Bool.false_eq_true, ↓reduceIte] using B.first_top w
    · intro w
      simpa only [hs, flipBandWidth, Bool.false_eq_true, ↓reduceIte] using B.second_right w
  have hzeroDetour (α β : Vertex S)
      (hone : geometricIntersection α β = 1) :
      ∃ γ : Vertex S, geometricIntersection α γ = 0 ∧ geometricIntersection γ β = 0 := by
    obtain ⟨a,b,ha,hb,ht,hcount,_⟩ :=
      one_crossing_representatives_of_isGenus S g hS α β hone
    obtain ⟨D⟩ := exists_oneCrossingBandBase a.val b.val ht hcount
    obtain ⟨B⟩ := hbands D
    obtain ⟨c,_,hac,hbc,_,_⟩ :=
      intersection_one_detour_of_actual_compatible_bands hg hS a b
        (by simpa only [ha,hb] using hone) D B
    refine ⟨Quotient.mk (essentialCurveSetoid S) c, ?_, ?_⟩
    · simpa only [ha] using hac
    · rw [geometricIntersection_symm_of_chart]
      simpa only [hb] using hbc
  let vertexPoint (v : Vertex S) := realizationVertex (curveComplex S 0) v
    ((curveComplex S 0).singleton_mem v)
  have hzeroEdge (a b : Vertex S) (hab : geometricIntersection a b = 0) :
      Joined (vertexPoint a) (vertexPoint b) := by
    let K := curveComplex S 0
    have hface : ({a,b} : Finset (Vertex S)) ∈ K.faces := by
      refine ⟨by simp, ?_⟩
      intro x hx y hy hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hne rfl).elim
      · simp [hab]
      · rw [geometricIntersection_symm_of_chart]; simp [hab]
      · exact (hne rfl).elim
    let p := (finiteSegmentPath {a,b}
      (finiteSimplexVertex {a,b} a (by simp))
      (finiteSimplexVertex {a,b} b (by simp))).map
      (continuous_faceInclusion_local K {a,b} hface)
    have ha : vertexPoint a =
        faceInclusion K {a,b} hface (finiteSimplexVertex {a,b} a (by simp)) := by
      apply RealizationPoint.ext
      funext w
      simp [vertexPoint, realizationVertex, finiteSimplexVertex_faceInclusion_weight]
    have hb : vertexPoint b =
        faceInclusion K {a,b} hface (finiteSimplexVertex {a,b} b (by simp)) := by
      apply RealizationPoint.ext
      funext w
      simp [vertexPoint, realizationVertex, finiteSimplexVertex_faceInclusion_weight]
    exact ⟨p.cast ha hb⟩
  have honeEdge (a b : Vertex S) (hab : geometricIntersection a b ≤ 1) :
      Joined (vertexPoint a) (vertexPoint b) := by
    by_cases hz : geometricIntersection a b = 0
    · exact hzeroEdge a b hz
    obtain ⟨c,hac,hcb⟩ := hzeroDetour a b (by omega)
    exact (hzeroEdge a c hac).trans (hzeroEdge c b hcb)
  have hreturn (α β : Vertex S) (hlarge : 1 < geometricIntersection α β) :
      ∃ a b : EssentialCurve S,
        Quotient.mk (essentialCurveSetoid S) a = α ∧
        Quotient.mk (essentialCurveSetoid S) b = β ∧
        ∃ ht : Transverse a.val b.val,
          ht.1.toFinset.card = geometricIntersection α β ∧
          Nonempty (SourceFirstReturnBoundary b.val a.val) := by
    obtain ⟨a,b,ha,hb,ht,hmin⟩ := source_geometric_intersection_attained S α β
    have hcard : 1 < ht.1.toFinset.card := by rw [hmin]; exact hlarge
    obtain ⟨u,v,hu,hv,huv⟩ := Finset.one_lt_card_iff.mp hcard
    have hu' : u ∈ a.val.image ∩ b.val.image := by simpa using hu
    have hv' : v ∈ a.val.image ∩ b.val.image := by simpa using hv
    obtain ⟨w,huw,hw,f,g,hf,hg,hf0,hg0,hf1,hg1,hfb,hga,havoid,hmeet,c,hc,hcompact⟩ :=
      LocalSurgery.source_two_curve_first_return_boundary b.val a.val
        (transverse_symm_of_chart ht) u v ⟨hu'.2,hu'.1⟩ ⟨hv'.2,hv'.1⟩ huv
    refine ⟨a,b,ha,hb,ht,hmin,?_⟩
    exact ⟨{
      start := u, finish := w, distinct := huw,
      start_mem := ⟨hu'.2,hu'.1⟩, finish_mem := hw,
      first := f, second := g, first_embedded := hf, second_embedded := hg,
      first_zero := hf0, second_zero := hg0, first_one := hf1, second_one := hg1,
      first_subset := hfb, second_subset := hga, first_interior_avoids := havoid,
      intersection := hmeet, boundary := c, boundary_image := hc,
      boundary_compact := hcompact }⟩
  let P (v : Vertex S) : Prop := ∃ c : EssentialCurve S,
    Quotient.mk (essentialCurveSetoid S) c = v ∧
    HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨c.val.map,c.val.embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass ≠ 0
  have hreduce (α : {v : Vertex S // P v}) (β : Vertex S)
      (hlarge : 1 < geometricIntersection α.val β) :
      ∃ γ : {v : Vertex S // P v},
        geometricIntersection α.val γ.val ≤ 1 ∧
        geometricIntersection γ.val β < geometricIntersection α.val β := by
    obtain ⟨a,b,ha,hb,ht,hmin,⟨D⟩⟩ := hreturn α.val β hlarge
    obtain ⟨c,hc,hcNonzero⟩ := α.property
    have hrelCa : AmbientIsotopy.Rel c.val.image a.val.image :=
      Quotient.eq.mp (hc.trans ha.symm)
    have hna := curve_fundamental_nonzero_of_ambient_isotopy c.val a.val hrelCa hcNonzero
    obtain ⟨B⟩ := source_first_return_two_surgery_branches D
    obtain ⟨i,hraw⟩ := source_first_return_homologically_nonzero_branch S D B hna
    obtain ⟨d,hrel,hbd,had,hcount,hret⟩ :=
      source_closed_surface_first_return_branch_push_off S D B
        (transverse_symm_of_chart ht) i
    have hrawEssential := essential_of_curve_fundamental_nonzero (B.boundary i) hraw
    have hdEssential : Essential d := (essential_isotopy_invariant hrel).mp hrawEssential
    let raw : EssentialCurve S := ⟨B.boundary i,hrawEssential⟩
    let dc : EssentialCurve S := ⟨d,hdEssential⟩
    have hdNonzero := curve_fundamental_nonzero_of_ambient_isotopy
      (B.boundary i) d hrel hraw
    let γ : {v : Vertex S // P v} :=
      ⟨Quotient.mk (essentialCurveSetoid S) dc,⟨dc,rfl,hdNonzero⟩⟩
    have hcurrent : geometricIntersection α.val γ.val ≤ hbd.1.toFinset.card := by
      apply Nat.sInf_le
      exact ⟨a,dc,ha,rfl,hbd,rfl⟩
    have htarget : geometricIntersection β γ.val ≤ had.1.toFinset.card := by
      apply Nat.sInf_le
      exact ⟨b,dc,hb,rfl,had,rfl⟩
    have hbudget := (source_surgery_closing_crossings_budget D B
      (transverse_symm_of_chart ht) i).2
    have htotal : (b.val.image ∩ a.val.image).ncard = geometricIntersection α.val β := by
      rw [Set.inter_comm,Set.ncard_eq_toFinset_card _ ht.1]
      exact hmin
    change (source_surgery_retained_crossings B i).ncard+2≤
      (b.val.image ∩ a.val.image).ncard at hbudget
    rw [htotal] at hbudget
    refine ⟨γ,hcurrent.trans hcount,?_⟩
    rw [geometricIntersection_symm_of_chart γ.val β]
    exact htarget.trans_lt (by omega)
  have hnonzeroTarget (α : {v : Vertex S // P v}) (β : Vertex S) :
      Joined (vertexPoint α.val) (vertexPoint β) := by
    generalize hn : geometricIntersection α.val β = n
    induction n using Nat.strong_induction_on generalizing α with
    | h n ih =>
      by_cases hsmall : geometricIntersection α.val β ≤ 1
      · exact honeEdge α.val β hsmall
      · obtain ⟨γ,hαγ,hdecrease⟩ := hreduce α β (Nat.lt_of_not_ge hsmall)
        exact (honeEdge α.val γ.val hαγ).trans
          (ih (geometricIntersection γ.val β) (by omega) γ rfl)
  have hvertices : ∀ a b : Vertex S, Joined (vertexPoint a) (vertexPoint b) := by
    obtain ⟨c,hc⟩ := source_homologically_nonzero_curve_exists S g hg hS
    let ec : EssentialCurve S := ⟨c,essential_of_curve_fundamental_nonzero c hc⟩
    let seed : {v : Vertex S // P v} :=
      ⟨Quotient.mk (essentialCurveSetoid S) ec,⟨ec,rfl,hc⟩⟩
    intro a b
    exact (hnonzeroTarget seed a).symm.trans (hnonzeroTarget seed b)
  have hradius (x : curveComplexRealization S 0) (v : Vertex S)
      (hx : 0 < x.weight v) : Joined x (vertexPoint v) := by
    have he : vertexPoint v = starVertexPoint (curveComplex S 0) v x hx := by
      apply RealizationPoint.ext
      funext w
      simp [vertexPoint, realizationVertex, finiteSimplexVertex_faceInclusion_weight,
        starVertexPoint, starCone]
    exact ⟨(radialPath (curveComplex S 0) v x hx).cast rfl he⟩
  have hconnected : PathConnectedSpace (curveComplexRealization S 0) := by
    refine ⟨hvertex.map vertexPoint, ?_⟩
    intro x y
    obtain ⟨a, ha⟩ := supportFinset_nonempty (curveComplex S 0) x
    obtain ⟨b, hb⟩ := supportFinset_nonempty (curveComplex S 0) y
    have hxa := (mem_supportFinset_iff_pos (curveComplex S 0) x a).mp ha
    have hyb := (mem_supportFinset_iff_pos (curveComplex S 0) y b).mp hb
    exact (hradius x a hxa).trans ((hvertices a b).trans (hradius y b hyb).symm)
  exact hconnected

end CurveComplexGenusTwo.SourceTopology
