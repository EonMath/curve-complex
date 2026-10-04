import HarerC0ConsumerBinding
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

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex
open CategoryTheory CategoryTheory.Limits Set
open CurveComplexGenusTwo.CWHurewicz
open CurveComplex.GenusOrientationCandidate
set_option backward.isDefEq.respectTransparency false

theorem c1_simplyConnected_allGenus
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) :
    SimplyConnectedSpace (curveComplexRealization S 1) := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  -- Genuine source obligation: Harer's theorem for the actual all-curve C₀.
  have hHarer : SimplyConnectedSpace (curveComplexRealization S 0) := by
    exact source_c0_simplyConnected_allGenus S g hg hS
  let : SimplyConnectedSpace (curveComplexRealization S 0) := hHarer
  -- Genuine geometric obligation: actual outside bands, with untwisted signs.
  -- The D-only unsigned producer and orientation/sign producer are separate owners.
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
  let K := CurveComplex.curveComplex S 0
  let L := CurveComplex.curveComplex S 1
  have hKL : ∀ σ, σ ∈ K.faces → σ ∈ L.faces := curveComplex_mono S (by omega)
  have hvertices : ∀ v : Vertex S, ({v} : Finset (Vertex S)) ∈ L.faces →
      ({v} : Finset (Vertex S)) ∈ K.faces := by
    intro v _
    exact K.singleton_mem v
  have hfill : ∀ α β : Vertex S, ({α, β} : Finset (Vertex S)) ∈ L.faces →
      ({α, β} : Finset (Vertex S)) ∈ K.faces ∨
      ∃ γ : Vertex S, ({α, β, γ} : Finset (Vertex S)) ∈ L.faces ∧
        ({α, γ} : Finset (Vertex S)) ∈ K.faces ∧
        ({γ, β} : Finset (Vertex S)) ∈ K.faces := by
    intro α β hedge
    by_cases heq : α = β
    · left
      subst β
      simpa using K.singleton_mem α
    have hle : geometricIntersection α β ≤ 1 :=
      hedge.2 α (by simp) β (by simp) heq
    by_cases hz : geometricIntersection α β = 0
    · left
      refine ⟨hedge.1, ?_⟩
      intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · simp [hz]
      · rw [geometricIntersection_symm_of_chart]; simp [hz]
      · exact (hxy rfl).elim
    have hone : geometricIntersection α β = 1 := by omega
    obtain ⟨a, b, ha, hb, ht, hcount, _⟩ :=
      one_crossing_representatives_of_isGenus S g hS α β hone
    obtain ⟨D⟩ := exists_oneCrossingBandBase a.val b.val ht hcount
    obtain ⟨B⟩ := hbands D
    obtain ⟨c, _, hac, hbc, hneac, hnebc⟩ :=
      intersection_one_detour_of_actual_compatible_bands hg hS a b
        (by simpa only [ha, hb] using hone) D B
    rw [ha] at hac hneac
    rw [hb] at hbc hnebc
    have hf := Topology.fillsIntersectionOneEdge_of_geometric_data
      geometricIntersection (fun x y => geometricIntersection_symm_of_chart x y)
      heq hnebc hneac hone hac hbc
    refine Or.inr ⟨Quotient.mk (essentialCurveSetoid S) c,
      ⟨by simp, hf.2.2.2.2.2.2.1⟩,
      ⟨by simp, hf.2.2.2.2.2.2.2.1⟩, ?_⟩
    have hh := hf.2.2.2.2.2.2.2.2
    simpa only [Finset.pair_comm] using
      (show ({β, Quotient.mk (essentialCurveSetoid S) c} : Finset (Vertex S)) ∈
        K.faces from ⟨by simp, hh⟩)
  let f : C(RealizationPoint K, RealizationPoint L) :=
    ⟨realizationMap K L hKL, realizationMap_continuous K L hKL⟩
  have hvertexmap (v : Vertex S) :
      f (realizationVertex K v (K.singleton_mem v)) =
        realizationVertex L v (L.singleton_mem v) := by
    apply RealizationPoint.ext
    funext w
    simp [f, realizationMap_weight, realizationVertex_weight]
  have hradial (x : RealizationPoint L) : ∃ v : Vertex S,
      Nonempty (Path x (f (realizationVertex K v (K.singleton_mem v)))) := by
    obtain ⟨v, hv⟩ := exists_mem_openVertexStar L x
    have hs : realizationVertex L v (L.singleton_mem v) ∈ openVertexStar L v := by
      change 0 < (realizationVertex L v (L.singleton_mem v)).weight v
      simp [realizationVertex_weight]
    have hend : starVertexPoint L v x hv =
        realizationVertex L v (L.singleton_mem v) := by
      rw [starVertexPoint_eq L v x (realizationVertex L v (L.singleton_mem v)) hv hs]
      exact starCone_vertex_self L v (L.singleton_mem v) hs 1
    refine ⟨v, ⟨(radialPath L v x hv).cast rfl ?_⟩⟩
    exact (hend.trans (hvertexmap v).symm).symm
  have hPC : PathConnectedSpace (RealizationPoint L) := by
    refine ⟨?_, ?_⟩
    · exact ⟨f (Classical.choice (inferInstance : Nonempty (RealizationPoint K)))⟩
    · intro x y
      obtain ⟨v, ⟨p⟩⟩ := hradial x
      obtain ⟨w, ⟨q⟩⟩ := hradial y
      exact ⟨(p.trans ((PathConnectedSpace.somePath
        (realizationVertex K v (K.singleton_mem v))
        (realizationVertex K w (K.singleton_mem w))).map f.continuous)).trans q.symm⟩
  let : PathConnectedSpace (RealizationPoint L) := hPC
  let x : RealizationPoint K := Classical.choice (inferInstance : Nonempty (RealizationPoint K))
  obtain ⟨v, hv⟩ := exists_mem_openVertexStar K x
  let z := realizationVertex K v (K.singleton_mem v)
  have hsurj := fundamentalGroupMap_surjective_of_triangle_fillers
    K L hKL hvertices hfill v (K.singleton_mem v)
  have hbase : ∀ a b : FundamentalGroup (RealizationPoint L) (f z), a = b := by
    intro a b
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    exact congrArg (FundamentalGroup.map f z) (Subsingleton.elim a' b')
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨hPC, ?_⟩
  intro y γ
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath
    (PathConnectedSpace.somePath (f z) y)
  have hall (a b : FundamentalGroup (RealizationPoint L) y) : a = b := by
    calc
      a = e (e.symm a) := (e.apply_symm_apply a).symm
      _ = e (e.symm b) := congrArg e (hbase (e.symm a) (e.symm b))
      _ = b := e.apply_symm_apply b
  exact Quotient.eq.mp (hall (⟦γ⟧ : FundamentalGroup (RealizationPoint L) y) 1)

end CurveComplexGenusTwo.SourceTopology
