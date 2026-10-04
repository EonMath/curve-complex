import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceHomologicallyNonzeroCurveCanonicalProof

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CurveComplexGenusTwo.CWHurewicz
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

-- Ephemeral local producer, derived directly from the completed finite-cycle
-- straightening theorem. This is a nonbounding embedded circle cycle, without
-- identifying nonbounding homology with connected complement.
theorem source_positive_genus_nonbounding_embedded_circle_cycle
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) :
    ∃ (c : Curve S)
      (z : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ →₀ ℤ),
      z ∈ absoluteSingularCycles (TopCat.of Circle) 1 ∧
      ¬ ∃ b : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of S) 1 b =
          singularFinsuppPush (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩) 1 z := by
  classical
  obtain ⟨c,hc⟩ := source_homologically_nonzero_curve_exists S g hg hS
  let z := CircleFundamentalCycle.circleBoundaryChain
  have hz : z ∈ absoluteSingularCycles (TopCat.of Circle) 1 := by
    exact LinearMap.mem_ker.mpr CircleFundamentalCycle.circle_boundary_is_cycle
  refine ⟨c,z,hz,?_⟩
  rintro ⟨b,hb⟩
  let f := singularFinsuppMap (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)
  let K := mvAmbientComplex (TopCat.of S)
  have hfz : f.f 1 z = singularFinsuppPush (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩) 1 z := by
    simp only [f,singularFinsuppMap_f]
    rfl
  have hw : K.d 1 (1-1) (f.f 1 z) = 0 := by
    rw [hfz]
    simp only [K,mvAmbientComplex]
    change singularBoundaryFinsupp (TopCat.of S) 0
      (singularFinsuppPush (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩) 1 z) = 0
    rw [singularFinsuppPush_boundary, CircleFundamentalCycle.circle_boundary_is_cycle, map_zero]
  have hclass : CircleFundamentalCycle.cycleClass K 1 (f.f 1 z) hw = 0 := by
    apply (ModuleCat.mono_iff_injective (K.homologyι 1)).mp inferInstance
    rw [map_zero]
    have hi : K.homologyι 1
        (CircleFundamentalCycle.cycleClass K 1 (f.f 1 z) hw) =
        K.pOpcycles 1 (f.f 1 z) := by
      unfold CircleFundamentalCycle.cycleClass
      rw [← ModuleCat.comp_apply, Category.assoc, K.homology_π_ι, ← Category.assoc]
      simp
    rw [hi]
    rw [hfz, ← hb]
    exact congrArg (fun m => m b) (K.d_pOpcycles 2 1)
  apply hc
  have hn := congrArg (fun m => m
      (CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1 z
        CircleFundamentalCycle.circle_boundary_is_cycle))
    (singularHomologyRepresentation_naturality
      (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩) 1)
  change (singularHomologyRepresentation (TopCat.of S) 1).hom
      (HomologicalComplex.homologyMap f 1
        (CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1 z
          CircleFundamentalCycle.circle_boundary_is_cycle)) =
      HomologicalComplex.homologyMap
        (actualSingularFunctor.map (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1
        CircleFundamentalCycle.fundamentalClass at hn
  rw [CircleFundamentalCycle.cycleClass_map f 1 z
    CircleFundamentalCycle.circle_boundary_is_cycle hw, hclass, map_zero] at hn
  exact hn.symm

end CurveComplexGenusTwo.SourceTopology
