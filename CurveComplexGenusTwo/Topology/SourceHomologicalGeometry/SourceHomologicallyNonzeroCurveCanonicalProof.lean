import CurveComplexGenusTwo.Topology.SourceCycleActual.SourceEssentialCurveComplete
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseCircleFundamentalCycle
import CurveComplexGenusTwo.CWHurewicz.SingularNullhomotopyHeaders
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.Basic


namespace CurveComplexGenusTwo.SourceTopology
open CategoryTheory CategoryTheory.Limits CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem circle_chainMap_zero_of_fundamental_zero
    {S : Type} [TopologicalSpace S] (f : C(Circle,S))
    (hf : HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom f)) 1
      CircleFundamentalCycle.fundamentalClass = 0) :
    HomologicalComplex.homologyMap (singularFinsuppMap (TopCat.ofHom f)) 1 = 0 := by
  have hzero : HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom f)) 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨n,hn⟩ := CircleFundamentalCycle.fundamentalClass_generates x
    rw [←hn,map_zsmul,hf]
    change n • (0 : H S 1) = 0
    exact zsmul_zero n
  apply (cancel_mono (singularHomologyRepresentation (TopCat.of S) 1).hom).mp
  rw [singularHomologyRepresentation_naturality]
  change (singularHomologyRepresentation (TopCat.of Circle) 1).hom ≫
    HomologicalComplex.homologyMap (actualSingularFunctor.map (TopCat.ofHom f)) 1 = _
  rw [hzero]
  simp

end CurveComplexGenusTwo.SourceTopology


namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CurveComplexGenusTwo.CWHurewicz
open scoped Simplicial

-- Embedded source curve with genuinely nonzero pushed fundamental H1 class.
-- This is a source output, not a certificate premise on the Harer endpoint.
theorem source_homologically_nonzero_curve_exists
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) :
    ∃ c : Curve S,
      HomologicalComplex.homologyMap
        (actualSingularFunctor.map (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1
        CircleFundamentalCycle.fundamentalClass ≠ 0 := by
  classical
  obtain ⟨hsurface⟩ := hS.2.1
  letI : ClosedSurface S := hsurface
  obtain ⟨e⟩ := hS.2.2.2
  let u : Fin (2 * g) → ℤ := fun _ => 1
  have hnonzero : e.inv u ≠ 0 := by
    intro hz
    have hu : u = 0 := by
      calc
        u = e.hom (e.inv u) := (e.toLinearEquiv.apply_symm_apply u).symm
        _ = 0 := by rw [hz, map_zero]
    have hi := congrFun hu (⟨0, by omega⟩ : Fin (2 * g))
    norm_num [u] at hi
  by_contra hzero
  have hfund (c : Curve S) : HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass = 0 := by
    by_contra hn
    exact hzero ⟨c,hn⟩
  let r := singularHomologyRepresentation (TopCat.of S) 1
  have hnonzeroF : r.inv (e.inv u) ≠ 0 := by
    intro hz
    apply hnonzero
    have hi : r.hom (r.inv (e.inv u)) = e.inv u :=
      r.toLinearEquiv.apply_symm_apply (e.inv u)
    rw [hz] at hi
    change r.hom.hom 0 = e.inv u at hi
    rw [map_zero] at hi
    exact hi.symm
  let C := mvAmbientComplex (TopCat.of S)
  have hπ : Function.Surjective (C.homologyπ 1) :=
    (ModuleCat.epi_iff_surjective (C.homologyπ 1)).mp inferInstance
  obtain ⟨z, hz⟩ := hπ (r.inv (e.inv u))
  let chain : (TopCat.toSSet.obj (TopCat.of S)) _⦋1⦌ →₀ ℤ := C.iCycles 1 z
  have hchainCycle : singularBoundaryFinsupp (TopCat.of S) 0 chain = 0 := by
    have hi := congrArg (fun f => f z) (C.iCycles_d 1 0)
    change singularBoundaryFinsupp (TopCat.of S) 0 chain = 0 at hi
    exact hi
  have hfill : ∃ b : C.X 2, C.d 2 1 b = C.iCycles 1 z := by
    -- Exact outstanding surface geometry: straighten the finite cycle into a
    -- finite sum of embedded circle cycles, with an actual singular homotopy chain.
    have hstraight : ∃ (n : ℕ) (curves : Fin n → Curve S)
        (cycles : Fin n → ((TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ →₀ ℤ)),
        (∀ i, cycles i ∈ absoluteSingularCycles (TopCat.of Circle) 1) ∧
        ∃ b₀ : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
          singularBoundaryFinsupp (TopCat.of S) 1 b₀ = chain -
            ∑ i, singularFinsuppPush
              (TopCat.ofHom ⟨(curves i).map, (curves i).embedded.continuous⟩) 1 (cycles i) := by
      exact source_singular_one_cycle_straightening S g hg hS chain hchainCycle
    obtain ⟨n, curves, cycles, hcycles, b₀, hb₀⟩ := hstraight
    have hcircles (i : Fin n) :
        ∃ b : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
          singularBoundaryFinsupp (TopCat.of S) 1 b =
            singularFinsuppPush (TopCat.ofHom
              ⟨(curves i).map,(curves i).embedded.continuous⟩) 1 (cycles i) := by
      have hcycle : ((mvAmbientComplex (TopCat.of Circle)).sc 1).g (cycles i) = 0 := by
        change (mvAmbientComplex (TopCat.of Circle)).d 1
          ((ComplexShape.down ℕ).next 1) (cycles i) = 0
        rw [ChainComplex.next_nat_succ]
        exact LinearMap.mem_ker.mp (hcycles i)
      obtain ⟨b,hb⟩ := CurveComplex.WeightedFlowScratch.chainMap_cycle_fills_of_homologyMap_zero
        (singularFinsuppMap (TopCat.ofHom
          ⟨(curves i).map,(curves i).embedded.continuous⟩)) 1 (cycles i) hcycle
        (circle_chainMap_zero_of_fundamental_zero
          ⟨(curves i).map,(curves i).embedded.continuous⟩ (hfund (curves i)))
      refine ⟨b,?_⟩
      simp only [mvAmbientComplex,ChainComplex.of_d,singularFinsuppMap_f] at hb
      change singularBoundaryFinsupp (TopCat.of S) 1 b =
        singularFinsuppPush (TopCat.ofHom
          ⟨(curves i).map,(curves i).embedded.continuous⟩) 1 (cycles i) at hb
      exact hb
    choose fillings hfillings using hcircles
    refine ⟨b₀ + ∑ i, fillings i, ?_⟩
    change singularBoundaryFinsupp (TopCat.of S) 1 (b₀ + ∑ i, fillings i) = chain
    rw [map_add, map_sum, hb₀]
    simp_rw [hfillings]
    exact sub_add_cancel _ _
  obtain ⟨b, hb⟩ := hfill
  apply hnonzeroF
  apply (ModuleCat.mono_iff_injective (C.homologyι 1)).mp inferInstance
  rw [← hz]
  change C.homologyι 1 (C.homologyπ 1 z) = (C.homologyι 1).hom 0
  rw [map_zero]
  have hident := congrArg (fun f => f z) (C.homology_π_ι 1)
  change C.homologyι 1 (C.homologyπ 1 z) = C.pOpcycles 1 (C.iCycles 1 z) at hident
  rw [hident, ← hb]
  have hzero := congrArg (fun f => f b) (C.d_pOpcycles 2 1)
  change C.pOpcycles 1 (C.d 2 1 b) = 0 at hzero
  exact hzero


end CurveComplexGenusTwo.SourceTopology
