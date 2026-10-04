import CurveComplexGenusTwo.Topology.CapBandGeometry.BandMVNaturality
import CurveComplexGenusTwo.Topology.CapBandGeometry.BandIncidence

noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.CapBandGeometry
set_option backward.isDefEq.respectTransparency false
variable {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)

theorem bandMV_difference_kernel (x : H ↥(bandMVU D B ∩ bandMVV D B) 0) :
    actualMVDifference (bandTopCat D B) (bandMVU D B) (bandMVV D B) 0 x = 0 ↔
      bandIncidence (bandMVOverlapHZeroCoordinates D B x) = 0 := by
  rw [actualMVDifference_apply]
  change (bandMVSquareInclusionZero D B x, -bandMVMiddleInclusionZero D B x) = 0 ↔ _
  constructor
  · intro h
    have hu : bandMVSquareInclusionZero D B x = 0 := congrArg Prod.fst h
    have hv : bandMVMiddleInclusionZero D B x = 0 := neg_eq_zero.mp (congrArg Prod.snd h)
    apply Prod.ext
    · have h := bandMVSquareInclusion_coordinates D B x
      rw [hu, map_zero] at h
      simpa [bandIncidence, Fin.sum_univ_succ, add_assoc] using h.symm
    · funext i
      have h := bandMVMiddleInclusion_coordinates D B x i
      rw [hv, map_zero] at h
      fin_cases i <;> simpa [bandIncidence] using congrArg Neg.neg h.symm
  · intro h
    have hu : bandMVSquareInclusionZero D B x = 0 := by
      apply (bandMVUHZeroCoordinates D B).injective
      rw [bandMVSquareInclusion_coordinates, map_zero]
      have hs := congrArg Prod.fst h
      simpa [bandIncidence, Fin.sum_univ_succ, add_assoc] using hs
    have hv : bandMVMiddleInclusionZero D B x = 0 := by
      apply (bandMVVHZeroCoordinates D B).injective
      funext i
      rw [bandMVMiddleInclusion_coordinates]
      simp only [map_zero, Pi.zero_apply]
      fin_cases i
      · have hs := congrArg (fun y : ℤ × (Fin 2 → ℤ) => y.2 0) h
        simpa [bandIncidence] using neg_eq_zero.mp hs
      · have hs := congrArg (fun y : ℤ × (Fin 2 → ℤ) => y.2 1) h
        simpa [bandIncidence] using neg_eq_zero.mp hs
    simp [hu, hv]

/-- The genuine singular H1 of the same square/two-band witness has rank two.
The four-window incidence calculation is connected to actual MV inclusion maps. -/
def actual_band_HOne_coordinates : H (bandUnion D B) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) := by
  let X := bandTopCat D B
  let U := bandMVU D B
  let V := bandMVV D B
  let f := actualMVConnecting X U V (bandMVU_open D B) (bandMVV_open D B) (bandMV_cover D B) 0
  let g := actualMVDifference X U V 0
  have hfg : f ≫ g = 0 := actualMVConnecting_difference X U V
    (bandMVU_open D B) (bandMVV_open D B) (bandMV_cover D B) 0
  have ex := actualMV_exact_intersection X U V
    (bandMVU_open D B) (bandMVV_open D B) (bandMV_cover D B) 0
  have hsum : actualMVSum X U V 1 = 0 := (bandMV_pair_positive_zero D B 1 (by omega)).eq_of_src _ _
  have hm : Mono f := (ShortComplex.exact_iff_mono _ hsum).mp
    (actualMV_exact_ambient X U V (bandMVU_open D B) (bandMVV_open D B) (bandMV_cover D B) 0)
  have hinj : Function.Injective f := (ModuleCat.mono_iff_injective _).mp hm
  let e := bandMVOverlapHZeroCoordinates D B
  let ef : H (bandUnion D B) 1 →ₗ[ℤ] (Fin 4 → ℤ) := e.toLinearMap.comp f.hom
  have hz (a : H (bandUnion D B) 1) : ef a ∈ LinearMap.ker bandIncidence := by
    apply LinearMap.mem_ker.mpr
    apply (bandMV_difference_kernel D B (f a)).mp
    exact congrArg (fun m => m a) hfg
  let k : H (bandUnion D B) 1 →ₗ[ℤ] LinearMap.ker bandIncidence := ef.codRestrict _ hz
  let l : H (bandUnion D B) 1 →ₗ[ℤ] (Fin 2 → ℤ) :=
    bandIncidenceKernelEquiv.symm.toLinearMap.comp k
  have hi : Function.Injective l := by
    intro a b hab
    apply hinj
    apply e.injective
    change bandIncidenceKernelEquiv.symm (k a) = bandIncidenceKernelEquiv.symm (k b) at hab
    exact congrArg Subtype.val (bandIncidenceKernelEquiv.symm.injective hab)
  have hs : Function.Surjective l := by
    intro z
    let q : LinearMap.ker bandIncidence := bandIncidenceKernelEquiv z
    let b : H ↥(U ∩ V) 0 := e.symm q.1
    have hb : g b = 0 := (bandMV_difference_kernel D B b).mpr (by
      change bandIncidence (e (e.symm q.1)) = 0
      rw [e.apply_symm_apply]
      exact q.2)
    obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp ex b hb
    refine ⟨a, ?_⟩
    change bandIncidenceKernelEquiv.symm (k a) = z
    rw [← bandIncidenceKernelEquiv.symm_apply_apply z]
    apply congrArg bandIncidenceKernelEquiv.symm
    apply Subtype.ext
    change e (f a) = q.1
    rw [ha]
    simp [b]
  exact LinearEquiv.ofBijective l ⟨hi, hs⟩

#print axioms actual_band_HOne_coordinates
end CurveComplex.CapBandGeometry
