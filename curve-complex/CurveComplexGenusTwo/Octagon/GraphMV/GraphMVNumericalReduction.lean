import CurveComplexGenusTwo.Octagon.GraphMV.GraphMVActual
import CurveComplexGenusTwo.Octagon.GraphMV.GraphMVKernel

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.Octagon.AttachingMap.GraphMV

private abbrev GX := TopCat.of BoundaryGraph
private abbrev U : Set GX := vertexStar
private abbrev V : Set GX := edgeMiddles

/-- Exactness turns the actual degree-zero MV coordinate comparison into the
rank-four homology result. The coordinate comparison itself remains geometric. -/
def graph_H1_iso_of_coordinates
    (hpair : IsZero (ModuleCat.of ℤ (H U 1 × H V 1)))
    (e : H ↥(U ∩ V) 0 ≃ₗ[ℤ] CurveComplex.Octagon.GraphMV.OverlapCoordinates)
    (hdiff : ∀ x : H ↥(U ∩ V) 0,
      graphMVDifference 0 x = 0 ↔
        CurveComplex.Octagon.GraphMV.difference (e x) = 0) :
    H BoundaryGraph 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ) := by
  let f := graphMVConnecting 0
  let g := graphMVDifference 0
  have hfg : f ≫ g = 0 := graphMV_connecting_difference 0
  have ex := graphMV_exact_intersection 0
  have hsum : graphMVSum 1 = 0 := hpair.eq_of_src _ _
  have hm : Mono f := (ShortComplex.exact_iff_mono _ hsum).mp (graphMV_exact_ambient 0)
  have hinj : Function.Injective f := (ModuleCat.mono_iff_injective _).mp hm
  let ef : H BoundaryGraph 1 →ₗ[ℤ] CurveComplex.Octagon.GraphMV.OverlapCoordinates :=
    e.toLinearMap.comp f.hom
  have hz (a : H BoundaryGraph 1) :
      ef a ∈ LinearMap.ker CurveComplex.Octagon.GraphMV.difference := by
    apply LinearMap.mem_ker.mpr
    apply (hdiff (f a)).mp
    exact congrArg (fun m => m a) hfg
  let k : H BoundaryGraph 1 →ₗ[ℤ]
      LinearMap.ker CurveComplex.Octagon.GraphMV.difference :=
    ef.codRestrict _ hz
  let l : H BoundaryGraph 1 →ₗ[ℤ] (Fin 4 → ℤ) :=
    CurveComplex.Octagon.GraphMV.kernelEquiv.toLinearMap.comp k
  have hi : Function.Injective l := by
    intro a b hab
    apply hinj
    apply e.injective
    change CurveComplex.Octagon.GraphMV.kernelEquiv (k a) =
      CurveComplex.Octagon.GraphMV.kernelEquiv (k b) at hab
    change (k a).1 = (k b).1
    exact congrArg Subtype.val
      (CurveComplex.Octagon.GraphMV.kernelEquiv.injective hab)
  have hs : Function.Surjective l := by
    intro z
    let q : LinearMap.ker CurveComplex.Octagon.GraphMV.difference :=
      CurveComplex.Octagon.GraphMV.kernelEquiv.symm z
    let b : H ↥(U ∩ V) 0 := e.symm q.1
    have hb : g b = 0 := (hdiff b).mpr (by simp [b])
    obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp ex b hb
    refine ⟨a, ?_⟩
    change CurveComplex.Octagon.GraphMV.kernelEquiv (k a) = z
    rw [← CurveComplex.Octagon.GraphMV.kernelEquiv.apply_symm_apply z]
    apply congrArg CurveComplex.Octagon.GraphMV.kernelEquiv
    apply Subtype.ext
    change e (f a) = q.1
    rw [ha]
    simp [b]
  exact (LinearEquiv.ofBijective l ⟨hi, hs⟩).toModuleIso

end CurveComplex.Octagon.AttachingMap.GraphMV

#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.graph_H1_iso_of_coordinates
