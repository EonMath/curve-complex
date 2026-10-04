import CurveComplexGenusTwo.Topology.ActualThreeArcCount.OriginalRegionVanishing
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHZero
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

open CurveComplex Set Topology CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz CircleHomologyComputation
open scoped Manifold ContDiff
noncomputable section
namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut
private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private theorem positive_homology_zero_of_contractible
    (V : Type) [TopologicalSpace V] [ContractibleSpace V] (z : H V 1) : z = 0 := by
  have hh := positiveHomologyMap_eq_zero_of_nullhomotopic
    (ContinuousMap.id V) (id_nullhomotopic V) 1 (by omega)
  change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (𝟙 (TopCat.of V)) = 0 at hh
  rw [CategoryTheory.Functor.map_id] at hh
  exact congrArg (fun f => f z) hh

private theorem mv_inclusion_surjective_of_connected_overlap
    (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace ↥(U ∩ V)] [ContractibleSpace ↥V] :
    Function.Surjective (homologyInclusion X U 1) := by
  have hinj : Function.Injective (actualMVDifference X U V 0) := by
    intro a b hab
    rw [actualMVDifference_apply, actualMVDifference_apply] at hab
    have hleft := congrArg Prod.fst hab
    have hn := augmentation_naturality (singularSubsetInclusion X (U ∩ V) U Set.inter_subset_left)
    have ha := congrArg (fun f => f a) hn
    have hb := congrArg (fun f => f b) hn
    apply (ModuleCat.mono_iff_injective
      ((TopCat.of ↥(U ∩ V)).singularHomology₀ε (ModuleCat.of ℤ ℤ))).mp inferInstance
    exact ha.symm.trans ((congrArg
      (fun x => (TopCat.of U).singularHomology₀ε (ModuleCat.of ℤ ℤ) x) hleft).trans hb)
  intro y
  have hδ : actualMVConnecting X U V hU hV hcover 0 y = 0 := by
    apply hinj
    have hh := congrArg (fun f => f y) (actualMVConnecting_difference X U V hU hV hcover 0)
    simpa using hh
  obtain ⟨q, hq⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (actualMV_exact_ambient X U V hU hV hcover 0) y hδ
  refine ⟨q.1, ?_⟩
  rw [actualMVSum_apply, positive_homology_zero_of_contractible V q.2, map_zero, add_zero] at hq
  exact hq

private theorem planar_annulus_pathConnected (p : Plane) (r s : ℝ)
    (hr : 0 < r) (hrs : r < s) :
    IsPathConnected (Metric.ball p s \ Metric.closedBall p r) := by
  have hrank : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hsphere := isPathConnected_sphere hrank (0 : Plane) (by norm_num : (0 : ℝ) ≤ 1)
  have hradii := (convex_Ioo r s).isPathConnected ⟨(r+s)/2, by constructor <;> linarith⟩
  let F : Plane × ℝ → Plane := fun z => p + z.2 • z.1
  have hF : Continuous F := continuous_const.add (continuous_snd.smul continuous_fst)
  have heq : F '' (Metric.sphere (0 : Plane) 1 ×ˢ Set.Ioo r s) =
      Metric.ball p s \ Metric.closedBall p r := by
    ext z
    constructor
    · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
      have htpos : 0 < t := hr.trans ht.1
      simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le]
      change dist (p + t • u) p < s ∧ r < dist (p + t • u) p
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, hu', mul_one]
      exact ⟨ht.2, ht.1⟩
    · rintro ⟨hzs, hzr⟩
      have hlo : r < ‖z-p‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzr
      have hhi : ‖z-p‖ < s := by simpa [Metric.mem_ball, dist_eq_norm] using hzs
      have hn : 0 < ‖z-p‖ := hr.trans hlo
      refine ⟨(‖z-p‖⁻¹ • (z-p), ‖z-p‖), ⟨?_, hlo, hhi⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
      · change p + ‖z-p‖ • ‖z-p‖⁻¹ • (z-p) = z
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul, add_sub_cancel]
  rw [← heq]
  exact (hsphere.prod hradii).image hF

/-- The actual open exterior carries every first-homology class of the capped
source. The proof uses a slightly enlarged original chart disk. -/
theorem original_open_exterior_homologyInclusion_surjective
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target) :
    Function.Surjective (homologyInclusion S (interior (exterior S x R)) 1) := by
  letI : ClosedSurface S := Classical.choice hS.2.1
  let E := chartAt Plane x
  let p := E x
  obtain ⟨δ, hδ, ht⟩ := (isCompact_closedBall p R).exists_thickening_subset_open E.open_target htarget
  rw [thickening_closedBall hδ hR.le p] at ht
  let V : Set S := E.symm '' Metric.ball p (δ + R)
  let U : Set S := interior (exterior S x R)
  have hUeq : U = (E.symm '' Metric.closedBall p R)ᶜ := by
    dsimp only [U]
    rw [OriginalBoundaryArc.exterior_interior_eq_complement_chart_closed_disk S g hS x R hR htarget]
    simp only [OriginalBoundaryArc.openDisk, OriginalBoundaryArc.boundaryCircle,
      ← Set.image_union, Metric.ball_union_sphere]
    rfl
  have hV : IsOpen V := E.isOpen_image_symm_of_subset_target Metric.isOpen_ball ht
  have hcover : U ∪ V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ U
    · exact Or.inl hy
    · rw [hUeq] at hy
      obtain ⟨z, hz, rfl⟩ := not_not.mp hy
      refine Or.inr ⟨z, ?_, rfl⟩
      change dist z p ≤ R at hz
      change dist z p < δ + R
      linarith
  let d : Metric.ball p (δ+R) → S := fun z => E.symm z.val
  have hd : IsEmbedding d := E.symm.isEmbedding_restrict.comp (IsEmbedding.inclusion ht)
  have hrange : Set.range d = V := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩; exact ⟨z.val, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz⟩, rfl⟩
  let ev := hd.toHomeomorph.trans (Homeomorph.setCongr hrange)
  letI : ContractibleSpace (Metric.ball p (δ+R)) := Metric.contractibleSpace_ball (by linarith)
  letI : ContractibleSpace V := ev.contractibleSpace_iff.mp inferInstance
  have hoverlap : U ∩ V = E.symm '' (Metric.ball p (δ+R) \ Metric.closedBall p R) := by
    rw [hUeq]
    ext y
    constructor
    · rintro ⟨hy, z, hz, rfl⟩
      exact ⟨z, ⟨hz, fun h => hy ⟨z, h, rfl⟩⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hnot⟩, rfl⟩
      refine ⟨?_, ⟨z, hz, rfl⟩⟩
      rintro ⟨w, hw, he⟩
      have heq := E.symm.injOn (htarget hw) (ht hz) he
      exact hnot (heq ▸ hw)
  have hconn : IsPathConnected (U ∩ V) := by
    rw [hoverlap]
    exact (planar_annulus_pathConnected p R (δ+R) hR (by linarith)).image'
      (E.continuousOn_symm.mono (fun _ h => ht h.1))
  letI : PathConnectedSpace ↥(U ∩ V) := isPathConnected_iff_pathConnectedSpace.mp hconn
  exact mv_inclusion_surjective_of_connected_overlap (TopCat.of S) U V isOpen_interior hV hcover

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
