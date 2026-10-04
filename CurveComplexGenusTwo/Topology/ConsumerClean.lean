import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.CWHurewicz.HomotopyHomologyIso
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

namespace BoundaryEssentiality
open CategoryTheory CurveComplex CurveComplexGenusTwo.CWHurewicz

open CategoryTheory.Limits
open scoped Simplicial
private abbrev RZ := ModuleCat.of ℤ ℤ
private noncomputable abbrev HF0 := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj RZ

private noncomputable def pointClass (X : SSet) (x : X _⦋0⦌) : RZ ⟶ X.homology RZ 0 :=
  (X.chainComplex RZ).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
    (X.chainComplex RZ).homologyπ 0

private theorem pointClass_iso (X : SSet) (x : X _⦋0⦌) :
    pointClass X x ≫ (X.homology₀Iso RZ).hom =
      Sigma.ι (fun _ : X.π₀ => RZ) (SSet.π₀.mk x) := by
  simp [pointClass]

private theorem hzero_ext {X : SSet} {M : ModuleCat ℤ} {f g : X.homology RZ 0 ⟶ M}
    (h : ∀ x, pointClass X x ≫ f = pointClass X x ≫ g) : f = g := by
  apply (cancel_epi (X.homology₀Iso RZ).inv).mp
  apply Sigma.hom_ext
  intro i
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective i
  rw [← pointClass_iso X x]
  simpa using h x

private theorem pointClass_map {X Y : SSet} (f : X ⟶ Y) (x : X _⦋0⦌) :
    pointClass X x ≫ HomologicalComplex.homologyMap (SSet.chainComplexMap f RZ) 0 =
      pointClass Y (f.app _ x) := by
  simp [pointClass]

private theorem augmentation_naturality {X Y : TopCat} (f : X ⟶ Y) :
    HF0.map f ≫ Y.singularHomology₀ε RZ = X.singularHomology₀ε RZ := by
  apply hzero_ext
  intro x
  change pointClass (TopCat.toSSet.obj X) x ≫
    (HomologicalComplex.homologyMap (SSet.chainComplexMap (TopCat.toSSet.map f) RZ) 0 ≫
      (TopCat.toSSet.obj Y).homology₀ε RZ) = _
  rw [← Category.assoc, pointClass_map]
  simp [pointClass, TopCat.singularHomology₀ε]


private theorem rank_obstruction {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {g : ℕ} (hg : 2 ≤ g) (hS : IsGenus S g)
    (f : (Fin 2 → ℤ) →ₗ[ℤ] H S 1) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨e⟩ := hS.2.2.2
  let k := e.toLinearEquiv.toLinearMap.comp f
  have hk : Function.Surjective k := e.toLinearEquiv.surjective.comp hf
  have hn := LinearMap.finrank_le_finrank_of_surjective hk
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at hn
  omega

private theorem inclusion_surjective_of_disk_cover (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
    (hi : Function.Injective (actualMVDifference X U V 0))
    (hv : ∀ v : H V 1, v = 0) :
    Function.Surjective (homologyInclusion X U 1) := by
  intro x
  have hz : actualMVConnecting X U V hU hV hc 0 x = 0 := by
    apply hi
    have h := congrArg (fun f => f x) (actualMVConnecting_difference X U V hU hV hc 0)
    simpa using h
  obtain ⟨q, hq⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (actualMV_exact_ambient X U V hU hV hc 0) x hz
  refine ⟨q.1, ?_⟩
  rw [actualMVSum_apply, hv q.2, map_zero, add_zero] at hq
  exact hq

private theorem difference_injective_of_connected_overlap (X : TopCat) (U V : Set X)
    [PathConnectedSpace ↥(U ∩ V)] :
    Function.Injective (actualMVDifference X U V 0) := by
  intro a b hab
  have hab' := congrArg Prod.fst hab
  dsimp only at hab'
  rw [actualMVDifference_apply, actualMVDifference_apply] at hab'
  have hn := augmentation_naturality (singularSubsetInclusion X (U ∩ V) U Set.inter_subset_left)
  have ha := congrArg (fun f => f a) hn
  have hb := congrArg (fun f => f b) hn
  apply (ModuleCat.mono_iff_injective ((TopCat.of ↥(U ∩ V)).singularHomology₀ε RZ)).mp inferInstance
  exact ha.symm.trans ((congrArg (fun x => (TopCat.of U).singularHomology₀ε RZ x) hab').trans hb)

private theorem no_disk_cover_of_genus {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {g : ℕ} (hg : 2 ≤ g) (hS : IsGenus S g)
    (U V : Set S) (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
    [PathConnectedSpace ↥(U ∩ V)]
    (hv : ∀ v : H V 1, v = 0)
    (p : (Fin 2 → ℤ) →ₗ[ℤ] H U 1) (hp : Function.Surjective p) : False := by
  exact rank_obstruction hg hS ((homologyInclusion (TopCat.of S) U 1).hom.comp p)
    ((inclusion_surjective_of_disk_cover (TopCat.of S) U V hU hV hc
      (difference_injective_of_connected_overlap (TopCat.of S) U V) hv).comp hp)

private theorem homology_one_zero_of_contractible (V : Type) [TopologicalSpace V]
    [ContractibleSpace V] (v : H V 1) : v = 0 := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit V
  let i := singularHomologyIsoOfHomotopyInverse RZ 1 e.toFun e.invFun e.left_inv e.right_inv
  have hz := AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) 1 RZ (TopCat.of Unit) (by decide)
  letI : Subsingleton (H Unit 1) := ModuleCat.subsingleton_of_isZero hz
  apply i.toLinearEquiv.injective
  exact Subsingleton.elim _ _

private theorem no_contractible_cap_of_genus {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {g : ℕ} (hg : 2 ≤ g) (hS : IsGenus S g)
    (U V : Set S) (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
    [PathConnectedSpace ↥(U ∩ V)] [ContractibleSpace V]
    (p : (Fin 2 → ℤ) →ₗ[ℤ] H U 1) (hp : Function.Surjective p) : False := by
  exact no_disk_cover_of_genus hg hS U V hU hV hc
    (homology_one_zero_of_contractible V) p hp

#print axioms no_contractible_cap_of_genus
#print axioms no_disk_cover_of_genus
end BoundaryEssentiality


/-! Review candidates only. Every `sorry` below is an explicitly open obligation.
The final two declarations retain the original genus hypotheses and assume no
essential disjoint curve, compatible bands, frontier, or cap producer. -/

namespace CurveComplex
open Topology CurveComplexGenusTwo.CWHurewicz

/-- Pure frontier consumer; no new geometric construction. -/
theorem crossing_curves_disjoint_frontier
    {S : Type} [TopologicalSpace S] (A B : Curve S)
    (N : Set S) (c : Curve S)
    (hinside : A.image ∪ B.image ⊆ interior N)
    (hfrontier : frontier N = c.image) :
    Disjoint A.image c.image ∧ Disjoint B.image c.image := by
  have hdisj : Disjoint (interior N) c.image := by
    rw [← hfrontier]
    exact disjoint_interior_frontier
  exact ⟨hdisj.mono_left (Set.Subset.trans Set.subset_union_left hinside),
    hdisj.mono_left (Set.Subset.trans Set.subset_union_right hinside)⟩

/-- Homological contradiction consumer. The cap owner must prove this
disk-to-cover implication for the exact geometric frontier it constructs.
It is an intermediate obligation, not a final source theorem hypothesis. -/
theorem frontier_essential_of_disk_cap_cover
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {g : ℕ} (hg : 2 ≤ g) (hS : IsGenus S g) (c : Curve S)
    (hcap : BoundsDisc c →
      ∃ U V : Set S, IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧
        PathConnectedSpace ↥(U ∩ V) ∧ ContractibleSpace ↥V ∧
        ∃ p : (Fin 2 → ℤ) →ₗ[ℤ] H U 1, Function.Surjective p) :
    Essential c := by
  intro hdisc
  obtain ⟨U, V, hU, hV, hcover, hinter, hcontract, p, hp⟩ := hcap hdisc
  letI := hinter
  letI := hcontract
  exact BoundaryEssentiality.no_contractible_cap_of_genus hg hS U V hU hV hcover p hp

/-- Consumer for the actual supplied frontier curve, retaining the cap
obligation explicitly instead of postulating essentiality. -/
theorem essential_disjoint_frontier_of_disk_cap_cover
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {g : ℕ} (hg : 2 ≤ g) (hS : IsGenus S g)
    (A B : Curve S) (N : Set S) (c : Curve S)
    (hinside : A.image ∪ B.image ⊆ interior N)
    (hfrontier : frontier N = c.image)
    (hcap : BoundsDisc c →
      ∃ U V : Set S, IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧
        PathConnectedSpace ↥(U ∩ V) ∧ ContractibleSpace ↥V ∧
        ∃ p : (Fin 2 → ℤ) →ₗ[ℤ] H U 1, Function.Surjective p) :
    Essential c ∧ Disjoint A.image c.image ∧ Disjoint B.image c.image := by
  exact ⟨frontier_essential_of_disk_cap_cover hg hS c hcap,
    crossing_curves_disjoint_frontier A B N c hinside hfrontier⟩

end CurveComplex

#print axioms CurveComplex.crossing_curves_disjoint_frontier
#print axioms CurveComplex.frontier_essential_of_disk_cap_cover
#print axioms CurveComplex.essential_disjoint_frontier_of_disk_cap_cover
