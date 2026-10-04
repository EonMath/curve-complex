import CurveComplexGenusTwo.Topology.ActualThreeArcCount.GeneratorIncrement
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.RegionHomology
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open Set Topology CategoryTheory CategoryTheory.Limits ContinuousMap
open CurveComplexGenusTwo.CWHurewicz CircleHomologyComputation
noncomputable section
namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

private theorem positive_homology_contractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (z : H X 1) : z = 0 := by
  have h := positiveHomologyMap_eq_zero_of_nullhomotopic
    (ContinuousMap.id X) (id_nullhomotopic X) 1 (by omega)
  change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (𝟙 (TopCat.of X)) = 0 at h
  rw [CategoryTheory.Functor.map_id] at h
  exact congrArg (fun f => f z) h

/-- Concrete subset version of the one-strip Mayer--Vietoris step. -/
theorem mv_union_one_generator
    (S : Type) [TopologicalSpace S] (U V : Set S)
    (hU : IsOpen U) (hV : IsOpen V) [ContractibleSpace V]
    (e : ↥(U ∩ V) ≃ₕ (Unit ⊕ Unit)) :
    ∃ z : H ↥(U ∪ V) 1, ∀ y : H ↥(U ∪ V) 1,
      ∃ m : H U 1, ∃ k : ℤ,
        y = actualSubsetHomologyMap (TopCat.of S) U (U ∪ V) Set.subset_union_left 1 m + k • z := by
  let X := U ∪ V
  let A : Set X := {z | z.val ∈ U}
  let B : Set X := {z | z.val ∈ V}
  let eA : A ≃ₜ U :=
    { toFun := fun t => ⟨t.val.val, t.property⟩
      invFun := fun t => ⟨⟨t.val, Or.inl t.property⟩, t.property⟩
      left_inv := by intro t; rfl
      right_inv := by intro t; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let eB : B ≃ₜ V :=
    { toFun := fun t => ⟨t.val.val, t.property⟩
      invFun := fun t => ⟨⟨t.val, Or.inr t.property⟩, t.property⟩
      left_inv := by intro t; rfl
      right_inv := by intro t; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let eAB : ↥(A ∩ B) ≃ₜ ↥(U ∩ V) :=
    { toFun := fun t => ⟨t.val.val, t.property⟩
      invFun := fun t => ⟨⟨t.val, Or.inl t.property.1⟩, t.property⟩
      left_inv := by intro t; rfl
      right_inv := by intro t; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hA : IsOpen A := hU.preimage continuous_subtype_val
  have hB : IsOpen B := hV.preimage continuous_subtype_val
  have hcover : A ∪ B = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact z.property
  letI : ContractibleSpace B := eB.contractibleSpace
  obtain ⟨z, hz⟩ := mv_one_generator_modulo_old_image (TopCat.of X) A B hA hB hcover
    (positive_homology_contractible B) (eAB.toHomotopyEquiv.trans e)
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have hnat : F.map (TopCat.ofHom (⟨eA, eA.continuous⟩ : C(A, U))) ≫
      actualSubsetHomologyMap (TopCat.of S) U X Set.subset_union_left 1 =
      homologyInclusion X A 1 := by
    change F.map _ ≫ F.map _ = F.map _
    rw [← F.map_comp]
    rfl
  refine ⟨z, fun y => ?_⟩
  obtain ⟨m, k, hm⟩ := hz y
  refine ⟨F.map (TopCat.ofHom (⟨eA, eA.continuous⟩ : C(A, U))) m, k, ?_⟩
  rw [hm]
  congr 1
  exact (congrArg (fun f => f m) hnat).symm

private theorem subset_homologyInclusion_comp
    (S : Type) [TopologicalSpace S] (U V : Set S) (h : U ⊆ V) (n : ℕ) :
    actualSubsetHomologyMap (TopCat.of S) U V h n ≫ homologyInclusion S V n =
      homologyInclusion S U n := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)
  change F.map _ ≫ F.map _ = F.map _
  rw [← F.map_comp]
  rfl

/-- A finite disjoint family of contractible windows with two-component overlaps
adds at most one ambient first-homology generator per window. -/
theorem finite_disjoint_open_cover_image_generators
    (S : Type) [TopologicalSpace S] (D : Set S) (hD : IsOpen D)
    {ι : Type} (W : ι → Set S)
    (hW : ∀ i, IsOpen (W i) ∧ ContractibleSpace ↥(W i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hoverlap : ∀ i, Nonempty (↥(D ∩ W i) ≃ₕ (Unit ⊕ Unit)))
    (hzero : homologyInclusion S D 1 = 0)
    (F : Finset ι) :
    ∃ v : Fin F.card → H S 1,
      ∀ y : H ↥(D ∪ ⋃ i ∈ F, W i) 1,
        homologyInclusion S (D ∪ ⋃ i ∈ F, W i) 1 y ∈ Submodule.span ℤ (Set.range v) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty]
    have hempty : D ∪ ⋃ i ∈ (∅ : Finset ι), W i = D := by simp
    rw [hempty]
    refine ⟨Fin.elim0, fun y => ?_⟩
    rw [hzero]
    exact Submodule.zero_mem _
  | @insert i F hi ih =>
    let U : Set S := D ∪ ⋃ j ∈ F, W j
    have hU : IsOpen U := hD.union (isOpen_iUnion (fun j => isOpen_iUnion (fun _ => (hW j).1)))
    have heq : D ∪ ⋃ j ∈ insert i F, W j = U ∪ W i := by
      ext y
      simp only [mem_union, mem_iUnion, Finset.mem_insert]
      dsimp [U]
      aesop
    rw [Finset.card_insert_of_notMem hi, heq]
    obtain ⟨v, hv⟩ := ih
    have hint : U ∩ W i = D ∩ W i := by
      apply Set.Subset.antisymm
      · rintro y ⟨hy, hyi⟩
        rcases hy with hyD | hyW
        · exact ⟨hyD, hyi⟩
        · simp only [Set.mem_iUnion] at hyW
          obtain ⟨j, hj, hyj⟩ := hyW
          exact False.elim (Set.disjoint_left.mp (hdisj j i (fun h => hi (h ▸ hj))) hyj hyi)
      · exact fun y hy => ⟨Or.inl hy.1, hy.2⟩
    letI : ContractibleSpace ↥(W i) := (hW i).2
    let e : ↥(U ∩ W i) ≃ₕ (Unit ⊕ Unit) :=
      (Homeomorph.setCongr hint).toHomotopyEquiv.trans (hoverlap i).some
    obtain ⟨z, hz⟩ := mv_union_one_generator S U (W i) hU (hW i).1 e
    let w : Fin (F.card + 1) → H S 1 := Fin.cons (homologyInclusion S (U ∪ W i) 1 z) v
    refine ⟨w, fun y => ?_⟩
    obtain ⟨m, k, hm⟩ := hz y
    rw [hm, map_add, map_zsmul]
    apply Submodule.add_mem
    · have hnat := congrArg (fun f => f m)
        (subset_homologyInclusion_comp S U (U ∪ W i) Set.subset_union_left 1)
      change homologyInclusion S (U ∪ W i) 1
        (actualSubsetHomologyMap (TopCat.of S) U (U ∪ W i) Set.subset_union_left 1 m) =
        homologyInclusion S U 1 m at hnat
      rw [hnat]
      exact (Submodule.span_mono (by
        rintro _ ⟨j, rfl⟩
        exact ⟨j.succ, by simp [w]⟩)) (hv m)
    · exact (Submodule.span ℤ (Set.range w)).toAddSubgroup.zsmul_mem
        (Submodule.subset_span ⟨0, by simp [w]⟩) k

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
