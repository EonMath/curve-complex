import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.GenericRealization
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

open CurveComplex Set Topology
open scoped Manifold ContDiff

namespace RegionalEmbeddedFamily

theorem mem_interior_of_mem_subtype_not_frontier
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (y : F) (hy : y.val ∉ frontier F) : y.val ∈ interior F := by
  by_contra hn
  exact hy ⟨subset_closure y.property, hn⟩

theorem proper_arc_interior_mem_interior
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (a : C(Interval, ↥F))
    (ha : ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F)
    {t : Interval} (ht : t ∈ Set.Ioo (0 : Interval) 1) :
    (a t).val ∈ interior F :=
  mem_interior_of_mem_subtype_not_frontier (a t) (ha t ht)

theorem proper_arc_interior_has_regional_chart
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {F : Set S} (a : C(Interval, ↥F))
    (ha : ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F)
    {t : Interval} (ht : t ∈ Set.Ioo (0 : Interval) 1) :
    ∃ U : Set S, IsOpen U ∧ (a t).val ∈ U ∧
      U ⊆ interior F ∧
      U ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (a t).val).source := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) (a t).val
  refine ⟨interior F ∩ e.source, isOpen_interior.inter e.open_source,
    ⟨proper_arc_interior_mem_interior a ha ht, mem_chart_source _ _⟩,
    inter_subset_left, inter_subset_right⟩

theorem homotopic_proper_arcs_bound_null_loop
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval, ↥F))
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hhom : Path.Homotopic
      (⟨a, rfl, rfl⟩ : Path (a 0) (a 1))
      (⟨b, h0, h1⟩ : Path (a 0) (a 1))) :
    Path.Homotopic
      ((⟨a, rfl, rfl⟩ : Path (a 0) (a 1)).trans
        (⟨b, h0, h1⟩ : Path (a 0) (a 1)).symm)
      (Path.refl (a 0)) := by
  let p : Path (a 0) (a 1) := ⟨a, rfl, rfl⟩
  let q : Path (a 0) (a 1) := ⟨b, h0, h1⟩
  exact (hhom.hcomp (Path.Homotopic.refl q.symm)).trans
    (Path.Homotopic.trans_symm q)

theorem proper_arc_avoids_retained_frontier_curve
    {S : Type*} [TopologicalSpace S] {F B C : Set S}
    (hCB : Disjoint C B) (hCfrontier : C ⊆ frontier F)
    (a : C(Interval, ↥F))
    (ha0 : (a 0).val ∈ B) (ha1 : (a 1).val ∈ B)
    (haClear : ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F) :
    Disjoint C (Set.range (fun t => (a t).val)) := by
  apply Set.disjoint_left.mpr
  rintro y hyC ⟨t, rfl⟩
  by_cases ht0 : t = 0
  · subst t
    exact Set.disjoint_left.mp hCB hyC ha0
  by_cases ht1 : t = 1
  · subst t
    exact Set.disjoint_left.mp hCB hyC ha1
  have ht : t ∈ Set.Ioo (0 : Interval) 1 :=
    ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
      lt_of_le_of_ne t.property.2 ht1⟩
  exact haClear t ht (hCfrontier hyC)

theorem embedded_arcs_same_range_family
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hr : Set.range a = Set.range b)
    (haClear : ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F) :
    ∃ (V : C(Interval × Interval, ↥F)) (ρ : Interval ≃ₜ Interval),
      ρ 0 = 0 ∧ ρ 1 = 1 ∧
      (∀ s, V (0,s) = a s) ∧ (∀ s, V (1,s) = b (ρ s)) ∧
      (∀ t, Topology.IsEmbedding (fun s => V (t,s))) ∧
      (∀ t, V (t,0) = a 0 ∧ V (t,1) = a 1) ∧
      (∀ t s, s ∈ Set.Ioo (0 : Interval) 1 → (V (t,s)).val ∉ frontier F) := by
  let ρ : Interval ≃ₜ Interval :=
    ha.toHomeomorph.trans ((Homeomorph.setCongr hr).trans hb.toHomeomorph.symm)
  have hρ (s : Interval) : b (ρ s) = a s := by
    apply Subtype.ext
    calc
      (b (ρ s)).val = (hb.toHomeomorph (ρ s)).val := rfl
      _ = ((Homeomorph.setCongr hr) (ha.toHomeomorph s)).val := by
        dsimp [ρ]
        exact congrArg (fun z : Set.range b => z.val.val) (hb.toHomeomorph.apply_symm_apply
          ((Homeomorph.setCongr hr) (ha.toHomeomorph s)))
      _ = (ha.toHomeomorph s).val := rfl
      _ = (a s).val := rfl
  have hρ0 : ρ 0 = 0 := hb.injective (by rw [hρ, h0])
  have hρ1 : ρ 1 = 1 := hb.injective (by rw [hρ, h1])
  let V : C(Interval × Interval, ↥F) :=
    ⟨fun p => a p.2, a.continuous.comp continuous_snd⟩
  refine ⟨V, ρ, hρ0, hρ1, ?_, ?_, ?_, ?_, ?_⟩
  · intro s; rfl
  · intro s; exact (hρ s).symm
  · intro t; exact ha
  · intro t; exact ⟨rfl, rfl⟩
  · intro t s hs; exact haClear s hs

end RegionalEmbeddedFamily
