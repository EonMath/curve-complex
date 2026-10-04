import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualAdjacentFixedArcCompetitor
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import Mathlib.Topology.Compactness.Compact

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A genuine continuous arc sweep cannot create contacts on a compact
parameter carrier away from all its initial contacts. The open time
neighborhood is produced by the tube lemma from the actual sweep. -/
theorem actual_marked_sweep_compact_contact_localization
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (F : C(Interval × Interval,S)) (τ : Interval)
    (K W : Set Interval) (hK : IsCompact K) (hW : IsOpen W)
    (hcontacts : ∀ t ∈ K, F (τ,t) ∈ a.val.image → t ∈ W) :
    ∃ V : Set Interval, IsOpen V ∧ τ ∈ V ∧
      ∀ σ ∈ V, ∀ t ∈ K, F (σ,t) ∈ a.val.image → t ∈ W := by
  letI : T2Space S := M.sphere.symm.t2Space
  have hAclosed : IsClosed a.val.image := (isCompact_range a.val.continuous).isClosed
  let N : Set (Interval × Interval) := F ⁻¹' a.val.imageᶜ
  have hN : IsOpen N := hAclosed.isOpen_compl.preimage F.continuous
  have hbadcompact : IsCompact (K \ W) := hK.inter_right hW.isClosed_compl
  have hsafe : ({τ} : Set Interval) ×ˢ (K \ W) ⊆ N := by
    rintro ⟨σ,t⟩ ⟨hσ,htK,htW⟩ hhit
    have hστ : σ=τ := mem_singleton_iff.mp hσ
    subst σ
    exact htW (hcontacts t htK hhit)
  obtain ⟨V,U,hV,hU,hτ,hcarrier,hprod⟩ :=
    generalized_tube_lemma isCompact_singleton hbadcompact hN hsafe
  refine ⟨V,hV,hτ (mem_singleton τ),?_⟩
  intro σ hσ t htK hhit
  by_contra htW
  exact hprod ⟨hσ,hcarrier ⟨htK,htW⟩⟩ hhit

/-- The contact parameter set for a genuine finite-transverse slice is
finite on every compact interval strictly inside the marked endpoints.
Thus the preceding localization is genuinely around finitely many
actual crossings, not an assumed finite sweep-event decomposition. -/
theorem actual_nonloop_slice_contact_parameters_finite
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : b.val.map 0 ≠ b.val.map 1)
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (l u : ℝ) (hl : 0 < l) (hu : u < 1) :
    {t : Interval | l ≤ (t:ℝ) ∧ (t:ℝ) ≤ u ∧ b.val.map t ∈ a.val.image}.Finite := by
  have hinj := NonLoopArc.injective ⟨b.val,hne⟩
  apply (hfinite.preimage hinj.injOn).subset
  intro t ht
  have ht0 : t ≠ 0 := by intro he; subst t; have hh : l ≤ (0:ℝ) := ht.1; linarith
  have ht1 : t ≠ 1 := by intro he; subst t; have hh : (1:ℝ) ≤ u := ht.2.1; linarith
  have hnotmark : b.val.map t ∉ (M.cover.branch : Set S) := fun hm =>
    (b.val.marked_only_at_ends t hm).elim ht0 ht1
  exact ⟨⟨ht.2.2,hnotmark⟩,⟨t,rfl⟩,hnotmark⟩

end CurveComplex.HyperellipticModel
