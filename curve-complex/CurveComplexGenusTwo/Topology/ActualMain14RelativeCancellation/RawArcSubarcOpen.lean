import CurveComplexGenusTwo.Topology.IntersectionParity.SurfaceDiskInterior
import Mathlib.Topology.Order.IntermediateValue

namespace CurveComplex.LocalSurgery
open Set Topology

theorem embedded_interval_subarc_interior_isOpen
    {S : Type} [TopologicalSpace S]
    (a f : C(Interval,S)) (ha : IsEmbedding a) (hf : IsEmbedding f)
    (hfa : range f ⊆ range a) :
    IsOpen {x : range a | (x : S) ∈ f '' Ioo (0:Interval) 1} := by
  let e : Interval ≃ₜ range a := ha.toHomeomorph
  let coords : Interval → Interval := fun t => e.symm ⟨f t,hfa (mem_range_self t)⟩
  have hcoords : Continuous coords := e.symm.continuous.comp (f.continuous.subtype_mk _)
  have hcoords_map (t : Interval) : a (coords t) = f t :=
    congrArg Subtype.val (e.apply_symm_apply ⟨f t,hfa (mem_range_self t)⟩)
  have hci : Function.Injective coords := by
    intro t u he
    apply hf.injective
    exact (hcoords_map t).symm.trans ((congrArg a he).trans (hcoords_map u))
  have hco : IsOpen (coords '' Ioo (0:Interval) 1) := by
    rcases hcoords.strictMono_of_inj_boundedOrder' hci with hmono | hanti
    · rw [hcoords.image_Ioo_of_strictMono hmono]
      exact isOpen_Ioo
    · have hdual : Continuous (fun t => OrderDual.toDual (coords t)) := hcoords
      change IsOpen ((fun t => OrderDual.toDual (coords t)) '' Ioo (0:Interval) 1)
      rw [hdual.image_Ioo_of_strictMono hanti]
      exact isOpen_Ioo
  have hset : {x : range a | (x : S) ∈ f '' Ioo (0:Interval) 1} =
      e.symm ⁻¹' (coords '' Ioo (0:Interval) 1) := by
    ext x
    constructor
    · rintro ⟨t,ht,he⟩
      exact ⟨t,ht,congrArg e.symm (Subtype.ext he)⟩
    · rintro ⟨t,ht,he⟩
      refine ⟨t,ht,?_⟩
      exact (hcoords_map t).symm.trans ((congrArg a he).trans
        (congrArg Subtype.val (e.apply_symm_apply x)))
  rw [hset]
  exact hco.preimage e.symm.continuous

theorem embedded_interval_subarc_subset_of_endpoints_mem
    {S : Type} [TopologicalSpace S]
    (a f q : C(Interval,S)) (ha : IsEmbedding a) (hq : IsEmbedding q)
    (hfa : range f ⊆ range a) (hqa : range q ⊆ range a)
    (h0 : q 0 ∈ range f) (h1 : q 1 ∈ range f) : range q ⊆ range f := by
  let e : Interval ≃ₜ range a := ha.toHomeomorph
  let cf : Interval → Interval := fun t => e.symm ⟨f t,hfa (mem_range_self t)⟩
  let cq : Interval → Interval := fun t => e.symm ⟨q t,hqa (mem_range_self t)⟩
  have hcf : Continuous cf := e.symm.continuous.comp (f.continuous.subtype_mk _)
  have hcq : Continuous cq := e.symm.continuous.comp (q.continuous.subtype_mk _)
  have hfm (t : Interval) : a (cf t) = f t :=
    congrArg Subtype.val (e.apply_symm_apply ⟨f t,hfa (mem_range_self t)⟩)
  have hqm (t : Interval) : a (cq t) = q t :=
    congrArg Subtype.val (e.apply_symm_apply ⟨q t,hqa (mem_range_self t)⟩)
  have hcqi : Function.Injective cq := by
    intro t u he
    exact hq.injective ((hqm t).symm.trans ((congrArg a he).trans (hqm u)))
  have h0c : cq 0 ∈ range cf := by
    obtain ⟨t,ht⟩ := h0
    refine ⟨t,congrArg e.symm (Subtype.ext ht)⟩
  have h1c : cq 1 ∈ range cf := by
    obtain ⟨t,ht⟩ := h1
    refine ⟨t,congrArg e.symm (Subtype.ext ht)⟩
  have hconn : IsPreconnected (range cf) := by
    simpa only [Set.image_univ] using isPreconnected_univ.image cf hcf.continuousOn
  rintro x ⟨t,rfl⟩
  have htc : cq t ∈ range cf := by
    rcases hcq.strictMono_of_inj_boundedOrder' hcqi with hm | hm
    · exact hconn.Icc_subset h0c h1c ⟨hm.monotone t.property.1,hm.monotone t.property.2⟩
    · exact hconn.Icc_subset h1c h0c ⟨hm.antitone t.property.2,hm.antitone t.property.1⟩
  obtain ⟨v,hv⟩ := htc
  exact ⟨v,(hfm v).symm.trans ((congrArg a hv).trans (hqm t))⟩

end CurveComplex.LocalSurgery
