import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopOriginalPlaneJordanProducer
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualJordanPointInteriorArc
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- The actual original loop constructs an embedded ORIGINAL boundary arc
through its marked BASE as an interior point, with literal unmarked quarter
endpoints. No arc around the base or axis chart is supplied. -/
theorem actual_loop_base_original_arc
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1) :
    ∃ f : C(Interval,S), IsEmbedding f ∧ range f ⊆ a.val.image ∧
      f 0=a.val.map ⟨1/4,by norm_num⟩ ∧ f 1=a.val.map ⟨3/4,by norm_num⟩ ∧
      (∀ t, f t ∈ (M.cover.branch : Set S) ↔ f t=a.val.map 0) ∧
    ∃ Tail : Set S, IsClosed Tail ∧ a.val.image=range f ∪ Tail ∧
      range f ∩ Tail={f 0,f 1} ∧ a.val.map 0 ∉ Tail ∧
    ∃ r : Interval, 0<r ∧ r<1 ∧ f r=a.val.map 0 := by
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨p,hp,γ,hγ,hC,hcollision⟩ := actual_loop_original_plane_jordan_producer M a ha
  let s : Interval := ⟨1/4,by norm_num⟩
  let t : Interval := ⟨3/4,by norm_num⟩
  have hst : γ s≠γ t := by
    intro he
    rcases hcollision s t he with hh | hh | hh
    · have h := congrArg Subtype.val hh; norm_num [s,t] at h
    · have h := congrArg Subtype.val hh.1; norm_num [s] at h
    · have h := congrArg Subtype.val hh.1; norm_num [s] at h
  have hbaseNe (q : Interval) (hq : 0<q ∧ q<1) : γ 0≠γ q := by
    intro he
    rcases hcollision 0 q he with hh | hh | hh
    · exact (ne_of_gt hq.1) hh.symm
    · exact (ne_of_lt hq.2) hh.2
    · have h := congrArg Subtype.val hh.1; norm_num at h
  obtain ⟨R,T,hRT,c,hc,hcR,hc0,hc1,r,hr0,hr1,hcr⟩ := actual_jordan_point_interior_arc
    hC (mem_range_self s) (mem_range_self t) hst (mem_range_self 0)
    (hbaseNe s (by change (0:ℝ)<1/4 ∧ (1/4:ℝ)<1; norm_num))
    (hbaseNe t (by change (0:ℝ)<3/4 ∧ (3/4:ℝ)<1; norm_num))
  let f : C(Interval,S) := ⟨fun q => ((M.puncturedPlane p).symm (c q)).val,
    continuous_subtype_val.comp ((M.puncturedPlane p).symm.continuous.comp c.continuous)⟩
  have hf : IsEmbedding f := by
    apply (f.continuous.isClosedEmbedding _).isEmbedding
    intro u v he
    have hh : (M.puncturedPlane p).symm (c u)=(M.puncturedPlane p).symm (c v) := Subtype.ext he
    exact hc.injective ((M.puncturedPlane p).symm.injective hh)
  have hpoint (u q : Interval) (he : c u=γ q) : f u=a.val.map q := by
    change ((M.puncturedPlane p).symm (c u)).val=a.val.map q
    rw [he,hγ]
    exact congrArg Subtype.val ((M.puncturedPlane p).symm_apply_apply _)
  have hfa : range f ⊆ a.val.image := by
    rintro _ ⟨u,rfl⟩
    have hcu : c u ∈ R := hcR ▸ mem_range_self u
    obtain ⟨q,hq⟩ := hRT.fst_subset hcu
    exact ⟨q,(hpoint u q hq.symm).symm⟩
  have hmarks (u : Interval) : f u ∈ (M.cover.branch : Set S) ↔ f u=a.val.map 0 := by
    constructor
    · intro hm
      obtain ⟨q,hq⟩ := hfa (mem_range_self u)
      rcases a.val.marked_only_at_ends q (hq ▸ hm) with rfl | rfl
      · exact hq.symm
      · exact hq.symm.trans ha.symm
    · intro he; exact he ▸ a.val.start_marked
  let inv : Plane → S := fun x => ((M.puncturedPlane p).symm x).val
  have hinv : Continuous inv := continuous_subtype_val.comp (M.puncturedPlane p).symm.continuous
  let Tail : Set S := inv '' T
  have hTcompact : IsCompact T := by
    obtain ⟨d,_,hdr,_,_⟩ := actual_plane_arc_interval_producer hRT.snd
    rw [←hdr]; exact isCompact_range d.continuous
  have hTail : IsClosed Tail := (hTcompact.image hinv).isClosed
  have hunion : a.val.image=range f ∪ Tail := by
    apply Subset.antisymm
    · rintro x ⟨q,hq⟩
      have hqC : γ q ∈ R ∪ T := hRT.union_eq ▸ mem_range_self q
      rcases hqC with hqR | hqT
      · obtain ⟨u,hu⟩ := hcR.symm ▸ hqR
        exact Or.inl ⟨u,(hpoint u q hu).trans hq⟩
      · apply Or.inr
        refine ⟨γ q,hqT,?_⟩
        change ((M.puncturedPlane p).symm (γ q)).val=x
        rw [hγ]
        exact (congrArg Subtype.val ((M.puncturedPlane p).symm_apply_apply _)).trans hq
    · rintro x (hx | hx)
      · exact hfa hx
      · obtain ⟨q,hq,rfl⟩ := hx
        obtain ⟨u,hu⟩ := hRT.snd_subset hq
        refine ⟨u,?_⟩
        change a.val.map u=((M.puncturedPlane p).symm q).val
        rw [←hu,hγ]
        simp only [Homeomorph.symm_apply_apply]
  have hinter : range f ∩ Tail={f 0,f 1} := by
    apply Subset.antisymm
    · rintro x ⟨⟨u,rfl⟩,q,hq,he⟩
      have hcq : c u=q := (M.puncturedPlane p).symm.injective (Subtype.ext he.symm)
      have hcuR : c u ∈ R := hcR ▸ mem_range_self u
      have hcuEnd : c u ∈ ({γ s,γ t}:Set Plane) := hRT.inter_eq ▸ ⟨hcuR,hcq.symm ▸ hq⟩
      rcases hcuEnd with hcu | hcu
      · exact Or.inl ((hpoint u s hcu).trans (hpoint 0 s hc0).symm)
      · exact Or.inr (mem_singleton_iff.mpr ((hpoint u t (mem_singleton_iff.mp hcu)).trans
          (hpoint 1 t hc1).symm))
    · apply pair_subset
      · refine ⟨mem_range_self 0,γ s,hRT.snd.left_mem,?_⟩
        change ((M.puncturedPlane p).symm (γ s)).val=f 0
        exact congrArg (fun z => ((M.puncturedPlane p).symm z).val) hc0.symm
      · refine ⟨mem_range_self 1,γ t,hRT.snd.right_mem,?_⟩
        change ((M.puncturedPlane p).symm (γ t)).val=f 1
        exact congrArg (fun z => ((M.puncturedPlane p).symm z).val) hc1.symm
  have hfr : f r=a.val.map 0 := hpoint r 0 hcr
  have hbaseOff : a.val.map 0 ∉ Tail := by
    intro hh
    have he : f r ∈ ({f 0,f 1}:Set S) := hinter ▸ ⟨mem_range_self r,hfr.symm ▸ hh⟩
    rcases he with he | he
    · exact (ne_of_gt hr0) (hf.injective he)
    · exact (ne_of_lt hr1) (hf.injective (mem_singleton_iff.mp he))
  exact ⟨f,hf,hfa,hpoint 0 s hc0,hpoint 1 t hc1,hmarks,Tail,hTail,hunion,hinter,hbaseOff,r,hr0,hr1,hfr⟩
end CurveComplex.HyperellipticModel
