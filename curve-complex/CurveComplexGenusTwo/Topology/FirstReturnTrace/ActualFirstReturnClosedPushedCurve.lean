import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnGlobalPortIncidence
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualClosedTrackAttachment
namespace CurveComplex
open Set Topology Schoenflies
/-- Construct an ACTUAL embedded closed pushed Curve with the complete
strictly reduced target budget and current budget <=1. All global incidences
come from the source geometry; no track incidence or count is assumed. -/
theorem source_first_return_actual_closed_pushed_curve
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ P : SourceFirstReturnBudgetTracks D B i, ∃ d : Curve S,
      d.image=P.trace ∧ (d.image ∩ a.image).Finite ∧ (d.image ∩ b.image).Finite ∧
      (d.image ∩ a.image).ncard≤(source_surgery_retained_crossings B i).ncard+1 ∧
      (d.image ∩ b.image).ncard≤1 ∧ (d.image ∩ a.image).ncard<ht.1.toFinset.card := by
  classical
  obtain ⟨P,hdis,hfirst,hclosing⟩ := source_first_return_global_port_incidence S D B ht i
  obtain ⟨qf,hqf,hqf0,hqf1,hqfrange,hqfval⟩ :=
    source_affine_subinterval (P.F.θf false) (P.F.θf true) P.F.first_ports_order
  obtain ⟨qg,hqg,hqg0,hqg1,hqgrange,hqgval⟩ :=
    source_affine_subinterval (P.F.θg false) (P.F.θg true) P.F.closing_ports_order
  let f : C(Interval,S) := ⟨fun t=>P.F.N (qf t,P.caps.w),P.F.first_embedding.continuous.comp (qf.continuous.prodMk continuous_const)⟩
  let g : C(Interval,S) := ⟨fun t=>P.F.M (qg t,P.caps.z),P.F.closing_embedding.continuous.comp (qg.continuous.prodMk continuous_const)⟩
  have hf : IsEmbedding f := P.F.first_embedding.comp ((isEmbedding_prodMkLeft P.caps.w).comp hqf)
  have hg : IsEmbedding g := P.F.closing_embedding.comp ((isEmbedding_prodMkLeft P.caps.z).comp hqg)
  have hfrange : Set.range f=(fun u=>P.F.N (u,P.caps.w)) '' Set.Icc (P.F.θf false) (P.F.θf true) := by
    change Set.range ((fun u=>P.F.N (u,P.caps.w)) ∘ qf)=_
    rw [Set.range_comp,hqfrange]
  have hgrange : Set.range g=(fun u=>P.F.M (u,P.caps.z)) '' Set.Icc (P.F.θg false) (P.F.θg true) := by
    change Set.range ((fun u=>P.F.M (u,P.caps.z)) ∘ qg)=_
    rw [Set.range_comp,hqgrange]
  have hf0 : f 0=P.F.N (P.F.θf false,P.caps.w) := by change P.F.N (qf 0,P.caps.w)=_; rw [hqf0]
  have hf1 : f 1=P.F.N (P.F.θf true,P.caps.w) := by change P.F.N (qf 1,P.caps.w)=_; rw [hqf1]
  have hg0 : g 0=P.F.M (P.F.θg false,P.caps.z) := by change P.F.M (qg 0,P.caps.z)=_; rw [hqg0]
  have hg1 : g 1=P.F.M (P.F.θg true,P.caps.z) := by change P.F.M (qg 1,P.caps.z)=_; rw [hqg1]
  have hfmeet (k : Bool) : Set.range (P.caps.C k) ∩ Set.range f={P.F.N (P.F.θf k,P.caps.w)} := by
    ext x
    constructor
    · rintro ⟨hx,hxf⟩
      obtain ⟨u,hu,he⟩ := hfrange ▸ hxf
      change P.F.N (u,P.caps.w)=x at he
      have hue := (hfirst k u hu).mp (by rw [he]; exact hx)
      exact he.symm.trans (by rw [hue])
    · intro hx
      have he : x=P.F.N (P.F.θf k,P.caps.w) := hx
      rw [he]
      refine ⟨⟨0,P.caps.first_port k⟩,?_⟩
      rw [hfrange]
      refine ⟨P.F.θf k,?_,rfl⟩
      cases k
      · exact ⟨le_rfl,P.F.first_ports_order.le⟩
      · exact ⟨P.F.first_ports_order.le,le_rfl⟩
  have hgmeet (k : Bool) : Set.range (P.caps.C k) ∩ Set.range g={P.F.M (P.F.θg k,P.caps.z)} := by
    ext x
    constructor
    · rintro ⟨hx,hxg⟩
      obtain ⟨u,hu,he⟩ := hgrange ▸ hxg
      change P.F.M (u,P.caps.z)=x at he
      have hue := (hclosing k u hu).mp (by rw [he]; exact hx)
      exact he.symm.trans (by rw [hue])
    · intro hx
      have he : x=P.F.M (P.F.θg k,P.caps.z) := hx
      rw [he]
      refine ⟨⟨1,P.caps.closing_port k⟩,?_⟩
      rw [hgrange]
      refine ⟨P.F.θg k,?_,rfl⟩
      cases k
      · exact ⟨le_rfl,P.F.closing_ports_order.le⟩
      · exact ⟨P.F.closing_ports_order.le,le_rfl⟩
  have hfg : Disjoint (Set.range f) (Set.range g) := hdis.mono
    (by rintro x ⟨t,rfl⟩; exact ⟨(qf t,P.caps.w),⟨hqfrange ▸ Set.mem_range_self t,Set.mem_univ _⟩,rfl⟩)
    (by rintro x ⟨t,rfl⟩; exact ⟨(qg t,P.caps.z),⟨hqgrange ▸ Set.mem_range_self t,Set.mem_univ _⟩,rfl⟩)
  obtain ⟨d,hd⟩ := source_closed_curve_of_tracks_and_connectors f g (P.caps.C false) (P.caps.C true)
    hf hg (P.caps.embedding false) (P.caps.embedding true)
    ((P.caps.first_port false).trans hf0.symm) ((P.caps.closing_port false).trans hg0.symm)
    ((P.caps.first_port true).trans hf1.symm) ((P.caps.closing_port true).trans hg1.symm)
    (by rw [hfmeet,hf0]) (by rw [Set.inter_comm,hfmeet,hf1])
    (by rw [hgmeet,hg0]) (by rw [hgmeet,hg1]) hfg P.caps.caps_disjoint
  have htrace : d.image=P.trace := by
    rw [hd,hfrange,hgrange]
    ext x
    simp only [SourceFirstReturnBudgetTracks.trace,Set.mem_union]
    tauto
  exact ⟨P,d,htrace,htrace ▸ source_first_return_whole_trace_budget D B ht i P⟩
end CurveComplex
#print axioms CurveComplex.source_first_return_actual_closed_pushed_curve
