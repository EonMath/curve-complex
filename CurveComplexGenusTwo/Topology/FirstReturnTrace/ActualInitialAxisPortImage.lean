import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualInitialPortSubarc
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualArcPrefixInduction
namespace CurveComplex
open Set Topology Schoenflies
/-- An actual initial source subarc lying on a positive chart axis occupies
exactly the segment from its endpoint to its selected port. Scalar strict
monotonicity is derived from the actual embeddings. -/
theorem source_initial_axis_port_exact_image
    {S : Type} [TopologicalSpace S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (E : OpenPartialHomeomorph S Plane) (u : Interval) (hu : 0<(u:ℝ))
    (hsource : ∀ t : Interval, t≤u → f t ∈ E.source)
    (hzero : E (f 0)=0)
    (haxis : ∀ t : Interval, t≤u → E (f t) 0=0)
    (hport : 0<E (f u) 1) :
    f '' Set.Icc (0:Interval) u =
      {x : S | x ∈ E.source ∧ E x 0=0 ∧ 0≤E x 1 ∧ E x 1≤E (f u) 1} ∧
      ∀ t : Interval, f t ∈ E.source → E (f t) 0=0 →
        0≤E (f t) 1 → E (f t) 1≤E (f u) 1 → t≤u := by
  have h0u : (0:ℝ)<(u:ℝ) := hu
  obtain ⟨q,hq,hq0,hq1,hqrange,hqval⟩ := source_affine_subinterval 0 u h0u
  have hqs (s : Interval) : f (q s) ∈ E.source :=
    hsource (q s) ((hqrange ▸ Set.mem_range_self s).2)
  have hqa (s : Interval) : E (f (q s)) 0=0 :=
    haxis (q s) ((hqrange ▸ Set.mem_range_self s).2)
  let z : C(Interval,ℝ) := ⟨fun s => E (f (q s)) 1,by
    apply continuous_iff_continuousAt.mpr
    intro s
    have heval : Continuous (fun y : Plane => y 1) := by fun_prop
    have hc : ContinuousAt (fun t => E (f (q t))) s :=
      (E.continuousAt (hqs s)).comp (f := fun t => f (q t))
        (f.continuous.comp q.continuous).continuousAt
    exact heval.continuousAt.comp hc⟩
  have hz0 : z 0=0 := by change E (f (q 0)) 1=0; rw [hq0,hzero]; rfl
  have hz1 : z 1=E (f u) 1 := by change E (f (q 1)) 1=_; rw [hq1]
  have hzi : Function.Injective z := by
    intro s t he
    apply hq.injective
    apply hf.injective
    apply E.injOn (hqs s) (hqs t)
    ext j
    fin_cases j
    · exact (hqa s).trans (hqa t).symm
    · exact he
  have hzm : StrictMono z := by
    rcases z.continuous.strictMono_of_inj_boundedOrder' hzi with hm | hm
    · exact hm
    · have hh := hm (by norm_num : (0:Interval)<1)
      rw [hz0,hz1] at hh
      linarith
  have hI : Set.Icc (0:Interval) 1=Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact ⟨t.property.1,t.property.2⟩
  have hzrange : Set.range z=Set.Icc 0 (E (f u) 1) := by
    rw [← Set.image_univ,hI.symm,
      z.continuous.continuousOn.image_Icc_of_monotoneOn (by norm_num : (0:Interval)≤1)
        (hzm.monotone.monotoneOn _),hz0,hz1]
  have himage : f '' Set.Icc (0:Interval) u =
      {x : S | x ∈ E.source ∧ E x 0=0 ∧ 0≤E x 1 ∧ E x 1≤E (f u) 1} := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      obtain ⟨s,hs⟩ := hqrange.symm ▸ ht
      have hzmem : z s ∈ Set.Icc 0 (E (f u) 1) := hzrange ▸ Set.mem_range_self s
      exact ⟨hsource t ht.2,haxis t ht.2,by simpa [z,hs] using hzmem.1,by simpa [z,hs] using hzmem.2⟩
    · rintro ⟨hx,hx0,hxlo,hxhi⟩
      obtain ⟨s,hs⟩ := hzrange.symm ▸ (show E x 1 ∈ Set.Icc 0 (E (f u) 1) from ⟨hxlo,hxhi⟩)
      refine ⟨q s,hqrange ▸ Set.mem_range_self s,?_⟩
      apply E.injOn (hqs s) hx
      ext j
      fin_cases j
      · exact (hqa s).trans hx0.symm
      · exact hs
  refine ⟨himage,?_⟩
  intro t htE ht0 htlo hthi
  have htmem : f t ∈ f '' Set.Icc (0:Interval) u :=
    himage.symm ▸ (show f t ∈ {x : S | x ∈ E.source ∧ E x 0=0 ∧ 0≤E x 1 ∧ E x 1≤E (f u) 1} from ⟨htE,ht0,htlo,hthi⟩)
  obtain ⟨s,hs,hst⟩ := htmem
  exact hf.injective hst ▸ hs.2
end CurveComplex
#print axioms CurveComplex.source_initial_axis_port_exact_image
