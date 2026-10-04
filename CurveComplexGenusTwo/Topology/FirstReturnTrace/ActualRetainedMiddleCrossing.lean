import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualHorizontalSubarcCrossing
namespace CurveComplex
open Set Topology Schoenflies

theorem source_budget_retained_middle_crossing
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} {D : SourceFirstReturnBoundary a b}
    {B : SourceTwoSurgeryBranches D} {i : Bool}
    (P : SourceFirstReturnBudgetTracks D B i) (d : Curve S) (hd : d.image=P.trace)
    (p : source_surgery_retained_crossings B i) :
    CrossesAt a d (P.F.M (P.F.θR p,P.caps.z)) := by
  let θ : Interval := P.F.θR p
  have hports := source_retained_parameters_strictly_between_closing_ports D B i P.F p
  let ε : ℝ := min (P.F.ηR p/2)
    (min (((θ:ℝ)-(P.F.θg false:ℝ))/2) (((P.F.θg true:ℝ)-(θ:ℝ))/2))
  have hε : 0<ε := lt_min (by positivity [(P.F.retained_positive p).2])
    (lt_min (by dsimp [θ]; linarith [hports.1]) (by dsimp [θ]; linarith [hports.2]))
  have hεη : ε<P.F.ηR p := lt_of_le_of_lt (min_le_left _ _) (by linarith [(P.F.retained_positive p).2])
  have hεleft : ε≤((θ:ℝ)-(P.F.θg false:ℝ))/2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hεright : ε≤((P.F.θg true:ℝ)-(θ:ℝ))/2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hα0 : 0≤(θ:ℝ)-ε := by linarith [(P.F.θg false).property.1]
  have hα1 : (θ:ℝ)-ε≤1 := by linarith [θ.property.2]
  have hβ0 : 0≤(θ:ℝ)+ε := by linarith [θ.property.1]
  have hβ1 : (θ:ℝ)+ε≤1 := by linarith [(P.F.θg true).property.2]
  let α : Interval := ⟨(θ:ℝ)-ε,⟨hα0,hα1⟩⟩
  let β : Interval := ⟨(θ:ℝ)+ε,⟨hβ0,hβ1⟩⟩
  have hαβ : (α:ℝ)<β := by dsimp [α,β]; linarith
  obtain ⟨q,hq,hq0,hq1,hqrange,hqval⟩ := source_affine_subinterval α β hαβ
  have hqbounds (u : Interval) : α≤q u ∧ q u≤β :=
    by
      have hh : q u ∈ Set.Icc α β := hqrange ▸ Set.mem_range_self u
      exact hh
  have hqwindow (u : Interval) : |(q u:ℝ)-(P.F.θR p:ℝ)|<P.F.ηR p := by
    rw [abs_lt]
    have hh := hqbounds u
    change (θ:ℝ)-ε≤(q u:ℝ) ∧ (q u:ℝ)≤(θ:ℝ)+ε at hh
    change -P.F.ηR p < (q u:ℝ)-(θ:ℝ) ∧ (q u:ℝ)-(θ:ℝ)<P.F.ηR p
    constructor <;> linarith [hh.1,hh.2]
  have hqports (u : Interval) : q u ∈ Set.Icc (P.F.θg false) (P.F.θg true) := by
    have hh := hqbounds u
    change (θ:ℝ)-ε≤(q u:ℝ) ∧ (q u:ℝ)≤(θ:ℝ)+ε at hh
    change (P.F.θg false:ℝ)≤(q u:ℝ) ∧ (q u:ℝ)≤(P.F.θg true:ℝ)
    constructor <;> linarith [hh.1,hh.2]
  have hθrange : θ ∈ Set.range q := by
    rw [hqrange]
    change (θ:ℝ)-ε≤(θ:ℝ) ∧ (θ:ℝ)≤(θ:ℝ)+ε
    constructor <;> linarith
  obtain ⟨t,ht⟩ := hθrange
  have ht0 : 0<(t:ℝ) := by
    apply lt_of_le_of_ne t.property.1
    intro he
    have htzero : t=0 := Subtype.ext he.symm
    have hh := htzero ▸ ht
    rw [hq0] at hh
    have hv := congrArg Subtype.val hh
    change (θ:ℝ)-ε=(θ:ℝ) at hv
    linarith
  have ht1 : (t:ℝ)<1 := by
    apply lt_of_le_of_ne t.property.2
    intro he
    have htone : t=1 := Subtype.ext he
    have hh := htone ▸ ht
    rw [hq1] at hh
    have hv := congrArg Subtype.val hh
    change (θ:ℝ)+ε=(θ:ℝ) at hv
    linarith
  let f : C(Interval,S) := ⟨fun u=>P.F.M (q u,P.caps.z),
    P.F.closing_embedding.continuous.comp (q.continuous.prodMk continuous_const)⟩
  have hf : IsEmbedding f := P.F.closing_embedding.comp
    ((isEmbedding_prodMkLeft P.caps.z).comp hq)
  have hsub : Set.range f ⊆ d.image := by
    rw [hd]
    rintro x ⟨u,rfl⟩
    exact Or.inl (Or.inl (Or.inr ⟨q u,hqports u,rfl⟩))
  have hsource (u) : f u ∈ (P.F.ER p).source := (P.F.retained_framing p (q u) P.caps.z (hqwindow u)).1
  have hflat (u) : P.F.ER p (f u) 1=P.F.γ p*(P.caps.z:ℝ) :=
    congrArg (fun v : Plane=>v 1) (P.F.retained_framing p (q u) P.caps.z (hqwindow u)).2
  have hp0 : P.F.ER p (f t) 0=0 := by
    have hh := congrArg (fun v : Plane=>v 0) (P.F.retained_framing p (q t) P.caps.z (hqwindow t)).2
    change P.F.ER p (f t) 0=P.F.ER p (B.closing i (q t)) 0 at hh
    rw [ht,P.F.θR_center,(P.F.retained_point p).2] at hh
    exact hh
  have hc := source_horizontal_subarc_crossing S a d f hf hsub t ht0 ht1
    (P.F.ER p) hsource (P.F.γ p*(P.caps.z:ℝ)) hflat hp0 (P.F.retained_target_axis p)
  change CrossesAt a d (P.F.M (q t,P.caps.z)) at hc
  rw [ht] at hc
  exact hc
end CurveComplex
#print axioms CurveComplex.source_budget_retained_middle_crossing
