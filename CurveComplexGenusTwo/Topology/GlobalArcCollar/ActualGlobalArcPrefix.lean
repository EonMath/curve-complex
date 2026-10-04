import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualArcPrefixInduction
namespace CurveComplex
open Set Topology Schoenflies Metric

/-- Openness extends a chart-contained compact segment a little past its
internal right endpoint. This supplies the margin in the extension induction. -/
theorem source_chart_subarc_right_margin
    {S : Type} [TopologicalSpace S]
    (f : C(Interval,S)) (b c : Interval) (hbc : b ≤ c) (hc1 : (c:ℝ) < 1)
    (e : OpenPartialHomeomorph S Plane) (hchart : f '' Icc b c ⊆ e.source) :
    ∃ d : Interval, (c:ℝ) < d ∧ f '' Icc b d ⊆ e.source := by
  have hce : f c ∈ e.source := hchart ⟨c,⟨hbc,le_rfl⟩,rfl⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((e.open_source.preimage f.continuous).mem_nhds hce)
  let δ : ℝ := min (r/2) ((1-(c:ℝ))/2)
  have hδ : 0 < δ := lt_min (half_pos hr) (by linarith)
  have hδr : δ < r := by have hh := min_le_left (r/2) ((1-(c:ℝ))/2); dsimp [δ]; linarith
  have hδ1 : (c:ℝ)+δ ≤ 1 := by
    have hh := min_le_right (r/2) ((1-(c:ℝ))/2); dsimp [δ]; linarith
  let d : Interval := ⟨(c:ℝ)+δ,⟨by linarith [c.property.1],hδ1⟩⟩
  refine ⟨d,by change (c:ℝ) < (c:ℝ)+δ; linarith,?_⟩
  rintro x ⟨t,ht,rfl⟩
  by_cases htc : t ≤ c
  · exact hchart ⟨t,⟨ht.1,htc⟩,rfl⟩
  · apply hball
    rw [mem_ball,Subtype.dist_eq,Real.dist_eq,abs_of_nonneg (show 0 ≤ (t:ℝ)-(c:ℝ) by have hh : (c:ℝ) ≤ t := (lt_of_not_ge htc).le; linarith)]
    have htd : (t:ℝ) ≤ (c:ℝ)+δ := ht.2
    linarith

/-- Actual finite global assembly: successively extend the endpoint seed through
the atlas cover, deriving every shared seam inside the extension producer. -/
theorem source_whole_arc_prefix_strip
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (U : Set S) (hU : IsOpen U) (hfU : range f ⊆ U) :
    Nonempty (SourceArcPrefixStrip f U 1) := by
  classical
  obtain ⟨b,hb,hb1,hB⟩ := source_exists_initial_arc_prefix_strip f hf U hU hfU
  obtain ⟨q,hq,hq0,hq1,hqrange,hqval⟩ := source_affine_subinterval b 1 hb1
  let g : C(Interval,S) := f.comp q
  obtain ⟨n,hn,c,hc⟩ := position_interval_subdivision g
    (fun x : S => (chartAt Plane x).source)
    (fun x => (chartAt Plane x).open_source)
    (fun t => ⟨g t,mem_chart_source _ _⟩)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let s : ℕ → Interval := fun i => projIcc 0 1 zero_le_one ((i:ℝ)/n)
  let τ : ℕ → Interval := fun i => q (s i)
  have hs (i : ℕ) (hi : i ≤ n) : (s i:ℝ) = (i:ℝ)/n := by
    have himem : (i:ℝ)/n ∈ Icc (0:ℝ) 1 := ⟨by positivity,
      (div_le_one hnR).mpr (by exact_mod_cast hi)⟩
    exact congrArg Subtype.val (projIcc_of_mem zero_le_one himem)
  have hτ (i : ℕ) (hi : i ≤ n) : (τ i:ℝ) = (b:ℝ)+(1-(b:ℝ))*((i:ℝ)/n) := by
    change (q (s i):ℝ) = _
    rw [hqval,hs i hi]
    norm_num
  have hτ0 : τ 0 = b := by
    change q (s 0) = b
    have hs0 : s 0 = 0 := Subtype.ext (by rw [hs 0 (by omega)]; norm_num)
    rw [hs0,hq0]
  have hτn : τ n = 1 := by
    change q (s n) = 1
    have hsn : s n = 1 := Subtype.ext (by rw [hs n le_rfl,div_self hnR.ne']; rfl)
    rw [hsn,hq1]
  have hstep (i : ℕ) (hi : i < n) : (τ i:ℝ) < τ (i+1) := by
    rw [hτ i (by omega),hτ (i+1) (by omega)]
    have hmesh : (i:ℝ)/n < ((i+1:ℕ):ℝ)/n :=
      div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self i) hnR
    nlinarith
  have hchart (i : ℕ) (hi : i < n) : f '' Icc (τ i) (τ (i+1)) ⊆
      (chartAt Plane (c ⟨i,hi⟩)).source := by
    rintro x ⟨t,ht,rfl⟩
    have htb : b ≤ t := by
      have hh : b ≤ τ i := (hqrange ▸ mem_range_self (s i)).1
      exact hh.trans ht.1
    obtain ⟨u,hu⟩ := (hqrange.symm ▸ ⟨htb,t.property.2⟩ : t ∈ range q)
    have hulo : (i:ℝ)/n ≤ (u:ℝ) := by
      have hh : (τ i:ℝ) ≤ t := ht.1
      rw [hτ i (by omega),← hu,hqval] at hh
      norm_num at hh
      nlinarith
    have huhi : (u:ℝ) ≤ (i+1:ℝ)/n := by
      have hh : (t:ℝ) ≤ τ (i+1) := ht.2
      rw [hτ (i+1) (by omega),← hu,hqval] at hh
      norm_num at hh
      norm_num
      nlinarith
    have hh := hc ⟨i,hi⟩ u hulo huhi
    change f (q u) ∈ _ at hh
    rw [hu] at hh
    exact hh
  have hind : ∀ i : ℕ, i ≤ n → Nonempty (SourceArcPrefixStrip f U (τ i)) := by
    intro i
    induction i with
    | zero => intro _; rw [hτ0]; exact hB
    | succ i ih =>
      intro hi
      have hin : i < n := by omega
      obtain ⟨B⟩ := ih (by omega)
      let e := chartAt Plane (c ⟨i,hin⟩)
      by_cases heq : τ (i+1) = 1
      · exact source_extend_arc_prefix_strip f hf U hU hfU (τ i) (τ (i+1)) 1
          (hstep i hin) (by rw [heq]) (Or.inr rfl) B e (by simpa [heq] using hchart i hin)
      · have hc1 : (τ (i+1):ℝ) < 1 := lt_of_le_of_ne (τ (i+1)).property.2
          (fun h => heq (Subtype.ext h))
        obtain ⟨d,hcd,hdchart⟩ := source_chart_subarc_right_margin f
          (τ i) (τ (i+1)) (hstep i hin).le hc1 e (hchart i hin)
        exact source_extend_arc_prefix_strip f hf U hU hfU (τ i) (τ (i+1)) d
          (hstep i hin) hcd.le (Or.inl hcd) B e hdchart
  simpa only [hτn] using hind n le_rfl
end CurveComplex
#print axioms CurveComplex.source_chart_subarc_right_margin
#print axioms CurveComplex.source_whole_arc_prefix_strip
