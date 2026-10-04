import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.VerifiedCarrierComponents
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualWholeInteriorAxisChart
namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
theorem actual_marked_whole_local_vertical_trace
    (M : HyperellipticModel E S) [T2Space S] (c : EssentialMarkedArc M) (p : S)
      (hp : p ∈ arcInterior M c) (F : OpenPartialHomeomorph S Plane)
      (hpF : p ∈ F.source) (hFp : F p=0)
      (hFMarks : Disjoint F.source (M.cover.branch : Set S))
      (hline : ∀ x ∈ c.val.image ∩ F.source, F x 0=0) :
      ∃ G : OpenPartialHomeomorph S Plane, p ∈ G.source ∧ G p=0 ∧
        G.source ⊆ F.source ∧ (∀ x, G x=F x) ∧
        Disjoint G.source (M.cover.branch : Set S) ∧
        ∀ x ∈ G.source, x ∈ c.val.image ↔ G x 0=0 := by
  classical
  obtain ⟨q,hq⟩ := hp.1
  have hq0 : 0 < q.val := by
    by_contra hn
    have he : q=0 := Subtype.ext (le_antisymm (le_of_not_gt hn) q.property.1)
    exact hp.2 (hq ▸ (he ▸ c.val.start_marked))
  have hq1 : q.val < 1 := by
    by_contra hn
    have he : q=1 := Subtype.ext (le_antisymm q.property.2 (le_of_not_gt hn))
    exact hp.2 (hq ▸ (he ▸ c.val.end_marked))
  let l : ℝ := q.val/2
  let r : ℝ := (q.val+1)/2
  have hl : 0 < l := half_pos hq0
  have hr : r < 1 := by dsimp [r]; linarith
  have hlq : l < q.val := by dsimp [l]; linarith
  have hqr : q.val < r := by dsimp [r]; linarith
  have hlr : l < r := hlq.trans hqr
  let coreC : C(Interval,S) := ⟨fun t => c.val.map (Set.projIcc 0 1 zero_le_one (l+t.val*(r-l))),
    c.val.continuous.comp (continuous_projIcc.comp (by fun_prop))⟩
  have hθ (t : Interval) : l ≤ l+t.val*(r-l) ∧ l+t.val*(r-l) ≤ r := by
    constructor <;> nlinarith [t.property.1,t.property.2]
  have hθ01 (t : Interval) : l+t.val*(r-l) ∈ Icc (0:ℝ) 1 :=
    ⟨(hl.trans_le (hθ t).1).le,((hθ t).2.trans_lt hr).le⟩
  have hcoreE : IsEmbedding coreC := by
    apply (coreC.continuous.isClosedEmbedding ?_).isEmbedding
    intro t u he
    rcases c.val.injective_except_loop_closure _ _ he with he|he|he
    · have hh := congrArg Subtype.val he
      rw [Set.projIcc_of_mem zero_le_one (hθ01 t),Set.projIcc_of_mem zero_le_one (hθ01 u)] at hh
      apply Subtype.ext
      nlinarith [sub_pos.mpr hlr]
    · have hh := congrArg Subtype.val he.1
      rw [Set.projIcc_of_mem zero_le_one (hθ01 t)] at hh
      change l+t.val*(r-l)=0 at hh
      linarith [(hθ t).1]
    · have hh := congrArg Subtype.val he.1
      rw [Set.projIcc_of_mem zero_le_one (hθ01 t)] at hh
      change l+t.val*(r-l)=1 at hh
      linarith [(hθ t).2]
  let tails : Set S := c.val.map '' {t : Interval | t.val ≤ l ∨ r ≤ t.val}
  have hTailsCompact : IsCompact tails :=
    ((isClosed_le continuous_subtype_val continuous_const).union
      (isClosed_le continuous_const continuous_subtype_val)).isCompact.image c.val.continuous
  have hpTail : p ∉ tails := by
    rintro ⟨u,hu,he⟩
    rcases c.val.injective_except_loop_closure _ _ (he.trans hq.symm) with huq|huq|huq
    · subst u
      rcases hu with hu|hu <;> linarith
    · exact hp.2 (he ▸ (huq.1 ▸ c.val.start_marked))
    · exact hp.2 (he ▸ (huq.1 ▸ c.val.end_marked))
  let F' := F.restrOpen tailsᶜ hTailsCompact.isClosed.isOpen_compl
  have hpF' : p ∈ F'.source := ⟨hpF,hpTail⟩
  have hWholeCore (x : S) (hx : x ∈ F'.source) : x ∈ c.val.image ↔ x ∈ range coreC := by
    constructor
    · rintro ⟨u,hu⟩
      have hnot : ¬(u.val ≤ l ∨ r ≤ u.val) := fun hh => hx.2 ⟨u,hh,hu⟩
      have huL : l < u.val := lt_of_not_ge (fun hh => hnot (Or.inl hh))
      have huR : u.val < r := lt_of_not_ge (fun hh => hnot (Or.inr hh))
      let t : Interval := ⟨(u.val-l)/(r-l),(div_pos (sub_pos.mpr huL) (sub_pos.mpr hlr)).le,
        ((div_lt_one (sub_pos.mpr hlr)).mpr (by linarith)).le⟩
      refine ⟨t,?_⟩
      have he : l+t.val*(r-l)=u.val := by dsimp [t]; rw [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hlr))]; ring
      change c.val.map (Set.projIcc 0 1 zero_le_one (l+t.val*(r-l)))=x
      rw [he,Set.projIcc_of_mem zero_le_one u.property]
      exact hu
    · rintro ⟨t,rfl⟩
      exact Set.mem_range_self _
  let tq : Interval := ⟨(q.val-l)/(r-l), (div_pos (sub_pos.mpr hlq) (sub_pos.mpr hlr)).le,
    ((div_lt_one (sub_pos.mpr hlr)).mpr (by linarith)).le⟩
  have htq0 : 0 < tq.val := div_pos (sub_pos.mpr hlq) (sub_pos.mpr hlr)
  have htq1 : tq.val < 1 := (div_lt_one (sub_pos.mpr hlr)).mpr (by linarith)
  have htqp : coreC tq=p := by
    change c.val.map (Set.projIcc 0 1 zero_le_one (l+tq.val*(r-l)))=p
    have he : l+tq.val*(r-l)=q.val := by dsimp [tq]; rw [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hlr))]; ring
    rw [he,Set.projIcc_of_mem zero_le_one q.property]
    exact hq
  let swapPair : Plane ≃ₜ ℝ × ℝ := {
    toFun := fun z => (z 1,z 0)
    invFun := fun z => Plane.mk z.2 z.1
    left_inv := by intro z; ext i; fin_cases i <;> rfl
    right_inv := by intro z; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let EF := F'.trans swapPair.toOpenPartialHomeomorph
  have hEFSource : EF.source=F'.source := by simp [EF]
  obtain ⟨ε,hε,hεT,htrace⟩ := CurveComplex.actual_embedded_arc_local_chart_horizontal_trace
    coreC hcoreE tq htq0 htq1 EF (hEFSource.symm ▸ (htqp.symm ▸ hpF')) 0
    (fun x hx => hline x ⟨(hWholeCore x (hEFSource ▸ hx.2)).mpr hx.1,(hEFSource ▸ hx.2).1⟩)
  let O := EF.source ∩ EF ⁻¹' Metric.ball (EF p) ε
  have hO : IsOpen O := EF.isOpen_inter_preimage isOpen_ball
  let G := F'.restrOpen O hO
  have hpG : p ∈ G.source := ⟨hpF',hEFSource.symm ▸ hpF',by simp [hε]⟩
  refine ⟨G,hpG,hFp,fun x hx => hx.1.1,fun x => rfl,hFMarks.mono_left (fun x hx => hx.1.1),?_⟩
  intro x hx
  have ht := htrace x hx.2.1 (by simpa only [htqp,Set.mem_preimage,Metric.mem_ball] using hx.2.2)
  change (x ∈ range coreC ↔ F' x 0=0) at ht
  exact (hWholeCore x hx.1).trans ht
end CurveComplex.HyperellipticModel
