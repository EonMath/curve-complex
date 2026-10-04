import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopAllowedFiniteContactParameters
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual finite original crossings, including loop representatives, produce
an embedded affine central parameter window that captures EVERY crossing.
The original endpoint tails have no unmarked crossing. -/
theorem actual_loop_allowed_crossing_window
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (p : S) (hp : p ∈ ArcSurgery.crossings M a b) :
    ∃ ε : ℝ, 0<ε ∧ ε<1/2 ∧ ∃ φ : C(Interval,Interval),
      IsEmbedding φ ∧
      (∀ t, (φ t:ℝ)=ε+(1-2*ε)*(t:ℝ)) ∧
      (∀ t, 0<(φ t:ℝ) ∧ (φ t:ℝ)<1) ∧
      (∀ t, b.val.map t ∈ ArcSurgery.crossings M a b →
        ε<(t:ℝ) ∧ (t:ℝ)<1-ε ∧ ∃ s, φ s=t) ∧
      (∀ t : Interval, (t:ℝ)≤ε ∨ 1-ε≤(t:ℝ) →
        b.val.map t ∉ ArcSurgery.crossings M a b) := by
  classical
  let K : Set Interval := {t | b.val.map t ∈ ArcSurgery.crossings M a b}
  have hKfinite : K.Finite :=
    (actual_loop_allowed_all_contact_parameters_finite M a b hfinite).subset
      (fun _ ht => ht.1.1)
  have hKnonempty : K.Nonempty := by
    obtain ⟨t,ht⟩ := hp.2.1
    refine ⟨t,?_⟩
    change b.val.map t ∈ ArcSurgery.crossings M a b
    rw [ht]; exact hp
  obtain ⟨l,hl,hlmin⟩ := hKfinite.isCompact.exists_isLeast hKnonempty
  obtain ⟨u,hu,humax⟩ := hKfinite.isCompact.exists_isGreatest hKnonempty
  have hlpos : (0:ℝ)<l := by
    apply lt_of_le_of_ne l.property.1
    intro he
    have hh : l=(0:Interval) := Subtype.ext he.symm
    exact hl.2.2 (hh ▸ b.val.start_marked)
  have hult : (u:ℝ)<1 := by
    apply lt_of_le_of_ne u.property.2
    intro he
    have hh : u=(1:Interval) := Subtype.ext he
    exact hu.2.2 (hh ▸ b.val.end_marked)
  let ε : ℝ := min (l:ℝ) (1-(u:ℝ))/2
  have hεpos : 0<ε := by dsimp [ε]; positivity
  have hεhalf : ε<1/2 := by
    have hle : (l:ℝ)≤u := hlmin hu
    have hm₁ := min_le_left (l:ℝ) (1-(u:ℝ))
    have hm₂ := min_le_right (l:ℝ) (1-(u:ℝ))
    dsimp [ε]; linarith
  have hmargin (t : Interval) (ht : t ∈ K) : ε<(t:ℝ) ∧ (t:ℝ)<1-ε := by
    have hlo : (l:ℝ)≤t := hlmin ht
    have hhi : (t:ℝ)≤u := humax ht
    have hm₁ := min_le_left (l:ℝ) (1-(u:ℝ))
    have hm₂ := min_le_right (l:ℝ) (1-(u:ℝ))
    dsimp [ε]; constructor <;> linarith
  let φ : C(Interval,Interval) := {
    toFun := fun t => ⟨ε+(1-2*ε)*(t:ℝ),by
      constructor <;> nlinarith [t.property.1,t.property.2]⟩
    continuous_toFun := by fun_prop }
  have hφinj : Function.Injective φ := by
    intro s t he
    have hh := congrArg Subtype.val he
    change ε+(1-2*ε)*(s:ℝ)=ε+(1-2*ε)*(t:ℝ) at hh
    apply Subtype.ext
    nlinarith
  refine ⟨ε,hεpos,hεhalf,φ,(φ.continuous.isClosedEmbedding hφinj).isEmbedding,
    fun _ => rfl,?_,?_,?_⟩
  · intro t
    change 0<ε+(1-2*ε)*(t:ℝ) ∧ ε+(1-2*ε)*(t:ℝ)<1
    constructor <;> nlinarith [t.property.1,t.property.2]
  · intro t ht
    obtain ⟨hlo,hhi⟩ := hmargin t ht
    have hden : 0<1-2*ε := by linarith
    let s : Interval := ⟨((t:ℝ)-ε)/(1-2*ε),by
      constructor
      · exact div_nonneg (by linarith) hden.le
      · apply (div_le_one hden).mpr; linarith⟩
    refine ⟨hlo,hhi,s,Subtype.ext ?_⟩
    change ε+(1-2*ε)*(((t:ℝ)-ε)/(1-2*ε))=(t:ℝ)
    rw [←mul_div_assoc,mul_div_cancel_left₀ _ hden.ne']
    ring
  · intro t ht hc
    obtain ⟨hlo,hhi⟩ := hmargin t hc
    rcases ht with ht | ht <;> linarith
end CurveComplex.HyperellipticModel
