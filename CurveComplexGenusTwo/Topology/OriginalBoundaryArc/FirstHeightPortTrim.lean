import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.Plane
import Mathlib
namespace CurveComplex
open Set
set_option maxHeartbeats 2000000

/-- Trim an ACTUAL positive embedded half-port at its first common height.
The complete surviving clock is literal, and every noncorner point is
strictly below the height, which will prove corner-only horizontal overlaps. -/
theorem actual_positive_port_first_height
    (P : C(Interval,Schoenflies.Plane)) (hP : Topology.IsEmbedding P)
    (h0 : P 0 1 = 0) (hpositive : ∀ t : Interval, 0 < (t:ℝ) → 0 < P t 1)
    (δ : ℝ) (hδ : 0 < δ) (hδP : δ < P 1 1) :
    ∃ τ : Interval, 0 < (τ:ℝ) ∧
    ∃ E : C(Interval,Schoenflies.Plane), Topology.IsEmbedding E ∧
      (∀ t, E t = P ⟨(τ:ℝ)*(t:ℝ),by constructor <;>
        nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩) ∧
      E 0 = P 0 ∧ E 1 1 = δ ∧
      (∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) < 1 → 0 < E t 1 ∧ E t 1 < δ) ∧
      (∀ t : Interval, E t 1 = 0 ↔ t=0) ∧
      (∀ t : Interval, E t 1 = δ ↔ t=1) := by
  let f : Interval → ℝ := fun t => P t 1
  have hfc : Continuous f := by dsimp [f]; fun_prop
  let K : Set Interval := {t | δ ≤ f t}
  have hKc : IsCompact K := (isClosed_le continuous_const hfc).isCompact
  have hKne : K.Nonempty := ⟨1,hδP.le⟩
  obtain ⟨τ,hτ,hmin⟩ := hKc.exists_isMinOn hKne continuous_id.continuousOn
  have hτ0 : 0 < (τ:ℝ) := by
    have htne : τ≠0 := by
      intro ht
      subst τ
      change δ ≤ P 0 1 at hτ
      rw [h0] at hτ
      linarith
    exact lt_of_le_of_ne τ.property.1 (fun ht => htne (Subtype.ext ht.symm))
  have hbefore (s : Interval) (hs : s<τ) : f s < δ := by
    by_contra hn
    have hsK : s∈K := le_of_not_gt hn
    exact (not_le_of_gt hs) (hmin hsK)
  have hτheight : f τ=δ := by
    have hz : f 0 ≤ δ := by change P 0 1 ≤ δ; rw [h0]; exact hδ.le
    obtain ⟨s,hs,hfs⟩ := intermediate_value_Icc (show (0:Interval)≤τ from τ.property.1)
      hfc.continuousOn ⟨hz,hτ⟩
    have hsK : s∈K := by change δ≤f s; rw [hfs]
    have heq : s=τ := le_antisymm hs.2 (hmin hsK)
    simpa [heq] using hfs
  let q : C(Interval,Interval) := ⟨fun t => ⟨(τ:ℝ)*(t:ℝ),by constructor <;>
    nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,by fun_prop⟩
  have hqi : Function.Injective q := by
    intro t u he
    apply Subtype.ext
    exact mul_left_cancel₀ hτ0.ne' (congrArg Subtype.val he)
  have hq : Topology.IsEmbedding q := (q.continuous.isClosedEmbedding hqi).isEmbedding
  let E := P.comp q
  have hq0 : q 0=0 := Subtype.ext (by change (τ:ℝ)*0=0; ring)
  have hq1 : q 1=τ := Subtype.ext (by change (τ:ℝ)*1=(τ:ℝ); ring)
  have he0 : E 0=P 0 := by change P (q 0)=P 0; rw [hq0]
  have he1 : E 1 1=δ := by change f (q 1)=δ; rw [hq1]; exact hτheight
  have hint (t : Interval) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) :
      0<E t 1 ∧ E t 1<δ := by
    refine ⟨hpositive (q t) (mul_pos hτ0 ht0),hbefore (q t) ?_⟩
    change (τ:ℝ)*(t:ℝ)<(τ:ℝ)
    nlinarith
  refine ⟨τ,hτ0,E,hP.comp hq,fun _ => rfl,he0,he1,hint,?_,?_⟩
  · intro t
    constructor
    · intro ht
      by_contra htn
      have htpos : 0<(t:ℝ) := lt_of_le_of_ne t.property.1
        (fun he => htn (Subtype.ext he.symm))
      have hh := hpositive (q t) (mul_pos hτ0 htpos)
      change 0<E t 1 at hh
      linarith
    · rintro rfl
      rw [he0,h0]
  · intro t
    constructor
    · intro ht
      by_contra htn
      have htlt : (t:ℝ)<1 := lt_of_le_of_ne t.property.2
        (fun he => htn (Subtype.ext he))
      have hh := hbefore (q t) (by change (τ:ℝ)*(t:ℝ)<(τ:ℝ); nlinarith)
      change E t 1<δ at hh
      linarith
    · rintro rfl
      exact he1
end CurveComplex
