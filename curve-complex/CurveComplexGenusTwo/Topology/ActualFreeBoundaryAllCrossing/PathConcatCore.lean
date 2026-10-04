import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.W81FiniteEventLiftFamily
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryTracks

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology
open CurveComplex.BranchedDoubleCover

noncomputable def halfClock (t : Interval) : Interval :=
  ⟨t.val / 2, by constructor <;> linarith [t.property.1,t.property.2]⟩
noncomputable def laterClock (t : Interval) : Interval :=
  ⟨(1 + t.val) / 2, by constructor <;> linarith [t.property.1,t.property.2]⟩

lemma trans_halfClock {X : Type} [TopologicalSpace X] {x y z : X}
    (P : Path x y) (Q : Path y z) (t : Interval) :
    (P.trans Q) (halfClock t) = P t := by
  rw [Path.trans_apply,dite_eq_left (show (halfClock t).val ≤ 1/2 by
    dsimp [halfClock]; linarith [t.property.2])]
  congr 1
  apply Subtype.ext
  dsimp [halfClock]
  ring

lemma trans_laterClock {X : Type} [TopologicalSpace X] {x y z : X}
    (P : Path x y) (Q : Path y z) (t : Interval) :
    (P.trans Q) (laterClock t) = Q t := by
  by_cases ht : t = 0
  · subst t
    have he : laterClock 0 = halfClock 1 := by apply Subtype.ext; norm_num [laterClock,halfClock]
    rw [he,trans_halfClock,P.target,Q.source]
  · have htpos : 0 < t.val := lt_of_le_of_ne t.property.1 (by
      intro he; apply ht; exact Subtype.ext he.symm)
    rw [Path.trans_apply,dite_eq_right (show ¬ (laterClock t).val ≤ 1/2 by
      dsimp [laterClock]; linarith)]
    congr 1
    apply Subtype.ext
    dsimp [laterClock]
    ring

lemma trans_parameter_cases {X : Type} [TopologicalSpace X] {x y z : X}
    (P : Path x y) (Q : Path y z) (t : Interval) :
    (∃ u, t = halfClock u ∧ (P.trans Q) t = P u) ∨
    (∃ u, t = laterClock u ∧ (P.trans Q) t = Q u) := by
  by_cases ht : t.val ≤ 1/2
  · let u : Interval := ⟨2*t.val,by constructor <;> linarith [t.property.1]⟩
    have he : t = halfClock u := by apply Subtype.ext; dsimp [halfClock,u]; ring
    exact Or.inl ⟨u,he,he ▸ trans_halfClock P Q u⟩
  · let u : Interval := ⟨2*t.val-1,by constructor <;> linarith [t.property.2]⟩
    have he : t = laterClock u := by apply Subtype.ext; dsimp [laterClock,u]; ring
    exact Or.inr ⟨u,he,he ▸ trans_laterClock P Q u⟩

lemma finite_trans_events {X : Type} [TopologicalSpace X]
    (B : Set X) {x y z : X} (P : Path x y) (Q : Path y z)
    (hP : (P ⁻¹' B).Finite) (hQ : (Q ⁻¹' B).Finite) :
    ((P.trans Q) ⁻¹' B).Finite := by
  apply ((hP.image halfClock).union (hQ.image laterClock)).subset
  intro t ht
  rcases trans_parameter_cases P Q t with ⟨u,he,hu⟩ | ⟨u,he,hu⟩
  · exact Or.inl ⟨u,by simpa only [Set.mem_preimage,hu] using ht,he.symm⟩
  · exact Or.inr ⟨u,by simpa only [Set.mem_preimage,hu] using ht,he.symm⟩

lemma finite_symm_events {X : Type} [TopologicalSpace X]
    (B : Set X) {x y : X} (P : Path x y) (hP : (P ⁻¹' B).Finite) :
    (P.symm ⁻¹' B).Finite := by
  change (unitInterval.symm ⁻¹' (P ⁻¹' B)).Finite
  exact hP.preimage unitInterval.symm_bijective.injective.injOn

/-- Local switching along a continuous path, in the exact quantifier order of
the finite separating-family consumer. -/
def TrackSwitch {X : Type} [TopologicalSpace X]
    (Γ : C(Interval,X)) (A U V : Set X) : Prop :=
  ∀ t : Interval, t ∈ Ioo (0 : Interval) 1 → Γ t ∈ A →
    ∀ l r : Interval, l < t → t < r →
      ∃ u v : Interval, l < u ∧ u < t ∧ t < v ∧ v < r ∧
        ((Γ u ∈ U ∧ Γ v ∈ V) ∨ (Γ u ∈ V ∧ Γ v ∈ U))

lemma trackSwitch_symm {X : Type} [TopologicalSpace X]
    (A U V : Set X) {x y : X} (P : Path x y)
    (hP : TrackSwitch P.toContinuousMap A U V) :
    TrackSwitch P.symm.toContinuousMap A U V := by
  intro t ht hAt l r hlt htr
  have hst : unitInterval.symm t ∈ Ioo (0 : Interval) 1 := by
    constructor
    · change (0:ℝ) < 1-t.val
      have h := ht.2; change t.val < 1 at h; linarith
    · change 1-t.val < (1:ℝ)
      have h := ht.1; change 0 < t.val at h; linarith
  have hr : unitInterval.symm r < unitInterval.symm t := by
    change 1-r.val < 1-t.val
    change t.val < r.val at htr
    linarith
  have hl : unitInterval.symm t < unitInterval.symm l := by
    change 1-t.val < 1-l.val
    change l.val < t.val at hlt
    linarith
  obtain ⟨u,v,hru,hut,htv,hvl,hs⟩ := hP _ hst hAt _ _ hr hl
  refine ⟨unitInterval.symm v,unitInterval.symm u,?_,?_,?_,?_,?_⟩
  · change l.val < 1-v.val
    change v.val < 1-l.val at hvl
    linarith
  · change 1-v.val < t.val
    change 1-t.val < v.val at htv
    linarith
  · change t.val < 1-u.val
    change u.val < 1-t.val at hut
    linarith
  · change 1-u.val < r.val
    change 1-r.val < u.val at hru
    linarith
  · change ((P (unitInterval.symm (unitInterval.symm v)) ∈ U ∧
      P (unitInterval.symm (unitInterval.symm u)) ∈ V) ∨
      (P (unitInterval.symm (unitInterval.symm v)) ∈ V ∧
      P (unitInterval.symm (unitInterval.symm u)) ∈ U))
    simp only [unitInterval.symm_symm]
    exact hs.elim (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)

lemma trackSwitch_trans {X : Type} [TopologicalSpace X]
    (A U V : Set X) {x y z : X} (P : Path x y) (Q : Path y z)
    (hP : TrackSwitch P.toContinuousMap A U V)
    (hQ : TrackSwitch Q.toContinuousMap A U V) (hy : y ∉ A) :
    TrackSwitch (P.trans Q).toContinuousMap A U V := by
  intro t ht hAt l r hlt htr
  rcases trans_parameter_cases P Q t with ⟨s,rfl,hs⟩ | ⟨s,rfl,hs⟩
  · have hsA : P s ∈ A := hs ▸ hAt
    have hs0 : 0 < s.val := by
      have h := ht.1
      change 0 < s.val / 2 at h
      linarith
    have hs1 : s.val < 1 := lt_of_le_of_ne s.property.2 (by
      intro he
      have hes : s = 1 := Subtype.ext he
      exact hy (by simpa only [hes,P.target] using hsA))
    let l' : Interval := ⟨2*l.val,by
      have hh : l.val < s.val/2 := hlt
      constructor <;> linarith [l.property.1,s.property.2]⟩
    let r' : Interval := ⟨min 1 (2*r.val),by
      constructor
      · exact le_min (by norm_num) (by linarith [r.property.1])
      · exact min_le_left _ _⟩
    have hls : l' < s := by change 2*l.val < s.val; change l.val < s.val/2 at hlt; linarith
    have hsr : s < r' := by
      change s.val < min 1 (2*r.val)
      exact lt_min hs1 (by change s.val/2 < r.val at htr; linarith)
    obtain ⟨u,v,hlu,hus,hsv,hvr,hUV⟩ := hP s ⟨hs0,hs1⟩ hsA l' r' hls hsr
    refine ⟨halfClock u,halfClock v,?_,?_,?_,?_,?_⟩
    · change l.val < u.val/2
      change 2*l.val < u.val at hlu
      linarith
    · change u.val/2 < s.val/2
      change u.val < s.val at hus
      linarith
    · change s.val/2 < v.val/2
      change s.val < v.val at hsv
      linarith
    · change v.val/2 < r.val
      have hv : v.val < r'.val := hvr
      have hh := lt_of_lt_of_le hv (show r'.val ≤ 2*r.val from min_le_right _ _)
      linarith
    · simpa only [Path.coe_toContinuousMap,trans_halfClock] using hUV
  · have hsA : Q s ∈ A := hs ▸ hAt
    have hs0 : 0 < s.val := lt_of_le_of_ne s.property.1 (by
      intro he
      have hes : s = 0 := Subtype.ext he.symm
      exact hy (by simpa only [hes,Q.source] using hsA))
    have hs1 : s.val < 1 := by
      have h := ht.2
      change (1+s.val)/2 < 1 at h
      linarith
    let l' : Interval := ⟨max 0 (2*l.val-1),by
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (by linarith [l.property.2])⟩
    let r' : Interval := ⟨2*r.val-1,by
      have hh : (1+s.val)/2 < r.val := htr
      constructor <;> linarith [r.property.2,s.property.1]⟩
    have hls : l' < s := by
      change max 0 (2*l.val-1) < s.val
      exact max_lt hs0 (by change l.val < (1+s.val)/2 at hlt; linarith)
    have hsr : s < r' := by
      change s.val < 2*r.val-1
      change (1+s.val)/2 < r.val at htr
      linarith
    obtain ⟨u,v,hlu,hus,hsv,hvr,hUV⟩ := hQ s ⟨hs0,hs1⟩ hsA l' r' hls hsr
    refine ⟨laterClock u,laterClock v,?_,?_,?_,?_,?_⟩
    · change l.val < (1+u.val)/2
      have hh := lt_of_le_of_lt (show 2*l.val-1 ≤ l'.val from le_max_right _ _) hlu
      change 2*l.val-1 < u.val at hh
      linarith
    · change (1+u.val)/2 < (1+s.val)/2
      change u.val < s.val at hus
      linarith
    · change (1+s.val)/2 < (1+v.val)/2
      change s.val < v.val at hsv
      linarith
    · change (1+v.val)/2 < r.val
      change v.val < 2*r.val-1 at hvr
      linarith
    · simpa only [Path.coe_toContinuousMap,trans_laterClock] using hUV

end CoherentEndpointMotion.FreeBoundaryContactRepair
