import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.PathConcatCore

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology

/-- Select a mixed boundary/middle return from a clean return on the concatenated
track. The boundary-only exclusion and middle singleton property are explicit
geometric inputs, discharged by the source caller. -/
theorem clean_three_piece_return_is_mixed
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (a : C(Interval,Y))
    {a₀ a₁ b₀ b₁ : X}
    (P : Path a₀ b₀) (Q : Path b₀ b₁) (R : Path a₁ b₁)
    (hseam0 : p b₀ ∉ range a) (hseam1 : p b₁ ∉ range a)
    (hcontact : ∃ t : Interval, p (Q t) ∈ range a)
    (hPno : ∀ (E : C(Interval,X)), (∀ t, p (E t) = a t) →
      ∀ l r : Interval, l < r → P l ∈ range E → P r ∈ range E →
        (∀ t, l < t → t < r → p (P t) ∉ range a) → False)
    (hRno : ∀ (E : C(Interval,X)), (∀ t, p (E t) = a t) →
      ∀ l r : Interval, l < r → R l ∈ range E → R r ∈ range E →
        (∀ t, l < t → t < r → p (R t) ∉ range a) → False)
    (hQsingle : ∀ (E : C(Interval,X)), (∀ t, p (E t) = a t) →
      ∀ l r, Q l ∈ range E → Q r ∈ range E → l = r)
    (E : C(Interval,X)) (hEp : ∀ t, p (E t) = a t)
    (l r : Interval) (hlr : l < r)
    (hl : ((P.trans Q).trans R.symm) l ∈ range E)
    (hr : ((P.trans Q).trans R.symm) r ∈ range E)
    (hgap : ∀ t : Interval, l < t → t < r →
      p (((P.trans Q).trans R.symm) t) ∉ range a) :
    (∃ u v : Interval, u < 1 ∧ v ∈ Ioo (0 : Interval) 1 ∧
      P u ∈ range E ∧ Q v ∈ range E ∧
      (∀ t : Interval, u < t → t ≤ 1 → p (P t) ∉ range a) ∧
      (∀ t : Interval, t < v → p (Q t) ∉ range a)) ∨
    (∃ u v : Interval, u < 1 ∧ v ∈ Ioo (0 : Interval) 1 ∧
      R u ∈ range E ∧ Q.symm v ∈ range E ∧
      (∀ t : Interval, u < t → t ≤ 1 → p (R t) ∉ range a) ∧
      (∀ t : Interval, t < v → p (Q.symm t) ∉ range a)) := by
  have hproj {z : X} (hz : z ∈ range E) : p z ∈ range a := by
    obtain ⟨s,hs⟩ := hz
    exact ⟨s,(hEp s).symm.trans (congrArg p hs)⟩
  have hPi {u : Interval} (hu : P u ∈ range E) : u < 1 := by
    apply lt_of_le_of_ne (show u ≤ (1 : Interval) from u.property.2)
    intro he
    exact hseam0 (by simpa only [he,P.target] using hproj hu)
  have hRi {u : Interval} (hu : R u ∈ range E) : u < 1 := by
    apply lt_of_le_of_ne (show u ≤ (1 : Interval) from u.property.2)
    intro he
    exact hseam1 (by simpa only [he,R.target] using hproj hu)
  have hQi {u : Interval} (hu : Q u ∈ range E) : u ∈ Ioo (0 : Interval) 1 := by
    constructor
    · apply lt_of_le_of_ne (show (0 : Interval) ≤ u from u.property.1)
      intro he
      exact hseam0 (by simpa only [← he,Q.source] using hproj hu)
    · apply lt_of_le_of_ne (show u ≤ (1 : Interval) from u.property.2)
      intro he
      exact hseam1 (by simpa only [he,Q.target] using hproj hu)
  let cP := fun u => halfClock (halfClock u)
  let cQ := fun u => halfClock (laterClock u)
  let cR := fun u => laterClock (unitInterval.symm u)
  have hPclock (u) : ((P.trans Q).trans R.symm) (cP u) = P u := by
    simp only [cP,trans_halfClock]
  have hQclock (u) : ((P.trans Q).trans R.symm) (cQ u) = Q u := by
    simp only [cQ,trans_halfClock,trans_laterClock]
  have hRclock (u) : ((P.trans Q).trans R.symm) (cR u) = R u := by
    simp only [cR,trans_laterClock,Path.symm_apply,Function.comp_apply,unitInterval.symm_symm]
  have hcases (t : Interval) :
      (∃ u, t = cP u) ∨ (∃ u, t = cQ u) ∨ (∃ u, t = cR u) := by
    rcases trans_parameter_cases (P.trans Q) R.symm t with ⟨s,hs,_⟩ | ⟨s,hs,_⟩
    · rcases trans_parameter_cases P Q s with ⟨u,hu,_⟩ | ⟨u,hu,_⟩
      · exact Or.inl ⟨u,hs.trans (congrArg halfClock hu)⟩
      · exact Or.inr (Or.inl ⟨u,hs.trans (congrArg halfClock hu)⟩)
    · exact Or.inr (Or.inr ⟨unitInterval.symm s,by simpa [cR] using hs⟩)
  rcases hcases l with ⟨u,rfl⟩ | ⟨u,rfl⟩ | ⟨u,rfl⟩ <;>
    rcases hcases r with ⟨v,rfl⟩ | ⟨v,rfl⟩ | ⟨v,rfl⟩
  all_goals simp only [hPclock,hQclock,hRclock] at hl hr
  · exfalso
    apply hPno E hEp u v (by
      change u.val/2/2 < v.val/2/2 at hlr
      change u.val < v.val
      linarith) hl hr
    intro t hut htv
    have ht := hgap (cP t) (by
      change u.val/2/2 < t.val/2/2
      change u.val < t.val at hut
      linarith) (by
      change t.val/2/2 < v.val/2/2
      change t.val < v.val at htv
      linarith)
    simpa only [hPclock] using ht
  · refine Or.inl ⟨u,v,hPi hl,hQi hr,hl,hr,?_,?_⟩
    · intro t hut _
      have ht := hgap (cP t) (by
        change u.val/2/2 < t.val/2/2
        change u.val < t.val at hut
        linarith) (by
        change t.val/2/2 < (1+v.val)/2/2
        have hv : 0 < v.val := (hQi hr).1
        linarith [t.property.2])
      simpa only [hPclock] using ht
    · intro t htv
      have ht := hgap (cQ t) (by
        change u.val/2/2 < (1+t.val)/2/2
        have hu : u.val < 1 := hPi hl
        linarith [t.property.1]) (by
        change (1+t.val)/2/2 < (1+v.val)/2/2
        change t.val < v.val at htv
        linarith)
      simpa only [hQclock] using ht
  · exfalso
    obtain ⟨t,ht⟩ := hcontact
    have hti : t ∈ Ioo (0 : Interval) 1 := by
      constructor
      · apply lt_of_le_of_ne (show (0 : Interval) ≤ t from t.property.1)
        intro he; exact hseam0 (by simpa only [← he,Q.source] using ht)
      · apply lt_of_le_of_ne (show t ≤ (1 : Interval) from t.property.2)
        intro he; exact hseam1 (by simpa only [he,Q.target] using ht)
    apply hgap (cQ t) ?_ ?_ (by simpa only [hQclock] using ht)
    · change u.val/2/2 < (1+t.val)/2/2
      have hh : 0 < t.val := hti.1
      linarith [u.property.2]
    · change (1+t.val)/2/2 < (1+(1-v.val))/2
      have hh : t.val < 1 := hti.2
      linarith [v.property.2]
  · exfalso
    change (1+u.val)/2/2 < v.val/2/2 at hlr
    linarith [u.property.1,v.property.2]
  · have he := hQsingle E hEp u v hl hr
    subst v
    exact False.elim (lt_irrefl _ hlr)
  · refine Or.inr ⟨v,unitInterval.symm u,hRi hr,?_,hr,?_,?_,?_⟩
    · have hu := hQi hl
      constructor
      · change 0 < 1-u.val
        have hh : u.val < 1 := hu.2
        linarith
      · change 1-u.val < 1
        have hh : 0 < u.val := hu.1
        linarith
    · simpa only [Path.symm_apply,Function.comp_apply,unitInterval.symm_symm] using hl
    · intro t hvt _
      have ht := hgap (cR t) (by
        change (1+u.val)/2/2 < (1+(1-t.val))/2
        have hu : u.val < 1 := (hQi hl).2
        linarith [t.property.2]) (by
        change (1+(1-t.val))/2 < (1+(1-v.val))/2
        change v.val < t.val at hvt
        linarith)
      simpa only [hRclock] using ht
    · intro t htu
      have ht := hgap (cQ (unitInterval.symm t)) (by
        change (1+u.val)/2/2 < (1+(1-t.val))/2/2
        change t.val < 1-u.val at htu
        linarith) (by
        change (1+(1-t.val))/2/2 < (1+(1-v.val))/2
        have hv : v.val < 1 := hRi hr
        linarith [t.property.1])
      simpa only [hQclock,Path.symm_apply,Function.comp_apply] using ht
  · exfalso
    change (1+(1-u.val))/2 < v.val/2/2 at hlr
    linarith [u.property.2,v.property.2]
  · exfalso
    change (1+(1-u.val))/2 < (1+v.val)/2/2 at hlr
    linarith [u.property.2,v.property.2]
  · exfalso
    apply hRno E hEp v u (by
      change (1+(1-u.val))/2 < (1+(1-v.val))/2 at hlr
      change v.val < u.val
      linarith) hr hl
    intro t hvt htu
    have ht := hgap (cR t) (by
      change (1+(1-u.val))/2 < (1+(1-t.val))/2
      change t.val < u.val at htu
      linarith) (by
      change (1+(1-t.val))/2 < (1+(1-v.val))/2
      change v.val < t.val at hvt
      linarith)
    simpa only [hRclock] using ht

end CoherentEndpointMotion.FreeBoundaryContactRepair
