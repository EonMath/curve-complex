import CurveComplexGenusTwo.Dictionary.Circle24.OneMarkRadialFilling
open Set Topology
namespace CurveComplex

abbrev OneMarkPolarStrip := (Interval × Interval) × Bool

def oneMarkPolarRel (x y : OneMarkPolarStrip) : Prop :=
  x.1.1=y.1.1 ∧ (x.1.1=0 ∨
    (x.1.2=y.1.2 ∧ x.2=y.2) ∨
    (x.1.2=0 ∧ y.1.2=1 ∧ x.2≠y.2) ∨
    (x.1.2=1 ∧ y.1.2=0 ∧ x.2≠y.2))

abbrev OneMarkPolarCell := Quot oneMarkPolarRel

namespace BranchedDoubleCover
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

def sheetSelect (q : BranchedDoubleCover E S) (b : Bool) (x : E) : E :=
  if b then q.deck x else x

private theorem select_projection (q : BranchedDoubleCover E S) (b : Bool) (x : E) :
    q.projection (q.sheetSelect b x)=q.projection x := by
  cases b <;> simp [sheetSelect,q.projection_deck]

private theorem select_same_iff (q : BranchedDoubleCover E S) (b c : Bool) (x : E)
    (hx : q.deck x≠x) : q.sheetSelect b x=q.sheetSelect c x ↔ b=c := by
  cases b <;> cases c <;> simp [sheetSelect,hx,Ne.symm hx]

private theorem select_deck_iff (q : BranchedDoubleCover E S) (b c : Bool) (x : E)
    (hx : q.deck x≠x) : q.sheetSelect b x=q.sheetSelect c (q.deck x) ↔ b≠c := by
  cases b <;> cases c <;> simp [sheetSelect,hx,Ne.symm hx,q.deck_involution]

/-- The exact gluing relation of the two full radial strips: their center faces
collapse together; their angular endpoints cross sheets; no other points glue. -/
theorem radial_sheet_collision_iff
    (q : BranchedDoubleCover E S)
    (f : C(Metric.closedBall (0:Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
    (honly : ∀ z, f z ∈ q.branch ↔ z=(⟨0,by simp⟩ : Metric.closedBall (0:Schoenflies.Plane) 1))
    (β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1))
    (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hnorm : ∀ t, ‖(β t).val‖=1)
    (L : C(Interval × Interval,E))
    (hπ : ∀ r t, q.projection (L (r,t)) =
      f (HyperellipticModel.discRadialContraction ⟨0,by simp⟩ r (β t)))
    (hedge : ∀ r, L (r,1)=q.deck (L (r,0)))
    (hzero : ∀ t t', L (0,t)=L (0,t'))
    (x y : OneMarkPolarStrip) :
    q.sheetSelect x.2 (L x.1)=q.sheetSelect y.2 (L y.1) ↔ oneMarkPolarRel x y := by
  have hval (r t : Interval) :
      (HyperellipticModel.discRadialContraction (⟨0,by simp⟩ : Metric.closedBall (0:Schoenflies.Plane) 1) r (β t)).val =
      (r:ℝ) • (β t).val := by simp [HyperellipticModel.discRadialContraction]
  have hfree (r t : Interval) (hr : r≠0) : q.deck (L (r,t))≠L (r,t) := by
    intro hfix
    have hb := (q.fixed_iff_branch _).mp hfix
    rw [hπ,honly] at hb
    have he := congrArg (fun z : Metric.closedBall (0:Schoenflies.Plane) 1 => ‖z.val‖) hb
    rw [hval,norm_smul,Real.norm_eq_abs,abs_of_nonneg r.property.1,hnorm,mul_one,norm_zero] at he
    exact hr (Subtype.ext he)
  have hfixzero (t : Interval) : q.deck (L (0,t))=L (0,t) := by
    apply (q.fixed_iff_branch _).mpr
    rw [hπ,honly]
    apply Subtype.ext
    simp [hval]
  constructor
  · intro he
    change q.sheetSelect x.2 (L (x.1.1,x.1.2))=
      q.sheetSelect y.2 (L (y.1.1,y.1.2)) at he
    have hπeq : q.projection (L x.1)=q.projection (L y.1) := by
      simpa only [select_projection] using congrArg q.projection he
    rw [hπ,hπ] at hπeq
    have hrad := congrArg Subtype.val (hf.injective hπeq)
    rw [hval,hval] at hrad
    have hrval := congrArg norm hrad
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg x.1.1.property.1,
      abs_of_nonneg y.1.1.property.1,hnorm,mul_one] at hrval
    have hr : x.1.1=y.1.1 := Subtype.ext hrval
    refine ⟨hr,?_⟩
    by_cases hz : x.1.1=0
    · exact Or.inl hz
    · right
      have hpos : 0 < (x.1.1:ℝ) := lt_of_le_of_ne x.1.1.property.1
        (fun hh => hz (Subtype.ext hh.symm))
      rw [← hr] at hrad
      have hβeq : β x.1.2=β y.1.2 := Subtype.ext
        (smul_right_injective Schoenflies.Plane (ne_of_gt hpos) hrad)
      rcases hcoll _ _ hβeq with ht | ⟨ht,ht'⟩ | ⟨ht,ht'⟩
      · left
        refine ⟨ht,?_⟩
        have he' : q.sheetSelect x.2 (L (x.1.1,x.1.2))=
            q.sheetSelect y.2 (L (x.1.1,x.1.2)) := by
          simpa only [← hr,← ht] using he
        exact (select_same_iff q _ _ _ (hfree _ _ hz)).mp he'
      · right; left
        refine ⟨ht,ht',?_⟩
        have he' : q.sheetSelect x.2 (L (x.1.1,0))=
            q.sheetSelect y.2 (q.deck (L (x.1.1,0))) := by
          simpa only [← hr,ht,ht',hedge] using he
        exact (select_deck_iff q _ _ _ (hfree _ _ hz)).mp he'
      · right; right
        refine ⟨ht,ht',?_⟩
        have he' : q.sheetSelect y.2 (L (x.1.1,0))=
            q.sheetSelect x.2 (q.deck (L (x.1.1,0))) := by
          simpa only [← hr,ht,ht',hedge] using he.symm
        exact Ne.symm ((select_deck_iff q _ _ _ (hfree _ _ hz)).mp he')
  · rintro ⟨hr,hz | ⟨ht,hb⟩ | ⟨ht,ht',hb⟩ | ⟨ht,ht',hb⟩⟩
    · have hL : L x.1=L y.1 := by
        change L (x.1.1,x.1.2)=L (y.1.1,y.1.2)
        simpa only [hz,← hr] using hzero x.1.2 y.1.2
      have hfixed : q.deck (L x.1)=L x.1 := by
        change q.deck (L (x.1.1,x.1.2))=L (x.1.1,x.1.2)
        simpa only [hz] using hfixzero x.1.2
      cases hx : x.2 <;> cases hy : y.2 <;> simp [sheetSelect,← hL,hfixed]
    · have hp : x.1=y.1 := Prod.ext hr ht
      simp only [hp,hb]
    · have heq : L y.1=q.deck (L x.1) := by
        change L (y.1.1,y.1.2)=q.deck (L (x.1.1,x.1.2))
        simpa only [← hr,ht,ht'] using hedge x.1.1
      rw [heq]
      by_cases hz : x.1.1=0
      · have hfixed : q.deck (L x.1)=L x.1 := by
          change q.deck (L (x.1.1,x.1.2))=L (x.1.1,x.1.2)
          simpa only [hz] using hfixzero x.1.2
        cases hx : x.2 <;> cases hy : y.2 <;> simp [sheetSelect,hfixed]
      · exact (select_deck_iff q _ _ _ (hfree _ _ hz)).mpr hb
    · have heq : L x.1=q.deck (L y.1) := by
        change L (x.1.1,x.1.2)=q.deck (L (y.1.1,y.1.2))
        simpa only [hr,ht,ht'] using hedge y.1.1
      rw [heq]
      by_cases hz : y.1.1=0
      · have hfixed : q.deck (L y.1)=L y.1 := by
          change q.deck (L (y.1.1,y.1.2))=L (y.1.1,y.1.2)
          simpa only [hz] using hfixzero y.1.2
        cases hx : x.2 <;> cases hy : y.2 <;> simp [sheetSelect,hfixed]
      · exact ((select_deck_iff q _ _ _ (hfree _ _ hz)).mpr (Ne.symm hb)).symm

end BranchedDoubleCover
end CurveComplex
#print axioms CurveComplex.BranchedDoubleCover.radial_sheet_collision_iff
