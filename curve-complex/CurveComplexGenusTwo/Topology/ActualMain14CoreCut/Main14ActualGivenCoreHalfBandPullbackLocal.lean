import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCoreSmallComparisonCylindersSourceLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
-- This is the actual pullback port for the two alternatives already proved
-- for the SAME supplied G. No annulus confinement certificate is an input.
example (G : C(Circle × Interval,Circle × Interval))
    (ε : ℝ) (hε : 0 < ε) (hεq : ε < 1/4)
    (hband : ∀ z (u : Interval), |(u:ℝ)-1/2| ≤ ε →
      ∃ p : Circle × Interval, 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1 ∧ G p=(z,u))
    (hgap : ∀ z, ε < |((G (z,0)).2:ℝ)-1/2|)
    (b : Bool)
    (hside : ∀ z (u : Interval), 1/2 < (u:ℝ) →
      if b then ((G (z,u)).2:ℝ)<1/2 else 1/2<((G (z,u)).2:ℝ)) :
    (∀ z (t : Interval), ∃ p : Circle × Interval,
      (p.2:ℝ) ≤ 1/2 ∧
      G p=(z,⟨1/2+(if b then ε else -ε)*(1-(t:ℝ)),by
        cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> nlinarith [t.property.1,t.property.2]⟩)) ∧
    Disjoint (Set.range (fun z : Circle => G (z,0)))
      (Set.range (fun p : Circle × Interval =>
        ((p.1,⟨1/2+(if b then ε else -ε)*(1-(p.2:ℝ)),by
          cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> nlinarith [p.2.property.1,p.2.property.2]⟩) : Circle × Interval))) := by
  audit_main14_base3
    have habs (t : Interval) : |(if b then ε else -ε)*(1-(t:ℝ))| ≤ ε := by
      cases b
      · simp only [Bool.false_eq_true,if_false]
        rw [abs_mul,abs_neg,abs_of_pos hε,abs_of_nonneg (by linarith [t.property.2])]
        nlinarith [t.property.1]
      · simp only [if_true]
        rw [abs_mul,abs_of_pos hε,abs_of_nonneg (by linarith [t.property.2])]
        nlinarith [t.property.1]
    constructor
    · intro z t
      let u : Interval := ⟨1/2+(if b then ε else -ε)*(1-(t:ℝ)),by
        cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> nlinarith [t.property.1,t.property.2]⟩
      have hu : |(u:ℝ)-1/2| ≤ ε := by
        change |1/2+(if b then ε else -ε)*(1-(t:ℝ))-1/2| ≤ ε
        have he : (1/2:ℝ)+(if b then ε else -ε)*(1-(t:ℝ))-1/2 =
            (if b then ε else -ε)*(1-(t:ℝ)) := by ring
        rw [he]
        exact habs t
      obtain ⟨p,hp0,hp1,he⟩ := hband z u hu
      refine ⟨p,?_,he⟩
      by_contra hn
      have hs := hside p.1 p.2 (lt_of_not_ge hn)
      have hv := congrArg (fun x : Circle × Interval => (x.2:ℝ)) he
      cases b
      · simp only [Bool.false_eq_true,if_false] at hs hv
        change ((G p).2:ℝ)=1/2+-ε*(1-(t:ℝ)) at hv
        nlinarith [t.property.2]
      · simp only [if_true] at hs hv
        change ((G p).2:ℝ)=1/2+ε*(1-(t:ℝ)) at hv
        nlinarith [t.property.2]
    · apply Set.disjoint_left.mpr
      rintro x ⟨z,rfl⟩ ⟨p,he⟩
      have hv := congrArg (fun x : Circle × Interval => (x.2:ℝ)) he
      have hh : ((G (z,0)).2:ℝ)-1/2=(if b then ε else -ε)*(1-(p.2:ℝ)) := by
        change 1/2+(if b then ε else -ε)*(1-(p.2:ℝ))=((G (z,0)).2:ℝ) at hv
        linarith
      have hg := hgap z
      rw [hh] at hg
      exact (not_lt_of_ge (habs p.2)) hg
end CurveComplex.HyperellipticModel
