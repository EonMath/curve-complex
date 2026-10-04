import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic
namespace CurveComplex.LocalSurgery
open Set Topology
open scoped unitInterval

def actualMarkedCollarQuadrilateralParameterMap (r q : ℝ) :
    C(unitInterval × unitInterval,ℝ × ℝ) :=
  ⟨fun z => (z.1.val,z.1.val*r+(1-z.1.val+z.1.val*(q-r))*z.2.val),by fun_prop⟩

theorem actualMarkedCollarQuadrilateralCoefficientPositive
    (r q : ℝ) (hqr : r<q) (x : unitInterval) :
    0<1-x.val+x.val*(q-r) := by
  have hm : 0≤x.val*(q-r) := mul_nonneg x.property.1 (sub_pos.mpr hqr).le
  by_cases hx : x.val=1
  · rw [hx]
    simpa using sub_pos.mpr hqr
  · have hp : 0<1-x.val := sub_pos.mpr (lt_of_le_of_ne x.property.2 hx)
    exact add_pos_of_pos_of_nonneg hp hm

theorem actualMarkedCollarQuadrilateralParameterMapEmbedding
    (r q : ℝ) (hqr : r<q) :
    IsEmbedding (actualMarkedCollarQuadrilateralParameterMap r q) := by
  apply ((actualMarkedCollarQuadrilateralParameterMap r q).continuous.isClosedEmbedding ?_).isEmbedding
  intro z w he
  have hx : z.1=w.1 := Subtype.ext (congrArg Prod.fst he)
  have ht := congrArg Prod.snd he
  change z.1.val*r+(1-z.1.val+z.1.val*(q-r))*z.2.val=
    w.1.val*r+(1-w.1.val+w.1.val*(q-r))*w.2.val at ht
  rw [hx] at ht
  have hs := mul_left_cancel₀ (actualMarkedCollarQuadrilateralCoefficientPositive r q hqr w.1).ne'
    (add_left_cancel ht)
  exact Prod.ext hx (Subtype.ext hs)

theorem actualMarkedCollarQuadrilateralParameterMapRange
    (r q : ℝ) (hqr : r<q) :
    range (actualMarkedCollarQuadrilateralParameterMap r q)=
      {z : ℝ × ℝ | 0≤z.1 ∧ z.1≤1 ∧ z.1*r≤z.2 ∧ z.2≤1-z.1*(1-q)} := by
  ext z
  constructor
  · rintro ⟨⟨x,t⟩,rfl⟩
    have hc := actualMarkedCollarQuadrilateralCoefficientPositive r q hqr x
    refine ⟨x.property.1,x.property.2,?_,?_⟩
    · change x.val*r≤x.val*r+(1-x.val+x.val*(q-r))*t.val
      exact le_add_of_nonneg_right (mul_nonneg hc.le t.property.1)
    · have hm := mul_le_of_le_one_right hc.le t.property.2
      change x.val*r+(1-x.val+x.val*(q-r))*t.val≤1-x.val*(1-q)
      nlinarith only [hm]
  · rintro ⟨hx₀,hx₁,ht₀,ht₁⟩
    let x : unitInterval := ⟨z.1,hx₀,hx₁⟩
    let a := 1-z.1+z.1*(q-r)
    have ha : 0<a := actualMarkedCollarQuadrilateralCoefficientPositive r q hqr x
    have hnum : 0≤z.2-z.1*r := sub_nonneg.mpr ht₀
    have hnumUpper : z.2-z.1*r≤a := by
      dsimp [a]
      nlinarith only [ht₁]
    let t : unitInterval := ⟨(z.2-z.1*r)/a,div_nonneg hnum ha.le,(div_le_one ha).mpr hnumUpper⟩
    refine ⟨(x,t),?_⟩
    apply Prod.ext
    · rfl
    · change z.1*r+a*((z.2-z.1*r)/a)=z.2
      rw [←mul_div_assoc,mul_div_cancel_left₀ _ ha.ne']
      ring

theorem actualMarkedCollarQuadrilateralParameterBoundary
    (r q : ℝ) :
    (∀ t : unitInterval,actualMarkedCollarQuadrilateralParameterMap r q (0,t)=(0,t.val)) ∧
    (∀ t : unitInterval,actualMarkedCollarQuadrilateralParameterMap r q (1,t)=
      (1,r+(q-r)*t.val)) ∧
    (∀ x : unitInterval,actualMarkedCollarQuadrilateralParameterMap r q (x,0)=(x.val,x.val*r)) ∧
    (∀ x : unitInterval,actualMarkedCollarQuadrilateralParameterMap r q (x,1)=
      (x.val,1-x.val*(1-q))) := by
  repeat' constructor
  all_goals intro t;apply Prod.ext
  all_goals simp [actualMarkedCollarQuadrilateralParameterMap]
  all_goals ring
end CurveComplex.LocalSurgery
