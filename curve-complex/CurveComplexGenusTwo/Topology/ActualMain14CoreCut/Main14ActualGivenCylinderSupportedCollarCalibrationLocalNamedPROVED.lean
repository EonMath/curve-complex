import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCylinderExteriorShrinkLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
set_option maxHeartbeats 4000000
-- Recalibrate the ACTUAL shrunken exterior extension; the WHOLE original
-- cylinder remains at (u+1)/3 and the two given traces are at G3's levels.
theorem actual_given_cylinder_supported_collar_calibration {X : Type} [TopologicalSpace X] [T2Space X]
    (g : C(Circle × Set.Icc (-2:ℝ) 3,X)) (hg : IsEmbedding g)
    (q : C(Circle × Interval,X))
    (hgiven : ∀ z (t : Set.Icc (-2:ℝ) 3), ∀ ht0 : 0 ≤ (t:ℝ), ∀ ht1 : (t:ℝ)≤1,
      g (z,t)=q (z,⟨t.val,ht0,ht1⟩))
    (U : Set X) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsub : ∀ z (t : Set.Icc (-2:ℝ) 3), -δ ≤ (t:ℝ) → (t:ℝ)≤1+δ → g (z,t)∈U) :
    ∃ Q : C(Circle × Interval,X), IsEmbedding Q ∧ Set.range Q ⊆ U ∧
      ∀ z (u : Interval), Q (z,⟨((u:ℝ)+1)/3,by
        constructor <;> linarith [u.property.1,u.property.2]⟩)=q (z,u) := by
  audit_main14_base3
    let scale : Interval → ℝ := fun u =>
      if (u:ℝ)≤1/3 then -δ+3*δ*(u:ℝ)
      else if (u:ℝ)≤2/3 then 3*(u:ℝ)-1
      else 1+3*δ*((u:ℝ)-2/3)
    have hscalebound (u : Interval) : -δ ≤ scale u ∧ scale u ≤ 1+δ := by
      dsimp [scale]
      split_ifs <;> constructor <;> nlinarith [u.property.1,u.property.2]
    have hscalemem (u : Interval) : scale u ∈ Set.Icc (-2:ℝ) 3 := by
      obtain ⟨h0,h1⟩ := hscalebound u
      constructor <;> linarith
    have hc2 : Continuous (fun u : Interval =>
        if (u:ℝ)≤2/3 then 3*(u:ℝ)-1 else 1+3*δ*((u:ℝ)-2/3)) := by
      apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) (by fun_prop)
      intro u hu
      rw [hu]
      ring
    have hscalec : Continuous scale := by
      apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) hc2.continuousOn
      intro u hu
      rw [hu,if_pos (by norm_num : (1/3:ℝ)≤2/3)]
      ring
    have hscalemono : StrictMono scale := by
      intro x y hxy
      have hxyR : (x:ℝ)<(y:ℝ) := hxy
      have hs : 0<3*δ*((y:ℝ)-(x:ℝ)) :=
        mul_pos (mul_pos (by norm_num) hδ) (sub_pos.mpr hxyR)
      dsimp [scale]
      split_ifs <;> nlinarith [x.property.1,x.property.2,y.property.1,y.property.2]
    let k : Interval → Set.Icc (-2:ℝ) 3 := fun u => ⟨scale u,hscalemem u⟩
    let Q : C(Circle × Interval,X) := ⟨fun p => g (p.1,k p.2),
      g.continuous.comp (continuous_fst.prodMk ((hscalec.subtype_mk _).comp continuous_snd))⟩
    have hQi : Function.Injective Q := by
      intro p v he
      have hh := hg.injective he
      have hfirst : p.1=v.1 := congrArg (fun p : Circle × Set.Icc (-2:ℝ) 3 => p.1) hh
      refine Prod.ext hfirst ?_
      apply hscalemono.injective
      exact congrArg (fun p : Circle × Set.Icc (-2:ℝ) 3 => (p.2:ℝ)) hh
    refine ⟨Q,(Q.continuous.isClosedEmbedding hQi).isEmbedding,?_,?_⟩
    · rintro x ⟨p,rfl⟩
      exact hsub p.1 (k p.2) (hscalebound p.2).1 (hscalebound p.2).2
    · intro z u
      let v : Interval := ⟨((u:ℝ)+1)/3,by constructor <;> linarith [u.property.1,u.property.2]⟩
      have hkv : scale v=(u:ℝ) := by
        dsimp [scale,v]
        split_ifs <;> nlinarith [u.property.1,u.property.2]
      have h0 : (0:ℝ)≤(k v:ℝ) := by change 0 ≤ scale v;rw [hkv];exact u.property.1
      have h1 : (k v:ℝ)≤1 := by change scale v≤1;rw [hkv];exact u.property.2
      change g (z,k v)=q (z,u)
      rw [hgiven z (k v) h0 h1]
      congr 1
      refine Prod.ext rfl ?_
      exact Subtype.ext hkv
end CurveComplex.HyperellipticModel
