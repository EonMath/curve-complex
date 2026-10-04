import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib
namespace CurveComplex
open Set Topology
theorem square_band_ambient_motion :
      ∃ K : AmbientIsotopy (Interval × Interval), ∃ J : C(Interval × (Interval × Interval),Interval × Interval),
        (∀ t z, J (t,K.map (t,z)) = z) ∧
        (∀ t z, K.map (t,J (t,z)) = z) ∧
        (∀ t z, (K.map (t,z)).1 = z.1) ∧
        (∀ t z, K.map (t,(z,0)) = (z,0)) ∧
        (∀ t z, K.map (t,(z,1)) = (z,1)) ∧
        (∀ z, K.finalMap (z,⟨1/3,by norm_num⟩) = (z,⟨2/3,by norm_num⟩)) := by
    let r (t u : Interval) : ℝ :=
      if (u : ℝ) ≤ 1/3 then (1 + (t : ℝ)) * u
      else (1 - (t : ℝ)/2) * u + (t : ℝ)/2
    let v (t u : Interval) : ℝ :=
      if (u : ℝ) ≤ (1 + (t : ℝ))/3 then (u : ℝ)/(1 + (t : ℝ))
      else ((u : ℝ) - (t : ℝ)/2)/(1 - (t : ℝ)/2)
    have ha (t : Interval) : 0 < 1 + (t : ℝ) := by linarith [t.property.1]
    have hb (t : Interval) : 0 < 1 - (t : ℝ)/2 := by linarith [t.property.2]
    have htwo (t : Interval) : (2 : ℝ) - (t : ℝ) ≠ 0 := by linarith [t.property.2]
    have hrmem (t u : Interval) : r t u ∈ Set.Icc (0:ℝ) 1 := by
      dsimp [r]
      split_ifs with h
      · constructor <;> nlinarith [t.property.1,t.property.2,u.property.1]
      · constructor <;> nlinarith [t.property.1,t.property.2,u.property.1,u.property.2]
    have hvmem (t u : Interval) : v t u ∈ Set.Icc (0:ℝ) 1 := by
      dsimp [v]
      split_ifs with h
      · constructor
        · exact div_nonneg u.property.1 (ha t).le
        · apply (div_le_iff₀ (ha t)).mpr
          nlinarith [u.property.2,t.property.1]
      · constructor
        · apply (le_div_iff₀ (hb t)).mpr
          nlinarith [t.property.1,t.property.2]
        · apply (div_le_iff₀ (hb t)).mpr
          linarith [u.property.2]
    let R (t u : Interval) : Interval := ⟨r t u,hrmem t u⟩
    let V (t u : Interval) : Interval := ⟨v t u,hvmem t u⟩
    have hRc : Continuous (fun tu : Interval × Interval => R tu.1 tu.2) := by
      apply Continuous.subtype_mk
      apply continuous_if_le (by fun_prop) continuous_const
        (by fun_prop) (by fun_prop)
      intro tu htu
      rw [htu]
      ring
    have hVc : Continuous (fun tu : Interval × Interval => V tu.1 tu.2) := by
      apply Continuous.subtype_mk
      apply continuous_if_le (by fun_prop) (by fun_prop)
        (by exact (continuous_snd.subtype_val.div (continuous_const.add
          continuous_fst.subtype_val) (fun tu => (ha tu.1).ne')).continuousOn)
        (by exact ((continuous_snd.subtype_val.sub
          (continuous_fst.subtype_val.div_const 2)).div
          (continuous_const.sub (continuous_fst.subtype_val.div_const 2))
          (fun tu => (hb tu.1).ne')).continuousOn)
      intro tu htu
      have h1 := ha tu.1
      have h2 := hb tu.1
      rw [htu]
      field_simp [(ha tu.1).ne', (hb tu.1).ne', htwo tu.1]
      ring
    have hVR (t u : Interval) : V t (R t u) = u := by
      apply Subtype.ext
      dsimp [V,R,v,r]
      split_ifs with hu hv hv
      · field_simp [(ha t).ne', (hb t).ne', htwo t]
      · exfalso
        nlinarith [t.property.1]
      · exfalso
        nlinarith [t.property.2]
      · field_simp [(ha t).ne', (hb t).ne', htwo t]
        ring
    have hRV (t u : Interval) : R t (V t u) = u := by
      apply Subtype.ext
      dsimp [V,R,v,r]
      split_ifs with hu hv hv
      · field_simp [(ha t).ne', (hb t).ne', htwo t]
      · exfalso
        have hh : (u : ℝ)/(1+(t:ℝ)) ≤ 1/3 :=
          (div_le_iff₀ (ha t)).mpr (by linarith)
        exact hv hh
      · exfalso
        have hh := (div_le_iff₀ (hb t)).mp hv
        linarith
      · field_simp [(ha t).ne', (hb t).ne', htwo t]
        ring
    let map : C(Interval × (Interval × Interval),Interval × Interval) :=
      ⟨fun z => (z.2.1,R z.1 z.2.2),continuous_snd.fst.prodMk
        (hRc.comp (continuous_fst.prodMk continuous_snd.snd))⟩
    let invmap : C(Interval × (Interval × Interval),Interval × Interval) :=
      ⟨fun z => (z.2.1,V z.1 z.2.2),continuous_snd.fst.prodMk
        (hVc.comp (continuous_fst.prodMk continuous_snd.snd))⟩
    have hR0 (u : Interval) : R 0 u = u := by
      apply Subtype.ext
      dsimp [R,r]
      split_ifs <;> simp
    let K : AmbientIsotopy (Interval × Interval) := {
      map := map
      homeomorphism_at := by
        intro t
        refine ⟨{ toFun := fun z => (z.1,R t z.2)
                  invFun := fun z => (z.1,V t z.2)
                  left_inv := fun z => Prod.ext rfl (hVR t z.2)
                  right_inv := fun z => Prod.ext rfl (hRV t z.2)
                  continuous_toFun := continuous_fst.prodMk
                    (hRc.comp (continuous_const.prodMk continuous_snd))
                  continuous_invFun := continuous_fst.prodMk
                    (hVc.comp (continuous_const.prodMk continuous_snd)) },fun z => rfl⟩
      at_zero := fun z => Prod.ext rfl (hR0 z.2) }
    refine ⟨K,invmap,fun t z => Prod.ext rfl (hVR t z.2),
      fun t z => Prod.ext rfl (hRV t z.2),fun _ _ => rfl,?_,?_,?_⟩
    · intro t z
      apply Prod.ext
      · rfl
      apply Subtype.ext
      dsimp [K,map,R,r]
      simp
    · intro t z
      apply Prod.ext
      · rfl
      apply Subtype.ext
      dsimp [K,map,R,r]
      norm_num
    · intro z
      apply Prod.ext
      · rfl
      apply Subtype.ext
      dsimp [AmbientIsotopy.finalMap,K,map,R,r]
      norm_num

end CurveComplex
