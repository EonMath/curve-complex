import CurveComplexGenusTwo.Topology.Orientation.PlaneReflection
import CurveComplexGenusTwo.CWHurewicz.ExcisionDifferentialTransport
import CurveComplexGenusTwo.CWHurewicz.ExcisionConnecting

import CurveComplexGenusTwo.CWHurewicz.PairNaturality
open CategoryTheory CategoryTheory.Limits Set Topology
open CurveComplexGenusTwo.CWHurewicz
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ReflectionGermProof

def inclusion {X : Type} [TopologicalSpace X] (W : Set X) : C(W,X) :=
  ⟨Subtype.val,continuous_subtype_val⟩

lemma pairMap_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f g : C(X,Y))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (h : f = g) (n : ℕ) :
    pairRelativeHomologyMap A B f hf n = pairRelativeHomologyMap A B g hg n := by
  subst g
  rfl

lemma pairHomeo_isIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y)
    (hf : ∀ x ∈ A, e x ∈ B) (hg : ∀ y ∈ B, e.symm y ∈ A) (n : ℕ) :
    IsIso (pairRelativeHomologyMap A B ⟨e,e.continuous⟩ hf n) := by
  let f : C(X,Y) := ⟨e,e.continuous⟩
  let g : C(Y,X) := ⟨e.symm,e.symm.continuous⟩
  have hgf : g.comp f = ContinuousMap.id X := by ext z; exact e.symm_apply_apply z
  have hfg : f.comp g = ContinuousMap.id Y := by ext z; exact e.apply_symm_apply z
  let iso : relativeHomology X A n ≅ relativeHomology Y B n :=
    ⟨pairRelativeHomologyMap A B f hf n,pairRelativeHomologyMap B A g hg n,by
      rw [← pairRelativeHomologyMap_comp]
      simpa only [hgf] using pairRelativeHomologyMap_id A n,by
      rw [← pairRelativeHomologyMap_comp]
      simpa only [hfg] using pairRelativeHomologyMap_id B n⟩
  exact iso.isIso_hom

lemma inclusion_isIso {X : Type} [TopologicalSpace X]
    (A W : Set X) (h : closure Wᶜ ⊆ interior A) :
    IsIso (pairRelativeHomologyMap {z : W | z.val ∈ A} A (inclusion W)
      (fun z hz => hz) 2) := by
  let Y := Excised X Wᶜ
  let D : Set Y := excisedSubspace A Wᶜ
  let e : W ≃ₜ Y := Homeomorph.setCongr (compl_compl W).symm
  let k : C(W,Y) := ⟨e,e.continuous⟩
  let j : C(Y,X) := ⟨Subtype.val,continuous_subtype_val⟩
  have hk : ∀ z ∈ {z : W | z.val ∈ A}, k z ∈ D := fun z hz => hz
  have hki : ∀ z ∈ D, e.symm z ∈ {z : W | z.val ∈ A} := fun z hz => hz
  have hj : ∀ z ∈ D, j z ∈ A := fun z hz => hz
  haveI hkIso : IsIso (pairRelativeHomologyMap {z : W | z.val ∈ A} D k hk 2) :=
    pairHomeo_isIso {z : W | z.val ∈ A} D e hk hki 2
  haveI : IsIso (pairRelativeHomologyMap D A j hj 2) := by
    exact canonicalExcisionHomologyMap_isIso X A Wᶜ h 1
  have he : j.comp k = inclusion W := by ext z; rfl
  have hm := pairRelativeHomologyMap_comp {z : W | z.val ∈ A} D A k j hk hj 2
  have hm' := (pairMap_congr {z : W | z.val ∈ A} A _ _ (fun z hz => hz) _ he.symm 2).trans hm
  rw [hm']
  infer_instance

lemma puncture_excision {X : Type} [TopologicalSpace X] [T1Space X]
    (x : X) (W : Set X) (hW : IsOpen W) (hx : x ∈ W) :
    closure Wᶜ ⊆ interior ({x}ᶜ : Set X) := by
  rw [hW.isClosed_compl.closure_eq,isOpen_compl_singleton.interior_eq]
  intro z hz
  simp only [mem_compl_iff,mem_singleton_iff] at hz ⊢
  rintro rfl
  exact hz hx
end ReflectionGermProof

open CategoryTheory CategoryTheory.Limits Set Topology
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
namespace CurveComplex.GenusOrientationCandidate

/-- Actual relative-homology transport of a literal reflection germ in a surface
chart. This uses the given map and chart and contains no orientability premise. -/
theorem chart_reflection_germ_relativeHomologyMap
    (S : Type) [TopologicalSpace S] [T2Space S]
    (x : S) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (hx : x ∈ e.source) (hex : e x = 0)
    (f : C(S,S))
    (hf : ∀ y ∈ ({x}ᶜ : Set S), f y ∈ ({x}ᶜ : Set S))
    (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall (0 : ℝ × ℝ) r ⊆ e.target)
    (hgerm : ∀ z ∈ Metric.ball (0 : ℝ × ℝ) r,
      f (e.symm z) = e.symm (planeReflection z)) :
    pairRelativeHomologyMap ({x}ᶜ : Set S) ({x}ᶜ : Set S) f hf 2 =
      -(𝟙 (relativeHomology S ({x}ᶜ : Set S) 2)) := by
  let B : Set (ℝ × ℝ) := Metric.ball 0 r
  let W : Set S := e.source ∩ e ⁻¹' B
  have hB : B ⊆ e.target := fun z hz => hball (Metric.ball_subset_closedBall hz)
  have hW : IsOpen W := e.isOpen_inter_preimage Metric.isOpen_ball
  have hxW : x ∈ W := ⟨hx,by
    change e x ∈ Metric.ball 0 r
    simpa only [hex,Metric.mem_ball,dist_self] using hr⟩
  let c : B ≃ₜ W := {
    toFun := fun z => ⟨e.symm z,⟨e.map_target (hB z.property),by
      change e (e.symm z.val) ∈ B
      rw [e.right_inv (hB z.property)]
      exact z.property⟩⟩
    invFun := fun y => ⟨e y,y.property.2⟩
    left_inv := fun z => Subtype.ext (e.right_inv (hB z.property))
    right_inv := fun y => Subtype.ext (e.left_inv y.property.1)
    continuous_toFun := (e.symm.continuousOn.comp_continuous continuous_subtype_val
      (fun z => hB z.property)).subtype_mk _
    continuous_invFun := (e.continuousOn.comp_continuous continuous_subtype_val
      (fun y => y.property.1)).subtype_mk _ }
  let A : Set B := {z | z.val ≠ 0}
  let D : Set W := {y | y.val ≠ x}
  let C : Set S := {x}ᶜ
  let P : Set (ℝ × ℝ) := {0}ᶜ
  have hc : ∀ z ∈ A, c z ∈ D := by
    intro z hz he
    apply hz
    have hh := congrArg e he
    change e (e.symm z.val) = e x at hh
    rw [e.right_inv (hB z.property),hex] at hh
    exact hh
  have hci : ∀ y ∈ D, c.symm y ∈ A := by
    intro y hy he
    apply hy
    have he' : e y.val = e x := he.trans hex.symm
    exact e.injOn y.property.1 hx he'
  let k : C(B,W) := ⟨c,c.continuous⟩
  let i : C(B,S) := (ReflectionGermProof.inclusion W).comp k
  let j : C(B,ℝ × ℝ) := ReflectionGermProof.inclusion B
  have hi : ∀ z ∈ A, i z ∈ C := hc
  have hj : ∀ z ∈ A, j z ∈ P := fun z hz => hz
  have hreflectionB : ∀ z ∈ B, planeReflection z ∈ B := by
    intro z hz
    simpa only [B,Metric.mem_ball,dist_zero_right,planeReflection,ContinuousMap.coe_mk,
      Prod.norm_mk,norm_neg,Prod.norm_def] using hz
  let g : C(B,B) := ⟨fun z => ⟨planeReflection z,hreflectionB z.val z.property⟩,
    (planeReflection.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hg : ∀ z ∈ A, g z ∈ A := by
    intro z hz
    exact planeReflection_preserves_puncture z.val hz
  have hiIso : IsIso (pairRelativeHomologyMap A C i hi 2) := by
    haveI hkIso : IsIso (pairRelativeHomologyMap A D k hc 2) :=
      ReflectionGermProof.pairHomeo_isIso A D c hc hci 2
    haveI hwIso : IsIso (pairRelativeHomologyMap D C (ReflectionGermProof.inclusion W)
        (fun y hy => hy) 2) := ReflectionGermProof.inclusion_isIso C W
      (ReflectionGermProof.puncture_excision x W hW hxW)
    have hm := pairRelativeHomologyMap_comp A D C k (ReflectionGermProof.inclusion W)
      hc (fun y hy => hy) 2
    rw [hm]
    infer_instance
  have hjIso : IsIso (pairRelativeHomologyMap A P j hj 2) :=
    ReflectionGermProof.inclusion_isIso P B
      (ReflectionGermProof.puncture_excision (0 : ℝ × ℝ) B Metric.isOpen_ball
        (by simpa only [B,Metric.mem_ball,dist_self] using hr))
  have hfg : f.comp i = i.comp g := by
    apply ContinuousMap.ext
    intro z
    change f (e.symm z.val) = e.symm (planeReflection z.val)
    exact hgerm z.val z.property
  have hjg : planeReflection.comp j = j.comp g := by ext z <;> rfl
  have hpr : pairRelativeHomologyMap P P planeReflection planeReflection_preserves_puncture 2 =
      -(𝟙 (relativeHomology (ℝ × ℝ) P 2)) := planeReflection_relativeHomologyMap_eq_neg_id
  have hgn : pairRelativeHomologyMap A A g hg 2 = -(𝟙 (relativeHomology B A 2)) := by
    apply (cancel_mono (pairRelativeHomologyMap A P j hj 2)).1
    calc
      pairRelativeHomologyMap A A g hg 2 ≫ pairRelativeHomologyMap A P j hj 2 =
          pairRelativeHomologyMap A P (j.comp g) (fun z hz => hj (g z) (hg z hz)) 2 :=
        (pairRelativeHomologyMap_comp A A P g j hg hj 2).symm
      _ = pairRelativeHomologyMap A P (planeReflection.comp j)
          (fun z hz => planeReflection_preserves_puncture (j z) (hj z hz)) 2 :=
        ReflectionGermProof.pairMap_congr A P _ _ _ _ hjg.symm 2
      _ = pairRelativeHomologyMap A P j hj 2 ≫
          pairRelativeHomologyMap P P planeReflection planeReflection_preserves_puncture 2 :=
        pairRelativeHomologyMap_comp A P P j planeReflection hj planeReflection_preserves_puncture 2
      _ = (-(𝟙 (relativeHomology B A 2))) ≫ pairRelativeHomologyMap A P j hj 2 := by
        rw [hpr]
        simp only [Preadditive.comp_neg,Preadditive.neg_comp,Category.comp_id,Category.id_comp]
  apply (cancel_epi (pairRelativeHomologyMap A C i hi 2)).1
  calc
    pairRelativeHomologyMap A C i hi 2 ≫ pairRelativeHomologyMap C C f hf 2 =
        pairRelativeHomologyMap A C (f.comp i) (fun z hz => hf (i z) (hi z hz)) 2 :=
      (pairRelativeHomologyMap_comp A C C i f hi hf 2).symm
    _ = pairRelativeHomologyMap A C (i.comp g) (fun z hz => hi (g z) (hg z hz)) 2 :=
      ReflectionGermProof.pairMap_congr A C _ _ _ _ hfg 2
    _ = pairRelativeHomologyMap A A g hg 2 ≫ pairRelativeHomologyMap A C i hi 2 :=
      pairRelativeHomologyMap_comp A A C g i hg hi 2
    _ = pairRelativeHomologyMap A C i hi 2 ≫ (-(𝟙 (relativeHomology S C 2))) := by
      rw [hgn]
      simp only [Preadditive.comp_neg,Preadditive.neg_comp,Category.comp_id,Category.id_comp]

end CurveComplex.GenusOrientationCandidate
