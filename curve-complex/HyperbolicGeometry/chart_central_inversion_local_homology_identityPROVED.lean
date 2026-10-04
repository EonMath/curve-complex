import CurveComplexGenusTwo.Topology.LocalOrientation.LocalReflectionGerm
open CategoryTheory CategoryTheory.Limits Set Topology
open CurveComplexGenusTwo.CWHurewicz
open CurveComplex.GenusOrientationCandidate
set_option backward.isDefEq.respectTransparency false
namespace CurveComplex.Hyperbolic
theorem chart_central_inversion_local_homology_identity
    (S : Type) [TopologicalSpace S] [T2Space S]
    (x : S) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (hx : x ∈ e.source) (hex : e x = 0)
    (f : C(S,S))
    (hf : ∀ y ∈ ({x}ᶜ : Set S), f y ∈ ({x}ᶜ : Set S))
    (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall (0 : ℝ × ℝ) r ⊆ e.target)
    (hgerm : ∀ z ∈ Metric.ball (0 : ℝ × ℝ) r,
      f (e.symm z) = e.symm (-z)) :
    pairRelativeHomologyMap ({x}ᶜ : Set S) ({x}ᶜ : Set S) f hf 2 =
      (𝟙 (relativeHomology S ({x}ᶜ : Set S) 2)) := by
  let negation : C(ℝ × ℝ,ℝ × ℝ) := ⟨fun z => -z, continuous_neg⟩
  have hneg : ∀ z ∈ ({(0,0)}ᶜ : Set (ℝ × ℝ)), negation z ∈ ({(0,0)}ᶜ : Set (ℝ × ℝ)) := by
    intro z hz he
    apply hz
    change -z = (0,0) at he
    have hh := congrArg Neg.neg he
    simpa using hh
  have planeCentral : pairRelativeHomologyMap ({(0,0)}ᶜ : Set (ℝ × ℝ)) ({(0,0)}ᶜ : Set (ℝ × ℝ))
      negation hneg 2 = 𝟙 (relativeHomology (ℝ × ℝ) ({(0,0)}ᶜ : Set (ℝ × ℝ)) 2) := by
    let P : Set (ℝ × ℝ) := {(0,0)}ᶜ
    let q : C(ℝ × ℝ,ℝ × ℝ) := ⟨Prod.swap,continuous_swap⟩
    have hq : ∀ z ∈ P, q z ∈ P := by
      intro z hz hh
      apply hz
      change Prod.swap z = (0,0) at hh
      have he := congrArg Prod.swap hh
      exact he
    have hqq : q.comp q = ContinuousMap.id (ℝ × ℝ) := by ext z <;> rfl
    have hqqmap : pairRelativeHomologyMap P P q hq 2 ≫
        pairRelativeHomologyMap P P q hq 2 = 𝟙 (relativeHomology (ℝ × ℝ) P 2) := by
      rw [← pairRelativeHomologyMap_comp]
      exact (ReflectionGermProof.pairMap_congr P P (q.comp q) (ContinuousMap.id _)
        (fun z hz => hq (q z) (hq z hz)) (fun z hz => hz) hqq 2).trans
          (pairRelativeHomologyMap_id P 2)
    have hform : (⟨fun z : ℝ × ℝ => -z,continuous_neg⟩ : C(ℝ × ℝ,ℝ × ℝ)) =
        q.comp (planeReflection.comp (q.comp planeReflection)) := by
      ext z <;> rfl
    have hcomp : ∀ z ∈ P, (q.comp (planeReflection.comp (q.comp planeReflection))) z ∈ P := by
      intro z hz
      exact hq _ (planeReflection_preserves_puncture (q (planeReflection z)) (hq (planeReflection z) (planeReflection_preserves_puncture z hz)))
    have hf := ReflectionGermProof.pairMap_congr P P
      (⟨fun z : ℝ × ℝ => -z,continuous_neg⟩ : C(ℝ × ℝ,ℝ × ℝ))
        (q.comp (planeReflection.comp (q.comp planeReflection))) hneg hcomp hform 2
    rw [hf, pairRelativeHomologyMap_comp P P P _ q
      (fun z hz => planeReflection_preserves_puncture (q (planeReflection z)) (hq (planeReflection z) (planeReflection_preserves_puncture z hz))) hq,
      pairRelativeHomologyMap_comp P P P _ planeReflection
      (fun z hz => hq (planeReflection z) (planeReflection_preserves_puncture z hz)) planeReflection_preserves_puncture,
      pairRelativeHomologyMap_comp P P P planeReflection q planeReflection_preserves_puncture hq]
    rw [planeReflection_relativeHomologyMap_eq_neg_id]
    dsimp only [P] at hqqmap ⊢
    simpa only [Preadditive.neg_comp,Preadditive.comp_neg,Category.id_comp,
      Category.comp_id,neg_neg] using hqqmap
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
  have hreflectionB : ∀ z ∈ B, negation z ∈ B := by
    intro z hz
    simpa only [B,Metric.mem_ball,dist_zero_right,negation,ContinuousMap.coe_mk,
      norm_neg] using hz
  let g : C(B,B) := ⟨fun z => ⟨negation z,hreflectionB z.val z.property⟩,
    (negation.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hg : ∀ z ∈ A, g z ∈ A := by
    intro z hz
    exact hneg z.val hz
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
    change f (e.symm z.val) = e.symm (negation z.val)
    exact hgerm z.val z.property
  have hjg : negation.comp j = j.comp g := by ext z <;> rfl
  have hpr : pairRelativeHomologyMap P P negation hneg 2 =
      (𝟙 (relativeHomology (ℝ × ℝ) P 2)) := planeCentral
  have hgn : pairRelativeHomologyMap A A g hg 2 = (𝟙 (relativeHomology B A 2)) := by
    apply (cancel_mono (pairRelativeHomologyMap A P j hj 2)).1
    calc
      pairRelativeHomologyMap A A g hg 2 ≫ pairRelativeHomologyMap A P j hj 2 =
          pairRelativeHomologyMap A P (j.comp g) (fun z hz => hj (g z) (hg z hz)) 2 :=
        (pairRelativeHomologyMap_comp A A P g j hg hj 2).symm
      _ = pairRelativeHomologyMap A P (negation.comp j)
          (fun z hz => hneg (j z) (hj z hz)) 2 :=
        ReflectionGermProof.pairMap_congr A P _ _ _ _ hjg.symm 2
      _ = pairRelativeHomologyMap A P j hj 2 ≫
          pairRelativeHomologyMap P P negation hneg 2 :=
        pairRelativeHomologyMap_comp A P P j negation hj hneg 2
      _ = ((𝟙 (relativeHomology B A 2))) ≫ pairRelativeHomologyMap A P j hj 2 := by
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
    _ = pairRelativeHomologyMap A C i hi 2 ≫ ((𝟙 (relativeHomology S C 2))) := by
      rw [hgn]
      simp only [Preadditive.comp_neg,Preadditive.neg_comp,Category.comp_id,Category.id_comp]

end CurveComplex.Hyperbolic
