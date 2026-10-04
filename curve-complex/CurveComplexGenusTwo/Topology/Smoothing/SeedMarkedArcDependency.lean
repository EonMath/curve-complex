import Schoenflies.MatchedArc

open Set Topology unitInterval
namespace CurveComplex
open Schoenflies

/-- An endpoint-preserving homeomorphism of the actual free-boundary arc
carrying one specified nonendpoint to another. -/
theorem exists_marked_arcHomeo
    {P : Set Plane} {a b u v : Plane}
    (hP : IsArcBetween P a b)
    (hu : u ∈ P \ {a,b}) (hv : v ∈ P \ {a,b}) :
    ∃ h : ArcHomeo P P a b a b, h.toFun u = v := by
  classical
  have marked (r s : I) (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1) :
      ∃ e : I ≃ₜ I, e 0 = 0 ∧ e 1 = 1 ∧ e r = s := by
    have hd (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (x : I) :
        0 < A*(1-(x:ℝ))+B*(x:ℝ) := by
      rcases lt_or_eq_of_le x.property.2 with hx | hx
      · exact add_pos_of_pos_of_nonneg (mul_pos hA (sub_pos.mpr hx))
          (mul_nonneg hB.le x.property.1)
      · rw [hx]
        simpa using hB
    let φ (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : I → I := fun x =>
      ⟨B*(x:ℝ)/(A*(1-(x:ℝ))+B*(x:ℝ)), by
        constructor
        · exact div_nonneg (mul_nonneg hB.le x.property.1) (hd A B hA hB x).le
        · apply (div_le_one (hd A B hA hB x)).mpr
          have := mul_nonneg hA.le (sub_nonneg.mpr x.property.2)
          linarith⟩
    have hc (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : Continuous (φ A B hA hB) := by
      apply Continuous.subtype_mk
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x
        exact ne_of_gt (hd A B hA hB x)
    have hinv (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (x : I) :
        φ B A hB hA (φ A B hA hB x) = x := by
      apply Subtype.ext
      have hdx := ne_of_gt (hd A B hA hB x)
      have hdy := ne_of_gt (hd B A hB hA (φ A B hA hB x))
      change A*(B*(x:ℝ)/(A*(1-(x:ℝ))+B*(x:ℝ)))/
        (B*(1-B*(x:ℝ)/(A*(1-(x:ℝ))+B*(x:ℝ)))+
          A*(B*(x:ℝ)/(A*(1-(x:ℝ))+B*(x:ℝ)))) = (x:ℝ)
      field_simp [hdx]
      all_goals
        ring_nf
        field_simp [ne_of_gt hA,ne_of_gt hB]
    let A : ℝ := (r:ℝ)*(1-(s:ℝ))
    let B : ℝ := (s:ℝ)*(1-(r:ℝ))
    have hA : 0 < A := mul_pos hr0 (sub_pos.mpr hs1)
    have hB : 0 < B := mul_pos hs0 (sub_pos.mpr hr1)
    let e : I ≃ₜ I := {
      toEquiv := {
        toFun := φ A B hA hB
        invFun := φ B A hB hA
        left_inv := hinv A B hA hB
        right_inv := hinv B A hB hA }
      continuous_toFun := hc A B hA hB
      continuous_invFun := hc B A hB hA }
    refine ⟨e,?_,?_,?_⟩
    · apply Subtype.ext
      simp [e,φ]
    · apply Subtype.ext
      simp [e,φ,ne_of_gt hB]
    · apply Subtype.ext
      change B*(r:ℝ)/(A*(1-(r:ℝ))+B*(r:ℝ)) = (s:ℝ)
      apply (div_eq_iff (ne_of_gt (hd A B hA hB r))).mpr
      dsimp [A,B]
      ring
  obtain ⟨f,hfc,hfi,hfim,hf0,hf1⟩ := hP
  let fi : Plane → ℝ := Function.invFunOn f I
  have hfiC : ContinuousOn fi P := by
    rw [← hfim]
    exact continuousOn_invFunOn_image' isCompact_I hfc hfi
  have hfiMap : MapsTo fi P I := by
    rw [← hfim]
    rintro z ⟨t,ht,rfl⟩
    change Function.invFunOn f I (f t) ∈ I
    rw [hfi.leftInvOn_invFunOn ht]
    exact ht
  let gi : Plane → I := fun z => projIcc 0 1 zero_le_one (fi z)
  let fI : I → Plane := fun t => f t
  have hfIc : Continuous fI := hfc.domRestrict
  have hgif (t : I) : gi (fI t) = t := by
    apply Subtype.ext
    simp [gi,fI,fi,hfi.leftInvOn_invFunOn t.property,
      projIcc_of_mem zero_le_one t.property]
  have hfg (z : Plane) (hz : z ∈ P) : fI (gi z) = z := by
    obtain ⟨t,ht,rfl⟩ := hfim ▸ hz
    change fI (gi (fI ⟨t,ht⟩)) = f t
    rw [hgif]
  let r : I := gi u
  let s : I := gi v
  have hfr : fI r = u := hfg u hu.1
  have hfs : fI s = v := hfg v hv.1
  have hr0 : r ≠ 0 := by
    intro he
    have he' : u = a := by rw [← hfr,he]; exact hf0
    exact hu.2 (by simp [he'])
  have hr1 : r ≠ 1 := by
    intro he
    have he' : u = b := by rw [← hfr,he]; exact hf1
    exact hu.2 (by simp [he'])
  have hs0 : s ≠ 0 := by
    intro he
    have he' : v = a := by rw [← hfs,he]; exact hf0
    exact hv.2 (by simp [he'])
  have hs1 : s ≠ 1 := by
    intro he
    have he' : v = b := by rw [← hfs,he]; exact hf1
    exact hv.2 (by simp [he'])
  obtain ⟨e,he0,he1,hem⟩ := marked r s
    (lt_of_le_of_ne r.property.1 hr0.symm) (lt_of_le_of_ne r.property.2 hr1)
    (lt_of_le_of_ne s.property.1 hs0.symm) (lt_of_le_of_ne s.property.2 hs1)
  let F : Plane → Plane := fun z => fI (e (gi z))
  let G : Plane → Plane := fun z => fI (e.symm (gi z))
  have hgiC : ContinuousOn gi P := continuous_projIcc.continuousOn.comp hfiC
    (fun _ _ => Set.mem_univ _)
  have hFc : ContinuousOn F P := hfIc.continuousOn.comp
    (e.continuous.continuousOn.comp hgiC (fun _ _ => Set.mem_univ _))
    (fun _ _ => Set.mem_univ _)
  have hGc : ContinuousOn G P := hfIc.continuousOn.comp
    (e.symm.continuous.continuousOn.comp hgiC (fun _ _ => Set.mem_univ _))
    (fun _ _ => Set.mem_univ _)
  have hFmap (z) : F z ∈ P := hfim ▸ ⟨e (gi z),(e (gi z)).property,rfl⟩
  have hGmap (z) : G z ∈ P := hfim ▸ ⟨e.symm (gi z),(e.symm (gi z)).property,rfl⟩
  have hleft (z) (hz : z ∈ P) : G (F z) = z := by
    dsimp [G,F]
    rw [hgif,e.symm_apply_apply]
    exact hfg z hz
  have hright (z) (hz : z ∈ P) : F (G z) = z := by
    dsimp [F,G]
    rw [hgif,e.apply_symm_apply]
    exact hfg z hz
  have hga : gi a = 0 := by rw [← hf0]; exact hgif 0
  have hgb : gi b = 1 := by rw [← hf1]; exact hgif 1
  let h : ArcHomeo P P a b a b := {
    toFun := F
    invFun := G
    continuousOn_toFun := hFc
    continuousOn_invFun := hGc
    leftInvOn := hleft
    rightInvOn := hright
    image_eq := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩; exact hFmap w
      · intro hz; exact ⟨G z,hGmap z,hright z hz⟩
    map_left := by dsimp [F]; rw [hga,he0]; exact hf0
    map_right := by dsimp [F]; rw [hgb,he1]; exact hf1 }
  refine ⟨h,?_⟩
  change fI (e r) = v
  rw [hem]
  exact hfs

#print axioms exists_marked_arcHomeo

end CurveComplex
