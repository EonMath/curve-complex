import BranchData
import SquareRootContracts

namespace AlternatingSphereCover
noncomputable def rotVector (v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  !₂[(v 0 - Real.sqrt 3 * v 1)/2, (Real.sqrt 3 * v 0 + v 1)/2, v 2]

noncomputable def rotInvVector (v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  !₂[(v 0 + Real.sqrt 3 * v 1)/2, (-Real.sqrt 3 * v 0 + v 1)/2, v 2]

theorem rotVector_mem (x : Sphere) : rotVector x.val ∈ Sphere := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x.val
  have hx : ‖x.val‖=1 := by simp
  rw [hx] at hn
  simp [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs] at hn
  have hnorm : ‖rotVector x.val‖^2=1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [rotVector,Fin.sum_univ_succ,PiLp.toLp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Matrix.cons_val_fin_one,Real.norm_eq_abs,sq_abs,
      Finset.univ_eq_empty,Finset.sum_empty,add_zero]
    linear_combination (x.val 0^2+x.val 1^2)/4 * hs - hn
  change ‖rotVector x.val-0‖=1
  rw [sub_zero]
  nlinarith [norm_nonneg (rotVector x.val)]

theorem rotInvVector_mem (x : Sphere) : rotInvVector x.val ∈ Sphere := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x.val
  have hx : ‖x.val‖=1 := by simp
  rw [hx] at hn
  simp [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs] at hn
  have hnorm : ‖rotInvVector x.val‖^2=1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [rotInvVector,Fin.sum_univ_succ,PiLp.toLp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Matrix.cons_val_fin_one,Real.norm_eq_abs,sq_abs,
      Finset.univ_eq_empty,Finset.sum_empty,add_zero]
    linear_combination (x.val 0^2+x.val 1^2)/4 * hs - hn
  change ‖rotInvVector x.val-0‖=1
  rw [sub_zero]
  nlinarith [norm_nonneg (rotInvVector x.val)]

noncomputable def sphereRot (x : Sphere) : Sphere := ⟨rotVector x.val,rotVector_mem x⟩

noncomputable def sphereRotInv (x : Sphere) : Sphere := ⟨rotInvVector x.val,rotInvVector_mem x⟩

noncomputable def sphereRotation : Sphere ≃ₜ Sphere where
  toFun := sphereRot
  invFun := sphereRotInv
  left_inv := by
    intro x
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
    apply Subtype.ext
    ext i
    fin_cases i
    · dsimp [sphereRotInv,sphereRot,rotVector,rotInvVector]
      linear_combination x.val 0 / 4 * hs
    · dsimp [sphereRotInv,sphereRot,rotVector,rotInvVector]
      linear_combination x.val 1 / 4 * hs
    · rfl
  right_inv := by
    intro x
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
    apply Subtype.ext
    ext i
    fin_cases i
    · dsimp [sphereRotInv,sphereRot,rotVector,rotInvVector]
      linear_combination x.val 0 / 4 * hs
    · dsimp [sphereRotInv,sphereRot,rotVector,rotInvVector]
      linear_combination x.val 1 / 4 * hs
    · rfl
  continuous_toFun := by
    unfold sphereRot
    apply Continuous.subtype_mk
    unfold rotVector
    fun_prop
  continuous_invFun := by
    unfold sphereRotInv
    apply Continuous.subtype_mk
    unfold rotInvVector
    fun_prop

theorem sphereRot_height (x : Sphere) : height (sphereRot x)=height x := rfl

theorem sphereRot_seam (x : Sphere) : seamPolynomial (sphereRot x) = -seamPolynomial x := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hs3 : Real.sqrt (3:ℝ)^3=3*Real.sqrt 3 := by
    nlinarith [congrArg (fun a : ℝ => a*Real.sqrt 3) hs]
  dsimp [seamPolynomial,sphereRot,rotVector]
  ring_nf
  rw [hs,hs3]
  ring

def rawSignMap (f : Sphere → Sphere) (hf : ∀ b, height (f b)=height b) (x : Raw) : Raw :=
  ⟨(f x.val.1,x.val.2.1,x.val.2.2 ^^ x.val.2.1),by simpa only [hf] using x.property⟩

theorem rawSignMap_respects (f : Sphere → Sphere) (hf : ∀ b, height (f b)=height b)
    (hp : ∀ b, seamPolynomial (f b) = -seamPolynomial b) (x y : Raw) (h : Rel x y) :
    Rel (rawSignMap f hf x) (rawSignMap f hf y) := by
  rcases x with ⟨⟨b,a,s⟩,px⟩
  rcases y with ⟨⟨c,d,t⟩,py⟩
  rcases h with ⟨he,h⟩
  change b=c at he
  subst c
  refine ⟨rfl,?_⟩
  rcases h with hb | hl
  · left
    exact ⟨(hf b).trans hb.1, by change seamPolynomial (f b)=0; rw [hp,hb.2,neg_zero]⟩
  · have hl' : (s ^^ (a && decide (0<seamPolynomial b))) =
        (t ^^ (d && decide (0<seamPolynomial b))) := hl
    have px' : if a then 0≤height b else height b≤0 := px
    have py' : if d then 0≤height b else height b≤0 := py
    by_cases hz : seamPolynomial b=0
    · by_cases hb : height b=0
      · left
        exact ⟨(hf b).trans hb,by change seamPolynomial (f b)=0; rw [hp,hz,neg_zero]⟩
      · have had : a=d := by
          cases a <;> cases d
          · rfl
          · exact (hb (le_antisymm px' py')).elim
          · exact (hb (le_antisymm py' px')).elim
          · rfl
        subst d
        have hst : s=t := by simpa [hz] using hl'
        subst t
        exact Or.inr rfl
    · right
      change ((s ^^ a) ^^ (a && decide (0<seamPolynomial (f b)))) =
        ((t ^^ d) ^^ (d && decide (0<seamPolynomial (f b))))
      rw [hp]
      by_cases hpos : 0<seamPolynomial b
      · have hneg : ¬0 < -seamPolynomial b := by linarith
        cases a <;> cases d <;> cases s <;> cases t <;> simp_all <;> linarith
      · have hneg : 0 < -seamPolynomial b := by rcases lt_or_gt_of_ne hz with h|h <;> linarith
        cases a <;> cases d <;> cases s <;> cases t <;> simp_all <;> linarith

noncomputable def rawRotation : Raw ≃ₜ Raw where
  toFun := rawSignMap sphereRot sphereRot_height
  invFun := rawSignMap sphereRotInv (by intro x; rfl)
  left_inv := by
    intro x
    apply Subtype.ext
    change (sphereRotation.symm (sphereRotation x.val.1),x.val.2.1,
        (x.val.2.2 ^^ x.val.2.1) ^^ x.val.2.1)=x.val
    simp
  right_inv := by
    intro x
    apply Subtype.ext
    change (sphereRotation (sphereRotation.symm x.val.1),x.val.2.1,
        (x.val.2.2 ^^ x.val.2.1) ^^ x.val.2.1)=x.val
    simp
  continuous_toFun := by
    unfold rawSignMap
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact sphereRotation.continuous_toFun.comp (continuous_fst.comp continuous_subtype_val)
    apply Continuous.prodMk
    · exact continuous_fst.comp (continuous_snd.comp continuous_subtype_val)
    · exact (continuous_of_discreteTopology : Continuous (fun p : Bool × Bool => p.2 ^^ p.1)).comp
        (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := by
    unfold rawSignMap
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact sphereRotation.continuous_invFun.comp (continuous_fst.comp continuous_subtype_val)
    apply Continuous.prodMk
    · exact continuous_fst.comp (continuous_snd.comp continuous_subtype_val)
    · exact (continuous_of_discreteTopology : Continuous (fun p : Bool × Bool => p.2 ^^ p.1)).comp
        (continuous_snd.comp continuous_subtype_val)

theorem rawRotation_rel (x y : Raw) : Rel x y ↔ Rel (rawRotation x) (rawRotation y) := by
  constructor
  · exact rawSignMap_respects sphereRot sphereRot_height sphereRot_seam x y
  · intro h
    have hp (b : Sphere) : seamPolynomial (sphereRotInv b) = -seamPolynomial b := by
      have hh := sphereRot_seam (sphereRotInv b)
      have he : sphereRot (sphereRotInv b)=b := sphereRotation.apply_symm_apply b
      rw [he] at hh
      linarith
    have hh := rawSignMap_respects sphereRotInv (by intro b; rfl) hp (rawRotation x) (rawRotation y) h
    change Rel (rawRotation.symm (rawRotation x)) (rawRotation.symm (rawRotation y)) at hh
    simpa using hh

noncomputable def totalRotation : Total ≃ₜ Total :=
  Homeomorph.Quotient.congr rawRotation rawRotation_rel

theorem totalRotation_projection (x : Total) :
    projection (totalRotation x)=sphereRotation (projection x) := by
  induction x using Quotient.inductionOn with
  | h x => rfl

def nextBranch (i : Fin 6) : Fin 6 := (![2,5,4,0,1,3]) i

theorem sphereRotation_branchPoint (i : Fin 6) :
    sphereRotation (branchPoint i)=branchPoint (nextBranch i) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  fin_cases i <;> apply Subtype.ext <;> ext j <;> fin_cases j <;>
    norm_num [sphereRotation,sphereRot,rotVector,branchPoint,branchVector,nextBranch] <;>
    nlinarith

end AlternatingSphereCover
