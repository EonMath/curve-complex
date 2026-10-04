import CurveComplexGenusTwo.Cover.ActualWholeBankSectorSide
import CurveComplexGenusTwo.Topology.TwoClosedSquaresActualSeamMerger
import Mathlib
open Set Metric Bornology
open scoped Topology
namespace AlternatingSphereCover
theorem actual_one_face_source_cut_disk_total_attaching :
  let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
    fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
      closedArcSector (0 : Fin 6) p ∧
      a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
  let Q0 := Quotient (Relation.EqvGen.setoid R0)
  let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
    ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
      a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
      b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
  ∃ F : C(Quotient (Relation.EqvGen.setoid R1),Total),
    Function.Surjective F ∧
    (∀ v, F (Quotient.mk _ (Sum.inl (Quotient.mk _ (Sum.inl v)))) = northDiskFace false v) ∧
    (∀ v, F (Quotient.mk _ (Sum.inl (Quotient.mk _ (Sum.inr v)))) = southDiskFace true v) ∧
    (∀ v, F (Quotient.mk _ (Sum.inr (Quotient.mk _ (Sum.inl v)))) = northDiskFace true v) ∧
    (∀ v, F (Quotient.mk _ (Sum.inr (Quotient.mk _ (Sum.inr v)))) = southDiskFace false v) ∧
    Nonempty (Quotient (Relation.EqvGen.setoid R1) ≃ₜ (unitInterval × unitInterval)) := by
  classical
  let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
    fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
      closedArcSector (0 : Fin 6) p ∧
      a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
  let Q0 := Quotient (Relation.EqvGen.setoid R0)
  let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
    ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
      a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
      b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
  have hzero (p : Sphere) (hp : height p=0) (hi : closedArcSector (0 : Fin 6) p) (s : Bool) :
      northDiskFace s (diskBoundaryPoint p hp) = southDiskFace (!s) (diskBoundaryPoint p hp) := by
    rw [northDiskFace_boundary,southDiskFace_boundary,boundary_attach]
    have hv := hi.2
    change 0 ≤ p.val 1 ∧ 0 ≤ seamA p ∧ 0 ≤ seamB p at hv
    have hn : 0 ≤ seamPolynomial p := by
      rw [seamPolynomial_factor]
      exact mul_nonneg (mul_nonneg hv.1 hv.2.1) hv.2.2
    by_cases hpos : 0 < seamPolynomial p
    · right; cases s <;> simp [hpos]
    · left; exact ⟨hp,le_antisymm (le_of_not_gt hpos) hn⟩
  let g (s : Bool) : C(StandardDisk ⊕ StandardDisk,Total) :=
    ⟨Sum.elim (northDiskFace s) (southDiskFace (!s)),
      continuous_sumElim.mpr ⟨northDiskFace_continuous s,southDiskFace_continuous (!s)⟩⟩
  have hg (s : Bool) (x y) (h : Relation.EqvGen R0 x y) : g s x=g s y := by
    induction h with
    | rel x y h =>
      rcases h with ⟨p,hp,hi,rfl,rfl⟩
      exact hzero p hp hi s
    | refl x => rfl
    | symm x y h ih => exact ih.symm
    | trans x y z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  let B (s : Bool) : C(Q0,Total) := ⟨Quotient.lift (g s) (hg s),(g s).continuous.quotient_lift (hg s)⟩
  let G : C(Q0 ⊕ Q0,Total) := ⟨Sum.elim (B false) (B true),
    continuous_sumElim.mpr ⟨(B false).continuous,(B true).continuous⟩⟩
  have hG (x y) (h : Relation.EqvGen R1 x y) : G x=G y := by
    induction h with
    | rel x y h =>
      rcases h with ⟨p,hp,hi,rfl,rfl⟩
      change northDiskFace false (diskBoundaryPoint p hp)=southDiskFace false (diskBoundaryPoint p hp)
      rw [northDiskFace_boundary,southDiskFace_boundary,boundary_attach]
      right
      have hv := hi.2
      change 0 ≤ p.val 1 ∧ seamA p ≤ 0 ∧ 0 ≤ seamB p at hv
      have hn : seamPolynomial p ≤ 0 := by
        rw [seamPolynomial_factor]
        exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hv.1 hv.2.1) hv.2.2
      simp [not_lt.mpr hn]
    | refl x => rfl
    | symm x y h ih => exact ih.symm
    | trans x y z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  let F : C(Quotient (Relation.EqvGen.setoid R1),Total) :=
    ⟨Quotient.lift G hG,G.continuous.quotient_lift hG⟩
  refine ⟨F,?_,fun v => rfl,fun v => rfl,fun v => rfl,fun v => rfl,?_⟩
  · intro z
    obtain ⟨q,rfl⟩ := fourDiskQuotientHomeomorphTotal.surjective z
    obtain ⟨r,rfl⟩ := Quotient.exists_rep q
    cases r with
    | inl r =>
      rcases r with ⟨s,v⟩
      cases s
      · exact ⟨Quotient.mk _ (Sum.inl (Quotient.mk _ (Sum.inl v))),rfl⟩
      · exact ⟨Quotient.mk _ (Sum.inr (Quotient.mk _ (Sum.inl v))),rfl⟩
    | inr r =>
      rcases r with ⟨s,v⟩
      cases s
      · exact ⟨Quotient.mk _ (Sum.inr (Quotient.mk _ (Sum.inr v))),rfl⟩
      · exact ⟨Quotient.mk _ (Sum.inl (Quotient.mk _ (Sum.inr v))),rfl⟩
  · have diskData :
      let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
        fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
          closedArcSector (0 : Fin 6) p ∧
          a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
      let Q0 := Quotient (Relation.EqvGen.setoid R0)
      let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
        ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
          a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
          b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
      Nonempty (Quotient (Relation.EqvGen.setoid R1) ≃ₜ (unitInterval × unitInterval)) := by
      classical
      let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
        fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
          closedArcSector (0 : Fin 6) p ∧
          a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
      let Q0 := Quotient (Relation.EqvGen.setoid R0)
      let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
        ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
          a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
          b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
      let D := unitInterval × unitInterval
      have cutData : let R : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
        fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
          closedArcSector (0 : Fin 6) p ∧
          a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
      ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
      ∃ H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
      ∃ M : Quotient (Relation.EqvGen.setoid R) ≃ₜ (unitInterval × unitInterval),
        (∀ x, L x=(x 0+x 1/Real.sqrt 3,-x 0+Real.sqrt 3*x 1)) ∧
        (∀ v : StandardDisk, (H v).val=gaugeRescale
          (L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
          (Metric.closedBall (0 : ℝ × ℝ) 1) (L v.val)) ∧
        (∀ p : Sphere, ∀ hp : height p=0,
          closedArcSector (0 : Fin 6) p ↔ ((H (diskBoundaryPoint p hp)).val).1=1) ∧
        (∀ p : Sphere, ∀ hp : height p=0,
          closedArcSector (1 : Fin 6) p ↔ ((H (diskBoundaryPoint p hp)).val).2=1 ∧
            0 ≤ ((H (diskBoundaryPoint p hp)).val).1) ∧
        (∀ v, (M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inl v))).1.val=
            ((H v).val.1+1)/4 ∧
          (M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inl v))).2.val=((H v).val.2+1)/2) ∧
        (∀ v, (M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inr v))).1.val=
            1-((H v).val.1+1)/4 ∧
          (M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inr v))).2.val=((H v).val.2+1)/2) := by
        classical
        let R : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
          fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
            closedArcSector (0 : Fin 6) p ∧
            a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
        let D := unitInterval × unitInterval
        have chData : ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
          ∃ H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
          ∃ N : Set.range (northDiskFace false) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
          ∃ S : Set.range (southDiskFace true) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
            (∀ x, L x=(x 0+x 1/Real.sqrt 3,-x 0+Real.sqrt 3*x 1)) ∧
            (∀ v : StandardDisk, (H v).val=gaugeRescale
              (L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
              (Metric.closedBall (0 : ℝ × ℝ) 1) (L v.val)) ∧
            (∀ v : StandardDisk, N ⟨northDiskFace false v,⟨v,rfl⟩⟩=H v) ∧
            (∀ v : StandardDisk, S ⟨southDiskFace true v,⟨v,rfl⟩⟩=H v) ∧
            (∀ p : Sphere, ∀ hp : height p=0,
              closedArcSector (0 : Fin 6) p ↔ ((H (diskBoundaryPoint p hp)).val).1=1) ∧
            (∀ p : Sphere, ∀ hp : height p=0,
              closedArcSector (1 : Fin 6) p ↔
                ((H (diskBoundaryPoint p hp)).val).2=1 ∧
                0 ≤ ((H (diskBoundaryPoint p hp)).val).1) := by
          obtain ⟨L,H,hL,hcone,hH,⟨N,S,hN,hS⟩,hside⟩ := actual_whole_bank_exact_sector_square_side
          have hgauge (x : EuclideanSpace ℝ (Fin 2)) :
              gauge (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (L x) = ‖x‖ := by
            have he : {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • L x ∈ L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} =
                {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
              ext r
              simp only [mem_setOf_eq]
              constructor
              · rintro ⟨hr,z,hz,hzx⟩
                have hz' : z = r⁻¹ • x := L.injective (by simpa using hzx)
                exact ⟨hr,hz' ▸ hz⟩
              · rintro ⟨hr,hx⟩
                exact ⟨hr,r⁻¹ • x,hx,by simp⟩
            rw [gauge_def',he,← gauge_def']
            simpa using gauge_closedBall (E := EuclideanSpace ℝ (Fin 2)) (by norm_num : 0  ≤  (1 : ℝ)) x
          have hs : 0<Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
          have hs2 : Real.sqrt (3 : ℝ)^2=3 := Real.sq_sqrt (by norm_num)
          have cone (p : Sphere) (hp : height p=0) :
              closedArcSector (1 : Fin 6) p ↔
                0 ≤ (L (horizontal p)).1 ∧ (L (horizontal p)).1 ≤ (L (horizontal p)).2 := by
            have eX : Real.sqrt 3*(L (horizontal p)).1=seamB p := by
              rw [hL]
              dsimp [horizontal,seamB]
              field_simp [hs.ne']
            have eYX : Real.sqrt 3*((L (horizontal p)).2-(L (horizontal p)).1)=-2*seamA p := by
              rw [hL]
              dsimp [horizontal,seamA]
              field_simp [hs.ne']
              ring_nf
              rw [hs2]
              ring
            change (height p=0 ∧ 0 ≤ p.val 1 ∧ seamA p ≤ 0 ∧ 0 ≤ seamB p) ↔ _
            rw [hp]
            simp only [true_and]
            constructor
            · rintro ⟨hy,hA,hB⟩
              have hx : 0 ≤ (L (horizontal p)).1 :=
                nonneg_of_mul_nonneg_left (by rw [mul_comm,eX];exact hB) hs
              have hxy : 0 ≤ (L (horizontal p)).2-(L (horizontal p)).1 :=
                nonneg_of_mul_nonneg_left (by rw [mul_comm,eYX];linarith) hs
              exact ⟨hx,by linarith⟩
            · rintro ⟨hx,hxy⟩
              have hB : 0 ≤ seamB p := eX ▸ mul_nonneg hs.le hx
              have hA : seamA p ≤ 0 := by
                have h := mul_nonneg hs.le (sub_nonneg.mpr hxy)
                rw [eYX] at h
                linarith
              refine ⟨?_,hA,hB⟩
              dsimp [seamA,seamB] at hA hB
              linarith
          refine ⟨L,H,N,S,hL,hH,hN,hS,hside,?_⟩
          intro p hp
          have hn : ‖horizontal p‖=1 := by
            have hc := sphere_coordinate_squares p
            have hn2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (horizontal p)
            simp [Fin.sum_univ_succ,horizontal,Real.norm_eq_abs,sq_abs] at hn2
            change ‖horizontal p‖^2=(p.val 0)^2+(p.val 1)^2 at hn2
            have hp2 : p.val 2=0 := hp
            rw [hp2] at hc
            nlinarith only [hc,hn2,norm_nonneg (horizontal p)]
          have hz : L (horizontal p)≠0 := by
            intro hz
            have hh : horizontal p=0 := L.injective (by simpa using hz)
            rw [hh,norm_zero] at hn
            norm_num at hn
          have hnpos : 0<‖L (horizontal p)‖ := norm_pos_iff.mpr hz
          have hvalue : (H (diskBoundaryPoint p hp)).val=
              (1/‖L (horizontal p)‖) • L (horizontal p) := by
            rw [hH]
            change gaugeRescale (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
              (closedBall (0 : ℝ × ℝ) 1) (L (horizontal p))=_
            rw [gaugeRescale_def,hgauge,hn,gauge_closedBall (by norm_num : (0 : ℝ) ≤ 1),div_one]
          rw [hvalue]
          change closedArcSector (1 : Fin 6) p ↔
            (1/‖L (horizontal p)‖)*(L (horizontal p)).2=1 ∧
              0 ≤ (1/‖L (horizontal p)‖)*(L (horizontal p)).1
          rw [one_div_mul_eq_div,div_eq_one_iff_eq hnpos.ne',
            one_div_mul_eq_div,le_div_iff₀ hnpos,zero_mul,cone p hp]
          constructor
          · rintro ⟨hx,hxy⟩
            have hy : 0 ≤ (L (horizontal p)).2 := hx.trans hxy
            refine ⟨?_,hx⟩
            rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,
              abs_of_nonneg hx,abs_of_nonneg hy,max_eq_right hxy]
          · rintro ⟨hy,hx⟩
            refine ⟨hx,?_⟩
            rw [hy,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hx]
            exact le_max_left _ _
        obtain ⟨L,H,N,S,hL,hH,hN,hS,hside,hsector1⟩ := chData
        have mData : let D := unitInterval × unitInterval
          ∃ f : C(D ⊕ D,D), Function.Surjective f ∧
            Function.Injective (fun x => f (Sum.inl x)) ∧
            Function.Injective (fun y => f (Sum.inr y)) ∧
            (∀ x y, f (Sum.inl x)=f (Sum.inr y) ↔
              x.1=1 ∧ y.1=0 ∧ x.2=y.2) ∧
            ∃ H : Quotient (Setoid.ker f) ≃ₜ D,
              (∀ x, (f (Sum.inl x)).1.val=x.1.val/2 ∧ (f (Sum.inl x)).2=x.2) ∧
              (∀ y, (f (Sum.inr y)).1.val=(y.1.val+1)/2 ∧ (f (Sum.inr y)).2=y.2) ∧
              (∀ r, H (Quotient.mk (Setoid.ker f) r)=f r) := by
          classical
          let D := unitInterval × unitInterval
          let L : D → D := fun x =>
            (⟨x.1.val / 2, ⟨by linarith [x.1.property.1], by linarith [x.1.property.2]⟩⟩, x.2)
          let R : D → D := fun x =>
            (⟨(x.1.val + 1) / 2, ⟨by linarith [x.1.property.1], by linarith [x.1.property.2]⟩⟩, x.2)
          have hL : Continuous L := by
            apply Continuous.prodMk
            · apply Continuous.subtype_mk
              exact (continuous_subtype_val.comp continuous_fst).div_const 2
            · exact continuous_snd
          have hR : Continuous R := by
            apply Continuous.prodMk
            · apply Continuous.subtype_mk
              exact ((continuous_subtype_val.comp continuous_fst).add_const 1).div_const 2
            · exact continuous_snd
          let f : C(D ⊕ D,D) := ⟨Sum.elim L R, hL.sumElim hR⟩
          have hs : Function.Surjective f := by
            intro x
            by_cases hx : x.1.val ≤ 1/2
            · refine ⟨Sum.inl (⟨2*x.1.val, ⟨by linarith [x.1.property.1], by linarith⟩⟩,x.2), ?_⟩
              apply Prod.ext
              · apply Subtype.ext
                dsimp [f,L]
                ring
              · rfl
            · refine ⟨Sum.inr (⟨2*x.1.val-1, ⟨by linarith, by linarith [x.1.property.2]⟩⟩,x.2), ?_⟩
              apply Prod.ext
              · apply Subtype.ext
                dsimp [f,R]
                ring
              · rfl
          have hiL : Function.Injective (fun x => f (Sum.inl x)) := by
            intro x y h
            apply Prod.ext
            · apply Subtype.ext
              have h₁ := congrArg (fun z : D => z.1.val) h
              dsimp [f,L] at h₁
              linarith
            · simpa [f,L,R] using congrArg (fun z : D => z.2) h
          have hiR : Function.Injective (fun x => f (Sum.inr x)) := by
            intro x y h
            apply Prod.ext
            · apply Subtype.ext
              have h₁ := congrArg (fun z : D => z.1.val) h
              dsimp [f,R] at h₁
              linarith
            · simpa [f,L,R] using congrArg (fun z : D => z.2) h
          have hseam (x y : D) : f (Sum.inl x) = f (Sum.inr y) ↔
              x.1 = 1 ∧ y.1 = 0 ∧ x.2 = y.2 := by
            constructor
            · intro h
              have h₁ := congrArg (fun z : D => z.1.val) h
              dsimp [f,L,R] at h₁
              refine ⟨Subtype.ext ?_, Subtype.ext ?_, by simpa [f,L,R] using congrArg (fun z : D => z.2) h⟩
              · change x.1.val = 1
                linarith [x.1.property.2,y.1.property.1]
              · change y.1.val = 0
                linarith [x.1.property.2,y.1.property.1]
            · rintro ⟨hx,hy,h₂⟩
              apply Prod.ext
              · apply Subtype.ext
                dsimp [f,L,R]
                rw [hx,hy]
                norm_num
              · exact h₂
          let q : Quotient (Setoid.ker f) → D := Quotient.lift f (fun x y h => h)
          have hq : Continuous q := f.continuous.quotient_lift _
          have hiq : Function.Injective q := by
            intro x y h
            induction x using Quotient.inductionOn with
            | _ x =>
              induction y using Quotient.inductionOn with
              | _ y => exact Quotient.sound h
          have hsq : Function.Surjective q := by
            intro y
            obtain ⟨x,hx⟩ := hs y
            exact ⟨Quotient.mk (Setoid.ker f) x,hx⟩
          let e := Equiv.ofBijective q ⟨hiq,hsq⟩
          let H : Quotient (Setoid.ker f) ≃ₜ D :=
            (show Continuous (e : Quotient (Setoid.ker f) → D) from hq).homeoOfEquivCompactToT2
          exact ⟨f,hs,hiL,hiR,hseam,H,fun _ => ⟨rfl,rfl⟩,
            fun _ => ⟨rfl,rfl⟩,fun _ => rfl⟩
        obtain ⟨m,hm,hml,hmr,hseam,He,hmL,hmR,hmpin⟩ := mData
        have qData : ∃ Q : Metric.closedBall (0 : ℝ × ℝ) 1 ≃ₜ (unitInterval × unitInterval),
          ∀ z, (Q z).1.val = (z.val.1 + 1)/2 ∧ (Q z).2.val = (z.val.2 + 1)/2 := by
          have bounds (z : Metric.closedBall (0 : ℝ × ℝ) 1) :
              (-1 ≤ z.val.1 ∧ z.val.1 ≤ 1) ∧ (-1 ≤ z.val.2 ∧ z.val.2 ≤ 1) := by
            have h := z.property
            simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le] using h
          let F : Metric.closedBall (0 : ℝ × ℝ) 1 → unitInterval × unitInterval :=
            fun z => (⟨(z.val.1+1)/2,⟨by linarith [(bounds z).1.1],by linarith [(bounds z).1.2]⟩⟩,
              ⟨(z.val.2+1)/2,⟨by linarith [(bounds z).2.1],by linarith [(bounds z).2.2]⟩⟩)
          let G : unitInterval × unitInterval → Metric.closedBall (0 : ℝ × ℝ) 1 :=
            fun z => ⟨(2*z.1.val-1,2*z.2.val-1),by
              simp only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
              exact ⟨⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩,
                ⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩⟩
          have hF : Continuous F := by
            apply Continuous.prodMk
            · apply Continuous.subtype_mk
              exact ((continuous_fst.comp continuous_subtype_val).add_const 1).div_const 2
            · apply Continuous.subtype_mk
              exact ((continuous_snd.comp continuous_subtype_val).add_const 1).div_const 2
          have hG : Continuous G := by
            apply Continuous.subtype_mk
            apply Continuous.prodMk
            · exact ((continuous_subtype_val.comp continuous_fst).const_mul 2).sub continuous_const
            · exact ((continuous_subtype_val.comp continuous_snd).const_mul 2).sub continuous_const
          let Q : Metric.closedBall (0 : ℝ × ℝ) 1 ≃ₜ (unitInterval × unitInterval) := {
            toFun := F
            invFun := G
            left_inv := by
              intro z
              apply Subtype.ext
              apply Prod.ext
              all_goals (dsimp [F,G]; ring)
            right_inv := by
              intro z
              apply Prod.ext
              all_goals (apply Subtype.ext; dsimp [F,G]; ring)
            continuous_toFun := hF
            continuous_invFun := hG }
          exact ⟨Q,fun _ => ⟨rfl,rfl⟩⟩
        obtain ⟨Q,hQ⟩ := qData
        let flip : D ≃ₜ D := Homeomorph.prodCongr unitInterval.symmHomeomorph
          (Homeomorph.refl unitInterval)
        let n := H.trans Q
        let s := n.trans flip
        let B := Homeomorph.sumCongr n s
        let F : C(StandardDisk ⊕ StandardDisk,D) := m.comp ⟨B,B.continuous⟩
        have hFl : Function.Injective (fun v => F (Sum.inl v)) := hml.comp n.injective
        have hFr : Function.Injective (fun v => F (Sum.inr v)) := hmr.comp s.injective
        have hgauge (x : EuclideanSpace ℝ (Fin 2)) :
            gauge (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (L x) = ‖x‖ := by
          have he : {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • L x ∈ L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
            ext r
            simp only [mem_setOf_eq]
            constructor
            · rintro ⟨hr,z,hz,hzx⟩
              have hz' : z = r⁻¹ • x := L.injective (by simpa using hzx)
              exact ⟨hr,hz' ▸ hz⟩
            · rintro ⟨hr,hx⟩
              exact ⟨hr,r⁻¹ • x,hx,by simp⟩
          rw [gauge_def',he,← gauge_def']
          simpa using gauge_closedBall (E := EuclideanSpace ℝ (Fin 2)) (by norm_num : 0 ≤ (1 : ℝ)) x
        have hboundary (v : StandardDisk) (hv : ((H v).val).1 = 1) : ‖v.val‖ = 1 := by
          have hnorm : ‖(H v).val‖ = 1 := by
            have hle : ‖(H v).val‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using (H v).property
            rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
            have hle' : |(H v).val.2| ≤ 1 := by
              have ha : |(H v).val.1| ≤ 1 ∧ |(H v).val.2| ≤ 1 := by
                simpa only [Prod.norm_def,Real.norm_eq_abs,max_le_iff] using hle
              exact ha.2
            rw [hv]
            simpa using max_eq_left hle'
          have hne : L v.val ≠ 0 := by
            intro he
            have hz : (H v).val = 0 := by rw [hH v,he,gaugeRescale_zero]
            have := congrArg Prod.fst hz
            simpa [hv] using this
          have ht : gauge (closedBall (0 : ℝ × ℝ) 1) (L v.val) ≠ 0 := by
            simpa [gauge_closedBall, norm_ne_zero_iff] using hne
          have h := gauge_gaugeRescale' (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ht
          rw [← hH v,hgauge] at h
          simpa [gauge_closedBall,hnorm] using h.symm
        have hparam (v : StandardDisk) (hv : ((H v).val).1 = 1) :
            ∃ p : Sphere, ∃ hp : height p = 0,
              closedArcSector (0 : Fin 6) p ∧ v = diskBoundaryPoint p hp := by
          have hnorm := hboundary v hv
          let p := northHemisphereDiskHomeomorph.symm (coordinateDiskClosedBallHomeomorph.symm v)
          have hv' : v = coordinateDiskClosedBallHomeomorph (northHemisphereDiskHomeomorph p) := by
            dsimp [p]
            simp
          have hhor : v.val = horizontal p.val := congrArg Subtype.val hv'
          have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hhor
          have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hhor
          change v.val 0 = p.val.val 0 at h0
          change v.val 1 = p.val.val 1 at h1
          have hs := sphere_coordinate_squares p.val
          have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) v.val
          simp only [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,Fin.sum_univ_zero,add_zero] at hn
          change ‖v.val‖ ^ 2 = (v.val 0)^2 + (v.val 1)^2 at hn
          rw [hnorm,h0,h1] at hn
          have hp : height p.val = 0 := by
            change p.val.val 2 = 0
            nlinarith only [hs,hn]
          have hparam : v = diskBoundaryPoint p.val hp := hv'
          refine ⟨p.val,hp,?_,hparam⟩
          apply (hside p.val hp).mpr
          rw [← hparam]
          exact hv
        have hcross (v w : StandardDisk) : F (Sum.inl v)=F (Sum.inr w) ↔
            ∃ p : Sphere, ∃ hp : height p=0,
              closedArcSector (0 : Fin 6) p ∧ v=diskBoundaryPoint p hp ∧ w=diskBoundaryPoint p hp := by
          change m (Sum.inl (n v))=m (Sum.inr (s w)) ↔ _
          rw [hseam]
          constructor
          · rintro ⟨hv,hw,hvw⟩
            have hv' := congrArg Subtype.val hv
            have hw' := congrArg Subtype.val hw
            have hvw' := congrArg Subtype.val hvw
            change (Q (H v)).1.val=1 at hv'
            change 1-(Q (H w)).1.val=0 at hw'
            change (Q (H v)).2.val=(Q (H w)).2.val at hvw'
            rw [(hQ (H v)).1] at hv'
            rw [(hQ (H w)).1] at hw'
            rw [(hQ (H v)).2,(hQ (H w)).2] at hvw'
            have hvside : (H v).val.1=1 := by linarith
            have hwside : (H w).val.1=1 := by linarith
            have he : v=w := by
              apply H.injective
              apply Subtype.ext
              apply Prod.ext
              · exact hvside.trans hwside.symm
              · linarith
            obtain ⟨p,hp,hi,hvparam⟩ := hparam v hvside
            exact ⟨p,hp,hi,hvparam,he.symm.trans hvparam⟩
          · rintro ⟨p,hp,hi,rfl,rfl⟩
            have hright := (hside p hp).mp hi
            refine ⟨?_,?_,?_⟩ <;> apply Subtype.ext
            · change (Q (H (diskBoundaryPoint p hp))).1.val=1
              rw [(hQ _).1,hright];norm_num
            · change 1-(Q (H (diskBoundaryPoint p hp))).1.val=0
              rw [(hQ _).1,hright];norm_num
            · rfl
        have hgenerated (a b : StandardDisk ⊕ StandardDisk) :
            F a = F b ↔ Relation.EqvGen R a b := by
          constructor
          · intro hab
            cases a with
            | inl v =>
              cases b with
              | inl w =>
                have he := hFl hab
                subst w
                exact .refl _
              | inr w =>
                obtain ⟨p,hp,hi,hv,hw⟩ := (hcross v w).mp hab
                exact .rel _ _ ⟨p,hp,hi,congrArg Sum.inl hv,congrArg Sum.inr hw⟩
            | inr v =>
              cases b with
              | inl w =>
                obtain ⟨p,hp,hi,hw,hv⟩ := (hcross w v).mp hab.symm
                exact .symm _ _ (.rel _ _ ⟨p,hp,hi,congrArg Sum.inl hw,congrArg Sum.inr hv⟩)
              | inr w =>
                have he := hFr hab
                subst w
                exact .refl _
          · intro hab
            induction hab with
            | rel a b h =>
              rcases h with ⟨p,hp,hi,rfl,rfl⟩
              exact (hcross _ _).mpr ⟨p,hp,hi,rfl,rfl⟩
            | refl a => rfl
            | symm a b h ih => exact ih.symm
            | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
        let HF : Quotient (Setoid.ker F) ≃ₜ D :=
          (Homeomorph.Quotient.congr B (by intros;rfl)).trans He
        let M : Quotient (Relation.EqvGen.setoid R) ≃ₜ D :=
          (Homeomorph.Quotient.congr (Homeomorph.refl (StandardDisk ⊕ StandardDisk))
            (fun a b => (hgenerated a b).symm)).trans HF
        have hpinL (v : StandardDisk) : M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inl v))=
            m (Sum.inl (n v)) := by
          change He (Quotient.mk (Setoid.ker m) (Sum.inl (n v)))=_
          exact hmpin _
        have hpinR (v : StandardDisk) : M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inr v))=
            m (Sum.inr (s v)) := by
          change He (Quotient.mk (Setoid.ker m) (Sum.inr (s v)))=_
          exact hmpin _
        refine ⟨L,H,M,hL,hH,hside,hsector1,?_,?_⟩
        · intro v
          rw [hpinL]
          constructor
          · rw [(hmL (n v)).1]
            change (Q (H v)).1.val/2=((H v).val.1+1)/4
            rw [(hQ _).1];ring
          · rw [(hmL (n v)).2]
            exact (hQ _).2
        · intro v
          rw [hpinR]
          constructor
          · rw [(hmR (s v)).1]
            change ((1-(Q (H v)).1.val)+1)/2=1-((H v).val.1+1)/4
            rw [(hQ _).1];ring
          · rw [(hmR (s v)).2]
            exact (hQ _).2
      obtain ⟨L,H,M,hL,hH,hside,hsector1,hML,hMR⟩ := cutData
      have quarterData : let D := unitInterval × unitInterval
        ∃ f : C(D ⊕ D,D), Function.Surjective f ∧
          Function.Injective (fun x => f (Sum.inl x)) ∧
          Function.Injective (fun y => f (Sum.inr y)) ∧
          (∀ x y, f (Sum.inl x)=f (Sum.inr y) ↔
            x.2.val=1 ∧ y.2.val=1 ∧ x.1.val+y.1.val=1 ∧
            (1/4 : ℝ)≤x.1.val ∧ x.1.val≤1/2) ∧
          Nonempty (Quotient (Setoid.ker f) ≃ₜ D) := by
        classical
        let D := unitInterval × unitInterval
        have gData : ∃ G : (unitInterval × unitInterval) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
          (∀ v, ((G v).val).1 = 1 ↔
            v.2.val = 1 ∧ (1/4 : ℝ) ≤ v.1.val ∧ v.1.val ≤ 1/2) ∧
          (∀ v, v.2.val = 1 → (1/4 : ℝ) ≤ v.1.val → v.1.val ≤ 1/2 →
            ((G v).val).2 = 8*v.1.val-3) := by
          let s : Set (ℝ × ℝ) := Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)
          let t : Set (ℝ × ℝ) := closedBall 0 1
          have hsc : Convex ℝ s := (convex_Icc _ _).prod (convex_Icc _ _)
          have hscompact : IsCompact s := isCompact_Icc.prod isCompact_Icc
          have hs0 : s ∈ 𝓝 (0 : ℝ × ℝ) := by
            have h := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
              (show (0 : ℝ × ℝ) ∈ Ioo (-7/8 : ℝ) (1/8) ×ˢ Ioo (-3/8 : ℝ) (5/8) from by norm_num)
            exact Filter.mem_of_superset h (by rintro z ⟨hz,hw⟩; exact ⟨⟨hz.1.le,hz.2.le⟩,⟨hw.1.le,hw.2.le⟩⟩)
          have hsb : IsVonNBounded ℝ s := NormedSpace.isVonNBounded_of_isBounded ℝ hscompact.isBounded
          have htc : Convex ℝ t := convex_closedBall _ _
          have ht0 : t ∈ 𝓝 (0 : ℝ × ℝ) := closedBall_mem_nhds _ (by norm_num)
          have htb : IsVonNBounded ℝ t := NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_closedBall
          let g := gaugeRescaleHomeomorph s t hsc hs0 hsb htc ht0 htb
          have himage : g '' s = t := by
            have h := image_gaugeRescaleHomeomorph_closure hsc hs0 hsb htc ht0 htb
            rw [hscompact.isClosed.closure_eq,isClosed_closedBall.closure_eq] at h
            exact h
          let f : (unitInterval × unitInterval) → ↥s := fun v =>
            ⟨(v.2.val-7/8,v.1.val-3/8),by
              exact ⟨⟨by linarith [v.2.property.1],by linarith [v.2.property.2]⟩,
                ⟨by linarith [v.1.property.1],by linarith [v.1.property.2]⟩⟩⟩
          let fi : ↥s → (unitInterval × unitInterval) := fun z =>
            (⟨z.val.2+3/8,⟨by linarith [z.property.2.1],by linarith [z.property.2.2]⟩⟩,
              ⟨z.val.1+7/8,⟨by linarith [z.property.1.1],by linarith [z.property.1.2]⟩⟩)
          let e : (unitInterval × unitInterval) ≃ₜ ↥s := {
            toFun := f
            invFun := fi
            left_inv := by
              intro v
              apply Prod.ext <;> apply Subtype.ext
              all_goals (dsimp [f,fi];ring)
            right_inv := by
              intro z
              apply Subtype.ext
              apply Prod.ext
              all_goals (dsimp [f,fi];ring)
            continuous_toFun := by
              apply Continuous.subtype_mk
              apply Continuous.prodMk
              · exact (continuous_subtype_val.comp continuous_snd).sub continuous_const
              · exact (continuous_subtype_val.comp continuous_fst).sub continuous_const
            continuous_invFun := by
              apply Continuous.prodMk
              · apply Continuous.subtype_mk
                exact (continuous_snd.comp continuous_subtype_val).add_const _
              · apply Continuous.subtype_mk
                exact (continuous_fst.comp continuous_subtype_val).add_const _ }
          let G := e.trans ((g.image s).trans (Homeomorph.setCongr himage))
          have hval (v : unitInterval × unitInterval) :
              (G v).val = gaugeRescale s t (v.2.val-7/8,v.1.val-3/8) := rfl
          have hfront (v : unitInterval × unitInterval) (hv : v.2.val=1) :
              (v.2.val-7/8,v.1.val-3/8) ∈ frontier s := by
            change _ ∈ closure s ∧ _ ∉ interior s
            refine ⟨?_,?_⟩
            · rw [hscompact.isClosed.closure_eq]
              exact (f v).property
            · intro hi
              have hfst : v.2.val-7/8 ∈ interior (Icc (-7/8 : ℝ) (1/8)) := by
                change _ ∈ interior (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)) at hi
                rw [interior_prod_eq] at hi
                exact hi.1
              rw [interior_Icc] at hfst
              rw [hv] at hfst
              norm_num at hfst
          have htopgauge (v : unitInterval × unitInterval) (hv : v.2.val=1) :
              gauge s (v.2.val-7/8,v.1.val-3/8)=1 :=
            (gauge_eq_one_iff_mem_frontier hsc hs0).mpr (hfront v hv)
          have hnorm (v : unitInterval × unitInterval)
              (hv : v.2.val=1) (hl : (1/4 : ℝ) ≤ v.1.val) (hr : v.1.val≤1/2) :
              ‖(v.2.val-7/8,v.1.val-3/8)‖ = (1/8 : ℝ) := by
            rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,hv]
            norm_num
            rw [abs_le]
            constructor <;> linarith
          have hright (v : unitInterval × unitInterval)
              (hv : v.2.val=1) (hl : (1/4 : ℝ) ≤ v.1.val) (hr : v.1.val≤1/2) :
              (G v).val=(1,8*v.1.val-3) := by
            rw [hval,gaugeRescale_def,htopgauge v hv]
            have hgt : gauge t (v.2.val-7/8,v.1.val-3/8) = (1/8 : ℝ) := by
              simpa only [t,gauge_closedBall (by norm_num : 0 ≤ (1 : ℝ)),div_one] using hnorm v hv hl hr
            rw [hgt]
            apply Prod.ext <;> dsimp
            · rw [hv]; norm_num
            · ring
          refine ⟨G,?_,?_⟩
          · intro v
            constructor
            · intro hv
              let z : ℝ × ℝ := (v.2.val-7/8,v.1.val-3/8)
              have hle : ‖(G v).val‖≤1 := by
                simpa only [t,mem_closedBall,dist_zero_right] using (G v).property
              have hnG : ‖(G v).val‖=1 := by
                have h2 : |(G v).val.2|≤1 := by
                  have h' : |(G v).val.1|≤1 ∧ |(G v).val.2|≤1 := by
                    simpa only [Prod.norm_def,Real.norm_eq_abs,max_le_iff] using hle
                  exact h'.2
                rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,hv]
                simpa using max_eq_left h2
              have hz : z ≠ 0 := by
                intro he
                have hh : (G v).val=0 := by rw [hval]; change gaugeRescale s t z=0; rw [he,gaugeRescale_zero]
                have hf := congrArg Prod.fst hh
                simpa [hv] using hf
              have hgt : gauge t z=‖z‖ := by simp only [t,gauge_closedBall (by norm_num : 0 ≤ (1 : ℝ)),div_one]
              have hgs : gauge s z=1 := by
                have h := gauge_gaugeRescale' s (show gauge t z≠0 from by rw [hgt]; exact norm_ne_zero_iff.mpr hz)
                change gauge t (gaugeRescale s t z)=gauge s z at h
                rw [← hval v] at h
                simpa only [t,gauge_closedBall (by norm_num : 0 ≤ (1 : ℝ)),div_one,hnG] using h.symm
              have hfirst : z.1=‖z‖ := by
                have hf := congrArg Prod.fst (hval v)
                change (G v).val.1=(gauge s z/gauge t z)*z.1 at hf
                rw [hv,hgs,hgt,one_div_mul_eq_div] at hf
                exact ((div_eq_one_iff_eq (norm_ne_zero_iff.mpr hz)).mp hf.symm)
              have hcone : 0≤z.1 ∧ |z.2|≤z.1 := by
                refine ⟨hfirst.symm ▸ norm_nonneg z,?_⟩
                rw [hfirst,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
                exact le_max_right _ _
              have hmem : z∈s := (f v).property
              have hzfirst : z.1=1/8 := by
                by_contra hne
                have hlt : z.1<1/8 := lt_of_le_of_ne hmem.1.2 hne
                have hinter : z∈interior s := by
                  rw [interior_prod_eq,interior_Icc,interior_Icc]
                  have hcone' := abs_le.mp hcone.2
                  constructor
                  · exact ⟨by linarith [hcone.1],hlt⟩
                  · exact ⟨by linarith [hcone'.1],by linarith [hcone'.2]⟩
                have hglt := (gauge_lt_one_iff_mem_interior hsc hs0).mpr hinter
                linarith
              have hc := abs_le.mp hcone.2
              change v.2.val-7/8=1/8 at hzfirst
              change -(v.2.val-7/8)≤v.1.val-3/8 ∧ v.1.val-3/8≤v.2.val-7/8 at hc
              exact ⟨by linarith,by linarith [hc.1],by linarith [hc.2]⟩
            · rintro ⟨hv,hl,hr⟩
              exact congrArg Prod.fst (hright v hv hl hr)
          · intro v hv hl hr
            exact congrArg Prod.snd (hright v hv hl hr)
        obtain ⟨G,hside,hparam⟩ := gData
        have qData : ∃ Q : Metric.closedBall (0 : ℝ × ℝ) 1 ≃ₜ D,
            ∀ z, (Q z).1.val=(z.val.1+1)/2 ∧ (Q z).2.val=(z.val.2+1)/2 := by
          have bounds (z : Metric.closedBall (0 : ℝ × ℝ) 1) :
              (-1 ≤ z.val.1 ∧ z.val.1 ≤ 1) ∧ (-1 ≤ z.val.2 ∧ z.val.2 ≤ 1) := by
            have h := z.property
            simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le] using h
          let F : Metric.closedBall (0 : ℝ × ℝ) 1 → unitInterval × unitInterval :=
            fun z => (⟨(z.val.1+1)/2,⟨by linarith [(bounds z).1.1],by linarith [(bounds z).1.2]⟩⟩,
              ⟨(z.val.2+1)/2,⟨by linarith [(bounds z).2.1],by linarith [(bounds z).2.2]⟩⟩)
          let G : unitInterval × unitInterval → Metric.closedBall (0 : ℝ × ℝ) 1 :=
            fun z => ⟨(2*z.1.val-1,2*z.2.val-1),by
              simp only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
              exact ⟨⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩,
                ⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩⟩
          have hF : Continuous F := by
            apply Continuous.prodMk
            · apply Continuous.subtype_mk
              exact ((continuous_fst.comp continuous_subtype_val).add_const 1).div_const 2
            · apply Continuous.subtype_mk
              exact ((continuous_snd.comp continuous_subtype_val).add_const 1).div_const 2
          have hG : Continuous G := by
            apply Continuous.subtype_mk
            apply Continuous.prodMk
            · exact ((continuous_subtype_val.comp continuous_fst).const_mul 2).sub continuous_const
            · exact ((continuous_subtype_val.comp continuous_snd).const_mul 2).sub continuous_const
          let Q : Metric.closedBall (0 : ℝ × ℝ) 1 ≃ₜ (unitInterval × unitInterval) := {
            toFun := F
            invFun := G
            left_inv := by
              intro z
              apply Subtype.ext
              apply Prod.ext
              all_goals (dsimp [F,G]; ring)
            right_inv := by
              intro z
              apply Prod.ext
              all_goals (apply Subtype.ext; dsimp [F,G]; ring)
            continuous_toFun := hF
            continuous_invFun := hG }
          exact ⟨Q,fun _ => ⟨rfl,rfl⟩⟩
        obtain ⟨Q,hQ⟩ := qData
        let flip : D ≃ₜ D := Homeomorph.prodCongr unitInterval.symmHomeomorph
          (Homeomorph.refl unitInterval)
        let n := G.trans Q
        let s := ((flip.trans G).trans Q).trans flip
        let B := Homeomorph.sumCongr n s
        obtain ⟨m,hm,hml,hmr,hseam,⟨He⟩⟩ := two_closed_squares_actual_seam_merger
        let f : C(D ⊕ D,D) := m.comp ⟨B,B.continuous⟩
        refine ⟨f,hm.comp B.surjective,hml.comp n.injective,hmr.comp s.injective,?_,?_⟩
        · intro x y
          change m (Sum.inl (n x))=m (Sum.inr (s y)) ↔ _
          rw [hseam]
          constructor
          · rintro ⟨hx,hy,hxy⟩
            have hx' := congrArg Subtype.val hx
            have hy' := congrArg Subtype.val hy
            have hxy' := congrArg Subtype.val hxy
            change (Q (G x)).1.val=1 at hx'
            change 1-(Q (G (flip y))).1.val=0 at hy'
            change (Q (G x)).2.val=(Q (G (flip y))).2.val at hxy'
            rw [(hQ (G x)).1] at hx'
            rw [(hQ (G (flip y))).1] at hy'
            rw [(hQ (G x)).2,(hQ (G (flip y))).2] at hxy'
            have hxside : (G x).val.1=1 := by linarith
            have hyside : (G (flip y)).val.1=1 := by linarith
            obtain ⟨hx2,hxl,hxr⟩ := (hside x).mp hxside
            obtain ⟨hy2,hyl,hyr⟩ := (hside (flip y)).mp hyside
            rw [hparam x hx2 hxl hxr,hparam (flip y) hy2 hyl hyr] at hxy'
            change y.2.val=1 at hy2
            change 1/4≤1-y.1.val at hyl
            change 1-y.1.val≤1/2 at hyr
            change (8*x.1.val-3+1)/2=(8*(1-y.1.val)-3+1)/2 at hxy'
            exact ⟨hx2,hy2,by linarith,hxl,hxr⟩
          · rintro ⟨hx2,hy2,hxy,hxl,hxr⟩
            have hy2' : (flip y).2.val=1 := hy2
            have hyl : (1/4 : ℝ)≤(flip y).1.val := by change 1/4≤1-y.1.val;linarith
            have hyr : (flip y).1.val≤(1/2 : ℝ) := by change 1-y.1.val≤1/2;linarith
            have hxside := (hside x).mpr ⟨hx2,hxl,hxr⟩
            have hyside := (hside (flip y)).mpr ⟨hy2',hyl,hyr⟩
            refine ⟨?_,?_,?_⟩ <;> apply Subtype.ext
            · change (Q (G x)).1.val=1
              rw [(hQ (G x)).1,hxside];norm_num
            · change 1-(Q (G (flip y))).1.val=0
              rw [(hQ (G (flip y))).1,hyside];norm_num
            · change (Q (G x)).2.val=(Q (G (flip y))).2.val
              rw [(hQ (G x)).2,(hQ (G (flip y))).2,
                hparam x hx2 hxl hxr,hparam (flip y) hy2' hyl hyr]
              change (8*x.1.val-3+1)/2=(8*(1-y.1.val)-3+1)/2
              linarith
        · exact ⟨(Homeomorph.Quotient.congr B (by intros;rfl)).trans He⟩
      obtain ⟨m,hm,hml,hmr,hseam,⟨He⟩⟩ := quarterData
      have hgauge (x : EuclideanSpace ℝ (Fin 2)) :
          gauge (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (L x) = ‖x‖ := by
        have he : {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • L x ∈ L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
          ext r
          simp only [mem_setOf_eq]
          constructor
          · rintro ⟨hr,z,hz,hzx⟩
            have hz' : z = r⁻¹ • x := L.injective (by simpa using hzx)
            exact ⟨hr,hz' ▸ hz⟩
          · rintro ⟨hr,hx⟩
            exact ⟨hr,r⁻¹ • x,hx,by simp⟩
        rw [gauge_def',he,← gauge_def']
        simpa using gauge_closedBall (E := EuclideanSpace ℝ (Fin 2)) (by norm_num : 0 ≤ (1 : ℝ)) x
      have hboundary (v : StandardDisk) (hv : ‖(H v).val‖=1) :
          ∃ p : Sphere, ∃ hp : height p=0, v=diskBoundaryPoint p hp := by
        have hz : L v.val≠0 := by
          intro hz
          have hh : (H v).val=0 := by rw [hH v,hz,gaugeRescale_zero]
          rw [hh,norm_zero] at hv
          norm_num at hv
        have ht : gauge (closedBall (0 : ℝ × ℝ) 1) (L v.val)≠0 := by
          simpa [gauge_closedBall,norm_ne_zero_iff] using hz
        have hg := gauge_gaugeRescale' (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ht
        rw [← hH v,hgauge] at hg
        have hnorm : ‖v.val‖=1 := by simpa [gauge_closedBall,hv] using hg.symm
        let p := northHemisphereDiskHomeomorph.symm (coordinateDiskClosedBallHomeomorph.symm v)
        have hv' : v = coordinateDiskClosedBallHomeomorph (northHemisphereDiskHomeomorph p) := by
          dsimp [p]
          simp
        have hhor : v.val = horizontal p.val := congrArg Subtype.val hv'
        have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hhor
        have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hhor
        change v.val 0 = p.val.val 0 at h0
        change v.val 1 = p.val.val 1 at h1
        have hs := sphere_coordinate_squares p.val
        have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) v.val
        simp only [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,Fin.sum_univ_zero,add_zero] at hn
        change ‖v.val‖ ^ 2 = (v.val 0)^2 + (v.val 1)^2 at hn
        rw [hnorm,h0,h1] at hn
        have hp : height p.val = 0 := by
          change p.val.val 2 = 0
          nlinarith only [hs,hn]
        have hparam : v = diskBoundaryPoint p.val hp := hv'
        exact ⟨p.val,hp,hparam⟩
      have hupper (v : StandardDisk) : (H v).val.1≤1 := by
        have h : |(H v).val.1|≤1 ∧ |(H v).val.2|≤1 := by
          simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff]
            using (H v).property
        exact (abs_le.mp h.1).2
      have hleft (u : Q0) (hy : (M u).2.val=1)
          (hl : (1/4 : ℝ)≤(M u).1.val) (hr : (M u).1.val≤1/2) :
          ∃ p : Sphere, ∃ hp : height p=0, closedArcSector (1 : Fin 6) p ∧
            u=Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp)) := by
        let z : Metric.closedBall (0 : ℝ × ℝ) 1 := ⟨(4*(M u).1.val-1,1),by
          rw [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff,abs_le,abs_le]
          exact ⟨⟨by linarith,by linarith⟩,⟨by norm_num,by norm_num⟩⟩⟩
        let v := H.symm z
        have hv : H v=z := H.apply_symm_apply z
        have hnorm : ‖(H v).val‖=1 := by
          rw [hv]
          change ‖(4*(M u).1.val-1,(1 : ℝ))‖=1
          rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
          norm_num
          rw [abs_le]
          exact ⟨by linarith,by linarith⟩
        obtain ⟨p,hp,hparam⟩ := hboundary v hnorm
        have hi : closedArcSector (1 : Fin 6) p := by
          apply (hsector1 p hp).mpr
          rw [← hparam,hv]
          exact ⟨rfl,by change 0≤4*(M u).1.val-1;linarith⟩
        have hu : u=Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v) := by
          apply M.injective
          apply Prod.ext <;> apply Subtype.ext
          · rw [(hML v).1,hv]
            change (M u).1.val=((4*(M u).1.val-1)+1)/4
            ring
          · rw [(hML v).2,hv]
            change (M u).2.val=((1 : ℝ)+1)/2
            rw [hy];norm_num
        exact ⟨p,hp,hi,hu.trans (congrArg (fun v => Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v)) hparam)⟩
      let B := Homeomorph.sumCongr M M
      let F : C(Q0 ⊕ Q0,D) := m.comp ⟨B,B.continuous⟩
      have hFl : Function.Injective (fun u => F (Sum.inl u)) := hml.comp M.injective
      have hFr : Function.Injective (fun v => F (Sum.inr v)) := hmr.comp M.injective
      have hcross (u v : Q0) : F (Sum.inl u)=F (Sum.inr v) ↔
          ∃ p : Sphere, ∃ hp : height p=0, closedArcSector (1 : Fin 6) p ∧
            u=Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp)) ∧
            v=Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)) := by
        change m (Sum.inl (M u))=m (Sum.inr (M v)) ↔ _
        rw [hseam]
        constructor
        · rintro ⟨hu2,hv2,huv,hul,hur⟩
          obtain ⟨p,hp,hi,hu⟩ := hleft u hu2 hul hur
          have hv : v=Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)) := by
            apply M.injective
            apply Prod.ext <;> apply Subtype.ext
            · have he := (hML (diskBoundaryPoint p hp)).1
              rw [← hu] at he
              rw [(hMR (diskBoundaryPoint p hp)).1]
              linarith
            · rw [(hMR (diskBoundaryPoint p hp)).2,(hsector1 p hp).mp hi |>.1,hv2]
              norm_num
          exact ⟨p,hp,hi,hu,hv⟩
        · rintro ⟨p,hp,hi,rfl,rfl⟩
          obtain ⟨hy,hx⟩ := (hsector1 p hp).mp hi
          have hxu := hupper (diskBoundaryPoint p hp)
          rw [(hML _).1,(hML _).2,(hMR _).1,(hMR _).2,hy]
          exact ⟨by norm_num,by norm_num,by ring,by linarith,by linarith⟩
      have hgenerated (a b : Q0 ⊕ Q0) : F a=F b ↔ Relation.EqvGen R1 a b := by
        constructor
        · intro hab
          cases a with
          | inl u =>
            cases b with
            | inl v =>
              have he := hFl hab
              subst v
              exact .refl _
            | inr v =>
              obtain ⟨p,hp,hi,hu,hv⟩ := (hcross u v).mp hab
              exact .rel _ _ ⟨p,hp,hi,congrArg Sum.inl hu,congrArg Sum.inr hv⟩
          | inr u =>
            cases b with
            | inl v =>
              obtain ⟨p,hp,hi,hv,hu⟩ := (hcross v u).mp hab.symm
              exact .symm _ _ (.rel _ _ ⟨p,hp,hi,congrArg Sum.inl hv,congrArg Sum.inr hu⟩)
            | inr v =>
              have he := hFr hab
              subst v
              exact .refl _
        · intro hab
          induction hab with
          | rel a b h =>
            rcases h with ⟨p,hp,hi,rfl,rfl⟩
            exact (hcross _ _).mpr ⟨p,hp,hi,rfl,rfl⟩
          | refl a => rfl
          | symm a b h ih => exact ih.symm
          | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
      let HF : Quotient (Setoid.ker F) ≃ₜ D :=
        (Homeomorph.Quotient.congr B (by intros;rfl)).trans He
      exact ⟨(Homeomorph.Quotient.congr (Homeomorph.refl (Q0 ⊕ Q0))
        (fun a b => (hgenerated a b).symm)).trans HF⟩
    exact diskData
end AlternatingSphereCover

#print axioms AlternatingSphereCover.actual_one_face_source_cut_disk_total_attaching
