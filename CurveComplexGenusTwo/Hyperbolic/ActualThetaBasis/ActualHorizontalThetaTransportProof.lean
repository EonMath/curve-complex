import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualMappedArcFormulaRecoveryProof
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualRetractedBasedInterpolationProbeProof
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualRealRetractionProbeProof
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualPairedConcatSafetyProbeProof
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualCylinderRealHomeomorphProbeProof
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualPairedArcSafetyProof
open Set Topology ContinuousMap
namespace CurveComplex.Hyperbolic.PantsTheta
theorem actual_horizontal_theta_transport (e : ActualPuncturedCylinder ≃ₜ ActualPuncturedRealPlane)
    (he : ∀ z,(e z).val=(Real.exp z.val.2*(z.val.1 : ℂ).re,Real.exp z.val.2*(z.val.1 : ℂ).im))
    (R : ActualPuncturedRealPlane ≃ₕ ActualSquareTheta)
    (haxis : ∀ (a : ℝ),0<a → ∀ (z : ActualPuncturedRealPlane),z.val=(-a,0) → R z=thetaBase)
    (hfix : ∀ z : ActualSquareTheta,R (thetaRealEmbedding z)=z) :
    ∀ outer : Bool,
      let ε : ℝ := if outer then 1 else -1
      let hε : ε≠0 := by dsimp [ε];cases outer <;> norm_num
      ∃ hb : R (e (actualPantsLevelPoint ε hε))=thetaBase,
      Path.Homotopic
        ((((actualPantsHorizontalLoop ε hε).map e.continuous).map R.continuous).cast hb.symm hb.symm)
        (thetaLoop outer) := by
  intro outer ε hε
  let b := e (actualPantsLevelPoint ε hε)
  have hb : R b=thetaBase := by
    apply haxis (Real.exp ε) (Real.exp_pos ε)
    rw [he]
    simp [b,actualPantsLevelPoint]
  refine ⟨hb,?_⟩
  let γ : Path b b := (actualPantsHorizontalLoop ε hε).map e.continuous
  let pseq : Fin 6 → ActualPuncturedRealPlane := γ ∘ arcMark
  let F : (i : Fin 5) → Path (pseq i.castSucc) (pseq i.succ) :=
    fun i => γ.subpath (arcMark i.castSucc) (arcMark i.succ)
  let qseq : Fin 6 → ActualPuncturedRealPlane := fun i => thetaRealEmbedding (thetaVertex outer i)
  let G : (i : Fin 5) → Path (qseq i.castSucc) (qseq i.succ) :=
    fun i => (thetaLeg outer i).map thetaRealEmbedding.continuous
  let A (i : Fin 6) : ℝ :=
      (match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 5 | 4 => 7 | _ => 8)*Real.pi/4
  have ha (i : Fin 6) : 2*Real.pi*(arcMark i).val=A i := by
    fin_cases i <;> dsimp [arcMark,A] <;> ring
  have hF : ∀ (i : Fin 5) (t s : unitInterval),
      (1-s.val) • (F i t).val+s.val • (G i t).val ≠ ((0:ℝ),0) ∧
      (1-s.val) • (F i t).val+s.val • (G i t).val ≠ ((1:ℝ),0) := by
    intro i t s
    have hg := actual_mapped_horizontal_arc_formula e he outer i t
    change (F i t).val=_ at hg
    have hφ : 2*Real.pi*((1-t.val)*(arcMark i.castSucc).val+t.val*(arcMark i.succ).val)=
        (1-t.val)*A i.castSucc+t.val*A i.succ := by
      rw [← ha,← ha]
      ring
    rw [hφ] at hg
    rw [hg]
    exact actual_paired_boundary_arc_interpolation_avoids_punctures outer i t s
  have hp : ∀ s : unitInterval,
      (1-s.val) • (pseq 0).val+s.val • (qseq 0).val ≠ ((0:ℝ),0) ∧
      (1-s.val) • (pseq 0).val+s.val • (qseq 0).val ≠ ((1:ℝ),0) := by
    intro s
    simpa only [Path.source,Fin.castSucc_zero] using hF 0 0 s
  have hsafe := paired_concat_interpolation_safety 5 pseq qseq F G hp hF
  have hp0 : b=pseq 0 := by simp [pseq,arcMark]
  have hp1 : b=pseq (Fin.last 5) := by simp [pseq,arcMark]
  have hq0 : thetaRealEmbedding thetaBase=qseq 0 := rfl
  have hq1 : thetaRealEmbedding thetaBase=qseq (Fin.last 5) := rfl
  let p : Path b b := (Path.concat pseq F).cast hp0 hp1
  let q : Path (thetaRealEmbedding thetaBase) (thetaRealEmbedding thetaBase) :=
    (Path.concat qseq G).cast hq0 hq1
  have hbase : ∀ (s : unitInterval) (z : ActualPuncturedRealPlane),
      z.val=(1-s.val) • b.val+s.val • (thetaRealEmbedding thetaBase).val → R z=thetaBase := by
    intro s z hz
    have hbval : b.val=(-Real.exp ε,0) := by rw [he];simp [b,actualPantsLevelPoint]
    have hcval : (thetaRealEmbedding thetaBase).val=((-1/2:ℝ),0) := by norm_num [thetaRealEmbedding,thetaBase]
    apply haxis ((1-s.val)*Real.exp ε+s.val/2)
    · have hs0 := s.property.1
      have hs1 := s.property.2
      have hr := Real.exp_pos ε
      by_cases hs : s.val=1
      · rw [hs];norm_num
      · have hlt : s.val<1 := lt_of_le_of_ne hs1 hs
        positivity
    · rw [hz,hbval,hcval]
      apply Prod.ext <;> dsimp <;> ring
  have h := retracted_based_interpolation R.toFun thetaBase b
    (thetaRealEmbedding thetaBase) p q hb (hfix thetaBase)
    (fun s t => hsafe t s) hbase
  have hq : ((q.map R.continuous).cast (hfix thetaBase).symm (hfix thetaBase).symm)=thetaLoop outer := by
    apply Path.ext
    funext t
    change R (q t)=thetaLoop outer t
    have hqval : q t=thetaRealEmbedding (thetaLoop outer t) := by
      change Path.concat qseq G t=thetaRealEmbedding (Path.concat (thetaVertex outer) (thetaLeg outer) t)
      rw [← concat_map_paths 5 (thetaVertex outer) (thetaLeg outer) thetaRealEmbedding]
      rfl
    rw [hqval,hfix]
  rw [hq] at h
  have hγ := (Path.Homotopic.concat_subpath γ arcMark).map R.toFun
  have hγ' := hγ.pathCast (show thetaBase=R (pseq 0) by rw [←hp0,hb])
    (show thetaBase=R (pseq (Fin.last 5)) by rw [←hp1,hb])
  have heq : ((γ.subpath (arcMark 0) (arcMark (Fin.last 5))).map R.continuous).cast
      (show thetaBase=R (pseq 0) by rw [←hp0,hb])
      (show thetaBase=R (pseq (Fin.last 5)) by rw [←hp1,hb]) =
      (γ.map R.continuous).cast hb.symm hb.symm := by
    apply Path.ext
    funext t
    change R (γ.subpath (arcMark 0) (arcMark (Fin.last 5)) t)=R (γ t)
    have hm0 : arcMark 0=0 := by apply Subtype.ext;norm_num [arcMark]
    have hm1 : arcMark (Fin.last 5)=1 := by apply Subtype.ext;norm_num [arcMark]
    rw [hm0,hm1,Path.subpath_zero_one]
    rfl
  rw [heq] at hγ'
  exact hγ'.symm.trans h
end CurveComplex.Hyperbolic.PantsTheta
