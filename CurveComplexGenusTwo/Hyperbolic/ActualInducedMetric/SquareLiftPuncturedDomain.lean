import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.SquareLiftExponentialDescent

namespace CurveComplex.Hyperbolic
open Set Topology

 def squareLiftPuncturedDisc (A : ℝ) : Set ℂ :=
  {z | z ≠ 0 ∧ ‖z‖ < Real.exp (A / 2)}

theorem squareLiftPuncturedDisc_isOpen (A : ℝ) : IsOpen (squareLiftPuncturedDisc A) := by
  exact isClosed_singleton.isOpen_compl.inter (isOpen_lt continuous_norm continuous_const)

theorem exp_mem_squareLiftPuncturedDisc (A : ℝ) (w : ℂ)
    (hw : w ∈ logLeftHalfPlane (A / 2)) : Complex.exp w ∈ squareLiftPuncturedDisc A := by
  exact ⟨Complex.exp_ne_zero w, by rw [Complex.norm_exp]; exact Real.exp_lt_exp.mpr hw⟩

theorem log_mem_squareLiftHalfPlane (A : ℝ) (z : ℂ)
    (hz : z ∈ squareLiftPuncturedDisc A) : Complex.log z ∈ logLeftHalfPlane (A / 2) := by
  change (Complex.log z).re < A / 2
  rw [Complex.log_re]
  apply Real.exp_lt_exp.mp
  rw [Real.exp_log (norm_pos_iff.mpr hz.1)]
  exact hz.2

noncomputable def squareLiftExpProjection (A : ℝ) :
    logLeftHalfPlane (A / 2) → squareLiftPuncturedDisc A :=
  fun w => ⟨Complex.exp w.val, exp_mem_squareLiftPuncturedDisc A w.val w.property⟩

theorem squareLiftExpProjection_isQuotientMap (A : ℝ) : IsQuotientMap (squareLiftExpProjection A) := by
  have hopen : IsOpenMap (squareLiftExpProjection A) := by
    apply (squareLiftPuncturedDisc_isOpen A).isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
    exact Complex.isOpenMap_exp.comp (logLeftHalfPlane_isOpen (A / 2)).isOpenMap_subtype_val
  have hcont : Continuous (squareLiftExpProjection A) := by
    apply Continuous.subtype_mk
    exact Complex.continuous_exp.comp continuous_subtype_val
  have hsurj : Function.Surjective (squareLiftExpProjection A) := by
    intro z
    refine ⟨⟨Complex.log z.val, log_mem_squareLiftHalfPlane A z.val z.property⟩, ?_⟩
    apply Subtype.ext
    exact Complex.exp_log z.property.1
  exact hopen.isQuotientMap hcont hsurj

theorem squareLiftLogFormula_continuousOn (A : ℝ) (F : ℂ → ℂ)
    (hF : ContinuousOn F (logLeftHalfPlane A)) :
    ContinuousOn (squareLiftLogFormula F) (logLeftHalfPlane (A / 2)) := by
  have hmaps : MapsTo (fun w : ℂ => 2 * w) (logLeftHalfPlane (A / 2)) (logLeftHalfPlane A) := by
    intro w hw
    change w.re < A / 2 at hw
    change (2 * w).re < A
    norm_num [Complex.mul_re]
    linarith
  exact Complex.continuous_exp.comp_continuousOn
    ((hF.comp (continuous_const.mul continuous_id).continuousOn hmaps).div_const 2)

 theorem squareLiftLogFormula_descends_continuously (A : ℝ) (F : ℂ → ℂ) (k : ℤ)
    (hF : ContinuousOn F (logLeftHalfPlane A))
    (hperiod : ∀ z ∈ logLeftHalfPlane A,
      F (z + logarithmDeckPeriod) = F z + k * logarithmDeckPeriod) :
    ContinuousOn (fun z => squareLiftLogFormula F (Complex.log z)) (squareLiftPuncturedDisc A) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply (squareLiftExpProjection_isQuotientMap A).continuous_iff.mpr
  have heq :
      (squareLiftPuncturedDisc A).domRestrict (fun z => squareLiftLogFormula F (Complex.log z)) ∘
        squareLiftExpProjection A =
      (logLeftHalfPlane (A / 2)).domRestrict (squareLiftLogFormula F) := by
    funext w
    exact (squareLiftLogFormula_equal_exp_representatives A F k hperiod w.val
      (Complex.log (Complex.exp w.val)) w.property (Complex.exp_log (Complex.exp_ne_zero w.val)).symm).symm
  rw [heq]
  exact continuousOn_iff_continuous_domRestrict.mp (squareLiftLogFormula_continuousOn A F hF)

end CurveComplex.Hyperbolic
