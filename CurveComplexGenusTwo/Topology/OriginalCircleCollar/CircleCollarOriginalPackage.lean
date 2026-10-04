import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.PositionExtension.SurfacePuncture
import CurveComplexGenusTwo.Topology.PositionExtension.LocalOrientationAlgebra
import CurveComplexGenusTwo.Topology.PositionExtension.TwistedBandReflection
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisChart
import CurveComplexGenusTwo.Topology.GlobalArcCollar.AxisFramedStripProducerStatement

open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz CurveComplex.GenusOrientationCandidate
set_option maxHeartbeats 3000000
namespace CurveComplex.LocalSurgery
open scoped Manifold ContDiff
open Topology Set Filter unitInterval Schoenflies

/-- Review request: orientation-free regular-neighborhood dichotomy for the
literal topologically embedded circle. A twist is detected by an actual local
reflection map, rather than an assumed orientation or an annulus certificate. -/
theorem embedded_circle_annular_collar_or_local_reflection
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (b : CurveComplex.Curve S) :
    (∃ e : C(Set.Ioo (-1 : ℝ) 1 × Circle, S),
      Topology.IsOpenEmbedding e ∧
      ∀ w : Circle, e (⟨0, by norm_num⟩, w) = b.map w) ∨
    (∃ x : S, Nonempty (CurveComplex.GenusOrientationCandidate.LocalReflectionWitness x)) := by
  have untwisted
    (ε : ℝ) (hε : 0 < ε)
    (square : Metric.closedBall ((0,0) : ℝ × ℝ) ε → S)
    (hsquare : Topology.IsEmbedding square)
    (band : unitInterval × BandWidth → S)
    (hband : Topology.IsEmbedding band)
    (hbottom : ∀ t, band (0,t) = square (squarePort ε hε 2 t))
    (htop : ∀ t, band (1,t) = square (squarePort ε hε 0 t))
    (hmeet : Set.range band ∩ Set.range square =
      Set.range (fun t => square (squarePort ε hε 2 t)) ∪
      Set.range (fun t => square (squarePort ε hε 0 t))) :
    ∃ q : unitInterval × BandWidth → Metric.closedBall ((0,0) : ℝ × ℝ) ε,
      (∀ u w, (q (u,w) : ℝ × ℝ) = (ε/4*(w:ℝ),ε*(1-2*(u:ℝ)))) ∧
      ∃ E : C(Set.Ioo (-1 : ℝ) 1 × Circle,S), Topology.IsOpenEmbedding E ∧
        (∀ u : unitInterval, E (⟨0,by norm_num⟩,
          AddCircle.homeomorphCircle (by norm_num : (2:ℝ) ≠ 0) (u: AddCircle (2:ℝ))) =
          band (u,⟨0,by norm_num⟩)) ∧
        (∀ u : unitInterval, E (⟨0,by norm_num⟩,
          AddCircle.homeomorphCircle (by norm_num : (2:ℝ) ≠ 0) (((u:ℝ)+1 : ℝ): AddCircle (2:ℝ))) =
          square (q (u,⟨0,by norm_num⟩))) := by
    have openAnnulus
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S))
      (hE : Function.Injective E) : Topology.IsOpenEmbedding E := by
      have hopen : IsOpenMap E := by
        intro V hV
        rw [isOpen_iff_forall_mem_open]
        rintro z ⟨⟨w,c⟩,hwV,rfl⟩
        let a : ℝ := ((w : ℝ)-1)/2
        let b : ℝ := ((w : ℝ)+1)/2
        have haw : a < (w : ℝ) := by dsimp [a]; linarith [w.property.1]
        have hwb : (w : ℝ) < b := by dsimp [b]; linarith [w.property.2]
        have ha : -1 < a := by dsimp [a]; linarith [w.property.1]
        have hb : b < 1 := by dsimp [b]; linarith [w.property.2]
        have hab : a ≤ b := (haw.trans hwb).le
        let width : ℝ → Set.Ioo (-1 : ℝ) 1 := fun t =>
          ⟨(Set.projIcc a b hab t : ℝ),
            ⟨ha.trans_le (Set.projIcc a b hab t).property.1,
              lt_of_le_of_lt (Set.projIcc a b hab t).property.2 hb⟩⟩
        have hwc : Continuous width := by
          exact (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
        let angle : ℝ := Complex.arg (c : ℂ)
        let F : EuclideanSpace ℝ (Fin 2) → S :=
          fun x => E (width (x 0), Circle.exp (x 1))
        have hFc : Continuous F := E.continuous.comp
          ((hwc.comp (by fun_prop)).prodMk (Circle.exp.continuous.comp (by fun_prop)))
        let U : Set (EuclideanSpace ℝ (Fin 2)) :=
          {x | x 0 ∈ Set.Ioo a b ∧ x 1 ∈ Set.Ioo (angle-Real.pi/2) (angle+Real.pi/2) ∧
            (width (x 0),Circle.exp (x 1)) ∈ V}
        have hU : IsOpen U :=
          (isOpen_Ioo.preimage (by fun_prop)).inter
            ((isOpen_Ioo.preimage (by fun_prop)).inter
              (hV.preimage ((hwc.comp (by fun_prop)).prodMk
                (Circle.exp.continuous.comp (by fun_prop)))))
        have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ U) :
            (width (x 0) : ℝ) = x 0 := by
          exact congrArg Subtype.val (Set.projIcc_of_mem hab ⟨hx.1.1.le,hx.1.2.le⟩)
        have hi : Set.InjOn F U := by
          intro x hx y hy he
          have hh := hE he
          have hx0 := congrArg (fun q : Set.Ioo (-1 : ℝ) 1 × Circle => (q.1 : ℝ)) hh
          have hx1 := congrArg Prod.snd hh
          have hangle : x 1 = y 1 :=
            Circle.exp_injOn_Icc (a := angle-Real.pi/2) (b := angle+Real.pi/2)
              (by linarith [Real.pi_pos])
              ⟨hx.2.1.1.le,hx.2.1.2.le⟩ ⟨hy.2.1.1.le,hy.2.1.2.le⟩ hx1
          have hwidth : x 0 = y 0 := by
            change (width (x 0) : ℝ) = (width (y 0) : ℝ) at hx0
            simpa only [hclip x hx,hclip y hy] using hx0
          ext i
          fin_cases i
          · exact hwidth
          · exact hangle
        have hFU : IsOpen (F '' U) :=
          CurveComplex.surface_invariance_of_domain_probe F U hU hFc.continuousOn hi
        have hclipw : width (w : ℝ) = w := by
          apply Subtype.ext
          change (Set.projIcc a b hab (w : ℝ) : ℝ) = (w : ℝ)
          exact congrArg Subtype.val (Set.projIcc_of_mem hab ⟨haw.le,hwb.le⟩)
        have hexp : Circle.exp angle = c := Circle.exp_arg c
        let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (w : ℝ) angle
        have hx0 : x 0 = (w : ℝ) := by simp [x,Schoenflies.Plane.mk]
        have hx1 : x 1 = angle := by simp [x,Schoenflies.Plane.mk]
        have hx : x ∈ U := by
          refine ⟨?_,?_,?_⟩
          · change a < x 0 ∧ x 0 < b
            rw [hx0]
            exact ⟨haw,hwb⟩
          · rw [hx1]
            constructor <;> linarith [Real.pi_pos]
          · simpa only [hx0,hx1,hclipw,hexp] using hwV
        refine ⟨F '' U,?_,hFU,?_⟩
        · rintro y ⟨u,hu,rfl⟩
          exact ⟨(width (u 0),Circle.exp (u 1)),hu.2.2,rfl⟩
        · refine ⟨x,hx,?_⟩
          simp only [F,hx0,hx1,hclipw,hexp]
      exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap E.continuous hE hopen
    have descend
      (F : C(Set.Icc (0 : ℝ) 2 × Set.Icc (-1 : ℝ) 1, S))
      (hclose : ∀ w, F (⟨0,by norm_num⟩,w) = F (⟨2,by norm_num⟩,w))
      (hFi : ∀ x y : Set.Icc (0 : ℝ) 2 × Set.Icc (-1 : ℝ) 1,
        (x.1 : ℝ) < 2 → (y.1 : ℝ) < 2 → F x = F y → x = y) :
      ∃ E : C(Set.Ioo (-1 : ℝ) 1 × Circle,S), Function.Injective E ∧
        ∀ (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 2) (w : Set.Ioo (-1 : ℝ) 1),
          E (w,AddCircle.homeomorphCircle (by norm_num : (2 : ℝ) ≠ 0) (t : AddCircle (2 : ℝ))) =
            F (⟨t,⟨ht.1,ht.2.le⟩⟩,⟨w,⟨w.property.1.le,w.property.2.le⟩⟩) := by
      letI : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
      let G : C(ℝ × Set.Icc (-1 : ℝ) 1,S) :=
        ⟨fun z => F (Set.projIcc 0 2 (by norm_num) z.1,z.2),
          by fun_prop⟩
      let k : C(ℝ,C(Set.Icc (-1 : ℝ) 1,S)) := G.curry
      have hkclose : k 0 = k 2 := by
        ext w
        change F (Set.projIcc 0 2 (by norm_num) 0,w) =
          F (Set.projIcc 0 2 (by norm_num) 2,w)
        simpa only [Set.projIcc_of_mem (by norm_num) (show (0 : ℝ) ∈ Set.Icc 0 2 by norm_num),
          Set.projIcc_of_mem (by norm_num) (show (2 : ℝ) ∈ Set.Icc 0 2 by norm_num)] using hclose w
      let g : C(AddCircle (2 : ℝ),C(Set.Icc (-1 : ℝ) 1,S)) :=
        ⟨AddCircle.liftIco 2 0 k,AddCircle.liftIco_zero_continuous hkclose k.continuous.continuousOn⟩
      let c : AddCircle (2 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
      let width : Set.Ioo (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1 :=
        fun w => ⟨w,⟨w.property.1.le,w.property.2.le⟩⟩
      have hwc : Continuous width := continuous_subtype_val.subtype_mk _
      let E : C(Set.Ioo (-1 : ℝ) 1 × Circle,S) :=
        g.uncurry.comp ⟨fun z => (c.symm z.2,width z.1),
          (c.symm.continuous.comp continuous_snd).prodMk (hwc.comp continuous_fst)⟩
      have hval (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 2) (w : Set.Ioo (-1 : ℝ) 1) :
          E (w,c (t : AddCircle (2 : ℝ))) = F (⟨t,⟨ht.1,ht.2.le⟩⟩,width w) := by
        change g (c.symm (c (t : AddCircle (2 : ℝ)))) (width w) = _
        rw [c.symm_apply_apply]
        change AddCircle.liftIco 2 0 k (t : AddCircle (2 : ℝ)) (width w) = _
        rw [AddCircle.liftIco_zero_coe_apply ht]
        change F (Set.projIcc 0 2 (by norm_num) t,width w) = _
        rw [Set.projIcc_of_mem (by norm_num) ⟨ht.1,ht.2.le⟩]
      have hEi : Function.Injective E := by
        rintro ⟨w,x⟩ ⟨v,y⟩ he
        obtain ⟨t,ht,hxt⟩ := AddCircle.eq_coe_Ico (c.symm x)
        obtain ⟨u,hu,hyu⟩ := AddCircle.eq_coe_Ico (c.symm y)
        have hx : x = c (t : AddCircle (2 : ℝ)) := by
          rw [hxt,c.apply_symm_apply]
        have hy : y = c (u : AddCircle (2 : ℝ)) := by
          rw [hyu,c.apply_symm_apply]
        rw [hx,hy,hval t ht w,hval u hu v] at he
        have hp := hFi (⟨t,⟨ht.1,ht.2.le⟩⟩,width w)
          (⟨u,⟨hu.1,hu.2.le⟩⟩,width v) ht.2 hu.2 he
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z : Set.Icc (0 : ℝ) 2 × Set.Icc (-1 : ℝ) 1 => (z.2 : ℝ)) hp
        · have htu := congrArg (fun z : Set.Icc (0 : ℝ) 2 × Set.Icc (-1 : ℝ) 1 => (z.1 : ℝ)) hp
          change t = u at htu
          change x = y
          rw [hx,hy,htu]
      exact ⟨E,hEi,hval⟩
    classical
    have hrectangle (u : I) (t : BandWidth) :
        (ε/4 * (t : ℝ), ε * (1 - 2 * (u : ℝ))) ∈
          Metric.closedBall ((0,0) : ℝ × ℝ) ε := by
      simp only [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq,
        sub_zero, max_le_iff]
      constructor
      · calc
          |ε/4 * (t : ℝ)| = ε/4 * |(t : ℝ)| := by
            rw [abs_mul, abs_of_pos (by positivity)]
          _ ≤ ε/4 := by
            have ht := abs_le.mpr t.property
            nlinarith
          _ ≤ ε := by linarith
      · have hu : |1 - 2 * (u : ℝ)| ≤ 1 := by
          apply abs_le.mpr
          constructor <;> linarith [u.property.1,u.property.2]
        rw [abs_mul, abs_of_pos hε]
        nlinarith
    let qbase : I × BandWidth → Metric.closedBall ((0,0) : ℝ × ℝ) ε :=
      fun z => ⟨(ε/4 * (z.2 : ℝ), ε * (1 - 2 * (z.1 : ℝ))),
        hrectangle z.1 z.2⟩
    let Q : I × BandWidth → S := fun z => square (qbase z)
    have hqcont : Continuous qbase := by
      dsimp [qbase]
      fun_prop
    have hqinj : Function.Injective qbase := by
      intro x y hh
      have hp := congrArg Subtype.val hh
      have hx := congrArg Prod.fst hp
      have hy := congrArg Prod.snd hp
      dsimp [qbase] at hx hy
      apply Prod.ext
      · apply Subtype.ext
        have hh := mul_left_cancel₀ hε.ne' hy
        linarith
      · apply Subtype.ext
        have hh := mul_left_cancel₀ (by positivity : ε/4 ≠ 0) hx
        exact hh
    have hQembedded : IsEmbedding Q :=
      hsquare.comp (hqcont.isClosedEmbedding hqinj).isEmbedding
    have hQtop (t : BandWidth) : Q (0,t) = band (1,t) := by
      rw [htop]
      change square (qbase (0,t)) = square (squarePort ε hε 0 (t))
      apply congrArg square
      apply Subtype.ext
      simp [qbase,squarePort,crossingEndRectangle,flipBandWidth]
    have hQbottom (t : BandWidth) : Q (1,t) = band (0,t) := by
      rw [hbottom]
      change square (qbase (1,t)) = square (squarePort ε hε 2 (t))
      apply congrArg square
      apply Subtype.ext
      simp [qbase,squarePort,crossingEndRectangle,flipBandWidth]
      ring
    have hQinterior (u : I) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
        (t : BandWidth) : Q (u,t) ∉ Set.range band := by
      intro hmem
      have hboth : Q (u,t) ∈ Set.range band ∩ Set.range square :=
        ⟨hmem, ⟨qbase (u,t), rfl⟩⟩
      rw [hmeet] at hboth
      rcases hboth with ⟨v, hv⟩ | ⟨v, hv⟩
      · have heq := hsquare.injective hv
        have hy := congrArg (fun z : Metric.closedBall ((0,0) : ℝ × ℝ) ε => (z : ℝ × ℝ).2) heq
        simp only [squarePort, crossingEndRectangle, qbase] at hy
        change -(ε + ε / 4 * 0) = ε * (1 - 2 * (u : ℝ)) at hy
        have hh := mul_left_cancel₀ hε.ne' (show ε * (-1) = ε * (1 - 2 * (u : ℝ)) by nlinarith [hy])
        linarith
      · have heq := hsquare.injective hv
        have hy := congrArg (fun z : Metric.closedBall ((0,0) : ℝ × ℝ) ε => (z : ℝ × ℝ).2) heq
        simp only [squarePort, crossingEndRectangle, qbase] at hy
        change ε + ε / 4 * 0 = ε * (1 - 2 * (u : ℝ)) at hy
        have hh := mul_left_cancel₀ hε.ne' (show ε * 1 = ε * (1 - 2 * (u : ℝ)) by simpa using hy)
        linarith
    let P := Set.Icc (0 : ℝ) 2 × BandWidth
    let left : P → S := fun z => band (projIcc 0 1 zero_le_one (z.1 : ℝ), z.2)
    let right : P → S := fun z => Q (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1), z.2)
    let F : P → S := fun z => if (z.1 : ℝ) ≤ 1 then left z else right z
    have hleft : Continuous left := hband.continuous.comp
      ((continuous_projIcc.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
    have hright : Continuous right := hQembedded.continuous.comp
      ((continuous_projIcc.comp ((continuous_subtype_val.comp continuous_fst).sub continuous_const)).prodMk continuous_snd)
    have hFcont : Continuous F := by
      apply continuous_if_le (continuous_subtype_val.comp continuous_fst) continuous_const
        hleft.continuousOn hright.continuousOn
      intro z hz
      change (z.1 : ℝ) = 1 at hz
      change left z = right z
      dsimp only [left, right]
      rw [hz]
      simp only [sub_self, projIcc_of_mem zero_le_one (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num),
        projIcc_of_mem zero_le_one (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)]
      exact (hQtop z.2).symm
    have hFzero (t : BandWidth) : F (⟨0, by norm_num⟩,t) = band (0,t) := by
      simp [F,left]
    have hFtwo (t : BandWidth) : F (⟨2, by norm_num⟩,t) = band (0,t) := by
      simp only [F, show ¬ (2:ℝ) ≤ 1 by norm_num, ↓reduceIte, right]
      convert hQbottom t using 1 <;> norm_num [projIcc_of_mem]
    have hFinj (x y : P) (hx2 : (x.1 : ℝ) < 2)
        (hy2 : (y.1 : ℝ) < 2) (he : F x = F y) : x = y := by
      have hclipleft (z : P) (hz : (z.1 : ℝ) ≤ 1) :
          (projIcc 0 1 zero_le_one (z.1 : ℝ) : ℝ) = (z.1 : ℝ) := by
        simp only [projIcc_of_mem zero_le_one ⟨z.1.property.1, hz⟩]
      have hclipright (z : P) (hz : 1 < (z.1 : ℝ)) :
          (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1) : ℝ) = (z.1 : ℝ)-1 := by
        rw [projIcc_of_mem zero_le_one (show (z.1 : ℝ)-1 ∈ Icc (0:ℝ) 1 by
          constructor <;> linarith [z.1.property.2])]
      dsimp only [F] at he
      split_ifs at he with hx hy hy
      · have hh := hband.injective he
        apply Prod.ext
        · apply Subtype.ext
          have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
          exact (hclipleft x hx).symm.trans (hh1.trans (hclipleft y hy))
        · exact congrArg (fun z : I × BandWidth => z.2) hh
      · have hy' : 1 < (y.1 : ℝ) := lt_of_not_ge hy
        have ha := hQinterior (projIcc 0 1 zero_le_one ((y.1 : ℝ)-1))
          (by rw [hclipright y hy']; linarith)
          (by rw [hclipright y hy']; linarith) y.2
        exact False.elim (ha ⟨_, he⟩)
      · have hx' : 1 < (x.1 : ℝ) := lt_of_not_ge hx
        have ha := hQinterior (projIcc 0 1 zero_le_one ((x.1 : ℝ)-1))
          (by rw [hclipright x hx']; linarith)
          (by rw [hclipright x hx']; linarith) x.2
        exact False.elim (ha ⟨_, he.symm⟩)
      · have hh := hQembedded.injective he
        apply Prod.ext
        · apply Subtype.ext
          have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
          rw [hclipright x (lt_of_not_ge hx), hclipright y (lt_of_not_ge hy)] at hh1
          linarith
        · exact congrArg (fun z : I × BandWidth => z.2) hh
    let Fc : C(Set.Icc (0 : ℝ) 2 × BandWidth,S) := ⟨F,hFcont⟩
    have hclose : ∀ w, Fc (⟨0,by norm_num⟩,w) = Fc (⟨2,by norm_num⟩,w) := by
      intro w
      exact (hFzero w).trans (hFtwo w).symm
    obtain ⟨E,hEi,hEvalue⟩ := descend Fc hclose hFinj
    let c : AddCircle (2 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
    have hbandcore (u : unitInterval) : E (⟨0,by norm_num⟩,c (u : AddCircle (2 : ℝ))) =
        band (u,⟨0,by norm_num⟩) := by
      rw [hEvalue (u:ℝ) ⟨u.property.1,by linarith [u.property.2]⟩]
      change (if (u:ℝ) ≤ 1 then left (⟨u,by constructor <;> linarith [u.property.1,u.property.2]⟩,⟨0,by norm_num⟩)
        else right (⟨u,by constructor <;> linarith [u.property.1,u.property.2]⟩,⟨0,by norm_num⟩)) = _
      rw [if_pos u.property.2]
      simp only [left,Set.projIcc_of_mem zero_le_one u.property]
    have hsquarecore (u : unitInterval) : E (⟨0,by norm_num⟩,c (((u:ℝ)+1 : ℝ) : AddCircle (2 : ℝ))) =
        Q (u,⟨0,by norm_num⟩) := by
      by_cases hu1 : u = 1
      · subst u
        have hnum : (((1 : unitInterval) : ℝ)+1) = 2 := by norm_num
        rw [hnum,AddCircle.coe_period]
        have hz0 : E (⟨0,by norm_num⟩,c 0) = band (0,⟨0,by norm_num⟩) := by
          simpa using hbandcore 0
        exact hz0.trans (hQbottom _).symm
      · have hu2 : (u:ℝ)+1 < 2 := by
          have hune : (u:ℝ) ≠ 1 := by intro h; exact hu1 (Subtype.ext h)
          linarith [lt_of_le_of_ne u.property.2 hune]
        rw [hEvalue ((u:ℝ)+1) ⟨by linarith [u.property.1],hu2⟩]
        change F (⟨(u:ℝ)+1,by constructor <;> linarith [u.property.1,u.property.2]⟩,⟨0,by norm_num⟩) = _
        by_cases hu0 : u = 0
        · subst u
          simpa [F,left,Set.projIcc_of_mem] using (hQtop (⟨0,by norm_num⟩ : BandWidth)).symm
        · have hup : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (by intro h; exact hu0 (Subtype.ext h.symm))
          simp only [F,show ¬ (u:ℝ)+1 ≤ 1 by linarith,↓reduceIte,right]
          rw [show (u:ℝ)+1-1 = (u:ℝ) by ring,Set.projIcc_of_mem zero_le_one u.property]
    exact ⟨qbase,fun _ _ => rfl,E,openAnnulus E hEi,hbandcore,hsquarecore⟩
  have reparam
    (b : CurveComplex.Curve S)
    (E : C(Set.Ioo (-1 : ℝ) 1 × Circle,S)) (hE : IsOpenEmbedding E)
    (him : Set.range (fun z : Circle => E (⟨0,by norm_num⟩,z)) = b.image) :
    ∃ e : C(Set.Ioo (-1 : ℝ) 1 × Circle,S), IsOpenEmbedding e ∧
      ∀ z : Circle, e (⟨0,by norm_num⟩,z) = b.map z := by
    let zero : Set.Ioo (-1 : ℝ) 1 := ⟨0,by norm_num⟩
    let c : Circle → S := fun z => E (zero,z)
    have hc : IsEmbedding c := hE.isEmbedding.comp (isEmbedding_prodMkRight zero)
    have him' : Set.range c = Set.range b.map := him
    let ρ : Circle ≃ₜ Circle :=
      b.embedded.toHomeomorph.trans ((Homeomorph.setCongr him'.symm).trans hc.toHomeomorph.symm)
    have hcore (z : Circle) : c (ρ z) = b.map z := by
      exact congrArg Subtype.val
        (hc.toHomeomorph.apply_symm_apply ((Homeomorph.setCongr him'.symm) (b.embedded.toHomeomorph z)))
    let H : Set.Ioo (-1 : ℝ) 1 × Circle ≃ₜ Set.Ioo (-1 : ℝ) 1 × Circle :=
      (Homeomorph.refl _).prodCongr ρ
    let e : C(Set.Ioo (-1 : ℝ) 1 × Circle,S) := E.comp ⟨H,H.continuous⟩
    refine ⟨e,hE.comp H.isOpenEmbedding,?_⟩
    intro z
    exact hcore z
  have twisted
      (ε : ℝ) (hε : 0 < ε)
      (square : Metric.closedBall ((0,0) : ℝ × ℝ) ε → S)
      (hsquare : Topology.IsEmbedding square)
      (band : unitInterval × BandWidth → S)
      (hband : Topology.IsEmbedding band)
      (hbottom : ∀ t, band (0,t) = square (squarePort ε hε 2 t))
      (htop : ∀ t, band (1,t) = square (squarePort ε hε 0 (flipBandWidth true t)))
      (hmeet : Set.range band ∩ Set.range square =
        Set.range (fun t => square (squarePort ε hε 2 t)) ∪
        Set.range (fun t => square (squarePort ε hε 0 t))) :
      ∃ x : S, Nonempty (CurveComplex.GenusOrientationCandidate.LocalReflectionWitness x) := by
    classical
    have hrectangle (u : I) (t : BandWidth) :
        (ε/4 * -(t : ℝ), ε * (1 - 2 * (u : ℝ))) ∈
          Metric.closedBall ((0,0) : ℝ × ℝ) ε := by
      simp only [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq,
        sub_zero, max_le_iff]
      constructor
      · calc
          |ε/4 * -(t : ℝ)| = ε/4 * |(t : ℝ)| := by
            rw [abs_mul, abs_neg, abs_of_pos (by positivity)]
          _ ≤ ε/4 := by
            have ht := abs_le.mpr t.property
            nlinarith
          _ ≤ ε := by linarith
      · have hu : |1 - 2 * (u : ℝ)| ≤ 1 := by
          apply abs_le.mpr
          constructor <;> linarith [u.property.1,u.property.2]
        rw [abs_mul, abs_of_pos hε]
        nlinarith
    let qbase : I × BandWidth → Metric.closedBall ((0,0) : ℝ × ℝ) ε :=
      fun z => ⟨(ε/4 * -(z.2 : ℝ), ε * (1 - 2 * (z.1 : ℝ))),
        hrectangle z.1 z.2⟩
    let Q : I × BandWidth → S := fun z => square (qbase z)
    have hqcont : Continuous qbase := by
      dsimp [qbase]
      fun_prop
    have hqinj : Function.Injective qbase := by
      intro x y hh
      have hp := congrArg Subtype.val hh
      have hx := congrArg Prod.fst hp
      have hy := congrArg Prod.snd hp
      dsimp [qbase] at hx hy
      apply Prod.ext
      · apply Subtype.ext
        have hh := mul_left_cancel₀ hε.ne' hy
        linarith
      · apply Subtype.ext
        have hh := mul_left_cancel₀ (by positivity : ε/4 ≠ 0) hx
        exact neg_injective hh
    have hQembedded : IsEmbedding Q :=
      hsquare.comp (hqcont.isClosedEmbedding hqinj).isEmbedding
    have hQtop (t : BandWidth) : Q (0,t) = band (1,t) := by
      rw [htop]
      change square (qbase (0,t)) = square (squarePort ε hε 0 (flipBandWidth true t))
      apply congrArg square
      apply Subtype.ext
      simp [qbase,squarePort,crossingEndRectangle,flipBandWidth]
    have hQbottom (t : BandWidth) : Q (1,t) = band (0,flipBandWidth true t) := by
      rw [hbottom]
      change square (qbase (1,t)) = square (squarePort ε hε 2 (flipBandWidth true t))
      apply congrArg square
      apply Subtype.ext
      simp [qbase,squarePort,crossingEndRectangle,flipBandWidth]
      ring
    have hQinterior (u : I) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
        (t : BandWidth) : Q (u,t) ∉ Set.range band := by
      intro hmem
      have hboth : Q (u,t) ∈ Set.range band ∩ Set.range square :=
        ⟨hmem, ⟨qbase (u,t), rfl⟩⟩
      rw [hmeet] at hboth
      rcases hboth with ⟨v, hv⟩ | ⟨v, hv⟩
      · have heq := hsquare.injective hv
        have hy := congrArg (fun z : Metric.closedBall ((0,0) : ℝ × ℝ) ε => (z : ℝ × ℝ).2) heq
        simp only [squarePort, crossingEndRectangle, qbase] at hy
        change -(ε + ε / 4 * 0) = ε * (1 - 2 * (u : ℝ)) at hy
        have hh := mul_left_cancel₀ hε.ne' (show ε * (-1) = ε * (1 - 2 * (u : ℝ)) by nlinarith [hy])
        linarith
      · have heq := hsquare.injective hv
        have hy := congrArg (fun z : Metric.closedBall ((0,0) : ℝ × ℝ) ε => (z : ℝ × ℝ).2) heq
        simp only [squarePort, crossingEndRectangle, qbase] at hy
        change ε + ε / 4 * 0 = ε * (1 - 2 * (u : ℝ)) at hy
        have hh := mul_left_cancel₀ hε.ne' (show ε * 1 = ε * (1 - 2 * (u : ℝ)) by simpa using hy)
        linarith
    let P := Set.Icc (0 : ℝ) 2 × BandWidth
    let left : P → S := fun z => band (projIcc 0 1 zero_le_one (z.1 : ℝ), z.2)
    let right : P → S := fun z => Q (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1), z.2)
    let F : P → S := fun z => if (z.1 : ℝ) ≤ 1 then left z else right z
    have hleft : Continuous left := hband.continuous.comp
      ((continuous_projIcc.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
    have hright : Continuous right := hQembedded.continuous.comp
      ((continuous_projIcc.comp ((continuous_subtype_val.comp continuous_fst).sub continuous_const)).prodMk continuous_snd)
    have hFcont : Continuous F := by
      apply continuous_if_le (continuous_subtype_val.comp continuous_fst) continuous_const
        hleft.continuousOn hright.continuousOn
      intro z hz
      change (z.1 : ℝ) = 1 at hz
      change left z = right z
      dsimp only [left, right]
      rw [hz]
      simp only [sub_self, projIcc_of_mem zero_le_one (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num),
        projIcc_of_mem zero_le_one (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)]
      exact (hQtop z.2).symm
    have hFzero (t : BandWidth) : F (⟨0, by norm_num⟩,t) = band (0,t) := by
      simp [F,left]
    have hFtwo (t : BandWidth) : F (⟨2, by norm_num⟩,t) = band (0,flipBandWidth true t) := by
      simp only [F, show ¬ (2:ℝ) ≤ 1 by norm_num, ↓reduceIte, right]
      convert hQbottom t using 1 <;> norm_num [projIcc_of_mem]
    have hFinj (x y : P) (hx0 : 0 < (x.1 : ℝ)) (hx2 : (x.1 : ℝ) < 2)
        (hy0 : 0 < (y.1 : ℝ)) (hy2 : (y.1 : ℝ) < 2) (he : F x = F y) : x = y := by
      have hclipleft (z : P) (hz : (z.1 : ℝ) ≤ 1) :
          (projIcc 0 1 zero_le_one (z.1 : ℝ) : ℝ) = (z.1 : ℝ) := by
        simp only [projIcc_of_mem zero_le_one ⟨z.1.property.1, hz⟩]
      have hclipright (z : P) (hz : 1 < (z.1 : ℝ)) :
          (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1) : ℝ) = (z.1 : ℝ)-1 := by
        rw [projIcc_of_mem zero_le_one (show (z.1 : ℝ)-1 ∈ Icc (0:ℝ) 1 by
          constructor <;> linarith [z.1.property.2])]
      dsimp only [F] at he
      split_ifs at he with hx hy hy
      · have hh := hband.injective he
        apply Prod.ext
        · apply Subtype.ext
          have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
          exact (hclipleft x hx).symm.trans (hh1.trans (hclipleft y hy))
        · exact congrArg (fun z : I × BandWidth => z.2) hh
      · have hy' : 1 < (y.1 : ℝ) := lt_of_not_ge hy
        have ha := hQinterior (projIcc 0 1 zero_le_one ((y.1 : ℝ)-1))
          (by rw [hclipright y hy']; linarith)
          (by rw [hclipright y hy']; linarith) y.2
        exact False.elim (ha ⟨_, he⟩)
      · have hx' : 1 < (x.1 : ℝ) := lt_of_not_ge hx
        have ha := hQinterior (projIcc 0 1 zero_le_one ((x.1 : ℝ)-1))
          (by rw [hclipright x hx']; linarith)
          (by rw [hclipright x hx']; linarith) x.2
        exact False.elim (ha ⟨_, he.symm⟩)
      · have hh := hQembedded.injective he
        apply Prod.ext
        · apply Subtype.ext
          have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
          rw [hclipright x (lt_of_not_ge hx), hclipright y (lt_of_not_ge hy)] at hh1
          linarith
        · exact congrArg (fun z : I × BandWidth => z.2) hh
    let f : EuclideanSpace ℝ (Fin 2) → S := fun z =>
      F (projIcc 0 2 (by norm_num) (z 0), projIcc (-1) 1 (by norm_num) (z 1))
    let U : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z 0 ∈ Ioo 0 2 ∧ z 1 ∈ Ioo (-1) 1}
    have hUopen : IsOpen U := (isOpen_Ioo.preimage (by fun_prop)).inter
      (isOpen_Ioo.preimage (by fun_prop))
    have hfcont : Continuous f := hFcont.comp
      ((continuous_projIcc.comp (by fun_prop)).prodMk
        (continuous_projIcc.comp (by fun_prop)))
    have hclip (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ U) :
        (projIcc 0 2 (by norm_num) (z 0) : ℝ) = z 0 ∧
        (projIcc (-1) 1 (by norm_num) (z 1) : ℝ) = z 1 := by
      constructor
      · exact congrArg Subtype.val (projIcc_of_mem (by norm_num) ⟨hz.1.1.le,hz.1.2.le⟩)
      · exact congrArg Subtype.val (projIcc_of_mem (by norm_num) ⟨hz.2.1.le,hz.2.2.le⟩)
    have hfinj : InjOn f U := by
      intro x hx y hy he
      have hh := hFinj
        (projIcc 0 2 (by norm_num) (x 0), projIcc (-1) 1 (by norm_num) (x 1))
        (projIcc 0 2 (by norm_num) (y 0), projIcc (-1) 1 (by norm_num) (y 1))
        (by rw [(hclip x hx).1]; exact hx.1.1)
        (by rw [(hclip x hx).1]; exact hx.1.2)
        (by rw [(hclip y hy).1]; exact hy.1.1)
        (by rw [(hclip y hy).1]; exact hy.1.2) he
      have h0 := congrArg (fun z : P => (z.1 : ℝ)) hh
      have h1 := congrArg (fun z : P => (z.2 : ℝ)) hh
      rw [(hclip x hx).1, (hclip y hy).1] at h0
      rw [(hclip x hx).2, (hclip y hy).2] at h1
      ext i
      fin_cases i
      · exact h0
      · exact h1
    have hTubeChartOpen : IsOpen (f '' U) :=
      surface_invariance_of_domain_probe f U hUopen hfcont.continuousOn hfinj
    let fU : U → S := fun z => f z
    have hfUopen : IsOpenMap fU := by
      intro V hV
      let W : Set (EuclideanSpace ℝ (Fin 2)) := Subtype.val '' V
      have hW : IsOpen W := hUopen.isOpenMap_subtype_val V hV
      have hWU : W ⊆ U := by
        rintro z ⟨w,hw,rfl⟩
        exact w.property
      have hWi : InjOn f W := hfinj.mono hWU
      have heq : fU '' V = f '' W := by
        simp only [W, Set.image_image]
        rfl
      rw [heq]
      exact surface_invariance_of_domain_probe f W hW hfcont.continuousOn hWi
    have hfUembedded : IsOpenEmbedding fU :=
      IsOpenEmbedding.of_continuous_injective_isOpenMap
        (hfcont.comp continuous_subtype_val)
        (by intro x y he; exact Subtype.ext (hfinj x.property y.property he)) hfUopen
    let tubeChart : U ≃ₜ Set.range fU := hfUembedded.isEmbedding.toHomeomorph
    have hMeet : Set.range Q ∩ Set.range band =
        Set.range (fun t => Q (0,t)) ∪ Set.range (fun t => Q (1,t)) := by
      ext z
      constructor
      · rintro ⟨⟨⟨u,t⟩,hu⟩, hBz⟩
        by_cases h0 : u = 0
        · exact Or.inl ⟨t, by simpa [h0] using hu⟩
        by_cases h1 : u = 1
        · exact Or.inr ⟨t, by simpa [h1] using hu⟩
        have hu0 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (by
          intro heq; exact h0 (Subtype.ext heq.symm))
        have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 (by
          intro heq; exact h1 (Subtype.ext heq))
        exact False.elim (hQinterior u hu0 hu1 t (hu.symm ▸ hBz))
      · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
        · exact ⟨⟨(0,t),rfl⟩, ⟨(1,t), (hQtop t).symm⟩⟩
        · exact ⟨⟨(1,t),rfl⟩, ⟨(0,flipBandWidth true t), (hQbottom t).symm⟩⟩
    have hQband (u v : I) (t w : BandWidth) (he : Q (u,t) = band (v,w)) :
        (u = 0 ∧ v = 1 ∧ w = t) ∨
        (u = 1 ∧ v = 0 ∧ w = flipBandWidth true t) := by
      by_cases h0 : u = 0
      · subst u
        have hh := hband.injective ((hQtop t).symm.trans he)
        exact Or.inl ⟨rfl, (congrArg Prod.fst hh).symm,
          (congrArg Prod.snd hh).symm⟩
      by_cases h1 : u = 1
      · subst u
        have hh := hband.injective ((hQbottom t).symm.trans he)
        exact Or.inr ⟨rfl, (congrArg Prod.fst hh).symm,
          (congrArg Prod.snd hh).symm⟩
      have hu0 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (by
        intro heq; exact h0 (Subtype.ext heq.symm))
      have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 (by
        intro heq; exact h1 (Subtype.ext heq))
      exact False.elim (hQinterior u hu0 hu1 t ⟨(v,w),he.symm⟩)
    let left2 : P → S := fun z => Q (projIcc 0 1 zero_le_one (z.1 : ℝ), z.2)
    let right2 : P → S := fun z => band
      (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1), flipBandWidth true z.2)
    let G : P → S := fun z => if (z.1 : ℝ) ≤ 1 then left2 z else right2 z
    have hleft2 : Continuous left2 := hQembedded.continuous.comp
      ((continuous_projIcc.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
    have hflip : Continuous (flipBandWidth true) :=
      continuous_subtype_val.neg.subtype_mk _
    have hright2 : Continuous right2 := hband.continuous.comp
      ((continuous_projIcc.comp ((continuous_subtype_val.comp continuous_fst).sub continuous_const)).prodMk
        (hflip.comp continuous_snd))
    have hGcont : Continuous G := by
      apply continuous_if_le (continuous_subtype_val.comp continuous_fst) continuous_const
        hleft2.continuousOn hright2.continuousOn
      intro z hz
      change (z.1 : ℝ) = 1 at hz
      change Q (projIcc 0 1 zero_le_one (z.1 : ℝ), z.2) =
        band (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1), flipBandWidth true z.2)
      rw [hz]
      simp only [sub_self, projIcc_of_mem zero_le_one (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num),
        projIcc_of_mem zero_le_one (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)]
      exact hQbottom z.2
    have hGinj (x y : P) (hx0 : 0 < (x.1 : ℝ)) (hx2 : (x.1 : ℝ) < 2)
        (hy0 : 0 < (y.1 : ℝ)) (hy2 : (y.1 : ℝ) < 2) (he : G x = G y) : x = y := by
      have hclipleft (z : P) (hz : (z.1 : ℝ) ≤ 1) :
          (projIcc 0 1 zero_le_one (z.1 : ℝ) : ℝ) = (z.1 : ℝ) := by
        simp only [projIcc_of_mem zero_le_one ⟨z.1.property.1, hz⟩]
      have hclipright (z : P) (hz : 1 < (z.1 : ℝ)) :
          (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1) : ℝ) = (z.1 : ℝ)-1 := by
        rw [projIcc_of_mem zero_le_one (show (z.1 : ℝ)-1 ∈ Icc (0:ℝ) 1 by
          constructor <;> linarith [z.1.property.2])]
      dsimp only [G] at he
      split_ifs at he with hx hy hy
      · have hh := hQembedded.injective he
        apply Prod.ext
        · apply Subtype.ext
          have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
          exact (hclipleft x hx).symm.trans (hh1.trans (hclipleft y hy))
        · exact congrArg (fun z : I × BandWidth => z.2) hh
      · have hh := hQband _ _ _ _ he
        rcases hh with ⟨h0,_,_⟩ | ⟨_,h0,_⟩
        · have hv := congrArg Subtype.val h0
          rw [hclipleft x hx] at hv
          norm_num at hv
          linarith
        · have hv := congrArg Subtype.val h0
          rw [hclipright y (lt_of_not_ge hy)] at hv
          norm_num at hv
          linarith
      · have hh := hQband _ _ _ _ he.symm
        rcases hh with ⟨h0,_,_⟩ | ⟨_,h0,_⟩
        · have hv := congrArg Subtype.val h0
          rw [hclipleft y hy] at hv
          norm_num at hv
          linarith
        · have hv := congrArg Subtype.val h0
          rw [hclipright x (lt_of_not_ge hx)] at hv
          norm_num at hv
          linarith
      · have hh := hband.injective he
        apply Prod.ext
        · apply Subtype.ext
          have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
          rw [hclipright x (lt_of_not_ge hx), hclipright y (lt_of_not_ge hy)] at hh1
          linarith
        · apply Subtype.ext
          have hh2 := congrArg (fun z : I × BandWidth => (z.2 : ℝ)) hh
          change -(x.2 : ℝ) = -(y.2 : ℝ) at hh2
          exact neg_injective hh2
    let g : EuclideanSpace ℝ (Fin 2) → S := fun z =>
      G (projIcc 0 2 (by norm_num) (z 0), projIcc (-1) 1 (by norm_num) (z 1))
    have hgcont : Continuous g := hGcont.comp
      ((continuous_projIcc.comp (by fun_prop)).prodMk
        (continuous_projIcc.comp (by fun_prop)))
    have hginj : InjOn g U := by
      intro x hx y hy he
      have hh := hGinj
        (projIcc 0 2 (by norm_num) (x 0), projIcc (-1) 1 (by norm_num) (x 1))
        (projIcc 0 2 (by norm_num) (y 0), projIcc (-1) 1 (by norm_num) (y 1))
        (by rw [(hclip x hx).1]; exact hx.1.1)
        (by rw [(hclip x hx).1]; exact hx.1.2)
        (by rw [(hclip y hy).1]; exact hy.1.1)
        (by rw [(hclip y hy).1]; exact hy.1.2) he
      have h0 := congrArg (fun z : P => (z.1 : ℝ)) hh
      have h1 := congrArg (fun z : P => (z.2 : ℝ)) hh
      rw [(hclip x hx).1, (hclip y hy).1] at h0
      rw [(hclip x hx).2, (hclip y hy).2] at h1
      ext i
      fin_cases i
      · exact h0
      · exact h1
    have hTubeChartOpen2 : IsOpen (g '' U) :=
      surface_invariance_of_domain_probe g U hUopen hgcont.continuousOn hginj
    let gU : U → S := fun z => g z
    have hgUopen : IsOpenMap gU := by
      intro V hV
      let W : Set (EuclideanSpace ℝ (Fin 2)) := Subtype.val '' V
      have hW : IsOpen W := hUopen.isOpenMap_subtype_val V hV
      have hWU : W ⊆ U := by
        rintro z ⟨w,hw,rfl⟩
        exact w.property
      have hWi : InjOn g W := hginj.mono hWU
      have heq : gU '' V = g '' W := by
        simp only [W, Set.image_image]
        rfl
      rw [heq]
      exact surface_invariance_of_domain_probe g W hW hgcont.continuousOn hWi
    have hgUembedded : IsOpenEmbedding gU :=
      IsOpenEmbedding.of_continuous_injective_isOpenMap
        (hgcont.comp continuous_subtype_val)
        (by intro x y he; exact Subtype.ext (hginj x.property y.property he)) hgUopen
    let tubeChart2 : U ≃ₜ Set.range gU := hgUembedded.isEmbedding.toHomeomorph
    have hFG (u : I) (hu0 : 0 < (u : ℝ)) (t : BandWidth) :
        F (⟨(u : ℝ)+1, by constructor <;> linarith [u.property.1,u.property.2]⟩, t) =
        G (⟨(u : ℝ), ⟨u.property.1, by linarith [u.property.2]⟩⟩, t) := by
      dsimp only [F,G]
      rw [if_neg (show ¬ (u : ℝ)+1 ≤ 1 by linarith), if_pos u.property.2]
      dsimp only [right,left2]
      simp only [add_sub_cancel_right]
    have hGF (u : I) (hu0 : 0 < (u : ℝ)) (t : BandWidth) :
        F (⟨(u : ℝ), ⟨u.property.1, by linarith [u.property.2]⟩⟩, t) =
        G (⟨(u : ℝ)+1, by constructor <;> linarith [u.property.1,u.property.2]⟩,
          flipBandWidth true t) := by
      dsimp only [F,G]
      rw [if_pos u.property.2, if_neg (show ¬ (u : ℝ)+1 ≤ 1 by linarith)]
      dsimp only [left,right2]
      simp only [add_sub_cancel_right]
      have hflipflip : flipBandWidth true (flipBandWidth true t) = t := by
        apply Subtype.ext
        simp [flipBandWidth]
      rw [hflipflip]
    have hshift (p v : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (hR : 0 < R)
        (hv : ‖v‖ < R/2) :
        ∃ H : AmbientIsotopy (EuclideanSpace ℝ (Fin 2)),
          (∀ t x, x ∈ Metric.closedBall p (R/2) → H.map (t,x) = x+(t:ℝ) • v) ∧
          (∀ t x, x ∉ Metric.closedBall p R → H.map (t,x) = x) := by
      obtain ⟨K,hflat,hfix⟩ := plane_flat_bump_translation R hR v hv
      let e := Homeomorph.addRight (-p)
      let H : AmbientIsotopy (EuclideanSpace ℝ (Fin 2)) := {
        map := ⟨fun z => K.map (z.1,z.2-p)+p,
          (K.map.continuous.comp (continuous_fst.prodMk
            (continuous_snd.sub continuous_const))).add continuous_const⟩
        homeomorphism_at := fun t => by
          obtain ⟨h,hh⟩ := K.homeomorphism_at t
          refine ⟨(e.trans h).trans e.symm, ?_⟩
          intro x
          simpa [e, Homeomorph.addRight_symm, sub_eq_add_neg] using congrArg (fun y => y+p) (hh (x-p))
        at_zero := fun x => by
          change K.map (⟨0, by norm_num⟩,x-p)+p = x
          rw [K.at_zero]
          module }
      have hdist (x : EuclideanSpace ℝ (Fin 2)) : dist (x-p) 0 = dist x p := by
        rw [_root_.dist_eq_norm, _root_.dist_eq_norm]
        simp
      refine ⟨H, ?_, ?_⟩
      · intro t x hx
        change K.map (t,x-p)+p = x+(t:ℝ) • v
        have hx0 : x-p ∈ Metric.closedBall 0 (R/2) := by
          simpa only [Metric.mem_closedBall, hdist] using hx
        rw [hflat t (x-p) hx0]
        module
      · intro t x hx
        change K.map (t,x-p)+p = x
        have hx0 : x-p ∉ Metric.closedBall 0 R := by
          simpa only [Metric.mem_closedBall, hdist] using hx
        rw [hfix t (x-p) hx0]
        module
    have hpushChart (q : U → S) (hq : IsOpenEmbedding q)
        (p v : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (hR : 0 < R)
        (hv : ‖v‖ < R/2) (hCU : Metric.closedBall p R ⊆ U) :
        ∃ H : AmbientIsotopy S, ∀ (t : Interval) (x y : U),
          (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.closedBall p (R/2) →
          (y : EuclideanSpace ℝ (Fin 2)) = (x : EuclideanSpace ℝ (Fin 2))+(t:ℝ) • v →
          H.map (t,q x) = q y := by
      obtain ⟨L,hL,hfix⟩ := hshift p v R hR hv
      let E : U ≃ₜ Set.range q := hq.isEmbedding.toHomeomorph
      have hsource : IsOpen (Set.range q) := by
        simpa only [Set.image_univ] using hq.isOpenMap Set.univ isOpen_univ
      obtain ⟨K,H,hK,hH,_⟩ := position_surface_chart_lift S (Set.range q) U hsource
        E.symm (Metric.closedBall p R) (isCompact_closedBall _ _) hCU L hfix
      refine ⟨H, ?_⟩
      intro t x y hx hy
      have hcoord : E.symm (K.map (t,E x)) = y := by
        apply Subtype.ext
        have hh := hK t (E x)
        rw [E.symm_apply_apply, hL t (x : EuclideanSpace ℝ (Fin 2)) hx] at hh
        exact hh.trans hy.symm
      have hKy : K.map (t,E x) = E y := by
        apply E.symm.injective
        rw [hcoord,E.symm_apply_apply]
      change H.map (t,(E x : S)) = (E y : S)
      rw [hH t (E x),hKy]
    let p0 : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (1/2) 0
    let v : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (1/16) 0
    have hvnorm : ‖v‖ = 1/16 := by
      have hh := EuclideanSpace.real_norm_sq_eq v
      norm_num [v, Schoenflies.Plane.mk, Fin.sum_univ_two] at hh
      nlinarith [norm_nonneg v]
    have hcenters (n : ℕ) (hn : n ≤ 16) :
        Metric.closedBall (p0+(n:ℝ) • v) (1/4) ⊆ U := by
      intro z hz
      have hd : ‖z-(p0+(n:ℝ) • v)‖ ≤ 1/4 := by
        rw [← _root_.dist_eq_norm]
        exact Metric.mem_closedBall.mp hz
      have hcoord (i : Fin 2) : |z i-(p0+(n:ℝ) • v) i| ≤ 1/4 := by
        have hh := PiLp.norm_apply_le (z-(p0+(n:ℝ) • v)) i
        change |z i-(p0+(n:ℝ) • v) i| ≤ ‖z-(p0+(n:ℝ) • v)‖ at hh
        exact hh.trans hd
      have h0 := abs_le.mp (hcoord 0)
      have h1 := abs_le.mp (hcoord 1)
      have hn' : (n:ℝ) ≤ 16 := by exact_mod_cast hn
      have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
      change (0 < z 0 ∧ z 0 < 2) ∧ (-1 < z 1 ∧ z 1 < 1)
      norm_num [p0,v,Schoenflies.Plane.mk] at h0 h1
      constructor <;> constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]
    have hcompose (H K : AmbientIsotopy S) :
        ∃ L : AmbientIsotopy S, ∀ t x, L.map (t,x) = K.map (t,H.map (t,x)) := by
      refine ⟨{ map := ⟨fun z => K.map (z.1,H.map z), K.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩, homeomorphism_at := ?_, at_zero := ?_ }, fun t x => rfl⟩
      · intro t
        obtain ⟨hH,hh⟩ := H.homeomorphism_at t
        obtain ⟨hK,hk⟩ := K.homeomorphism_at t
        refine ⟨hH.trans hK, ?_⟩
        intro x
        change hK (hH x) = K.map (t,H.map (t,x))
        rw [hk,hh]
      · intro x
        change K.map (⟨0, by norm_num⟩,H.map (⟨0, by norm_num⟩,x)) = x
        rw [H.at_zero,K.at_zero]
    have hhalf (q : U → S) (hq : IsOpenEmbedding q) :
        ∀ n : ℕ, n ≤ 16 → ∃ H : AmbientIsotopy S, ∀ x y : U,
          (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.closedBall p0 (1/16) →
          (y : EuclideanSpace ℝ (Fin 2)) = (x : EuclideanSpace ℝ (Fin 2))+(n:ℝ) • v →
          H.finalMap (q x) = q y := by
      intro n
      induction n with
      | zero =>
        intro hn
        let H : AmbientIsotopy S := {
          map := ⟨Prod.snd, continuous_snd⟩
          homeomorphism_at := fun _ => ⟨Homeomorph.refl S, fun _ => rfl⟩
          at_zero := fun _ => rfl }
        refine ⟨H, ?_⟩
        intro x y hx hy
        have hxy : x = y := Subtype.ext (by simpa using hy.symm)
        rw [← hxy]
        rfl
      | succ n ih =>
        intro hn
        have hn16 : n ≤ 16 := by omega
        obtain ⟨H,hH⟩ := ih hn16
        obtain ⟨K,hK⟩ := hpushChart q hq (p0+(n:ℝ) • v) v (1/4)
          (by norm_num) (by rw [hvnorm]; norm_num) (hcenters n hn16)
        obtain ⟨L,hL⟩ := hcompose H K
        refine ⟨L, ?_⟩
        intro x y hx hy
        have hxnorm : ‖(x : EuclideanSpace ℝ (Fin 2))-p0‖ ≤ 1/16 := by
          rw [← _root_.dist_eq_norm]
          exact Metric.mem_closedBall.mp hx
        have hmid : (x : EuclideanSpace ℝ (Fin 2))+(n:ℝ) • v ∈
            Metric.closedBall (p0+(n:ℝ) • v) (1/16) := by
          rw [Metric.mem_closedBall,_root_.dist_eq_norm]
          have heq : (x : EuclideanSpace ℝ (Fin 2))+(n:ℝ) • v-(p0+(n:ℝ) • v) =
              (x : EuclideanSpace ℝ (Fin 2))-p0 := by module
          rw [heq]
          exact hxnorm
        let z : U := ⟨(x : EuclideanSpace ℝ (Fin 2))+(n:ℝ) • v,
          hcenters n hn16 (Metric.closedBall_subset_closedBall (by norm_num) hmid)⟩
        have hzflat : (z : EuclideanSpace ℝ (Fin 2)) ∈
            Metric.closedBall (p0+(n:ℝ) • v) ((1/4)/2) :=
          Metric.closedBall_subset_closedBall (by norm_num) hmid
        have hyz : (y : EuclideanSpace ℝ (Fin 2)) = (z : EuclideanSpace ℝ (Fin 2))+
            ((⟨1,by norm_num⟩ : Interval) : ℝ) • v := by
          rw [hy]
          dsimp [z]
          push_cast
          module
        have hstep := hK (⟨1,by norm_num⟩ : Interval) z y hzflat hyz
        change L.map (⟨1,by norm_num⟩,q x) = q y
        rw [hL]
        change K.finalMap (H.finalMap (q x)) = q y
        rw [hH x z hx rfl]
        exact hstep
    obtain ⟨Hf,hHf⟩ := hhalf fU hfUembedded 16 (by omega)
    obtain ⟨Hg,hHg⟩ := hhalf gU hgUembedded 16 (by omega)
    obtain ⟨H,hH⟩ := hcompose Hf Hg
    have hfcoords (u t : ℝ) (hu : u ∈ Icc (0:ℝ) 2) (ht : t ∈ Icc (-1:ℝ) 1) :
        f (Schoenflies.Plane.mk u t) = F (⟨u,hu⟩,⟨t,ht⟩) := by
      simp [f,Schoenflies.Plane.mk,projIcc_of_mem (show (0:ℝ) ≤ 2 by norm_num) hu,
        projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) ht]
    have hgcoords (u t : ℝ) (hu : u ∈ Icc (0:ℝ) 2) (ht : t ∈ Icc (-1:ℝ) 1) :
        g (Schoenflies.Plane.mk u t) = G (⟨u,hu⟩,⟨t,ht⟩) := by
      simp [g,Schoenflies.Plane.mk,projIcc_of_mem (show (0:ℝ) ≤ 2 by norm_num) hu,
        projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) ht]
    have hFGcoords (u : I) (hu0 : 0 < (u:ℝ)) (t : BandWidth) :
        f (Schoenflies.Plane.mk ((u:ℝ)+1) t) = g (Schoenflies.Plane.mk u t) := by
      rw [hfcoords _ _ (by constructor <;> linarith [u.property.1,u.property.2]) t.property,
        hgcoords _ _ ⟨u.property.1,by linarith [u.property.2]⟩ t.property]
      exact hFG u hu0 t
    have hGFcoords (u : I) (hu0 : 0 < (u:ℝ)) (t : BandWidth) :
        f (Schoenflies.Plane.mk u t) = g (Schoenflies.Plane.mk ((u:ℝ)+1) (-(t:ℝ))) := by
      rw [hfcoords _ _ ⟨u.property.1,by linarith [u.property.2]⟩ t.property,
        hgcoords _ _ (by constructor <;> linarith [u.property.1,u.property.2])
          (by constructor <;> linarith [t.property.1,t.property.2])]
      exact hGF u hu0 t
    have hnear (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ Metric.closedBall p0 (1/16)) :
        z 0 ∈ Ioo (0:ℝ) 1 ∧ z 1 ∈ Ioo (-1:ℝ) 1 := by
      have hd : ‖z-p0‖ ≤ 1/16 := by
        rw [← _root_.dist_eq_norm]
        exact Metric.mem_closedBall.mp hz
      have hcoord (i : Fin 2) : |z i-p0 i| ≤ 1/16 := by
        have hh := PiLp.norm_apply_le (z-p0) i
        change |z i-p0 i| ≤ ‖z-p0‖ at hh
        exact hh.trans hd
      have h0 := abs_le.mp (hcoord 0)
      have h1 := abs_le.mp (hcoord 1)
      norm_num [p0,Schoenflies.Plane.mk] at h0 h1
      constructor <;> constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]
    let w : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk 1 0
    have h16v : (16:ℝ) • v = w := by
      ext i
      fin_cases i <;> norm_num [v,w,Schoenflies.Plane.mk]
    let refl : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => Schoenflies.Plane.mk (z 0) (-(z 1))
    have hreturn (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ Metric.closedBall p0 (1/16)) :
        H.finalMap (f z) = f (refl z) := by
      obtain ⟨hz0,hz1⟩ := hnear z hz
      have hzU : z ∈ U := ⟨⟨hz0.1,by linarith [hz0.2]⟩,hz1⟩
      have hzwU : z+w ∈ U := by
        change ((z+w) 0 ∈ Ioo (0:ℝ) 2) ∧ ((z+w) 1 ∈ Ioo (-1:ℝ) 1)
        norm_num [w,Schoenflies.Plane.mk]
        constructor <;> constructor <;> linarith [hz0.1,hz0.2,hz1.1,hz1.2]
      let x : U := ⟨z,hzU⟩
      let y : U := ⟨z+w,hzwU⟩
      have hy : (y : EuclideanSpace ℝ (Fin 2)) = (x : EuclideanSpace ℝ (Fin 2))+(16:ℝ) • v := by
        dsimp [x,y]
        rw [h16v]
      have hfirst := hHf x y hz hy
      have hsecond := hHg x y hz hy
      change Hf.finalMap (f z) = f (z+w) at hfirst
      change Hg.finalMap (g z) = g (z+w) at hsecond
      let u : I := ⟨z 0,⟨hz0.1.le,hz0.2.le⟩⟩
      let t : BandWidth := ⟨z 1,⟨hz1.1.le,hz1.2.le⟩⟩
      have hzmk : Schoenflies.Plane.mk (z 0) (z 1) = z := by
        ext i
        fin_cases i <;> rfl
      have hplus : z+w = Schoenflies.Plane.mk (z 0+1) (z 1) := by
        ext i
        fin_cases i <;> simp [w,Schoenflies.Plane.mk]
      have hfg : f (z+w) = g z := by
        rw [hplus,← hzmk]
        exact hFGcoords u hz0.1 t
      have hgf : g (z+w) = f (refl z) := by
        rw [hplus]
        let tn : BandWidth := ⟨-(z 1),by constructor <;> linarith [hz1.1,hz1.2]⟩
        have hh := hGFcoords u hz0.1 tn
        simpa only [u,tn,refl,neg_neg] using hh.symm
      change H.map (⟨1,by norm_num⟩,f z) = f (refl z)
      rw [hH]
      change Hg.finalMap (Hf.finalMap (f z)) = f (refl z)
      rw [hfirst,hfg,hsecond,hgf]
    have hp0U : p0 ∈ U := by
      apply hcenters 0 (by omega)
      simp
    letI : Nonempty U := ⟨⟨p0,hp0U⟩⟩
    let qE := hfUembedded.toOpenPartialHomeomorph fU
    have hqtarget : qE.target = Set.range fU := by
      simp [qE,IsOpenEmbedding.toOpenPartialHomeomorph_target]
    let A : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S := {
      toFun := f
      invFun := fun y => (qE.symm y : EuclideanSpace ℝ (Fin 2))
      source := U
      target := Set.range fU
      map_source' := fun z hz => ⟨⟨z,hz⟩,rfl⟩
      map_target' := fun y hy => (qE.symm y).property
      left_inv' := fun z hz => by
        have hh := hfUembedded.toOpenPartialHomeomorph_left_inv (f := fU) (x := ⟨z,hz⟩)
        exact congrArg Subtype.val hh
      right_inv' := fun y hy => by
        exact hfUembedded.toOpenPartialHomeomorph_right_inv (f := fU) hy
      continuousOn_toFun := hfcont.continuousOn
      continuousOn_invFun := by
        apply continuous_subtype_val.comp_continuousOn
        simpa only [OpenPartialHomeomorph.symm_source,hqtarget] using qE.symm.continuousOn
      open_source := hUopen
      open_target := by simpa only [Set.image_univ] using hfUopen Set.univ isOpen_univ }
    have hAapply (z : EuclideanSpace ℝ (Fin 2)) : A z = f z := rfl
    let x : S := f p0
    have hfixx : H.finalMap x = x := by
      have hh := hreturn p0 (by simp)
      have hrefl : refl p0 = p0 := by ext i; fin_cases i <;> simp [refl,p0,Schoenflies.Plane.mk]
      simpa only [hrefl] using hh
    let Fend : C(S,S) := ⟨H.finalMap,
      H.map.continuous.comp (continuous_const.prodMk continuous_id)⟩
    have hpres : ∀ y ∈ ({x}ᶜ : Set S), Fend y ∈ ({x}ᶜ : Set S) := by
      intro y hy
      change y ≠ x at hy
      change Fend y ≠ x
      intro hh
      obtain ⟨e,he⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
      apply hy
      apply e.injective
      rw [he,he]
      exact hh.trans hfixx.symm
    have hhom : ContinuousMap.Homotopic Fend (ContinuousMap.id S) := by
      apply ContinuousMap.Homotopic.symm
      exact ⟨{ toContinuousMap := H.map, map_zero_left := H.at_zero, map_one_left := fun _ => rfl }⟩
    let c : (EuclideanSpace ℝ (Fin 2)) ≃ₜ (ℝ × ℝ) := {
      toFun := fun z => (z 0,z 1)
      invFun := fun z => Schoenflies.Plane.mk z.1 z.2
      left_inv := fun z => by ext i; fin_cases i <;> rfl
      right_inv := fun z => by rcases z with ⟨u,t⟩; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let b : (EuclideanSpace ℝ (Fin 2)) ≃ₜ (ℝ × ℝ) :=
      (Homeomorph.addRight (-p0)).trans c
    let e : OpenPartialHomeomorph S (ℝ × ℝ) := A.symm.trans b.toOpenPartialHomeomorph
    have hxsource : x ∈ e.source := ⟨A.map_source hp0U,Set.mem_univ _⟩
    have hex : e x = 0 := by
      change c (A.symm x + -p0) = 0
      have hAx : A.symm x = p0 := A.left_inv hp0U
      rw [hAx,add_neg_cancel]
      rfl
    have hbinv (z : ℝ × ℝ) : b.symm z = Schoenflies.Plane.mk z.1 z.2+p0 := by
      change (Homeomorph.addRight (-p0)).symm (c.symm z) = Schoenflies.Plane.mk z.1 z.2+p0
      rw [Homeomorph.addRight_symm,neg_neg]
      rfl
    have heinv (z : ℝ × ℝ) : e.symm z = f (Schoenflies.Plane.mk z.1 z.2+p0) := by
      change A (b.symm z) = _
      rw [hbinv]
      rfl
    have hsmallball (z : ℝ × ℝ) (hz : z ∈ Metric.closedBall (0 : ℝ × ℝ) (1/64)) :
        Schoenflies.Plane.mk z.1 z.2+p0 ∈ Metric.closedBall p0 (1/16) := by
      have hp : |z.1| ≤ 1/64 ∧ |z.2| ≤ 1/64 := by
        have hd : dist z ((0,0) : ℝ × ℝ) ≤ 1/64 := Metric.mem_closedBall.mp hz
        rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq] at hd
        simpa only [sub_zero,max_le_iff] using hd
      have h1sq : z.1^2 ≤ (1/64:ℝ)^2 := by
        have hh := (sq_le_sq₀ (abs_nonneg z.1) (by norm_num : (0:ℝ) ≤ 1/64)).mpr hp.1
        simpa only [sq_abs] using hh
      have h2sq : z.2^2 ≤ (1/64:ℝ)^2 := by
        have hh := (sq_le_sq₀ (abs_nonneg z.2) (by norm_num : (0:ℝ) ≤ 1/64)).mpr hp.2
        simpa only [sq_abs] using hh
      have hh := EuclideanSpace.real_norm_sq_eq (Schoenflies.Plane.mk z.1 z.2)
      norm_num [Schoenflies.Plane.mk,Fin.sum_univ_two] at hh
      rw [Metric.mem_closedBall,_root_.dist_eq_norm,add_sub_cancel_right]
      nlinarith [norm_nonneg (Schoenflies.Plane.mk z.1 z.2)]
    have hball : Metric.closedBall (0 : ℝ × ℝ) (1/64) ⊆ e.target := by
      intro z hz
      have hsmall := hsmallball z hz
      have hzU : Schoenflies.Plane.mk z.1 z.2+p0 ∈ U :=
        hcenters 0 (by omega) (by simpa using Metric.closedBall_subset_closedBall (by norm_num : (1/16:ℝ) ≤ 1/4) hsmall)
      change z ∈ Set.univ ∩ b.symm ⁻¹' A.source
      refine ⟨Set.mem_univ _, ?_⟩
      change b.symm z ∈ U
      rw [hbinv]
      exact hzU
    have hgerm : ∀ z ∈ Metric.ball (0 : ℝ × ℝ) (1/64),
        Fend (e.symm z) = e.symm (planeReflection z) := by
      intro z hz
      rw [heinv,heinv]
      change H.finalMap (f (Schoenflies.Plane.mk z.1 z.2+p0)) = _
      rw [hreturn _ (hsmallball z (Metric.ball_subset_closedBall hz))]
      apply congrArg f
      ext i
      fin_cases i <;> simp [refl,p0,planeReflection,Schoenflies.Plane.mk]
    have hnegative := chart_reflection_germ_relativeHomologyMap S x e hxsource hex
      Fend hpres (1/64) (by norm_num) hball hgerm
    exact ⟨x,⟨{ map := Fend, preserves := hpres, isotopy := hhom, acts_neg := hnegative }⟩⟩
  classical
  have localArc (z : Circle) :
    let e := chartAt (EuclideanSpace ℝ (Fin 1)) z
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) (b.map z)
    ∃ (r : ℝ) (U : Set S), 0 < r ∧ IsOpen U ∧ b.map z ∈ U ∧
      U ⊆ c.source ∧
      Metric.closedBall (e z) r ⊆ e.target ∧
      (b.map ∘ e.symm) '' Metric.closedBall (e z) r ⊆ c.source ∧
      b.image ∩ U ⊆ b.map '' (e.symm '' Metric.ball (e z) r) := by
    classical
    dsimp only
    let e := chartAt (EuclideanSpace ℝ (Fin 1)) z
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) (b.map z)
    have hz : z ∈ e.source := mem_chart_source _ z
    have haz : b.map z ∈ c.source := mem_chart_source _ (b.map z)
    let V := e.target ∩ e.symm ⁻¹' (b.map ⁻¹' c.source)
    have hVopen : IsOpen V := e.isOpen_inter_preimage_symm
      (c.open_source.preimage b.embedded.continuous)
    have hVz : e z ∈ V := by
      exact ⟨e.map_source hz, by simpa [e.left_inv hz] using haz⟩
    obtain ⟨d, hd, hdV⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hVz)
    let r := d / 2
    have hr : 0 < r := by dsimp [r]; linarith
    have hballV : Metric.closedBall (e z) r ⊆ V := by
      intro x hx
      apply hdV
      exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx)
        (by dsimp [r]; linarith))
    have hbt : Metric.closedBall (e z) r ⊆ e.target := fun x hx => (hballV hx).1
    let W := e.symm '' Metric.ball (e z) r
    have hWopen : IsOpen W := e.symm.isOpen_image_of_subset_source
      Metric.isOpen_ball (fun x hx => hbt (Metric.ball_subset_closedBall hx))
    have hzW : z ∈ W := by
      exact ⟨e z, Metric.mem_ball_self hr, e.left_inv hz⟩
    have hclosed : IsClosed (b.map '' Wᶜ) :=
      (hWopen.isClosed_compl.isCompact.image b.embedded.continuous).isClosed
    let U := c.source ∩ (b.map '' Wᶜ)ᶜ
    have hUopen : IsOpen U := c.open_source.inter hclosed.isOpen_compl
    have hazU : b.map z ∈ U := by
      refine ⟨haz, ?_⟩
      rintro ⟨w, hw, heq⟩
      exact hw ((b.embedded.injective heq) ▸ hzW)
    refine ⟨r, U, hr, hUopen, hazU, inter_subset_left, hbt, ?_, ?_⟩
    · rintro x ⟨y, hy, rfl⟩
      exact (hballV hy).2
    · rintro x ⟨⟨w, rfl⟩, hxU⟩
      refine ⟨w, ?_, rfl⟩
      by_contra hw
      exact hxU.2 ⟨w, hw, rfl⟩
  choose radius U hrad hUopen hcenter hUchart htarget hcompactArc hisolate using localArc
  have hcover : b.image ⊆ ⋃ w : Circle, U w := by
    rintro x ⟨w, rfl⟩
    exact Set.mem_iUnion.mpr ⟨w, hcenter w⟩
  obtain ⟨centers, hfiniteCover⟩ :=
    (isCompact_range b.embedded.continuous).elim_finite_subcover U hUopen hcover
  have makeSquare
    (b : CurveComplex.Curve S) :
    ∃ ε : ℝ, ∃ hε : 0 < ε,
      ∃ square : Metric.closedBall ((0,0) : ℝ × ℝ) ε → S,
        IsEmbedding square ∧
        (∀ z, square z ∈ b.image ↔ (z : ℝ × ℝ).1 = 0) ∧
        square ⟨(0,0),by simp [Metric.mem_closedBall,hε.le]⟩ = b.map 1 := by
    obtain ⟨U,V,hp,h,hU,hV,hp0,haxis⟩ :=
      embedded_curve_has_local_axis_chart b (b.map 1) (Set.mem_range_self 1)
    have hzero : ((0,0) : ℝ × ℝ) ∈ V := hp0 ▸ (h ⟨b.map 1,hp⟩).property
    obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV (0,0) hzero
    let ε : ℝ := r/2
    have hε : 0 < ε := half_pos hr
    have hεr : ε < r := half_lt_self hr
    let q : Metric.closedBall ((0,0) : ℝ × ℝ) ε → V :=
      fun z => ⟨z,hrV (Metric.mem_ball.mpr
        (lt_of_le_of_lt (Metric.mem_closedBall.mp z.property) hεr))⟩
    have hqc : Continuous q := continuous_subtype_val.subtype_mk _
    have hqi : Function.Injective q := by
      intro z w he
      have he' : (z : ℝ × ℝ) = (w : ℝ × ℝ) := congrArg (fun v : V => (v : ℝ × ℝ)) he
      exact Subtype.ext he'
    have hq : IsEmbedding q := (hqc.isClosedEmbedding hqi).isEmbedding
    let square : Metric.closedBall ((0,0) : ℝ × ℝ) ε → S :=
      fun z => (h.symm (q z) : U).val
    have hsquare : IsEmbedding square :=
      IsEmbedding.subtypeVal.comp (h.symm.isEmbedding.comp hq)
    have hflat (z : Metric.closedBall ((0,0) : ℝ × ℝ) ε) :
        square z ∈ b.image ↔ (z : ℝ × ℝ).1 = 0 := by
      have ha := haxis (h.symm (q z)).val (h.symm (q z)).property
      change (h.symm (q z)).val ∈ b.image ↔ ((h (h.symm (q z)) : V) : ℝ × ℝ).1 = 0 at ha
      rw [h.apply_symm_apply] at ha
      exact ha
    refine ⟨ε,hε,square,hsquare,hflat,?_⟩
    let z : Metric.closedBall ((0,0) : ℝ × ℝ) ε := ⟨(0,0),by simp [Metric.mem_closedBall,hε.le]⟩
    have hcenter : q z = h ⟨b.map 1,hp⟩ := by
      apply Subtype.ext
      exact hp0.symm
    change (h.symm (q z) : U).val = b.map 1
    rw [hcenter,h.symm_apply_apply]
  have angularSquare (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
      (b : CurveComplex.Curve S) :
      ∃ ε : ℝ, ∃ hε : 0 < ε,
      ∃ square : Metric.closedBall ((0,0) : ℝ × ℝ) ε → S,
        IsEmbedding square ∧
        (∀ z, square z ∈ b.image ↔ (z : ℝ × ℝ).1 = 0) ∧
      ∃ F : OpenPartialHomeomorph S (ℝ × ℝ),
        (∀ z, square z ∈ F.source ∧ F (square z) = (z:ℝ × ℝ)) ∧
        (∀ x, x ∈ F.source → (x ∈ b.image ↔ (F x).1 = 0)) ∧
      ∃ g : C(Interval,Circle), IsEmbedding g ∧
        (∀ u, 0 < ((g u : Circle) : ℂ).re) ∧
      ∃ a : C(Interval,ℝ), Function.Injective a ∧
        (∀ u, Circle.exp (a u) = g u) ∧
        ∀ u, b.map (g u) = square ⟨(0,ε*(2*(u:ℝ)-1)),by
          rw [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
          simp only [Prod.fst_zero,Prod.snd_zero,sub_zero,abs_zero]
          apply max_le hε.le
          apply abs_le.mpr
          constructor <;> nlinarith [u.property.1,u.property.2]⟩ := by
    classical
    obtain ⟨U,V,hp,h,hU,hV,hp0,haxis⟩ :=
      embedded_curve_has_local_axis_chart b (b.map 1) (Set.mem_range_self 1)
    let C : Set S := b.map '' {w : Circle | (w:ℂ).re ≤ 0}
    have hC : IsClosed C := ((isClosed_le (by fun_prop) continuous_const).isCompact.image
      b.embedded.continuous).isClosed
    have hpC : b.map 1 ∉ C := by
      rintro ⟨w,hw,he⟩
      have hw1 := b.embedded.injective he
      subst w
      norm_num at hw
    let D : Set U := Subtype.val ⁻¹' Cᶜ
    have hD : IsOpen D := hC.isOpen_compl.preimage continuous_subtype_val
    let W : Set (ℝ × ℝ) := Subtype.val '' (h '' D)
    have hW : IsOpen W := hV.isOpenEmbedding_subtypeVal.isOpenMap _ (h.isOpenMap _ hD)
    have hzero : ((0,0):ℝ × ℝ) ∈ W := by
      refine ⟨h ⟨b.map 1,hp⟩,⟨⟨b.map 1,hp⟩,hpC,rfl⟩,hp0⟩
    obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hW (0,0) hzero
    let ε : ℝ := r/2
    have hε : 0 < ε := half_pos hr
    have hsmall (z : Metric.closedBall ((0,0):ℝ × ℝ) ε) : (z:ℝ × ℝ) ∈ W :=
      hrW (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp z.property)
        (half_lt_self hr)))
    have hWV : W ⊆ V := by rintro z ⟨v,hv,rfl⟩; exact v.property
    let q : Metric.closedBall ((0,0):ℝ × ℝ) ε → V := fun z => ⟨z,hWV (hsmall z)⟩
    have hqc : Continuous q := continuous_subtype_val.subtype_mk _
    have hqi : Function.Injective q := by
      intro z w he
      exact Subtype.ext (congrArg (fun v : V => (v:ℝ × ℝ)) he)
    have hq : IsEmbedding q := (hqc.isClosedEmbedding hqi).isEmbedding
    let square : Metric.closedBall ((0,0):ℝ × ℝ) ε → S :=
      fun z => (h.symm (q z) : U).val
    have hsquare : IsEmbedding square :=
      IsEmbedding.subtypeVal.comp (h.symm.isEmbedding.comp hq)
    have hflat (z : Metric.closedBall ((0,0):ℝ × ℝ) ε) :
        square z ∈ b.image ↔ (z:ℝ × ℝ).1 = 0 := by
      have ha := haxis (h.symm (q z)).val (h.symm (q z)).property
      change (h.symm (q z)).val ∈ b.image ↔ ((h (h.symm (q z)) : V):ℝ × ℝ).1 = 0 at ha
      rw [h.apply_symm_apply] at ha
      exact ha
    have havoid (z : Metric.closedBall ((0,0):ℝ × ℝ) ε) : square z ∉ C := by
      obtain ⟨v,⟨x,hx,hxv⟩,hvz⟩ := hsmall z
      have hqz : q z = v := Subtype.ext hvz.symm
      change (h.symm (q z) : U).val ∉ C
      rw [hqz,← hxv,h.symm_apply_apply]
      exact hx
    letI : Nonempty U := ⟨⟨b.map 1,hp⟩⟩
    letI : Nonempty V := ⟨h ⟨b.map 1,hp⟩⟩
    let A := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → S)
    let B := hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : V → ℝ × ℝ)
    let F := (A.symm.trans h.toOpenPartialHomeomorph).trans B
    have hA : A.source = univ := by simp [A]
    have hAt : A.target = U := by simp [A,Subtype.range_val]
    have hB : B.source = univ := by simp [B]
    have hsource : F.source = U := by
      simp [F,OpenPartialHomeomorph.trans_source,hA,hAt,hB]
    have hF (x : U) : F x = (h x : ℝ × ℝ) := by
      change B (h (A.symm x)) = (h x : ℝ × ℝ)
      rw [show A.symm (x:S) = x from hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv _]
      rfl
    have hFsquare (z : Metric.closedBall ((0,0):ℝ × ℝ) ε) :
        square z ∈ F.source ∧ F (square z) = (z:ℝ × ℝ) := by
      refine ⟨hsource ▸ (h.symm (q z)).property,?_⟩
      change F (h.symm (q z)).val = (z:ℝ × ℝ)
      rw [hF,h.apply_symm_apply]
    have hFaxis (x:S) (hx:x∈F.source) : x ∈ b.image ↔ (F x).1 = 0 := by
      rw [hsource] at hx
      rw [hF ⟨x,hx⟩]
      exact haxis x hx
    let v : C(Interval,Metric.closedBall ((0,0):ℝ × ℝ) ε) := ⟨fun u =>
      ⟨(0,ε*(2*(u:ℝ)-1)),by
        rw [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
        simp only [Prod.fst_zero,Prod.snd_zero,sub_zero,abs_zero]
        apply max_le hε.le
        apply abs_le.mpr
        constructor <;> nlinarith [u.property.1,u.property.2]⟩,by fun_prop⟩
    have hvi : Function.Injective v := by
      intro u w he
      apply Subtype.ext
      have hh := congrArg (fun z : Metric.closedBall ((0,0):ℝ × ℝ) ε => (z:ℝ × ℝ).2) he
      change ε*(2*(u:ℝ)-1) = ε*(2*(w:ℝ)-1) at hh
      nlinarith
    let z : C(Interval,b.image) := ⟨fun u => ⟨square (v u),(hflat _).mpr rfl⟩,
      (hsquare.continuous.comp v.continuous).subtype_mk _⟩
    let g : C(Interval,Circle) := ⟨fun u => b.embedded.toHomeomorph.symm (z u),
      b.embedded.toHomeomorph.symm.continuous.comp z.continuous⟩
    have hcore (u : Interval) : b.map (g u) = square (v u) := by
      have hh := b.embedded.toHomeomorph.apply_symm_apply (z u)
      exact congrArg Subtype.val hh
    have hgi : Function.Injective g := by
      intro u w he
      apply hvi
      apply hsquare.injective
      rw [← hcore,← hcore,he]
    have hg : IsEmbedding g := (g.continuous.isClosedEmbedding hgi).isEmbedding
    have hpos (u : Interval) : 0 < (g u:ℂ).re := by
      by_contra hn
      have hh := havoid (v u)
      apply hh
      exact ⟨g u,le_of_not_gt hn,hcore u⟩
    let a : C(Interval,ℝ) := ⟨fun u => Complex.arg (g u),by
      apply continuous_iff_continuousAt.mpr
      intro u
      exact (Complex.continuousAt_arg (Or.inl (hpos u))).comp
        continuous_subtype_val.continuousAt |>.comp g.continuous.continuousAt⟩
    have hai : Function.Injective a := by
      intro u w he
      apply hgi
      exact Circle.injective_arg he
    exact ⟨ε,hε,square,hsquare,hflat,F,hFsquare,hFaxis,g,hg,hpos,a,hai,fun u => Circle.exp_arg _,hcore⟩
  have angularSpan (g : C(Interval,Circle)) (hg : IsEmbedding g)
      (hpos : ∀ u, 0 < (g u : ℂ).re) :
      ∃ α β : ℝ, α < β ∧ β < α + 2*Real.pi ∧
        Set.range g = Circle.exp '' Set.Icc α β ∧
        ((g 0 = Circle.exp α ∧ g 1 = Circle.exp β) ∨
         (g 0 = Circle.exp β ∧ g 1 = Circle.exp α)) := by
    let a : C(Interval,ℝ) := ⟨fun u => Complex.arg (g u),by
      apply continuous_iff_continuousAt.mpr
      intro u
      exact (Complex.continuousAt_arg (Or.inl (hpos u))).comp
        continuous_subtype_val.continuousAt |>.comp g.continuous.continuousAt⟩
    have hai : Function.Injective a := by
      intro u w he
      exact hg.injective (Circle.injective_arg he)
    have hI : Set.Icc (0 : Interval) 1 = Set.univ := by
      ext u
      simp only [Set.mem_Icc,Set.mem_univ,iff_true]
      exact ⟨u.property.1,u.property.2⟩
    have hexp (u : Interval) : Circle.exp (a u) = g u := Circle.exp_arg _
    have hrange : Set.range g = Circle.exp '' Set.range a := by
      ext z
      constructor
      · rintro ⟨u,rfl⟩
        exact ⟨a u,Set.mem_range_self _,hexp u⟩
      · rintro ⟨t,⟨u,rfl⟩,rfl⟩
        exact ⟨u,(hexp u).symm⟩
    have hlo (u : Interval) : -Real.pi < a u := Complex.neg_pi_lt_arg _
    have hhi (u : Interval) : a u < Real.pi :=
      (Complex.arg_le_pi _).lt_of_ne (Complex.slitPlane_arg_ne_pi (Or.inl (hpos u)))
    rcases a.continuous.strictMono_of_inj_boundedOrder' hai with hm|hm
    · have hab : a 0 < a 1 := hm (by norm_num)
      have hspan : Set.range a = Set.Icc (a 0) (a 1) := by
        have hh := a.continuous.continuousOn.image_Icc_of_monotoneOn
          (by norm_num : (0:Interval) ≤ 1) (hm.monotone.monotoneOn _)
        simpa only [hI,Set.image_univ] using hh
      refine ⟨a 0,a 1,hab,?_,hrange.trans (congrArg (fun A => Circle.exp '' A) hspan),
        Or.inl ⟨(hexp 0).symm,(hexp 1).symm⟩⟩
      linarith [hlo 0,hhi 1]
    · have hab : a 1 < a 0 := hm (by norm_num)
      have hspan : Set.range a = Set.Icc (a 1) (a 0) := by
        have hh := a.continuous.continuousOn.image_Icc_of_antitoneOn
          (by norm_num : (0:Interval) ≤ 1) (hm.antitone.antitoneOn _)
        simpa only [hI,Set.image_univ] using hh
      refine ⟨a 1,a 0,hab,?_,hrange.trans (congrArg (fun A => Circle.exp '' A) hspan),
        Or.inr ⟨(hexp 0).symm,(hexp 1).symm⟩⟩
      linarith [hlo 1,hhi 0]
  have complementaryArc (S : Type) [TopologicalSpace S] [T2Space S] (b : CurveComplex.Curve S)
      (α β : ℝ) (hab : α < β) (hspan : β < α+2*Real.pi) :
      ∃ f : C(unitInterval,S), IsEmbedding f ∧
        f 0 = b.map (Circle.exp β) ∧ f 1 = b.map (Circle.exp α) ∧
        Set.range f = b.image \ b.map '' (Circle.exp '' Set.Ioo α β) := by
    let T : ℝ := 2*Real.pi
    have hT : 0 < T := by dsimp [T]; positivity
    letI : Fact (0 < T) := ⟨hT⟩
    let angle : unitInterval → ℝ := fun u => β+(α+T-β)*(u:ℝ)
    have hangle : Continuous angle := by dsimp [angle]; fun_prop
    have hpos : 0 < α+T-β := by dsimp [T]; linarith
    have hmem (u : unitInterval) : angle u ∈ Set.Icc β (α+T) := by
      dsimp [angle]
      constructor <;> nlinarith [u.property.1,u.property.2]
    let f : C(unitInterval,S) := ⟨fun u => b.map (Circle.exp (angle u)),
      b.embedded.continuous.comp (Circle.exp.continuous.comp hangle)⟩
    have hfi : Function.Injective f := by
      intro u v he
      have he' := Circle.exp_injOn_Icc (a := β) (b := α+T)
        (by dsimp [T]; linarith) (hmem u) (hmem v) (b.embedded.injective he)
      apply Subtype.ext
      dsimp [angle] at he'
      exact mul_left_cancel₀ hpos.ne' (by linarith)
    have hfrange : Set.range f = b.map '' (Circle.exp '' Set.Icc β (α+T)) := by
      apply Set.Subset.antisymm
      · rintro x ⟨u,rfl⟩
        exact ⟨Circle.exp (angle u),⟨angle u,hmem u,rfl⟩,rfl⟩
      · rintro x ⟨z,⟨t,ht,rfl⟩,rfl⟩
        let u : unitInterval := ⟨(t-β)/(α+T-β),by
          constructor
          · exact div_nonneg (sub_nonneg.mpr ht.1) hpos.le
          · apply (div_le_one hpos).mpr
            linarith [ht.2]⟩
        refine ⟨u,?_⟩
        have ha : angle u = t := by
          dsimp [angle,u]
          field_simp
          <;> ring
        change b.map (Circle.exp (angle u)) = b.map (Circle.exp t)
        rw [ha]
    have hrepresent (z : Circle) : ∃ t ∈ Set.Ico α (α+T), Circle.exp t = z := by
      let a := AddCircle.equivIco T α (AddCircle.homeomorphCircle'.symm z)
      refine ⟨a,a.property,?_⟩
      have ha : (a : AddCircle T) = AddCircle.homeomorphCircle'.symm z := AddCircle.coe_equivIco
      have he := congrArg AddCircle.homeomorphCircle' ha
      rw [AddCircle.homeomorphCircle'.apply_symm_apply] at he
      change Circle.exp (a : ℝ) = z at he
      exact he
    have hset : b.map '' (Circle.exp '' Set.Icc β (α+T)) =
        b.image \ b.map '' (Circle.exp '' Set.Ioo α β) := by
      apply Set.Subset.antisymm
      · rintro x ⟨z,⟨t,ht,rfl⟩,rfl⟩
        refine ⟨Set.mem_range_self _,?_⟩
        rintro ⟨z,⟨u,hu,rfl⟩,he⟩
        have hexp := b.embedded.injective he
        by_cases htend : t = α+T
        · rw [htend] at hexp
          have hperiod : Circle.exp (α+T) = Circle.exp α := Circle.periodic_exp α
          have heu : u = α := Circle.exp_injOn_Ico (a := α) (b := α+T)
            (by dsimp [T]; linarith) ⟨hu.1.le,by linarith [hu.2]⟩ ⟨le_rfl,by linarith⟩
            (hexp.trans hperiod)
          exact (ne_of_gt hu.1) heu
        · have htt : t < α+T := lt_of_le_of_ne ht.2 htend
          have heu : u = t := Circle.exp_injOn_Ico (a := α) (b := α+T)
            (by dsimp [T]; linarith) ⟨hu.1.le,by linarith [hu.2]⟩
            ⟨by linarith [ht.1],htt⟩ hexp
          linarith [hu.2,ht.1]
      · rintro x ⟨⟨z,rfl⟩,hx⟩
        obtain ⟨t,ht,he⟩ := hrepresent z
        by_cases htβ : β ≤ t
        · exact ⟨z,⟨t,⟨htβ,ht.2.le⟩,he⟩,rfl⟩
        · have hta : t = α := by
            by_contra h
            have hlt : α < t := lt_of_le_of_ne ht.1 (Ne.symm h)
            exact hx ⟨z,⟨t,⟨hlt,lt_of_not_ge htβ⟩,he⟩,rfl⟩
          refine ⟨z,⟨α+T,⟨hspan.le,le_rfl⟩,?_⟩,rfl⟩
          exact (Circle.periodic_exp α).trans (hta ▸ he)
    refine ⟨f,(f.continuous.isClosedEmbedding hfi).isEmbedding,?_,?_,hfrange.trans hset⟩
    · simp [f,angle]
    · simpa [f,angle,T] using congrArg b.map (Circle.periodic_exp α)
  have diameterCover (S : Type) [TopologicalSpace S] (b : CurveComplex.Curve S)
      (ε : ℝ) (hε : 0 < ε)
      (square : Metric.closedBall ((0,0):ℝ × ℝ) ε → S)
      (g : C(Interval,Circle))
      (hcore : ∀ u, b.map (g u) = square ⟨(0,ε*(2*(u:ℝ)-1)),by
        rw [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
        simp only [Prod.fst_zero,Prod.snd_zero,sub_zero,abs_zero]
        apply max_le hε.le
        apply abs_le.mpr
        constructor <;> nlinarith [u.property.1,u.property.2]⟩) :
      square '' {z | (z:ℝ × ℝ).1=0} = b.map '' Set.range g := by
    let v (u:Interval) : Metric.closedBall ((0,0):ℝ × ℝ) ε :=
      ⟨(0,ε*(2*(u:ℝ)-1)),by
        rw [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
        simp only [Prod.fst_zero,Prod.snd_zero,sub_zero,abs_zero]
        apply max_le hε.le
        apply abs_le.mpr
        constructor <;> nlinarith [u.property.1,u.property.2]⟩
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hymax : max |(z:ℝ × ℝ).1| |(z:ℝ × ℝ).2| ≤ ε := by
        simpa only [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,
          Prod.fst_zero,Prod.snd_zero,sub_zero] using z.property
      have hy := abs_le.mp ((le_max_right _ _).trans hymax)
      have hydiv : -1 ≤ (z:ℝ × ℝ).2/ε ∧ (z:ℝ × ℝ).2/ε ≤ 1 := by
        constructor
        · apply (le_div_iff₀ hε).mpr
          linarith [hy.1]
        · apply (div_le_iff₀ hε).mpr
          linarith [hy.2]
      let t : Interval := ⟨((z:ℝ × ℝ).2/ε+1)/2,by constructor <;> linarith [hydiv.1,hydiv.2]⟩
      have hv : v t = z := by
        apply Subtype.ext
        apply Prod.ext
        · exact hz.symm
        · change ε*(2*(((z:ℝ × ℝ).2/ε+1)/2)-1) = (z:ℝ × ℝ).2
          field_simp
          <;> ring
      refine ⟨g t,Set.mem_range_self t,?_⟩
      exact (hcore t).trans (congrArg square hv)
    · rintro ⟨w,⟨u,rfl⟩,he⟩
      exact ⟨v u,rfl,(hcore u).symm.trans he⟩
  have complementMeet (S : Type) [TopologicalSpace S] (b : CurveComplex.Curve S)
      (ε : ℝ) (square : Metric.closedBall ((0,0):ℝ × ℝ) ε → S)
      (hflat : ∀ z, square z ∈ b.image ↔ (z:ℝ × ℝ).1=0)
      (α β : ℝ)
      (hdiameter : square '' {z | (z:ℝ × ℝ).1=0} =
        b.map '' (Circle.exp '' Set.Icc α β))
      (f : C(Interval,S)) (hf : IsEmbedding f)
      (hf0 : f 0 = b.map (Circle.exp β)) (hf1 : f 1 = b.map (Circle.exp α))
      (hfimage : Set.range f = b.image \ b.map '' (Circle.exp '' Set.Ioo α β)) :
      ∀ u, f u ∈ Set.range square → u = 0 ∨ u = 1 := by
    intro u hu
    have hfub : f u ∈ b.image \ b.map '' (Circle.exp '' Set.Ioo α β) :=
      hfimage ▸ Set.mem_range_self u
    obtain ⟨z,hz⟩ := hu
    have hzaxis : (z:ℝ × ℝ).1=0 := (hflat z).mp (hz ▸ hfub.1)
    have hd : f u ∈ b.map '' (Circle.exp '' Set.Icc α β) :=
      hdiameter ▸ ⟨z,hzaxis,hz⟩
    obtain ⟨w,⟨t,ht,rfl⟩,he⟩ := hd
    have htopen : t ∉ Set.Ioo α β := by
      intro hto
      exact hfub.2 ⟨Circle.exp t,⟨t,hto,rfl⟩,he⟩
    have hends : t = α ∨ t = β := by
      by_cases ha : t=α
      · exact Or.inl ha
      · right
        by_contra hb
        apply htopen
        exact ⟨lt_of_le_of_ne ht.1 (Ne.symm ha),lt_of_le_of_ne ht.2 hb⟩
    rcases hends with rfl|rfl
    · right
      apply hf.injective
      exact he.symm.trans hf1.symm
    · left
      apply hf.injective
      exact he.symm.trans hf0.symm
  have sharedFrame (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
      (f : C(Interval,S)) (hf : IsEmbedding f)
      (F : OpenPartialHomeomorph S (ℝ × ℝ)) (ε : ℝ)
      (hp₀ : f 0 ∈ F.source) (hp₁ : f 1 ∈ F.source)
      (h₀ : F (f 0) = (0,ε)) (h₁ : F (f 1) = (0,-ε))
      (haxis : ∀ u, f u ∈ F.source → (F (f u)).1 = 0) :
      ∃ N : Interval × Set.Icc (-1:ℝ) 1 → S,
        IsEmbedding N ∧ (∀ u, N (u,⟨0,by norm_num⟩) = f u) ∧
        ∃ sgn δ η : Fin 2 → ℝ,
          (∀ k, sgn k = -1 ∨ sgn k = 1) ∧
          (∀ k, 0 < δ k ∧ 0 < η k) ∧
          ∀ k (u : Interval) (w : Set.Icc (-1:ℝ) 1),
            |(u:ℝ)-(if k = 0 then 0 else 1)| < η k →
            N (u,w) ∈ F.source ∧
            F (N (u,w)) = (sgn k*δ k*(w:ℝ),(F (f u)).2) := by
    let shift (c:ℝ) : (ℝ × ℝ) ≃ₜ Plane := {
      toFun := fun z => Plane.mk (z.2-c) z.1
      invFun := fun z => (z 1,z 0+c)
      left_inv := by intro z; simp [Plane.mk]
      right_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop
    }
    let c : Fin 2 → ℝ := fun k => if k = 0 then ε else -ε
    let E : Fin 2 → OpenPartialHomeomorph S Plane := fun k => F.transHomeomorph (shift (c k))
    have hEs (k:Fin 2) : (E k).source = F.source := by
      simp [E,OpenPartialHomeomorph.transHomeomorph_source]
    have hEF (k:Fin 2) (x:S) : E k x = Plane.mk ((F x).2-c k) (F x).1 := rfl
    let θ : Fin 2 → Interval := fun k => if k = 0 then 0 else 1
    have hθ : Function.Injective θ := by
      intro k l he
      fin_cases k <;> fin_cases l <;> simp_all [θ]
    have hpE (k:Fin 2) : f (θ k) ∈ (E k).source := by
      rw [hEs]
      by_cases hk:k=0
      · simpa [θ,hk] using hp₀
      · simpa [θ,hk] using hp₁
    have hE0 (k:Fin 2) : E k (f (θ k)) = 0 := by
      rw [hEF]
      by_cases hk:k=0
      · simp only [θ,c,if_pos hk,h₀]
        ext i
        fin_cases i <;> simp [Plane.mk]
      · simp only [θ,c,if_neg hk,h₁]
        ext i
        fin_cases i <;> simp [Plane.mk]
    have hEa (k:Fin 2) (u:Interval) (hu:f u ∈ (E k).source) : E k (f u) 1 = 0 := by
      rw [hEF]
      simpa [Plane.mk] using haxis u (hEs k ▸ hu)
    obtain ⟨N,hN,hNU,hcenter,sgn,δ,η,hsign,hpos,hcoords⟩ :=
      source_finite_axis_framed_arc_strip S f hf (Fin 2) θ hθ E hpE hE0 hEa
        Set.univ isOpen_univ (by simp)
    refine ⟨N,hN,hcenter,sgn,δ,η,hsign,hpos,?_⟩
    intro k u w hu
    have huθ : |(u:ℝ)-(θ k:ℝ)| < η k := by
      by_cases hk:k=0 <;> simpa [θ,hk] using hu
    obtain ⟨hNs,hNc⟩ := hcoords k u w huθ
    refine ⟨hEs k ▸ hNs,?_⟩
    rw [hEF,hEF] at hNc
    have hx := congrArg (fun z:Plane => z 1) hNc
    have hy := congrArg (fun z:Plane => z 0) hNc
    simp only [Plane.mk] at hx hy
    apply Prod.ext
    · exact hx
    · change (F (N (u,w))).2-c k = (F (f u)).2-c k at hy
      linarith only [hy]
  have avoidFramed (S : Type) [TopologicalSpace S] [T2Space S]
      (ε : ℝ) (hε : 0<ε)
      (square : Metric.closedBall ((0,0):ℝ × ℝ) ε → S) (hsquare : IsEmbedding square)
      (F : OpenPartialHomeomorph S (ℝ × ℝ))
      (hFsquare : ∀ z, square z ∈ F.source ∧ F (square z) = (z:ℝ × ℝ))
      (f : C(I,S)) (N : I × BandWidth → S) (hN : Continuous N)
      (hcenter : ∀ u, N (u,⟨0,by norm_num⟩)=f u)
      (haxis : ∀ u, f u ∈ F.source → (F (f u)).1=0)
      (hfmeet : ∀ u, f u ∈ Set.range square → u=0 ∨ u=1)
      (sgn δ η : Fin 2 → ℝ) (hη : ∀ k, 0<η k)
      (hcoords : ∀ k (u:I) (w:BandWidth),
        |(u:ℝ)-(if k=0 then 0 else 1)|<η k →
        N (u,w) ∈ F.source ∧ F (N (u,w))=(sgn k*δ k*(w:ℝ),(F (f u)).2)) :
      ∃ ρ : ℝ, ∃ hρ : 0<ρ ∧ ρ≤1,
        ∀ (u:I) (w:BandWidth),
          N (u,⟨ρ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩)
            ∈ Set.range square → u=0 ∨ u=1 := by
    have near (k:Fin 2) (u:I) (w:BandWidth)
        (hu:|(u:ℝ)-(if k=0 then 0 else 1)|<η k)
        (hw:N (u,w)∈Set.range square) : u=0 ∨ u=1 := by
      obtain ⟨hNs,hNc⟩ := hcoords k u w hu
      have hfs : f u ∈ F.source := by
        have hh := (hcoords k u ⟨0,by norm_num⟩ hu).1
        rwa [hcenter] at hh
      obtain ⟨z,hz⟩ := hw
      have hFy : (F (f u)).2=(z:ℝ × ℝ).2 := by
        have hh := congrArg Prod.snd hNc
        rw [← hz,(hFsquare z).2] at hh
        exact hh.symm
      have hzmax : max |(z:ℝ × ℝ).1| |(z:ℝ × ℝ).2|≤ε := by
        simpa only [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,
          Prod.fst_zero,Prod.snd_zero,sub_zero] using z.property
      let v : Metric.closedBall ((0,0):ℝ × ℝ) ε := ⟨(0,(F (f u)).2),by
        rw [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
        simp only [Prod.fst_zero,Prod.snd_zero,sub_zero,abs_zero,hFy]
        exact max_le hε.le ((le_max_right _ _).trans hzmax)⟩
      apply hfmeet u
      refine ⟨v,?_⟩
      apply F.injOn (hFsquare v).1 hfs
      rw [(hFsquare v).2]
      apply Prod.ext
      · exact (haxis u hfs).symm
      · rfl
    let a : I := ⟨min (η 0/2) (1/4),by
      constructor
      · exact (lt_min (half_pos (hη 0)) (by norm_num)).le
      · exact (min_le_right _ _).trans (by norm_num)⟩
    let b : I := ⟨1-min (η 1/2) (1/4),by
      constructor
      · linarith [min_le_right (η 1/2) (1/4)]
      · have hh : 0 ≤ min (η 1/2) (1/4) := (lt_min (half_pos (hη 1)) (by norm_num)).le
        linarith⟩
    have ha : 0<(a:ℝ) := lt_min (half_pos (hη 0)) (by norm_num)
    have hb : (b:ℝ)<1 := by
      dsimp [b]
      linarith [lt_min (half_pos (hη 1)) (by norm_num : (0:ℝ)<1/4)]
    have hab : a≤b := by
      change min (η 0/2) (1/4) ≤ 1-min (η 1/2) (1/4)
      linarith [min_le_right (η 0/2) (1/4),min_le_right (η 1/2) (1/4)]
    let clip : C(I,I) := ⟨fun u =>
      ⟨min (max (u:ℝ) (a:ℝ)) (b:ℝ),
        le_min (u.property.1.trans (le_max_left _ _)) b.property.1,
        (min_le_right _ _).trans b.property.2⟩,by fun_prop⟩
    have hclipa (u:I) : a≤clip u := le_min (le_max_right _ _) hab
    have hclipb (u:I) : clip u≤b := by
      change min (max (u:ℝ) (a:ℝ)) (b:ℝ) ≤ (b:ℝ)
      exact min_le_right _ _
    let T : I × BandWidth → S := fun z => N (clip z.1,z.2)
    have hT : Continuous T := hN.comp ((clip.continuous.comp continuous_fst).prodMk continuous_snd)
    let U : Set S := (Set.range square)ᶜ
    have hU : IsOpen U := (isCompact_range hsquare.continuous).isClosed.isOpen_compl
    have hc (u:I) : T (u,⟨0,by norm_num⟩) ∈ U := by
      change N (clip u,⟨0,by norm_num⟩) ∉ Set.range square
      rw [hcenter]
      intro hh
      rcases hfmeet (clip u) hh with he|he
      · have hh := hclipa u
        rw [he] at hh
        exact (not_le_of_gt ha) hh
      · have hh := hclipb u
        rw [he] at hh
        exact (not_le_of_gt hb) hh
    obtain ⟨ρ,hρ,hwidth⟩ := source_continuous_strip_uniform_width T hT U hU hc
    refine ⟨ρ,hρ,?_⟩
    intro u w hu
    by_cases hleft : u≤a
    · apply near 0 u _ _ hu
      norm_num only [show (0:Fin 2)=0 from rfl,if_true]
      rw [sub_zero,abs_of_nonneg u.property.1]
      exact (show (u:ℝ)≤(a:ℝ) from hleft).trans_lt
        ((min_le_left _ _).trans_lt (half_lt_self (hη 0)))
    · by_cases hright : b≤u
      · apply near 1 u _ _ hu
        norm_num only [show (1:Fin 2)≠0 by decide,if_false]
        rw [abs_of_nonpos (by linarith [u.property.2] : (u:ℝ)-1≤0)]
        change -((u:ℝ)-1)<η 1
        have hh : min (η 1/2) (1/4)≤η 1/2 := min_le_left _ _
        change 1-min (η 1/2) (1/4)≤(u:ℝ) at hright
        linarith [hη 1]
      · have hclipu : clip u=u := by
          apply Subtype.ext
          change min (max (u:ℝ) (a:ℝ)) (b:ℝ)=(u:ℝ)
          rw [max_eq_left (show (a:ℝ)≤(u:ℝ) from le_of_not_ge hleft),
            min_eq_left (show (u:ℝ)≤(b:ℝ) from le_of_not_ge hright)]
        have hh := hwidth u w
        change N (clip u,_)∉Set.range square at hh
        rw [hclipu] at hh
        exact (hh hu).elim
  have signedAssembly (S : Type) [TopologicalSpace S] [T2Space S]
      (ε : ℝ) (hε : 0 < ε)
      (square : Metric.closedBall ((0,0):ℝ × ℝ) ε → S) (hsquare : IsEmbedding square)
      (F : OpenPartialHomeomorph S (ℝ × ℝ))
      (hFsquare : ∀ z, square z ∈ F.source ∧ F (square z) = (z:ℝ × ℝ))
      (N : I × BandWidth → S) (hN : IsEmbedding N)
      (s₀ s₁ d₀ d₁ : ℝ) (hs₀ : s₀=-1 ∨ s₀=1) (hs₁ : s₁=-1 ∨ s₁=1)
      (hd₀ : 0<d₀) (hd₁ : 0<d₁)
      (hend₀ : ∀ w, N (0,w) ∈ F.source ∧ F (N (0,w)) = (s₀*d₀*(w:ℝ),ε))
      (hend₁ : ∀ w, N (1,w) ∈ F.source ∧ F (N (1,w)) = (s₁*d₁*(w:ℝ),-ε))
      (ρ : ℝ) (hρ : 0<ρ ∧ ρ≤1)
      (hmeet : ∀ (u:I) (w:BandWidth),
        N (u,⟨ρ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩)
          ∈ Set.range square → u=0 ∨ u=1) :
      ∃ square' : Metric.closedBall ((0,0):ℝ × ℝ) ε → S,
        IsEmbedding square' ∧
        square' '' {z | (z:ℝ × ℝ).1=0} = square '' {z | (z:ℝ × ℝ).1=0} ∧
      ∃ flip : Bool, ∃ band : I × BandWidth → S,
        IsEmbedding band ∧
        (∀ u, band (u,⟨0,by norm_num⟩) = N (u,⟨0,by norm_num⟩)) ∧
        (∀ w, band (0,w) = square' (squarePort ε hε 2 w)) ∧
        (∀ w, band (1,w) = square' (squarePort ε hε 0 (flipBandWidth flip w))) ∧
        (Set.range band ∩ Set.range square' =
          Set.range (fun w => square' (squarePort ε hε 2 w)) ∪
          Set.range (fun w => square' (squarePort ε hε 0 w))) := by
    classical
    let r : ℝ := min (ε/4) (ρ*min d₀ d₁)
    have hr : 0<r := lt_min (by positivity) (mul_pos hρ.1 (lt_min hd₀ hd₁))
    have hrε : r ≤ ε/4 := min_le_left _ _
    have hrρ : r ≤ ρ*min d₀ d₁ := min_le_right _ _
    let d : C(I,ℝ) := ⟨fun u => (1-(u:ℝ))*d₀+(u:ℝ)*d₁,by fun_prop⟩
    have hmin (u:I) : min d₀ d₁ ≤ d u := by
      have h0 := min_le_left d₀ d₁
      have h1 := min_le_right d₀ d₁
      dsimp [d]
      nlinarith [u.property.1,u.property.2]
    have hd (u:I) : 0<d u := (lt_min hd₀ hd₁).trans_le (hmin u)
    let lam : C(I,ℝ) := ⟨fun u => r/d u,continuous_const.div d.continuous (fun u => (hd u).ne')⟩
    have hlam (u:I) : 0<lam u ∧ lam u≤ρ := by
      refine ⟨div_pos hr (hd u),?_⟩
      exact (div_le_iff₀ (hd u)).mpr (hrρ.trans (mul_le_mul_of_nonneg_left (hmin u) hρ.1.le))
    have hlam₀ : d₀*lam 0=r := by change d₀*(r/((1-(0:I):ℝ)*d₀+(0:I)*d₁))=r; norm_num; field_simp
    have hlam₁ : d₁*lam 1=r := by change d₁*(r/((1-(1:I):ℝ)*d₀+(1:I)*d₁))=r; norm_num; field_simp
    have hs₀abs : |s₀|=1 := by rcases hs₀ with h|h <;> rw [h] <;> norm_num
    have hs₀sq : s₀*s₀=1 := by rcases hs₀ with h|h <;> rw [h] <;> norm_num
    have hs₀ne : s₀≠0 := by intro he; rw [he] at hs₀abs; norm_num at hs₀abs
    let flip : Bool := decide (s₀≠s₁)
    have hflip (w:BandWidth) : (flipBandWidth flip w:ℝ)=s₀*s₁*(w:ℝ) := by
      rcases hs₀ with h0|h0 <;> rcases hs₁ with h1|h1 <;>
        norm_num [flip,flipBandWidth,h0,h1]
    let width (u:I) (w:BandWidth) : BandWidth :=
      ⟨s₀*lam u*(w:ℝ),by
        have hw : |s₀*lam u*(w:ℝ)|≤1 := by
          rw [abs_mul,abs_mul,hs₀abs,abs_of_pos (hlam u).1,one_mul]
          nlinarith [abs_le.mpr w.property,(hlam u).2,hρ.2,(hlam u).1]
        exact abs_le.mp hw⟩
    let shrink : I × BandWidth → I × BandWidth := fun z => (z.1,width z.1 z.2)
    have hsc : Continuous shrink := by dsimp [shrink,width]; fun_prop
    have hsi : Function.Injective shrink := by
      intro z w he
      have hfirst := congrArg Prod.fst he
      change z.1=w.1 at hfirst
      apply Prod.ext hfirst
      apply Subtype.ext
      have hh := congrArg (fun z:I × BandWidth => (z.2:ℝ)) he
      change s₀*lam z.1*(z.2:ℝ)=s₀*lam w.1*(w.2:ℝ) at hh
      rw [← hfirst] at hh
      exact mul_left_cancel₀ (mul_ne_zero hs₀ne (hlam z.1).1.ne') hh
    have hse : IsEmbedding shrink := (hsc.isClosedEmbedding hsi).isEmbedding
    let band := N ∘ shrink
    have hband : IsEmbedding band := hN.comp hse
    have hcenter (u:I) : band (u,⟨0,by norm_num⟩)=N (u,⟨0,by norm_num⟩) := by
      change N (u,⟨s₀*lam u*0,_⟩)=_
      simp
    let k : ℝ := 4*r/ε
    have hk : 0<k := by dsimp [k]; positivity
    have hk1 : k≤1 := by dsimp [k]; apply (div_le_iff₀ hε).mpr; nlinarith
    let q : Metric.closedBall ((0,0):ℝ × ℝ) ε → Metric.closedBall ((0,0):ℝ × ℝ) ε :=
      fun z => ⟨(k*(z:ℝ × ℝ).1,-(z:ℝ × ℝ).2),by
        have hz : max |(z:ℝ × ℝ).1| |(z:ℝ × ℝ).2|≤ε := by
          simpa only [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,Prod.fst_zero,Prod.snd_zero,sub_zero] using z.property
        rw [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
        simp only [Prod.fst_zero,Prod.snd_zero,sub_zero,abs_mul,abs_of_pos hk,abs_neg]
        exact max_le (by nlinarith [(le_max_left _ _).trans hz,abs_nonneg (z:ℝ × ℝ).1])
          ((le_max_right _ _).trans hz)⟩
    have hqc : Continuous q := by dsimp [q]; fun_prop
    have hqi : Function.Injective q := by
      intro z w he
      apply Subtype.ext
      have hh := congrArg (fun z:Metric.closedBall ((0,0):ℝ × ℝ) ε => (z:ℝ × ℝ)) he
      apply Prod.ext
      · exact mul_left_cancel₀ hk.ne' (congrArg Prod.fst hh)
      · exact neg_injective (congrArg Prod.snd hh)
    let square' := square ∘ q
    have hsquare' : IsEmbedding square' := hsquare.comp ((hqc.isClosedEmbedding hqi).isEmbedding)
    have hq₂ (w:BandWidth) : (q (squarePort ε hε 2 w):ℝ × ℝ)=(r*(w:ℝ),ε) := by
      apply Prod.ext
      · change (4*r/ε)*(ε/4*(w:ℝ))=r*(w:ℝ)
        field_simp
        <;> ring
      · simp [q,squarePort,crossingEndRectangle]
    have hq₀ (w:BandWidth) : (q (squarePort ε hε 0 w):ℝ × ℝ)=(r*(w:ℝ),-ε) := by
      apply Prod.ext
      · change (4*r/ε)*(ε/4*(w:ℝ))=r*(w:ℝ)
        field_simp
        <;> ring
      · simp [q,squarePort,crossingEndRectangle]
    have hbottom (w:BandWidth) : band (0,w)=square' (squarePort ε hε 2 w) := by
      apply F.injOn (hend₀ (width 0 w)).1 (hFsquare _).1
      rw [(hend₀ (width 0 w)).2,(hFsquare _).2,hq₂]
      apply Prod.ext
      · change s₀*d₀*(s₀*lam 0*(w:ℝ))=r*(w:ℝ)
        calc
          _ = (s₀*s₀)*(d₀*lam 0)*(w:ℝ) := by ring
          _ = r*(w:ℝ) := by rw [hs₀sq,hlam₀]; ring
      · rfl
    have htop (w:BandWidth) : band (1,w)=square' (squarePort ε hε 0 (flipBandWidth flip w)) := by
      apply F.injOn (hend₁ (width 1 w)).1 (hFsquare _).1
      rw [(hend₁ (width 1 w)).2,(hFsquare _).2,hq₀,hflip]
      apply Prod.ext
      · change s₁*d₁*(s₀*lam 1*(w:ℝ))=r*(s₀*s₁*(w:ℝ))
        calc
          _ = s₀*s₁*(d₁*lam 1)*(w:ℝ) := by ring
          _ = r*(s₀*s₁*(w:ℝ)) := by rw [hlam₁]; ring
      · rfl
    have hmeet' (u:I) (w:BandWidth) (hu:band (u,w)∈Set.range square') : u=0 ∨ u=1 := by
      obtain ⟨z,hz⟩ := hu
      have hw : |s₀*lam u*(w:ℝ)/ρ|≤1 := by
        rw [abs_div,abs_mul,abs_mul,hs₀abs,abs_of_pos (hlam u).1,abs_of_pos hρ.1,one_mul]
        apply (div_le_iff₀ hρ.1).mpr
        nlinarith [abs_le.mpr w.property,(hlam u).1,(hlam u).2]
      let w' : BandWidth := ⟨s₀*lam u*(w:ℝ)/ρ,abs_le.mp hw⟩
      apply hmeet u w'
      have hww : (⟨ρ*(w':ℝ),by constructor <;> nlinarith [w'.property.1,w'.property.2,hρ.1,hρ.2]⟩:BandWidth)=width u w := by
        apply Subtype.ext
        dsimp [w',width]
        field_simp [hρ.1.ne']
      rw [hww]
      exact ⟨q z,hz⟩
    have hdiam : square' '' {z | (z:ℝ × ℝ).1=0} = square '' {z | (z:ℝ × ℝ).1=0} := by
      ext x
      constructor
      · rintro ⟨z,hz,rfl⟩
        refine ⟨q z,?_,rfl⟩
        change k*(z:ℝ × ℝ).1=0
        rw [hz,mul_zero]
      · rintro ⟨z,hz,rfl⟩
        let v : Metric.closedBall ((0,0):ℝ × ℝ) ε := ⟨(0,-(z:ℝ × ℝ).2),by
          have hzmax : max |(z:ℝ × ℝ).1| |(z:ℝ × ℝ).2|≤ε := by
            simpa only [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,Prod.fst_zero,Prod.snd_zero,sub_zero] using z.property
          rw [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
          simp only [Prod.fst_zero,Prod.snd_zero,sub_zero,abs_zero,abs_neg]
          exact max_le hε.le ((le_max_right _ _).trans hzmax)⟩
        refine ⟨v,rfl,?_⟩
        change square (q v)=square z
        apply congrArg square
        apply Subtype.ext
        apply Prod.ext
        · change k*0=(z:ℝ × ℝ).1
          rw [mul_zero]
          exact hz.symm
        · change -(-(z:ℝ × ℝ).2)=(z:ℝ × ℝ).2
          simp
    refine ⟨square',hsquare',hdiam,flip,band,hband,hcenter,hbottom,htop,?_⟩
    ext x
    constructor
    · rintro ⟨⟨⟨u,w⟩,rfl⟩,hx⟩
      rcases hmeet' u w hx with rfl|rfl
      · exact Or.inl ⟨w,(hbottom w).symm⟩
      · exact Or.inr ⟨flipBandWidth flip w,(htop w).symm⟩
    · rintro (⟨w,rfl⟩|⟨w,rfl⟩)
      · exact ⟨⟨(0,w),hbottom w⟩,Set.mem_range_self _⟩
      · have hinvol : flipBandWidth flip (flipBandWidth flip w)=w := by
          cases flip <;> simp [flipBandWidth]
        exact ⟨⟨(1,flipBandWidth flip w),by rw [htop,hinvol]⟩,Set.mem_range_self _⟩
  have regular : ∃ ε : ℝ, ∃ hε : 0 < ε,
      ∃ square : Metric.closedBall ((0,0) : ℝ × ℝ) ε → S,
        IsEmbedding square ∧ ∃ flip : Bool, ∃ band : unitInterval × BandWidth → S,
          IsEmbedding band ∧
          (∀ t, band (0,t) = square (squarePort ε hε 2 t)) ∧
          (∀ t, band (1,t) = square (squarePort ε hε 0 (flipBandWidth flip t))) ∧
          (Set.range band ∩ Set.range square =
            Set.range (fun t => square (squarePort ε hε 2 t)) ∪
            Set.range (fun t => square (squarePort ε hε 0 t))) ∧
          b.image = square '' {z | (z : ℝ × ℝ).1 = 0} ∪
            Set.range (fun u : unitInterval => band (u,⟨0,by norm_num⟩)) := by
    obtain ⟨ε,hε,square,hsquare,hflat,F,hFsquare,hFaxis,g,hg,hgpos,a,hai,haexp,hgcore⟩ := angularSquare S b
    obtain ⟨α,β,hab,hspan,hgimage,hgends⟩ := angularSpan g hg hgpos
    obtain ⟨fbase,hfbase,hfbase0,hfbase1,hfbaseimage⟩ := complementaryArc S b α β hab hspan
    have hdiameter : square '' {z | (z:ℝ × ℝ).1=0} = b.map '' (Circle.exp '' Set.Icc α β) := by
      rw [diameterCover S b ε hε square g hgcore,hgimage]
    have hfbasemeet := complementMeet S b ε square hflat α β hdiameter fbase hfbase hfbase0 hfbase1 hfbaseimage
    let zero : BandWidth := ⟨0,by norm_num⟩
    let top := square (squarePort ε hε 0 zero)
    let bottom := square (squarePort ε hε 2 zero)
    have hg0 : b.map (g 0)=bottom := by
      rw [hgcore]
      apply congrArg square
      apply Subtype.ext
      norm_num [bottom,zero,squarePort,crossingEndRectangle]
    have hg1 : b.map (g 1)=top := by
      rw [hgcore]
      apply congrArg square
      apply Subtype.ext
      norm_num [top,zero,squarePort,crossingEndRectangle]
    obtain ⟨f,hf,hf0,hf1,hfimage,hfmeet⟩ :
      ∃ f : C(I,S), IsEmbedding f ∧ f 0=top ∧ f 1=bottom ∧
        Set.range f=Set.range fbase ∧
        (∀ u, f u∈Set.range square → u=0 ∨ u=1) := by
      rcases hgends with ⟨hgα,hgβ⟩|⟨hgβ,hgα⟩
      · refine ⟨fbase,hfbase,?_,?_,rfl,hfbasemeet⟩
        · exact hfbase0.trans ((congrArg b.map hgβ.symm).trans hg1)
        · exact hfbase1.trans ((congrArg b.map hgα.symm).trans hg0)
      · let rev : C(I,I) := ⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩
        let f := fbase.comp rev
        have hrev0 : rev 0=1 := by apply Subtype.ext; norm_num [rev]
        have hrev1 : rev 1=0 := by apply Subtype.ext; norm_num [rev]
        refine ⟨f,hfbase.comp unitInterval.symmHomeomorph.isEmbedding,?_,?_,?_,?_⟩
        · change fbase (rev 0)=top
          rw [hrev0]
          exact hfbase1.trans ((congrArg b.map hgα.symm).trans hg1)
        · change fbase (rev 1)=bottom
          rw [hrev1]
          exact hfbase0.trans ((congrArg b.map hgβ.symm).trans hg0)
        · ext x
          constructor
          · rintro ⟨u,rfl⟩
            exact Set.mem_range_self (rev u)
          · rintro ⟨u,rfl⟩
            obtain ⟨v,hv⟩ := unitInterval.symmHomeomorph.surjective u
            exact ⟨v,congrArg fbase hv⟩
        · intro u hu
          rcases hfbasemeet (rev u) hu with he|he
          · right
            apply unitInterval.symmHomeomorph.injective
            exact he.trans hrev1.symm
          · left
            apply unitInterval.symmHomeomorph.injective
            exact he.trans hrev0.symm
    have hfb : Set.range f⊆b.image := by
      rw [hfimage,hfbaseimage]
      exact Set.sdiff_subset
    have hp0 : f 0∈F.source := hf0.symm ▸ (hFsquare _).1
    have hp1 : f 1∈F.source := hf1.symm ▸ (hFsquare _).1
    have hF0 : F (f 0)=(0,ε) := by
      rw [hf0,(hFsquare _).2]
      simp [top,zero,squarePort,crossingEndRectangle]
    have hF1 : F (f 1)=(0,-ε) := by
      rw [hf1,(hFsquare _).2]
      simp [bottom,zero,squarePort,crossingEndRectangle]
    have haxis : ∀ u, f u∈F.source → (F (f u)).1=0 :=
      fun u hu => (hFaxis _ hu).mp (hfb (Set.mem_range_self _))
    obtain ⟨N,hN,hcenter,sgn,δ,η,hsign,hpos,hcoords⟩ := sharedFrame S f hf F ε hp0 hp1 hF0 hF1 haxis
    obtain ⟨ρ,hρ,hmeet⟩ := avoidFramed S ε hε square hsquare F hFsquare f N hN.continuous
      hcenter haxis hfmeet sgn δ η (fun k => (hpos k).2) hcoords
    have hend0 (w:BandWidth) : N (0,w)∈F.source ∧ F (N (0,w))=(sgn 0*δ 0*(w:ℝ),ε) := by
      have hh := hcoords 0 0 w (by simpa using (hpos 0).2)
      simpa only [hF0] using hh
    have hend1 (w:BandWidth) : N (1,w)∈F.source ∧ F (N (1,w))=(sgn 1*δ 1*(w:ℝ),-ε) := by
      have hh := hcoords 1 1 w (by simpa using (hpos 1).2)
      simpa only [hF1] using hh
    obtain ⟨square',hsquare',hdiameter',flip,band,hband,hbandcenter,hbottom,htop,hbandmeet⟩ :=
      signedAssembly S ε hε square hsquare F hFsquare N hN (sgn 0) (sgn 1) (δ 0) (δ 1)
        (hsign 0) (hsign 1) (hpos 0).1 (hpos 1).1 hend0 hend1 ρ hρ hmeet
    refine ⟨ε,hε,square',hsquare',flip,band,hband,hbottom,htop,hbandmeet,?_⟩
    have hbandrange : Set.range (fun u : I => band (u,⟨0,by norm_num⟩))=Set.range f := by
      have heq : (fun u : I => band (u,⟨0,by norm_num⟩))=f := by
        funext u
        exact (hbandcenter u).trans (hcenter u)
      rw [heq]
    rw [hdiameter',hbandrange,hdiameter,hfimage,hfbaseimage]
    ext x
    constructor
    · intro hx
      by_cases hi : x∈b.map '' (Circle.exp '' Set.Ioo α β)
      · left
        obtain ⟨w,⟨t,ht,rfl⟩,he⟩ := hi
        exact ⟨Circle.exp t,⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩,he⟩
      · exact Or.inr ⟨hx,hi⟩
    · rintro (⟨w,hw,rfl⟩|hx)
      · exact Set.mem_range_self w
      · exact hx.1
  obtain ⟨ε,hε,square,hsquare,flip,band,hband,hbottom,htop,hmeet,himage⟩ := regular
  cases flip with
  | true => exact Or.inr (twisted ε hε square hsquare band hband hbottom htop hmeet)
  | false =>
    have htop' : ∀ t, band (1,t) = square (squarePort ε hε 0 t) := by
      intro t
      simpa [flipBandWidth] using htop t
    obtain ⟨q,hq,E,hE,hBand,hSquare⟩ := untwisted ε hε square hsquare band hband hbottom htop' hmeet
    letI : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
    let c : AddCircle (2 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
    let zero : BandWidth := ⟨0,by norm_num⟩
    have hqcore : Set.range (fun u : unitInterval => square (q (u,zero))) =
        square '' {z | (z : ℝ × ℝ).1 = 0} := by
      apply Set.Subset.antisymm
      · rintro x ⟨u,rfl⟩
        refine ⟨q (u,zero),?_,rfl⟩
        have h := congrArg Prod.fst (hq u zero)
        simpa [zero] using h
      · rintro x ⟨z,hz,rfl⟩
        have hdist : max |(z : ℝ × ℝ).1| |(z : ℝ × ℝ).2| ≤ ε := by
          simpa only [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,
            Prod.fst_zero,Prod.snd_zero,sub_zero] using z.property
        have hy : |(z : ℝ × ℝ).2| ≤ ε := (max_le_iff.mp hdist).2
        let u : unitInterval := ⟨(ε-(z : ℝ × ℝ).2)/(2*ε),by
          constructor
          · exact div_nonneg (by linarith [(abs_le.mp hy).2]) (by positivity)
          · apply (div_le_one (by positivity : 0 < 2*ε)).mpr
            linarith [(abs_le.mp hy).1]⟩
        refine ⟨u,?_⟩
        apply congrArg square
        apply Subtype.ext
        rw [hq u zero]
        apply Prod.ext
        · simpa [zero] using hz.symm
        · change ε*(1-2*((ε-(z : ℝ × ℝ).2)/(2*ε))) = (z : ℝ × ℝ).2
          field_simp
          <;> ring
    have hcenterImage : Set.range (fun z : Circle => E (⟨0,by norm_num⟩,z)) =
        Set.range (fun u : unitInterval => band (u,zero)) ∪
          Set.range (fun u : unitInterval => square (q (u,zero))) := by
      apply Set.Subset.antisymm
      · rintro x ⟨z,rfl⟩
        obtain ⟨t,ht,hzt⟩ := AddCircle.eq_coe_Ico (c.symm z)
        have hz : z = c (t : AddCircle (2 : ℝ)) := by rw [hzt,c.apply_symm_apply]
        by_cases ht1 : t ≤ 1
        · let u : unitInterval := ⟨t,⟨ht.1,ht1⟩⟩
          exact Or.inl ⟨u,(hBand u).symm.trans (congrArg (fun w => E (⟨0,by norm_num⟩,w)) hz.symm)⟩
        · let u : unitInterval := ⟨t-1,by constructor <;> linarith [ht.2]⟩
          have hu : (u:ℝ)+1 = t := by dsimp [u]; ring
          have hs := hSquare u
          rw [hu] at hs
          exact Or.inr ⟨u,hs.symm.trans (congrArg (fun w => E (⟨0,by norm_num⟩,w)) hz.symm)⟩
      · rintro x (⟨u,rfl⟩ | ⟨u,rfl⟩)
        · exact ⟨c (u : AddCircle (2 : ℝ)),hBand u⟩
        · exact ⟨c (((u:ℝ)+1 : ℝ) : AddCircle (2 : ℝ)),hSquare u⟩
    have hcenter : Set.range (fun z : Circle => E (⟨0,by norm_num⟩,z)) = b.image := by
      rw [hcenterImage,hqcore,Set.union_comm]
      exact himage.symm
    exact Or.inl (reparam b E hE hcenter)

end CurveComplex.LocalSurgery

namespace CurveComplex.LocalSurgery
open scoped Manifold ContDiff

/-- Actual two-sided topological collar, with the unchanged b parametrization.
No orientation or annulus certificate is supplied as an input. -/
theorem actual_original_essential_circle_has_annular_collar
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (genus : ℕ) (hgenus : 2 ≤ genus) (hS : CurveComplex.IsGenus S genus)
    (b : CurveComplex.EssentialCurve S) :
    ∃ e : C(Set.Ioo (-1 : ℝ) 1 × Circle, S),
      Topology.IsOpenEmbedding e ∧
      ∀ w : Circle, e (⟨0, by norm_num⟩, w) = b.val.map w  := by
  rcases embedded_circle_annular_collar_or_local_reflection S b.val with hcollar | ⟨x, ⟨W⟩⟩
  · exact hcollar
  · exact False.elim
      (CurveComplex.GenusOrientationCandidate.no_local_reflection_witness
        genus hS x
        (CurveComplex.GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) W)

end CurveComplex.LocalSurgery
