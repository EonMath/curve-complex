import CurveComplexGenusTwo.Topology.ActualCrosscapGeometry.RawCrosscapSquareStrip
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceCircleGluingProbe
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib
open scoped Manifold ContDiff
open Set Topology
open LeanEval.Topology.ClassificationOfSurfaces
namespace CurveComplex.LocalSurgery
set_option maxHeartbeats 1000000
theorem actual_nonorientable_crosscap_embedding_has_single_crossing
    {U : Type} [TopologicalSpace U] [T2Space U]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U]
    (p n : ℕ) (hp : 1 ≤ p)
    (f : Quot (NonOrientableRel p n) → U) (hf : Topology.IsEmbedding f) :
    ∃ (a b : Curve U) (hab : Transverse a b), hab.1.toFinset.card = 1 := by
  classical
  obtain ⟨ε,hε,square0,band0,hSquare0,hBand0,hBottom0,hTop0,hMeet0⟩ :=
    CurveComplex.Hyperbolic.actual_nonorientable_normal_form_first_crosscap_square_strip p n
      (by omega)
  let D := Metric.closedBall ((0,0):ℝ×ℝ) ε
  let square : D → U := f ∘ square0
  let band : unitInterval × CurveComplex.BandWidth → U := f ∘ band0
  have hSquare : Topology.IsEmbedding square := hf.comp hSquare0
  have hBand : Topology.IsEmbedding band := hf.comp hBand0
  have hBottom (w : CurveComplex.BandWidth) : band (0,w)=square (CurveComplex.squarePort ε hε 2 w) :=
    congrArg f (hBottom0 w)
  have hTop (w : CurveComplex.BandWidth) : band (1,w)=square
      (CurveComplex.squarePort ε hε 0 (CurveComplex.flipBandWidth true w)) :=
    congrArg f (hTop0 w)
  have hMeet : Set.range band ∩ Set.range square =
      Set.range (fun w => square (CurveComplex.squarePort ε hε 2 w)) ∪
      Set.range (fun w => square (CurveComplex.squarePort ε hε 0 w)) := by
    have hh := congrArg (fun A => f '' A) hMeet0
    rw [Set.image_inter hf.injective,Set.image_union] at hh
    simpa only [square,band,←Set.range_comp,Function.comp_def] using hh
  have hFlip (w : CurveComplex.BandWidth) : CurveComplex.flipBandWidth true
      (CurveComplex.flipBandWidth true w)=w := by
    apply Subtype.ext
    simp [CurveComplex.flipBandWidth]
  have hBandEnds (t : unitInterval) (w : CurveComplex.BandWidth)
      (u : D) (he : square u=band (t,w)) : t=0 ∨ t=1 := by
    have hm : band (t,w) ∈ Set.range band ∩ Set.range square :=
      ⟨Set.mem_range_self _,⟨u,he⟩⟩
    rw [hMeet] at hm
    rcases hm with ⟨w',hw'⟩ | ⟨w',hw'⟩
    · have hh := hBand.injective (hw'.symm.trans (hBottom w').symm)
      exact Or.inl (congrArg Prod.fst hh)
    · have hhTop : band (1,CurveComplex.flipBandWidth true w')=
          square (CurveComplex.squarePort ε hε 0 w') := by rw [hTop,hFlip]
      have hh := hBand.injective (hw'.symm.trans hhTop.symm)
      exact Or.inr (congrArg Prod.fst hh)
  let seg (w : CurveComplex.BandWidth) (t : unitInterval) : D :=
    ⟨(ε/4*(w:ℝ)*(2*(t:ℝ)-1), ε*(1-2*(t:ℝ))), by
      have hw : |(w:ℝ)| ≤ 1 := abs_le.mpr w.property
      have ht : |2*(t:ℝ)-1| ≤ 1 := abs_le.mpr ⟨by linarith [t.property.1],by linarith [t.property.2]⟩
      have ht' : |1-2*(t:ℝ)| ≤ 1 := by
        rw [show 1-2*(t:ℝ)=-(2*(t:ℝ)-1) by ring,abs_neg]
        exact ht
      have hprod : |(w:ℝ)| * |2*(t:ℝ)-1| ≤ 1 := by
        nlinarith [abs_nonneg (w:ℝ),abs_nonneg (2*(t:ℝ)-1)]
      change (ε/4*(w:ℝ)*(2*(t:ℝ)-1), ε*(1-2*(t:ℝ))) ∈ Metric.closedBall (0,0) ε
      simp only [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,sub_zero,max_le_iff]
      constructor
      · rw [abs_mul,abs_mul,abs_div,abs_of_pos hε]
        norm_num
        nlinarith [mul_le_mul_of_nonneg_left hprod hε.le]
      · rw [abs_mul,abs_of_pos hε]
        nlinarith [mul_le_mul_of_nonneg_left ht' hε.le]⟩
  have hSegContinuous (w : CurveComplex.BandWidth) : Continuous (seg w) := by
    apply Continuous.subtype_mk
    fun_prop
  have hSegInjective (w : CurveComplex.BandWidth) : Function.Injective (seg w) := by
    intro t u he
    have hh := congrArg (fun v : D => v.val.2) he
    dsimp [seg] at hh
    apply Subtype.ext
    nlinarith
  have hSegEmbedding (w : CurveComplex.BandWidth) : IsEmbedding (seg w) :=
    ((hSegContinuous w).isClosedEmbedding (hSegInjective w)).isEmbedding
  have hSegTop (w : CurveComplex.BandWidth) : seg w 0=
      CurveComplex.squarePort ε hε 0 (CurveComplex.flipBandWidth true w) := by
    apply Subtype.ext
    simp [seg,CurveComplex.squarePort,CurveComplex.crossingEndRectangle,CurveComplex.flipBandWidth]
  have hSegBottom (w : CurveComplex.BandWidth) : seg w 1=
      CurveComplex.squarePort ε hε 2 w := by
    apply Subtype.ext
    norm_num [seg,CurveComplex.squarePort,CurveComplex.crossingEndRectangle]
  have hBandSliceEmbedding (w : CurveComplex.BandWidth) :
      IsEmbedding (fun t : unitInterval => band (t,w)) :=
    hBand.comp (IsEmbedding.of_leftInverse (by intro t; rfl :
      Function.LeftInverse Prod.fst (fun t : unitInterval => (t,w))) continuous_fst (by fun_prop))
  have hCurveForWidth (w : CurveComplex.BandWidth) :
      ∃ c : Curve U, c.image=Set.range (square ∘ seg w) ∪ Set.range (fun t : unitInterval => band (t,w)) := by
    let upper := square (seg w 0)
    let lower := square (seg w 1)
    let P : Path upper lower :=
      { toFun := square ∘ seg w
        continuous_toFun := hSquare.continuous.comp (hSegContinuous w)
        source' := rfl
        target' := rfl }
    let Q : Path lower upper :=
      { toFun := fun t => band (t,w)
        continuous_toFun := hBand.continuous.comp (by fun_prop)
        source' := by rw [hBottom,←hSegBottom]
        target' := by rw [hTop,←hSegTop] }
    have hP : IsEmbedding P := hSquare.comp (hSegEmbedding w)
    have hQ : IsEmbedding Q := hBandSliceEmbedding w
    have hInter : Set.range P ∩ Set.range Q = {upper,lower} := by
      ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,⟨u,heu⟩⟩
        have hh : square (seg w t)=band (u,w) := heu.symm
        rcases hBandEnds u w (seg w t) hh with hu | hu
        · rw [hu] at hh
          right
          exact hh.trans Q.source
        · rw [hu] at hh
          left
          exact hh.trans Q.target
      · rintro (hz | hz)
        · exact ⟨⟨0,P.source.trans hz.symm⟩,⟨1,Q.target.trans hz.symm⟩⟩
        · exact ⟨⟨1,P.target.trans hz.symm⟩,⟨0,Q.source.trans hz.symm⟩⟩
    obtain ⟨c,hc,himage⟩ := CurveComplex.exists_embedded_circle_of_two_paths_probe P Q hP hQ hInter
    exact ⟨⟨c,hc⟩,himage⟩
  let w0 : CurveComplex.BandWidth := ⟨0,by norm_num⟩
  let w1 : CurveComplex.BandWidth := ⟨1/2,by norm_num⟩
  let mid : unitInterval := ⟨1/2,by norm_num⟩
  let origin : D := ⟨(0,0),by simp [D,hε.le]⟩
  have hMid (w : CurveComplex.BandWidth) : seg w mid=origin := by
    apply Subtype.ext
    norm_num [seg,mid,origin]
  have hSegIntersect (t u : unitInterval) (he : seg w0 t=seg w1 u) : t=mid ∧ u=mid := by
    have hx := congrArg (fun v : D => v.val.1) he
    have hy := congrArg (fun v : D => v.val.2) he
    dsimp [seg,w0,w1] at hx hy
    have hu : (u:ℝ)=1/2 := by nlinarith
    have ht : (t:ℝ)=1/2 := by nlinarith
    exact ⟨Subtype.ext ht,Subtype.ext hu⟩
  obtain ⟨a,ha⟩ := hCurveForWidth w0
  obtain ⟨b,hb⟩ := hCurveForWidth w1
  have hSquareBandDisjoint (t u : unitInterval) :
      square (seg w0 t) ≠ band (u,w1) := by
    intro he
    rcases hBandEnds u w1 (seg w0 t) he with hu | hu
    · rw [hu,hBottom,←hSegBottom] at he
      have hh := (hSegIntersect t 1 (hSquare.injective he)).2
      have hhR := congrArg Subtype.val hh
      norm_num [mid] at hhR
    · rw [hu,hTop,←hSegTop] at he
      have hh := (hSegIntersect t 0 (hSquare.injective he)).2
      have hhR := congrArg Subtype.val hh
      norm_num [mid] at hhR
  have hBandSquareDisjoint (t u : unitInterval) :
      band (t,w0) ≠ square (seg w1 u) := by
    intro he
    rcases hBandEnds t w0 (seg w1 u) he.symm with ht | ht
    · rw [ht,hBottom,←hSegBottom] at he
      have hh := (hSegIntersect 1 u (hSquare.injective he)).1
      have hhR := congrArg Subtype.val hh
      norm_num [mid] at hhR
    · rw [ht,hTop,←hSegTop] at he
      have hh := (hSegIntersect 0 u (hSquare.injective he)).1
      have hhR := congrArg Subtype.val hh
      norm_num [mid] at hhR
  have hBandBandDisjoint (t u : unitInterval) : band (t,w0) ≠ band (u,w1) := by
    intro he
    have hh := congrArg (fun v : unitInterval × CurveComplex.BandWidth => (v.2:ℝ))
      (hBand.injective he)
    norm_num [w0,w1] at hh
  have hOne : a.image ∩ b.image={square origin} := by
    rw [ha,hb]
    ext z
    constructor
    · rintro ⟨(⟨t,rfl⟩ | ⟨t,rfl⟩),(⟨u,heu⟩ | ⟨u,heu⟩)⟩
      · have hh := hSegIntersect t u (hSquare.injective heu.symm)
        simp only [Set.mem_singleton_iff]
        change square (seg w0 t)=square origin
        rw [hh.1,hMid]
      · exact False.elim (hSquareBandDisjoint t u heu.symm)
      · exact False.elim (hBandSquareDisjoint t u heu.symm)
      · exact False.elim (hBandBandDisjoint t u heu.symm)
    · intro hz
      have hz' : z=square origin := hz
      rw [hz']
      exact ⟨Or.inl ⟨mid,by rw [Function.comp_apply,hMid]⟩,
        Or.inl ⟨mid,by rw [Function.comp_apply,hMid]⟩⟩
  have hTrace (w : CurveComplex.BandWidth) (c : Curve U)
      (hc : c.image=Set.range (square ∘ seg w) ∪ Set.range (fun t : unitInterval => band (t,w)))
      (u : D) (hu : |u.val.2| < ε) :
      square u ∈ c.image ↔ u.val.1+(w:ℝ)/4*u.val.2=0 := by
    rw [hc]
    constructor
    · rintro (⟨t,he⟩ | ⟨t,he⟩)
      · have hh : seg w t=u := hSquare.injective he
        rw [←hh]
        dsimp [seg]
        ring
      · have hh : square u=band (t,w) := he.symm
        rcases hBandEnds t w u hh with ht | ht
        · rw [ht,hBottom] at hh
          have hcoord := congrArg (fun v : D => v.val.2) (hSquare.injective hh)
          have hcoord' : u.val.2 = -ε := by
            simpa [CurveComplex.squarePort,CurveComplex.crossingEndRectangle] using hcoord
          rw [hcoord',abs_neg,abs_of_pos hε] at hu
          exact False.elim (lt_irrefl _ hu)
        · rw [ht,hTop] at hh
          have hcoord := congrArg (fun v : D => v.val.2) (hSquare.injective hh)
          have hcoord' : u.val.2 = ε := by
            simpa [CurveComplex.squarePort,CurveComplex.crossingEndRectangle] using hcoord
          rw [hcoord',abs_of_pos hε] at hu
          exact False.elim (lt_irrefl _ hu)
    · intro hx
      have hy := abs_lt.mp hu
      let t : unitInterval := ⟨(ε-u.val.2)/(2*ε),by
        constructor
        · exact div_nonneg (by linarith) (by positivity)
        · apply (div_le_iff₀ (by positivity : 0 < 2*ε)).mpr
          linarith⟩
      have hh : seg w t=u := by
        apply Subtype.ext
        apply Prod.ext
        · have hux : u.val.1=-(w:ℝ)/4*u.val.2 := by linarith
          change ε/4*(w:ℝ)*(2*((ε-u.val.2)/(2*ε))-1)=u.val.1
          rw [hux]
          field_simp
          ring
        · change ε*(1-2*((ε-u.val.2)/(2*ε)))=u.val.2
          field_simp
          ring
      exact Or.inl ⟨t,congrArg square hh⟩
  have hCross : CrossesAt a b (square origin) := by
    let O : Set (ℝ×ℝ) := {z | |z.1|<ε/2 ∧ |z.2|<ε/2}
    have hO : IsOpen O := (isOpen_lt
      (by fun_prop : Continuous (fun z : ℝ×ℝ => |z.1|)) continuous_const).inter
      (isOpen_lt (by fun_prop : Continuous (fun z : ℝ×ℝ => |z.2|)) continuous_const)
    let j : O → D := fun z => ⟨z.val,by
      change z.val ∈ Metric.closedBall (0,0) ε
      simp only [Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,sub_zero,max_le_iff]
      exact ⟨by linarith [z.property.1],by linarith [z.property.2]⟩⟩
    have hjc : Continuous j := continuous_subtype_val.subtype_mk _
    have hje : IsEmbedding j := IsEmbedding.of_comp hjc continuous_subtype_val IsEmbedding.subtypeVal
    let g : O → U := square ∘ j
    have hge : IsEmbedding g := hSquare.comp hje
    let pc : (EuclideanSpace ℝ (Fin 2)) ≃ₜ (ℝ×ℝ) :=
      { toEquiv :=
          { toFun := fun z => (z 0,z 1)
            invFun := fun z => Schoenflies.Plane.mk z.1 z.2
            left_inv := by intro z; ext i; fin_cases i <;> rfl
            right_inv := by intro z; rfl }
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let V := pc ⁻¹' O
    let k : V → U := fun z => g ⟨pc z.val,z.property⟩
    let F : EuclideanSpace ℝ (Fin 2) → U :=
      Function.extend Subtype.val k (fun _ => square origin)
    have hFk (z : V) : F z=k z := Subtype.val_injective.extend_apply _ _ z
    have hFc : ContinuousOn F V := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      have heq : V.domRestrict F=k := funext hFk
      rw [heq]
      exact hge.continuous.comp ((pc.continuous.comp continuous_subtype_val).subtype_mk _)
    have hFi : InjOn F V := by
      intro z hz w hw he
      have he' : k ⟨z,hz⟩=k ⟨w,hw⟩ := by rw [←hFk ⟨z,hz⟩,←hFk ⟨w,hw⟩]; exact he
      have hh := congrArg Subtype.val (hge.injective he')
      exact pc.injective hh
    have hFU : IsOpen (F '' V) := surface_invariance_of_domain_probe F V
      (hO.preimage pc.continuous) hFc hFi
    have hRange : Set.range g=F '' V := by
      ext z
      constructor
      · rintro ⟨u,rfl⟩
        have hpc : pc (pc.symm u.val)=u.val := pc.apply_symm_apply u.val
        refine ⟨pc.symm u.val,by change pc (pc.symm u.val) ∈ O; rw [hpc]; exact u.property,?_⟩
        rw [hFk ⟨pc.symm u.val,by change pc (pc.symm u.val) ∈ O; rw [hpc]; exact u.property⟩]
        change g ⟨pc (pc.symm u.val),_⟩=g u
        congr 1
      · rintro ⟨u,hu,rfl⟩
        exact ⟨⟨pc u,hu⟩,(hFk ⟨u,hu⟩).symm⟩
    have hGOpen : IsOpen (Set.range g) := hRange.symm ▸ hFU
    let shear : (ℝ×ℝ) ≃ₜ (ℝ×ℝ) :=
      { toEquiv :=
          { toFun := fun z => (z.1,z.1+z.2/8)
            invFun := fun z => (z.1,8*(z.2-z.1))
            left_inv := by intro z; ext <;> dsimp <;> ring
            right_inv := by intro z; ext <;> dsimp <;> ring }
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let H := hge.toHomeomorph.symm.trans (shear.image O)
    let z0 : O := ⟨(0,0),by constructor <;> simpa using (half_pos hε)⟩
    have hg0 : g z0=square origin := rfl
    have hp : square origin ∈ Set.range g := ⟨z0,hg0⟩
    have hInv0 : hge.toHomeomorph.symm ⟨square origin,hp⟩=z0 := by
      apply hge.toHomeomorph.injective
      rw [hge.toHomeomorph.apply_symm_apply]
      exact Subtype.ext hg0.symm
    refine ⟨Set.range g,shear '' O,hp,H,hGOpen,shear.isOpenMap O hO,?_,?_⟩
    · change shear (hge.toHomeomorph.symm ⟨square origin,hp⟩)=(0,0)
      rw [hInv0]
      norm_num [shear,z0]
    · intro x hx
      let z := hge.toHomeomorph.symm ⟨x,hx⟩
      have hgx : g z=x := congrArg Subtype.val (hge.toHomeomorph.apply_symm_apply ⟨x,hx⟩)
      have hzY : |(j z).val.2| < ε := by
        change |z.val.2| < ε
        linarith [z.property.2]
      have htA := hTrace w0 a ha (j z) hzY
      have htB := hTrace w1 b hb (j z) hzY
      change square (j z)=x at hgx
      rw [hgx] at htA htB
      change (x∈a.image ↔ z.val.1=0) ∧ (x∈b.image ↔ z.val.1+z.val.2/8=0)
      constructor
      · simpa [w0,j] using htA
      · convert htB using 1 <;> dsimp [w1,j] <;> ring

  have hab : Transverse a b := by
    refine ⟨by rw [hOne]; exact Set.finite_singleton _,?_⟩
    intro z hz
    rw [hOne] at hz
    have hz' : z=square origin := hz
    simpa only [hz'] using hCross
  refine ⟨a,b,hab,?_⟩
  have hh : hab.1.toFinset={square origin} := by
    ext z
    simp only [Set.Finite.mem_toFinset,Finset.mem_singleton]
    rw [hOne]
    rfl
  rw [hh]
  exact Finset.card_singleton _

end CurveComplex.LocalSurgery
