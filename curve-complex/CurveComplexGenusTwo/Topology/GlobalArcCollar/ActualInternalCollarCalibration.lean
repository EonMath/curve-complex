import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchSquares
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualFiniteAxisPatches
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualLocalAxisNormalizationProducer
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSurfaceAxisRectangleTransplant
set_option maxHeartbeats 3000000
namespace CurveComplex
open Set Topology Schoenflies

/-- Reuse the proved interior geometry to calibrate an actual seam while
fixing the whole original center and every point outside prescribed V. -/
theorem source_internal_collar_calibration
    {S : Type} [TopologicalSpace S] [T2Space S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (N : Interval × Set.Icc (-1:ℝ) 1 → S) (hN : IsEmbedding N)
    (hcenter : ∀ u, N (u,⟨0,by norm_num⟩) = f u)
    (t₀ : Interval) (hint : 0 < (t₀:ℝ) ∧ (t₀:ℝ) < 1)
    (D : OpenPartialHomeomorph S Plane) (hpD : f t₀ ∈ D.source)
    (hD0 : D (f t₀) = 0)
    (haxisD : ∀ u, f u ∈ D.source → D (f u) 1 = 0)
    (U V : Set S) (hU : IsOpen U) (hVo : IsOpen V) (hVU : V ⊆ U)
    (htV : f t₀ ∈ V) (hNU : Set.range N ⊆ U) :
    ∃ widthFactor : ℝ, ∃ hw : 0 < widthFactor ∧ widthFactor ≤ 1,
    ∃ sgn δ η : ℝ, ∃ F : S ≃ₜ S,
      (sgn = -1 ∨ sgn = 1) ∧ 0 < δ ∧ 0 < η ∧
      (∀ u, F (f u) = f u) ∧ (∀ x, x ∉ V → F x = x) ∧
      ∀ (u : Interval) (w : Set.Icc (-1:ℝ) 1),
        |(u:ℝ)-(t₀:ℝ)| < η →
        F (N (u,⟨widthFactor*(w:ℝ),by
          constructor <;> nlinarith [w.property.1,w.property.2,hw.1,hw.2]⟩)) ∈ D.source ∧
        D (F (N (u,⟨widthFactor*(w:ℝ),by
          constructor <;> nlinarith [w.property.1,w.property.2,hw.1,hw.2]⟩))) =
          Plane.mk (D (f u) 0) (sgn*δ*(w:ℝ)) := by
  classical
  have hopen : IsOpen (f ⁻¹' D.source) := D.open_source.preimage f.continuous
  obtain ⟨a₀,ha₀,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hpD)
  let ηlocal := a₀/2
  have hηlocal : 0 < ηlocal := half_pos ha₀
  have hηsource : f '' Metric.closedBall t₀ ηlocal ⊆ D.source := by
    rintro x ⟨u,hu,rfl⟩
    exact hball ((Metric.closedBall_subset_ball (half_lt_self ha₀)) hu)
  let d : ℝ := min (ηlocal / 2) (min ((t₀:ℝ)/2) ((1-(t₀:ℝ))/2))
  have hd : 0 < d := lt_min (half_pos hηlocal)
    (lt_min (by linarith [hint.1]) (by linarith [hint.2]))
  have hdη : d ≤ ηlocal / 2 := min_le_left _ _
  have hdt : d ≤ (t₀:ℝ)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hd1 : d ≤ (1-(t₀:ℝ))/2 := (min_le_right _ _).trans (min_le_right _ _)
  let a : Interval := ⟨(t₀:ℝ)-d,by constructor <;> linarith [hint.2]⟩
  let b : Interval := ⟨(t₀:ℝ)+d,by constructor <;> linarith [hint.1]⟩
  have hab : (a:ℝ) < b := by dsimp [a,b]; linarith
  obtain ⟨q,hq,hq0,hq1,hqrange,hqval⟩ := source_affine_subinterval a b hab
  let p : C(Interval,S) := f.comp q
  have hp : IsEmbedding p := hf.comp hq
  have hps : Set.range p ⊆ D.source := by
    rintro x ⟨t,rfl⟩
    have hqt : q t ∈ Set.Icc a b := hqrange ▸ Set.mem_range_self t
    have hdqt : dist (q t) t₀ ≤ ηlocal := by
      rw [Subtype.dist_eq,Real.dist_eq]
      apply abs_le.mpr
      change (t₀:ℝ)-d ≤ (q t:ℝ) ∧ (q t:ℝ) ≤ (t₀:ℝ)+d at hqt
      constructor <;> linarith [hηlocal]
    exact hηsource ⟨q t,hdqt,rfl⟩
  have hpaxis : ∀ t, D (p t) 1 = 0 := fun t => haxisD (q t) (hps (Set.mem_range_self t))
  let mid : Interval := ⟨1/2,by constructor <;> norm_num⟩
  have hqmid : q mid = t₀ := by
    apply Subtype.ext
    rw [hqval]
    dsimp [a,b,mid]
    ring
  have hpmid : D (p mid) 0 = 0 := by
    change D (f (q mid)) 0 = 0
    rw [hqmid,hD0]
    rfl
  -- Actual compact supports for previously framed windows, avoided by
  -- a selected new chart square BEFORE choosing the normalized radius.
  have hpointV : f t₀ ∈ V := htV
  have hplaneOpen : IsOpen (D '' (D.source ∩ V)) :=
    D.isOpen_image_source_inter hVo
  have hplaneZero : (0:Plane) ∈ D '' (D.source ∩ V) :=
    ⟨f t₀,⟨hpD,hpointV⟩,hD0⟩
  obtain ⟨s,hs,hs1,hsmall⟩ := Plane.exists_openSquare_subset hplaneOpen hplaneZero (by norm_num : (0:ℝ)<1)
  let ε : ℝ := s/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsupport : Plane.closedSquare 0 (2*ε) ⊆ D '' (D.source ∩ V) := by
    intro z hz
    apply hsmall
    change Plane.supDist z 0 < s
    have hz' : Plane.supDist z 0 ≤ 2*ε := hz
    dsimp [ε] at hz'
    linarith
  obtain ⟨r,hr,hr1,j,J,hj,hJ,hjcoords,hJcoords⟩ :=
    source_local_axis_normalization p hp D hps hpaxis mid
      (by norm_num [mid]) (by norm_num [mid]) hpmid ε hε
  -- ACTUAL INTERNAL EXTRACTION: construct the normalized old-collar
  -- rectangle and its small chart support. Nothing below is an input
  -- premise of t₀he original theorem.
  have hextract :
      ∃ ρ : ℝ, ∃ hρ : 0 < ρ ∧ ρ ≤ 1,
      ∃ e : OpenPartialHomeomorph S Plane,
      ∃ B : ↥(Plane.closedSquare 0 1) → S,
        Plane.closedSquare 0 2 ⊆ e.target ∧ e.source ⊆ V ∧
        (∀ x ∈ e.source, x ∈ U ∧ x ∈ D.source ∧
          e x = (1/r) • D x) ∧
        (∀ u, f u ∈ e.source → e (f u) 1 = 0) ∧
        IsEmbedding B ∧ Set.range B ⊆ e.source ∧
        (∀ z, B z = N (q (j ⟨z.val 0,by
          have hz : max |z.val 0| |z.val 1| ≤ 1 := by
            simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
          exact abs_le.mp ((le_max_left _ _).trans hz)⟩),
          ⟨ρ*z.val 1,by
            have hz : max |z.val 0| |z.val 1| ≤ 1 := by
              simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
            have hy := abs_le.mp ((le_max_right _ _).trans hz)
            constructor <;> nlinarith [hρ.1,hρ.2]⟩)) ∧
        (∀ t : Set.Icc (-1:ℝ) 1,
          e (B ⟨Plane.mk t 0,by
            simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩) = Plane.mk t 0) ∧
        (Set.range (e ∘ B) ∩ {z : Plane | z 1 = 0} =
          (fun t : Set.Icc (-1:ℝ) 1 => Plane.mk t 0) '' Set.univ) := by
    let scale : Plane ≃ₜ Plane := {
      toFun := fun z => (1/r) • z
      invFun := fun z => r • z
      left_inv := by intro z; simp [smul_smul,hr.ne']
      right_inv := by intro z; simp [smul_smul,hr.ne']
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop
    }
    let e := (D.restr V).transHomeomorph scale
    have heSource : e.source = D.source ∩ V := by
      simp only [e,OpenPartialHomeomorph.transHomeomorph_source,
        D.restr_source' V hVo]
    have heFun (x : S) : e x = (1/r) • D x := rfl
    have heOriginal : ∀ x ∈ e.source, x ∈ U ∧ x ∈ D.source ∧
        e x = (1/r) • D x := by
      intro x hx
      rw [heSource] at hx
      exact ⟨hVU hx.2,hx.1,heFun x⟩
    have hrSupport : Plane.closedSquare 0 (2*r) ⊆
        D '' (D.source ∩ V) := by
      apply Set.Subset.trans _ hsupport
      intro z hz
      change Plane.supDist z 0 ≤ 2*ε
      exact (show Plane.supDist z 0 ≤ 2*r from hz).trans (by linarith)
    have heTarget : Plane.closedSquare 0 2 ⊆ e.target := by
      intro z hz
      have hzB : max |z 0| |z 1| ≤ 2 := by
        simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using hz
      have hrsq : r • z ∈ Plane.closedSquare 0 (2*r) := by
        simp only [Plane.closedSquare,Plane.supDist,Plane.supNorm,sub_zero,Set.mem_setOf_eq]
        simp only [PiLp.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hr]
        apply max_le
        · nlinarith [(le_max_left _ _).trans hzB]
        · nlinarith [(le_max_right _ _).trans hzB]
      obtain ⟨x,hx,hEx⟩ := hrSupport hrsq
      have hxe : x ∈ e.source := heSource ▸ hx
      have heq : e x = z := by rw [heFun,hEx]; simp [smul_smul,hr.ne']
      exact heq ▸ e.map_source hxe
    have heAxis : ∀ u, f u ∈ e.source → e (f u) 1 = 0 := by
      intro u hu
      rw [heFun]
      change (1/r)*D (f u) 1 = 0
      rw [haxisD u (heOriginal _ hu).2.1,mul_zero]
    let W := Set.Icc (-1:ℝ) 1
    letI : CompactSpace W := isCompact_iff_compactSpace.mp isCompact_Icc
    let raw : W × W → S := fun z => N (q (j z.1),z.2)
    have hrawc : Continuous raw := hN.continuous.comp
      ((q.continuous.comp (j.continuous.comp continuous_fst)).prodMk continuous_snd)
    let Oambient : Set S := e.source ∩
      (D.source ∩ D ⁻¹' {z : Plane | |z 0| < 2*r})
    have hOambient : IsOpen Oambient := e.open_source.inter
      (D.isOpen_inter_preimage (isOpen_lt (by fun_prop) continuous_const))
    have hrawCenter : ∀ x : W, raw (x,⟨0,by norm_num [W]⟩) ∈ Oambient := by
      intro x
      have hcoords := hjcoords x
      have hsource := hps (Set.mem_range_self (j x))
      have hsmallCenter : D (p (j x)) ∈ Plane.closedSquare 0 (2*r) := by
        rw [hcoords]
        simp only [Plane.closedSquare,Plane.supDist,Plane.supNorm,sub_zero,Set.mem_setOf_eq,Plane.mk]
        change max |r*(x:ℝ)| |(0:ℝ)| ≤ 2*r
        rw [abs_mul,abs_of_pos hr,abs_zero]
        exact max_le (by nlinarith [abs_le.mpr x.property]) (by positivity)
      obtain ⟨y,hy,hEy⟩ := hrSupport hsmallCenter
      have heq : y = p (j x) := D.injOn hy.1 hsource hEy
      have hV : p (j x) ∈ V := heq ▸ hy.2
      change N (q (j x),⟨0,by norm_num [W]⟩) ∈ Oambient
      rw [hcenter]
      refine ⟨heSource ▸ ⟨hsource,hV⟩,hsource,?_⟩
      have hh := congrArg (fun z : Plane => z 0) hcoords
      change D (f (q (j x))) 0 = r*(x:ℝ) at hh
      change |D (f (q (j x))) 0| < 2*r
      rw [hh,abs_mul,abs_of_pos hr]
      nlinarith [abs_le.mpr x.property]
    let O : Set (W × W) := raw ⁻¹' Oambient
    have hO : IsOpen O := hOambient.preimage hrawc
    have hbase : Set.univ ×ˢ ({⟨0,by norm_num [W]⟩} : Set W) ⊆ O := by
      rintro ⟨x,w⟩ ⟨_,hw⟩
      have he : w = ⟨0,by norm_num [W]⟩ := hw
      subst w
      exact hrawCenter x
    obtain ⟨L,T,hL,hT,hUL,h0T,hLT⟩ := generalized_tube_lemma
      isCompact_univ isCompact_singleton hO hbase
    let clip : ℝ → W := Set.projIcc (-1) 1 (by norm_num [W])
    have h0pre : (0:ℝ) ∈ clip ⁻¹' T := by
      simpa [clip,Set.projIcc_of_mem] using
        h0T (Set.mem_singleton (⟨0,by norm_num [W]⟩ : W))
    obtain ⟨d₀,hd₀,hdT⟩ := Metric.mem_nhds_iff.mp
      ((hT.preimage continuous_projIcc).mem_nhds h0pre)
    let ρ : ℝ := min (d₀/2) (1/2)
    have hρ : 0 < ρ ∧ ρ ≤ 1 := by
      constructor
      · dsimp [ρ]; positivity
      · have hh := min_le_right (d₀/2) (1/2:ℝ); dsimp [ρ]; linarith
    have hρd : ρ < d₀ := by
      have hh := min_le_left (d₀/2) (1/2:ℝ); dsimp [ρ]; linarith
    have hstrip : ∀ (x w : W), raw (x,⟨ρ*(w:ℝ),by
        constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩) ∈ Oambient := by
      intro x w
      apply hLT ⟨hUL trivial,?_⟩
      have hw : ρ*(w:ℝ) ∈ Set.Icc (-1:ℝ) 1 := by
        constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]
      have habs : |ρ*(w:ℝ)| < d₀ := by
        rw [abs_mul,abs_of_pos hρ.1]
        exact (mul_le_mul_of_nonneg_left (abs_le.mpr w.property) hρ.1.le).trans_lt
          (by simpa using hρd)
      have hh := hdT (show ρ*(w:ℝ) ∈ Metric.ball (0:ℝ) d₀ by
        simpa [Metric.mem_ball,Real.dist_eq] using habs)
      simpa [clip,Set.projIcc_of_mem _ hw] using hh
    let sx : ↥(Plane.closedSquare 0 1) → W := fun z => ⟨z.val 0,by
      have hz : max |z.val 0| |z.val 1| ≤ 1 := by
        simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
      exact abs_le.mp ((le_max_left _ _).trans hz)⟩
    let sy : ↥(Plane.closedSquare 0 1) → W := fun z => ⟨z.val 1,by
      have hz : max |z.val 0| |z.val 1| ≤ 1 := by
        simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
      exact abs_le.mp ((le_max_right _ _).trans hz)⟩
    let narrow : ↥(Plane.closedSquare 0 1) → Interval × W := fun z =>
      (q (j (sx z)),⟨ρ*(sy z:ℝ),by
        constructor <;> nlinarith [(sy z).property.1,(sy z).property.2,hρ.1,hρ.2]⟩)
    have hnc : Continuous narrow := by dsimp [narrow,sx,sy]; fun_prop
    have hni : Function.Injective narrow := by
      intro z w he
      have hx := hj.injective (hq.injective (congrArg Prod.fst he))
      have hx' := congrArg Subtype.val hx
      have hy := congrArg (fun z => (z.2:ℝ)) he
      have hy' : z.val 1 = w.val 1 := mul_left_cancel₀ hρ.1.ne' hy
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · exact hx'
      · exact hy'
    let B : ↥(Plane.closedSquare 0 1) → S := N ∘ narrow
    letI : CompactSpace ↥(Plane.closedSquare 0 1) :=
      isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
    have hB : IsEmbedding B := hN.comp (hnc.isClosedEmbedding hni).isEmbedding
    have hBambient : ∀ z, B z ∈ Oambient := fun z => hstrip (sx z) (sy z)
    have hBsource : Set.range B ⊆ e.source := by
      rintro x ⟨z,rfl⟩
      exact (hBambient z).1
    have hBcenter : ∀ t : W, e (B ⟨Plane.mk t 0,by
        simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩) = Plane.mk t 0 := by
      intro t
      change e (N (q (j t),⟨ρ*0,_⟩)) = _
      have hz : (⟨ρ*0,by constructor <;> norm_num [W]⟩ : W) = ⟨0,by norm_num [W]⟩ := Subtype.ext (mul_zero _)
      rw [hz,hcenter,heFun]
      change (1/r) • D (p (j t)) = _
      rw [hjcoords]
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [Plane.mk,smul_eq_mul,hr.ne']
    have hrecognize : ∀ z, e (B z) 1 = 0 → z.val 1 = 0 := by
      intro z hz
      have hcoordZero : D (B z) 1 = 0 := by
        rw [heFun] at hz
        change (1/r)*D (B z) 1 = 0 at hz
        exact (mul_eq_zero.mp hz).resolve_left (one_div_ne_zero hr.ne')
      have hcoordBound : |D (B z) 0| < 2*r := (hBambient z).2.2
      let x : W := ⟨D (B z) 0 / (2*r),by
        have hb := abs_lt.mp hcoordBound
        constructor
        · apply (le_div_iff₀ (by positivity : (0:ℝ)<2*r)).mpr; linarith [hb.1]
        · apply (div_le_iff₀ (by positivity : (0:ℝ)<2*r)).mpr; linarith [hb.2]⟩
      have haxisEq : D (B z) = D (p (J x)) := by
        rw [hJcoords]
        apply PiLp.ext
        intro i
        fin_cases i
        · change D (B z) 0 = 2*r*(D (B z) 0/(2*r))
          field_simp [hr.ne']
        · exact hcoordZero
      have heq : B z = p (J x) := D.injOn
        (hBambient z).2.1 (hps (Set.mem_range_self (J x))) haxisEq
      have htuple : narrow z = (q (J x),⟨0,by norm_num [W]⟩) :=
        hN.injective (heq.trans (hcenter (q (J x))).symm)
      have hy := congrArg (fun z => (z.2:ℝ)) htuple
      change ρ*z.val 1 = 0 at hy
      exact (mul_eq_zero.mp hy).resolve_left hρ.1.ne'
    have hBaxis : Set.range (e ∘ B) ∩ {z : Plane | z 1 = 0} =
        (fun t : W => Plane.mk t 0) '' Set.univ := by
      ext y
      constructor
      · rintro ⟨⟨z,rfl⟩,hz⟩
        have hy := hrecognize z hz
        have he : z = ⟨Plane.mk (sx z) 0,by
            simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr (sx z).property⟩ := by
          apply Subtype.ext
          apply PiLp.ext
          intro i
          fin_cases i
          · rfl
          · exact hy
        refine ⟨sx z,Set.mem_univ _,?_⟩
        exact (hBcenter (sx z)).symm.trans (congrArg (e ∘ B) he.symm)
      · rintro ⟨t,_,rfl⟩
        let z : ↥(Plane.closedSquare 0 1) := ⟨Plane.mk t 0,by
          simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩
        exact ⟨⟨z,hBcenter t⟩,rfl⟩
    refine ⟨ρ,hρ,e,B,heTarget,?_,heOriginal,heAxis,hB,hBsource,fun _ => rfl,hBcenter,hBaxis⟩
    intro x hx
    exact ((heSource ▸ hx) : x ∈ D.source ∩ V).2
  obtain ⟨ρ,hρ,e,B,heTarget,heV,heOriginal,heAxis,hB,hBsource,hBformula,
    hBcenter,hBaxis⟩ := hextract
  obtain ⟨τ,hτ,sgn,F,hsgn,hFcenter,hFfix,hFcoords⟩ :=
    source_surface_axis_rectangle_transplant e heTarget f heAxis B hB
      hBsource hBcenter hBaxis
  -- ACTUAL INVERSE COVERAGE: t is internal to the selected r-axis
  -- segment. The compact inverse exists already; its image must contain
  -- an actual parameter neighborhood of t₀.
  have hcoverage : ∃ ηnew : ℝ, 0 < ηnew ∧
      ∀ u : Interval, |(u:ℝ)-(t₀:ℝ)| < ηnew →
        ∃ x : Set.Icc (-1:ℝ) 1, q (j x) = u := by
    letI : Fact ((-1:ℝ) ≤ 1) := ⟨by norm_num⟩
    letI : Fact ((-1:ℝ) < 1) := ⟨by norm_num⟩
    letI : PreconnectedSpace (Set.Icc (-1:ℝ) 1) :=
      (isPreconnected_iff_preconnectedSpace).mp isPreconnected_Icc
    let v : Set.Icc (-1:ℝ) 1 → Interval := q ∘ j
    have hvc : Continuous v := q.continuous.comp j.continuous
    have hvi : Function.Injective v := hq.injective.comp hj.injective
    let zero : Set.Icc (-1:ℝ) 1 := ⟨0,by norm_num⟩
    let lo : Set.Icc (-1:ℝ) 1 := ⟨-1,by constructor <;> norm_num⟩
    let hi : Set.Icc (-1:ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
    have hvzero : v zero = t₀ := by
      apply hf.injective
      apply D.injOn (hps (Set.mem_range_self (j zero))) (hpD)
      rw [hD0]
      have hh := hjcoords zero
      have hzero : Plane.mk (r*(zero:ℝ)) 0 = (0:Plane) := by
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [Plane.mk,zero]
      exact hh.trans hzero
    have select (l r : Set.Icc (-1:ℝ) 1)
        (hl : (v l:ℝ) < (t₀:ℝ)) (hr : (t₀:ℝ) < (v r:ℝ)) :
        ∃ ηnew : ℝ, 0 < ηnew ∧
          ∀ u : Interval, |(u:ℝ)-(t₀:ℝ)| < ηnew →
            ∃ x : Set.Icc (-1:ℝ) 1, q (j x) = u := by
      let e := min ((t₀:ℝ)-(v l:ℝ)) ((v r:ℝ)-(t₀:ℝ))/2
      have he : 0 < e := by dsimp [e]; positivity
      have hel := min_le_left ((t₀:ℝ)-(v l:ℝ)) ((v r:ℝ)-(t₀:ℝ))
      have her := min_le_right ((t₀:ℝ)-(v l:ℝ)) ((v r:ℝ)-(t₀:ℝ))
      refine ⟨e,he,?_⟩
      intro u hu
      have habs := abs_lt.mp hu
      have huI : u ∈ Set.Icc (v l) (v r) := by
        change (v l:ℝ) ≤ (u:ℝ) ∧ (u:ℝ) ≤ (v r:ℝ)
        dsimp [e] at habs
        constructor <;> linarith [habs.1,habs.2]
      obtain ⟨x,hx⟩ := intermediate_value_univ l r hvc huI
      exact ⟨x,hx⟩
    rcases hvc.strictMono_of_inj_boundedOrder' hvi with hm | hm
    · apply select lo hi
      · have hh := hm (show lo < zero by change (-1:ℝ) < 0; norm_num)
        rwa [hvzero] at hh
      · have hh := hm (show zero < hi by change (0:ℝ) < 1; norm_num)
        rwa [hvzero] at hh
    · apply select hi lo
      · have hh := hm (show zero < hi by change (0:ℝ) < 1; norm_num)
        rwa [hvzero] at hh
      · have hh := hm (show lo < zero by change (-1:ℝ) < 0; norm_num)
        rwa [hvzero] at hh
  obtain ⟨ηnew,hηnew,hcoverage⟩ := hcoverage
  let widthFactor := ρ*τ
  have hwidthFactor : 0 < widthFactor ∧ widthFactor ≤ 1 := by
    dsimp [widthFactor]
    constructor
    · exact mul_pos hρ.1 hτ.1
    · nlinarith [hρ.1,hρ.2,hτ.1,hτ.2]
  let narrow : Interval × Set.Icc (-1:ℝ) 1 → Interval × Set.Icc (-1:ℝ) 1 :=
    fun z => (z.1,⟨widthFactor*(z.2:ℝ),by
      constructor <;> nlinarith [z.2.property.1,z.2.property.2,hwidthFactor.1,hwidthFactor.2]⟩)
  have hnarrowc : Continuous narrow := by dsimp [narrow]; fun_prop
  have hnarrowi : Function.Injective narrow := by
    intro z w he
    apply Prod.ext
    · simpa only [narrow] using congrArg Prod.fst he
    · apply Subtype.ext
      exact mul_left_cancel₀ hwidthFactor.1.ne' (congrArg (fun z => (z.2:ℝ)) he)
  have hnarrowe : IsEmbedding narrow :=
    (hnarrowc.isClosedEmbedding hnarrowi).isEmbedding
  let M : Interval × Set.Icc (-1:ℝ) 1 → S := F ∘ N ∘ narrow
  have hM : IsEmbedding M := F.isEmbedding.comp (hN.comp hnarrowe)
  have hMU : Set.range M ⊆ U := by
    rintro x ⟨z,rfl⟩
    have hxU := hNU (Set.mem_range_self (narrow z))
    by_contra hn
    change F (N (narrow z)) ∉ U at hn
    have hnot : F (N (narrow z)) ∉ e.source :=
      fun hs => hn (heOriginal _ hs).1
    have hfixed := hFfix (F (N (narrow z))) (fun hs => hnot hs.1)
    have heq : F (N (narrow z)) = N (narrow z) := F.injective hfixed
    exact hn (by rwa [heq])
  have hMcenter : ∀ u, M (u,⟨0,by norm_num⟩) = f u := by
    intro u
    have he : narrow (u,⟨0,by norm_num⟩) = (u,⟨0,by norm_num⟩) := by
      apply Prod.ext
      · rfl
      apply Subtype.ext
      simp [narrow]
    change F (N (narrow (u,⟨0,by norm_num⟩))) = f u
    rw [he,hcenter,hFcenter]
  have hMnew : ∀ (u : Interval) (w : Set.Icc (-1:ℝ) 1),
      |(u:ℝ)-(t₀:ℝ)| < ηnew →
      M (u,w) ∈ D.source ∧
      D (M (u,w)) = Plane.mk (D (f u) 0) (sgn*r*(w:ℝ)) := by
    intro u w hu
    obtain ⟨x,hxu⟩ := hcoverage u hu
    let z : ↥(Plane.closedSquare 0 1) := ⟨Plane.mk x w,by
      simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using
        max_le (abs_le.mpr x.property) (abs_le.mpr w.property)⟩
    have hbEq : B (sourceSquareTransverseNarrow τ hτ z) = N (narrow (u,w)) := by
      rw [hBformula]
      apply congrArg N
      apply Prod.ext
      · exact hxu
      · apply Subtype.ext
        change ρ*(τ*(w:ℝ)) = widthFactor*(w:ℝ)
        dsimp [widthFactor]
        ring
    have hFz := hFcoords z
    rw [hbEq] at hFz
    have horig := heOriginal (M (u,w)) hFz.1
    refine ⟨horig.2.1,?_⟩
    have hplane : (1/r) • D (M (u,w)) = Plane.mk (x:ℝ) (sgn*(w:ℝ)) :=
      horig.2.2.symm.trans hFz.2
    have hcenterx : D (f u) 0 = r*(x:ℝ) := by
      have hh := congrArg (fun v : Plane => v 0) (hjcoords x)
      change D (f (q (j x))) 0 = r*(x:ℝ) at hh
      rwa [hxu] at hh
    apply PiLp.ext
    intro i
    fin_cases i
    · have hh := congrArg (fun v : Plane => v 0) hplane
      change (1/r)*D (M (u,w)) 0 = (x:ℝ) at hh
      change D (M (u,w)) 0 = D (f u) 0
      rw [hcenterx]
      field_simp at hh
      nlinarith
    · have hh := congrArg (fun v : Plane => v 1) hplane
      change (1/r)*D (M (u,w)) 1 = sgn*(w:ℝ) at hh
      change D (M (u,w)) 1 = sgn*r*(w:ℝ)
      field_simp at hh
      nlinarith
  refine ⟨widthFactor,hwidthFactor,sgn,r,ηnew,F,hsgn,hr,hηnew,hFcenter,?_,?_⟩
  · intro x hx
    exact hFfix x (fun he => hx (heV he.1))
  · exact hMnew

#print axioms CurveComplex.source_internal_collar_calibration


end CurveComplex
