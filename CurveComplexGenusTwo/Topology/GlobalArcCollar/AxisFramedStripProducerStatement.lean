import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchSquares
import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualEndpointPortSelection
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualCompactStripWidth
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualInternalCollarCalibration
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualFiniteAxisPatches
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualLocalAxisNormalizationProducer
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSurfaceAxisRectangleTransplant
set_option maxHeartbeats 3000000
namespace CurveComplex
open Set Topology Schoenflies

theorem source_finite_axis_framed_arc_strip
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (K : Type) [Fintype K]
    (θ : K → Interval) (hθ : Function.Injective θ)
    (E : K → OpenPartialHomeomorph S Plane)
    (hpE : ∀ k, f (θ k) ∈ (E k).source)
    (hE0 : ∀ k, E k (f (θ k)) = 0)
    (haxis : ∀ k u, f u ∈ (E k).source → E k (f u) 1 = 0)
    (U : Set S) (hU : IsOpen U) (hfU : Set.range f ⊆ U) :
    ∃ N : Interval × Set.Icc (-1:ℝ) 1 → S,
      IsEmbedding N ∧ Set.range N ⊆ U ∧
      (∀ u, N (u,⟨0,by norm_num⟩) = f u) ∧
      ∃ σ δ η : K → ℝ,
        (∀ k, σ k = -1 ∨ σ k = 1) ∧
        (∀ k, 0 < δ k ∧ 0 < η k) ∧
        ∀ k (u : Interval) (w : Set.Icc (-1:ℝ) 1),
          |(u:ℝ)-(θ k:ℝ)| < η k →
          N (u,w) ∈ (E k).source ∧
          E k (N (u,w)) = Plane.mk (E k (f u) 0) (σ k*δ k*(w:ℝ)) := by
  classical
  obtain ⟨N₀,hN₀,hcenter₀,hN₀U⟩ := source_whole_embedded_arc_strip f hf U hU hfU
  obtain ⟨ηpatch,δpatch,hpatchpos,Bpatch,hBpatch,hBpatchU,hBpatchcenter,
    hBpatchcoords,hBpatchavoid,hBpatchdis⟩ :=
    source_finite_actual_axis_patches f hf θ hθ E hpE haxis U hU hfU
  let Framed (A : Finset K) : Prop :=
    ∃ N : Interval × Set.Icc (-1:ℝ) 1 → S,
      IsEmbedding N ∧ Set.range N ⊆ U ∧
      (∀ u, N (u,⟨0,by norm_num⟩) = f u) ∧
      ∃ σ δ η : K → ℝ,
        (∀ k ∈ A, σ k = -1 ∨ σ k = 1) ∧
        (∀ k ∈ A, 0 < δ k ∧ 0 < η k) ∧
        ∀ k ∈ A, ∀ (u : Interval) (w : Set.Icc (-1:ℝ) 1),
          |(u:ℝ)-(θ k:ℝ)| < η k →
          N (u,w) ∈ (E k).source ∧
          E k (N (u,w)) = Plane.mk (E k (f u) 0) (σ k*δ k*(w:ℝ))
  have hfinite : ∀ A : Finset K, Framed A := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      exact ⟨N₀,hN₀,hN₀U,hcenter₀,fun _ => 1,fun _ => 1,fun _ => 1,
        by simp,by simp,by simp⟩
    | @insert k A hk hA =>
      obtain ⟨N,hN,hNU,hcenter,σold,δold,ηold,holdsign,holdpos,holdcoords⟩ := hA
      by_cases hint : 0 < (θ k:ℝ) ∧ (θ k:ℝ) < 1
      · let d : ℝ := min (ηpatch k / 2) (min ((θ k:ℝ)/2) ((1-(θ k:ℝ))/2))
        have hd : 0 < d := lt_min (half_pos (hpatchpos k).1)
          (lt_min (by linarith [hint.1]) (by linarith [hint.2]))
        have hdη : d ≤ ηpatch k / 2 := min_le_left _ _
        have hdt : d ≤ (θ k:ℝ)/2 := (min_le_right _ _).trans (min_le_left _ _)
        have hd1 : d ≤ (1-(θ k:ℝ))/2 := (min_le_right _ _).trans (min_le_right _ _)
        let a : Interval := ⟨(θ k:ℝ)-d,by constructor <;> linarith [hint.2]⟩
        let b : Interval := ⟨(θ k:ℝ)+d,by constructor <;> linarith [hint.1]⟩
        have hab : (a:ℝ) < b := by dsimp [a,b]; linarith
        obtain ⟨q,hq,hq0,hq1,hqrange,hqval⟩ := source_affine_subinterval a b hab
        let p : C(Interval,S) := f.comp q
        have hp : IsEmbedding p := hf.comp hq
        have hps : Set.range p ⊆ (E k).source := by
          rintro x ⟨t,rfl⟩
          have hqt : q t ∈ Set.Icc a b := hqrange ▸ Set.mem_range_self t
          have hdqt : dist (q t) (θ k) ≤ ηpatch k := by
            rw [Subtype.dist_eq,Real.dist_eq]
            apply abs_le.mpr
            change (θ k:ℝ)-d ≤ (q t:ℝ) ∧ (q t:ℝ) ≤ (θ k:ℝ)+d at hqt
            constructor <;> linarith [(hpatchpos k).1]
          have hh := (hBpatchU k (Set.mem_range_self
            (⟨q t,hdqt⟩,⟨0,by norm_num⟩))).2
          rw [hBpatchcenter] at hh
          exact hh
        have hpaxis : ∀ t, E k (p t) 1 = 0 := fun t => haxis k (q t) (hps (Set.mem_range_self t))
        let mid : Interval := ⟨1/2,by constructor <;> norm_num⟩
        have hqmid : q mid = θ k := by
          apply Subtype.ext
          rw [hqval]
          dsimp [a,b,mid]
          ring
        have hpmid : E k (p mid) 0 = 0 := by
          change E k (f (q mid)) 0 = 0
          rw [hqmid,hE0]
          rfl
        -- Actual compact supports for previously framed windows, avoided by
        -- a selected new chart square BEFORE choosing the normalized radius.
        let ηkeep : K → ℝ := fun i => min (ηold i / 2) (dist (θ i) (θ k) / 2)
        have hηkeep : ∀ i ∈ A, 0 < ηkeep i ∧ ηkeep i ≤ ηold i := by
          intro i hi
          have hik : i ≠ k := by intro he; exact hk (he ▸ hi)
          have hdist : 0 < dist (θ i) (θ k) := dist_pos.mpr (fun he => hik (hθ he))
          refine ⟨lt_min (half_pos (holdpos i hi).2) (half_pos hdist),?_⟩
          have hh := min_le_left (ηold i / 2) (dist (θ i) (θ k) / 2)
          dsimp [ηkeep]
          linarith [(holdpos i hi).2]
        let C : Set S := ⋃ i : ↥A,
          N '' (Metric.closedBall (θ i.val) (ηkeep i.val) ×ˢ
            (Set.univ : Set (Set.Icc (-1:ℝ) 1)))
        have hCc : IsCompact C := isCompact_iUnion (fun i =>
          ((isCompact_closedBall _ _).prod isCompact_univ).image hN.continuous)
        have hnotC : f (θ k) ∉ C := by
          intro hx
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
          obtain ⟨z,hz,he⟩ := hi
          have hzEq : z = (θ k,⟨0,by norm_num⟩) :=
            hN.injective (he.trans (hcenter (θ k)).symm)
          have hdclosed := hz.1
          rw [hzEq] at hdclosed
          have hdle : dist (θ k) (θ i.val) ≤ ηkeep i.val := hdclosed
          have hdpos : 0 < dist (θ i.val) (θ k) := by
            apply dist_pos.mpr
            intro heq
            exact hk (hθ heq ▸ i.property)
          have hdhalf := min_le_right (ηold i.val / 2) (dist (θ i.val) (θ k) / 2)
          change dist (θ k) (θ i.val) ≤ min (ηold i.val / 2) (dist (θ i.val) (θ k) / 2) at hdle
          rw [dist_comm] at hdle
          linarith
        let V : Set S := U \ C
        have hVo : IsOpen V := hU.sdiff hCc.isClosed
        have hpointV : f (θ k) ∈ V := ⟨hfU (Set.mem_range_self _),hnotC⟩
        have hplaneOpen : IsOpen ((E k) '' ((E k).source ∩ V)) :=
          (E k).isOpen_image_source_inter hVo
        have hplaneZero : (0:Plane) ∈ (E k) '' ((E k).source ∩ V) :=
          ⟨f (θ k),⟨hpE k,hpointV⟩,hE0 k⟩
        obtain ⟨s,hs,hs1,hsmall⟩ := Plane.exists_openSquare_subset hplaneOpen hplaneZero (by norm_num : (0:ℝ)<1)
        let ε : ℝ := s/4
        have hε : 0 < ε := by dsimp [ε]; positivity
        have hsupport : Plane.closedSquare 0 (2*ε) ⊆ (E k) '' ((E k).source ∩ V) := by
          intro z hz
          apply hsmall
          change Plane.supDist z 0 < s
          have hz' : Plane.supDist z 0 ≤ 2*ε := hz
          dsimp [ε] at hz'
          linarith
        obtain ⟨r,hr,hr1,j,J,hj,hJ,hjcoords,hJcoords⟩ :=
          source_local_axis_normalization p hp (E k) hps hpaxis mid
            (by norm_num [mid]) (by norm_num [mid]) hpmid ε hε
        -- ACTUAL INTERNAL EXTRACTION: construct the normalized old-collar
        -- rectangle and its small chart support. Nothing below is an input
        -- premise of the original theorem.
        have hextract :
            ∃ ρ : ℝ, ∃ hρ : 0 < ρ ∧ ρ ≤ 1,
            ∃ e : OpenPartialHomeomorph S Plane,
            ∃ B : ↥(Plane.closedSquare 0 1) → S,
              Plane.closedSquare 0 2 ⊆ e.target ∧
              (∀ x ∈ e.source, x ∈ U ∧ x ∈ (E k).source ∧
                e x = (1/r) • E k x) ∧
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
                (fun t : Set.Icc (-1:ℝ) 1 => Plane.mk t 0) '' Set.univ) ∧
              ∃ ηkeep : K → ℝ,
                (∀ i ∈ A, 0 < ηkeep i ∧ ηkeep i ≤ ηold i) ∧
                ∀ i ∈ A, ∀ (u : Interval) (w : Set.Icc (-1:ℝ) 1),
                  |(u:ℝ)-(θ i:ℝ)| < ηkeep i →
                  N (u,w) ∉ e.source ∩ e ⁻¹' Plane.openSquare 0 2 := by
          let scale : Plane ≃ₜ Plane := {
            toFun := fun z => (1/r) • z
            invFun := fun z => r • z
            left_inv := by intro z; simp [smul_smul,hr.ne']
            right_inv := by intro z; simp [smul_smul,hr.ne']
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop
          }
          let e := ((E k).restr V).transHomeomorph scale
          have heSource : e.source = (E k).source ∩ V := by
            simp only [e,OpenPartialHomeomorph.transHomeomorph_source,
              (E k).restr_source' V hVo]
          have heFun (x : S) : e x = (1/r) • E k x := rfl
          have heOriginal : ∀ x ∈ e.source, x ∈ U ∧ x ∈ (E k).source ∧
              e x = (1/r) • E k x := by
            intro x hx
            rw [heSource] at hx
            exact ⟨hx.2.1,hx.1,heFun x⟩
          have hrSupport : Plane.closedSquare 0 (2*r) ⊆
              (E k) '' ((E k).source ∩ V) := by
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
            change (1/r)*E k (f u) 1 = 0
            rw [haxis k u (heOriginal _ hu).2.1,mul_zero]
          let W := Set.Icc (-1:ℝ) 1
          letI : CompactSpace W := isCompact_iff_compactSpace.mp isCompact_Icc
          let raw : W × W → S := fun z => N (q (j z.1),z.2)
          have hrawc : Continuous raw := hN.continuous.comp
            ((q.continuous.comp (j.continuous.comp continuous_fst)).prodMk continuous_snd)
          let Oambient : Set S := e.source ∩
            ((E k).source ∩ (E k) ⁻¹' {z : Plane | |z 0| < 2*r})
          have hOambient : IsOpen Oambient := e.open_source.inter
            ((E k).isOpen_inter_preimage (isOpen_lt (by fun_prop) continuous_const))
          have hrawCenter : ∀ x : W, raw (x,⟨0,by norm_num [W]⟩) ∈ Oambient := by
            intro x
            have hcoords := hjcoords x
            have hsource := hps (Set.mem_range_self (j x))
            have hsmallCenter : E k (p (j x)) ∈ Plane.closedSquare 0 (2*r) := by
              rw [hcoords]
              simp only [Plane.closedSquare,Plane.supDist,Plane.supNorm,sub_zero,Set.mem_setOf_eq,Plane.mk]
              change max |r*(x:ℝ)| |(0:ℝ)| ≤ 2*r
              rw [abs_mul,abs_of_pos hr,abs_zero]
              exact max_le (by nlinarith [abs_le.mpr x.property]) (by positivity)
            obtain ⟨y,hy,hEy⟩ := hrSupport hsmallCenter
            have heq : y = p (j x) := (E k).injOn hy.1 hsource hEy
            have hV : p (j x) ∈ V := heq ▸ hy.2
            change N (q (j x),⟨0,by norm_num [W]⟩) ∈ Oambient
            rw [hcenter]
            refine ⟨heSource ▸ ⟨hsource,hV⟩,hsource,?_⟩
            have hh := congrArg (fun z : Plane => z 0) hcoords
            change E k (f (q (j x))) 0 = r*(x:ℝ) at hh
            change |E k (f (q (j x))) 0| < 2*r
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
            change (1/r) • E k (p (j t)) = _
            rw [hjcoords]
            apply PiLp.ext
            intro i
            fin_cases i <;> simp [Plane.mk,smul_eq_mul,hr.ne']
          have hrecognize : ∀ z, e (B z) 1 = 0 → z.val 1 = 0 := by
            intro z hz
            have hcoordZero : E k (B z) 1 = 0 := by
              rw [heFun] at hz
              change (1/r)*E k (B z) 1 = 0 at hz
              exact (mul_eq_zero.mp hz).resolve_left (one_div_ne_zero hr.ne')
            have hcoordBound : |E k (B z) 0| < 2*r := (hBambient z).2.2
            let x : W := ⟨E k (B z) 0 / (2*r),by
              have hb := abs_lt.mp hcoordBound
              constructor
              · apply (le_div_iff₀ (by positivity : (0:ℝ)<2*r)).mpr; linarith [hb.1]
              · apply (div_le_iff₀ (by positivity : (0:ℝ)<2*r)).mpr; linarith [hb.2]⟩
            have haxisEq : E k (B z) = E k (p (J x)) := by
              rw [hJcoords]
              apply PiLp.ext
              intro i
              fin_cases i
              · change E k (B z) 0 = 2*r*(E k (B z) 0/(2*r))
                field_simp [hr.ne']
              · exact hcoordZero
            have heq : B z = p (J x) := (E k).injOn
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
          refine ⟨ρ,hρ,e,B,heTarget,heOriginal,heAxis,hB,hBsource,fun _ => rfl,hBcenter,hBaxis,
            ηkeep,hηkeep,?_⟩
          intro i hi u w hu hs
          have hNUC : N (u,w) ∈ C := by
            apply Set.mem_iUnion.mpr
            refine ⟨⟨i,hi⟩,?_⟩
            refine ⟨(u,w),⟨?_,Set.mem_univ _⟩,rfl⟩
            change dist u (θ i) ≤ ηkeep i
            rw [Subtype.dist_eq,Real.dist_eq]
            exact hu.le
          have hxSource : N (u,w) ∈ (E k).source ∩ V := heSource ▸ hs.1
          exact hxSource.2.2 hNUC
        obtain ⟨ρ,hρ,e,B,heTarget,heOriginal,heAxis,hB,hBsource,hBformula,
          hBcenter,hBaxis,ηretained,hηretained,hprotected⟩ := hextract
        obtain ⟨τ,hτ,sgn,F,hsgn,hFcenter,hFfix,hFcoords⟩ :=
          source_surface_axis_rectangle_transplant e heTarget f heAxis B hB
            hBsource hBcenter hBaxis
        -- ACTUAL INVERSE COVERAGE: θ k is internal to the selected r-axis
        -- segment. The compact inverse exists already; its image must contain
        -- an actual parameter neighborhood of θ k.
        have hcoverage : ∃ ηnew : ℝ, 0 < ηnew ∧
            ∀ u : Interval, |(u:ℝ)-(θ k:ℝ)| < ηnew →
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
          have hvzero : v zero = θ k := by
            apply hf.injective
            apply (E k).injOn (hps (Set.mem_range_self (j zero))) (hpE k)
            rw [hE0]
            have hh := hjcoords zero
            have hzero : Plane.mk (r*(zero:ℝ)) 0 = (0:Plane) := by
              apply PiLp.ext
              intro i
              fin_cases i <;> simp [Plane.mk,zero]
            exact hh.trans hzero
          have select (l r : Set.Icc (-1:ℝ) 1)
              (hl : (v l:ℝ) < (θ k:ℝ)) (hr : (θ k:ℝ) < (v r:ℝ)) :
              ∃ ηnew : ℝ, 0 < ηnew ∧
                ∀ u : Interval, |(u:ℝ)-(θ k:ℝ)| < ηnew →
                  ∃ x : Set.Icc (-1:ℝ) 1, q (j x) = u := by
            let e := min ((θ k:ℝ)-(v l:ℝ)) ((v r:ℝ)-(θ k:ℝ))/2
            have he : 0 < e := by dsimp [e]; positivity
            have hel := min_le_left ((θ k:ℝ)-(v l:ℝ)) ((v r:ℝ)-(θ k:ℝ))
            have her := min_le_right ((θ k:ℝ)-(v l:ℝ)) ((v r:ℝ)-(θ k:ℝ))
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
            |(u:ℝ)-(θ k:ℝ)| < ηnew →
            M (u,w) ∈ (E k).source ∧
            E k (M (u,w)) = Plane.mk (E k (f u) 0) (sgn*r*(w:ℝ)) := by
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
          have hplane : (1/r) • E k (M (u,w)) = Plane.mk (x:ℝ) (sgn*(w:ℝ)) :=
            horig.2.2.symm.trans hFz.2
          have hcenterx : E k (f u) 0 = r*(x:ℝ) := by
            have hh := congrArg (fun v : Plane => v 0) (hjcoords x)
            change E k (f (q (j x))) 0 = r*(x:ℝ) at hh
            rwa [hxu] at hh
          apply PiLp.ext
          intro i
          fin_cases i
          · have hh := congrArg (fun v : Plane => v 0) hplane
            change (1/r)*E k (M (u,w)) 0 = (x:ℝ) at hh
            change E k (M (u,w)) 0 = E k (f u) 0
            rw [hcenterx]
            field_simp at hh
            nlinarith
          · have hh := congrArg (fun v : Plane => v 1) hplane
            change (1/r)*E k (M (u,w)) 1 = sgn*(w:ℝ) at hh
            change E k (M (u,w)) 1 = sgn*r*(w:ℝ)
            field_simp at hh
            nlinarith
        let σnew : K → ℝ := Function.update σold k sgn
        let δnew : K → ℝ := Function.update (fun i => δold i * widthFactor) k r
        let ηnext : K → ℝ := Function.update ηretained k ηnew
        refine ⟨M,hM,hMU,hMcenter,σnew,δnew,ηnext,?_,?_,?_⟩
        · intro i hi
          by_cases hik : i = k
          · subst i
            simpa [σnew] using hsgn
          · have hiA : i ∈ A := (Finset.mem_insert.mp hi).resolve_left hik
            simpa [σnew,Function.update_of_ne hik] using holdsign i hiA
        · intro i hi
          by_cases hik : i = k
          · subst i
            simpa [δnew,ηnext] using (show 0 < r ∧ 0 < ηnew from ⟨hr,hηnew⟩)
          · have hiA : i ∈ A := (Finset.mem_insert.mp hi).resolve_left hik
            simpa [δnew,ηnext,Function.update_of_ne hik] using
              (show 0 < δold i*widthFactor ∧ 0 < ηretained i from
                ⟨mul_pos (holdpos i hiA).1 hwidthFactor.1,(hηretained i hiA).1⟩)
        · intro i hi u w hu
          by_cases hik : i = k
          · subst i
            simpa [σnew,δnew,ηnext] using hMnew u w (by simpa [ηnext] using hu)
          · have hiA : i ∈ A := (Finset.mem_insert.mp hi).resolve_left hik
            have hη : |(u:ℝ)-(θ i:ℝ)| < ηretained i := by
              simpa [ηnext,Function.update_of_ne hik] using hu
            have hno := hprotected i hiA u (narrow (u,w)).2 hη
            have hfixed := hFfix (N (narrow (u,w))) hno
            have hcoords := holdcoords i hiA u (narrow (u,w)).2
              (hη.trans_le (hηretained i hiA).2)
            change M (u,w) ∈ (E i).source ∧ _
            have hMeq : M (u,w) = N (narrow (u,w)) := hfixed
            rw [hMeq]
            refine ⟨hcoords.1,?_⟩
            rw [hcoords.2]
            apply congrArg (Plane.mk (E i (f u) 0))
            simp only [σnew,δnew,Function.update_of_ne hik]
            change σold i*δold i*(widthFactor*(w:ℝ)) = σold i*(δold i*widthFactor)*(w:ℝ)
            ring
      · -- OPEN ENDPOINT SPLICE: use Bpatch k at an internal seam of its
        -- parameter window, retain the old framed patches after narrowing.
        have hend : θ k = 0 ∨ θ k = 1 := by
          by_cases h0 : (θ k:ℝ) = 0
          · exact Or.inl (Subtype.ext h0)
          · have hpos : 0 < (θ k:ℝ) := lt_of_le_of_ne (θ k).property.1 (Ne.symm h0)
            have h1 : (θ k:ℝ) = 1 := by
              have hn : ¬ (θ k:ℝ) < 1 := fun h => hint ⟨hpos,h⟩
              exact le_antisymm (θ k).property.2 (le_of_not_gt hn)
            exact Or.inr (Subtype.ext h1)
        -- Orient the original endpoint to parameter 0, including θ k=1.
        let rev : Interval ≃ₜ Interval := if θ k = 0 then Homeomorph.refl _ else unitInterval.symmHomeomorph
        have hrev0 : rev 0 = θ k := by
          dsimp [rev]
          split_ifs with h0
          · exact h0.symm
          · have h1 := hend.resolve_left h0
            rw [h1]
            apply Subtype.ext
            norm_num [unitInterval.symmHomeomorph,unitInterval.symm]
        have hrevrev : ∀ u, rev (rev u) = u := by
          intro u
          dsimp [rev]
          split_ifs
          · rfl
          · exact unitInterval.symm_symm u
        let fR : C(Interval,S) := ⟨f ∘ rev,f.continuous.comp rev.continuous⟩
        have hfR : IsEmbedding fR := hf.comp rev.isEmbedding
        let orient : Interval × Set.Icc (-1:ℝ) 1 → Interval × Set.Icc (-1:ℝ) 1 :=
          fun z => (rev z.1,z.2)
        have horientc : Continuous orient :=
          (rev.continuous.comp continuous_fst).prodMk continuous_snd
        have horienti : Function.Injective orient := by
          intro z w he
          apply Prod.ext
          · apply rev.injective
            exact congrArg Prod.fst he
          · simpa only [orient] using congrArg Prod.snd he
        have horiente : IsEmbedding orient := (horientc.isClosedEmbedding horienti).isEmbedding
        let NR : Interval × Set.Icc (-1:ℝ) 1 → S := N ∘ orient
        have hNR : IsEmbedding NR := hN.comp horiente
        have hNRU : Set.range NR ⊆ U := by
          rintro x ⟨z,rfl⟩
          exact hNU (Set.mem_range_self (orient z))
        have hcenterR : ∀ u, NR (u,⟨0,by norm_num⟩) = fR u := fun u => hcenter (rev u)
        have hpR : fR 0 ∈ (E k).source := by
          change f (rev 0) ∈ (E k).source
          rw [hrev0]
          exact hpE k
        have hzeroR : E k (fR 0) = 0 := by change E k (f (rev 0)) = 0; rw [hrev0,hE0]
        let cutoff : ℝ := min (ηpatch k / 2) (1/2)
        have hcutoff : 0 < cutoff ∧ cutoff ≤ 1/2 :=
          ⟨lt_min (half_pos (hpatchpos k).1) (by norm_num),min_le_right _ _⟩
        obtain ⟨seam,hseampos,hseamone,hseamcut,hseamsource,hseamnorm,hseamnonzero⟩ :=
          source_embedded_arc_endpoint_small_port fR hfR (E k) hpR hzeroR
            (cutoff/2) 1 (half_pos hcutoff.1) (by norm_num)
        have hseamBelow : (seam:ℝ) < cutoff := by linarith [hcutoff.1]
        let tailStart : Interval := ⟨cutoff,by constructor; exact hcutoff.1.le; linarith [hcutoff.2]⟩
        let Tail : Set S := NR '' (Set.Icc tailStart 1 ×ˢ
          (Set.univ : Set (Set.Icc (-1:ℝ) 1)))
        have hTail : IsCompact Tail := (isCompact_Icc.prod isCompact_univ).image hNR.continuous
        have hseamTail : fR seam ∉ Tail := by
          rintro ⟨z,hz,he⟩
          have heq := hNR.injective (he.trans (hcenterR seam).symm)
          have hp := congrArg Prod.fst heq
          have hz0 : tailStart ≤ z.1 := hz.1.1
          rw [hp] at hz0
          change cutoff ≤ (seam:ℝ) at hz0
          linarith
        let Vcap : Set S := U \ Tail
        have hVcap : IsOpen Vcap := hU.sdiff hTail.isClosed
        have hseamV : fR seam ∈ Vcap :=
          ⟨hNRU (by rw [← hcenterR seam]; exact Set.mem_range_self _),hseamTail⟩
        let shift : Plane ≃ₜ Plane := {
          toFun := fun z => z - E k (fR seam)
          invFun := fun z => z + E k (fR seam)
          left_inv := by intro z; simp
          right_inv := by intro z; simp
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop
        }
        let D := (E k).transHomeomorph shift
        have hDsource : D.source = (E k).source := rfl
        have hDseam : D (fR seam) = 0 := sub_self _
        have hDaxis : ∀ u, fR u ∈ D.source → D (fR u) 1 = 0 := by
          intro u hu
          change E k (f (rev u)) 1 - E k (f (rev seam)) 1 = 0
          rw [haxis k (rev u) hu,haxis k (rev seam) hseamsource,sub_self]
        obtain ⟨factor,hfactor,sgn,height,radius,F,hsgn,hheight,hradius,
          hFcenter,hFoutside,hFformula⟩ :=
          source_internal_collar_calibration fR hfR NR hNR hcenterR seam
            ⟨hseampos,hseamone⟩ D hseamsource hDseam hDaxis U Vcap
            hU hVcap Set.sdiff_subset hseamV hNRU
        let shrink : Interval × Set.Icc (-1:ℝ) 1 → Interval × Set.Icc (-1:ℝ) 1 :=
          fun z => (z.1,⟨factor*(z.2:ℝ),by
            constructor <;> nlinarith [z.2.property.1,z.2.property.2,hfactor.1,hfactor.2]⟩)
        let Cal : Interval × Set.Icc (-1:ℝ) 1 → S := F ∘ NR ∘ shrink
        have hCalc : Continuous Cal := by
          apply F.continuous.comp
          apply hNR.continuous.comp
          dsimp [shrink]
          fun_prop
        have hCali : Function.Injective Cal := by
          intro z w he
          have hh := hNR.injective (F.injective he)
          apply Prod.ext
          · simpa only [shrink] using congrArg Prod.fst hh
          · apply Subtype.ext
            exact mul_left_cancel₀ hfactor.1.ne' (congrArg (fun z => (z.2:ℝ)) hh)
        have hCal : IsEmbedding Cal := (hCalc.isClosedEmbedding hCali).isEmbedding
        have hCalcenter : ∀ u, Cal (u,⟨0,by norm_num⟩) = fR u := by
          intro u
          change F (NR (u,⟨factor*0,_⟩)) = _
          have he : (⟨factor*0,by constructor <;> norm_num⟩ : Set.Icc (-1:ℝ) 1) = ⟨0,by norm_num⟩ := Subtype.ext (mul_zero _)
          rw [he,hcenterR,hFcenter]
        have hCalTail : ∀ (u : Interval) (w : Set.Icc (-1:ℝ) 1), cutoff ≤ (u:ℝ) →
            Cal (u,w) = NR (shrink (u,w)) := by
          intro u w hu
          apply hFoutside
          intro hV
          apply hV.2
          exact ⟨shrink (u,w),⟨⟨hu,u.property.2⟩,Set.mem_univ _⟩,rfl⟩
        have hCalcoords : ∀ (u : Interval) (w : Set.Icc (-1:ℝ) 1),
            |(u:ℝ)-(seam:ℝ)| < radius →
            Cal (u,w) ∈ (E k).source ∧
            E k (Cal (u,w)) = Plane.mk (E k (fR u) 0) (sgn*height*(w:ℝ)) := by
          intro u w hu
          obtain ⟨hs,hc⟩ := hFformula u w hu
          refine ⟨hs,?_⟩
          change E k (Cal (u,w)) - E k (fR seam) =
            Plane.mk (E k (fR u) 0 - E k (fR seam) 0) (sgn*height*(w:ℝ)) at hc
          apply PiLp.ext
          intro i
          fin_cases i
          · have hh := congrArg (fun z : Plane => z 0) hc
            change E k (Cal (u,w)) 0 - E k (fR seam) 0 =
              E k (fR u) 0 - E k (fR seam) 0 at hh
            exact sub_left_injective hh
          · have hh := congrArg (fun z : Plane => z 1) hc
            change E k (Cal (u,w)) 1 - E k (fR seam) 1 = sgn*height*(w:ℝ) at hh
            have hzero : E k (fR seam) 1 = 0 := haxis k (rev seam) hseamsource
            rw [hzero,sub_zero] at hh
            exact hh
        have hseamPatch : rev seam ∈ Metric.closedBall (θ k) (ηpatch k) := by
          change dist (rev seam) (θ k) ≤ ηpatch k
          rw [← hrev0]
          dsimp [rev]
          split_ifs with hz
          · rw [Subtype.dist_eq,Real.dist_eq]
            change |(seam:ℝ)-0| ≤ ηpatch k
            rw [sub_zero,abs_of_pos hseampos]
            have hc := min_le_left (ηpatch k / 2) (1/2)
            dsimp [cutoff] at hseamBelow
            linarith
          · rw [Subtype.dist_eq,Real.dist_eq]
            change |(1-(seam:ℝ))-(1-0)| ≤ ηpatch k
            have hc := min_le_left (ηpatch k / 2) (1/2)
            dsimp [cutoff] at hseamBelow
            rw [show (1-(seam:ℝ))-(1-0) = -(seam:ℝ) by ring,abs_neg,abs_of_pos hseampos]
            linarith
        let extra : ℝ := min (1/2) (δpatch k / (2*height))
        have hextra : 0 < extra ∧ extra ≤ 1 := by
          refine ⟨lt_min (by norm_num) (div_pos (hpatchpos k).2 (by positivity)),?_⟩
          exact (min_le_left _ _).trans (by norm_num)
        have hextraBound : height*extra ≤ δpatch k := by
          have he := min_le_right (1/2:ℝ) (δpatch k/(2*height))
          have hh := (le_div_iff₀ (show 0 < 2*height by positivity)).mp he
          dsimp [extra]
          nlinarith
        let narrowExtra (w : Set.Icc (-1:ℝ) 1) : Set.Icc (-1:ℝ) 1 :=
          ⟨extra*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hextra.1,hextra.2]⟩
        let patchWidth (w : Set.Icc (-1:ℝ) 1) : Set.Icc (-1:ℝ) 1 :=
          ⟨sgn*height*extra*(w:ℝ)/δpatch k,by
            have h0 : 0 ≤ height*extra := mul_nonneg hheight.le hextra.1.le
            have hwlo := mul_le_mul_of_nonneg_left w.property.1 h0
            have hwhi := mul_le_mul_of_nonneg_left w.property.2 h0
            constructor
            · apply (le_div_iff₀ (hpatchpos k).2).2
              rcases hsgn with hs|hs <;> rw [hs] <;>
                nlinarith [hwlo,hwhi,hextraBound]
            · apply (div_le_iff₀ (hpatchpos k).2).2
              rcases hsgn with hs|hs <;> rw [hs] <;>
                nlinarith [hwlo,hwhi,hextraBound]⟩
        have hmatchedSeam : ∀ w : Set.Icc (-1:ℝ) 1,
            Bpatch k (⟨rev seam,hseamPatch⟩,patchWidth w) = Cal (seam,narrowExtra w) := by
          intro w
          obtain ⟨hm,hc⟩ := hCalcoords seam (narrowExtra w) (by simp [hradius])
          apply (E k).injOn ((hBpatchU k (Set.mem_range_self _)).2) hm
          rw [hBpatchcoords,hc]
          apply congrArg (Plane.mk (E k (fR seam) 0))
          change δpatch k*(sgn*height*extra*(w:ℝ)/δpatch k) = sgn*height*(extra*(w:ℝ))
          field_simp [(hpatchpos k).2.ne']
          <;> ring
        have hnearMeeting
            (u : ↥(Metric.closedBall (θ k) (ηpatch k))) (v : Interval)
            (w w' : Set.Icc (-1:ℝ) 1) (hv : |(v:ℝ)-(seam:ℝ)| < radius)
            (he : Bpatch k (u,w) = Cal (v,w')) : (u:Interval) = rev v := by
          obtain ⟨hvsource,hvcoords⟩ := hCalcoords v w' hv
          have hx := congrArg (fun z : Plane => z 0) (congrArg (E k) he)
          rw [hBpatchcoords,hvcoords] at hx
          have husource : f (u:Interval) ∈ (E k).source := by
            have hh := (hBpatchU k (Set.mem_range_self (u,⟨0,by norm_num⟩))).2
            rw [hBpatchcenter] at hh
            exact hh
          have hvcentersource : fR v ∈ (E k).source := by
            have hh := (hCalcoords v ⟨0,by norm_num⟩ hv).1
            rw [hCalcenter] at hh
            exact hh
          apply hf.injective
          apply (E k).injOn husource hvcentersource
          apply PiLp.ext
          intro i
          fin_cases i
          · exact hx
          · change E k (f (u:Interval)) 1 = E k (f (rev v)) 1
            exact (haxis k u husource).trans (haxis k (rev v) hvcentersource).symm
        have hrevDist (u : Interval) : dist (rev u) (θ k) = (u:ℝ) := by
          rw [← hrev0]
          dsimp [rev]
          split_ifs
          · rw [Subtype.dist_eq,Real.dist_eq]
            change |(u:ℝ)-0| = (u:ℝ)
            simpa only [sub_zero] using abs_of_nonneg u.property.1
          · rw [Subtype.dist_eq,Real.dist_eq]
            change |(1-(u:ℝ))-(1-0)| = (u:ℝ)
            rw [show (1-(u:ℝ))-(1-0) = -(u:ℝ) by ring,abs_neg]
            exact abs_of_nonneg u.property.1
        let clipPrefix : C(Interval,Interval) := ⟨fun u =>
          ⟨min (u:ℝ) (seam:ℝ),le_min u.property.1 seam.property.1,
            (min_le_left _ _).trans u.property.2⟩,by fun_prop⟩
        have hclipPrefix (u : Interval) (hu : u ≤ seam) : clipPrefix u = u := by
          apply Subtype.ext
          exact min_eq_left hu
        let prefixParameter (u : Interval) : ↥(Metric.closedBall (θ k) (ηpatch k)) :=
          ⟨rev (clipPrefix u),by
            change dist (rev (clipPrefix u)) (θ k) ≤ ηpatch k
            rw [hrevDist]
            exact (min_le_right _ _).trans (by
              have hc := min_le_left (ηpatch k / 2) (1/2)
              dsimp [cutoff] at hseamBelow
              linarith)⟩
        have hprefixParameter : Continuous prefixParameter := by
          apply Continuous.subtype_mk
          exact rev.continuous.comp clipPrefix.continuous
        have hpatchWidth : Continuous patchWidth := by dsimp [patchWidth]; fun_prop
        let P : Interval × Set.Icc (-1:ℝ) 1 → S :=
          fun z => Bpatch k (prefixParameter z.1,patchWidth z.2)
        have hP : Continuous P := (hBpatch k).continuous.comp
          ((hprefixParameter.comp continuous_fst).prodMk (hpatchWidth.comp continuous_snd))
        have hPcenter (u : Interval) : P (u,⟨0,by norm_num⟩) = fR (clipPrefix u) := by
          change Bpatch k (prefixParameter u,patchWidth ⟨0,by norm_num⟩) = _
          have hw : patchWidth ⟨0,by norm_num⟩ = ⟨0,by norm_num⟩ := by
            apply Subtype.ext
            dsimp [patchWidth]
            ring
          rw [hw,hBpatchcenter]
          rfl
        let gap : ℝ := min ((1-(seam:ℝ))/2) (radius/2)
        have hgap : 0 < gap ∧ gap < 1-(seam:ℝ) ∧ gap < radius := by
          refine ⟨lt_min (by linarith) (half_pos hradius),?_,?_⟩
          · exact (min_le_left _ _).trans_lt (by linarith)
          · exact (min_le_right _ _).trans_lt (half_lt_self hradius)
        let farStart : Interval := ⟨(seam:ℝ)+gap,by constructor; linarith [seam.property.1,hgap.1]; linarith [hgap.2.1]⟩
        let Cleft : Set S := fR '' Set.Icc 0 seam
        let Cfar : Set S := fR '' Set.Icc farStart 1
        have hCleft : IsCompact Cleft := isCompact_Icc.image fR.continuous
        have hCfar : IsCompact Cfar := isCompact_Icc.image fR.continuous
        have hCdis : Disjoint Cleft Cfar := by
          apply Set.disjoint_left.mpr
          rintro x ⟨u,hu,he⟩ ⟨v,hv,he'⟩
          have huv := hfR.injective (he.trans he'.symm)
          subst v
          have h1 : (u:ℝ) ≤ (seam:ℝ) := hu.2
          have h2 : (seam:ℝ)+gap ≤ (u:ℝ) := hv.1
          linarith [hgap.1]
        obtain ⟨Vleft,Vfar,hVleft,hVfar,hleft,hfar,hVdis⟩ :=
          SeparatedNhds.of_isCompact_isCompact hCleft hCfar hCdis
        have hPleft (u : Interval) : P (u,⟨0,by norm_num⟩) ∈ Vleft := by
          rw [hPcenter]
          exact hleft ⟨clipPrefix u,⟨(clipPrefix u).property.1,min_le_right _ _⟩,rfl⟩
        let clipFar : C(Interval,Interval) := ⟨fun u =>
          ⟨max (u:ℝ) (farStart:ℝ),(u.property.1.trans (le_max_left _ _)),
            max_le u.property.2 farStart.property.2⟩,by fun_prop⟩
        have hnarrowExtra : Continuous narrowExtra := by dsimp [narrowExtra]; fun_prop
        let T : Interval × Set.Icc (-1:ℝ) 1 → S :=
          fun z => Cal (clipFar z.1,narrowExtra z.2)
        have hT : Continuous T := hCalc.comp
          ((clipFar.continuous.comp continuous_fst).prodMk (hnarrowExtra.comp continuous_snd))
        have hTfar (u : Interval) : T (u,⟨0,by norm_num⟩) ∈ Vfar := by
          change Cal (clipFar u,narrowExtra ⟨0,by norm_num⟩) ∈ Vfar
          have hw : narrowExtra ⟨0,by norm_num⟩ = ⟨0,by norm_num⟩ := Subtype.ext (mul_zero _)
          rw [hw,hCalcenter]
          exact hfar ⟨clipFar u,⟨le_max_right _ _,(clipFar u).property.2⟩,rfl⟩
        obtain ⟨ρL,hρL,hρLeft⟩ := source_continuous_strip_uniform_width P hP Vleft hVleft hPleft
        obtain ⟨ρR,hρR,hρFar⟩ := source_continuous_strip_uniform_width T hT Vfar hVfar hTfar
        let β : ℝ := ρL*ρR
        have hβ : 0 < β ∧ β ≤ 1 := ⟨mul_pos hρL.1 hρR.1,
          (mul_le_mul_of_nonneg_right hρL.2 hρR.1.le).trans (by simpa using hρR.2)⟩
        let narrowβ (w : Set.Icc (-1:ℝ) 1) : Set.Icc (-1:ℝ) 1 :=
          ⟨β*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hβ.1,hβ.2]⟩
        have hPβ (u : Interval) (w : Set.Icc (-1:ℝ) 1) : P (u,narrowβ w) ∈ Vleft := by
          have hh := hρLeft u ⟨ρR*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hρR.1,hρR.2]⟩
          convert hh using 1
          apply congrArg (fun w => P (u,w))
          apply Subtype.ext
          dsimp [narrowβ,β]
          ring
        have hTβ (u : Interval) (w : Set.Icc (-1:ℝ) 1) : T (u,narrowβ w) ∈ Vfar := by
          have hh := hρFar u ⟨ρL*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hρL.1,hρL.2]⟩
          convert hh using 1
          apply congrArg (fun w => T (u,w))
          apply Subtype.ext
          dsimp [narrowβ,β]
          ring
        have hfarNoMeeting (u v : Interval) (w w' : Set.Icc (-1:ℝ) 1)
            (hv : farStart ≤ v) : P (u,narrowβ w) ≠ Cal (v,narrowExtra (narrowβ w')) := by
          intro he
          have hclip : clipFar v = v := Subtype.ext (max_eq_left hv)
          have hh := hTβ v w'
          change Cal (clipFar v,narrowExtra (narrowβ w')) ∈ Vfar at hh
          rw [hclip,← he] at hh
          exact Set.disjoint_left.mp hVdis (hPβ u w) hh
        have hnarrowβ : Continuous narrowβ := by dsimp [narrowβ]; fun_prop
        have hnarrowβi : Function.Injective narrowβ := by
          intro w w' he
          apply Subtype.ext
          exact mul_left_cancel₀ hβ.1.ne' (congrArg Subtype.val he)
        have hextrai : Function.Injective narrowExtra := by
          intro w w' he
          apply Subtype.ext
          exact mul_left_cancel₀ hextra.1.ne' (congrArg Subtype.val he)
        have hsgnne : sgn ≠ 0 := by rcases hsgn with h|h <;> rw [h] <;> norm_num
        have hpatchWidthi : Function.Injective patchWidth := by
          intro w w' he
          apply Subtype.ext
          have hh := (div_left_inj' (hpatchpos k).2.ne').mp (congrArg Subtype.val he)
          exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hsgnne hheight.ne') hextra.1.ne') hh
        have hcross (u v : Interval) (w w' : Set.Icc (-1:ℝ) 1)
            (hu : u ≤ seam) (hv : seam < v) :
            P (u,narrowβ w) ≠ Cal (v,narrowExtra (narrowβ w')) := by
          by_cases hfarv : farStart ≤ v
          · exact hfarNoMeeting u v w w' hfarv
          · intro he
            have hnear : |(v:ℝ)-(seam:ℝ)| < radius := by
              rw [abs_of_pos (show 0 < (v:ℝ)-(seam:ℝ) by exact sub_pos.mpr hv)]
              have hlt : (v:ℝ) < (seam:ℝ)+gap := lt_of_not_ge hfarv
              linarith [hgap.2.2]
            have hp := hnearMeeting (prefixParameter u) v (patchWidth (narrowβ w))
              (narrowExtra (narrowβ w')) hnear he
            change rev (clipPrefix u) = rev v at hp
            have hh := rev.injective hp
            rw [hclipPrefix u hu] at hh
            exact (not_lt_of_ge hu) (hh ▸ hv)
        let M : Interval × Set.Icc (-1:ℝ) 1 → S := fun z =>
          if z.1 ≤ seam then P (z.1,narrowβ z.2) else Cal (z.1,narrowExtra (narrowβ z.2))
        have hMc : Continuous M := by
          apply Continuous.if_le
            (hP.comp (continuous_fst.prodMk (hnarrowβ.comp continuous_snd)))
            (hCalc.comp (continuous_fst.prodMk (hnarrowExtra.comp (hnarrowβ.comp continuous_snd))))
            continuous_fst continuous_const
          intro z hz
          have hclip : clipPrefix z.1 = seam := by rw [hz]; exact hclipPrefix seam le_rfl
          change Bpatch k (prefixParameter z.1,patchWidth (narrowβ z.2)) = _
          have hp : prefixParameter z.1 = ⟨rev seam,hseamPatch⟩ := Subtype.ext (congrArg rev hclip)
          change Bpatch k (prefixParameter z.1,patchWidth (narrowβ z.2)) = Cal (z.1,narrowExtra (narrowβ z.2))
          rw [hp,hz]
          exact hmatchedSeam (narrowβ z.2)
        have hMi : Function.Injective M := by
          intro z z' he
          by_cases hz : z.1 ≤ seam <;> by_cases hz' : z'.1 ≤ seam
          · simp only [M,if_pos hz,if_pos hz'] at he
            have hh := (hBpatch k).injective he
            apply Prod.ext
            · have hp := congrArg (fun z => (z.1:Interval)) hh
              change rev (clipPrefix z.1) = rev (clipPrefix z'.1) at hp
              have hp' := rev.injective hp
              rwa [hclipPrefix z.1 hz,hclipPrefix z'.1 hz'] at hp'
            · exact hnarrowβi (hpatchWidthi (congrArg Prod.snd hh))
          · simp only [M,if_pos hz,if_neg hz'] at he
            exact (hcross z.1 z'.1 z.2 z'.2 hz (lt_of_not_ge hz') he).elim
          · simp only [M,if_neg hz,if_pos hz'] at he
            exact (hcross z'.1 z.1 z'.2 z.2 hz' (lt_of_not_ge hz) he.symm).elim
          · simp only [M,if_neg hz,if_neg hz'] at he
            have hh := hCal.injective he
            apply Prod.ext
            · have hp := congrArg Prod.fst hh
              exact hp
            · exact hnarrowβi (hextrai (congrArg Prod.snd hh))
        have hM : IsEmbedding M := (hMc.isClosedEmbedding hMi).isEmbedding
        have hCalU : Set.range Cal ⊆ U := by
          rintro x ⟨z,rfl⟩
          have hxU := hNRU (Set.mem_range_self (shrink z))
          by_contra hn
          have hnot : Cal z ∉ Vcap := fun hs => hn hs.1
          have hfixed := hFoutside (Cal z) hnot
          have he : Cal z = NR (shrink z) := F.injective hfixed
          exact hn (by rwa [he])
        have hMU : Set.range M ⊆ U := by
          rintro x ⟨z,rfl⟩
          dsimp [M]
          split_ifs
          · exact (hBpatchU k (Set.mem_range_self _)).1
          · exact hCalU (Set.mem_range_self _)
        have hMcenter (u : Interval) : M (u,⟨0,by norm_num⟩) = fR u := by
          have hwβ : narrowβ ⟨0,by norm_num⟩ = ⟨0,by norm_num⟩ := Subtype.ext (mul_zero _)
          have hwE : narrowExtra ⟨0,by norm_num⟩ = ⟨0,by norm_num⟩ := Subtype.ext (mul_zero _)
          dsimp [M]
          split_ifs with hu
          · rw [hwβ,hPcenter,hclipPrefix u hu]
          · rw [hwβ,hwE,hCalcenter]
        let Nnew : Interval × Set.Icc (-1:ℝ) 1 → S := M ∘ orient
        have hNnew : IsEmbedding Nnew := hM.comp horiente
        have hNnewU : Set.range Nnew ⊆ U := by
          rintro x ⟨z,rfl⟩
          exact hMU (Set.mem_range_self (orient z))
        have hNnewcenter (u : Interval) : Nnew (u,⟨0,by norm_num⟩) = f u := by
          change M (rev u,⟨0,by norm_num⟩) = f u
          rw [hMcenter]
          change f (rev (rev u)) = f u
          rw [hrevrev]
        let κ : ℝ := factor*extra*β
        have hκ : 0 < κ ∧ κ ≤ 1 := by
          refine ⟨mul_pos (mul_pos hfactor.1 hextra.1) hβ.1,?_⟩
          exact (mul_le_mul_of_nonneg_right
            ((mul_le_mul_of_nonneg_right hfactor.2 hextra.1.le).trans (by simpa using hextra.2)) hβ.1.le).trans
            (by simpa using hβ.2)
        have hmarkedOutside (i : K) (hi : i ∈ A) : ηpatch k < dist (θ i) (θ k) := by
          by_contra hn
          have hm : θ i ∈ Metric.closedBall (θ k) (ηpatch k) := le_of_not_gt hn
          have hfi : f (θ i) ∈ Set.range (Bpatch i) := by
            refine ⟨(⟨θ i,by simp [(hpatchpos i).1.le]⟩,⟨0,by norm_num⟩),?_⟩
            exact hBpatchcenter i _
          have hfk : f (θ i) ∈ Set.range (Bpatch k) := by
            exact ⟨(⟨θ i,hm⟩,⟨0,by norm_num⟩),hBpatchcenter k _⟩
          have hik : i ≠ k := fun he => hk (he ▸ hi)
          exact Set.disjoint_left.mp (hBpatchdis i k hik) hfi hfk
        let ηret (i : K) : ℝ := min (ηold i/2) ((dist (θ i) (θ k)-cutoff)/2)
        have hηret (i : K) (hi : i ∈ A) : 0 < ηret i := by
          apply lt_min (half_pos (holdpos i hi).2)
          have hc := min_le_left (ηpatch k / 2) (1/2)
          have hd := hmarkedOutside i hi
          dsimp [cutoff]
          linarith
        let σnew := Function.update σold k sgn
        let δnew := Function.update (fun i => δold i*κ) k (height*extra*β)
        let ηnew := Function.update ηret k ((seam:ℝ)/2)
        refine ⟨Nnew,hNnew,hNnewU,hNnewcenter,σnew,δnew,ηnew,?_,?_,?_⟩
        · intro i hi
          by_cases hik : i = k
          · subst i
            simpa [σnew] using hsgn
          · simpa [σnew,hik] using holdsign i ((Finset.mem_insert.mp hi).resolve_left hik)
        · intro i hi
          by_cases hik : i = k
          · subst i
            simp only [δnew,ηnew,Function.update_self]
            exact ⟨mul_pos (mul_pos hheight hextra.1) hβ.1,half_pos hseampos⟩
          · have hiA := (Finset.mem_insert.mp hi).resolve_left hik
            simp only [δnew,ηnew,Function.update_of_ne hik]
            exact ⟨mul_pos (holdpos i hiA).1 hκ.1,hηret i hiA⟩
        · intro i hi u w hu
          by_cases hik : i = k
          · subst i
            simp only [ηnew,Function.update_self] at hu
            have hru : (rev u:ℝ) < (seam:ℝ) := by
              have hd := hrevDist (rev u)
              rw [hrevrev,Subtype.dist_eq,Real.dist_eq] at hd
              linarith
            have hclip : clipPrefix (rev u) = rev u := hclipPrefix _ hru.le
            have hp : (prefixParameter (rev u):Interval) = u := by
              change rev (clipPrefix (rev u)) = u
              rw [hclip,hrevrev]
            have hNformula : Nnew (u,w) =
                Bpatch k (prefixParameter (rev u),patchWidth (narrowβ w)) := by
              change (if rev u ≤ seam then _ else _) = _
              rw [if_pos (show rev u ≤ seam from hru.le)]
            rw [hNformula]
            refine ⟨(hBpatchU k (Set.mem_range_self _)).2,?_⟩
            rw [hBpatchcoords,hp]
            apply congrArg (Plane.mk (E k (f u) 0))
            simp only [σnew,δnew,Function.update_self]
            change δpatch k*(sgn*height*extra*(β*(w:ℝ))/δpatch k) = sgn*(height*extra*β)*(w:ℝ)
            field_simp [(hpatchpos k).2.ne']
            <;> ring
          · have hiA := (Finset.mem_insert.mp hi).resolve_left hik
            simp only [ηnew,Function.update_of_ne hik] at hu
            have huDist : dist u (θ i) < ηret i := by
              simpa only [Subtype.dist_eq,Real.dist_eq] using hu
            have huOld : |(u:ℝ)-(θ i:ℝ)| < ηold i :=
              hu.trans ((min_le_left _ _).trans_lt (half_lt_self (holdpos i hiA).2))
            have hruCut : cutoff ≤ (rev u:ℝ) := by
              have hd := hrevDist (rev u)
              rw [hrevrev] at hd
              have ht := dist_triangle (θ i) u (θ k)
              rw [dist_comm (θ i) u] at ht
              have hsmall : dist u (θ i) < (dist (θ i) (θ k)-cutoff)/2 :=
                huDist.trans_le (min_le_right _ _)
              have hsep := hmarkedOutside i hiA
              have hc := min_le_left (ηpatch k / 2) (1/2)
              linarith
            have hruSeam : seam < rev u := by
              change (seam:ℝ) < (rev u:ℝ)
              exact hseamBelow.trans_le hruCut
            have heN : Nnew (u,w) = N (u,⟨κ*(w:ℝ),by
                constructor <;> nlinarith [w.property.1,w.property.2,hκ.1,hκ.2]⟩) := by
              change (if rev u ≤ seam then _ else _) = _
              rw [if_neg (not_le_of_gt hruSeam),hCalTail _ _ hruCut]
              change N (rev (rev u),⟨factor*(extra*(β*(w:ℝ))),_⟩) = _
              rw [hrevrev]
              apply congrArg (fun w => N (u,w))
              apply Subtype.ext
              dsimp [κ]
              ring
            rw [heN]
            obtain ⟨hs,hc⟩ := holdcoords i hiA u ⟨κ*(w:ℝ),by
              constructor <;> nlinarith [w.property.1,w.property.2,hκ.1,hκ.2]⟩ huOld
            refine ⟨hs,?_⟩
            rw [hc]
            apply congrArg (Plane.mk (E i (f u) 0))
            simp only [σnew,δnew,Function.update_of_ne hik]
            change σold i*δold i*(κ*(w:ℝ)) = σold i*(δold i*κ)*(w:ℝ)
            ring
  obtain ⟨N,hN,hNU,hcenter,σ,δ,η,hsign,hpos,hcoords⟩ := hfinite Finset.univ
  exact ⟨N,hN,hNU,hcenter,σ,δ,η,
    fun k => hsign k (Finset.mem_univ k),
    fun k => hpos k (Finset.mem_univ k),
    fun k => hcoords k (Finset.mem_univ k)⟩
end CurveComplex
