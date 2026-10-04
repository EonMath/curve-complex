import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchSquares
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualFiniteAxisPatches
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualLocalAxisNormalizationProducer
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSurfaceAxisRectangleTransplant
set_option maxHeartbeats 3000000
namespace CurveComplex
open Set Topology Schoenflies
theorem source_finite_interior_axis_framed_arc_strip
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (K : Type) [Fintype K]
    (θ : K → Interval) (hθ : Function.Injective θ)
    (hinterior : ∀ k, 0 < (θ k:ℝ) ∧ (θ k:ℝ) < 1)
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
      · exact (hint (hinterior k)).elim
  obtain ⟨N,hN,hNU,hcenter,σ,δ,η,hsign,hpos,hcoords⟩ := hfinite Finset.univ
  exact ⟨N,hN,hNU,hcenter,σ,δ,η,
    fun k => hsign k (Finset.mem_univ k),
    fun k => hpos k (Finset.mem_univ k),
    fun k => hcoords k (Finset.mem_univ k)⟩
end CurveComplex

#print axioms CurveComplex.source_finite_interior_axis_framed_arc_strip
