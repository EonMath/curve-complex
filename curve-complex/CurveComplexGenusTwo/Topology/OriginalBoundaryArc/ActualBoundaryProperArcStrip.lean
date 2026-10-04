import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSurfaceStripGluing
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualFourHalfPortsMiddleStrip
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualHalfPortSideRetention
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualCompletePortAxisTransition
import CurveComplexGenusTwo.Topology.ActualSourceGeometry.ActualContinuousLongitudinalWidthTaper
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualStripSurfaceChart
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualStripNarrowing
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.HalfPlaneBandOpenness
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualEndpointAttachedAxisChartPackage
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.Basic
import CurveComplexGenusTwo.Foundations.EdgeHomotopy
import CurveComplexGenusTwo.Topology.GlobalMonodromy.GlobalLoopSubdivision

set_option maxHeartbeats 8000000

namespace CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc
open CurveComplex Set

variable (S : Type) [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (x : S) (R : ℝ)

abbrev openDisk : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
  Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
abbrev Q := ↥(openDisk S x R)ᶜ
abbrev boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
  Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
abbrev boundaryQ : Set (Q S x R) := {y | y.val ∈ boundaryCircle S x R}

def ProperArc := {a : C(Interval, Q S x R) //
  Topology.IsEmbedding a ∧
    a ⟨0, by norm_num⟩ ∈ boundaryQ S x R ∧
    a ⟨1, by norm_num⟩ ∈ boundaryQ S x R ∧
    ∀ t ∈ Set.Ioo (0 : Interval) 1, a t ∉ boundaryQ S x R}

def boundaryParallel (a : ProperArc S x R) : Prop :=
  ∃ b : C(Interval, Q S x R), Topology.IsEmbedding b ∧
    (∀ t, b t ∈ boundaryQ S x R) ∧
    ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, Q S x R),
      Topology.IsEmbedding d ∧
      d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range a.val ∪ Set.range b

def EssentialProperArc := {a : ProperArc S x R // ¬ boundaryParallel S x R a}

theorem source_actual_boundary_proper_arc_strip
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (a : ProperArc S x R) :
    ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R),
      Topology.IsEmbedding E ∧
      (∀ t, E (t, ⟨0, by norm_num⟩) = a.val t) ∧
      (∀ w, E (0, w) ∈ boundaryQ S x R ∧ E (1, w) ∈ boundaryQ S x R) ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w, E (t, w) ∉ boundaryQ S x R) ∧
      IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  have narrower_relative_open
      (E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R))
      (hE : Topology.IsEmbedding E)
      (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
      IsOpen (E '' {z | -δ < z.2.val ∧ z.2.val < δ}) := by
    have hW : IsOpen {z : Interval × Set.Icc (-1 : ℝ) 1 |
        -δ < z.2.val ∧ z.2.val < δ} :=
      (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
        (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
    obtain ⟨O,hO,himage⟩ := hE.isInducing.image_eq_isOpen_inter_range hW
    have heq : E '' {z | -δ < z.2.val ∧ z.2.val < δ} =
        O ∩ E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
      apply Set.Subset.antisymm
      · intro y hy
        have hOy := (himage ▸ hy).1
        obtain ⟨z,hz,rfl⟩ := hy
        exact ⟨hOy,⟨z,⟨by linarith [hz.1],by linarith [hz.2]⟩,rfl⟩⟩
      · rintro y ⟨hy, z,hz,rfl⟩
        rw [himage]
        exact ⟨hy,Set.mem_range_self z⟩
    rw [heq]
    exact hO.inter hopen
  have actual_boundary_parallel_push_off
      (E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R))
      (hE : Topology.IsEmbedding E)
      (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = a.val t)
      (hend : ∀ w, E (0,w) ∈ boundaryQ S x R ∧ E (1,w) ∈ boundaryQ S x R)
      (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w, E (t,w) ∉ boundaryQ S x R)
      (O : Set (Q S x R)) (hO : IsOpen O) (haO : Set.range a.val ⊆ O) :
      ∃ p q : ProperArc S x R,
        Set.range p.val ⊆ O ∧ Set.range q.val ⊆ O ∧
        Disjoint (Set.range p.val) (Set.range a.val) ∧
        Disjoint (Set.range q.val) (Set.range a.val) ∧
        Disjoint (Set.range p.val) (Set.range q.val) := by
    let zero : Set.Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
    have hprod : ({zero} : Set (Set.Icc (-1 : ℝ) 1)) ×ˢ Set.univ ⊆
        (fun z : Set.Icc (-1 : ℝ) 1 × Interval => E (z.2,z.1)) ⁻¹' O := by
      rintro ⟨w,t⟩ ⟨hw,ht⟩
      obtain rfl := Set.mem_singleton_iff.mp hw
      change E (t,zero) ∈ O
      rw [hcenter]
      exact haO (Set.mem_range_self t)
    obtain ⟨U,V,hU,hV,hzero,hI,hUV⟩ := generalized_tube_lemma
      isCompact_singleton isCompact_univ
      (hO.preimage (hE.continuous.comp continuous_swap)) hprod
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU zero (hzero (Set.mem_singleton _))
    let δ : ℝ := min (ε/2) (1/2)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
    let wp : Set.Icc (-1 : ℝ) 1 := ⟨δ,by constructor <;> linarith⟩
    let wm : Set.Icc (-1 : ℝ) 1 := ⟨-δ,by constructor <;> linarith⟩
    have side (w : Set.Icc (-1 : ℝ) 1) (hw : |(w : ℝ)| < ε) :
        ∃ b : ProperArc S x R, (∀ t, b.val t = E (t,w)) ∧ Set.range b.val ⊆ O := by
      let b : C(Interval,Q S x R) := ⟨fun t => E (t,w),
        hE.continuous.comp (continuous_id.prodMk continuous_const)⟩
      have hb : Topology.IsEmbedding b := (b.continuous.isClosedEmbedding (by
        intro s t he
        exact congrArg Prod.fst (hE.injective he))).isEmbedding
      refine ⟨⟨b,hb,(hend w).1,(hend w).2,fun t ht => hint t ht w⟩,
        fun t => rfl,?_⟩
      rintro _ ⟨t,rfl⟩
      change E (t,w) ∈ O
      apply hUV (show (w,t) ∈ U ×ˢ V from ?_)
      constructor
      · apply hεU
        change dist (w : ℝ) 0 < ε
        simpa only [Real.dist_eq,sub_zero] using hw
      · exact hI (Set.mem_univ t)
    obtain ⟨p,hp,hpO⟩ := side wp (by simpa only [wp,Subtype.coe_mk,abs_of_pos hδ] using hδε)
    obtain ⟨q,hq,hqO⟩ := side wm (by simpa only [wm,Subtype.coe_mk,abs_neg,abs_of_pos hδ] using hδε)
    have avoid (b : ProperArc S x R) (w : Set.Icc (-1 : ℝ) 1)
        (hb : ∀ t, b.val t = E (t,w)) (hw : (w : ℝ) ≠ 0) :
        Disjoint (Set.range b.val) (Set.range a.val) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨t,rfl⟩ ⟨u,hu⟩
      have he : E (u,zero) = E (t,w) := (hcenter u).trans (hu.trans (hb t))
      have hh := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => (z.2 : ℝ))
        (hE.injective he)
      exact hw hh.symm
    refine ⟨p,q,hpO,hqO,avoid p wp hp hδ.ne',
      avoid q wm hq (by change -δ ≠ 0; linarith),?_⟩
    apply Set.disjoint_left.mpr
    rintro y ⟨t,rfl⟩ ⟨u,hu⟩
    have he : E (u,wm) = E (t,wp) := (hq u).symm.trans (hu.trans (hp t))
    have hh := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => (z.2 : ℝ))
      (hE.injective he)
    change -δ = δ at hh
    linarith
  have source_actual_boundary_endpoint_seed
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
      (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (a : ProperArc S x R) :
        ∃ b : ℝ, ∃ hb : 0 < b ∧ b < 1,
        ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R),
          Topology.IsEmbedding E ∧
          (∀ t, E (t,⟨0,by norm_num⟩) =
            a.val ⟨b*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩) ∧
          (∀ w, E (0,w) ∈ boundaryQ S x R) ∧
          (∀ t : Interval, 0 < (t:ℝ) → ∀ w, E (t,w) ∉ boundaryQ S x R) ∧
          (∀ z, E z ∈ Set.range a.val ↔ (z.2 : ℝ) = 0) := by
      classical
      letI : ClosedSurface S := Classical.choice hS.2.1
      obtain ⟨U,V,hpU,h,hU,hV,hzero,hother,hdisk,hboundary,haxis⟩ :=
        CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.source_proper_arc_initial_endpoint_attached_axis_chart
          S g hg hS x R hR htarget a.val a.property.1 a.property.2.1
          a.property.2.2.1 (fun t ht => a.property.2.2.2 t ht)
      let f : C(Interval,S) := ⟨fun t => (a.val t).val,
        continuous_subtype_val.comp a.val.continuous⟩
      have hzeroF : ((h ⟨f 0,hpU⟩ : V) : ℝ × ℝ) = (0,0) := by
        simpa [f] using hzero
      have h0V : (0,0) ∈ V := hzeroF ▸ (h ⟨f 0,hpU⟩).property
      obtain ⟨ε,hε,hεV⟩ := Metric.isOpen_iff.mp hV (0,0) h0V
      let K : Set U := (fun y : U => (h y : ℝ × ℝ)) ⁻¹' Metric.ball (0,0) (ε/2)
      have hK : IsOpen K := Metric.isOpen_ball.preimage
        (continuous_subtype_val.comp h.continuous)
      let W : Set S := Subtype.val '' K
      have hW : IsOpen W := hU.isOpenMap_subtype_val K hK
      have hf0W : f 0 ∈ W := by
        refine ⟨⟨f 0,hpU⟩,?_,rfl⟩
        change dist ((h ⟨f 0,hpU⟩ : V) : ℝ × ℝ) (0,0) < ε/2
        rw [hzeroF,dist_self]
        positivity
      obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp
        ((hW.preimage f.continuous).mem_nhds hf0W)
      let b : ℝ := min (r/2) (1/2)
      have hb : 0 < b ∧ b < 1 := by
        constructor
        · exact lt_min (half_pos hr) (by norm_num)
        · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hbr : b < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      let τ : Interval → Interval := fun t => ⟨b*(t:ℝ),by
        constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩
      have hτc : Continuous τ := by dsimp [τ]; fun_prop
      have hτi : Function.Injective τ := by
        intro t u he
        apply Subtype.ext
        exact mul_left_cancel₀ hb.1.ne' (congrArg Subtype.val he)
      have hfW (t : Interval) : f (τ t) ∈ W := by
        apply hrW
        change dist (b*(t:ℝ)) (0:ℝ) < r
        rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg hb.1.le t.property.1)]
        exact (mul_le_of_le_one_right hb.1.le t.property.2).trans_lt hbr
      have hfU (t : Interval) : f (τ t) ∈ U := by
        obtain ⟨y,hy,he⟩ := hfW t
        exact he ▸ y.property
      let c : Interval → ℝ × ℝ := fun t => (h ⟨f (τ t),hfU t⟩ : V)
      have hcc : Continuous c := continuous_subtype_val.comp
        (h.continuous.comp ((f.continuous.comp hτc).subtype_mk _))
      have hcsmall (t : Interval) : dist (c t) (0,0) < ε/2 := by
        obtain ⟨y,hy,he⟩ := hfW t
        have hey : y = ⟨f (τ t),hfU t⟩ := Subtype.ext he
        have hy' : dist ((h y : V) : ℝ × ℝ) (0,0) < ε/2 := hy
        change dist ((h ⟨f (τ t),hfU t⟩ : V) : ℝ × ℝ) (0,0) < ε/2
        simpa only [hey] using hy'
      have hcaxis (t : Interval) : 0 ≤ (c t).1 ∧ (c t).2 = 0 :=
        (haxis (f (τ t)) (hfU t)).mp ⟨a.val (τ t),Set.mem_range_self _,rfl⟩
      have hc0 : c 0 = (0,0) := by
        have hτ0 : τ 0 = 0 := Subtype.ext (by change b*0=0; ring)
        change ((h ⟨f (τ 0),hfU 0⟩ : V) : ℝ × ℝ) = _
        simpa only [hτ0] using hzeroF
      have hcpos (t : Interval) (ht : 0 < (t:ℝ)) : 0 < (c t).1 := by
        apply lt_of_le_of_ne (hcaxis t).1
        intro he
        have hcB := (hboundary (f (τ t)) (hfU t)).mpr he.symm
        have hτint : τ t ∈ Set.Ioo (0 : Interval) 1 := by
          constructor
          · change 0 < b*(t:ℝ); exact mul_pos hb.1 ht
          · change b*(t:ℝ) < 1
            exact (mul_le_of_le_one_right hb.1.le t.property.2).trans_lt hb.2
        exact a.property.2.2.2 (τ t) hτint hcB
      let k : Interval × Set.Icc (-1 : ℝ) 1 → ℝ × ℝ :=
        fun z => ((c z.1).1,(ε/2)*(z.2:ℝ))
      have hkc : Continuous k := by dsimp [k]; fun_prop
      have hkV (z : Interval × Set.Icc (-1 : ℝ) 1) : k z ∈ V := by
        apply hεV
        change dist (k z) (0,0) < ε
        rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero]
        apply max_lt
        · have hc := (max_lt_iff.mp (by simpa only [Prod.dist_eq,Real.dist_eq,sub_zero] using hcsmall z.1)).1
          exact hc.trans (by linarith)
        · change |(ε/2)*(z.2:ℝ)| < ε
          rw [abs_mul,abs_of_pos (half_pos hε)]
          exact (mul_le_of_le_one_right (half_pos hε).le (abs_le.mpr z.2.property)).trans_lt (by linarith)
      let F : Interval × Set.Icc (-1 : ℝ) 1 → S :=
        fun z => (h.symm ⟨k z,hkV z⟩ : U)
      have hFc : Continuous F := continuous_subtype_val.comp
        (h.symm.continuous.comp (hkc.subtype_mk _))
      have hFk (z) : ((h ⟨F z,(h.symm ⟨k z,hkV z⟩).property⟩ : V) : ℝ × ℝ) = k z := by
        exact congrArg Subtype.val (h.apply_symm_apply ⟨k z,hkV z⟩)
      have hFi : Function.Injective F := by
        intro z w he
        have hh : k z = k w := (hFk z).symm.trans
          ((congrArg (fun y : U => ((h y : V) : ℝ × ℝ)) (Subtype.ext he)).trans (hFk w))
        have hwidth : (z.2:ℝ) = (w.2:ℝ) :=
          mul_left_cancel₀ (half_pos hε).ne' (congrArg Prod.snd hh)
        have hfirstK := congrArg (fun v : ℝ × ℝ => v.1) hh
        have hfirst : (c z.1).1 = (c w.1).1 := hfirstK
        have hcent : c z.1 = c w.1 := Prod.ext hfirst
          ((hcaxis z.1).2.trans (hcaxis w.1).2.symm)
        have hpoint : f (τ z.1) = f (τ w.1) := congrArg (fun y : U => (y : S))
          (h.injective (Subtype.ext hcent))
        have hparam : τ z.1 = τ w.1 := a.property.1.injective (Subtype.ext hpoint)
        exact Prod.ext (hτi hparam) (Subtype.ext hwidth)
      have boundary_avoids_disk (y : S) (hy : y ∈ boundaryCircle S x R) : y ∉ openDisk S x R := by
        rintro ⟨u,hu,heu⟩
        obtain ⟨v,hv,hev⟩ := hy
        have huv : u = v := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.injOn
          (htarget (Metric.ball_subset_closedBall hu))
          (htarget (Metric.sphere_subset_closedBall hv)) (heu.trans hev.symm)
        exact (ne_of_lt (Metric.mem_ball.mp hu)) (huv ▸ Metric.mem_sphere.mp hv)
      have hFQ (z : Interval × Set.Icc (-1 : ℝ) 1) : F z ∉ openDisk S x R := by
        intro ho
        have hD : F z ∈ CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.closedDisk S x R :=
          Set.image_mono Metric.ball_subset_closedBall ho
        have hnonpos := (hdisk (F z) (h.symm ⟨k z,hkV z⟩).property).mp hD
        rw [hFk] at hnonpos
        change (c z.1).1 ≤ 0 at hnonpos
        have hzeroX : (c z.1).1 = 0 := le_antisymm hnonpos (hcaxis z.1).1
        have hB : F z ∈ boundaryCircle S x R :=
          (hboundary (F z) (h.symm ⟨k z,hkV z⟩).property).mpr (by rw [hFk]; exact hzeroX)
        exact boundary_avoids_disk (F z) hB ho
      let E : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R) :=
        ⟨fun z => ⟨F z,hFQ z⟩,hFc.subtype_mk _⟩
      have hE : Topology.IsEmbedding E := (E.continuous.isClosedEmbedding (by
        intro z w he
        exact hFi (congrArg (fun y : Q S x R => (y : S)) he))).isEmbedding
      have hcenter (t : Interval) : E (t,⟨0,by norm_num⟩) = a.val (τ t) := by
        apply Subtype.ext
        change F (t,⟨0,by norm_num⟩) = f (τ t)
        have hh : h ⟨F (t,⟨0,by norm_num⟩),(h.symm ⟨k (t,⟨0,by norm_num⟩),hkV _⟩).property⟩ =
            h ⟨f (τ t),hfU t⟩ := by
          apply Subtype.ext
          rw [hFk]
          change ((c t).1,(ε/2)*0) = c t
          exact Prod.ext (by rfl) (by simpa only [mul_zero] using (hcaxis t).2.symm)
        exact congrArg (fun y : U => (y : S)) (h.injective hh)
      refine ⟨b,hb,E,hE,hcenter,?_,?_,?_⟩
      · intro w
        change F (0,w) ∈ boundaryCircle S x R
        apply (hboundary _ _).mpr
        rw [hFk]
        change (c 0).1 = 0
        rw [hc0]
      · intro t ht w hB
        have hh := (hboundary (F (t,w)) (h.symm ⟨k (t,w),hkV (t,w)⟩).property).mp hB
        rw [hFk] at hh
        exact (hcpos t ht).ne' hh
      · intro z
        constructor
        · rintro ⟨t,ht⟩
          have htrace : F z ∈ Subtype.val '' Set.range a.val :=
            ⟨a.val t,Set.mem_range_self t,congrArg Subtype.val ht⟩
          have hh := ((haxis (F z) (h.symm ⟨k z,hkV z⟩).property).mp htrace).2
          rw [hFk] at hh
          change (ε/2)*(z.2:ℝ) = 0 at hh
          exact (mul_eq_zero.mp hh).resolve_left (half_pos hε).ne'
        · intro hw
          have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hw)
          refine ⟨τ z.1,?_⟩
          rw [he,hcenter]
  
  have source_actual_boundary_endpoint_seed_in_open
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
      (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (a : ProperArc S x R)
      (O : Set (Q S x R)) (hO : IsOpen O) (haO : Set.range a.val ⊆ O) :
        ∃ b : ℝ, ∃ hb : 0 < b ∧ b < 1,
        ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R),
          Topology.IsEmbedding E ∧ Set.range E ⊆ O ∧
          (∀ t, E (t,⟨0,by norm_num⟩) =
            a.val ⟨b*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩) ∧
          (∀ w, E (0,w) ∈ boundaryQ S x R) ∧
          (∀ t : Interval, 0 < (t:ℝ) → ∀ w, E (t,w) ∉ boundaryQ S x R) ∧
          (∀ z, E z ∈ Set.range a.val ↔ (z.2 : ℝ) = 0) := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    obtain ⟨b,hb,E,hE,hcenter,hboundary,hinterior,havoid⟩ :=
      source_actual_boundary_endpoint_seed g hg hS hR htarget a
    obtain ⟨ρ,hρ,N,hN,hNO,hscale,hNcenter⟩ :=
      source_shrink_embedded_strip_in_open E hE O hO (fun t => by
        rw [hcenter]; exact haO (Set.mem_range_self _))
    let EN : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R) := ⟨N,hN.continuous⟩
    refine ⟨b,hb,EN,hN,hNO,?_,?_,?_,?_⟩
    · intro t
      exact (hNcenter t).trans (hcenter t)
    · intro w
      change N (0,w) ∈ boundaryQ S x R
      rw [hscale]
      exact hboundary _
    · intro t ht w
      change N (t,w) ∉ boundaryQ S x R
      rw [hscale]
      exact hinterior t ht _
    · intro z
      change N z ∈ Set.range a.val ↔ (z.2 : ℝ) = 0
      rw [hscale,havoid]
      change ρ*(z.2:ℝ) = 0 ↔ (z.2:ℝ) = 0
      exact mul_eq_zero.trans (or_iff_right hρ.1.ne')
  
  have source_actual_family_clear_boundary_endpoint_seed
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
      (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (a : ProperArc S x R)
      {ι : Type} [Fintype ι] (family : ι → ProperArc S x R)
      (hdisjoint : ∀ i, Disjoint (Set.range a.val) (Set.range (family i).val)) :
        ∃ b : ℝ, ∃ hb : 0 < b ∧ b < 1,
        ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R),
          Topology.IsEmbedding E ∧ (∀ i, Disjoint (Set.range E) (Set.range (family i).val)) ∧
          (∀ t, E (t,⟨0,by norm_num⟩) =
            a.val ⟨b*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩) ∧
          (∀ w, E (0,w) ∈ boundaryQ S x R) ∧
          (∀ t : Interval, 0 < (t:ℝ) → ∀ w, E (t,w) ∉ boundaryQ S x R) ∧
          (∀ z, E z ∈ Set.range a.val ↔ (z.2 : ℝ) = 0) := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    let O : Set (Q S x R) := (⋃ i, Set.range (family i).val)ᶜ
    have hc : ∀ i, IsClosed (Set.range (family i).val) := by
      intro i
      simpa only [Set.image_univ] using
        (isCompact_univ.image (family i).val.continuous).isClosed
    have hO : IsOpen O := (isClosed_iUnion_of_finite hc).isOpen_compl
    have haO : Set.range a.val ⊆ O := by
      intro y hy hmem
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hmem
      exact Set.disjoint_left.mp (hdisjoint i) hy hi
    obtain ⟨b,hb,E,hE,hEO,hcenter,hboundary,hinterior,havoid⟩ :=
      source_actual_boundary_endpoint_seed_in_open g hg hS hR htarget a O hO haO
    refine ⟨b,hb,E,hE,?_,hcenter,hboundary,hinterior,havoid⟩
    intro i
    apply Set.disjoint_left.mpr
    intro y hy hi
    exact hEO hy (Set.mem_iUnion.mpr ⟨i,hi⟩)
  have originalBoundaryBandInitialNeighborhood
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R))
      (hE : Topology.IsEmbedding E)
      (hend : ∀ w, E (0,w) ∈ boundaryQ S x R ∧ E (1,w) ∈ boundaryQ S x R)
      (hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w, E (t,w) ∉ boundaryQ S x R)
      (w : Set.Icc (-1 : ℝ) 1) (hw : -1 < (w:ℝ) ∧ (w:ℝ) < 1) :
      ∃ N : Set (Q S x R), IsOpen N ∧ E (0,w) ∈ N ∧
        N ⊆ E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    let b : C(Interval,Q S x R) := ⟨fun t => E (t,w),
      E.continuous.comp (continuous_id.prodMk continuous_const)⟩
    have hb : Topology.IsEmbedding b := hE.comp (isEmbedding_prodMkLeft w)
    obtain ⟨U,V,hpU,h,hU,hV,hzero,hother,hdisk,hboundary,haxis⟩ :=
      CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.source_proper_arc_initial_endpoint_attached_axis_chart
        S g hg hS x R hR htarget b hb (hend w).1 (hend w).2
        (fun t ht => hproper t ht w)
    let f : C(Interval × Set.Icc (-1 : ℝ) 1,S) :=
      ⟨fun z => (E z).val,continuous_subtype_val.comp E.continuous⟩
    have hp : f (0,w) ∈ U := hpU
    obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp
      ((hU.preimage f.continuous).mem_nhds hp)
    let a : ℝ := min (r/4) (1/2)
    have ha : 0 < a ∧ a < 1 :=
      ⟨lt_min (by positivity) (by norm_num),
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
    have har : a < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let η : ℝ := min (r/4) (min ((1-(w:ℝ))/2) ((1+(w:ℝ))/2))
    have hη : 0 < η := lt_min (by positivity)
      (lt_min (by linarith [hw.2]) (by linarith [hw.1]))
    have hηr : η < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηlo : η ≤ (1+(w:ℝ))/2 := (min_le_right _ _).trans (min_le_right _ _)
    have hηhi : η ≤ (1-(w:ℝ))/2 := (min_le_right _ _).trans (min_le_left _ _)
    have hwstrict (u : Set.Icc (-1 : ℝ) 1) : -1 < (w:ℝ)+η*(u:ℝ) ∧
        (w:ℝ)+η*(u:ℝ) < 1 := by
      constructor <;> nlinarith [u.property.1,u.property.2,hw.1,hw.2]
    let k : Interval × Set.Icc (-1 : ℝ) 1 → Interval × Set.Icc (-1 : ℝ) 1 := fun z =>
      (⟨a*(z.1:ℝ),by constructor <;> nlinarith [z.1.property.1,z.1.property.2,ha.1,ha.2]⟩,
        ⟨(w:ℝ)+η*(z.2:ℝ),⟨(hwstrict z.2).1.le,(hwstrict z.2).2.le⟩⟩)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      intro z v he
      apply Prod.ext
      · apply Subtype.ext
        exact mul_left_cancel₀ ha.1.ne' (congrArg (fun p => (p.1:ℝ)) he)
      · apply Subtype.ext
        have hh := congrArg (fun p => (p.2:ℝ)) he
        change (w:ℝ)+η*(z.2:ℝ) = (w:ℝ)+η*(v.2:ℝ) at hh
        nlinarith
    have hfkU (z) : f (k z) ∈ U := by
      apply hrU
      rw [Metric.mem_ball,Prod.dist_eq,Subtype.dist_eq,Subtype.dist_eq,Real.dist_eq,Real.dist_eq]
      apply max_lt
      · change |a*(z.1:ℝ)-0| < r
        rw [sub_zero,abs_of_nonneg (mul_nonneg ha.1.le z.1.property.1)]
        exact (mul_le_of_le_one_right ha.1.le z.1.property.2).trans_lt har
      · change |((w:ℝ)+η*(z.2:ℝ))-(w:ℝ)| < r
        have he : ((w:ℝ)+η*(z.2:ℝ))-(w:ℝ) = η*(z.2:ℝ) := by ring
        rw [he,abs_mul,abs_of_pos hη]
        exact (mul_le_of_le_one_right hη.le (abs_le.mpr z.2.property)).trans_lt hηr
    have outside_nonneg (y : S) (hy : y ∈ U) (hQ : y ∉ openDisk S x R) :
        0 ≤ (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).1 := by
      by_contra hn
      have hneg : (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).1 < 0 := lt_of_not_ge hn
      obtain ⟨z,hz,he⟩ := (hdisk y hy).mpr hneg.le
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlo | heq
      · exact hQ ⟨z,Metric.mem_ball.mpr hlo,he⟩
      · have hB : y ∈ CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.boundary S x R :=
          ⟨z,Metric.mem_sphere.mpr heq,he⟩
        exact hneg.ne ((hboundary y hy).mp hB)
    let coord : U → Schoenflies.Plane := fun y => Schoenflies.Plane.mk
      (((h y : V) : ℝ × ℝ)).1 (((h y : V) : ℝ × ℝ)).2
    have hcoord : Continuous coord := by dsimp [coord]; fun_prop
    have hcoordi : Function.Injective coord := by
      intro y z he
      apply h.injective
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun p : Schoenflies.Plane => p 0) he
      · exact congrArg (fun p : Schoenflies.Plane => p 1) he
    let C : C(Interval × Set.Icc (-1 : ℝ) 1,Schoenflies.Plane) :=
      ⟨fun z => coord ⟨f (k z),hfkU z⟩,
        hcoord.comp ((f.continuous.comp hkc).subtype_mk _)⟩
    have hCi : Function.Injective C := by
      intro z v he
      have hh := congrArg (fun y : U => (y:S)) (hcoordi he)
      have hEk : E (k z) = E (k v) := Subtype.ext hh
      exact hki (hE.injective hEk)
    have hC : Topology.IsEmbedding C := (C.continuous.isClosedEmbedding hCi).isEmbedding
    have hCzero (u : Set.Icc (-1 : ℝ) 1) : C (0,u) 0 = 0 := by
      apply (hboundary (f (k (0,u))) (hfkU (0,u))).mp
      have hk0 : (k (0,u)).1 = 0 := Subtype.ext (by change a*0=0; ring)
      change (E (k (0,u))).val ∈ boundaryCircle S x R
      have he : k (0,u) = (0,(k (0,u)).2) := Prod.ext hk0 rfl
      rw [he]
      exact (hend _).1
    have hCpos (t : Interval) (ht : 0 < (t:ℝ)) (u : Set.Icc (-1 : ℝ) 1) :
        0 < C (t,u) 0 := by
      have hn := outside_nonneg (f (k (t,u))) (hfkU (t,u)) (E (k (t,u))).property
      apply lt_of_le_of_ne hn
      intro he
      have hB := (hboundary (f (k (t,u))) (hfkU (t,u))).mpr he.symm
      have hti : (k (t,u)).1 ∈ Set.Ioo (0 : Interval) 1 := by
        constructor
        · change 0 < a*(t:ℝ); exact mul_pos ha.1 ht
        · change a*(t:ℝ) < 1
          exact (mul_le_of_le_one_right ha.1.le t.property.2).trans_lt ha.2
      exact hproper _ hti _ hB
    let P : Set {p : Schoenflies.Plane | 0 ≤ p 0} :=
      {y | y.val ∈ C '' {z | (z.1:ℝ) < 1 ∧ -1 < (z.2:ℝ) ∧ (z.2:ℝ) < 1}}
    have hP : IsOpen P := halfPlaneBandOpenness C hC hCzero hCpos
    let W : Set (Q S x R) := Subtype.val ⁻¹' U
    have hW : IsOpen W := hU.preimage continuous_subtype_val
    let J : W → U := fun y => ⟨y.val.val,y.property⟩
    have hJ : Continuous J := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    let H : W → {p : Schoenflies.Plane | 0 ≤ p 0} := fun y =>
      ⟨coord (J y),outside_nonneg y.val.val y.property y.val.property⟩
    have hH : Continuous H := (hcoord.comp hJ).subtype_mk _
    let K : Set W := H ⁻¹' P
    have hK : IsOpen K := hP.preimage hH
    let N : Set (Q S x R) := Subtype.val '' K
    have hN : IsOpen N := hW.isOpenMap_subtype_val K hK
    have hk00 : k (0,⟨0,by norm_num⟩) = (0,w) := by
      apply Prod.ext
      · apply Subtype.ext; change a*0=0; ring
      · apply Subtype.ext; change (w:ℝ)+η*0=(w:ℝ); ring
    have hpN : E (0,w) ∈ N := by
      refine ⟨⟨E (0,w),hp⟩,?_,rfl⟩
      change coord (J ⟨E (0,w),hp⟩) ∈ C '' _
      refine ⟨(0,⟨0,by norm_num⟩),⟨by norm_num,by norm_num,by norm_num⟩,?_⟩
      change coord ⟨f (k (0,⟨0,by norm_num⟩)),hfkU _⟩ =
        coord ⟨(E (0,w)).val,hp⟩
      apply congrArg coord
      apply Subtype.ext
      change (E (k (0,⟨0,by norm_num⟩))).val = (E (0,w)).val
      rw [hk00]
    refine ⟨N,hN,hpN,?_⟩
    rintro y ⟨u,hu,rfl⟩
    change coord (J u) ∈ C '' _ at hu
    obtain ⟨z,hz,he⟩ := hu
    have hh := congrArg (fun y : U => (y:S)) (hcoordi he)
    have hEq : E (k z) = u.val := Subtype.ext hh
    exact ⟨k z,hwstrict z.2,hEq⟩
  /- Relative openness is derived for every actual original-Q embedded proper
  band, including both full boundary width edges. No openness certificate is input. -/
  have source_original_boundary_band_relative_open
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R))
      (hE : Topology.IsEmbedding E)
      (hend : ∀ w, E (0,w) ∈ boundaryQ S x R ∧ E (1,w) ∈ boundaryQ S x R)
      (hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w, E (t,w) ∉ boundaryQ S x R) :
      IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    have interiorNeighborhood (t : Interval) (w : Set.Icc (-1 : ℝ) 1)
        (ht : 0 < (t:ℝ) ∧ (t:ℝ) < 1) (hw : -1 < (w:ℝ) ∧ (w:ℝ) < 1) :
        ∃ N : Set (Q S x R), IsOpen N ∧ E (t,w) ∈ N ∧
          N ⊆ E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
      let clip : Schoenflies.Plane → Interval × Set.Icc (-1 : ℝ) 1 := fun z =>
        (Set.projIcc 0 1 zero_le_one (z 0),Set.projIcc (-1) 1 (by norm_num) (z 1))
      let F : Schoenflies.Plane → S := fun z => (E (clip z)).val
      have hFc : Continuous F := continuous_subtype_val.comp
        (E.continuous.comp (by dsimp [clip]; fun_prop))
      let O : Set Schoenflies.Plane := {z | 0 < z 0 ∧ z 0 < 1 ∧ -1 < z 1 ∧ z 1 < 1}
      have hO : IsOpen O :=
        (isOpen_lt continuous_const (show Continuous (fun z : Schoenflies.Plane => z 0) by fun_prop)).inter
        ((isOpen_lt (show Continuous (fun z : Schoenflies.Plane => z 0) by fun_prop) continuous_const).inter
        ((isOpen_lt continuous_const (show Continuous (fun z : Schoenflies.Plane => z 1) by fun_prop)).inter
        (isOpen_lt (show Continuous (fun z : Schoenflies.Plane => z 1) by fun_prop) continuous_const)))
      have hclip (z : Schoenflies.Plane) (hz : z ∈ O) :
          ((clip z).1:ℝ) = z 0 ∧ ((clip z).2:ℝ) = z 1 := by
        constructor
        · exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hz.1.le,hz.2.1.le⟩)
        · exact congrArg Subtype.val (Set.projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
            ⟨hz.2.2.1.le,hz.2.2.2.le⟩)
      have hFi : Set.InjOn F O := by
        intro z hz v hv he
        have hEq : E (clip z) = E (clip v) := Subtype.ext he
        have hh := hE.injective hEq
        have h0 := congrArg (fun p : Interval × Set.Icc (-1 : ℝ) 1 => (p.1:ℝ)) hh
        have h1 := congrArg (fun p : Interval × Set.Icc (-1 : ℝ) 1 => (p.2:ℝ)) hh
        rw [(hclip z hz).1,(hclip v hv).1] at h0
        rw [(hclip z hz).2,(hclip v hv).2] at h1
        ext j
        fin_cases j <;> assumption
      have hFO : IsOpen (F '' O) :=
        surface_invariance_of_domain_probe F O hO hFc.continuousOn hFi
      let N : Set (Q S x R) := Subtype.val ⁻¹' (F '' O)
      have hN : IsOpen N := hFO.preimage continuous_subtype_val
      have htw : Schoenflies.Plane.mk t w ∈ O := ⟨ht.1,ht.2,hw.1,hw.2⟩
      have hcliptw : clip (Schoenflies.Plane.mk t w) = (t,w) := Prod.ext
        (Subtype.ext (hclip _ htw).1) (Subtype.ext (hclip _ htw).2)
      refine ⟨N,hN,?_,?_⟩
      · refine ⟨Schoenflies.Plane.mk t w,htw,?_⟩
        change (E (clip (Schoenflies.Plane.mk t w))).val = (E (t,w)).val
        rw [hcliptw]
      · rintro y ⟨z,hz,he⟩
        refine ⟨clip z,?_,Subtype.ext he⟩
        change -1 < ((clip z).2:ℝ) ∧ ((clip z).2:ℝ) < 1
        rw [(hclip z hz).2]
        exact ⟨hz.2.2.1,hz.2.2.2⟩
    let rev : Interval × Set.Icc (-1 : ℝ) 1 → Interval × Set.Icc (-1 : ℝ) 1 :=
      fun z => (unitInterval.symm z.1,z.2)
    have hrev : Topology.IsEmbedding rev :=
      unitInterval.symmHomeomorph.isEmbedding.prodMap Topology.IsEmbedding.id
    let Er : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R) :=
      ⟨E ∘ rev,E.continuous.comp hrev.continuous⟩
    have hEr : Topology.IsEmbedding Er := hE.comp hrev
    have hEr0 (w) : Er (0,w) = E (1,w) := by
      apply congrArg E
      apply Prod.ext
      · apply Subtype.ext; norm_num [rev,unitInterval.symm]
      · rfl
    have hEr1 (w) : Er (1,w) = E (0,w) := by
      apply congrArg E
      apply Prod.ext
      · apply Subtype.ext; norm_num [rev,unitInterval.symm]
      · rfl
    have hErend (w) : Er (0,w) ∈ boundaryQ S x R ∧ Er (1,w) ∈ boundaryQ S x R :=
      ⟨hEr0 w ▸ (hend w).2,hEr1 w ▸ (hend w).1⟩
    have hErproper (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1) (w) :
        Er (t,w) ∉ boundaryQ S x R := by
      apply hproper (unitInterval.symm t) _ w
      constructor
      · change (0:ℝ) < 1-(t:ℝ)
        have hh : (t:ℝ) < 1 := ht.2
        linarith
      · change 1-(t:ℝ) < (1:ℝ)
        have hh : (0:ℝ) < t := ht.1
        linarith
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨⟨t,w⟩,hw,rfl⟩
    by_cases ht0 : t = 0
    · subst t
      obtain ⟨N,hN,hp,hsub⟩ := originalBoundaryBandInitialNeighborhood
        g hg hS hR htarget E hE hend hproper w hw
      exact ⟨N,hsub,hN,hp⟩
    by_cases ht1 : t = 1
    · subst t
      obtain ⟨N,hN,hp,hsub⟩ := originalBoundaryBandInitialNeighborhood
        g hg hS hR htarget Er hEr hErend hErproper w hw
      refine ⟨N,?_,hN,(hEr0 w) ▸ hp⟩
      intro y hy
      obtain ⟨z,hz,he⟩ := hsub hy
      exact ⟨rev z,hz,he⟩
    · have ht : 0 < (t:ℝ) ∧ (t:ℝ) < 1 :=
        ⟨lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm)),
          lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))⟩
      obtain ⟨N,hN,hp,hsub⟩ := interiorNeighborhood t w ht hw
      exact ⟨N,hsub,hN,hp⟩
  have source_actual_two_boundary_endpoint_bands
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (a : ProperArc S x R) {ι : Type} [Fintype ι]
      (family : ι → ProperArc S x R)
      (hdisjoint : ∀ i, Disjoint (Set.range a.val) (Set.range (family i).val)) :
      ∃ b c : ℝ, ∃ hb : 0 < b ∧ b < 1, ∃ hc : 0 < c ∧ c < 1,
        b+c < 1 ∧
        ∃ L Rband : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R),
          Topology.IsEmbedding L ∧ Topology.IsEmbedding Rband ∧
          Disjoint (Set.range L) (Set.range Rband) ∧
          (∀ i, Disjoint (Set.range L) (Set.range (family i).val) ∧
            Disjoint (Set.range Rband) (Set.range (family i).val)) ∧
          (∀ t, L (t,⟨0,by norm_num⟩) = a.val
            ⟨b*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩) ∧
          (∀ t, Rband (t,⟨0,by norm_num⟩) = a.val
            ⟨1-c*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hc.1,hc.2]⟩) ∧
          (∀ w, L (0,w) ∈ boundaryQ S x R ∧ Rband (0,w) ∈ boundaryQ S x R) ∧
          (∀ t : Interval, 0 < (t:ℝ) → ∀ w,
            L (t,w) ∉ boundaryQ S x R ∧ Rband (t,w) ∉ boundaryQ S x R) ∧
          (∀ z, L z ∈ Set.range a.val ↔ (z.2:ℝ) = 0) ∧
          (∀ z, Rband z ∈ Set.range a.val ↔ (z.2:ℝ) = 0) := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    let ar : C(Interval,Q S x R) := a.val.comp
      (⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩ : C(Interval,Interval))
    have har : Topology.IsEmbedding ar := a.property.1.comp unitInterval.symmHomeomorph.isEmbedding
    have hr0 : unitInterval.symmHomeomorph 0 = 1 := by apply Subtype.ext; norm_num
    have hr1 : unitInterval.symmHomeomorph 1 = 0 := by apply Subtype.ext; norm_num
    let aR : ProperArc S x R := ⟨ar,har,by
      change a.val (unitInterval.symmHomeomorph 0) ∈ boundaryQ S x R
      rw [hr0]
      exact a.property.2.2.1,by
      change a.val (unitInterval.symmHomeomorph 1) ∈ boundaryQ S x R
      rw [hr1]
      exact a.property.2.1,by
      intro t ht
      apply a.property.2.2.2 (unitInterval.symmHomeomorph t)
      constructor
      · change (0:ℝ) < 1-(t:ℝ)
        have hh : (t:ℝ) < 1 := ht.2
        linarith
      · change 1-(t:ℝ) < (1:ℝ)
        have hh : (0:ℝ) < t := ht.1
        linarith⟩
    have harange : Set.range aR.val = Set.range a.val := by
      ext y
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symmHomeomorph t,rfl⟩
      · rintro ⟨t,rfl⟩
        refine ⟨unitInterval.symmHomeomorph.symm t,?_⟩
        exact congrArg a.val (unitInterval.symmHomeomorph.apply_symm_apply t)
    obtain ⟨b,hb,L,hL,hLfamily,hLcenter,hLboundary,hLinterior,hLavoid⟩ :=
      source_actual_family_clear_boundary_endpoint_seed g hg hS hR htarget a family hdisjoint
    obtain ⟨d,hd,T,hT,hTfamily,hTcenter,hTboundary,hTinterior,hTavoid⟩ :=
      source_actual_family_clear_boundary_endpoint_seed g hg hS hR htarget aR family
        (fun i => harange.symm ▸ hdisjoint i)
    let θ : ℝ := min ((1-b)/(2*d)) (1/2)
    have hθ : 0 < θ := lt_min (div_pos (by linarith [hb.2]) (by nlinarith [hd.1])) (by norm_num)
    have hθ1 : θ ≤ 1 := (min_le_right _ _).trans (by norm_num)
    have hgap : b+d*θ < 1 := by
      have hh : θ ≤ (1-b)/(2*d) := min_le_left _ _
      have hh' := (le_div_iff₀ (show 0 < 2*d by nlinarith [hd.1])).mp hh
      nlinarith [hb.2]
    let c : ℝ := d*θ
    have hc : 0 < c ∧ c < 1 := ⟨mul_pos hd.1 hθ,by dsimp [c]; linarith [hgap,hb.1]⟩
    let k : Interval × Set.Icc (-1 : ℝ) 1 → Interval × Set.Icc (-1 : ℝ) 1 := fun z =>
      (⟨θ*(z.1:ℝ),by constructor <;> nlinarith [z.1.property.1,z.1.property.2,hθ,hθ1]⟩,z.2)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      intro z v he
      have hs := congrArg Prod.snd he
      exact Prod.ext (Subtype.ext (mul_left_cancel₀ hθ.ne'
        (congrArg (fun p => (p.1:ℝ)) he))) hs
    let Tsmall : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R) := ⟨T ∘ k,T.continuous.comp hkc⟩
    have hTsmall : Topology.IsEmbedding Tsmall :=
      (Tsmall.continuous.isClosedEmbedding (hT.injective.comp hki)).isEmbedding
    have hsmallcenter (t : Interval) : Tsmall (t,⟨0,by norm_num⟩) = a.val
        ⟨1-c*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hc.1,hc.2]⟩ := by
      change T (k (t,⟨0,by norm_num⟩)) = _
      rw [hTcenter]
      apply congrArg a.val
      apply Subtype.ext
      change 1-d*(θ*(t:ℝ)) = 1-(d*θ)*(t:ℝ)
      ring
    let O : Set (Q S x R) := (Set.range L)ᶜ
    have hO : IsOpen O := (isCompact_range L.continuous).isClosed.isOpen_compl
    have hcenterO (t : Interval) : Tsmall (t,⟨0,by norm_num⟩) ∈ O := by
      intro hm
      obtain ⟨z,hz⟩ := hm
      have hza : L z ∈ Set.range a.val :=
        ⟨⟨1-c*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hc.1,hc.2]⟩,
          (hsmallcenter t).symm.trans hz.symm⟩
      have hw0 := (hLavoid z).mp hza
      have hzz : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hw0)
      have hEq : a.val ⟨b*(z.1:ℝ),by constructor <;>
          nlinarith [z.1.property.1,z.1.property.2,hb.1,hb.2]⟩ =
        a.val ⟨1-c*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hc.1,hc.2]⟩ := by
        rw [← hLcenter,← hzz]
        exact hz.trans (hsmallcenter t)
      have hh := congrArg Subtype.val (a.property.1.injective hEq)
      change b*(z.1:ℝ) = 1-c*(t:ℝ) at hh
      have hgap' : b+c < 1 := hgap
      nlinarith [z.1.property.1,z.1.property.2,t.property.1,t.property.2]
    obtain ⟨ρ,hρ,N,hN,hNO,hscale,hNcenter⟩ :=
      source_shrink_embedded_strip_in_open Tsmall hTsmall O hO hcenterO
    let Rband : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R) := ⟨N,hN.continuous⟩
    refine ⟨b,c,hb,hc,hgap,L,Rband,hL,hN,?_,?_,hLcenter,?_,?_,?_,hLavoid,?_⟩
    · exact Set.disjoint_left.mpr (fun y hy hz => hNO hz hy)
    · intro i
      refine ⟨hLfamily i,?_⟩
      apply (hTfamily i).mono_left
      rintro y ⟨z,rfl⟩
      change N z ∈ Set.range T
      rw [hscale]
      change T (k _) ∈ Set.range T
      exact Set.mem_range_self _
    · intro t
      exact (hNcenter t).trans (hsmallcenter t)
    · intro w
      refine ⟨hLboundary w,?_⟩
      change N (0,w) ∈ boundaryQ S x R
      rw [hscale]
      change T (k _) ∈ boundaryQ S x R
      have hk0 : (k (0,⟨ρ*(w:ℝ),by constructor <;>
          nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩)).1 = 0 :=
        Subtype.ext (by change θ*0=0; ring)
      have he : k (0,⟨ρ*(w:ℝ),by constructor <;>
          nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩) =
        (0,(k (0,⟨ρ*(w:ℝ),by constructor <;>
          nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩)).2) := Prod.ext hk0 rfl
      rw [he]
      exact hTboundary _
    · intro t ht w
      refine ⟨hLinterior t ht w,?_⟩
      change N (t,w) ∉ boundaryQ S x R
      rw [hscale]
      let v : Set.Icc (-1 : ℝ) 1 := ⟨ρ*(w:ℝ),by constructor <;>
        nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩
      change T (k (t,v)) ∉ boundaryQ S x R
      exact hTinterior (k (t,v)).1 (mul_pos hθ ht) (k (t,v)).2
    · intro z
      change N z ∈ Set.range a.val ↔ (z.2:ℝ) = 0
      rw [hscale,← harange]
      change T (k _) ∈ Set.range aR.val ↔ _
      rw [hTavoid]
      change ρ*(z.2:ℝ) = 0 ↔ (z.2:ℝ) = 0
      exact mul_eq_zero.trans (or_iff_right hρ.1.ne')
  have actual_unit_interval_product_bounds (s t : Interval) :
      0≤(s:ℝ)*(t:ℝ) ∧ (s:ℝ)*(t:ℝ)≤1 :=
    ⟨mul_nonneg s.property.1 t.property.1,
      mul_le_one₀ s.property.2 t.property.1 t.property.2⟩
  have source_actual_original_arc_interior_axis_chart
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
      (a : ProperArc S x R) :
      ∃ e : OpenPartialHomeomorph S Schoenflies.Plane,
        (∀ t : Interval, 0 < (t : ℝ) → (t : ℝ) < 1 →
          (a.val t).val ∈ e.source ∧ e (a.val t).val = Schoenflies.Plane.mk t 0) ∧
        (∀ y ∈ e.source, y ∈ Set.range (fun t => (a.val t).val) ↔ e y 1 = 0) := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    let f : C(Interval,S) := ⟨fun t => (a.val t).val,
      continuous_subtype_val.comp a.val.continuous⟩
    have hf : Topology.IsEmbedding f := Topology.IsEmbedding.subtypeVal.comp a.property.1
    obtain ⟨B,hB,hcenter,hBU⟩ := source_whole_embedded_arc_strip f hf Set.univ
      isOpen_univ (Set.subset_univ _)
    obtain ⟨e,hes,het,hcoord,haxis⟩ := source_embedded_strip_interior_chart B hB f hcenter
    refine ⟨e,?_,haxis⟩
    intro t ht0 ht1
    have hts : B (t,⟨0,by norm_num⟩) ∈ e.source := by
      rw [hes]
      exact ⟨(t,⟨0,by norm_num⟩),⟨ht0,ht1,neg_one_lt_zero,zero_lt_one⟩,rfl⟩
    have htc := hcoord (t,⟨0,by norm_num⟩) ht0 ht1 neg_one_lt_zero zero_lt_one
    rw [hcenter] at hts htc
    exact ⟨hts,htc⟩

  /- Localize the actual whole-interior axis chart OFF the original closed
  chart disk. Every original interior parameter is retained. -/
  have source_actual_original_arc_exterior_axis_chart
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (a : ProperArc S x R) :
      ∃ e : OpenPartialHomeomorph S Schoenflies.Plane,
        e.source ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ ∧
        (∀ t : Interval, 0 < (t : ℝ) → (t : ℝ) < 1 →
          (a.val t).val ∈ e.source ∧ e (a.val t).val = Schoenflies.Plane.mk t 0) ∧
        (∀ y ∈ e.source, y ∈ Set.range (fun t => (a.val t).val) ↔ e y 1 = 0) := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    let D := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    have hDc : IsCompact D := (isCompact_closedBall _ _).image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).continuousOn_symm.mono htarget)
    have hDo : IsOpen Dᶜ := hDc.isClosed.isOpen_compl
    obtain ⟨e,hcenter,haxis⟩ := source_actual_original_arc_interior_axis_chart g hg hS a
    let E := e.restr Dᶜ
    have hEs : E.source = e.source ∩ Dᶜ := e.restr_source' _ hDo
    refine ⟨E,?_,?_,?_⟩
    · rw [hEs]
      exact Set.inter_subset_right
    · intro t ht0 ht1
      have htc := hcenter t ht0 ht1
      constructor
      · rw [hEs]
        refine ⟨htc.1,?_⟩
        rintro ⟨z,hz,he⟩
        rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlt | heq
        · exact (a.val t).property ⟨z,Metric.mem_ball.mpr hlt,he⟩
        · exact a.property.2.2.2 t ⟨ht0,ht1⟩ ⟨z,Metric.mem_sphere.mpr heq,he⟩
      · exact htc.2
    · intro y hy
      rw [hEs] at hy
      exact haxis y hy.1
  have source_actual_boundary_band_interior_port_chart
      (a : ProperArc S x R)
      (L : C(Interval × Icc (-1 : ℝ) 1,Q S x R))
      (hL : Topology.IsEmbedding L)
      (havoid : ∀ z, L z ∈ Set.range a.val ↔ (z.2:ℝ) = 0) :
      ∃ e : OpenPartialHomeomorph S Schoenflies.Plane,
        e.source = (fun z => (L z).val) ''
          {z | 0 < (z.1:ℝ) ∧ (z.1:ℝ) < 1 ∧ -1 < (z.2:ℝ) ∧ (z.2:ℝ) < 1} ∧
        (∀ z, 0 < (z.1:ℝ) → (z.1:ℝ) < 1 → -1 < (z.2:ℝ) → (z.2:ℝ) < 1 →
          e (L z).val = Schoenflies.Plane.mk z.1 z.2) ∧
        (∀ y ∈ e.source,
          y ∈ Set.range (fun t => (a.val t).val) ↔ e y 1 = 0) := by
    let B : Interval × Icc (-1 : ℝ) 1 → S := fun z => (L z).val
    have hB : Topology.IsEmbedding B := Topology.IsEmbedding.subtypeVal.comp hL
    let f : C(Interval,S) := ⟨fun t => B (t,⟨0,by norm_num⟩),
      hB.continuous.comp (continuous_id.prodMk continuous_const)⟩
    obtain ⟨e,hes,het,hcoord,haxis⟩ := source_embedded_strip_interior_chart B hB f (fun _ => rfl)
    refine ⟨e,hes,hcoord,?_⟩
    intro y hy
    rw [hes] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    have hh := hcoord z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
    have hmem : B z ∈ Set.range (fun t => (a.val t).val) ↔ L z ∈ Set.range a.val := by
      constructor
      · rintro ⟨t,ht⟩
        exact ⟨t,Subtype.ext ht⟩
      · rintro ⟨t,ht⟩
        exact ⟨t,congrArg Subtype.val ht⟩
    rw [hmem,havoid,hh]
    rfl
  have source_actual_two_charted_terminal_bands
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (a : ProperArc S x R) :
      ∃ b c : ℝ, ∃ hb : 0<b ∧ b<1, ∃ hc : 0<c ∧ c<1, b+c<1 ∧
      ∃ L T : C(Interval × Icc (-1 : ℝ) 1,Q S x R),
        Topology.IsEmbedding L ∧ Topology.IsEmbedding T ∧
        Disjoint (Set.range L) (Set.range T) ∧
        (∀ t,L (t,⟨0,by norm_num⟩)=a.val ⟨b*(t:ℝ),by constructor <;>
          nlinarith only [t.property.1,t.property.2,hb.1,hb.2]⟩) ∧
        (∀ t,T (t,⟨0,by norm_num⟩)=a.val ⟨1-c*(t:ℝ),by constructor <;>
          nlinarith only [t.property.1,t.property.2,hc.1,hc.2]⟩) ∧
        (∀ w,L (0,w)∈boundaryQ S x R ∧ T (0,w)∈boundaryQ S x R) ∧
        (∀ t : Interval,0<(t:ℝ) → ∀ w,L (t,w)∉boundaryQ S x R ∧ T (t,w)∉boundaryQ S x R) ∧
        (∀ z,L z∈Set.range a.val ↔ (z.2:ℝ)=0) ∧
        (∀ z,T z∈Set.range a.val ↔ (z.2:ℝ)=0) ∧
      ∃ eL eT : OpenPartialHomeomorph S Schoenflies.Plane,
        (∀ w,(L (1,w)).val∈eL.source ∧ eL (L (1,w)).val=Schoenflies.Plane.mk (1/2) ((w:ℝ)/2)) ∧
        (∀ w,(T (1,w)).val∈eT.source ∧ eT (T (1,w)).val=Schoenflies.Plane.mk (1/2) ((w:ℝ)/2)) ∧
        (∀ y∈eL.source,y∈Set.range (fun t => (a.val t).val) ↔ eL y 1=0) ∧
        (∀ y∈eT.source,y∈Set.range (fun t => (a.val t).val) ↔ eT y 1=0) := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    obtain ⟨d,f,hd,hf,hgap,B,C,hB,hC,hBC,hfam,hBc,hCc,hboundary,hinterior,hBa,hCa⟩ :=
      source_actual_two_boundary_endpoint_bands g hg hS hR htarget a
        (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i)
    obtain ⟨eL,heLs,hLcoord,hLaxis⟩ := source_actual_boundary_band_interior_port_chart a B hB hBa
    obtain ⟨eT,heTs,hTcoord,hTaxis⟩ := source_actual_boundary_band_interior_port_chart a C hC hCa
    let k : C(Interval × Icc (-1 : ℝ) 1,Interval × Icc (-1 : ℝ) 1) :=
      ⟨fun z => (⟨(z.1:ℝ)/2,by constructor <;> linarith only [z.1.property.1,z.1.property.2]⟩,
        ⟨(z.2:ℝ)/2,by constructor <;> linarith only [z.2.property.1,z.2.property.2]⟩),by fun_prop⟩
    have hki : Function.Injective k := by
      intro z w he
      have hx := congrArg (fun v => (v.1:ℝ)) he
      have hy := congrArg (fun v => (v.2:ℝ)) he
      apply Prod.ext <;> apply Subtype.ext
      · change (z.1:ℝ)/2=(w.1:ℝ)/2 at hx; linarith
      · change (z.2:ℝ)/2=(w.2:ℝ)/2 at hy; linarith
    have hk : Topology.IsEmbedding k := (k.continuous.isClosedEmbedding hki).isEmbedding
    let L := B.comp k
    let T := C.comp k
    let b := d/2
    let c := f/2
    have hb : 0<b ∧ b<1 := by dsimp [b]; constructor <;> linarith only [hd.1,hd.2]
    have hc : 0<c ∧ c<1 := by dsimp [c]; constructor <;> linarith only [hf.1,hf.2]
    have hbc : b+c<1 := by dsimp [b,c]; linarith
    have hkcenter (t : Interval) : k (t,⟨0,by norm_num⟩)=
        (⟨(t:ℝ)/2,by constructor <;> linarith only [t.property.1,t.property.2]⟩,⟨0,by norm_num⟩) := by
      apply Prod.ext <;> apply Subtype.ext <;> simp [k]
    have hk0 (w : Icc (-1 : ℝ) 1) : k (0,w)=(0,(k (0,w)).2) :=
      Prod.ext (Subtype.ext (by simp [k])) rfl
    have hkport (w : Icc (-1 : ℝ) 1) :
        0<((k (1,w)).1:ℝ) ∧ ((k (1,w)).1:ℝ)<1 ∧
        -1<((k (1,w)).2:ℝ) ∧ ((k (1,w)).2:ℝ)<1 := by
      change 0<(1:ℝ)/2 ∧ (1:ℝ)/2<1 ∧ -1<(w:ℝ)/2 ∧ (w:ℝ)/2<1
      constructor
      · norm_num
      constructor
      · norm_num
      constructor <;> linarith only [w.property.1,w.property.2]
    refine ⟨b,c,hb,hc,hbc,L,T,hB.comp hk,hC.comp hk,?_,?_,?_,?_,?_,?_,?_,eL,eT,?_,?_,hLaxis,hTaxis⟩
    · apply Set.disjoint_left.mpr
      rintro y ⟨z,rfl⟩ ⟨w,he⟩
      exact Set.disjoint_left.mp hBC (Set.mem_range_self (k z)) ⟨k w,he⟩
    · intro t
      change B (k (t,⟨0,by norm_num⟩))=_
      rw [hkcenter,hBc]
      apply congrArg a.val
      apply Subtype.ext
      change d*((t:ℝ)/2)=(d/2)*(t:ℝ)
      ring
    · intro t
      change C (k (t,⟨0,by norm_num⟩))=_
      rw [hkcenter,hCc]
      apply congrArg a.val
      apply Subtype.ext
      change 1-f*((t:ℝ)/2)=1-(f/2)*(t:ℝ)
      ring
    · intro w
      change B (k (0,w))∈boundaryQ S x R ∧ C (k (0,w))∈boundaryQ S x R
      rw [hk0]
      exact hboundary _
    · intro t ht w
      exact hinterior (k (t,w)).1 (by change 0<(t:ℝ)/2; linarith) (k (t,w)).2
    · intro z
      change B (k z)∈Set.range a.val ↔ _
      rw [hBa]
      change (z.2:ℝ)/2=0 ↔ (z.2:ℝ)=0
      constructor <;> intro hh <;> linarith
    · intro z
      change C (k z)∈Set.range a.val ↔ _
      rw [hCa]
      change (z.2:ℝ)/2=0 ↔ (z.2:ℝ)=0
      constructor <;> intro hh <;> linarith
    · intro w
      have hh := hkport w
      refine ⟨?_,hLcoord (k (1,w)) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2⟩
      rw [heLs]
      exact ⟨k (1,w),hh,rfl⟩
    · intro w
      have hh := hkport w
      refine ⟨?_,hTcoord (k (1,w)) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2⟩
      rw [heTs]
      exact ⟨k (1,w),hh,rfl⟩
  have source_actual_simultaneous_complete_terminal_port_positioning
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (a : ProperArc S x R) :
      ∃ b c : ℝ, ∃ hb : 0<b ∧ b<1, ∃ hc : 0<c ∧ c<1, b+c<1 ∧
      ∃ L T : C(Interval × Icc (-1 : ℝ) 1,Q S x R),
        Topology.IsEmbedding L ∧ Topology.IsEmbedding T ∧
        Disjoint (Set.range L) (Set.range T) ∧
        (∀ t,L (t,⟨0,by norm_num⟩)=a.val ⟨b*(t:ℝ),by constructor <;>
          nlinarith only [t.property.1,t.property.2,hb.1,hb.2]⟩) ∧
        (∀ t,T (t,⟨0,by norm_num⟩)=a.val ⟨1-c*(t:ℝ),by constructor <;>
          nlinarith only [t.property.1,t.property.2,hc.1,hc.2]⟩) ∧
        (∀ w,L (0,w)∈boundaryQ S x R ∧ T (0,w)∈boundaryQ S x R) ∧
        (∀ t : Interval,0<(t:ℝ) → ∀ w,L (t,w)∉boundaryQ S x R ∧ T (t,w)∉boundaryQ S x R) ∧
        (∀ z,L z∈Set.range a.val ↔ (z.2:ℝ)=0) ∧
        (∀ z,T z∈Set.range a.val ↔ (z.2:ℝ)=0) ∧
      ∃ B : OpenPartialHomeomorph S (ℝ × ℝ),
        B.source ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ ∧
        (∀ y ∈ B.source, y ∈ Set.range (fun t => (a.val t).val) ↔ (B y).2 = 0) ∧
        (∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) < 1 →
          (a.val t).val ∈ B.source ∧ B (a.val t).val = ((t:ℝ),0)) ∧
        B (L (1,⟨0,by norm_num⟩)).val = (b,0) ∧
        B (T (1,⟨0,by norm_num⟩)).val = (1-c,0) ∧
      ∃ rL rT : ℝ, ∃ hrL : 0 < rL ∧ rL ≤ 1, ∃ hrT : 0 < rT ∧ rT ≤ 1,
        (∀ w : Icc (-1 : ℝ) 1,
          (L (1,⟨rL*(w:ℝ),by constructor <;>
            nlinarith only [hrL.1,hrL.2,w.property.1,w.property.2]⟩)).val ∈ B.source) ∧
        ((0 < (B (L (1,⟨rL,by constructor <;> linarith only [hrL.1,hrL.2]⟩)).val).2 ∧ (B (L (1,⟨-rL,by constructor <;> linarith only [hrL.1,hrL.2]⟩)).val).2 < 0) ∨
         ((B (L (1,⟨rL,by constructor <;> linarith only [hrL.1,hrL.2]⟩)).val).2 < 0 ∧ 0 < (B (L (1,⟨-rL,by constructor <;> linarith only [hrL.1,hrL.2]⟩)).val).2)) ∧
        (∀ w : Icc (-1 : ℝ) 1,
          (T (1,⟨rT*(w:ℝ),by constructor <;>
            nlinarith only [hrT.1,hrT.2,w.property.1,w.property.2]⟩)).val ∈ B.source) ∧
        ((0 < (B (T (1,⟨rT,by constructor <;> linarith only [hrT.1,hrT.2]⟩)).val).2 ∧ (B (T (1,⟨-rT,by constructor <;> linarith only [hrT.1,hrT.2]⟩)).val).2 < 0) ∨
         ((B (T (1,⟨rT,by constructor <;> linarith only [hrT.1,hrT.2]⟩)).val).2 < 0 ∧ 0 < (B (T (1,⟨-rT,by constructor <;> linarith only [hrT.1,hrT.2]⟩)).val).2)) := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    obtain ⟨b,c,hb,hc,hgap,L,T,hL,hT,hLT,hLc,hTc,hboundary,hinterior,hLa,hTa,
      eL,eT,hLport,hTport,hLaxis,hTaxis⟩ :=
      source_actual_two_charted_terminal_bands g hg hS hR htarget a
    obtain ⟨eG,hGout,hGc,hGa⟩ :=
      source_actual_original_arc_exterior_axis_chart g hg hS hR htarget a
    let H : Schoenflies.Plane ≃ₜ (ℝ × ℝ) :=
      ((EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
    let shift : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
      { toFun := fun z => (z.1-1/2,z.2)
        invFun := fun z => (z.1+1/2,z.2)
        left_inv := by intro z; apply Prod.ext <;> dsimp <;> ring
        right_inv := by intro z; apply Prod.ext <;> dsimp <;> ring
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let B := eG.trans H.toOpenPartialHomeomorph
    have hBs : B.source=eG.source := by simp [B,OpenPartialHomeomorph.trans_source]
    have hBc (t : Interval) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) :
        (a.val t).val∈B.source ∧ B (a.val t).val=((t:ℝ),0) := by
      obtain ⟨hs,hh⟩ := hGc t ht0 ht1
      refine ⟨hBs.symm ▸ hs,?_⟩
      change H (eG (a.val t).val)=((t:ℝ),0)
      rw [hh]
      rfl
    have transfer
        (N : C(Interval × Icc (-1 : ℝ) 1,Q S x R))
        (e : OpenPartialHomeomorph S Schoenflies.Plane)
        (hport : ∀ w,(N (1,w)).val∈e.source ∧
          e (N (1,w)).val=Schoenflies.Plane.mk (1/2) ((w:ℝ)/2))
        (haxis : ∀ y∈e.source,y∈Set.range (fun t => (a.val t).val) ↔ e y 1=0)
        (hcenter : (N (1,⟨0,by norm_num⟩)).val∈B.source) :
        ∃ r : ℝ, ∃ hr : 0<r ∧ r≤1,
          (∀ w : Icc (-1 : ℝ) 1,
            (N (1,⟨r*(w:ℝ),by constructor <;>
              nlinarith only [hr.1,hr.2,w.property.1,w.property.2]⟩)).val∈B.source) ∧
          ((0<(B (N (1,⟨r,by constructor <;> linarith only [hr.1,hr.2]⟩)).val).2 ∧
              (B (N (1,⟨-r,by constructor <;> linarith only [hr.1,hr.2]⟩)).val).2<0) ∨
           ((B (N (1,⟨r,by constructor <;> linarith only [hr.1,hr.2]⟩)).val).2<0 ∧
              0<(B (N (1,⟨-r,by constructor <;> linarith only [hr.1,hr.2]⟩)).val).2)) := by
      let A := e.trans (H.trans shift).toOpenPartialHomeomorph
      have hAs : A.source=e.source := by simp [A,OpenPartialHomeomorph.trans_source]
      let P : C(Icc (-1 : ℝ) 1,S) := ⟨fun w => (N (1,w)).val,
        continuous_subtype_val.comp (N.continuous.comp (continuous_const.prodMk continuous_id))⟩
      have hPA : ∀ w,P w∈A.source ∧ A (P w)=(0,(w:ℝ)/2) := by
        intro w
        refine ⟨hAs.symm ▸ (hport w).1,?_⟩
        change shift (H (e (N (1,w)).val))=(0,(w:ℝ)/2)
        rw [(hport w).2]
        apply Prod.ext
        · change (1/2:ℝ)-1/2=0
          ring
        · rfl
      have hAB : ∀ y∈A.source∩B.source,(A y).2=0 ↔ (B y).2=0 := by
        intro y hy
        rw [hAs,hBs] at hy
        change e y 1=0 ↔ eG y 1=0
        exact (haxis y hy.1).symm.trans (hGa y hy.2)
      obtain ⟨r,hr,hwhole,hp,hn,hside⟩ :=
        actual_charted_port_complete_opposite_sides P A B hPA hcenter hAB
      exact ⟨r,hr,hwhole,hside⟩
    have hLc0 : L (1,⟨0,by norm_num⟩)=a.val ⟨b,by constructor <;> linarith only [hb.1,hb.2]⟩ := by
      rw [hLc]
      apply congrArg a.val
      apply Subtype.ext
      change b*1=b
      ring
    have hTc0 : T (1,⟨0,by norm_num⟩)=a.val ⟨1-c,by constructor <;> linarith only [hc.1,hc.2]⟩ := by
      rw [hTc]
      apply congrArg a.val
      apply Subtype.ext
      change 1-c*1=1-c
      ring
    have hLB := hBc ⟨b,by constructor <;> linarith only [hb.1,hb.2]⟩ hb.1 hb.2
    have hTB := hBc ⟨1-c,by constructor <;> linarith only [hc.1,hc.2]⟩
      (by linarith only [hc.2]) (by linarith only [hc.1])
    obtain ⟨rL,hrL,hLwhole,hLside⟩ := transfer L eL hLport hLaxis (by rw [hLc0]; exact hLB.1)
    obtain ⟨rT,hrT,hTwhole,hTside⟩ := transfer T eT hTport hTaxis (by rw [hTc0]; exact hTB.1)
    refine ⟨b,c,hb,hc,hgap,L,T,hL,hT,hLT,hLc,hTc,hboundary,hinterior,hLa,hTa,
      B,?_,?_,hBc,?_,?_,rL,rT,hrL,hrT,hLwhole,hLside,hTwhole,hTside⟩
    · rw [hBs]
      exact hGout
    · intro y hy
      rw [hBs] at hy
      exact hGa y hy
    · rw [hLc0]
      exact hLB.2
    · rw [hTc0]
      exact hTB.2
  obtain ⟨b,c,hb,hc,hgap,L,Rband,hL,hRband,hLR,
      hLcenter,hRcenter,hboundary,hinterior,hLavoid,hRavoid,
      B,hBout,hBaxis,hBcenter,hBL0,hBR0,rL,rR,hrL,hrR,hLwhole,hLside,hRwhole,hRside⟩ :=
    source_actual_simultaneous_complete_terminal_port_positioning g hg hS hR htarget a
  have actual_original_middle_chart_box :
      ∃ l u δ : ℝ, 0<l ∧ l<b ∧ 1-c<u ∧ u<1 ∧ 0<δ ∧
        Icc l u ×ˢ Icc (-δ) δ ⊆ B.target := by
    let l := b/2
    let u := 1-c/2
    have hl : 0<l ∧ l<b := by dsimp [l]; constructor <;> linarith only [hb.1]
    have hu : 1-c<u ∧ u<1 := by dsimp [u]; constructor <;> linarith only [hc.1]
    have hprod : Icc l u ×ˢ ({0} : Set ℝ) ⊆ B.target := by
      rintro ⟨v,w⟩ ⟨hv,hw⟩
      obtain rfl := mem_singleton_iff.mp hw
      have hv0 : 0<v := hl.1.trans_le hv.1
      have hv1 : v<1 := hv.2.trans_lt hu.2
      let t : Interval := ⟨v,⟨hv0.le,hv1.le⟩⟩
      obtain ⟨ht,hcoord⟩ := hBcenter t hv0 hv1
      rw [← hcoord]
      exact B.map_source ht
    obtain ⟨U,V,hU,hV,hx,hy,hUV⟩ := generalized_tube_lemma
      (isCompact_Icc : IsCompact (Icc l u)) isCompact_singleton B.open_target hprod
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp
      (hV.mem_nhds (hy (mem_singleton 0)))
    refine ⟨l,u,ε/2,hl.1,hl.2,hu.1,hu.2,half_pos hε,?_⟩
    rintro ⟨v,w⟩ ⟨hv,hw⟩
    apply hUV
    refine ⟨hx hv,hball ?_⟩
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
    constructor <;> linarith only [hε,hw.1,hw.2]
  have actual_complete_terminal_port_coordinates
      (N : C(Interval × Icc (-1 : ℝ) 1,Q S x R))
      (hN : Topology.IsEmbedding N) (r : ℝ) (hr : 0<r ∧ r≤1)
      (hwhole : ∀ w : Icc (-1 : ℝ) 1,
        (N (1,⟨r*(w:ℝ),by constructor <;>
          nlinarith only [hr.1,hr.2,w.property.1,w.property.2]⟩)).val∈B.source) :
      ∃ P : C(Icc (-1 : ℝ) 1,ℝ × ℝ), Topology.IsEmbedding P ∧
        ∀ w,P w=B (N (1,⟨r*(w:ℝ),by constructor <;>
          nlinarith only [hr.1,hr.2,w.property.1,w.property.2]⟩)).val := by
    let k : Icc (-1 : ℝ) 1 → Interval × Icc (-1 : ℝ) 1 := fun w =>
      (1,⟨r*(w:ℝ),by constructor <;>
        nlinarith only [hr.1,hr.2,w.property.1,w.property.2]⟩)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      intro w v he
      have hh := congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => (z.2:ℝ)) he
      apply Subtype.ext
      change r*(w:ℝ)=r*(v:ℝ) at hh
      exact mul_left_cancel₀ (ne_of_gt hr.1) hh
    let f : Icc (-1 : ℝ) 1 → S := fun w => (N (k w)).val
    have hfc : Continuous f := continuous_subtype_val.comp (N.continuous.comp hkc)
    let P : C(Icc (-1 : ℝ) 1,ℝ × ℝ) :=
      ⟨B ∘ f,B.continuousOn.comp_continuous hfc hwhole⟩
    have hPi : Function.Injective P := by
      intro w v he
      have hf := B.injOn (hwhole w) (hwhole v) he
      exact hki (hN.injective (Subtype.ext hf))
    exact ⟨P,(P.continuous.isClosedEmbedding hPi).isEmbedding,fun _ => rfl⟩
  have actual_complete_terminal_coordinate_zero_trace
      (N : C(Interval × Icc (-1 : ℝ) 1,Q S x R))
      (hNa : ∀ z,N z∈Set.range a.val ↔ (z.2:ℝ)=0)
      (r : ℝ) (hr : 0<r ∧ r≤1)
      (hwhole : ∀ w : Icc (-1 : ℝ) 1,
        (N (1,⟨r*(w:ℝ),by constructor <;>
          nlinarith only [hr.1,hr.2,w.property.1,w.property.2]⟩)).val∈B.source)
      (P : C(Icc (-1 : ℝ) 1,ℝ × ℝ))
      (hP : ∀ w,P w=B (N (1,⟨r*(w:ℝ),by constructor <;>
        nlinarith only [hr.1,hr.2,w.property.1,w.property.2]⟩)).val) :
      ∀ w,(P w).2=0 ↔ (w:ℝ)=0 := by
    intro w
    rw [hP,← hBaxis _ (hwhole w)]
    have hmem (y : Q S x R) :
        y.val∈Set.range (fun t => (a.val t).val) ↔ y∈Set.range a.val := by
      constructor
      · rintro ⟨t,ht⟩
        exact ⟨t,Subtype.ext ht⟩
      · rintro ⟨t,ht⟩
        exact ⟨t,congrArg Subtype.val ht⟩
    rw [hmem,hNa]
    change r*(w:ℝ)=0 ↔ (w:ℝ)=0
    exact mul_eq_zero.trans (or_iff_right (ne_of_gt hr.1))
  have actual_scalar_positive_width_bounds (r : ℝ) (hr : 0<r ∧ r≤1) (t : Interval) :
      -1≤r*(t:ℝ) ∧ r*(t:ℝ)≤1 :=
    ⟨(show (-1:ℝ)≤0 by norm_num).trans (mul_nonneg hr.1.le t.property.1),
      mul_le_one₀ hr.2 t.property.1 t.property.2⟩
  have actual_scalar_negative_width_bounds (r : ℝ) (hr : 0<r ∧ r≤1) (t : Interval) :
      -1≤ -r*(t:ℝ) ∧ -r*(t:ℝ)≤1 := by
    have hp := actual_scalar_positive_width_bounds r hr t
    constructor <;> nlinarith only [hp.1,hp.2]
  have actual_signed_width_bounds (ε : ℝ) (hε : ε=1 ∨ ε= -1) (t : Interval) :
      -1≤ε*(t:ℝ) ∧ ε*(t:ℝ)≤1 := by
    rcases hε with rfl | rfl
    · simpa only [one_mul] using ⟨(by linarith only [t.property.1] : -1≤(t:ℝ)),t.property.2⟩
    · simpa only [neg_one_mul] using ⟨(by linarith only [t.property.2] : -1≤-(t:ℝ)),(by linarith only [t.property.1] : -(t:ℝ)≤1)⟩
  have actual_negative_signed_width_bounds (ε : ℝ) (hε : ε=1 ∨ ε= -1) (t : Interval) :
      -1≤-ε*(t:ℝ) ∧ -ε*(t:ℝ)≤1 := by
    have hp := actual_signed_width_bounds ε hε t
    constructor <;> nlinarith only [hp.1,hp.2]
  have actual_signed_terminal_bounds (ε : ℝ) (hε : ε=1 ∨ ε= -1) : -1≤ε ∧ ε≤1 := by
    rcases hε with rfl | rfl <;> norm_num
  have actual_negative_signed_terminal_bounds (ε : ℝ) (hε : ε=1 ∨ ε= -1) : -1≤-ε ∧ -ε≤1 := by
    rcases hε with rfl | rfl <;> norm_num
  have actual_sign_nonzero (ε : ℝ) (hε : ε=1 ∨ ε= -1) : ε≠0 := by
    rcases hε with rfl | rfl <;> norm_num
  have actual_signed_full_width_bounds (ε : ℝ) (hε : ε=1 ∨ ε= -1)
      (w : Icc (-1 : ℝ) 1) : -1≤ε*(w:ℝ) ∧ ε*(w:ℝ)≤1 := by
    rcases hε with rfl | rfl
    · simpa only [one_mul,Set.mem_Icc] using w.property
    · simpa only [neg_one_mul] using ⟨(by linarith only [w.property.2] : -1≤-(w:ℝ)),(by linarith only [w.property.1] : -(w:ℝ)≤1)⟩
  have actual_signed_complete_port_half_arcs (P : C(Icc (-1 : ℝ) 1,ℝ × ℝ))
      (hP : Topology.IsEmbedding P)
      (hzero : ∀ w,(P w).2=0 ↔ (w:ℝ)=0)
      (hside : (0<(P ⟨1,by norm_num⟩).2 ∧ (P ⟨-1,by norm_num⟩).2<0) ∨
        ((P ⟨1,by norm_num⟩).2<0 ∧ 0<(P ⟨-1,by norm_num⟩).2)) :
      ∃ ε : ℝ, ∃ hε : ε=1 ∨ ε= -1,
      ∃ U D : C(Interval,Schoenflies.Plane), Topology.IsEmbedding U ∧ Topology.IsEmbedding D ∧
        (∀ t,U t=Schoenflies.Plane.mk (P ⟨ε*(t:ℝ),actual_signed_width_bounds ε hε t⟩).1
          (P ⟨ε*(t:ℝ),actual_signed_width_bounds ε hε t⟩).2) ∧
        (∀ t,D t=Schoenflies.Plane.mk (P ⟨-ε*(t:ℝ),actual_negative_signed_width_bounds ε hε t⟩).1
          (-(P ⟨-ε*(t:ℝ),actual_negative_signed_width_bounds ε hε t⟩).2)) ∧
        (∀ t : Interval,0<(t:ℝ) → 0<U t 1 ∧ 0<D t 1) := by
    have make (ε : ℝ) (hε : ε=1 ∨ ε= -1)
        (hu : 0<(P ⟨ε,actual_signed_terminal_bounds ε hε⟩).2)
        (hd : (P ⟨-ε,actual_negative_signed_terminal_bounds ε hε⟩).2<0) :
        ∃ U D : C(Interval,Schoenflies.Plane), Topology.IsEmbedding U ∧ Topology.IsEmbedding D ∧
        (∀ t,U t=Schoenflies.Plane.mk (P ⟨ε*(t:ℝ),actual_signed_width_bounds ε hε t⟩).1
          (P ⟨ε*(t:ℝ),actual_signed_width_bounds ε hε t⟩).2) ∧
        (∀ t,D t=Schoenflies.Plane.mk (P ⟨-ε*(t:ℝ),actual_negative_signed_width_bounds ε hε t⟩).1
          (-(P ⟨-ε*(t:ℝ),actual_negative_signed_width_bounds ε hε t⟩).2)) ∧
        (∀ t : Interval,0<(t:ℝ) → 0<U t 1 ∧ 0<D t 1) := by
      let kp : Interval → Icc (-1 : ℝ) 1 := fun t => ⟨ε*(t:ℝ),actual_signed_width_bounds ε hε t⟩
      let km : Interval → Icc (-1 : ℝ) 1 := fun t => ⟨-ε*(t:ℝ),actual_negative_signed_width_bounds ε hε t⟩
      have he0 : ε≠0 := actual_sign_nonzero ε hε
      have kpC : Continuous kp := by dsimp [kp]; fun_prop
      have kmC : Continuous km := by dsimp [km]; fun_prop
      have kpI : Function.Injective kp := by
        intro t s he
        apply Subtype.ext
        exact mul_left_cancel₀ he0 (congrArg Subtype.val he)
      have kmI : Function.Injective km := by
        intro t s he
        apply Subtype.ext
        exact mul_left_cancel₀ (neg_ne_zero.mpr he0) (congrArg Subtype.val he)
      let U : C(Interval,Schoenflies.Plane) := ⟨fun t => Schoenflies.Plane.mk (P (kp t)).1 (P (kp t)).2,by fun_prop⟩
      let D : C(Interval,Schoenflies.Plane) := ⟨fun t => Schoenflies.Plane.mk (P (km t)).1 (-(P (km t)).2),by fun_prop⟩
      have hU : Topology.IsEmbedding U := by
        apply (U.continuous.isClosedEmbedding ?_).isEmbedding
        intro t s he
        apply kpI
        apply hP.injective
        apply Prod.ext
        · exact congrArg (fun z : Schoenflies.Plane => z 0) he
        · exact congrArg (fun z : Schoenflies.Plane => z 1) he
      have hD : Topology.IsEmbedding D := by
        apply (D.continuous.isClosedEmbedding ?_).isEmbedding
        intro t s he
        apply kmI
        apply hP.injective
        apply Prod.ext
        · exact congrArg (fun z : Schoenflies.Plane => z 0) he
        · exact neg_injective (congrArg (fun z : Schoenflies.Plane => z 1) he)
      have hUz : ∀ t,U t 1=0 ↔ t=0 := by
        intro t
        change (P (kp t)).2=0 ↔ t=0
        rw [hzero]
        change ε*(t:ℝ)=0 ↔ t=0
        rw [mul_eq_zero,or_iff_right he0]
        constructor
        · intro he; exact Subtype.ext he
        · intro he; exact congrArg Subtype.val he
      have hDz : ∀ t,D t 1=0 ↔ t=0 := by
        intro t
        change -(P (km t)).2=0 ↔ t=0
        rw [neg_eq_zero,hzero]
        change -ε*(t:ℝ)=0 ↔ t=0
        rw [mul_eq_zero,or_iff_right (neg_ne_zero.mpr he0)]
        constructor
        · intro he; exact Subtype.ext he
        · intro he; exact congrArg Subtype.val he
      have hUend : 0<U 1 1 := by simpa [U,kp] using hu
      have hDend : 0<D 1 1 := by
        have hh : 0< -(P ⟨-ε,actual_negative_signed_terminal_bounds ε hε⟩).2 := neg_pos.mpr hd
        simpa [D,km] using hh
      refine ⟨U,D,hU,hD,fun _ => rfl,fun _ => rfl,?_⟩
      intro t ht
      exact ⟨actual_half_port_positive_side_retention U hUz hUend t ht,
        actual_half_port_positive_side_retention D hDz hDend t ht⟩
    rcases hside with hh | hh
    · obtain ⟨U,D,hU,hD,hUl,hDl,hpos⟩ := make 1 (Or.inl rfl) hh.1 (by simpa using hh.2)
      exact ⟨1,Or.inl rfl,U,D,hU,hD,hUl,hDl,hpos⟩
    · obtain ⟨U,D,hU,hD,hUl,hDl,hpos⟩ := make (-1) (Or.inr rfl) hh.2 (by simpa using hh.1)
      exact ⟨-1,Or.inr rfl,U,D,hU,hD,hUl,hDl,hpos⟩
  have actual_complete_port_horizontal_slab (P : C(Icc (-1 : ℝ) 1,ℝ × ℝ)) (x l u : ℝ)
      (hP0 : P ⟨0,by norm_num⟩=(x,0)) (hx : l<x ∧ x<u) :
      ∃ r : ℝ, ∃ hr : 0<r ∧ r≤1,
        ∀ w : Icc (-1 : ℝ) 1,
          l<(P ⟨r*(w:ℝ),by constructor <;>
            nlinarith only [hr.1,hr.2,w.property.1,w.property.2]⟩).1 ∧
          (P ⟨r*(w:ℝ),by constructor <;>
            nlinarith only [hr.1,hr.2,w.property.1,w.property.2]⟩).1<u := by
    let O : Set (ℝ × ℝ) := Prod.fst ⁻¹' Ioo l u
    have hO : IsOpen O := isOpen_Ioo.preimage continuous_fst
    have hz : (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1) ∈ P ⁻¹' O := by
      change l<(P ⟨0,by norm_num⟩).1 ∧ (P ⟨0,by norm_num⟩).1<u
      rw [hP0]
      exact hx
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ((hO.preimage P.continuous).mem_nhds hz)
    let r := min (ε/2) (1/2)
    have hr0 : 0<r := lt_min (half_pos hε) (by norm_num)
    have hr1 : r≤1 := (min_le_right _ _).trans (by norm_num)
    have hrε : r<ε := (min_le_left _ _).trans_lt (by linarith)
    refine ⟨r,⟨hr0,hr1⟩,?_⟩
    intro w
    apply hball
    change dist (r*(w:ℝ)) (0:ℝ)<ε
    rw [Real.dist_eq,sub_zero,abs_mul,abs_of_pos hr0]
    have hw : abs (w:ℝ)≤1 := abs_le.mpr w.property
    calc
      r*abs (w:ℝ) ≤ r*1 := mul_le_mul_of_nonneg_left hw hr0.le
      _ < ε := by simpa only [mul_one] using hrε
  have actual_source_positive_ports_localized_rectangle
      (P Q : C(Interval,Schoenflies.Plane)) (hP : Topology.IsEmbedding P) (hQ : Topology.IsEmbedding Q)
      (a b δ l u : ℝ) (hab : a<b) (hδ : 0<δ)
      (hP0 : P 0=Schoenflies.Plane.mk a 0) (hQ0 : Q 0=Schoenflies.Plane.mk b 0)
      (hPpos : ∀ t : Interval,0<(t:ℝ) → 0<P t 1)
      (hQpos : ∀ t : Interval,0<(t:ℝ) → 0<Q t 1)
      (hδP : δ<P 1 1) (hδQ : δ<Q 1 1)
      (hseparate : ∀ s t,P s 0<Q t 0)
      (hPloc : ∀ t,l≤P t 0 ∧ P t 0≤u)
      (hQloc : ∀ t,l≤Q t 0 ∧ Q t 0≤u) :
      ∃ τ σ : Interval, 0<(τ:ℝ) ∧ 0<(σ:ℝ) ∧
        (∀ t : Interval,0<(t:ℝ) → (t:ℝ)<1 →
          0<P ⟨(τ:ℝ)*(t:ℝ),actual_unit_interval_product_bounds τ t⟩ 1 ∧
          P ⟨(τ:ℝ)*(t:ℝ),actual_unit_interval_product_bounds τ t⟩ 1<δ) ∧
        (∀ t : Interval,0<(t:ℝ) → (t:ℝ)<1 →
          0<Q ⟨(σ:ℝ)*(t:ℝ),actual_unit_interval_product_bounds σ t⟩ 1 ∧
          Q ⟨(σ:ℝ)*(t:ℝ),actual_unit_interval_product_bounds σ t⟩ 1<δ) ∧
      ∃ B : Interval × Interval → Schoenflies.Plane, Topology.IsEmbedding B ∧
        (∀ t,B (t,0)=Schoenflies.Plane.mk (a+(b-a)*(t:ℝ)) 0) ∧
        (∀ t,B (0,t)=P ⟨(τ:ℝ)*(t:ℝ),actual_unit_interval_product_bounds τ t⟩) ∧
        (∀ t,B (1,t)=Q ⟨(σ:ℝ)*(t:ℝ),actual_unit_interval_product_bounds σ t⟩) ∧
        (∀ t,B (t,1)=Schoenflies.Plane.mk (P τ 0+(Q σ 0-P τ 0)*(t:ℝ)) δ) ∧
        (∀ z,l≤B z 0 ∧ B z 0≤u ∧ 0≤B z 1 ∧ B z 1≤δ) ∧
        (∀ z,B z 1=0 ↔ z.2=0) := by
    have hPzero : P 0 1=0 := by rw [hP0]; rfl
    have hQzero : Q 0 1=0 := by rw [hQ0]; rfl
    obtain ⟨τ,hτ,E,hE,hElit,hE0,hE1,hEint,hEz,hEh⟩ :=
      actual_positive_port_first_height P hP hPzero hPpos δ hδ hδP
    obtain ⟨σ,hσ,R,hR,hRlit,hR0,hR1,hRint,hRz,hRh⟩ :=
      actual_positive_port_first_height Q hQ hQzero hQpos δ hδ hδQ
    have hEone : E 1=P τ := by rw [hElit]; apply congrArg P; apply Subtype.ext; simp
    have hRone : R 1=Q σ := by rw [hRlit]; apply congrArg Q; apply Subtype.ext; simp
    have hER : Disjoint (Set.range E) (Set.range R) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨s,rfl⟩ ⟨t,he⟩
      have hh := hseparate
        ⟨(τ:ℝ)*(s:ℝ),actual_unit_interval_product_bounds τ s⟩
        ⟨(σ:ℝ)*(t:ℝ),actual_unit_interval_product_bounds σ t⟩
      rw [← hElit,← hRlit] at hh
      rw [he] at hh
      exact lt_irrefl _ hh
    have hupper : E 1 0<R 1 0 := by rw [hEone,hRone]; exact hseparate τ σ
    obtain ⟨C,D,hC,hD,hClit,hDlit,hCE,hCR,hDE,hDR,hCD,B,hB,hBC,hBD,hBE,hBR⟩ :=
      actual_first_height_ports_prescribed_upper_rectangle E R hE hR a b δ hab hδ
        (hE0.trans hP0) (hR0.trans hQ0) hEz hRz hEh hRh hupper hER
    have hEall (t : Interval) : 0≤E t 1 ∧ E t 1≤δ := by
      by_cases ht0 : t=0
      · rw [ht0,hE0,hPzero]; exact ⟨le_refl _,hδ.le⟩
      by_cases ht1 : t=1
      · rw [ht1,hE1]; exact ⟨hδ.le,le_refl _⟩
      have hh := hEint t
        (lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm)))
        (lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he)))
      exact ⟨hh.1.le,hh.2.le⟩
    have hRall (t : Interval) : 0≤R t 1 ∧ R t 1≤δ := by
      by_cases ht0 : t=0
      · rw [ht0,hR0,hQzero]; exact ⟨le_refl _,hδ.le⟩
      by_cases ht1 : t=1
      · rw [ht1,hR1]; exact ⟨hδ.le,le_refl _⟩
      have hh := hRint t
        (lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm)))
        (lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he)))
      exact ⟨hh.1.le,hh.2.le⟩
    have hCy : ∀ t,C t 1=0 := by intro t; rw [hClit]; rfl
    have hDy : ∀ t,D t 1=δ := by intro t; rw [hDlit]; rfl
    have hEslab : ∀ t,l≤E t 0 ∧ E t 0≤u := by intro t; rw [hElit]; exact hPloc _
    have hRslab : ∀ t,l≤R t 0 ∧ R t 0≤u := by intro t; rw [hRlit]; exact hQloc _
    have haslab : l≤a ∧ a≤u := by simpa [hP0,Schoenflies.Plane.mk] using hPloc 0
    have hbslab : l≤b ∧ b≤u := by simpa [hQ0,Schoenflies.Plane.mk] using hQloc 0
    have hCslab (t : Interval) : l≤C t 0 ∧ C t 0≤u := by
      rw [hClit]
      change l≤a+(b-a)*(t:ℝ) ∧ a+(b-a)*(t:ℝ)≤u
      constructor <;> nlinarith only [haslab.1,haslab.2,hbslab.1,hbslab.2,t.property.1,t.property.2]
    have hDslab (t : Interval) : l≤D t 0 ∧ D t 0≤u := by
      rw [hDlit]
      change l≤E 1 0+(R 1 0-E 1 0)*(t:ℝ) ∧ E 1 0+(R 1 0-E 1 0)*(t:ℝ)≤u
      constructor <;> nlinarith only [(hEslab 1).1,(hEslab 1).2,(hRslab 1).1,(hRslab 1).2,t.property.1,t.property.2]
    have hboundary (z : Interval × Interval)
        (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
        l≤B z 0 ∧ B z 0≤u ∧ 0≤B z 1 ∧ B z 1≤δ := by
      rcases hz with hz|hz|hz|hz
      · have he : z=(0,z.2) := Prod.ext hz rfl
        rw [he,hBE]
        exact ⟨(hEslab _).1,(hEslab _).2,(hEall _).1,(hEall _).2⟩
      · have he : z=(1,z.2) := Prod.ext hz rfl
        rw [he,hBR]
        exact ⟨(hRslab _).1,(hRslab _).2,(hRall _).1,(hRall _).2⟩
      · have he : z=(z.1,0) := Prod.ext rfl hz
        rw [he,hBC,hCy]
        exact ⟨(hCslab _).1,(hCslab _).2,le_refl _,hδ.le⟩
      · have he : z=(z.1,1) := Prod.ext rfl hz
        rw [he,hBD,hDy]
        exact ⟨(hDslab _).1,(hDslab _).2,hδ.le,le_refl _⟩
    have hall (z : Interval × Interval) : l≤B z 0 ∧ B z 0≤u ∧ 0≤B z 1 ∧ B z 1≤δ :=
      ⟨actual_embedded_rectangle_coordinate_lower_bound B hB 0 l (fun z hz => (hboundary z hz).1) z,
       actual_embedded_rectangle_coordinate_upper_bound B hB 0 u (fun z hz => (hboundary z hz).2.1) z,
       actual_embedded_rectangle_coordinate_lower_bound B hB 1 0 (fun z hz => (hboundary z hz).2.2.1) z,
       actual_embedded_rectangle_coordinate_upper_bound B hB 1 δ (fun z hz => (hboundary z hz).2.2.2) z⟩
    refine ⟨τ,σ,hτ,hσ,?_,?_,B,hB,fun t => (hBC t).trans (hClit t),
      fun t => (hBE t).trans (hElit t),fun t => (hBR t).trans (hRlit t),?_,hall,?_⟩
    · intro t ht0 ht1
      have hh := hEint t ht0 ht1
      simpa only [hElit] using hh
    · intro t ht0 ht1
      have hh := hRint t ht0 ht1
      simpa only [hRlit] using hh
    · intro t
      rw [hBD,hDlit,hEone,hRone]
    · intro z
      constructor
      · intro hz
        rcases actual_embedded_rectangle_coordinate_equality_on_boundary B hB 1 0
          (fun z => (hall z).2.2.1) z hz with he|he|he|he
        · have hzz : z=(0,z.2) := Prod.ext he rfl
          rw [hzz,hBE] at hz
          exact (hEz _).mp hz
        · have hzz : z=(1,z.2) := Prod.ext he rfl
          rw [hzz,hBR] at hz
          exact (hRz _).mp hz
        · exact he
        · have hzz : z=(z.1,1) := Prod.ext rfl he
          rw [hzz,hBD,hDy] at hz
          linarith
      · intro hz
        have hzz : z=(z.1,0) := Prod.ext rfl hz
        rw [hzz,hBC,hCy]
  obtain ⟨PL,hPL,hPLliteral⟩ :=
    actual_complete_terminal_port_coordinates L hL rL hrL hLwhole
  obtain ⟨PR,hPR,hPRliteral⟩ :=
    actual_complete_terminal_port_coordinates Rband hRband rR hrR hRwhole
  have hPLzero := actual_complete_terminal_coordinate_zero_trace
    L hLavoid rL hrL hLwhole PL hPLliteral
  have hPRzero := actual_complete_terminal_coordinate_zero_trace
    Rband hRavoid rR hrR hRwhole PR hPRliteral
  have hPLside : (0<(PL ⟨1,by norm_num⟩).2 ∧ (PL ⟨-1,by norm_num⟩).2<0) ∨
      ((PL ⟨1,by norm_num⟩).2<0 ∧ 0<(PL ⟨-1,by norm_num⟩).2) := by
    simpa only [hPLliteral,mul_one,mul_neg_one] using hLside
  have hPRside : (0<(PR ⟨1,by norm_num⟩).2 ∧ (PR ⟨-1,by norm_num⟩).2<0) ∨
      ((PR ⟨1,by norm_num⟩).2<0 ∧ 0<(PR ⟨-1,by norm_num⟩).2) := by
    simpa only [hPRliteral,mul_one,mul_neg_one] using hRside
  obtain ⟨εL,hεL,UPL,DPL,hUPL,hDPL,hUPLliteral,hDPLliteral,hLpositive⟩ :=
    actual_signed_complete_port_half_arcs PL hPL hPLzero hPLside
  obtain ⟨εR,hεR,UPR,DPR,hUPR,hDPR,hUPRliteral,hDPRliteral,hRpositive⟩ :=
    actual_signed_complete_port_half_arcs PR hPR hPRzero hPRside
  have hPL0 : PL ⟨0,by norm_num⟩=(b,0) := by
    simpa only [hPLliteral,mul_zero] using hBL0
  have hPR0 : PR ⟨0,by norm_num⟩=(1-c,0) := by
    simpa only [hPRliteral,mul_zero] using hBR0
  obtain ⟨l,u,δbox,hl0,hlb,hrightu,hu1,hδbox,hbox⟩ := actual_original_middle_chart_box
  let mid := (b+(1-c))/2
  have hbmid : b < mid := by dsimp [mid]; linarith only [hgap]
  have hmidR : mid < 1-c := by dsimp [mid]; linarith only [hgap]
  obtain ⟨ρL,hρL,hPLslab⟩ := actual_complete_port_horizontal_slab PL b l mid hPL0 ⟨hlb,hbmid⟩
  obtain ⟨ρR,hρR,hPRslab⟩ := actual_complete_port_horizontal_slab PR (1-c) mid u hPR0 ⟨hmidR,hrightu⟩
  have actual_positive_half_port_scaled
      (P : C(Interval,Schoenflies.Plane)) (hP : Topology.IsEmbedding P)
      (hpos : ∀ t : Interval,0<(t:ℝ) → 0<P t 1)
      (ρ : ℝ) (hρ : 0<ρ ∧ ρ≤1) :
      ∃ E : C(Interval,Schoenflies.Plane), Topology.IsEmbedding E ∧
        (∀ t,E t=P ⟨ρ*(t:ℝ),by constructor <;>
          nlinarith only [hρ.1,hρ.2,t.property.1,t.property.2]⟩) ∧
        (∀ t : Interval,0<(t:ℝ) → 0<E t 1) := by
    let k : Interval → Interval := fun t => ⟨ρ*(t:ℝ),by
      constructor <;> nlinarith only [hρ.1,hρ.2,t.property.1,t.property.2]⟩
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      intro t u he
      apply Subtype.ext
      exact mul_left_cancel₀ (ne_of_gt hρ.1) (congrArg Subtype.val he)
    let E : C(Interval,Schoenflies.Plane) := ⟨P ∘ k,P.continuous.comp hkc⟩
    refine ⟨E,(E.continuous.isClosedEmbedding (hP.injective.comp hki)).isEmbedding,
      fun _ => rfl,?_⟩
    intro t ht
    exact hpos (k t) (mul_pos hρ.1 ht)
  obtain ⟨Pup,hPup,hPupliteral,hPuppos⟩ := actual_positive_half_port_scaled UPL hUPL
    (fun t ht => (hLpositive t ht).1) ρL hρL
  obtain ⟨Pdown,hPdown,hPdownliteral,hPdownpos⟩ := actual_positive_half_port_scaled DPL hDPL
    (fun t ht => (hLpositive t ht).2) ρL hρL
  obtain ⟨Qup,hQup,hQupliteral,hQuppos⟩ := actual_positive_half_port_scaled UPR hUPR
    (fun t ht => (hRpositive t ht).1) ρR hρR
  obtain ⟨Qdown,hQdown,hQdownliteral,hQdownpos⟩ := actual_positive_half_port_scaled DPR hDPR
    (fun t ht => (hRpositive t ht).2) ρR hρR
  have hPupslab (t : Interval) : l<Pup t 0 ∧ Pup t 0 < mid := by
    simpa only [hPupliteral,hUPLliteral,Schoenflies.Plane.mk,Matrix.cons_val_zero,mul_left_comm] using
      hPLslab ⟨εL*(t:ℝ),actual_signed_width_bounds εL hεL t⟩
  have hPdownslab (t : Interval) : l<Pdown t 0 ∧ Pdown t 0 < mid := by
    simpa only [hPdownliteral,hDPLliteral,Schoenflies.Plane.mk,Matrix.cons_val_zero,mul_left_comm] using
      hPLslab ⟨-εL*(t:ℝ),actual_negative_signed_width_bounds εL hεL t⟩
  have hQupslab (t : Interval) : mid<Qup t 0 ∧ Qup t 0<u := by
    simpa only [hQupliteral,hUPRliteral,Schoenflies.Plane.mk,Matrix.cons_val_zero,mul_left_comm] using
      hPRslab ⟨εR*(t:ℝ),actual_signed_width_bounds εR hεR t⟩
  have hQdownslab (t : Interval) : mid<Qdown t 0 ∧ Qdown t 0<u := by
    simpa only [hQdownliteral,hDPRliteral,Schoenflies.Plane.mk,Matrix.cons_val_zero,mul_left_comm] using
      hPRslab ⟨-εR*(t:ℝ),actual_negative_signed_width_bounds εR hεR t⟩
  have hPup0 : Pup 0=Schoenflies.Plane.mk b 0 := by
    simp only [hPupliteral,hUPLliteral,show ((0:Interval):ℝ)=0 from rfl,mul_zero,hPL0,neg_zero]
  have hPdown0 : Pdown 0=Schoenflies.Plane.mk b 0 := by
    simp only [hPdownliteral,hDPLliteral,show ((0:Interval):ℝ)=0 from rfl,mul_zero,hPL0,neg_zero]
  have hQup0 : Qup 0=Schoenflies.Plane.mk (1-c) 0 := by
    simp only [hQupliteral,hUPRliteral,show ((0:Interval):ℝ)=0 from rfl,mul_zero,hPR0,neg_zero]
  have hQdown0 : Qdown 0=Schoenflies.Plane.mk (1-c) 0 := by
    simp only [hQdownliteral,hDPRliteral,show ((0:Interval):ℝ)=0 from rfl,mul_zero,hPR0,neg_zero]
  let κ := min δbox (min (Pup 1 1) (min (Qup 1 1) (min (Pdown 1 1) (Qdown 1 1))))
  have hκ : 0<κ := lt_min hδbox (lt_min (hPuppos 1 (by norm_num))
    (lt_min (hQuppos 1 (by norm_num)) (lt_min (hPdownpos 1 (by norm_num))
      (hQdownpos 1 (by norm_num)))))
  let δ := κ/2
  have hδ : 0<δ := half_pos hκ
  have hδκ : δ<κ := half_lt_self hκ
  have hδsmall : δ<δbox := hδκ.trans_le (min_le_left _ _)
  have hδPup : δ<Pup 1 1 := hδκ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδQup : δ<Qup 1 1 := hδκ.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδPdown : δ<Pdown 1 1 := hδκ.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδQdown : δ<Qdown 1 1 := hδκ.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hhab : b<1-c := by linarith only [hgap]
  have hlocPup (t) : l≤Pup t 0 ∧ Pup t 0≤u :=
    ⟨(hPupslab t).1.le,((hPupslab t).2.trans (hmidR.trans hrightu)).le⟩
  have hlocQup (t) : l≤Qup t 0 ∧ Qup t 0≤u :=
    ⟨((hlb.trans hbmid).trans (hQupslab t).1).le,(hQupslab t).2.le⟩
  have hlocPdown (t) : l≤Pdown t 0 ∧ Pdown t 0≤u :=
    ⟨(hPdownslab t).1.le,((hPdownslab t).2.trans (hmidR.trans hrightu)).le⟩
  have hlocQdown (t) : l≤Qdown t 0 ∧ Qdown t 0≤u :=
    ⟨((hlb.trans hbmid).trans (hQdownslab t).1).le,(hQdownslab t).2.le⟩
  obtain ⟨τp,σp,hτp,hσp,hPuptrim,hQuptrim,U,hU,hUcenter,hUleft,hUright,hUtop,hUloc,hUzero⟩ :=
    actual_source_positive_ports_localized_rectangle Pup Qup hPup hQup b (1-c) δ l u hhab hδ
      hPup0 hQup0 hPuppos hQuppos hδPup hδQup
      (fun t v => (hPupslab t).2.trans (hQupslab v).1) hlocPup hlocQup
  obtain ⟨τm,σm,hτm,hσm,hPdowntrim,hQdowntrim,V,hV,hVcenter,hVleft,hVright,hVtop,hVloc,hVzero⟩ :=
    actual_source_positive_ports_localized_rectangle Pdown Qdown hPdown hQdown b (1-c) δ l u hhab hδ
      hPdown0 hQdown0 hPdownpos hQdownpos hδPdown hδQdown
      (fun t v => (hPdownslab t).2.trans (hQdownslab v).1) hlocPdown hlocQdown
  let planeReflect : Schoenflies.Plane → Schoenflies.Plane := fun p => Schoenflies.Plane.mk (p 0) (-(p 1))
  have hrc : Continuous planeReflect := by dsimp [planeReflect]; fun_prop
  have hri : Function.Injective planeReflect := by
    intro p q he
    have hh0 := congrArg (fun p : Schoenflies.Plane => p 0) he
    have hh1 := congrArg (fun p : Schoenflies.Plane => p 1) he
    ext i; fin_cases i
    · exact hh0
    · change p 1 = q 1
      exact neg_injective hh1
  let Lower := planeReflect ∘ V
  have hD : Topology.IsEmbedding Lower := ((hrc.comp hV.continuous).isClosedEmbedding
    (hri.comp hV.injective)).isEmbedding
  let Center : Interval → Schoenflies.Plane := fun t => Schoenflies.Plane.mk (b+(1-c-b)*(t:ℝ)) 0
  have hDcenter : ∀ t,Lower (t,0)=Center t := by
    intro t
    change planeReflect (V (t,0))=Center t
    rw [hVcenter]
    ext i; fin_cases i <;> simp [planeReflect,Center,Schoenflies.Plane.mk]
  have hDy : ∀ z,Lower z 1≤0 := by
    intro z
    change -(V z 1)≤0
    linarith only [(hVloc z).2.2.1]
  have hDz : ∀ z,Lower z 1=0 ↔ z.2=0 := by
    intro z
    change -(V z 1)=0 ↔ z.2=0
    rw [neg_eq_zero,hVzero]
  obtain ⟨F,hF,hFc,hFval,hFrange,hFzero⟩ :=
    actual_opposite_rectangles_literal_center_full_strip U Lower hU hD Center hUcenter hDcenter
      (fun z => (hUloc z).2.2.1) hDy hUzero hDz
  have hFloc (z) : l≤F z 0 ∧ F z 0≤u ∧ -δ≤F z 1 ∧ F z 1≤δ := by
    have hh : F z∈Set.range U ∪ Set.range Lower := hFrange ▸ Set.mem_range_self z
    rcases hh with ⟨v,hv⟩ | ⟨v,hv⟩
    · rw [← hv]
      have hvloc := hUloc v
      exact ⟨hvloc.1,hvloc.2.1,by linarith only [hδ,hvloc.2.2.1],hvloc.2.2.2⟩
    · rw [← hv]
      have hvloc := hVloc v
      change l≤V v 0 ∧ V v 0≤u ∧ -δ≤ -(V v 1) ∧ -(V v 1)≤δ
      exact ⟨hvloc.1,hvloc.2.1,by linarith only [hvloc.2.2.2],by linarith only [hδ,hvloc.2.2.1]⟩
  let coords : Interval × Icc (-1 : ℝ) 1 → ℝ × ℝ := fun z => (F z 0,F z 1)
  have hcoordsc : Continuous coords := by dsimp [coords]; fun_prop
  have hcoordst (z) : coords z∈B.target := by
    apply hbox
    have hz := hFloc z
    exact ⟨⟨hz.1,hz.2.1⟩,⟨by linarith only [hδsmall,hz.2.2.1],by linarith only [hδsmall,hz.2.2.2]⟩⟩
  let middlePoint : Interval × Icc (-1 : ℝ) 1 → S := B.symm ∘ coords
  have hmiddlec : Continuous middlePoint := B.symm.continuousOn.comp_continuous hcoordsc hcoordst
  have hmiddles (z) : middlePoint z∈B.source := B.symm.map_source (hcoordst z)
  have hmiddleQ (z) : middlePoint z∈(openDisk S x R)ᶜ := by
    rintro ⟨v,hv,he⟩
    exact hBout (hmiddles z) ⟨v,Metric.mem_closedBall.mpr (Metric.mem_ball.mp hv).le,he⟩
  let M : C(Interval × Icc (-1 : ℝ) 1,Q S x R) :=
    ⟨fun z => ⟨middlePoint z,hmiddleQ z⟩,hmiddlec.subtype_mk _⟩
  have hMcoord (z) : B (M z).val=coords z := B.right_inv (hcoordst z)
  have hM : Topology.IsEmbedding M := by
    apply (M.continuous.isClosedEmbedding ?_).isEmbedding
    intro z v he
    apply hF.injective
    have hc := congrArg (fun y : Q S x R => B y.val) he
    rw [hMcoord,hMcoord] at hc
    have h0 := congrArg Prod.fst hc
    have h1 := congrArg Prod.snd hc
    ext i
    fin_cases i <;> assumption
  have hMboundary (z) : M z∉boundaryQ S x R := by
    rintro ⟨v,hv,he⟩
    exact hBout (hmiddles z) ⟨v,Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hv).le,he⟩
  have hMaxis (z) : M z∈Set.range a.val ↔ (z.2:ℝ)=0 := by
    have hmem : (M z).val∈Set.range (fun t => (a.val t).val) ↔ M z∈Set.range a.val := by
      constructor
      · rintro ⟨t,ht⟩; exact ⟨t,Subtype.ext ht⟩
      · rintro ⟨t,ht⟩; exact ⟨t,congrArg Subtype.val ht⟩
    exact hmem.symm.trans ((hBaxis (M z).val (hmiddles z)).trans
      (by rw [hMcoord]; exact hFzero z))
  have actual_width_oriented_endpoint_band
      (N : C(Interval × Icc (-1 : ℝ) 1,Q S x R))
      (hN : Topology.IsEmbedding N) (ε : ℝ) (hε : ε=1 ∨ ε= -1) :
      ∃ E : C(Interval × Icc (-1 : ℝ) 1,Q S x R), Topology.IsEmbedding E ∧
        (∀ z,E z=N (z.1,⟨ε*(z.2:ℝ),actual_signed_full_width_bounds ε hε z.2⟩)) ∧
        Set.range E ⊆ Set.range N ∧
        (∀ t,E (t,⟨0,by norm_num⟩)=N (t,⟨0,by norm_num⟩)) := by
    let k : Interval × Icc (-1 : ℝ) 1 → Interval × Icc (-1 : ℝ) 1 := fun z =>
      (z.1,⟨ε*(z.2:ℝ),actual_signed_full_width_bounds ε hε z.2⟩)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have he0 : ε≠0 := actual_sign_nonzero ε hε
    have hki : Function.Injective k := by
      intro z v he
      have hfst := congrArg Prod.fst he
      have hsnd := congrArg (fun p : Interval × Icc (-1 : ℝ) 1 => (p.2:ℝ)) he
      exact Prod.ext hfst (Subtype.ext (mul_left_cancel₀ he0 hsnd))
    let E : C(Interval × Icc (-1 : ℝ) 1,Q S x R) := ⟨N ∘ k,N.continuous.comp hkc⟩
    refine ⟨E,(E.continuous.isClosedEmbedding (hN.injective.comp hki)).isEmbedding,
      fun _ => rfl,?_,?_⟩
    · rintro y ⟨z,rfl⟩
      exact Set.mem_range_self (k z)
    · intro t
      apply congrArg N
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact mul_zero ε
  obtain ⟨OL,hOL,hOLliteral,hOLsubset,hOLcenter⟩ := actual_width_oriented_endpoint_band L hL εL hεL
  obtain ⟨OR,hOR,hORliteral,hORsubset,hORcenter⟩ := actual_width_oriented_endpoint_band Rband hRband εR hεR
  have hOLR : Disjoint (Set.range OL) (Set.range OR) := hLR.mono hOLsubset hORsubset
  have hOLboundary (w) : OL (0,w)∈boundaryQ S x R := by
    rw [hOLliteral]
    exact (hboundary _).1
  have hORboundary (w) : OR (0,w)∈boundaryQ S x R := by
    rw [hORliteral]
    exact (hboundary _).2
  have hOLinterior (t : Interval) (ht : 0<(t:ℝ)) (w) : OL (t,w)∉boundaryQ S x R := by
    rw [hOLliteral]
    exact (hinterior t ht _).1
  have hORinterior (t : Interval) (ht : 0<(t:ℝ)) (w) : OR (t,w)∉boundaryQ S x R := by
    rw [hORliteral]
    exact (hinterior t ht _).2
  have hOLaxis (z) : OL z∈Set.range a.val ↔ (z.2:ℝ)=0 := by
    rw [hOLliteral,hLavoid]
    change εL*(z.2:ℝ)=0 ↔ (z.2:ℝ)=0
    have hε : εL≠0 := actual_sign_nonzero εL hεL
    exact mul_eq_zero.trans (or_iff_right hε)
  have hORaxis (z) : OR z∈Set.range a.val ↔ (z.2:ℝ)=0 := by
    rw [hORliteral,hRavoid]
    change εR*(z.2:ℝ)=0 ↔ (z.2:ℝ)=0
    have hε : εR≠0 := actual_sign_nonzero εR hεR
    exact mul_eq_zero.trans (or_iff_right hε)
  let widthTop : Icc (-1 : ℝ) 1 := ⟨1,by norm_num⟩
  let widthBottom : Icc (-1 : ℝ) 1 := ⟨-1,by norm_num⟩
  let JoinUp : C(Interval,Q S x R) :=
    ⟨fun t => M (t,widthTop),M.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let JoinDown : C(Interval,Q S x R) :=
    ⟨fun t => M (t,widthBottom),M.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hFtop (t : Interval) : F (t,widthTop)=U (t,1) := by
    rw [hFval]
    change (if (1:ℝ)≤0 then Lower (t,projIcc 0 1 zero_le_one (-1)) else
      U (t,projIcc 0 1 zero_le_one 1))=U (t,1)
    simp
  have hFbottom (t : Interval) : F (t,widthBottom)=Lower (t,1) := by
    rw [hFval]
    change (if (-1:ℝ)≤0 then Lower (t,projIcc 0 1 zero_le_one (-(-1))) else
      U (t,projIcc 0 1 zero_le_one (-1)))=Lower (t,1)
    simp
  have hJoinUp (t : Interval) : (JoinUp t).val∈B.source ∧ (B (JoinUp t).val).2=δ := by
    refine ⟨hmiddles (t,widthTop),?_⟩
    change (B (M (t,widthTop)).val).2=δ
    rw [hMcoord]
    change F (t,widthTop) 1=δ
    rw [hFtop,hUtop]
    rfl
  have hJoinDown (t : Interval) : (JoinDown t).val∈B.source ∧ (B (JoinDown t).val).2= -δ := by
    refine ⟨hmiddles (t,widthBottom),?_⟩
    change (B (M (t,widthBottom)).val).2= -δ
    rw [hMcoord]
    change F (t,widthBottom) 1= -δ
    rw [hFbottom]
    change -(V (t,1) 1)= -δ
    rw [hVtop]
    rfl
  let rpL := rL*ρL*(τp:ℝ)
  let rmL := rL*ρL*(τm:ℝ)
  let rpR := rR*ρR*(σp:ℝ)
  let rmR := rR*ρR*(σm:ℝ)
  have hrpL : 0<rpL ∧ rpL≤1 := by
    dsimp [rpL]
    constructor
    · exact mul_pos (mul_pos hrL.1 hρL.1) hτp
    · exact mul_le_one₀ (mul_le_one₀ hrL.2 hρL.1.le hρL.2) τp.property.1 τp.property.2
  have hrmL : 0<rmL ∧ rmL≤1 := by
    dsimp [rmL]
    constructor
    · exact mul_pos (mul_pos hrL.1 hρL.1) hτm
    · exact mul_le_one₀ (mul_le_one₀ hrL.2 hρL.1.le hρL.2) τm.property.1 τm.property.2
  have hrpR : 0<rpR ∧ rpR≤1 := by
    dsimp [rpR]
    constructor
    · exact mul_pos (mul_pos hrR.1 hρR.1) hσp
    · exact mul_le_one₀ (mul_le_one₀ hrR.2 hρR.1.le hρR.2) σp.property.1 σp.property.2
  have hrmR : 0<rmR ∧ rmR≤1 := by
    dsimp [rmR]
    constructor
    · exact mul_pos (mul_pos hrR.1 hρR.1) hσm
    · exact mul_le_one₀ (mul_le_one₀ hrR.2 hρR.1.le hρR.2) σm.property.1 σm.property.2
  have hLplusclock (t : Interval) :
      B (OL (1,⟨rpL*(t:ℝ),actual_scalar_positive_width_bounds rpL hrpL t⟩)).val =
      ((Pup ⟨(τp:ℝ)*(t:ℝ),actual_unit_interval_product_bounds τp t⟩) 0,(Pup ⟨(τp:ℝ)*(t:ℝ),actual_unit_interval_product_bounds τp t⟩) 1) := by
    simp only [hPupliteral,hUPLliteral]
    simp only [planeReflect,Schoenflies.Plane.mk,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,neg_neg]
    rw [hPLliteral,hOLliteral]
    apply congrArg B
    apply congrArg Subtype.val
    apply congrArg L
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp [rpL,planeReflect,Schoenflies.Plane.mk]
      ring
  have hLminusclock (t : Interval) :
      B (OL (1,⟨-rmL*(t:ℝ),actual_scalar_negative_width_bounds rmL hrmL t⟩)).val =
      ((planeReflect (Pdown ⟨(τm:ℝ)*(t:ℝ),actual_unit_interval_product_bounds τm t⟩)) 0,(planeReflect (Pdown ⟨(τm:ℝ)*(t:ℝ),actual_unit_interval_product_bounds τm t⟩)) 1) := by
    simp only [hPdownliteral,hDPLliteral]
    simp only [planeReflect,Schoenflies.Plane.mk,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,neg_neg]
    rw [hPLliteral,hOLliteral]
    apply congrArg B
    apply congrArg Subtype.val
    apply congrArg L
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp [rmL,planeReflect,Schoenflies.Plane.mk]
      ring
  have hRplusclock (t : Interval) :
      B (OR (1,⟨rpR*(t:ℝ),actual_scalar_positive_width_bounds rpR hrpR t⟩)).val =
      ((Qup ⟨(σp:ℝ)*(t:ℝ),actual_unit_interval_product_bounds σp t⟩) 0,(Qup ⟨(σp:ℝ)*(t:ℝ),actual_unit_interval_product_bounds σp t⟩) 1) := by
    simp only [hQupliteral,hUPRliteral]
    simp only [planeReflect,Schoenflies.Plane.mk,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,neg_neg]
    rw [hPRliteral,hORliteral]
    apply congrArg B
    apply congrArg Subtype.val
    apply congrArg Rband
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp [rpR,planeReflect,Schoenflies.Plane.mk]
      ring
  have hRminusclock (t : Interval) :
      B (OR (1,⟨-rmR*(t:ℝ),actual_scalar_negative_width_bounds rmR hrmR t⟩)).val =
      ((planeReflect (Qdown ⟨(σm:ℝ)*(t:ℝ),actual_unit_interval_product_bounds σm t⟩)) 0,(planeReflect (Qdown ⟨(σm:ℝ)*(t:ℝ),actual_unit_interval_product_bounds σm t⟩)) 1) := by
    simp only [hQdownliteral,hDPRliteral]
    simp only [planeReflect,Schoenflies.Plane.mk,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,neg_neg]
    rw [hPRliteral,hORliteral]
    apply congrArg B
    apply congrArg Subtype.val
    apply congrArg Rband
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp [rmR,planeReflect,Schoenflies.Plane.mk]
      ring
  have hOLstrict (w : Icc (-1 : ℝ) 1) (hw0 : -rmL<(w:ℝ)) (hw1 : (w:ℝ)<rpL) :
      -δ<(B (OL (1,w)).val).2 ∧ (B (OL (1,w)).val).2<δ := by
    by_cases hw : (w:ℝ)=0
    · have hwz : w=⟨0,by norm_num⟩ := Subtype.ext hw
      rw [hwz,hOLcenter]
      rw [hBL0]
      change -δ<0 ∧ (0:ℝ)<δ
      constructor <;> linarith only [hδ]
    rcases lt_or_gt_of_ne hw with hn | hp
    · let t : Interval := ⟨-(w:ℝ)/rmL,⟨(div_pos (neg_pos.mpr hn) hrmL.1).le,
          (div_le_one hrmL.1).mpr (by linarith only [hw0])⟩⟩
      have ht0 : 0<(t:ℝ) := div_pos (neg_pos.mpr hn) hrmL.1
      have ht1 : (t:ℝ)<1 := (div_lt_one hrmL.1).mpr (by linarith only [hw0])
      have hwt : (⟨-rmL*(t:ℝ),actual_scalar_negative_width_bounds rmL hrmL t⟩ : Icc (-1 : ℝ) 1)=w := by
        apply Subtype.ext
        dsimp [t]
        field_simp [ne_of_gt hrmL.1] <;> ring
      have hh := congrArg Prod.snd (hLminusclock t)
      rw [hwt] at hh
      have htrim := hPdowntrim t ht0 ht1
      change (B (OL (1,w)).val).2= -(Pdown ⟨(τm:ℝ)*(t:ℝ),actual_unit_interval_product_bounds τm t⟩ 1) at hh
      rw [hh]
      constructor <;> linarith only [htrim.1,htrim.2]
    · let t : Interval := ⟨(w:ℝ)/rpL,⟨(div_pos hp hrpL.1).le,
          (div_le_one hrpL.1).mpr hw1.le⟩⟩
      have ht0 : 0<(t:ℝ) := div_pos hp hrpL.1
      have ht1 : (t:ℝ)<1 := (div_lt_one hrpL.1).mpr hw1
      have hwt : (⟨rpL*(t:ℝ),actual_scalar_positive_width_bounds rpL hrpL t⟩ : Icc (-1 : ℝ) 1)=w := by
        apply Subtype.ext
        dsimp [t]
        field_simp [ne_of_gt hrpL.1] <;> ring
      have hh := congrArg Prod.snd (hLplusclock t)
      rw [hwt] at hh
      have htrim := hPuptrim t ht0 ht1
      rw [hh]
      change -δ<Pup ⟨(τp:ℝ)*(t:ℝ),actual_unit_interval_product_bounds τp t⟩ 1 ∧
        Pup ⟨(τp:ℝ)*(t:ℝ),actual_unit_interval_product_bounds τp t⟩ 1<δ
      exact ⟨by linarith only [htrim.1,hδ],htrim.2⟩
  have hORstrict (w : Icc (-1 : ℝ) 1) (hw0 : -rmR<(w:ℝ)) (hw1 : (w:ℝ)<rpR) :
      -δ<(B (OR (1,w)).val).2 ∧ (B (OR (1,w)).val).2<δ := by
    by_cases hw : (w:ℝ)=0
    · have hwz : w=⟨0,by norm_num⟩ := Subtype.ext hw
      rw [hwz,hORcenter]
      rw [hBR0]
      change -δ<0 ∧ (0:ℝ)<δ
      constructor <;> linarith only [hδ]
    rcases lt_or_gt_of_ne hw with hn | hp
    · let t : Interval := ⟨-(w:ℝ)/rmR,⟨(div_pos (neg_pos.mpr hn) hrmR.1).le,
          (div_le_one hrmR.1).mpr (by linarith only [hw0])⟩⟩
      have ht0 : 0<(t:ℝ) := div_pos (neg_pos.mpr hn) hrmR.1
      have ht1 : (t:ℝ)<1 := (div_lt_one hrmR.1).mpr (by linarith only [hw0])
      have hwt : (⟨-rmR*(t:ℝ),actual_scalar_negative_width_bounds rmR hrmR t⟩ : Icc (-1 : ℝ) 1)=w := by
        apply Subtype.ext
        dsimp [t]
        field_simp [ne_of_gt hrmR.1] <;> ring
      have hh := congrArg Prod.snd (hRminusclock t)
      rw [hwt] at hh
      have htrim := hQdowntrim t ht0 ht1
      change (B (OR (1,w)).val).2= -(Qdown ⟨(σm:ℝ)*(t:ℝ),actual_unit_interval_product_bounds σm t⟩ 1) at hh
      rw [hh]
      constructor <;> linarith only [htrim.1,htrim.2]
    · let t : Interval := ⟨(w:ℝ)/rpR,⟨(div_pos hp hrpR.1).le,
          (div_le_one hrpR.1).mpr hw1.le⟩⟩
      have ht0 : 0<(t:ℝ) := div_pos hp hrpR.1
      have ht1 : (t:ℝ)<1 := (div_lt_one hrpR.1).mpr hw1
      have hwt : (⟨rpR*(t:ℝ),actual_scalar_positive_width_bounds rpR hrpR t⟩ : Icc (-1 : ℝ) 1)=w := by
        apply Subtype.ext
        dsimp [t]
        field_simp [ne_of_gt hrpR.1] <;> ring
      have hh := congrArg Prod.snd (hRplusclock t)
      rw [hwt] at hh
      have htrim := hQuptrim t ht0 ht1
      rw [hh]
      change -δ<Qup ⟨(σp:ℝ)*(t:ℝ),actual_unit_interval_product_bounds σp t⟩ 1 ∧
        Qup ⟨(σp:ℝ)*(t:ℝ),actual_unit_interval_product_bounds σp t⟩ 1<δ
      exact ⟨by linarith only [htrim.1,hδ],htrim.2⟩
  /- The obstacle needed by whole-fill clearance is the ENTIRE endpoint band
  with its terminal port removed, not merely one of its side curves. -/
  have endpoint_band_minus_terminal_connected
      (N : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R))
      (hN : Topology.IsEmbedding N) :
      IsPreconnected (Set.range N \ Set.range (fun w => N (1,w))) := by
    have heq : Set.range N \ Set.range (fun w => N (1,w)) =
        N '' (Set.Iio (1 : Interval) ×ˢ Set.univ) := by
      ext y
      constructor
      · rintro ⟨⟨z,rfl⟩,hn⟩
        refine ⟨z,⟨?_,Set.mem_univ _⟩,rfl⟩
        apply lt_of_le_of_ne (show z.1 ≤ (1 : Interval) from z.1.property.2)
        intro he
        exact hn ⟨z.2,by rw [← he]⟩
      · rintro ⟨z,hz,rfl⟩
        refine ⟨Set.mem_range_self z,?_⟩
        rintro ⟨w,hw⟩
        have hh := congrArg Prod.fst (hN.injective hw)
        exact hz.1.ne hh.symm
    rw [heq]
    letI : PreconnectedSpace (Set.Icc (-1 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
    exact (isPreconnected_Iio.prod isPreconnected_univ).image N N.continuous.continuousOn
  have endpoint_band_initial_boundary_witness
      (N : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R))
      (hN : Topology.IsEmbedding N)
      (hNb : ∀ w,N (0,w) ∈ boundaryQ S x R) :
      ∃ y ∈ Set.range N \ Set.range (fun w => N (1,w)),
        y ∈ boundaryQ S x R := by
    refine ⟨N (0,⟨0,by norm_num⟩),⟨Set.mem_range_self _,?_⟩,hNb _⟩
    rintro ⟨w,hw⟩
    have hh := congrArg (fun z => (z.1:ℝ)) (hN.injective hw)
    norm_num at hh
  have hLobstacle_connected := endpoint_band_minus_terminal_connected L hL
  have hRobstacle_connected := endpoint_band_minus_terminal_connected Rband hRband
  have hLobstacle_boundary := endpoint_band_initial_boundary_witness L hL
    (fun w => (hboundary w).1)
  have hRobstacle_boundary := endpoint_band_initial_boundary_witness Rband hRband
    (fun w => (hboundary w).2)
  have surface_rectangle_interior_open
      (B : C(Interval × Interval,S)) (hB : Topology.IsEmbedding B) :
      IsOpen (B '' {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧
        0<(z.2:ℝ) ∧ (z.2:ℝ)<1}) := by
    let O : Set Schoenflies.Plane :=
      {p | 0<p 0 ∧ p 0<1 ∧ 0<p 1 ∧ p 1<1}
    have hc0 : Continuous (fun p : Schoenflies.Plane => p 0) := by fun_prop
    have hc1 : Continuous (fun p : Schoenflies.Plane => p 1) := by fun_prop
    have hO : IsOpen O := (isOpen_lt continuous_const hc0).inter
      ((isOpen_lt hc0 continuous_const).inter
        ((isOpen_lt continuous_const hc1).inter (isOpen_lt hc1 continuous_const)))
    let q : Schoenflies.Plane → Interval × Interval := fun p =>
      (Set.projIcc 0 1 zero_le_one (p 0),Set.projIcc 0 1 zero_le_one (p 1))
    have hqc : Continuous q := by dsimp [q]; fun_prop
    have hqval (p : Schoenflies.Plane) (hp : p∈O) :
        q p=(⟨p 0,⟨hp.1.le,hp.2.1.le⟩⟩,⟨p 1,⟨hp.2.2.1.le,hp.2.2.2.le⟩⟩) :=
      Prod.ext (Set.projIcc_of_mem zero_le_one ⟨hp.1.le,hp.2.1.le⟩)
        (Set.projIcc_of_mem zero_le_one ⟨hp.2.2.1.le,hp.2.2.2.le⟩)
    let F : Schoenflies.Plane → S := B ∘ q
    have hFc : Continuous F := B.continuous.comp hqc
    have hFi : Set.InjOn F O := by
      intro p hp v hv he
      have hh := hB.injective he
      change q p=q v at hh
      rw [hqval p hp,hqval v hv] at hh
      have hh0 := congrArg (fun w => (w.1:ℝ)) hh
      have hh1 := congrArg (fun w => (w.2:ℝ)) hh
      ext j
      fin_cases j <;> assumption
    have hopen : IsOpen (F '' O) :=
      surface_invariance_of_domain_probe F O hO hFc.continuousOn hFi
    have heq : F '' O = B '' {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧
        0<(z.2:ℝ) ∧ (z.2:ℝ)<1} := by
      apply Set.Subset.antisymm
      · rintro y ⟨p,hp,rfl⟩
        refine ⟨q p,?_,rfl⟩
        rw [hqval p hp]
        exact hp
      · rintro y ⟨z,hz,rfl⟩
        let p := Schoenflies.Plane.mk z.1 z.2
        have hp : p∈O := hz
        refine ⟨p,hp,?_⟩
        change B (q p)=B z
        rw [hqval p hp]
        rfl
    rwa [heq] at hopen
  /- Whole endpoint-band clearance in the ORIGINAL surface. The original
  boundary point supplies an exterior witness; no fill-clearance certificate
  is assumed. Only the four actual boundary-curve avoidance obligations remain. -/
  have original_endpoint_band_rectangle_clearance
      (N : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R))
      (hN : Topology.IsEmbedding N)
      (hNb : ∀ w,N (0,w) ∈ boundaryQ S x R)
      (B : C(Interval × Interval,S)) (hB : Topology.IsEmbedding B)
      (hBoutside : ∀ z,B z∉boundaryCircle S x R)
      (hedges : ∀ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
        B z ∉ Subtype.val '' (Set.range N \ Set.range (fun w => N (1,w)))) :
      Set.range B ∩ (Subtype.val '' Set.range N) ⊆
        Set.range (fun w => (N (1,w)).val) := by
    let K : Set S := Subtype.val '' (Set.range N \ Set.range (fun w => N (1,w)))
    have hK : IsPreconnected K :=
      (endpoint_band_minus_terminal_connected N hN).image _ continuous_subtype_val.continuousOn
    let I : Set (Interval × Interval) :=
      {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧ 0<(z.2:ℝ) ∧ (z.2:ℝ)<1}
    have hopen : IsOpen (B '' I) := surface_rectangle_interior_open B hB
    have hclosed : IsClosed (Set.range B) := (isCompact_range B.continuous).isClosed
    have hcover : K ⊆ B '' I ∪ (Set.range B)ᶜ := by
      intro y hy
      by_cases hr : y∈Set.range B
      · obtain ⟨z,rfl⟩ := hr
        have hn0 : z.1≠0 := by intro he; exact hedges z (Or.inl he) hy
        have hn1 : z.1≠1 := by intro he; exact hedges z (Or.inr (Or.inl he)) hy
        have hm0 : z.2≠0 := by intro he; exact hedges z (Or.inr (Or.inr (Or.inl he))) hy
        have hm1 : z.2≠1 := by intro he; exact hedges z (Or.inr (Or.inr (Or.inr he))) hy
        exact Or.inl ⟨z,⟨
          lt_of_le_of_ne z.1.property.1 (fun he => hn0 (Subtype.ext he.symm)),
          lt_of_le_of_ne z.1.property.2 (fun he => hn1 (Subtype.ext he)),
          lt_of_le_of_ne z.2.property.1 (fun he => hm0 (Subtype.ext he.symm)),
          lt_of_le_of_ne z.2.property.2 (fun he => hm1 (Subtype.ext he))⟩,rfl⟩
      · exact Or.inr hr
    have hdis : Disjoint (B '' I) (Set.range B)ᶜ := Set.disjoint_left.mpr (by
      rintro y ⟨z,hz,rfl⟩ hn
      exact hn (Set.mem_range_self z))
    obtain ⟨y,hy,hyb⟩ := endpoint_band_initial_boundary_witness N hN hNb
    have hyr : y.val∉Set.range B := by
      rintro ⟨z,hz⟩
      exact hBoutside z (hz ▸ hyb)
    have hsub : K ⊆ (Set.range B)ᶜ := hK.subset_right_of_subset_union hopen
      hclosed.isOpen_compl hdis hcover ⟨y.val,⟨y,hy,rfl⟩,hyr⟩
    rintro p ⟨hp,⟨y,hyn,rfl⟩⟩
    by_contra hn
    have hyport : y∉Set.range (fun w => N (1,w)) := by
      rintro ⟨w,hw⟩
      exact hn ⟨w,congrArg Subtype.val hw⟩
    exact hsub ⟨y,⟨hyn,hyport⟩,rfl⟩ hp
  have actual_two_endpoint_band_clearance
      (B : C(Interval × Interval,S)) (hB : Topology.IsEmbedding B)
      (hBoutside : ∀ z,B z∉boundaryCircle S x R)
      (hLedges : ∀ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
        B z ∉ Subtype.val '' (Set.range L \ Set.range (fun w => L (1,w))))
      (hRedges : ∀ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
        B z ∉ Subtype.val '' (Set.range Rband \ Set.range (fun w => Rband (1,w)))) :
      (Set.range B ∩ (Subtype.val '' Set.range L) ⊆
        Set.range (fun w => (L (1,w)).val)) ∧
      (Set.range B ∩ (Subtype.val '' Set.range Rband) ⊆
        Set.range (fun w => (Rband (1,w)).val)) := by
    exact ⟨original_endpoint_band_rectangle_clearance L hL
      (fun w => (hboundary w).1) B hB hBoutside hLedges,
      original_endpoint_band_rectangle_clearance Rband hRband
      (fun w => (hboundary w).2) B hB hBoutside hRedges⟩
  have actual_endpoint_band_full_seam_equality
      (N : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R))
      (hN : Topology.IsEmbedding N)
      (hNb : ∀ w,N (0,w) ∈ boundaryQ S x R)
      (B : C(Interval × Interval,S)) (hB : Topology.IsEmbedding B)
      (hBoutside : ∀ z,B z∉boundaryCircle S x R)
      (hedges : ∀ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
        B z ∉ Subtype.val '' (Set.range N \ Set.range (fun w => N (1,w))))
      (hport : Set.range (fun w => (N (1,w)).val) ⊆ Set.range B) :
      Set.range B ∩ (Subtype.val '' Set.range N) =
        Set.range (fun w => (N (1,w)).val) := by
    apply Set.Subset.antisymm
    · exact original_endpoint_band_rectangle_clearance N hN hNb B hB hBoutside hedges
    · intro y hy
      refine ⟨hport hy,?_⟩
      obtain ⟨w,rfl⟩ := hy
      exact ⟨N (1,w),Set.mem_range_self _,rfl⟩
  /- Actual tapering changes the band, not its original center or the
  prescribed terminal port. Every earlier COMPLETE width slice avoids J. -/
  have actual_tapered_endpoint_band
      (N : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R))
      (hN : Topology.IsEmbedding N) (J : Set (Q S x R)) (hJ : IsClosed J)
      (rp rm : ℝ) (hrp : 0<rp ∧ rp≤1) (hrm : 0<rm ∧ rm≤1)
      (hcenter : ∀ t,N (t,⟨0,by norm_num⟩)∉J)
      (hterminal : ∀ w : Set.Icc (-1 : ℝ) 1,-rm<(w:ℝ) → (w:ℝ)<rp → N (1,w)∉J) :
      ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R),
        Topology.IsEmbedding E ∧
        (∀ t,E (t,⟨0,by norm_num⟩)=N (t,⟨0,by norm_num⟩)) ∧
        (∀ w : Set.Icc (-1 : ℝ) 1,E (1,w)=N (1,
          ⟨if (w:ℝ)≤0 then rm*(w:ℝ) else rp*(w:ℝ),by
            split_ifs with hw
            · constructor <;> nlinarith only [hrm.1,hrm.2,w.property.1,w.property.2]
            · constructor <;> nlinarith only [hrp.1,hrp.2,w.property.1,w.property.2]⟩)) ∧
        Set.range E ⊆ Set.range N ∧
        (∀ t w,∃ v,E (t,w)=N (t,v)) ∧
        (∀ t : Interval,(t:ℝ)<1 → ∀ w,E (t,w)∉J) := by
    obtain ⟨bp,bm,hβ,hbp1,hbm1,hclear⟩ :=
      actual_continuous_longitudinal_width_taper N J hJ rp rm hrp hrm hcenter hterminal
    let q : Interval × Set.Icc (-1 : ℝ) 1 → ℝ := fun z =>
      bp z.1*max (z.2:ℝ) 0 - bm z.1*max (-(z.2:ℝ)) 0
    have hq (z : Interval × Set.Icc (-1 : ℝ) 1) :
        q z=if (z.2:ℝ)≤0 then bm z.1*(z.2:ℝ) else bp z.1*(z.2:ℝ) := by
      by_cases hw : (z.2:ℝ)≤0
      · simp only [q,ite_eq_left hw,max_eq_right hw,max_eq_left (by linarith : 0≤-(z.2:ℝ))]
        ring
      · simp only [q,ite_eq_right hw,max_eq_left (le_of_not_ge hw),
          max_eq_right (by linarith : -(z.2:ℝ)≤0)]
        ring
    have hqbound (z : Interval × Set.Icc (-1 : ℝ) 1) : -1≤q z ∧ q z≤1 := by
      rw [hq]
      split_ifs
      · constructor <;> nlinarith only [(hβ z.1).2.1,(hβ z.1).2.2,z.2.property.1,z.2.property.2]
      · constructor <;> nlinarith only [(hβ z.1).1.1,(hβ z.1).1.2,z.2.property.1,z.2.property.2]
    let k : Interval × Set.Icc (-1 : ℝ) 1 → Interval × Set.Icc (-1 : ℝ) 1 :=
      fun z => (z.1,⟨q z,hqbound z⟩)
    have hkc : Continuous k := by
      apply Continuous.prodMk continuous_fst
      apply Continuous.subtype_mk
      dsimp [q]
      fun_prop
    have hki : Function.Injective k := by
      rintro ⟨t,w⟩ ⟨s,v⟩ he
      have ht := congrArg Prod.fst he
      change t=s at ht
      subst s
      have hh := congrArg (fun z => (z.2:ℝ)) he
      change q (t,w)=q (t,v) at hh
      rw [hq,hq] at hh
      refine Prod.ext rfl ?_
      apply Subtype.ext
      by_cases hw : (w:ℝ)≤0
      · by_cases hv : (v:ℝ)≤0
        · rw [ite_eq_left hw,ite_eq_left hv] at hh
          exact mul_left_cancel₀ (hβ t).2.1.ne' hh
        · rw [ite_eq_left hw,ite_eq_right hv] at hh
          have hnonpos := mul_nonpos_of_nonneg_of_nonpos (hβ t).2.1.le hw
          have hpos := mul_pos (hβ t).1.1 (lt_of_not_ge hv)
          linarith
      · by_cases hv : (v:ℝ)≤0
        · rw [ite_eq_right hw,ite_eq_left hv] at hh
          have hnonpos := mul_nonpos_of_nonneg_of_nonpos (hβ t).2.1.le hv
          have hpos := mul_pos (hβ t).1.1 (lt_of_not_ge hw)
          linarith
        · rw [ite_eq_right hw,ite_eq_right hv] at hh
          exact mul_left_cancel₀ (hβ t).1.1.ne' hh
    have hk : Topology.IsEmbedding k := (hkc.isClosedEmbedding hki).isEmbedding
    let E : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R) := ⟨N ∘ k,N.continuous.comp hkc⟩
    refine ⟨E,hN.comp hk,?_,?_,?_,?_,?_⟩
    · intro t
      apply congrArg N
      refine Prod.ext rfl ?_
      apply Subtype.ext
      simp [k,q]
    · intro w
      apply congrArg N
      refine Prod.ext rfl ?_
      apply Subtype.ext
      change q (1,w)=_
      rw [hq,hbp1,hbm1]
    · rintro y ⟨z,rfl⟩
      exact Set.mem_range_self (k z)
    · intro t w
      exact ⟨(k (t,w)).2,rfl⟩
    · intro t ht w
      have hh := hclear t ht w
      change N (k (t,w))∉J
      have he : k (t,w)=(t,⟨if (w:ℝ)≤0 then bm t*(w:ℝ) else bp t*(w:ℝ),by
        split_ifs with hw
        · constructor <;> nlinarith only [(hβ t).2.1,(hβ t).2.2,w.property.1,w.property.2]
        · constructor <;> nlinarith only [(hβ t).1.1,(hβ t).1.2,w.property.1,w.property.2]⟩) :=
        Prod.ext rfl (Subtype.ext (hq (t,w)))
      rw [he]
      exact hh
  have actual_original_endpoint_taper_with_clearance
      (N : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R))
      (hN : Topology.IsEmbedding N)
      (hNb : ∀ w,N (0,w)∈boundaryQ S x R)
      (hNi : ∀ t : Interval,0<(t:ℝ) → ∀ w,N (t,w)∉boundaryQ S x R)
      (hNa : ∀ z,N z∈Set.range a.val ↔ (z.2:ℝ)=0)
      (J : Set (Q S x R)) (hJ : IsClosed J)
      (rp rm : ℝ) (hrp : 0<rp ∧ rp≤1) (hrm : 0<rm ∧ rm≤1)
      (hcenter : ∀ t,N (t,⟨0,by norm_num⟩)∉J)
      (hterminal : ∀ w : Set.Icc (-1 : ℝ) 1,-rm<(w:ℝ) → (w:ℝ)<rp → N (1,w)∉J) :
      ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R),
        Topology.IsEmbedding E ∧
        (∀ t,E (t,⟨0,by norm_num⟩)=N (t,⟨0,by norm_num⟩)) ∧
        (∀ w,E (0,w)∈boundaryQ S x R) ∧
        (∀ t : Interval,0<(t:ℝ) → ∀ w,E (t,w)∉boundaryQ S x R) ∧
        (∀ z,E z∈Set.range a.val ↔ (z.2:ℝ)=0) ∧
        (∀ w : Set.Icc (-1 : ℝ) 1,E (1,w)=N (1,
          ⟨if (w:ℝ)≤0 then rm*(w:ℝ) else rp*(w:ℝ),by
            split_ifs with hw
            · constructor <;> nlinarith only [hrm.1,hrm.2,w.property.1,w.property.2]
            · constructor <;> nlinarith only [hrp.1,hrp.2,w.property.1,w.property.2]⟩)) ∧
        Set.range E ⊆ Set.range N ∧
        Disjoint (Set.range E \ Set.range (fun w => E (1,w))) J := by
    obtain ⟨E,hE,hEc,hEport,hEsub,hlevel,hclear⟩ :=
      actual_tapered_endpoint_band N hN J hJ rp rm hrp hrm hcenter hterminal
    refine ⟨E,hE,hEc,?_,?_,?_,hEport,hEsub,?_⟩
    · intro w
      obtain ⟨v,hv⟩ := hlevel 0 w
      rw [hv]
      exact hNb v
    · intro t ht w
      obtain ⟨v,hv⟩ := hlevel t w
      rw [hv]
      exact hNi t ht v
    · intro z
      constructor
      · intro hz
        obtain ⟨v,hv⟩ := hlevel z.1 z.2
        have hvzero : (v:ℝ)=0 := (hNa (z.1,v)).mp (hv ▸ hz)
        have hv0 : v=⟨0,by norm_num⟩ := Subtype.ext hvzero
        have heq : E z=E (z.1,⟨0,by norm_num⟩) := by
          calc
            E z=N (z.1,v) := hv
            _=N (z.1,⟨0,by norm_num⟩) := by rw [hv0]
            _=E (z.1,⟨0,by norm_num⟩) := (hEc z.1).symm
        exact congrArg (fun v => (v.2:ℝ)) (hE.injective heq)
      · intro hz
        have hz0 : z.2=⟨0,by norm_num⟩ := Subtype.ext hz
        have hzz : z=(z.1,⟨0,by norm_num⟩) := Prod.ext rfl hz0
        rw [hzz,hEc]
        exact (hNa _).mpr (by norm_num)
    · apply Set.disjoint_left.mpr
      rintro y ⟨⟨z,rfl⟩,hnport⟩ hyJ
      have ht1 : z.1≠1 := by
        intro he
        exact hnport ⟨z.2,by rw [← he]⟩
      have ht : (z.1:ℝ)<1 := lt_of_le_of_ne z.1.property.2 (fun he => ht1 (Subtype.ext he))
      exact hclear z.1 ht z.2 hyJ
  /- The closed forbidden set is formed from the actual upper/lower joins.
  Its required taper hypotheses follow from source axis detection and the
  actual first-height port bounds, including centers OUTSIDE the chart. -/
  have actual_horizontal_joins_give_source_taper_hypotheses
      (N : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R))
      (hNa : ∀ z,N z∈Set.range a.val ↔ (z.2:ℝ)=0)
      (B : OpenPartialHomeomorph S (ℝ × ℝ))
      (haxis : ∀ y∈B.source,y∈Set.range (fun t => (a.val t).val) ↔ (B y).2=0)
      (U D : C(Interval,Q S x R)) (δ : ℝ) (hδ : 0<δ)
      (hU : ∀ t,(U t).val∈B.source ∧ (B (U t).val).2=δ)
      (hD : ∀ t,(D t).val∈B.source ∧ (B (D t).val).2= -δ)
      (rp rm : ℝ)
      (hterminal : ∀ w : Set.Icc (-1 : ℝ) 1,-rm<(w:ℝ) → (w:ℝ)<rp →
        -δ<(B (N (1,w)).val).2 ∧ (B (N (1,w)).val).2<δ) :
      IsClosed (Set.range U ∪ Set.range D) ∧
      (∀ t,N (t,⟨0,by norm_num⟩)∉Set.range U ∪ Set.range D) ∧
      (∀ w : Set.Icc (-1 : ℝ) 1,-rm<(w:ℝ) → (w:ℝ)<rp →
        N (1,w)∉Set.range U ∪ Set.range D) := by
    have hNc (t : Interval) : (N (t,⟨0,by norm_num⟩)).val∈
        Set.range (fun s => (a.val s).val) := by
      obtain ⟨s,hs⟩ := (hNa (t,⟨0,by norm_num⟩)).mpr (by norm_num)
      exact ⟨s,congrArg Subtype.val hs⟩
    refine ⟨(isCompact_range U.continuous).isClosed.union
      (isCompact_range D.continuous).isClosed,?_,?_⟩
    · intro t hm
      rcases hm with ⟨s,hs⟩ | ⟨s,hs⟩
      · have hsval := congrArg Subtype.val hs
        have hzero := (haxis (U s).val (hU s).1).mp (hsval.symm ▸ hNc t)
        linarith [(hU s).2]
      · have hsval := congrArg Subtype.val hs
        have hzero := (haxis (D s).val (hD s).1).mp (hsval.symm ▸ hNc t)
        linarith [(hD s).2]
    · intro w hwm hwp hm
      have hb := hterminal w hwm hwp
      rcases hm with ⟨s,hs⟩ | ⟨s,hs⟩
      · have hh := congrArg (fun y : Q S x R => (B y.val).2) hs
        linarith [(hU s).2]
      · have hh := congrArg (fun y : Q S x R => (B y.val).2) hs
        linarith [(hD s).2]
  have actual_original_band_avoiding_horizontal_joins
      (N : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R))
      (hN : Topology.IsEmbedding N)
      (hNb : ∀ w,N (0,w)∈boundaryQ S x R)
      (hNi : ∀ t : Interval,0<(t:ℝ) → ∀ w,N (t,w)∉boundaryQ S x R)
      (hNa : ∀ z,N z∈Set.range a.val ↔ (z.2:ℝ)=0)
      (B : OpenPartialHomeomorph S (ℝ × ℝ))
      (haxis : ∀ y∈B.source,y∈Set.range (fun t => (a.val t).val) ↔ (B y).2=0)
      (U D : C(Interval,Q S x R)) (δ : ℝ) (hδ : 0<δ)
      (hU : ∀ t,(U t).val∈B.source ∧ (B (U t).val).2=δ)
      (hD : ∀ t,(D t).val∈B.source ∧ (B (D t).val).2= -δ)
      (rp rm : ℝ) (hrp : 0<rp ∧ rp≤1) (hrm : 0<rm ∧ rm≤1)
      (hterminal : ∀ w : Set.Icc (-1 : ℝ) 1,-rm<(w:ℝ) → (w:ℝ)<rp →
        -δ<(B (N (1,w)).val).2 ∧ (B (N (1,w)).val).2<δ) :
      ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R),
        Topology.IsEmbedding E ∧
        (∀ t,E (t,⟨0,by norm_num⟩)=N (t,⟨0,by norm_num⟩)) ∧
        (∀ w,E (0,w)∈boundaryQ S x R) ∧
        (∀ t : Interval,0<(t:ℝ) → ∀ w,E (t,w)∉boundaryQ S x R) ∧
        (∀ z,E z∈Set.range a.val ↔ (z.2:ℝ)=0) ∧
        (∀ w : Set.Icc (-1 : ℝ) 1,E (1,w)=N (1,
          ⟨if (w:ℝ)≤0 then rm*(w:ℝ) else rp*(w:ℝ),by
            split_ifs with hw
            · constructor <;> nlinarith only [hrm.1,hrm.2,w.property.1,w.property.2]
            · constructor <;> nlinarith only [hrp.1,hrp.2,w.property.1,w.property.2]⟩)) ∧
        Set.range E ⊆ Set.range N ∧
        Disjoint (Set.range E \ Set.range (fun w => E (1,w))) (Set.range U ∪ Set.range D) ∧
        IsPreconnected (Set.range E \ Set.range (fun w => E (1,w))) ∧
        ∃ y∈Set.range E \ Set.range (fun w => E (1,w)),y∈boundaryQ S x R := by
    obtain ⟨hJ,hcenterJ,hterminalJ⟩ :=
      actual_horizontal_joins_give_source_taper_hypotheses N hNa B haxis U D δ hδ
        hU hD rp rm hterminal
    obtain ⟨E,hE,hEc,hEb,hEi,hEa,hEport,hEsub,hclear⟩ :=
      actual_original_endpoint_taper_with_clearance N hN hNb hNi hNa
        (Set.range U ∪ Set.range D) hJ rp rm hrp hrm hcenterJ hterminalJ
    exact ⟨E,hE,hEc,hEb,hEi,hEa,hEport,hEsub,hclear,
      endpoint_band_minus_terminal_connected E hE,
      endpoint_band_initial_boundary_witness E hE hEb⟩
  /- Once the actual middle strip is constructed, all gluing, original
  center parametrization and both boundary edges are discharged here. -/
  obtain ⟨TL,hTL,hTLcenter,hTLboundary,hTLinterior,hTLaxis,hTLport,hTLsubset,hTLjoins,hTLconnected,hTLwitness⟩ :=
    actual_original_band_avoiding_horizontal_joins OL hOL hOLboundary hOLinterior hOLaxis
      B hBaxis JoinUp JoinDown δ hδ hJoinUp hJoinDown rpL rmL hrpL hrmL hOLstrict
  obtain ⟨TR,hTR,hTRcenter,hTRboundary,hTRinterior,hTRaxis,hTRport,hTRsubset,hTRjoins,hTRconnected,hTRwitness⟩ :=
    actual_original_band_avoiding_horizontal_joins OR hOR hORboundary hORinterior hORaxis
      B hBaxis JoinUp JoinDown δ hδ hJoinUp hJoinDown rpR rmR hrpR hrmR hORstrict
  have hTLTR : Disjoint (Set.range TL) (Set.range TR) := hOLR.mono hTLsubset hTRsubset
  have actual_original_terminal_source_from_whole_port
      (N : C(Interval × Icc (-1 : ℝ) 1,Q S x R)) (r : ℝ) (hr : 0<r ∧ r≤1)
      (hwhole : ∀ w : Icc (-1 : ℝ) 1,
        (N (1,⟨r*(w:ℝ),by constructor <;>
          nlinarith only [hr.1,hr.2,w.property.1,w.property.2]⟩)).val∈B.source)
      (w : Icc (-1 : ℝ) 1) (hw : abs (w:ℝ)≤r) : (N (1,w)).val∈B.source := by
    have hw' : -r≤(w:ℝ) ∧ (w:ℝ)≤r := abs_le.mp hw
    let v : Icc (-1 : ℝ) 1 := ⟨(w:ℝ)/r,⟨
      (le_div_iff₀ hr.1).mpr (by nlinarith only [hw'.1]),
      (div_le_one hr.1).mpr hw'.2⟩⟩
    have hh := hwhole v
    have he : (⟨r*(v:ℝ),by constructor <;>
        nlinarith only [hr.1,hr.2,v.property.1,v.property.2]⟩ : Icc (-1 : ℝ) 1)=w := by
      apply Subtype.ext
      dsimp [v]
      field_simp [ne_of_gt hr.1] <;> ring
    rwa [he] at hh
  have actual_oriented_terminal_source
      (N E : C(Interval × Icc (-1 : ℝ) 1,Q S x R))
      (ε : ℝ) (hε : ε=1 ∨ ε= -1)
      (hlit : ∀ z,E z=N (z.1,⟨ε*(z.2:ℝ),actual_signed_full_width_bounds ε hε z.2⟩))
      (r : ℝ) (hr : 0<r ∧ r≤1)
      (hwhole : ∀ w : Icc (-1 : ℝ) 1,
        (N (1,⟨r*(w:ℝ),by constructor <;>
          nlinarith only [hr.1,hr.2,w.property.1,w.property.2]⟩)).val∈B.source)
      (w : Icc (-1 : ℝ) 1) (hw : abs (w:ℝ)≤r) : (E (1,w)).val∈B.source := by
    rw [hlit]
    apply actual_original_terminal_source_from_whole_port N r hr hwhole
    change abs (ε*(w:ℝ))≤r
    rcases hε with rfl | rfl
    · simpa using hw
    · simpa using hw
  have hTLsource (w : Icc (-1 : ℝ) 1) : (TL (1,w)).val∈B.source := by
    rw [hTLport]
    apply actual_oriented_terminal_source L OL εL hεL hOLliteral rL hrL hLwhole
    split_ifs with hw
    · change abs (rmL*(w:ℝ))≤rL
      rw [abs_mul,abs_of_pos hrmL.1]
      have hwr : abs (w:ℝ)≤1 := abs_le.mpr w.property
      have hq : rmL≤rL := by
        dsimp [rmL]
        calc
          rL*ρL*(τm:ℝ) ≤ rL*ρL*1 :=
            mul_le_mul_of_nonneg_left τm.property.2 (mul_nonneg hrL.1.le hρL.1.le)
          _ ≤ rL := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hρL.2 hrL.1.le
      calc
        rmL*abs (w:ℝ) ≤ rmL*1 := mul_le_mul_of_nonneg_left hwr hrmL.1.le
        _ ≤ rL := by simpa only [mul_one] using hq
    · change abs (rpL*(w:ℝ))≤rL
      rw [abs_mul,abs_of_pos hrpL.1]
      have hwr : abs (w:ℝ)≤1 := abs_le.mpr w.property
      have hq : rpL≤rL := by
        dsimp [rpL]
        calc
          rL*ρL*(τp:ℝ) ≤ rL*ρL*1 :=
            mul_le_mul_of_nonneg_left τp.property.2 (mul_nonneg hrL.1.le hρL.1.le)
          _ ≤ rL := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hρL.2 hrL.1.le
      calc
        rpL*abs (w:ℝ) ≤ rpL*1 := mul_le_mul_of_nonneg_left hwr hrpL.1.le
        _ ≤ rL := by simpa only [mul_one] using hq
  have hTRsource (w : Icc (-1 : ℝ) 1) : (TR (1,w)).val∈B.source := by
    rw [hTRport]
    apply actual_oriented_terminal_source Rband OR εR hεR hORliteral rR hrR hRwhole
    split_ifs with hw
    · change abs (rmR*(w:ℝ))≤rR
      rw [abs_mul,abs_of_pos hrmR.1]
      have hwr : abs (w:ℝ)≤1 := abs_le.mpr w.property
      have hq : rmR≤rR := by
        dsimp [rmR]
        calc
          rR*ρR*(σm:ℝ) ≤ rR*ρR*1 :=
            mul_le_mul_of_nonneg_left σm.property.2 (mul_nonneg hrR.1.le hρR.1.le)
          _ ≤ rR := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hρR.2 hrR.1.le
      calc
        rmR*abs (w:ℝ) ≤ rmR*1 := mul_le_mul_of_nonneg_left hwr hrmR.1.le
        _ ≤ rR := by simpa only [mul_one] using hq
    · change abs (rpR*(w:ℝ))≤rR
      rw [abs_mul,abs_of_pos hrpR.1]
      have hwr : abs (w:ℝ)≤1 := abs_le.mpr w.property
      have hq : rpR≤rR := by
        dsimp [rpR]
        calc
          rR*ρR*(σp:ℝ) ≤ rR*ρR*1 :=
            mul_le_mul_of_nonneg_left σp.property.2 (mul_nonneg hrR.1.le hρR.1.le)
          _ ≤ rR := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hρR.2 hrR.1.le
      calc
        rpR*abs (w:ℝ) ≤ rpR*1 := mul_le_mul_of_nonneg_left hwr hrpR.1.le
        _ ≤ rR := by simpa only [mul_one] using hq
  have hM0 (w : Icc (-1 : ℝ) 1) : M (0,w)=TL (1,w) := by
    apply Subtype.ext
    apply B.injOn (hmiddles (0,w)) (hTLsource w)
    change B (M (0,w)).val=B (TL (1,w)).val
    rw [hMcoord]
    change (F (0,w) 0,F (0,w) 1)=B (TL (1,w)).val
    rw [hFval,hTLport]
    by_cases hw : (w:ℝ)≤0
    · simp only [ite_eq_left hw]
      let t : Interval := ⟨-(w:ℝ),⟨by linarith,by linarith only [w.property.1]⟩⟩
      have he : projIcc 0 1 zero_le_one (-(w:ℝ))=t :=
        projIcc_of_mem zero_le_one t.property
      rw [he]
      change (planeReflect (V (0,t)) 0,planeReflect (V (0,t)) 1)=_
      rw [hVleft]
      have hh := hLminusclock t
      have hwidth : (-rmL*(t:ℝ))=rmL*(w:ℝ) := by dsimp [t]; ring
      simpa only [hwidth] using hh.symm
    · simp only [ite_eq_right hw]
      let t : Interval := ⟨(w:ℝ),⟨(lt_of_not_ge hw).le,w.property.2⟩⟩
      have he : projIcc 0 1 zero_le_one (w:ℝ)=t :=
        projIcc_of_mem zero_le_one t.property
      rw [he,hUleft]
      exact (hLplusclock t).symm
  have hM1 (w : Icc (-1 : ℝ) 1) : M (1,w)=TR (1,w) := by
    apply Subtype.ext
    apply B.injOn (hmiddles (1,w)) (hTRsource w)
    change B (M (1,w)).val=B (TR (1,w)).val
    rw [hMcoord]
    change (F (1,w) 0,F (1,w) 1)=B (TR (1,w)).val
    rw [hFval,hTRport]
    by_cases hw : (w:ℝ)≤0
    · simp only [ite_eq_left hw]
      let t : Interval := ⟨-(w:ℝ),⟨by linarith,by linarith only [w.property.1]⟩⟩
      have he : projIcc 0 1 zero_le_one (-(w:ℝ))=t :=
        projIcc_of_mem zero_le_one t.property
      rw [he]
      change (planeReflect (V (1,t)) 0,planeReflect (V (1,t)) 1)=_
      rw [hVright]
      have hh := hRminusclock t
      have hwidth : (-rmR*(t:ℝ))=rmR*(w:ℝ) := by dsimp [t]; ring
      simpa only [hwidth] using hh.symm
    · simp only [ite_eq_right hw]
      let t : Interval := ⟨(w:ℝ),⟨(lt_of_not_ge hw).le,w.property.2⟩⟩
      have he : projIcc 0 1 zero_le_one (w:ℝ)=t :=
        projIcc_of_mem zero_le_one t.property
      rw [he,hUright]
      exact (hRplusclock t).symm
  let centerClock : Interval → Interval := fun t => ⟨b+(1-c-b)*(t:ℝ),by
    constructor <;> nlinarith only [hb.1,hc.1,hgap,t.property.1,t.property.2]⟩
  have hcenterClock (t : Interval) : 0<(centerClock t:ℝ) ∧ (centerClock t:ℝ)<1 := by
    change 0<b+(1-c-b)*(t:ℝ) ∧ b+(1-c-b)*(t:ℝ)<1
    constructor <;> nlinarith only [hb.1,hc.1,hgap,t.property.1,t.property.2]
  have hMcenter (t : Interval) : M (t,⟨0,by norm_num⟩)=a.val (centerClock t) := by
    apply Subtype.ext
    have ha := hBcenter (centerClock t) (hcenterClock t).1 (hcenterClock t).2
    apply B.injOn (hmiddles _) ha.1
    change B (M (t,⟨0,by norm_num⟩)).val=B (a.val (centerClock t)).val
    rw [hMcoord]
    change (F (t,⟨0,by norm_num⟩) 0,F (t,⟨0,by norm_num⟩) 1)=B (a.val (centerClock t)).val
    rw [hFc]
    exact ha.2.symm
  have hTLoriginalcenter (t : Interval) : TL (t,⟨0,by norm_num⟩)=
      a.val ⟨b*(t:ℝ),by constructor <;> nlinarith only [hb.1,hb.2,t.property.1,t.property.2]⟩ := by
    rw [hTLcenter,hOLcenter,hLcenter]
  have hTRoriginalcenter (t : Interval) : TR (t,⟨0,by norm_num⟩)=
      a.val ⟨1-c*(t:ℝ),by constructor <;> nlinarith only [hc.1,hc.2,t.property.1,t.property.2]⟩ := by
    rw [hTRcenter,hORcenter,hRcenter]
  have hcenterTLclear (t : Interval) : M (t,⟨0,by norm_num⟩)∉
      Set.range TL \ Set.range (fun w => TL (1,w)) := by
    rintro ⟨⟨v,he⟩,hn⟩
    have hav : TL v∈Set.range a.val := ⟨centerClock t,(he.trans (hMcenter t)).symm⟩
    have hz := (hTLaxis v).mp hav
    have hv : v=(v.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hz)
    have heold := he
    rw [hv,hTLoriginalcenter,hMcenter] at he
    have hclockEq := congrArg Subtype.val (a.property.1.injective he)
    change b*(v.1:ℝ)=b+(1-c-b)*(t:ℝ) at hclockEq
    have hv1 : v.1=1 := Subtype.ext (by
      change (v.1:ℝ)=1
      nlinarith only [hclockEq,hb.1,hgap,t.property.1,v.1.property.2])
    apply hn
    refine ⟨v.2,?_⟩
    rw [← hv1]
    exact heold
  have hcenterTRclear (t : Interval) : M (t,⟨0,by norm_num⟩)∉
      Set.range TR \ Set.range (fun w => TR (1,w)) := by
    rintro ⟨⟨v,he⟩,hn⟩
    have hav : TR v∈Set.range a.val := ⟨centerClock t,(he.trans (hMcenter t)).symm⟩
    have hz := (hTRaxis v).mp hav
    have hv : v=(v.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hz)
    have heold := he
    rw [hv,hTRoriginalcenter,hMcenter] at he
    have hclockEq := congrArg Subtype.val (a.property.1.injective he)
    change 1-c*(v.1:ℝ)=b+(1-c-b)*(t:ℝ) at hclockEq
    have hv1 : v.1=1 := Subtype.ext (by
      change (v.1:ℝ)=1
      nlinarith only [hclockEq,hc.1,hgap,t.property.2,v.1.property.2])
    apply hn
    refine ⟨v.2,?_⟩
    rw [← hv1]
    exact heold
  have actual_rectangle_two_tapered_band_clearance
      (H : C(Interval × Interval,Q S x R)) (hH : Topology.IsEmbedding H)
      (hHoutside : ∀ z,H z∉boundaryQ S x R)
      (hHleft : ∀ t,H (0,t)∈Set.range (fun w => TL (1,w)))
      (hHright : ∀ t,H (1,t)∈Set.range (fun w => TR (1,w)))
      (hHbottom : ∀ t,H (t,0)=M (t,⟨0,by norm_num⟩))
      (hHtop : ∀ t,H (t,1)∈Set.range JoinUp ∪ Set.range JoinDown) :
      (Set.range H ∩ Set.range TL ⊆ Set.range (fun w => TL (1,w))) ∧
      (Set.range H ∩ Set.range TR ⊆ Set.range (fun w => TR (1,w))) := by
    let HS : C(Interval × Interval,S) := ⟨fun z => (H z).val,
      continuous_subtype_val.comp H.continuous⟩
    have hHS : Topology.IsEmbedding HS := Topology.IsEmbedding.subtypeVal.comp hH
    have hHSoutside (z) : HS z∉boundaryCircle S x R := hHoutside z
    have hedgeL (z) (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
        HS z∉Subtype.val '' (Set.range TL \ Set.range (fun w => TL (1,w))) := by
      rintro ⟨y,⟨hy,hyn⟩,he⟩
      have heQ : y=H z := Subtype.ext he
      subst y
      rcases hz with hz | hz | hz | hz
      · have hez : z=(0,z.2) := Prod.ext hz rfl
        exact hyn (hez.symm ▸ hHleft z.2)
      · have hez : z=(1,z.2) := Prod.ext hz rfl
        have hr := hez.symm ▸ hHright z.2
        obtain ⟨w,hw⟩ := hr
        exact Set.disjoint_left.mp hTLTR hy ⟨(1,w),hw⟩
      · have hez : z=(z.1,0) := Prod.ext rfl hz
        exact hcenterTLclear z.1 (by rw [← hHbottom,← hez]; exact ⟨hy,hyn⟩)
      · have hez : z=(z.1,1) := Prod.ext rfl hz
        exact Set.disjoint_left.mp hTLjoins ⟨hy,hyn⟩ (hez.symm ▸ hHtop z.1)
    have hedgeR (z) (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
        HS z∉Subtype.val '' (Set.range TR \ Set.range (fun w => TR (1,w))) := by
      rintro ⟨y,⟨hy,hyn⟩,he⟩
      have heQ : y=H z := Subtype.ext he
      subst y
      rcases hz with hz | hz | hz | hz
      · have hez : z=(0,z.2) := Prod.ext hz rfl
        obtain ⟨w,hw⟩ := hez.symm ▸ hHleft z.2
        exact Set.disjoint_left.mp hTLTR ⟨(1,w),hw⟩ hy
      · have hez : z=(1,z.2) := Prod.ext hz rfl
        exact hyn (hez.symm ▸ hHright z.2)
      · have hez : z=(z.1,0) := Prod.ext rfl hz
        exact hcenterTRclear z.1 (by rw [← hHbottom,← hez]; exact ⟨hy,hyn⟩)
      · have hez : z=(z.1,1) := Prod.ext rfl hz
        exact Set.disjoint_left.mp hTRjoins ⟨hy,hyn⟩ (hez.symm ▸ hHtop z.1)
    have hclearL := original_endpoint_band_rectangle_clearance TL hTL hTLboundary HS hHS hHSoutside hedgeL
    have hclearR := original_endpoint_band_rectangle_clearance TR hTR hTRboundary HS hHS hHSoutside hedgeR
    constructor
    · rintro y ⟨⟨z,hz⟩,hy⟩
      have hh := hclearL ⟨⟨z,congrArg Subtype.val hz⟩,⟨y,hy,rfl⟩⟩
      obtain ⟨w,hw⟩ := hh
      exact ⟨w,Subtype.ext hw⟩
    · rintro y ⟨⟨z,hz⟩,hy⟩
      have hh := hclearR ⟨⟨z,congrArg Subtype.val hz⟩,⟨y,hy,rfl⟩⟩
      obtain ⟨w,hw⟩ := hh
      exact ⟨w,Subtype.ext hw⟩
  have actual_half_width_rectangle_clearance (sign : ℝ) (hsign : sign=1 ∨ sign= -1) :
      ∀ z : Interval × Interval,
        let w : Icc (-1 : ℝ) 1 := ⟨sign*(z.2:ℝ),actual_signed_width_bounds sign hsign z.2⟩
        (M (z.1,w)∈Set.range TL → M (z.1,w)∈Set.range (fun v => TL (1,v))) ∧
        (M (z.1,w)∈Set.range TR → M (z.1,w)∈Set.range (fun v => TR (1,v))) := by
    let k : Interval × Interval → Interval × Icc (-1 : ℝ) 1 := fun z =>
      (z.1,⟨sign*(z.2:ℝ),actual_signed_width_bounds sign hsign z.2⟩)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hs0 : sign≠0 := actual_sign_nonzero sign hsign
    have hki : Function.Injective k := by
      intro z v he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg (fun p : Interval × Icc (-1 : ℝ) 1 => (p.2:ℝ)) he
      exact Prod.ext h1 (Subtype.ext (mul_left_cancel₀ hs0 h2))
    let H : C(Interval × Interval,Q S x R) := ⟨M ∘ k,M.continuous.comp hkc⟩
    have hH : Topology.IsEmbedding H :=
      (H.continuous.isClosedEmbedding (hM.injective.comp hki)).isEmbedding
    have hHleft (t) : H (0,t)∈Set.range (fun w => TL (1,w)) :=
      ⟨(k (0,t)).2,(hM0 _).symm⟩
    have hHright (t) : H (1,t)∈Set.range (fun w => TR (1,w)) :=
      ⟨(k (1,t)).2,(hM1 _).symm⟩
    have hHbottom (t) : H (t,0)=M (t,⟨0,by norm_num⟩) := by
      apply congrArg M
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact mul_zero sign
    have hHtop (t) : H (t,1)∈Set.range JoinUp ∪ Set.range JoinDown := by
      rcases hsign with hs | hs
      · left
        refine ⟨t,?_⟩
        apply congrArg M
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [k,widthTop,hs]
      · right
        refine ⟨t,?_⟩
        apply congrArg M
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [k,widthBottom,hs]
    obtain ⟨hclearL,hclearR⟩ := actual_rectangle_two_tapered_band_clearance H hH
      (fun z => hMboundary (k z)) hHleft hHright hHbottom hHtop
    intro z
    exact ⟨fun hz => hclearL ⟨Set.mem_range_self z,hz⟩,
      fun hz => hclearR ⟨Set.mem_range_self z,hz⟩⟩
  have hMwholeclear (z : Interval × Icc (-1 : ℝ) 1) :
      (M z∈Set.range TL → M z∈Set.range (fun v => TL (1,v))) ∧
      (M z∈Set.range TR → M z∈Set.range (fun v => TR (1,v))) := by
    by_cases hw : 0≤(z.2:ℝ)
    · let t : Interval := ⟨z.2,⟨hw,z.2.property.2⟩⟩
      have hh := actual_half_width_rectangle_clearance 1 (Or.inl rfl) (z.1,t)
      simpa only [t,one_mul] using hh
    · let t : Interval := ⟨-(z.2:ℝ),⟨neg_nonneg.mpr (lt_of_not_ge hw).le,by linarith only [z.2.property.1]⟩⟩
      have hh := actual_half_width_rectangle_clearance (-1) (Or.inr rfl) (z.1,t)
      simpa only [t,neg_one_mul,neg_neg] using hh
  have hmeetTL : Set.range TL ∩ Set.range M=Set.range (fun w => TL (1,w)) := by
    apply Set.Subset.antisymm
    · rintro y ⟨hy,⟨z,rfl⟩⟩
      exact (hMwholeclear z).1 hy
    · rintro y ⟨w,rfl⟩
      exact ⟨Set.mem_range_self _,⟨(0,w),hM0 w⟩⟩
  have hmeetTR : Set.range M ∩ Set.range TR=Set.range (fun w => TR (1,w)) := by
    apply Set.Subset.antisymm
    · rintro y ⟨⟨z,rfl⟩,hy⟩
      exact (hMwholeclear z).2 hy
    · rintro y ⟨w,rfl⟩
      exact ⟨⟨(1,w),hM1 w⟩,Set.mem_range_self _⟩
  have actual_middle_strip_completes_original_band
      (L Rband : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R))
      (hL : Topology.IsEmbedding L) (hRband : Topology.IsEmbedding Rband)
      (hLR : Disjoint (Set.range L) (Set.range Rband))
      (hLstart : L (0,⟨0,by norm_num⟩)=a.val 0)
      (hRstart : Rband (0,⟨0,by norm_num⟩)=a.val 1)
      (hboundary : ∀ w,L (0,w)∈boundaryQ S x R ∧ Rband (0,w)∈boundaryQ S x R)
      (hinterior : ∀ t : Interval,0<(t:ℝ) → ∀ w,
        L (t,w)∉boundaryQ S x R ∧ Rband (t,w)∉boundaryQ S x R)
      (hLavoid : ∀ z,L z∈Set.range a.val ↔ (z.2:ℝ)=0)
      (hRavoid : ∀ z,Rband z∈Set.range a.val ↔ (z.2:ℝ)=0)
      (M : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R))
      (hM : Topology.IsEmbedding M)
      (hM0 : ∀ w,M (0,w)=L (1,w))
      (hM1 : ∀ w,M (1,w)=Rband (1,w))
      (hmeetL : Set.range L ∩ Set.range M = Set.range (fun w => L (1,w)))
      (hmeetR : Set.range M ∩ Set.range Rband = Set.range (fun w => Rband (1,w)))
      (hMa : ∀ z,M z∈Set.range a.val ↔ (z.2:ℝ)=0)
      (hMb : ∀ z,M z∉boundaryQ S x R) :
      ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R),
        Topology.IsEmbedding E ∧
        (∀ t,E (t,⟨0,by norm_num⟩)=a.val t) ∧
        (∀ w,E (0,w)∈boundaryQ S x R ∧ E (1,w)∈boundaryQ S x R) ∧
        (∀ t∈Set.Ioo (0:Interval) 1,∀ w,E (t,w)∉boundaryQ S x R) := by
    let rev : Interval × Set.Icc (-1 : ℝ) 1 → Interval × Set.Icc (-1 : ℝ) 1 :=
      fun z => (unitInterval.symm z.1,z.2)
    have hre : Topology.IsEmbedding rev :=
      unitInterval.symmHomeomorph.isEmbedding.prodMap Topology.IsEmbedding.id
    have hr0 (w : Set.Icc (-1 : ℝ) 1) : rev (0,w)=(1,w) := by simp [rev]
    have hr1 (w : Set.Icc (-1 : ℝ) 1) : rev (1,w)=(0,w) := by simp [rev]
    have hrange (P : Interval × Set.Icc (-1 : ℝ) 1 → Q S x R) :
        Set.range (P ∘ rev)=Set.range P := by
      ext y
      constructor
      · rintro ⟨z,rfl⟩
        exact Set.mem_range_self (rev z)
      · rintro ⟨z,rfl⟩
        refine ⟨rev z,?_⟩
        simp [rev]
    let Lr := L ∘ rev
    have hLr : Topology.IsEmbedding Lr := hL.comp hre
    have hLM : Set.range Lr ∩ Set.range M=Set.range (fun w => Lr (0,w)) := by
      simp only [Lr,hrange,Function.comp_apply,hr0,hmeetL]
    obtain ⟨F,hF,hF0,hF1,hFmid,hFrange,hFtrack⟩ :=
      source_glue_two_surface_strips Lr M hLr hM
        (fun w => by simpa only [Lr,Function.comp_apply,hr0] using (hM0 w).symm) hLM
    have hFstart (w) : F (0,w)=L (0,w) := by
      simpa only [Lr,Function.comp_apply,hr1] using hF0 w
    have hFend (w) : F (1,w)=Rband (1,w) := (hF1 w).trans (hM1 w)
    let Fr := F ∘ rev
    let Rr := Rband ∘ rev
    have hFr : Topology.IsEmbedding Fr := hF.comp hre
    have hRr : Topology.IsEmbedding Rr := hRband.comp hre
    have hFR : Set.range Fr ∩ Set.range Rr=Set.range (fun w => Fr (0,w)) := by
      rw [hrange,hrange,hFrange]
      change (Set.range Lr ∪ Set.range M) ∩ Set.range Rband = _
      rw [show Set.range Lr=Set.range L from hrange L]
      have heq : (Set.range L ∪ Set.range M) ∩ Set.range Rband =
          Set.range M ∩ Set.range Rband := by
        ext y
        constructor
        · rintro ⟨hy,hr⟩
          rcases hy with hl | hm
          · exact False.elim (Set.disjoint_left.mp hLR hl hr)
          · exact ⟨hm,hr⟩
        · rintro ⟨hm,hr⟩
          exact ⟨Or.inr hm,hr⟩
      rw [heq,hmeetR]
      apply congrArg Set.range
      funext w
      simp only [Fr,Function.comp_apply,hr0,hFend]
    obtain ⟨G,hG,hG0,hG1,hGmid,hGrange,hGtrack⟩ :=
      source_glue_two_surface_strips Fr Rr hFr hRr
        (fun w => by simp only [Fr,Rr,Function.comp_apply,hr0,hFend]) hFR
    have hGstart (w) : G (0,w)=L (0,w) := by
      simpa only [Fr,Function.comp_apply,hr1,hFstart] using hG0 w
    have hGend (w) : G (1,w)=Rband (0,w) := by
      simpa only [Rr,Function.comp_apply,hr1] using hG1 w
    have htracks (z) : ∃ s : Interval,
        G z=L (s,z.2) ∨ G z=M (s,z.2) ∨ G z=Rband (s,z.2) := by
      obtain ⟨t,ht | ht⟩ := hGtrack z
      · obtain ⟨s,hs | hs⟩ := hFtrack (rev (t,z.2))
        · refine ⟨unitInterval.symm s,Or.inl ?_⟩
          exact ht.trans hs
        · exact ⟨s,Or.inr (Or.inl (ht.trans hs))⟩
      · exact ⟨unitInterval.symm t,Or.inr (Or.inr ht)⟩
    have hGa (z) : G z∈Set.range a.val ↔ (z.2:ℝ)=0 := by
      obtain ⟨s,hs | hs | hs⟩ := htracks z
      · rw [hs]
        exact hLavoid _
      · rw [hs]
        exact hMa _
      · rw [hs]
        exact hRavoid _
    have hGboundary (w) : G (0,w)∈boundaryQ S x R ∧ G (1,w)∈boundaryQ S x R := by
      rw [hGstart,hGend]
      exact hboundary w
    have hGinterior (t : Interval) (ht : t∈Set.Ioo (0:Interval) 1) (w) :
        G (t,w)∉boundaryQ S x R := by
      intro hbnd
      obtain ⟨s,hs | hs | hs⟩ := htracks (t,w)
      · have hs0 : s=0 := by
          by_contra hn
          have hp : 0<(s:ℝ) := lt_of_le_of_ne s.property.1 (fun he => hn (Subtype.ext he.symm))
          exact (hinterior s hp w).1 (hs ▸ hbnd)
        subst s
        have he := hG.injective (hs.trans (hGstart w).symm)
        exact ht.1.ne' (congrArg Prod.fst he)
      · exact hMb (s,w) (hs ▸ hbnd)
      · have hs0 : s=0 := by
          by_contra hn
          have hp : 0<(s:ℝ) := lt_of_le_of_ne s.property.1 (fun he => hn (Subtype.ext he.symm))
          exact (hinterior s hp w).2 (hs ▸ hbnd)
        subst s
        have he := hG.injective (hs.trans (hGend w).symm)
        exact ht.2.ne (congrArg Prod.fst he)
    let zero : Set.Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
    let cG : Interval → Q S x R := fun t => G (t,zero)
    have hcG : Topology.IsEmbedding cG := hG.comp (isEmbedding_prodMkLeft zero)
    have hc0 : cG 0=a.val 0 := (hGstart zero).trans hLstart
    have hc1 : cG 1=a.val 1 := (hGend zero).trans hRstart
    let ca : Interval → Set.range a.val := fun t => ⟨cG t,(hGa (t,zero)).mpr rfl⟩
    have hca : Continuous ca := hcG.continuous.subtype_mk _
    let τ : Interval → Interval := a.property.1.toHomeomorph.symm ∘ ca
    have hτc : Continuous τ := a.property.1.toHomeomorph.symm.continuous.comp hca
    have hτcenter (t) : a.val (τ t)=cG t :=
      congrArg Subtype.val (a.property.1.toHomeomorph.apply_symm_apply (ca t))
    have hτ0 : τ 0=0 := a.property.1.injective ((hτcenter 0).trans hc0)
    have hτ1 : τ 1=1 := a.property.1.injective ((hτcenter 1).trans hc1)
    have hsurj : Function.Surjective τ := by
      intro v
      have hτreal : Continuous (fun t => (τ t:ℝ)) := continuous_subtype_val.comp hτc
      have hv : (v:ℝ)∈Set.Icc (τ 0:ℝ) (τ 1:ℝ) := by
        rw [hτ0,hτ1]
        exact v.property
      obtain ⟨t,ht,he⟩ := intermediate_value_Icc (show (0:Interval)≤1 by norm_num)
        hτreal.continuousOn hv
      exact ⟨t,Subtype.ext he⟩
    have hcover : Set.range a.val ⊆ Set.range cG := by
      rintro y ⟨v,rfl⟩
      obtain ⟨t,ht⟩ := hsurj v
      exact ⟨t,(hτcenter t).symm.trans (congrArg a.val ht)⟩
    let g : Interval → Set.range cG := fun t => ⟨a.val t,hcover (Set.mem_range_self t)⟩
    have hgc : Continuous g := a.val.continuous.subtype_mk _
    let q : Interval → Interval := hcG.toHomeomorph.symm ∘ g
    have hqc : Continuous q := hcG.toHomeomorph.symm.continuous.comp hgc
    have hqcenter (t) : cG (q t)=a.val t :=
      congrArg Subtype.val (hcG.toHomeomorph.apply_symm_apply (g t))
    have hqi : Function.Injective q := by
      intro t u he
      apply a.property.1.injective
      rw [← hqcenter t,← hqcenter u,he]
    have hq0 : q 0=0 := hcG.injective ((hqcenter 0).trans hc0.symm)
    have hq1 : q 1=1 := hcG.injective ((hqcenter 1).trans hc1.symm)
    let k : Interval × Set.Icc (-1 : ℝ) 1 → Interval × Set.Icc (-1 : ℝ) 1 := fun z => (q z.1,z.2)
    have hkc : Continuous k := (hqc.comp continuous_fst).prodMk continuous_snd
    have hki : Function.Injective k := by
      intro z v he
      change (q z.1,z.2) = (q v.1,v.2) at he
      have hpair : q z.1 = q v.1 ∧ z.2 = v.2 := Prod.mk.inj he
      have h1 := hpair.1
      have h2 := hpair.2
      exact Prod.ext (hqi h1) h2
    let E : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R) := ⟨G ∘ k,hG.continuous.comp hkc⟩
    have hE : Topology.IsEmbedding E := (E.continuous.isClosedEmbedding (hG.injective.comp hki)).isEmbedding
    refine ⟨E,hE,hqcenter,?_,?_⟩
    · intro w
      change G (q 0,w)∈boundaryQ S x R ∧ G (q 1,w)∈boundaryQ S x R
      rw [hq0,hq1]
      exact hGboundary w
    · intro t ht w
      apply hGinterior
      have hn0 : q t≠0 := by
        intro he
        have hh := hqi (he.trans hq0.symm)
        exact ht.1.ne' hh
      have hn1 : q t≠1 := by
        intro he
        have hh := hqi (he.trans hq1.symm)
        exact ht.2.ne hh
      constructor
      · exact lt_of_le_of_ne (show (0 : Interval) ≤ q t from (q t).property.1) (fun he => hn0 he.symm)
      · exact lt_of_le_of_ne (show q t ≤ (1 : Interval) from (q t).property.2) (fun he => hn1 he)
  suffices hband : ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R),
      Topology.IsEmbedding E ∧
      (∀ t, E (t,⟨0,by norm_num⟩) = a.val t) ∧
      (∀ w, E (0,w) ∈ boundaryQ S x R ∧ E (1,w) ∈ boundaryQ S x R) ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w, E (t,w) ∉ boundaryQ S x R) by
    obtain ⟨E,hE,hcenter,hend,hproper⟩ := hband
    exact ⟨E,hE,hcenter,hend,hproper,
      source_original_boundary_band_relative_open g hg hS hR htarget E hE hend hproper⟩
  refine actual_middle_strip_completes_original_band TL TR hTL hTR hTLTR ?_ ?_
    (fun w => ⟨hTLboundary w,hTRboundary w⟩)
    (fun t ht w => ⟨hTLinterior t ht w,hTRinterior t ht w⟩)
    hTLaxis hTRaxis M hM hM0 hM1 hmeetTL hmeetTR hMaxis hMboundary
  · rw [hTLcenter,hOLcenter,hLcenter]
    apply congrArg a.val
    apply Subtype.ext
    exact mul_zero b
  · rw [hTRcenter,hORcenter,hRcenter]
    apply congrArg a.val
    apply Subtype.ext
    simp

end CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc
