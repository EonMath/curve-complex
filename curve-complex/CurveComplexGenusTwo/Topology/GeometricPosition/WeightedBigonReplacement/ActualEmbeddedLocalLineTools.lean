import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualChartArcTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualRetainedAngularDecompositionTools
import Mathlib.Topology.Order.IntermediateValue
open Set Topology Schoenflies
namespace CurveComplex

/-- A real embedded arc confined locally to a line fills an open line segment
at each interior parameter. This supplies the trace equality needed by crossing
charts after actual finite-carrier loop erasure. -/
theorem actual_embedded_arc_local_horizontal_trace
    (f : C(Interval,(ℝ × ℝ))) (hf : Topology.IsEmbedding f)
    (t : Interval) (ht0 : 0 < t.val) (ht1 : t.val < 1)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (htU : f t ∈ U)
    (k : ℝ) (hline : ∀ q ∈ Set.range f ∩ U, q.2 = k) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (f t) ε ⊆ U ∧
      ∀ q ∈ Metric.ball (f t) ε, (q ∈ Set.range f ↔ q.2 = k) := by
  classical
  let F : ℝ → (ℝ × ℝ) := Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num) f
  have hF (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : F s = f ⟨s,hs⟩ := by
    simp only [F,Set.IccExtend,Function.comp_apply,Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) hs]
  have hcF : Continuous F := f.continuous.Icc_extend'
  have hFt : F t.val = f t := by simpa using hF t.val t.property
  have hpre : F ⁻¹' U ∈ 𝓝 t.val := hcF.continuousAt.preimage_mem_nhds
    (hU.mem_nhds (hFt.symm ▸ htU))
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  let d := min (δ/2) (min (t.val/2) ((1-t.val)/2))
  have hd : 0 < d := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hdδ : d < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd0 : d < t.val := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
  have hd1 : d < 1-t.val := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  let L := t.val-d
  let R := t.val+d
  have hLR : L < R := by dsimp [L,R]; linarith
  have hsub : Icc L R ⊆ Icc (0 : ℝ) 1 := by
    intro s hs; dsimp [L,R] at hs; constructor <;> linarith only [hs.1,hs.2,hd0,hd1]
  have hFU (s : ℝ) (hs : s ∈ Icc L R) : F s ∈ U := by
    apply hδsub
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [L,R] at hs
    constructor <;> linarith only [hs.1,hs.2,hdδ]
  have hy (s : ℝ) (hs : s ∈ Icc L R) : (F s).2 = k := by
    apply hline
    exact ⟨⟨⟨s,hsub hs⟩,(hF s (hsub hs)).symm⟩,hFU s hs⟩
  have hinj : InjOn (fun s => (F s).1) (Icc L R) := by
    intro a ha b hb he
    have heF : F a = F b := Prod.ext he ((hy a ha).trans (hy b hb).symm)
    rw [hF a (hsub ha),hF b (hsub hb)] at heF
    exact congrArg Subtype.val (hf.injective heF)
  have hc : Continuous (fun s => (F s).1) := continuous_fst.comp hcF
  have hLt : L < t.val := by dsimp [L]; linarith
  have htR : t.val < R := by dsimp [R]; linarith
  have hLL : L ∈ Icc L R := ⟨le_rfl,hLR.le⟩
  have hRR : R ∈ Icc L R := ⟨hLR.le,le_rfl⟩
  have htt : t.val ∈ Icc L R := ⟨hLt.le,htR.le⟩
  have hbracket : min (F L).1 (F R).1 < (f t).1 ∧
      (f t).1 < max (F L).1 (F R).1 := by
    rcases hc.continuousOn.strictMonoOn_of_injOn_Icc' hLR.le hinj with hm | hm
    · have h1 := hm hLL htt hLt
      have h2 := hm htt hRR htR
      dsimp only at h1 h2
      rw [hFt] at h1 h2
      exact ⟨lt_of_le_of_lt (min_le_left _ _) h1,lt_of_lt_of_le h2 (le_max_right _ _)⟩
    · have h1 := hm hLL htt hLt
      have h2 := hm htt hRR htR
      dsimp only at h1 h2
      rw [hFt] at h1 h2
      exact ⟨lt_of_le_of_lt (min_le_right _ _) h2,lt_of_lt_of_le h1 (le_max_left _ _)⟩
  obtain ⟨η,hη,hηsub⟩ := Metric.isOpen_iff.mp hU (f t) htU
  let ε := min η (min (((f t).1-min (F L).1 (F R).1)/2)
    ((max (F L).1 (F R).1-(f t).1)/2))
  have hε : 0 < ε := lt_min hη (lt_min (by linarith [hbracket.1]) (by linarith [hbracket.2]))
  refine ⟨ε,hε,?_,?_⟩
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans hηsub
  · intro q hq
    constructor
    · intro hqr
      exact hline q ⟨hqr,hηsub (Metric.ball_subset_ball (min_le_left _ _) hq)⟩
    · intro hqline
      have hdist : |q.1-(f t).1| < ε := by
        calc |q.1-(f t).1| = dist q.1 (f t).1 := (Real.dist_eq _ _).symm
          _ ≤ dist q (f t) := by rw [Prod.dist_eq]; exact le_max_left _ _
          _ < ε := hq
      have hlo : ε ≤ ((f t).1-min (F L).1 (F R).1)/2 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      have hhi : ε ≤ (max (F L).1 (F R).1-(f t).1)/2 :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hqbetween : q.1 ∈ uIcc (F L).1 (F R).1 := by
        change min (F L).1 (F R).1 ≤ q.1 ∧ q.1 ≤ max (F L).1 (F R).1
        rw [abs_lt] at hdist
        constructor <;> linarith only [hdist.1,hdist.2,hlo,hhi,hbracket.1,hbracket.2]
      obtain ⟨s,hs,hse⟩ := intermediate_value_uIcc (a := L) (b := R) (f := fun s : ℝ => (F s).1) (by simpa only [Set.uIcc_of_le hLR.le] using hc.continuousOn) hqbetween
      have hs' : s ∈ Icc L R := by simpa only [Set.uIcc_of_le hLR.le] using hs
      refine ⟨⟨s,hsub hs'⟩,?_⟩
      rw [←hF s (hsub hs')]
      exact Prod.ext hse ((hy s hs').trans hqline.symm)

/-- Localization to a real surface chart needs only the actual arc germ. -/
theorem actual_embedded_arc_local_chart_horizontal_trace
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (f : C(Interval,S)) (hf : Topology.IsEmbedding f)
    (t : Interval) (ht0 : 0 < t.val) (ht1 : t.val < 1)
    (E : OpenPartialHomeomorph S (ℝ × ℝ)) (htE : f t ∈ E.source)
    (k : ℝ) (hline : ∀ x ∈ Set.range f ∩ E.source, (E x).2 = k) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (E (f t)) ε ⊆ E.target ∧
      ∀ x ∈ E.source, dist (E x) (E (f t)) < ε →
        (x ∈ Set.range f ↔ (E x).2 = k) := by
  classical
  let F : ℝ → S := Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num) f
  have hF (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : F s = f ⟨s,hs⟩ := by
    simp only [F,Set.IccExtend,Function.comp_apply,Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) hs]
  have hcF : Continuous F := f.continuous.Icc_extend'
  have hFt : F t.val = f t := by simpa using hF t.val t.property
  have hpre : F ⁻¹' E.source ∈ 𝓝 t.val := hcF.continuousAt.preimage_mem_nhds
    (E.open_source.mem_nhds (hFt.symm ▸ htE))
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  let d := min (δ/2) (min (t.val/2) ((1-t.val)/2))
  have hd : 0 < d := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hdδ : d < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd0 : d < t.val := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
  have hd1 : d < 1-t.val := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  let θ : Interval → ℝ := fun s => t.val-d+2*d*s.val
  have hθI (s : Interval) : θ s ∈ Icc (0 : ℝ) 1 := by
    have hs := s.property
    dsimp [θ]
    constructor <;> nlinarith only [hs.1,hs.2,hd,hd0,hd1]
  have hθsource (s : Interval) : F (θ s) ∈ E.source := by
    apply hδsub
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    have hs := s.property
    dsimp [θ]
    constructor <;> nlinarith only [hs.1,hs.2,hd,hdδ]
  have hcθ : Continuous θ := by fun_prop
  let g : C(Interval,ℝ × ℝ) := ⟨fun s => E (F (θ s)),
    E.continuousOn.comp_continuous (hcF.comp hcθ) hθsource⟩
  have hg : Topology.IsEmbedding g := by
    have hi : Function.Injective g := by
      intro a b he
      have heF := E.injOn (hθsource a) (hθsource b) he
      rw [hF (θ a) (hθI a),hF (θ b) (hθI b)] at heF
      have heθ := congrArg Subtype.val (hf.injective heF)
      apply Subtype.ext
      dsimp [θ] at heθ
      nlinarith only [heθ,hd]
    exact (g.continuous.isClosedEmbedding hi).isEmbedding
  let m : Interval := ⟨1/2,by constructor <;> norm_num⟩
  have hm : g m = E (f t) := by
    have hθm : θ m = t.val := by dsimp [θ,m]; ring
    change E (F (θ m)) = E (f t)
    rw [hθm,hFt]
  have hgl : ∀ q ∈ Set.range g ∩ E.target, q.2 = k := by
    rintro q ⟨⟨s,rfl⟩,hq⟩
    apply hline
    exact ⟨⟨⟨θ s,hθI s⟩,(hF (θ s) (hθI s)).symm⟩,hθsource s⟩
  obtain ⟨ε,hε,hεsub,htrace⟩ := actual_embedded_arc_local_horizontal_trace g hg m
    (by norm_num [m]) (by norm_num [m]) E.target E.open_target
    (E.map_source (hθsource m)) k hgl
  rw [hm] at hεsub htrace
  refine ⟨ε,hε,hεsub,?_⟩
  intro x hx hdist
  constructor
  · intro hxf
    exact hline x ⟨hxf,hx⟩
  · intro hxk
    have hxg := (htrace (E x) hdist).mpr hxk
    obtain ⟨s,hs⟩ := hxg
    have hex : F (θ s) = x := E.injOn (hθsource s) hx hs
    refine ⟨⟨θ s,hθI s⟩,?_⟩
    rw [←hF (θ s) (hθI s)]
    exact hex

/-- Whole embedded-circle traces fill each locally containing affine line. -/
theorem actual_embedded_curve_local_horizontal_trace
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (c : Curve S) (E : OpenPartialHomeomorph S (ℝ × ℝ))
    (p : S) (hp : p ∈ c.image ∩ E.source) (k : ℝ)
    (hline : ∀ x ∈ c.image ∩ E.source, (E x).2 = k) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (E p) ε ⊆ E.target ∧
      ∀ x ∈ E.source, dist (E x) (E p) < ε → (x ∈ c.image ↔ (E x).2 = k) := by
  obtain ⟨q,hq⟩ := hp.1
  have hπ := Real.pi_pos
  have hspan : Real.pi/2-(-Real.pi/2) < 2*Real.pi := by linarith
  obtain ⟨f,hf,hRange⟩ := actual_original_angular_subarc c q (-Real.pi/2) (Real.pi/2)
    (by linarith) hspan
  have hSub : Set.range f ⊆ c.image := by
    rw [hRange]
    rintro x ⟨θ,hθ,rfl⟩
    exact ⟨q*Circle.exp θ,rfl⟩
  have hpF : p ∈ Set.range f := by
    rw [hRange]
    refine ⟨0,⟨by linarith,by linarith⟩,?_⟩
    simpa using hq
  have hEndNe (θ : ℝ) (hθ : θ ∈ Icc (-Real.pi/2) (Real.pi/2)) (hθ0 : θ ≠ 0) :
      c.map (q*Circle.exp θ) ≠ p := by
    intro he
    have hc : Circle.exp θ = Circle.exp 0 := by
      apply mul_left_cancel (a := q)
      apply c.embedded.injective
      simpa using he.trans hq.symm
    have hθeq := Circle.exp_injOn_Icc hspan hθ (show (0 : ℝ) ∈ Icc (-Real.pi/2) (Real.pi/2) from ⟨by linarith,by linarith⟩) hc
    exact hθ0 hθeq
  have h0 : f 0 ≠ p := by
    rw [f.source]
    exact hEndNe _ ⟨le_rfl,by linarith⟩ (by linarith)
  have h1 : f 1 ≠ p := by
    rw [f.target]
    exact hEndNe _ ⟨by linarith,le_rfl⟩ (by linarith)
  obtain ⟨s,hs⟩ := hpF
  have hs0 : 0 < s.val := by
    have hn : s ≠ 0 := by intro he; subst s; exact h0 hs
    exact lt_of_le_of_ne s.property.1 (by intro he; apply hn; apply Subtype.ext; exact he.symm)
  have hs1 : s.val < 1 := by
    have hn : s ≠ 1 := by intro he; subst s; exact h1 hs
    exact lt_of_le_of_ne s.property.2 (by intro he; apply hn; apply Subtype.ext; exact he)
  let F : C(Interval,S) := ⟨f,f.continuous⟩
  obtain ⟨ε,hε,hεsub,htrace⟩ := actual_embedded_arc_local_chart_horizontal_trace F hf s hs0 hs1 E
    (hs.symm ▸ hp.2) k (fun x hx => hline x ⟨hSub hx.1,hx.2⟩)
  change Metric.ball (E (f s)) ε ⊆ E.target at hεsub
  change ∀ x ∈ E.source, dist (E x) (E (f s)) < ε → (x ∈ Set.range f ↔ (E x).2 = k) at htrace
  rw [hs] at hεsub htrace
  refine ⟨ε,hε,hεsub,?_⟩
  intro x hx hd
  exact ⟨fun hxc => hline x ⟨hxc,hx⟩,fun hxl => hSub ((htrace x hx hd).mpr hxl)⟩

/-- Actual affine containment of a whole embedded curve yields an exact local
crossing-chart trace; no converse trace is assumed. -/
theorem actual_embedded_curve_local_affine_graph_trace
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (c : Curve S) (E : OpenPartialHomeomorph S (ℝ × ℝ))
    (p : S) (hp : p ∈ c.image ∩ E.source) (t α k : ℝ)
    (hgraph : ∀ x ∈ c.image ∩ E.source, (E x).1 = α+k*((E x).2-t)) :
    ∃ E' : OpenPartialHomeomorph S (ℝ × ℝ), p ∈ E'.source ∧
      E'.source ⊆ E.source ∧ (∀ x, E' x = E x) ∧
      ∀ x ∈ E'.source, (x ∈ c.image ↔ (E' x).1 = α+k*((E' x).2-t)) := by
  let N : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
    toFun := fun q => (q.2-t,q.1-α-k*(q.2-t))
    invFun := fun q => (q.2+α+k*q.1,q.1+t)
    left_inv := by intro q; ext <;> dsimp <;> ring
    right_inv := by intro q; ext <;> dsimp <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let F := E.transHomeomorph N
  have hpF : p ∈ F.source := hp.2
  have hline : ∀ x ∈ c.image ∩ F.source, (F x).2 = 0 := by
    intro x hx
    change (E x).1-α-k*((E x).2-t) = 0
    rw [hgraph x hx]
    ring
  obtain ⟨ε,hε,hεsub,htrace⟩ := actual_embedded_curve_local_horizontal_trace c F p ⟨hp.1,hpF⟩ 0 hline
  let O := F.source ∩ F ⁻¹' Metric.ball (F p) ε
  have hO : IsOpen O := F.isOpen_inter_preimage Metric.isOpen_ball
  let E' := E.restrOpen O hO
  have hpE' : p ∈ E'.source := ⟨hp.2,hpF,by simp [hε]⟩
  refine ⟨E',hpE',(fun x hx => hx.1),(fun x => rfl),?_⟩
  intro x hx
  have hxF : x ∈ F.source := hx.2.1
  have hd : dist (F x) (F p) < ε := hx.2.2
  have he := htrace x hxF hd
  change (x ∈ c.image ↔ (E x).1 = α+k*((E x).2-t))
  change (x ∈ c.image ↔ (E x).1-α-k*((E x).2-t) = 0) at he
  rw [he]
  constructor <;> intro h <;> linarith

end CurveComplex
