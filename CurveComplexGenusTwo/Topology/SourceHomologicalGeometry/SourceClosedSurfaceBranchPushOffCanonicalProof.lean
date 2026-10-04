import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualSmallSupportedTranslation
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnClosedPushedCurve
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualCompactChartDisplacement
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnCapsDisplacement
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualOldFirstPorts
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualOldClosingPorts
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualOldMiddleDecomposition
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualStripSurfaceChart
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualCurveCrosscutReplacement
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualTraceTransverseStatement
set_option maxHeartbeats 3000000
namespace CurveComplex
open Set Topology Schoenflies Metric
open scoped NNReal
/-- Actual first-return branch push-off by one cap translation and two
whole-curve supported crosscut replacements, retaining the original budgets. -/
theorem source_closed_surface_first_return_branch_push_off
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ d : Curve S,
      AmbientIsotopy.Rel (B.boundary i).image d.image ∧
      ∃ hbd : Transverse b d, ∃ had : Transverse a d,
        hbd.1.toFinset.card ≤ 1 ∧
        had.1.toFinset.card ≤
          (source_surgery_retained_crossings B i).ncard + 1 := by
  have hCompact := source_compact_chart_displacement_radius (S := S)
  have hCapsBound := source_framed_first_return_caps_with_displacement S D B ht i
  have hOldFirstPorts := source_first_return_actual_old_first_ports S D B i
  have hOldClosingPorts := source_first_return_actual_old_closing_ports S D B i
  have hRetainTwo
      (E : Bool → OpenPartialHomeomorph S Plane)
      (hsquare : ∀ k, Plane.closedSquare (0 : Plane) 1 ⊆ (E k).target)
      (K U : Set S) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
      ∃ r : ℝ, 0<r ∧ ∀ (H : AmbientIsotopy S) (v : Bool → Plane),
        (∀ k, ‖v k‖<r) →
        (∀ t x, x ∉ (E false).source ∪ (E true).source → H.map (t,x)=x) →
        (∀ k t x, x ∈ (E k).source → H.map (t,x) ∈ (E k).source) →
        (∀ k t x, x ∈ (E k).source → 1/2 ≤ ‖E k x‖ → H.map (t,x)=x) →
        (∀ k t x, x ∈ (E k).source → ‖E k (H.map (t,x))-E k x‖ ≤ ‖v k‖) →
        ∀ t, (fun x=>H.map (t,x)) '' K ⊆ U := by
    classical
    choose rk hrk hretain using fun k=>hCompact (E k) (hsquare k) K U hK hU hKU
    let r : ℝ := min (rk false) (rk true)
    have hr : 0<r := lt_min (hrk false) (hrk true)
    have hrr (k : Bool) : r≤rk k := by cases k; exact min_le_left _ _; exact min_le_right _ _
    refine ⟨r,hr,?_⟩
    intro H v hv hfix hsource hfar hdisp t
    have hinside (k : Bool) (x : S) (hxK : x ∈ K) (hxE : x ∈ (E k).source) :
        H.map (t,x) ∈ U := by
      let f : S → S := fun y=>if y ∈ (E k).source then H.map (t,y) else y
      have hffix (y : S) (hy : y ∉ (E k).source) : f y=y := by simp only [f,ite_eq_right hy]
      have hfsource (y : S) (hy : y ∈ (E k).source) : f y ∈ (E k).source := by
        simp only [f,ite_eq_left hy]
        exact hsource k t y hy
      have hffar (y : S) (hy : y ∈ (E k).source) (hn : 1/2≤‖E k y‖) : f y=y := by
        simp only [f,ite_eq_left hy]
        exact hfar k t y hy hn
      have hfdisp (y : S) (hy : y ∈ (E k).source) : ‖E k (f y)-E k y‖<rk k := by
        simp only [f,ite_eq_left hy]
        exact (hdisp k t y hy).trans_lt ((hv k).trans_le (hrr k))
      have hu : f x ∈ U := hretain k f hffix hfsource hffar hfdisp ⟨x,hxK,rfl⟩
      simpa only [f,ite_eq_left hxE] using hu
    rintro y ⟨x,hxK,rfl⟩
    change H.map (t,x) ∈ U
    by_cases hx0 : x ∈ (E false).source
    · exact hinside false x hxK hx0
    · by_cases hx1 : x ∈ (E true).source
      · exact hinside true x hxK hx1
      · rw [hfix t x (by simpa only [Set.mem_union,not_or] using ⟨hx0,hx1⟩)]
        exact hKU hxK
  have hCapsRetain
      (F : SourceFirstReturnFramedStrips D B i)
      (K U : Set S) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
      (rmax : ℝ) (hrmax : 0<rmax) :
      ∃ A : SourceFirstReturnAttachedCaps F,
        (∀ k, ‖A.v k‖<rmax) ∧
        ∀ t, (fun x=>A.H.map (t,x)) '' K ⊆ U := by
    obtain ⟨r,hr,hretain⟩ := hRetainTwo F.E F.square K U hK hU hKU
    obtain ⟨A,hv,hfar,hdisp⟩ := hCapsBound F (min r rmax) (lt_min hr hrmax)
    refine ⟨A,fun k=>(hv k).trans_le (min_le_right _ _),?_⟩
    exact hretain A.H A.v (fun k=>(hv k).trans_le (min_le_left _ _))
      A.fixed A.source_preserved hfar hdisp
  have hParameterBetweenPorts
      (z : C(Interval,ℝ)) (l r : ℝ) (hlr : l<r)
      (hz0 : z 0=l) (hz1 : z 1=r)
      (hports : ∀ t, z t=l ∨ z t=r → t=0 ∨ t=1) :
      ∀ t : Interval, 0<(t:ℝ) → (t:ℝ)<1 → l<z t ∧ z t<r := by
    have hleft (t : Interval) (ht : t ∈ Set.Ioc (0:Interval) 1) : z t≠l := by
      intro he
      rcases hports t (Or.inl he) with he0|he1
      · exact ht.1.ne' he0
      · rw [he1,hz1] at he
        exact hlr.ne' he
    have hright (t : Interval) (ht : t ∈ Set.Ico (0:Interval) 1) : z t≠r := by
      intro he
      rcases hports t (Or.inr he) with he0|he1
      · rw [he0,hz0] at he
        exact hlr.ne he
      · exact ht.2.ne he1
    intro t ht0 ht1
    have ht0' : (0:Interval)<t := ht0
    have ht1' : t<(1:Interval) := ht1
    refine ⟨?_,?_⟩
    · exact isPreconnected_Ioc.lt_of_ne z.continuous.continuousOn hleft
        ⟨1,⟨by norm_num,le_rfl⟩,hz1 ▸ hlr⟩ ⟨ht0',t.property.2⟩
    · exact isPreconnected_Ico.gt_of_ne z.continuous.continuousOn hright
        ⟨0,⟨le_rfl,by norm_num⟩,hz0 ▸ hlr⟩ ⟨t.property.1,ht1'⟩
  have hPlaneQuarterBound (q : Plane)
      (h0 : |q 0|≤1/16) (h1 : |q 1|≤5/32) : ‖q‖≤1/4 := by
    have hn : ‖q‖^2=(q 0)^2+(q 1)^2 := by
      have he := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2=>ℝ) q
      simpa [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs] using he
    have hz := abs_le.mp h0
    have ho := abs_le.mp h1
    have hsq0 : (q 0)^2≤(1/16:ℝ)^2 := by
      nlinarith [mul_nonneg (by linarith : 0≤1/16-q 0) (by linarith : 0≤1/16+q 0)]
    have hsq1 : (q 1)^2≤(5/32:ℝ)^2 := by
      nlinarith [mul_nonneg (by linarith : 0≤5/32-q 1) (by linarith : 0≤5/32+q 1)]
    nlinarith [norm_nonneg q]
  have hPlaneQuarterBoundSym (q : Plane)
      (h0 : |q 0|≤5/32) (h1 : |q 1|≤1/16) : ‖q‖≤1/4 := by
    have hn : ‖q‖^2=(q 0)^2+(q 1)^2 := by
      have he := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2=>ℝ) q
      simpa [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs] using he
    have hz := abs_le.mp h0
    have ho := abs_le.mp h1
    have hsq0 : (q 0)^2≤(5/32:ℝ)^2 := by
      nlinarith [mul_nonneg (by linarith : 0≤5/32-q 0) (by linarith : 0≤5/32+q 0)]
    have hsq1 : (q 1)^2≤(1/16:ℝ)^2 := by
      nlinarith [mul_nonneg (by linarith : 0≤1/16-q 1) (by linarith : 0≤1/16+q 1)]
    nlinarith [norm_nonneg q]
  have hFirstVerticalSideSmall
      (F : SourceFirstReturnFramedStrips D B i)
      (A : SourceFirstReturnAttachedCaps F) (k : Bool)
      (w : Set.Icc (-1:ℝ) 1)
      (hwidth : |F.α k*(w:ℝ)|≤1/32) (hv : ‖A.v k‖<1/32) :
      ‖F.E k (F.N (F.θf k,w))-A.v k‖≤1/4 := by
    have hframe := (F.first_framing k (F.θf k) w
      (by simpa using (F.corner_positive k).2.2.1)).2
    have hv0 : |A.v k 0|≤‖A.v k‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A.v k) 0
    have hv1 : |A.v k 1|≤‖A.v k‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A.v k) 1
    apply hPlaneQuarterBound
    · have he := congrArg (fun q : Plane=>q 0) hframe
      change |F.E k (F.N (F.θf k,w)) 0-A.v k 0|≤1/16
      rw [he]
      change |F.α k*(w:ℝ)-A.v k 0|≤1/16
      exact (abs_sub _ _).trans (by linarith)
    · have he := congrArg (fun q : Plane=>q 1) hframe
      change |F.E k (F.N (F.θf k,w)) 1-A.v k 1|≤5/32
      rw [he]
      change |F.E k (D.first (F.θf k)) 1-A.v k 1|≤5/32
      have hh := F.first_height k
      have hhabs : |F.E k (D.first (F.θf k)) 1|≤1/8 := by
        rw [abs_of_pos hh.1]
        exact hh.2
      exact (abs_sub _ _).trans (by linarith)
  have hFirstVerticalSideContact
      (F : SourceFirstReturnFramedStrips D B i)
      (A : SourceFirstReturnAttachedCaps F) (k : Bool)
      (w : Set.Icc (-1:ℝ) 1)
      (hsmall : ‖F.E k (F.N (F.θf k,w))-A.v k‖≤1/4)
      (hheight : A.v k 1<F.E k (D.first (F.θf k)) 1) :
      F.N (F.θf k,w) ∈ A.d.image ↔ w=A.w := by
    have hframe := F.first_framing k (F.θf k) w
      (by simpa using (F.corner_positive k).2.2.1)
    constructor
    · intro hx
      have hshape := (A.local_trace k _ hframe.1 hsmall).mp hx
      have hn : F.E k (F.N (F.θf k,w)) 0=F.α k*(w:ℝ) :=
        congrArg (fun q : Plane=>q 0) hframe.2
      have hl : F.E k (F.N (F.θf k,w)) 1=F.E k (D.first (F.θf k)) 1 := by
        have he := congrArg (fun q : Plane=>q 1) hframe.2
        exact he
      have hv : A.v k 0=F.α k*(A.w:ℝ) :=
        congrArg (fun q : Plane=>q 0) (A.displacement k)
      rcases hshape with hh|hh
      · have he : F.α k*(w:ℝ)=F.α k*(A.w:ℝ) := by linarith [hh.1]
        exact Subtype.ext ((mul_left_cancel₀ (F.corner_positive k).1) he)
      · have he := hh.2
        linarith
    · intro he
      subst w
      rw [← A.first_port]
      exact (A.subset k (Set.mem_range_self 0)).2
  have hClosingHorizontalSideSmall
      (F : SourceFirstReturnFramedStrips D B i)
      (A : SourceFirstReturnAttachedCaps F) (k : Bool)
      (w : Set.Icc (-1:ℝ) 1)
      (hwidth : |F.β k*(w:ℝ)|≤1/32) (hv : ‖A.v k‖<1/32) :
      ‖F.E k (F.M (F.θg k,w))-A.v k‖≤1/4 := by
    have hframe := (F.closing_framing k (F.θg k) w
      (by simpa using (F.corner_positive k).2.2.2)).2
    have hv0 : |A.v k 0|≤‖A.v k‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A.v k) 0
    have hv1 : |A.v k 1|≤‖A.v k‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A.v k) 1
    apply hPlaneQuarterBoundSym
    · have he := congrArg (fun q : Plane=>q 0) hframe
      change |F.E k (F.M (F.θg k,w)) 0-A.v k 0|≤5/32
      rw [he]
      change |F.E k (B.closing i (F.θg k)) 0-A.v k 0|≤5/32
      have hh := F.closing_height k
      have hhabs : |F.E k (B.closing i (F.θg k)) 0|≤1/8 := by
        rw [abs_of_pos hh.1]
        exact hh.2
      exact (abs_sub _ _).trans (by linarith)
    · have he := congrArg (fun q : Plane=>q 1) hframe
      change |F.E k (F.M (F.θg k,w)) 1-A.v k 1|≤1/16
      rw [he]
      change |F.β k*(w:ℝ)-A.v k 1|≤1/16
      exact (abs_sub _ _).trans (by linarith)
  have hClosingHorizontalSideContact
      (F : SourceFirstReturnFramedStrips D B i)
      (A : SourceFirstReturnAttachedCaps F) (k : Bool)
      (w : Set.Icc (-1:ℝ) 1)
      (hsmall : ‖F.E k (F.M (F.θg k,w))-A.v k‖≤1/4)
      (hheight : A.v k 0<F.E k (B.closing i (F.θg k)) 0) :
      F.M (F.θg k,w) ∈ A.d.image ↔ w=A.z := by
    have hframe := F.closing_framing k (F.θg k) w
      (by simpa using (F.corner_positive k).2.2.2)
    constructor
    · intro hx
      have hshape := (A.local_trace k _ hframe.1 hsmall).mp hx
      have hn : F.E k (F.M (F.θg k,w)) 1=F.β k*(w:ℝ) := by
        have he := congrArg (fun q : Plane=>q 1) hframe.2
        exact he
      have hl : F.E k (F.M (F.θg k,w)) 0=F.E k (B.closing i (F.θg k)) 0 := by
        have he := congrArg (fun q : Plane=>q 0) hframe.2
        exact he
      have hv : A.v k 1=F.β k*(A.z:ℝ) :=
        congrArg (fun q : Plane=>q 1) (A.displacement k)
      rcases hshape with hh|hh
      · linarith [hh.1]
      · have he : F.β k*(w:ℝ)=F.β k*(A.z:ℝ) := by linarith [hh.2]
        exact Subtype.ext ((mul_left_cancel₀ (F.corner_positive k).2.1) he)
    · intro he
      subst w
      rw [← A.closing_port]
      exact (A.subset k (Set.mem_range_self 1)).2
  have hActualFirstVerticalSides
      (F : SourceFirstReturnFramedStrips D B i) :
      ∃ ρ r : ℝ, 0<ρ ∧ ρ<1 ∧ 0<r ∧
        ∀ A : SourceFirstReturnAttachedCaps F, (∀ k, ‖A.v k‖<r) →
        ∀ k (w : Set.Icc (-1:ℝ) 1), |(w:ℝ)|≤ρ →
          (F.N (F.θf k,w) ∈ A.d.image ↔ w=A.w) := by
    let m : ℝ := max |F.α false| |F.α true|+1
    have hm : 0 < m := by dsimp [m]; linarith [abs_nonneg (F.α false),le_max_left |F.α false| |F.α true|]
    let ρ : ℝ := min (1/2) ((1/32)/m)
    have hρ : 0<ρ := lt_min (by norm_num) (div_pos (by norm_num) hm)
    have hρlt : ρ<1 := (min_le_left _ _).trans_lt (by norm_num)
    let h : Bool → ℝ := fun k=>F.E k (D.first (F.θf k)) 1
    let r : ℝ := min (1/32) (min (h false/2) (h true/2))
    have hr : 0<r := lt_min (by norm_num)
      (lt_min (half_pos (F.first_height false).1) (half_pos (F.first_height true).1))
    have hrh (k : Bool) : r≤h k/2 := by
      cases k
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨ρ,r,hρ,hρlt,hr,?_⟩
    intro A hv k w hw
    have hvsmall : ‖A.v k‖<1/32 := (hv k).trans_le (min_le_left _ _)
    have hwm : |(w:ℝ)| *m≤1/32 := (le_div_iff₀ hm).mp (hw.trans (min_le_right _ _))
    have ham : |F.α k| ≤ m := by
      cases k
      · dsimp [m]; linarith [le_max_left |F.α false| |F.α true|]
      · dsimp [m]; linarith [le_max_right |F.α false| |F.α true|]
    have hwidth : |F.α k*(w:ℝ)|≤1/32 := by
      rw [abs_mul]
      calc
        |F.α k| * |(w:ℝ)| ≤ m* |(w:ℝ)| := mul_le_mul_of_nonneg_right ham (abs_nonneg _)
        _ ≤ 1/32 := by nlinarith [hwm]
    have hvcoord : |A.v k 1|≤‖A.v k‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A.v k) 1
    have hvheight : A.v k 1<h k := by
      have hh := F.first_height k
      change 0<h k ∧ h k≤1/8 at hh
      have hvr := (hv k).trans_le (hrh k)
      linarith [le_abs_self (A.v k 1)]
    exact hFirstVerticalSideContact F A k w (hFirstVerticalSideSmall F A k w hwidth hvsmall) hvheight
  have hActualClosingVerticalSides
      (F : SourceFirstReturnFramedStrips D B i) :
      ∃ ρ r : ℝ, 0<ρ ∧ ρ<1 ∧ 0<r ∧
        ∀ A : SourceFirstReturnAttachedCaps F, (∀ k, ‖A.v k‖<r) →
        ∀ k (w : Set.Icc (-1:ℝ) 1), |(w:ℝ)|≤ρ →
          (F.M (F.θg k,w) ∈ A.d.image ↔ w=A.z) := by
    let m : ℝ := max |F.β false| |F.β true|+1
    have hm : 0 < m := by dsimp [m]; linarith [abs_nonneg (F.β false),le_max_left |F.β false| |F.β true|]
    let ρ : ℝ := min (1/2) ((1/32)/m)
    have hρ : 0<ρ := lt_min (by norm_num) (div_pos (by norm_num) hm)
    have hρlt : ρ<1 := (min_le_left _ _).trans_lt (by norm_num)
    let h : Bool → ℝ := fun k=>F.E k (B.closing i (F.θg k)) 0
    let r : ℝ := min (1/32) (min (h false/2) (h true/2))
    have hr : 0<r := lt_min (by norm_num)
      (lt_min (half_pos (F.closing_height false).1) (half_pos (F.closing_height true).1))
    have hrh (k : Bool) : r≤h k/2 := by
      cases k
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨ρ,r,hρ,hρlt,hr,?_⟩
    intro A hv k w hw
    have hvsmall : ‖A.v k‖<1/32 := (hv k).trans_le (min_le_left _ _)
    have hwm : |(w:ℝ)| *m≤1/32 := (le_div_iff₀ hm).mp (hw.trans (min_le_right _ _))
    have ham : |F.β k| ≤ m := by
      cases k
      · dsimp [m]; linarith [le_max_left |F.β false| |F.β true|]
      · dsimp [m]; linarith [le_max_right |F.β false| |F.β true|]
    have hwidth : |F.β k*(w:ℝ)|≤1/32 := by
      rw [abs_mul]
      calc
        |F.β k| * |(w:ℝ)| ≤ m* |(w:ℝ)| := mul_le_mul_of_nonneg_right ham (abs_nonneg _)
        _ ≤ 1/32 := by nlinarith [hwm]
    have hvcoord : |A.v k 0|≤‖A.v k‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A.v k) 0
    have hvheight : A.v k 0<h k := by
      have hh := F.closing_height k
      change 0<h k ∧ h k≤1/8 at hh
      have hvr := (hv k).trans_le (hrh k)
      linarith [le_abs_self (A.v k 0)]
    exact hClosingHorizontalSideContact F A k w (hClosingHorizontalSideSmall F A k w hwidth hvsmall) hvheight
  have hFirstHorizontalRetention
      (F : SourceFirstReturnFramedStrips D B i)
      (hband : ∀ u ∈ Set.Icc (F.θf false) (F.θf true), ∀ w : Set.Icc (-1:ℝ) 1,
        F.N (u,w) ∉ b.image)
      (w : Set.Icc (-1:ℝ) 1) (hw : (w:ℝ)≠0)
      (rmax : ℝ) (hrmax : 0<rmax) :
      ∃ A : SourceFirstReturnAttachedCaps F,
        (∀ k, ‖A.v k‖<rmax) ∧ ∀ t,
        Disjoint ((fun x=>A.H.map (t,x)) '' (B.boundary i).image)
          (F.N '' (Set.Icc (F.θf false) (F.θf true) ×ˢ {w})) := by
    let X := F.N '' (Set.Icc (F.θf false) (F.θf true) ×ˢ {w})
    have hX : IsCompact X := (isCompact_Icc.prod (isCompact_singleton : IsCompact {w})).image F.first_embedding.continuous
    have hraw : (B.boundary i).image ⊆ Xᶜ := by
      intro x hx hxX
      obtain ⟨⟨u,z⟩,⟨hu,hz⟩,he⟩ := hxX
      have hzw : z=w := Set.mem_singleton_iff.mp hz
      subst z
      rw [B.boundary_image] at hx
      rcases hx with hx|hx
      · obtain ⟨t,ht⟩ := hx
        have hc : F.N (u,w)=F.N (t,⟨0,by norm_num⟩) := by
          rw [F.first_center]
          exact he.trans ht.symm
        have hp := F.first_embedding.injective hc
        exact hw (congrArg (fun q : Interval × Set.Icc (-1:ℝ) 1=>(q.2:ℝ)) hp)
      · have hb : x ∈ b.image := by
          rw [← B.closing_cover]
          cases i
          · exact Or.inl hx
          · exact Or.inr hx
        exact hband u hu w (he ▸ hb)
    obtain ⟨A,hsmall,hretain⟩ := hCapsRetain F (B.boundary i).image Xᶜ
      (isCompact_range (B.boundary i).embedded.continuous) hX.isClosed.isOpen_compl hraw rmax hrmax
    refine ⟨A,hsmall,?_⟩
    intro t
    exact Set.disjoint_left.mpr (fun _ hx hxX=>hretain t hx hxX)
  have hFirstCoreCompactRetention
      (F : SourceFirstReturnFramedStrips D B i)
      (lo hi : Interval) (hlo : 0<(lo:ℝ)) (hhi : (hi:ℝ)<1)
      (ρ : ℝ) (hρ : 0<ρ) :
      ∃ E : OpenPartialHomeomorph S Plane,
        E.source=F.N '' {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧ -1<(z.2:ℝ) ∧ (z.2:ℝ)<1} ∧
        E.target={z : Plane | 0<z 0 ∧ z 0<1 ∧ -1<z 1 ∧ z 1<1} ∧
        (∀ z, 0<(z.1:ℝ) → (z.1:ℝ)<1 → -1<(z.2:ℝ) → (z.2:ℝ)<1 →
          E (F.N z)=Plane.mk z.1 z.2) ∧
        ∃ r : ℝ, 0<r ∧ ∀ (H : AmbientIsotopy S) (v : Bool → Plane),
          (∀ k, ‖v k‖<r) →
          (∀ t x, x ∉ (F.E false).source ∪ (F.E true).source → H.map (t,x)=x) →
          (∀ k t x, x ∈ (F.E k).source → H.map (t,x) ∈ (F.E k).source) →
          (∀ k t x, x ∈ (F.E k).source → 1/2≤‖F.E k x‖ → H.map (t,x)=x) →
          (∀ k t x, x ∈ (F.E k).source → ‖F.E k (H.map (t,x))-F.E k x‖≤‖v k‖) →
          ∀ t u, u ∈ Set.Icc lo hi →
            H.map (t,D.first u) ∈ E.source ∧ |E (H.map (t,D.first u)) 1|<ρ := by
    obtain ⟨E,hEs,hEt,hcoord,_haxis⟩ := source_embedded_strip_interior_chart
      F.N F.first_embedding D.first F.first_center
    let K := D.first '' Set.Icc lo hi
    let U := E.source ∩ E ⁻¹' {z : Plane | |z 1|<ρ}
    have hK : IsCompact K := isCompact_Icc.image D.first.continuous
    have hU : IsOpen U := E.isOpen_inter_preimage
      (isOpen_lt (by fun_prop) continuous_const)
    have hKU : K ⊆ U := by
      rintro x ⟨u,hu,rfl⟩
      have hu0 : 0<(u:ℝ) := hlo.trans_le hu.1
      have hu1 : (u:ℝ)<1 := (show (u:ℝ)≤(hi:ℝ) from hu.2).trans_lt hhi
      refine ⟨?_,?_⟩
      · rw [hEs]
        exact ⟨(u,⟨0,by norm_num⟩),⟨hu0,hu1,by norm_num,by norm_num⟩,F.first_center u⟩
      · change |E (D.first u) 1|<ρ
        rw [← F.first_center u,hcoord (u,⟨0,by norm_num⟩) hu0 hu1 (by norm_num) (by norm_num)]
        simpa using hρ
    obtain ⟨r,hr,hretain⟩ := hRetainTwo F.E F.square K U hK hU hKU
    refine ⟨E,hEs,hEt,hcoord,r,hr,?_⟩
    intro H v hv hfix hsource hfar hdisp t u hu
    exact hretain H v hv hfix hsource hfar hdisp t ⟨D.first u,⟨u,hu,rfl⟩,rfl⟩
  have hClosingCoreCompactRetention
      (F : SourceFirstReturnFramedStrips D B i)
      (lo hi : Interval) (hlo : 0<(lo:ℝ)) (hhi : (hi:ℝ)<1)
      (ρ : ℝ) (hρ : 0<ρ) :
      ∃ E : OpenPartialHomeomorph S Plane,
        E.source=F.M '' {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧ -1<(z.2:ℝ) ∧ (z.2:ℝ)<1} ∧
        E.target={z : Plane | 0<z 0 ∧ z 0<1 ∧ -1<z 1 ∧ z 1<1} ∧
        (∀ z, 0<(z.1:ℝ) → (z.1:ℝ)<1 → -1<(z.2:ℝ) → (z.2:ℝ)<1 →
          E (F.M z)=Plane.mk z.1 z.2) ∧
        ∃ r : ℝ, 0<r ∧ ∀ (H : AmbientIsotopy S) (v : Bool → Plane),
          (∀ k, ‖v k‖<r) →
          (∀ t x, x ∉ (F.E false).source ∪ (F.E true).source → H.map (t,x)=x) →
          (∀ k t x, x ∈ (F.E k).source → H.map (t,x) ∈ (F.E k).source) →
          (∀ k t x, x ∈ (F.E k).source → 1/2≤‖F.E k x‖ → H.map (t,x)=x) →
          (∀ k t x, x ∈ (F.E k).source → ‖F.E k (H.map (t,x))-F.E k x‖≤‖v k‖) →
          ∀ t u, u ∈ Set.Icc lo hi →
            H.map (t,B.closing i u) ∈ E.source ∧ |E (H.map (t,B.closing i u)) 1|<ρ := by
    obtain ⟨E,hEs,hEt,hcoord,_haxis⟩ := source_embedded_strip_interior_chart
      F.M F.closing_embedding (B.closing i) F.closing_center
    let K := B.closing i '' Set.Icc lo hi
    let U := E.source ∩ E ⁻¹' {z : Plane | |z 1|<ρ}
    have hK : IsCompact K := isCompact_Icc.image (B.closing i).continuous
    have hU : IsOpen U := E.isOpen_inter_preimage
      (isOpen_lt (by fun_prop) continuous_const)
    have hKU : K ⊆ U := by
      rintro x ⟨u,hu,rfl⟩
      have hu0 : 0<(u:ℝ) := hlo.trans_le hu.1
      have hu1 : (u:ℝ)<1 := (show (u:ℝ)≤(hi:ℝ) from hu.2).trans_lt hhi
      refine ⟨?_,?_⟩
      · rw [hEs]
        exact ⟨(u,⟨0,by norm_num⟩),⟨hu0,hu1,by norm_num,by norm_num⟩,F.closing_center u⟩
      · change |E (B.closing i u) 1|<ρ
        rw [← F.closing_center u,hcoord (u,⟨0,by norm_num⟩) hu0 hu1 (by norm_num) (by norm_num)]
        simpa using hρ
    obtain ⟨r,hr,hretain⟩ := hRetainTwo F.E F.square K U hK hU hKU
    refine ⟨E,hEs,hEt,hcoord,r,hr,?_⟩
    intro H v hv hfix hsource hfar hdisp t u hu
    exact hretain H v hv hfix hsource hfar hdisp t ⟨B.closing i u,⟨u,hu,rfl⟩,rfl⟩
  have hOldFirstCoordinateInterior
      (F : SourceFirstReturnFramedStrips D B i)
      (E : OpenPartialHomeomorph S Plane)
      (hEs : E.source=F.N '' {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧ -1<(z.2:ℝ) ∧ (z.2:ℝ)<1})
      (hcoord : ∀ z, 0<(z.1:ℝ) → (z.1:ℝ)<1 → -1<(z.2:ℝ) → (z.2:ℝ)<1 →
        E (F.N z)=Plane.mk z.1 z.2)
      (ρ : ℝ) (A : SourceFirstReturnAttachedCaps F)
      (hside : ∀ k (w : Set.Icc (-1:ℝ) 1), |(w:ℝ)|≤ρ →
        (F.N (F.θf k,w) ∈ A.d.image ↔ w=A.w))
      (f : C(Interval,S)) (hf : IsEmbedding f)
      (hf0 : f 0=F.N (F.θf false,A.w))
      (hf1 : f 1=F.N (F.θf true,A.w))
      (hcurve : Set.range f ⊆ A.d.image)
      (hstrip : ∀ t, f t ∈ E.source ∧ |E (f t) 1|<ρ) :
      ∀ t : Interval, 0<(t:ℝ) → (t:ℝ)<1 →
        (F.θf false:ℝ)<E (f t) 0 ∧ E (f t) 0<(F.θf true:ℝ) := by
    have hfullcoord (q : Interval × Set.Icc (-1:ℝ) 1)
        (hq : F.N q ∈ E.source) : E (F.N q)=Plane.mk q.1 q.2 := by
      rw [hEs] at hq
      obtain ⟨p,hp,he⟩ := hq
      have hpq := F.first_embedding.injective he
      subst p
      exact hcoord q hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    let z : C(Interval,ℝ) := ⟨fun t=>E (f t) 0,by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (show Continuous (fun p : Plane=>p 0) by fun_prop).continuousAt.comp
        ((E.continuousAt (hstrip t).1).comp f.continuous.continuousAt)⟩
    have hz0 : z 0=(F.θf false:ℝ) := by
      change E (f 0) 0=_
      rw [hf0,hfullcoord (F.θf false,A.w) (hf0 ▸ (hstrip 0).1)]
      rfl
    have hz1 : z 1=(F.θf true:ℝ) := by
      change E (f 1) 0=_
      rw [hf1,hfullcoord (F.θf true,A.w) (hf1 ▸ (hstrip 1).1)]
      rfl
    have hport (t : Interval) (k : Bool) (ht : z t=(F.θf k:ℝ)) :
        t=(if k then 1 else 0) := by
      have hs := (hstrip t).1
      rw [hEs] at hs
      obtain ⟨⟨u,w⟩,hu,he⟩ := hs
      have hcoords : E (f t)=Plane.mk u w := by
        rw [← he]
        exact hcoord (u,w) hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
      have hutheta : u=F.θf k := by
        apply Subtype.ext
        have hc := congrArg (fun q : Plane=>q 0) hcoords
        change E (f t) 0=(u:ℝ) at hc
        exact hc.symm.trans ht
      have hw : |(w:ℝ)|≤ρ := by
        have hc := congrArg (fun q : Plane=>q 1) hcoords
        change E (f t) 1=(w:ℝ) at hc
        exact (hc ▸ (hstrip t).2).le
      have hwa : w=A.w := (hside k w hw).mp (by
        rw [← hutheta,he]
        exact hcurve (Set.mem_range_self t))
      have hpoint : f t=F.N (F.θf k,A.w) := by rw [← he,hutheta,hwa]
      cases k
      · exact hf.injective (hpoint.trans hf0.symm)
      · exact hf.injective (hpoint.trans hf1.symm)
    exact hParameterBetweenPorts z (F.θf false) (F.θf true) F.first_ports_order hz0 hz1
      (fun t hh=>by
        rcases hh with hh|hh
        · exact Or.inl (hport t false hh)
        · exact Or.inr (hport t true hh))
  have hOldClosingCoordinateInterior
      (F : SourceFirstReturnFramedStrips D B i)
      (E : OpenPartialHomeomorph S Plane)
      (hEs : E.source=F.M '' {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧ -1<(z.2:ℝ) ∧ (z.2:ℝ)<1})
      (hcoord : ∀ z, 0<(z.1:ℝ) → (z.1:ℝ)<1 → -1<(z.2:ℝ) → (z.2:ℝ)<1 →
        E (F.M z)=Plane.mk z.1 z.2)
      (ρ : ℝ) (A : SourceFirstReturnAttachedCaps F)
      (hside : ∀ k (w : Set.Icc (-1:ℝ) 1), |(w:ℝ)|≤ρ →
        (F.M (F.θg k,w) ∈ A.d.image ↔ w=A.z))
      (f : C(Interval,S)) (hf : IsEmbedding f)
      (hf0 : f 0=F.M (F.θg false,A.z))
      (hf1 : f 1=F.M (F.θg true,A.z))
      (hcurve : Set.range f ⊆ A.d.image)
      (hstrip : ∀ t, f t ∈ E.source ∧ |E (f t) 1|<ρ) :
      ∀ t : Interval, 0<(t:ℝ) → (t:ℝ)<1 →
        (F.θg false:ℝ)<E (f t) 0 ∧ E (f t) 0<(F.θg true:ℝ) := by
    have hfullcoord (q : Interval × Set.Icc (-1:ℝ) 1)
        (hq : F.M q ∈ E.source) : E (F.M q)=Plane.mk q.1 q.2 := by
      rw [hEs] at hq
      obtain ⟨p,hp,he⟩ := hq
      have hpq := F.closing_embedding.injective he
      subst p
      exact hcoord q hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    let z : C(Interval,ℝ) := ⟨fun t=>E (f t) 0,by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (show Continuous (fun p : Plane=>p 0) by fun_prop).continuousAt.comp
        ((E.continuousAt (hstrip t).1).comp f.continuous.continuousAt)⟩
    have hz0 : z 0=(F.θg false:ℝ) := by
      change E (f 0) 0=_
      rw [hf0,hfullcoord (F.θg false,A.z) (hf0 ▸ (hstrip 0).1)]
      rfl
    have hz1 : z 1=(F.θg true:ℝ) := by
      change E (f 1) 0=_
      rw [hf1,hfullcoord (F.θg true,A.z) (hf1 ▸ (hstrip 1).1)]
      rfl
    have hport (t : Interval) (k : Bool) (ht : z t=(F.θg k:ℝ)) :
        t=(if k then 1 else 0) := by
      have hs := (hstrip t).1
      rw [hEs] at hs
      obtain ⟨⟨u,w⟩,hu,he⟩ := hs
      have hcoords : E (f t)=Plane.mk u w := by
        rw [← he]
        exact hcoord (u,w) hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
      have hutheta : u=F.θg k := by
        apply Subtype.ext
        have hc := congrArg (fun q : Plane=>q 0) hcoords
        change E (f t) 0=(u:ℝ) at hc
        exact hc.symm.trans ht
      have hw : |(w:ℝ)|≤ρ := by
        have hc := congrArg (fun q : Plane=>q 1) hcoords
        change E (f t) 1=(w:ℝ) at hc
        exact (hc ▸ (hstrip t).2).le
      have hwa : w=A.z := (hside k w hw).mp (by
        rw [← hutheta,he]
        exact hcurve (Set.mem_range_self t))
      have hpoint : f t=F.M (F.θg k,A.z) := by rw [← he,hutheta,hwa]
      cases k
      · exact hf.injective (hpoint.trans hf0.symm)
      · exact hf.injective (hpoint.trans hf1.symm)
    exact hParameterBetweenPorts z (F.θg false) (F.θg true) F.closing_ports_order hz0 hz1
      (fun t hh=>by
        rcases hh with hh|hh
        · exact Or.inl (hport t false hh)
        · exact Or.inr (hport t true hh))
  have hIntervalPlaneArc (p : C(Interval,Plane)) (hpInjective : Function.Injective p) :
      IsArcBetween (Set.range p) (p 0) (p 1) := by
    let q : ℝ → Plane := fun t=>p (projIcc 0 1 zero_le_one t)
    have hqContinuous : Continuous q := by dsimp [q]; fun_prop
    have hqInjective : Set.InjOn q (Set.Icc (0:ℝ) 1) := by
      intro t ht u hu he
      have htu := hpInjective he
      have htproj : (projIcc 0 1 zero_le_one t:ℝ)=t := by
        rw [projIcc_of_mem zero_le_one ht]
      have huproj : (projIcc 0 1 zero_le_one u:ℝ)=u := by
        rw [projIcc_of_mem zero_le_one hu]
      exact htproj.symm.trans ((congrArg Subtype.val htu).trans huproj)
    have hqRange : q '' (Set.Icc (0:ℝ) 1)=Set.range p := by
      ext x
      constructor
      · rintro ⟨t,_ht,rfl⟩
        exact Set.mem_range_self _
      · rintro ⟨t,rfl⟩
        exact ⟨(t:ℝ),t.property,by dsimp [q]; rw [projIcc_of_mem zero_le_one t.property]⟩
    refine ⟨q,hqContinuous.continuousOn,hqInjective,hqRange,?_,?_⟩
    · dsimp [q]
      rw [projIcc_of_mem zero_le_one (by norm_num)]
      rfl
    · dsimp [q]
      rw [projIcc_of_mem zero_le_one (by norm_num)]
      rfl

  have hRepairThinSquare
      (E : OpenPartialHomeomorph S Plane)
      (hEt : E.target={z : Plane | 0<z 0 ∧ z 0<1 ∧ -1<z 1 ∧ z 1<1})
      (α β : ℝ) (hα : 0<α) (hαβ : α<β) (hβ : β<1)
      (ρ : ℝ) (hρ : 0<ρ) (hρlt : ρ<1) :
      ∃ R : OpenPartialHomeomorph S Plane,
        R.source=E.source ∧ Plane.closedSquare 0 1 ⊆ R.target ∧
        (∀ x, R x 0=(2*E x 0-α-β)/(β-α) ∧ R x 1=E x 1/ρ) ∧
        (∀ x, R x 1=0 ↔ E x 1=0) := by
    let L : Plane ≃ₜ Plane := {
      toEquiv := {
        toFun := fun z => Plane.mk ((2*z 0-α-β)/(β-α)) (z 1/ρ)
        invFun := fun z => Plane.mk ((α+β+(β-α)*z 0)/2) (ρ*z 1)
        left_inv := by
          intro z
          ext j
          fin_cases j
          · change (α+β+(β-α)*((2*z 0-α-β)/(β-α)))/2 = z 0
            field_simp [sub_ne_zero.mpr hαβ.ne']
            ring
          · change ρ*(z 1/ρ) = z 1
            field_simp [hρ.ne']
        right_inv := by
          intro z
          ext j
          fin_cases j
          · change (2*((α+β+(β-α)*z 0)/2)-α-β)/(β-α) = z 0
            field_simp [sub_ne_zero.mpr hαβ.ne']
            ring
          · change ρ*z 1/ρ = z 1
            field_simp [hρ.ne'] }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let F := E.trans L.toOpenPartialHomeomorph
    refine ⟨F,by simp [F],?_,fun _ => ⟨rfl,rfl⟩,?_⟩
    · intro z hz
      have hnorm : Plane.supNorm z ≤ 1 := by
        simpa [Plane.closedSquare,Plane.supDist] using hz
      have h0 := abs_le.mp ((Plane.abs_zero_le_supNorm z).trans hnorm)
      have h1 := abs_le.mp ((Plane.abs_one_le_supNorm z).trans hnorm)
      have hzin : L.symm z ∈ E.target := by
        rw [hEt]
        change 0 < (α+β+(β-α)*z 0)/2 ∧ (α+β+(β-α)*z 0)/2 < 1 ∧
          -1 < ρ*z 1 ∧ ρ*z 1 < 1
        refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [h0.1,h0.2,h1.1,h1.2]
      exact ⟨Set.mem_univ _,hzin⟩
    · intro x
      change E x 1/ρ = 0 ↔ E x 1 = 0
      simp [hρ.ne']

  have hAmbientRelTrans (X Y Z : Set S)
      (hXY : AmbientIsotopy.Rel X Y) (hYZ : AmbientIsotopy.Rel Y Z) :
      AmbientIsotopy.Rel X Z := by
    obtain ⟨H,hH⟩ := hXY
    obtain ⟨G,hG⟩ := hYZ
    let K : AmbientIsotopy S := {
      map:=⟨fun z=>G.map (z.1,H.map z),
        G.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩,
      homeomorphism_at:=by
        intro t
        obtain ⟨e,he⟩ := H.homeomorphism_at t
        obtain ⟨f,hf⟩ := G.homeomorphism_at t
        exact ⟨e.trans f,fun x=>(hf (e x)).trans (congrArg (fun z=>G.map (t,z)) (he x))⟩,
      at_zero:=by
        intro x
        change G.map (⟨0,by norm_num⟩,H.map (⟨0,by norm_num⟩,x))=x
        rw [H.at_zero,G.at_zero] }
    refine ⟨K,?_⟩
    change (fun x=>G.finalMap (H.finalMap x)) '' X=Z
    rw [← Set.image_image,hH,hG]
  have hClosingBandAvoidsWholeFirst
      (P : SourceFirstReturnBudgetTracks D B i)
      (hBands : Disjoint
        (P.F.N '' (Set.Icc (P.F.θf false) (P.F.θf true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))))
        (P.F.M '' (Set.Icc (P.F.θg false) (P.F.θg true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))))) :
      ∃ Q : SourceFirstReturnBudgetTracks D B i,
        Disjoint
          (Q.F.N '' (Set.Icc (Q.F.θf false) (Q.F.θf true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))))
          (Q.F.M '' (Set.Icc (Q.F.θg false) (Q.F.θg true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1)))) ∧
        ∀ u ∈ Set.Icc (Q.F.θg false) (Q.F.θg true), ∀ w : Set.Icc (-1:ℝ) 1,
          Q.F.M (u,w) ∉ Set.range D.first := by
    let T := Set.range D.first
    have hT : IsCompact T := isCompact_range D.first.continuous
    have hcenter (u : Interval) (hu : u ∈ Set.Icc (P.F.θg false) (P.F.θg true)) :
        P.F.M (u,⟨0,by norm_num⟩) ∉ T := by
      rw [P.F.closing_center]
      have hu0 : 0<(u:ℝ) := (P.F.θg_internal false).1.trans_le hu.1
      have hu1 : (u:ℝ)<1 :=
        (show (u:ℝ)≤(P.F.θg true:ℝ) from hu.2).trans_lt (P.F.θg_internal true).2
      rintro ⟨t,he⟩
      by_cases ht0 : t=0
      · have hcu : B.closing i u=B.closing i 0 := by
          rw [B.closing_zero]
          simpa only [ht0,D.first_zero] using he.symm
        have hue := congrArg Subtype.val ((B.closing_embedded i).injective hcu)
        exact hu0.ne' hue
      · by_cases ht1 : t=1
        · have hcu : B.closing i u=B.closing i 1 := by
            rw [B.closing_one]
            simpa only [ht1,D.first_one] using he.symm
          have hue := congrArg Subtype.val ((B.closing_embedded i).injective hcu)
          exact hu1.ne hue
        · apply D.first_interior_avoids t ht0 ht1
          rw [he,← B.closing_cover]
          cases i
          · exact Or.inl (Set.mem_range_self u)
          · exact Or.inr (Set.mem_range_self u)
    obtain ⟨τ,hτ,M,hM,hformula,hMc,hMT⟩ :=
      source_strip_finite_parameter_localization P.F.M P.F.closing_embedding Unit
        (fun _=>Set.Icc (P.F.θg false) (P.F.θg true)) (fun _=>isClosed_Icc)
        (fun _=>Tᶜ) (fun _=>hT.isClosed.isOpen_compl) (fun _=>hcenter)
    let G : SourceFirstReturnFramedStrips D B i := {
      (P.F) with
      M:=M,closing_embedding:=hM,
      closing_center:=(fun u=>(hMc u).trans (P.F.closing_center u)),
      β:=fun k=>P.F.β k*τ,γ:=fun p=>P.F.γ p*τ,
      corner_positive:=fun k=>⟨(P.F.corner_positive k).1,
        mul_ne_zero (P.F.corner_positive k).2.1 hτ.1.ne',(P.F.corner_positive k).2.2⟩,
      retained_positive:=fun p=>⟨mul_ne_zero (P.F.retained_positive p).1 hτ.1.ne',(P.F.retained_positive p).2⟩,
      closing_framing:=by
        intro k u w hu
        let w' : Set.Icc (-1:ℝ) 1 := ⟨τ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hτ.1,hτ.2]⟩
        have he : M (u,w)=P.F.M (u,w') := hformula (u,w)
        obtain ⟨hs,hcoords⟩ := P.F.closing_framing k u w' hu
        refine ⟨he ▸ hs,?_⟩
        rw [he,hcoords]
        ext j
        fin_cases j
        · rfl
        · change P.F.β k*(τ*(w:ℝ))=P.F.β k*τ*(w:ℝ); ring,
      retained_framing:=by
        intro p u w hu
        let w' : Set.Icc (-1:ℝ) 1 := ⟨τ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hτ.1,hτ.2]⟩
        have he : M (u,w)=P.F.M (u,w') := hformula (u,w)
        obtain ⟨hs,hcoords⟩ := P.F.retained_framing p u w' hu
        refine ⟨he ▸ hs,?_⟩
        rw [he,hcoords]
        ext j
        fin_cases j
        · rfl
        · change P.F.γ p*(τ*(w:ℝ))=P.F.γ p*τ*(w:ℝ); ring
    }
    have hbudget : ∀ u ∈ Set.Icc (G.θg false) (G.θg true), ∀ w : Set.Icc (-1:ℝ) 1,
        (G.M (u,w) ∈ b.image ↔ (w:ℝ)=0) ∧
        (G.M (u,w) ∈ a.image → ∃ p : source_surgery_retained_crossings B i, u=G.θR p) := by
      intro u hu w
      let w' : Set.Icc (-1:ℝ) 1 := ⟨τ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hτ.1,hτ.2]⟩
      have he : G.M (u,w)=P.F.M (u,w') := hformula (u,w)
      rw [he]
      obtain ⟨hb,ha⟩ := P.closing_middle u hu w'
      refine ⟨hb.trans ?_,ha⟩
      change τ*(w:ℝ)=0 ↔ (w:ℝ)=0
      exact mul_eq_zero_iff_left hτ.1.ne'
    obtain ⟨A⟩ := source_framed_first_return_caps_on_whole_curve S D B ht i G
    let Q : SourceFirstReturnBudgetTracks D B i := {
      F:=G,caps:=A,first_middle:=P.first_middle,closing_middle:=hbudget }
    have hMsub : M '' (Set.Icc (G.θg false) (G.θg true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))) ⊆
        P.F.M '' (Set.Icc (P.F.θg false) (P.F.θg true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))) := by
      rintro x ⟨⟨u,w⟩,hu,rfl⟩
      exact ⟨(u,⟨τ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hτ.1,hτ.2]⟩),
        ⟨hu.1,Set.mem_univ _⟩,(hformula (u,w)).symm⟩
    exact ⟨Q,hBands.mono (Set.Subset.refl _) hMsub,fun u hu w=>hMT () (u,w) hu⟩

  have hOldMiddleDecomposition := source_framed_first_return_old_middle_decomposition S D B i
  obtain ⟨P₀,hBands₀,_hGlobalFirst,_hGlobalClosing⟩ := source_first_return_global_port_incidence S D B ht i
  obtain ⟨P,hBands,hMWholeFirst⟩ := hClosingBandAvoidsWholeFirst P₀ hBands₀
  let F := P.F
  let δ : ℝ := min ((F.θf false:ℝ)/2) ((1-(F.θf true:ℝ))/2)
  have hδ : 0<δ := lt_min (half_pos (F.θf_internal false).1)
    (half_pos (sub_pos.mpr (F.θf_internal true).2))
  let δg : ℝ := min ((F.θg false:ℝ)/2) ((1-(F.θg true:ℝ))/2)
  have hδg : 0<δg := lt_min (half_pos (F.θg_internal false).1)
    (half_pos (sub_pos.mpr (F.θg_internal true).2))
  let G : SourceFirstReturnFramedStrips D B i := {
    F with
    ηf:=fun k=>min (F.ηf k) δ,ηg:=fun k=>min (F.ηg k) δg,
    corner_positive:=fun k=>⟨(F.corner_positive k).1,(F.corner_positive k).2.1,
      lt_min (F.corner_positive k).2.2.1 hδ,lt_min (F.corner_positive k).2.2.2 hδg⟩,
    first_framing:=fun k u w hu=>F.first_framing k u w (hu.trans_le (min_le_left _ _)),
    closing_framing:=fun k u w hu=>F.closing_framing k u w (hu.trans_le (min_le_left _ _)) }
  obtain ⟨ρ,rs,hρ,hρlt,hrs,hSide⟩ := hActualFirstVerticalSides G
  let lo : Interval := ⟨(F.θf false:ℝ)/2,by constructor <;> linarith [(F.θf_internal false).1,(F.θf_internal false).2]⟩
  let hi : Interval := ⟨(1+(F.θf true:ℝ))/2,by constructor <;> linarith [(F.θf_internal true).1,(F.θf_internal true).2]⟩
  have hlo : 0<(lo:ℝ) := half_pos (F.θf_internal false).1
  have hhi : (hi:ℝ)<1 := by dsimp [hi]; linarith [(F.θf_internal true).2]
  obtain ⟨E,hEs,hEt,hcoord,rr,hrr,hretain⟩ := hFirstCoreCompactRetention G lo hi hlo hhi ρ hρ
  obtain ⟨ρg,rsg,hρg,hρglt,hrsg,hSideClosing⟩ := hActualClosingVerticalSides G
  let log : Interval := ⟨(F.θg false:ℝ)/2,by constructor <;> linarith [(F.θg_internal false).1,(F.θg_internal false).2]⟩
  let hig : Interval := ⟨(1+(F.θg true:ℝ))/2,by constructor <;> linarith [(F.θg_internal true).1,(F.θg_internal true).2]⟩
  have hlog : 0<(log:ℝ) := half_pos (F.θg_internal false).1
  have hhig : (hig:ℝ)<1 := by dsimp [hig];linarith [(F.θg_internal true).2]
  obtain ⟨Eg,hEgs,hEgt,hgcoord,rrg,hrrg,hgretain⟩ := hClosingCoreCompactRetention G log hig hlog hhig ρg hρg
  obtain ⟨ro,hro,hOld⟩ := hOldMiddleDecomposition G
  let W : Bool → Set.Icc (-1:ℝ) 1 := fun k=>if k then
    ⟨ρ,by constructor <;> linarith⟩ else ⟨-ρ,by constructor <;> linarith⟩
  let X := G.N '' (Set.Icc (G.θf false) (G.θf true) ×ˢ Set.range W)
  have hX : IsCompact X := (isCompact_Icc.prod (Set.finite_range W).isCompact).image G.first_embedding.continuous
  have hRawAvoidX : (B.boundary i).image ⊆ Xᶜ := by
    intro x hx hxX
    obtain ⟨⟨u,w⟩,⟨hu,⟨k,hkw⟩⟩,he⟩ := hxX
    change W k=w at hkw
    have hw : (w:ℝ)≠0 := by
      rw [← hkw]
      cases k
      · exact neg_ne_zero.mpr hρ.ne'
      · exact hρ.ne'
    rw [B.boundary_image] at hx
    rcases hx with hx|hx
    · obtain ⟨t,ht⟩ := hx
      have hc : G.N (u,w)=G.N (t,⟨0,by norm_num⟩) := by
        rw [G.first_center]
        exact he.trans ht.symm
      have hp := G.first_embedding.injective hc
      exact hw (congrArg (fun q : Interval × Set.Icc (-1:ℝ) 1=>(q.2:ℝ)) hp)
    · have hb : x ∈ b.image := by
        rw [← B.closing_cover]
        cases i
        · exact Or.inl hx
        · exact Or.inr hx
      exact (P.first_middle u hu w).1 (he ▸ hb)
  let Wg : Bool → Set.Icc (-1:ℝ) 1 := fun k=>if k then
    ⟨ρg,by constructor <;> linarith⟩ else ⟨-ρg,by constructor <;> linarith⟩
  let Y := G.M '' (Set.Icc (G.θg false) (G.θg true) ×ˢ Set.range Wg)
  have hY : IsCompact Y := (isCompact_Icc.prod (Set.finite_range Wg).isCompact).image G.closing_embedding.continuous
  have hRawAvoidY : (B.boundary i).image ⊆ Yᶜ := by
    intro x hx hxY
    obtain ⟨⟨u,w⟩,⟨hu,⟨k,hkw⟩⟩,he⟩ := hxY
    change Wg k=w at hkw
    have hw : (w:ℝ)≠0 := by
      rw [← hkw]
      cases k
      · exact neg_ne_zero.mpr hρg.ne'
      · exact hρg.ne'
    rw [B.boundary_image] at hx
    rcases hx with hx|hx
    · exact hMWholeFirst u hu w (he ▸ hx)
    · obtain ⟨t,ht⟩ := hx
      have hc : G.M (u,w)=G.M (t,⟨0,by norm_num⟩) := by
        rw [G.closing_center]
        exact he.trans ht.symm
      have hp := G.closing_embedding.injective hc
      exact hw (congrArg (fun q : Interval × Set.Icc (-1:ℝ) 1=>(q.2:ℝ)) hp)
  let Z := X ∪ Y
  have hZ : IsCompact Z := hX.union hY
  have hRawAvoidZ : (B.boundary i).image ⊆ Zᶜ := by
    intro x hx
    exact fun hh=>hh.elim (hRawAvoidX hx) (hRawAvoidY hx)
  obtain ⟨rh,hrh,hHorizontalRetain⟩ := hRetainTwo G.E G.square (B.boundary i).image Zᶜ
    (isCompact_range (B.boundary i).embedded.continuous) hZ.isClosed.isOpen_compl hRawAvoidZ
  let r : ℝ := min ro (min rs (min rr (min rh (min rsg rrg))))
  have hr : 0<r := lt_min hro (lt_min hrs (lt_min hrr (lt_min hrh (lt_min hrsg hrrg))))
  obtain ⟨A,hv,hfar,hdisp⟩ := hCapsBound G r hr
  have hvOld (k) : ‖A.v k‖<ro := (hv k).trans_le (min_le_left _ _)
  have hvSide (k) : ‖A.v k‖<rs := (hv k).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hvRetain (k) : ‖A.v k‖<rr := (hv k).trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hvHorizontal (k) : ‖A.v k‖<rh := (hv k).trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hvSideClosing (k) : ‖A.v k‖<rsg := (hv k).trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hvRetainClosing (k) : ‖A.v k‖<rrg := (hv k).trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hAdAvoidZ : Disjoint A.d.image Z := Set.disjoint_left.mpr (by
    intro x hx hxX
    rw [A.image] at hx
    exact hHorizontalRetain A.H A.v hvHorizontal A.fixed A.source_preserved hfar hdisp 1 hx hxX)
  have hAdAvoidX : Disjoint A.d.image X := hAdAvoidZ.mono_right Set.subset_union_left
  have hAdAvoidY : Disjoint A.d.image Y := hAdAvoidZ.mono_right Set.subset_union_right
  obtain ⟨uf,ug,hufug,huf,hug,f,g,hf,hg,hf0,hf1,hg0,hg1,hfR,hgR,hWhole,hfg⟩ := hOld A hvOld
  have huflo : lo≤uf false := by
    have habs := (abs_lt.mp (huf false).2.2.1).1
    have hsmall : G.ηf false≤(F.θf false:ℝ)/2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    change -(G.ηf false)<(uf false:ℝ)-(F.θf false:ℝ) at habs
    change (F.θf false:ℝ)/2≤(uf false:ℝ)
    linarith
  have hufhi : uf true≤hi := by
    have habs := (abs_lt.mp (huf true).2.2.1).2
    have hsmall : G.ηf true≤(1-(F.θf true:ℝ))/2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    change (uf true:ℝ)-(F.θf true:ℝ)<G.ηf true at habs
    change (uf true:ℝ)≤(1+(F.θf true:ℝ))/2
    linarith
  have hFstrip (t : Interval) : f t ∈ E.source ∧ |E (f t) 1|<ρ := by
    have hx := hfR ▸ Set.mem_range_self t
    obtain ⟨x,⟨u,hu,rfl⟩,he⟩ := hx
    have huk : u ∈ Set.Icc lo hi := ⟨huflo.trans hu.1,hu.2.trans hufhi⟩
    have hh := hretain A.H A.v hvRetain A.fixed A.source_preserved hfar hdisp 1 u huk
    have he' : A.H.map (1,D.first u)=f t := he
    exact he' ▸ hh
  have hFcurve : Set.range f ⊆ A.d.image := by
    intro x hx
    rw [hWhole]
    exact Or.inl (Or.inl (Or.inl hx))
  have hFproper := hOldFirstCoordinateInterior G E hEs hcoord ρ A (hSide A hvSide)
    f hf hf0 hf1 hFcurve hFstrip
  have huglo : log≤ug false := by
    have habs := (abs_lt.mp (hug false).2.2.1).1
    have hsmall : G.ηg false≤(F.θg false:ℝ)/2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    change -(G.ηg false)<(ug false:ℝ)-(F.θg false:ℝ) at habs
    change (F.θg false:ℝ)/2≤(ug false:ℝ)
    linarith
  have hughi : ug true≤hig := by
    have habs := (abs_lt.mp (hug true).2.2.1).2
    have hsmall : G.ηg true≤(1-(F.θg true:ℝ))/2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    change (ug true:ℝ)-(F.θg true:ℝ)<G.ηg true at habs
    change (ug true:ℝ)≤(1+(F.θg true:ℝ))/2
    linarith
  have hGstrip (t : Interval) : g t ∈ Eg.source ∧ |Eg (g t) 1|<ρg := by
    have hx := hgR ▸ Set.mem_range_self t
    obtain ⟨x,⟨u,hu,rfl⟩,he⟩ := hx
    have huk : u ∈ Set.Icc log hig := ⟨huglo.trans hu.1,hu.2.trans hughi⟩
    have hh := hgretain A.H A.v hvRetainClosing A.fixed A.source_preserved hfar hdisp 1 u huk
    have he' : A.H.map (1,B.closing i u)=g t := he
    exact he' ▸ hh
  have hGcurveEarly : Set.range g ⊆ A.d.image := by
    intro x hx
    rw [hWhole]
    exact Or.inl (Or.inl (Or.inr hx))
  have hGproper := hOldClosingCoordinateInterior G Eg hEgs hgcoord ρg A (hSideClosing A hvSideClosing)
    g hg hg0 hg1 hGcurveEarly hGstrip
  obtain ⟨R,hRs,hRtarget,hRcoord,_hRaxis⟩ := hRepairThinSquare E hEt
    (G.θf false) (G.θf true) (G.θf_internal false).1 G.first_ports_order (G.θf_internal true).2 ρ hρ hρlt
  let p : C(Interval,Plane) := ⟨fun t=>R (f t),by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (R.continuousAt (hRs.symm ▸ (hFstrip t).1)).comp f.continuous.continuousAt⟩
  have hpInjective : Function.Injective p := by
    intro t u he
    apply hf.injective
    exact R.injOn (hRs.symm ▸ (hFstrip t).1) (hRs.symm ▸ (hFstrip u).1) he
  have hpArc := hIntervalPlaneArc p hpInjective
  have hpProper : Set.range p \ {p 0,p 1} ⊆ Plane.openSquare 0 1 := by
    rintro x ⟨⟨t,rfl⟩,hx⟩
    have ht0 : t≠0 := by intro he; exact hx (by rw [he]; simp)
    have ht1 : t≠1 := by intro he; exact hx (by rw [he]; simp)
    have ht0r : 0<(t:ℝ) := lt_of_le_of_ne t.property.1 (by exact fun he=>ht0 (Subtype.ext he.symm))
    have ht1r : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (by exact fun he=>ht1 (Subtype.ext he))
    have hlong := hFproper t ht0r ht1r
    have hnormal := (hFstrip t).2
    have hgap : 0<(G.θf true:ℝ)-(G.θf false:ℝ) := sub_pos.mpr G.first_ports_order
    have hlongR : |R (f t) 0|<1 := by
      rw [(hRcoord (f t)).1,abs_lt]
      constructor
      · apply (lt_div_iff₀ hgap).mpr
        linarith [hlong.1]
      · apply (div_lt_iff₀ hgap).mpr
        linarith [hlong.2]
    have hnormalR : |R (f t) 1|<1 := by
      rw [(hRcoord (f t)).2,abs_div,abs_of_pos hρ]
      exact (div_lt_one hρ).mpr hnormal
    change p t ∈ Plane.openSquare 0 1
    exact mem_openSquare_zero_one.mpr (max_lt hlongR hnormalR)
  let Q : Set S := {x | x ∈ R.source ∧ R x ∈ Plane.closedSquare 0 1}
  let V : Set S := {x | x ∈ R.source ∧ R x ∈ Plane.openSquare 0 1}
  have hgap : 0<(G.θf true:ℝ)-(G.θf false:ℝ) := sub_pos.mpr G.first_ports_order
  have hQData (x : S) (hx : x ∈ Q) :
      ∃ u : Interval, ∃ w : Set.Icc (-1:ℝ) 1,
        u ∈ Set.Icc (G.θf false) (G.θf true) ∧ |(w:ℝ)|≤ρ ∧
        G.N (u,w)=x ∧
        R x 0=(2*(u:ℝ)-(G.θf false:ℝ)-(G.θf true:ℝ))/((G.θf true:ℝ)-(G.θf false:ℝ)) ∧
        R x 1=(w:ℝ)/ρ := by
    have hs : x ∈ E.source := hRs ▸ hx.1
    rw [hEs] at hs
    obtain ⟨⟨u,w⟩,hu,he⟩ := hs
    have hEcoords : E x=Plane.mk u w := by
      rw [← he]
      exact hcoord (u,w) hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
    have hR0 := (hRcoord x).1
    have hR1 := (hRcoord x).2
    rw [hEcoords] at hR0 hR1
    change R x 0=(2*(u:ℝ)-(G.θf false:ℝ)-(G.θf true:ℝ))/((G.θf true:ℝ)-(G.θf false:ℝ)) at hR0
    change R x 1=(w:ℝ)/ρ at hR1
    have hnorm := mem_closedSquare_zero_one.mp hx.2
    have hlong := abs_le.mp ((Plane.abs_zero_le_supNorm (R x)).trans hnorm)
    have hnormal := (Plane.abs_one_le_supNorm (R x)).trans hnorm
    have hul : (G.θf false:ℝ)≤u := by
      rw [hR0] at hlong
      have hh := (le_div_iff₀ hgap).mp hlong.1
      linarith
    have hur : (u:ℝ)≤G.θf true := by
      rw [hR0] at hlong
      have hh := (div_le_iff₀ hgap).mp hlong.2
      linarith
    have hw : |(w:ℝ)|≤ρ := by
      rw [hR1,abs_div,abs_of_pos hρ] at hnormal
      exact (div_le_one hρ).mp hnormal
    exact ⟨u,w,⟨hul,hur⟩,hw,he,hR0,hR1⟩
  have hCurveBoundary (x : S) (hxQ : x ∈ Q) (hxV : x ∉ V) (hxd : x ∈ A.d.image) :
      x=f 0 ∨ x=f 1 := by
    obtain ⟨u,w,hu,hw,he,hR0,hR1⟩ := hQData x hxQ
    have hnorm := mem_closedSquare_zero_one.mp hxQ.2
    have hno : ¬ Plane.supNorm (R x)<1 := by
      intro hn
      exact hxV ⟨hxQ.1,mem_openSquare_zero_one.mpr hn⟩
    have hlongle := (Plane.abs_zero_le_supNorm (R x)).trans hnorm
    have hnormalle := (Plane.abs_one_le_supNorm (R x)).trans hnorm
    have hlongOrNormal : |R x 0|=1 ∨ |R x 1|=1 := by
      by_cases hl : |R x 0|<1
      · right
        apply le_antisymm hnormalle
        by_contra hn
        exact hno (max_lt hl (lt_of_not_ge hn))
      · exact Or.inl (le_antisymm hlongle (le_of_not_gt hl))
    rcases hlongOrNormal with hl|hn
    · have hlsign : R x 0=1 ∨ R x 0=-1 := by
        by_cases hp : 0≤R x 0
        · exact Or.inl (by rwa [abs_of_nonneg hp] at hl)
        · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge hp)] at hl; linarith)
      have huend : u=G.θf false ∨ u=G.θf true := by
        rcases hlsign with hright|hleft
        · right
          apply Subtype.ext
          have hh := (div_eq_iff hgap.ne').mp (hR0.symm.trans hright)
          linarith
        · left
          apply Subtype.ext
          have hh := (div_eq_iff hgap.ne').mp (hR0.symm.trans hleft)
          linarith
      rcases huend with hue|hue
      · have hwa : w=A.w := (hSide A hvSide false w hw).mp (by rw [← hue,he];exact hxd)
        exact Or.inl (by rw [← he,hue,hwa,← hf0])
      · have hwa : w=A.w := (hSide A hvSide true w hw).mp (by rw [← hue,he];exact hxd)
        exact Or.inr (by rw [← he,hue,hwa,← hf1])
    · have hnsign : R x 1=1 ∨ R x 1=-1 := by
        by_cases hp : 0≤R x 1
        · exact Or.inl (by rwa [abs_of_nonneg hp] at hn)
        · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge hp)] at hn; linarith)
      have hwW : w ∈ Set.range W := by
        rcases hnsign with hplus|hminus
        · refine ⟨true,?_⟩
          apply Subtype.ext
          have hh := (div_eq_iff hρ.ne').mp (hR1.symm.trans hplus)
          change ρ=(w:ℝ)
          linarith
        · refine ⟨false,?_⟩
          apply Subtype.ext
          have hh := (div_eq_iff hρ.ne').mp (hR1.symm.trans hminus)
          change -ρ=(w:ℝ)
          linarith
      exact (Set.disjoint_left.mp hAdAvoidX hxd ⟨(u,w),⟨hu,hwW⟩,he⟩).elim
  have hQCompact : IsCompact Q := by
    have hQeq : Q=R.symm '' Plane.closedSquare 0 1 := by
      ext x
      constructor
      · intro hx
        exact ⟨R x,hx.2,R.left_inv hx.1⟩
      · rintro ⟨z,hz,rfl⟩
        exact ⟨R.map_target (hRtarget hz),by rw [R.right_inv (hRtarget hz)];exact hz⟩
    rw [hQeq]
    exact (isCompact_closedSquare 0 1).image_of_continuousOn (R.symm.continuousOn.mono hRtarget)
  have hVOpen : IsOpen V := R.isOpen_inter_preimage (Plane.isOpen_openSquare 0 1)
  have hVQ : V ⊆ Q := fun _ hx=>⟨hx.1,Plane.openSquare_subset_closedSquare 0 1 hx.2⟩
  have hQBand : Q ⊆ G.N '' (Set.Icc (G.θf false) (G.θf true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))) := by
    intro x hx
    obtain ⟨u,w,hu,_hw,he,_hc⟩ := hQData x hx
    exact ⟨(u,w),⟨hu,Set.mem_univ _⟩,he⟩
  have hClosingPortOutside (k : Bool) : G.M (G.θg k,A.z) ∉ Q := by
    intro hx
    have hfirst := hQBand hx
    have hclosing : G.M (G.θg k,A.z) ∈ G.M ''
        (Set.Icc (G.θg false) (G.θg true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))) := by
      refine ⟨(G.θg k,A.z),⟨?_,Set.mem_univ _⟩,rfl⟩
      cases k
      · exact ⟨le_rfl,G.closing_ports_order.le⟩
      · exact ⟨G.closing_ports_order.le,le_rfl⟩
    exact Set.disjoint_left.mp hBands hfirst hclosing
  have hGcurve : Set.range g ⊆ A.d.image := by
    intro x hx
    rw [hWhole]
    exact Or.inl (Or.inl (Or.inr hx))
  have hGpartition : Set.range g ⊆ V ∪ Qᶜ := by
    intro x hx
    by_cases hxQ : x ∈ Q
    · left
      by_contra hxV
      rcases hCurveBoundary x hxQ hxV (hGcurve hx) with he|he
      · exact Set.disjoint_left.mp hfg (he ▸ Set.mem_range_self 0) hx
      · exact Set.disjoint_left.mp hfg (he ▸ Set.mem_range_self 1) hx
    · exact Or.inr hxQ
  have hGoutside : Set.range g ⊆ Qᶜ := by
    have hgConnected : IsPreconnected (Set.range g) := by
      simpa only [Set.image_univ] using isPreconnected_univ.image g g.continuous.continuousOn
    rcases hgConnected.subset_or_subset hVOpen hQCompact.isClosed.isOpen_compl
      (Set.disjoint_left.mpr (fun _ hxV hxQ=>hxQ (hVQ hxV))) hGpartition with hin|hout
    · exact (hClosingPortOutside false (hg0 ▸ hVQ (hin (Set.mem_range_self 0)))).elim
    · exact hout
  have hCapNoFirstPort (k j : Bool) (t : Interval) (ht : (0:Interval)<t) :
      A.C k t≠G.N (G.θf j,A.w) := by
    intro he
    have hhe : A.C k t=A.C j 0 := he.trans (A.first_port j).symm
    by_cases hkj : k=j
    · subst j
      exact ht.ne' ((A.embedding k).injective hhe)
    · have hxk := Set.mem_range_self (f:=A.C k) t
      have hxj : A.C k t ∈ Set.range (A.C j) := ⟨0,hhe.symm⟩
      cases k <;> cases j
      · exact hkj rfl
      · exact Set.disjoint_left.mp A.caps_disjoint hxk hxj
      · exact Set.disjoint_left.mp A.caps_disjoint hxj hxk
      · exact hkj rfl
  have hCapsOutside (k : Bool) :
      (A.C k '' Set.Ioc (0:Interval) 1) ⊆ Qᶜ := by
    have hCapPartition : A.C k '' Set.Ioc (0:Interval) 1 ⊆ V ∪ Qᶜ := by
      rintro x ⟨t,ht,rfl⟩
      by_cases hxQ : A.C k t ∈ Q
      · left
        by_contra hxV
        rcases hCurveBoundary _ hxQ hxV (A.subset k (Set.mem_range_self t)).2 with he|he
        · exact hCapNoFirstPort k false t ht.1 (he.trans hf0)
        · exact hCapNoFirstPort k true t ht.1 (he.trans hf1)
      · exact Or.inr hxQ
    have hCapConnected : IsPreconnected (A.C k '' Set.Ioc (0:Interval) 1) :=
      isPreconnected_Ioc.image (A.C k) (A.C k).continuous.continuousOn
    rcases hCapConnected.subset_or_subset hVOpen hQCompact.isClosed.isOpen_compl
      (Set.disjoint_left.mpr (fun _ hxV hxQ=>hxQ (hVQ hxV))) hCapPartition with hin|hout
    · have hend : A.C k 1 ∈ A.C k '' Set.Ioc (0:Interval) 1 := ⟨1,⟨by norm_num,le_rfl⟩,rfl⟩
      exact (hClosingPortOutside k ((A.closing_port k) ▸ hVQ (hin hend))).elim
    · exact hout
  have hFirstInQ : Set.range f ⊆ Q := by
    rintro x ⟨t,rfl⟩
    refine ⟨hRs.symm ▸ (hFstrip t).1,?_⟩
    by_cases ht0 : t=0
    · rw [ht0]
      have hnorm : |R (f 0) 1|<1 := by
        rw [(hRcoord (f 0)).2,abs_div,abs_of_pos hρ]
        exact (div_lt_one hρ).mpr (hFstrip 0).2
      have hlong : R (f 0) 0=-1 := by
        have hs := (hFstrip 0).1
        rw [hf0,hEs] at hs
        obtain ⟨z,hz,he⟩ := hs
        have heq := G.first_embedding.injective he
        subst z
        have hE := hcoord (G.θf false,A.w) hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
        rw [hf0,(hRcoord _).1,hE]
        change (2*(G.θf false:ℝ)-(G.θf false:ℝ)-(G.θf true:ℝ))/((G.θf true:ℝ)-(G.θf false:ℝ))=-1
        apply (div_eq_iff hgap.ne').mpr
        ring
      exact mem_closedSquare_zero_one.mpr (by rw [Plane.supNorm,hlong];norm_num;exact hnorm.le)
    · by_cases ht1 : t=1
      · rw [ht1]
        have hnorm : |R (f 1) 1|<1 := by
          rw [(hRcoord (f 1)).2,abs_div,abs_of_pos hρ]
          exact (div_lt_one hρ).mpr (hFstrip 1).2
        have hlong : R (f 1) 0=1 := by
          have hs := (hFstrip 1).1
          rw [hf1,hEs] at hs
          obtain ⟨z,hz,he⟩ := hs
          have heq := G.first_embedding.injective he
          subst z
          have hE := hcoord (G.θf true,A.w) hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
          rw [hf1,(hRcoord _).1,hE]
          change (2*(G.θf true:ℝ)-(G.θf false:ℝ)-(G.θf true:ℝ))/((G.θf true:ℝ)-(G.θf false:ℝ))=1
          apply (div_eq_iff hgap.ne').mpr
          ring
        exact mem_closedSquare_zero_one.mpr (by rw [Plane.supNorm,hlong];norm_num;exact hnorm.le)
      · exact Plane.openSquare_subset_closedSquare 0 1
          (hpProper ⟨Set.mem_range_self t,by
            simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
            exact ⟨fun he=>ht0 (hpInjective he),fun he=>ht1 (hpInjective he)⟩⟩)
  have hWholeSquareIntersection : Q ∩ A.d.image=Set.range f := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [hWhole] at hx
      rcases hx.2 with ((hxf|hxg)|hxC0)|hxC1
      · exact hxf
      · exact (hGoutside hxg hx.1).elim
      · obtain ⟨t,rfl⟩ := hxC0
        by_cases ht : t=0
        · rw [ht,A.first_port,← hf0]
          exact Set.mem_range_self 0
        · exact (hCapsOutside false ⟨t,⟨lt_of_le_of_ne t.property.1 (Ne.symm ht),t.property.2⟩,rfl⟩ hx.1).elim
      · obtain ⟨t,rfl⟩ := hxC1
        by_cases ht : t=0
        · rw [ht,A.first_port,← hf1]
          exact Set.mem_range_self 1
        · exact (hCapsOutside true ⟨t,⟨lt_of_le_of_ne t.property.1 (Ne.symm ht),t.property.2⟩,rfl⟩ hx.1).elim
    · exact fun _ hx=>⟨hFirstInQ hx,hFcurve hx⟩
  have hNcoords (u : Interval) (w : Set.Icc (-1:ℝ) 1) (hs : G.N (u,w) ∈ E.source) :
      E (G.N (u,w))=Plane.mk u w := by
    rw [hEs] at hs
    obtain ⟨z,hz,he⟩ := hs
    have heq := G.first_embedding.injective he
    subst z
    exact hcoord (u,w) hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  have hEPort (k : Bool) : E (G.N (G.θf k,A.w))=Plane.mk (G.θf k) A.w := by
    apply hNcoords
    cases k
    · exact hf0 ▸ (hFstrip 0).1
    · exact hf1 ▸ (hFstrip 1).1
  have hAwSmall : |(A.w:ℝ)|<ρ := by
    have he := congrArg (fun q : Plane=>q 1) (hEPort false)
    have hfE : E (f 0) 1=(A.w:ℝ) := by rw [hf0];exact he
    exact hfE ▸ (hFstrip 0).2
  have hAwUnit : |(A.w:ℝ)|<1 := hAwSmall.trans hρlt
  have hAwNormal : |(A.w:ℝ)/ρ|<1 := by
    rw [abs_div,abs_of_pos hρ]
    exact (div_lt_one hρ).mpr hAwSmall
  have hp0 : p 0=Plane.mk (-1) ((A.w:ℝ)/ρ) := by
    ext j
    fin_cases j
    · change R (f 0) 0=-1
      rw [(hRcoord _).1,hf0,hEPort]
      change (2*(G.θf false:ℝ)-(G.θf false:ℝ)-(G.θf true:ℝ))/((G.θf true:ℝ)-(G.θf false:ℝ))=-1
      apply (div_eq_iff hgap.ne').mpr
      ring
    · change R (f 0) 1=(A.w:ℝ)/ρ
      rw [(hRcoord _).2,hf0,hEPort]
      rfl
  have hp1 : p 1=Plane.mk 1 ((A.w:ℝ)/ρ) := by
    ext j
    fin_cases j
    · change R (f 1) 0=1
      rw [(hRcoord _).1,hf1,hEPort]
      change (2*(G.θf true:ℝ)-(G.θf false:ℝ)-(G.θf true:ℝ))/((G.θf true:ℝ)-(G.θf false:ℝ))=1
      apply (div_eq_iff hgap.ne').mpr
      ring
    · change R (f 1) 1=(A.w:ℝ)/ρ
      rw [(hRcoord _).2,hf1,hEPort]
      rfl
  have hp0Boundary : p 0 ∈ modelCurve := by
    change Plane.supNorm (p 0)=1
    rw [hp0]
    change max |(-1:ℝ)| |(A.w:ℝ)/ρ|=1
    norm_num
    exact hAwNormal.le
  have hp1Boundary : p 1 ∈ modelCurve := by
    change Plane.supNorm (p 1)=1
    rw [hp1]
    change max |(1:ℝ)| |(A.w:ℝ)/ρ|=1
    norm_num
    exact hAwNormal.le
  obtain ⟨qsrc,hqsrc,hqsrc0,hqsrc1,hqsrcRange,hqsrcVal⟩ := source_affine_subinterval
    (G.θf false) (G.θf true) G.first_ports_order
  have hNsource (u : Interval) (hu : u ∈ Set.Icc (G.θf false) (G.θf true)) : G.N (u,A.w) ∈ R.source := by
    rw [hRs,hEs]
    exact ⟨(u,A.w),⟨(G.θf_internal false).1.trans_le hu.1,
      (show (u:ℝ)≤(G.θf true:ℝ) from hu.2).trans_lt (G.θf_internal true).2,
      (abs_lt.mp hAwUnit).1,(abs_lt.mp hAwUnit).2⟩,rfl⟩
  let q : C(Interval,Plane) := ⟨fun t=>R (G.N (qsrc t,A.w)),by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hNc : ContinuousAt (fun u : Interval=>G.N (qsrc u,A.w)) t :=
      (G.first_embedding.continuous.comp (hqsrc.continuous.prodMk continuous_const)).continuousAt
    have hRc : ContinuousAt R (G.N (qsrc t,A.w)) :=
      R.continuousAt (hNsource (qsrc t) (hqsrcRange ▸ Set.mem_range_self t))
    exact hRc.comp (f:=fun u : Interval=>G.N (qsrc u,A.w)) hNc⟩
  have hqInjective : Function.Injective q := by
    intro t u he
    apply hqsrc.injective
    have hh := R.injOn (hNsource _ (hqsrcRange ▸ Set.mem_range_self t))
      (hNsource _ (hqsrcRange ▸ Set.mem_range_self u)) he
    exact congrArg Prod.fst (G.first_embedding.injective hh)
  have hq0 : q 0=p 0 := by change R (G.N (qsrc 0,A.w))=R (f 0);rw [hqsrc0,hf0]
  have hq1 : q 1=p 1 := by change R (G.N (qsrc 1,A.w))=R (f 1);rw [hqsrc1,hf1]
  have hqArc : IsArcBetween (Set.range q) (p 0) (p 1) := by
    rw [← hq0,← hq1]
    exact hIntervalPlaneArc q hqInjective
  have hqCoordinates (t : Interval) : q t 0=2*(t:ℝ)-1 ∧ q t 1=(A.w:ℝ)/ρ := by
    have hE := hNcoords (qsrc t) A.w (hRs ▸ hNsource _ (hqsrcRange ▸ Set.mem_range_self t))
    constructor
    · change R (G.N (qsrc t,A.w)) 0=_
      rw [(hRcoord _).1,hE]
      change (2*(qsrc t:ℝ)-(G.θf false:ℝ)-(G.θf true:ℝ))/((G.θf true:ℝ)-(G.θf false:ℝ))=2*(t:ℝ)-1
      rw [hqsrcVal]
      apply (div_eq_iff hgap.ne').mpr
      ring
    · change R (G.N (qsrc t,A.w)) 1=(A.w:ℝ)/ρ
      rw [(hRcoord _).2,hE]
      rfl
  have hqProper : Set.range q \ {p 0,p 1} ⊆ Plane.openSquare 0 1 := by
    rintro x ⟨⟨t,rfl⟩,hx⟩
    have ht0 : t≠0 := by intro he; exact hx (by rw [he,hq0];simp)
    have ht1 : t≠1 := by intro he; exact hx (by rw [he,hq1];simp)
    have ht0r : 0<(t:ℝ) := lt_of_le_of_ne t.property.1 (fun he=>ht0 (Subtype.ext he.symm))
    have ht1r : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (fun he=>ht1 (Subtype.ext he))
    apply mem_openSquare_zero_one.mpr
    rw [Plane.supNorm,(hqCoordinates t).1,(hqCoordinates t).2,max_lt_iff]
    refine ⟨?_,hAwNormal⟩
    rw [abs_lt]
    constructor <;> linarith
  have hPullOld : {x : S | x ∈ R.source ∧ R x ∈ Set.range p}=Set.range f := by
    ext x
    constructor
    · rintro ⟨hs,⟨t,ht⟩⟩
      exact ⟨t,R.injOn (hRs.symm ▸ (hFstrip t).1) hs ht⟩
    · rintro ⟨t,rfl⟩
      exact ⟨hRs.symm ▸ (hFstrip t).1,Set.mem_range_self t⟩
  obtain ⟨Hfirst,dfirst,hFirstAmbient,hFirstFinalMapImage,hFirstImage,hFirstSupport⟩ :=
    source_curve_surface_crosscut_replacement S A.d R hRtarget (Set.range p) (Set.range q) (p 0) (p 1)
      hpArc hqArc hp0Boundary hp1Boundary hpProper hqProper
      (hWholeSquareIntersection.trans hPullOld.symm)
  let T := G.N '' (Set.Icc (G.θf false) (G.θf true) ×ˢ {A.w})
  have hPullNew : {x : S | x ∈ R.source ∧ R x ∈ Set.range q}=T := by
    ext x
    constructor
    · rintro ⟨hs,⟨t,ht⟩⟩
      have hu := hqsrcRange ▸ Set.mem_range_self t
      exact ⟨(qsrc t,A.w),⟨hu,Set.mem_singleton _⟩,
        R.injOn (hNsource (qsrc t) hu) hs ht⟩
    · rintro ⟨⟨u,w⟩,⟨hu,hw⟩,he⟩
      have hwa : w=A.w := Set.mem_singleton_iff.mp hw
      subst w
      obtain ⟨t,ht⟩ := hqsrcRange.symm ▸ hu
      refine ⟨he ▸ hNsource u hu,⟨t,?_⟩⟩
      change R (G.N (qsrc t,A.w))=R x
      rw [ht,he]
  have hTrackPort (k : Bool) : G.N (G.θf k,A.w) ∈ T := by
    refine ⟨(G.θf k,A.w),⟨?_,Set.mem_singleton _⟩,rfl⟩
    cases k
    · exact ⟨le_rfl,G.first_ports_order.le⟩
    · exact ⟨G.first_ports_order.le,le_rfl⟩
  have hCapFirstIntersection (k : Bool) (x : S)
      (hxC : x ∈ Set.range (A.C k)) (hxf : x ∈ Set.range f) :
      x=G.N (G.θf k,A.w) := by
    obtain ⟨t,rfl⟩ := hxC
    by_cases ht : t=0
    · rw [ht,A.first_port]
    · have ht0 : (0:Interval)<t :=
        lt_of_le_of_ne (show (0:Interval)≤t from t.property.1) (Ne.symm ht)
      exact (hCapsOutside k ⟨t,⟨ht0,t.property.2⟩,rfl⟩ (hFirstInQ hxf)).elim
  rw [hPullOld,hPullNew] at hFirstImage
  have hFirstExactImage : dfirst.image=T ∪ Set.range g ∪ Set.range (A.C false) ∪ Set.range (A.C true) := by
    rw [hFirstImage]
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with ⟨hx,hxnot⟩|hx
      · rw [hWhole] at hx
        rcases hx with ((hxf|hxg)|hx0)|hx1
        · exact (hxnot hxf).elim
        · exact Or.inl (Or.inl (Or.inr hxg))
        · exact Or.inl (Or.inr hx0)
        · exact Or.inr hx1
      · exact Or.inl (Or.inl (Or.inl hx))
    · intro x hx
      rcases hx with ((hxT|hxg)|hx0)|hx1
      · exact Or.inr hxT
      · exact Or.inl ⟨hGcurve hxg,fun hxf=>Set.disjoint_left.mp hfg hxf hxg⟩
      · by_cases hxf : x ∈ Set.range f
        · exact Or.inr ((hCapFirstIntersection false x hx0 hxf).symm ▸ hTrackPort false)
        · exact Or.inl ⟨(A.subset false hx0).2,hxf⟩
      · by_cases hxf : x ∈ Set.range f
        · exact Or.inr ((hCapFirstIntersection true x hx1 hxf).symm ▸ hTrackPort true)
        · exact Or.inl ⟨(A.subset true hx1).2,hxf⟩
  obtain ⟨Rg,hRgs,hRgTarget,hRgCoord,_hRgAxis⟩ := hRepairThinSquare Eg hEgt
    (G.θg false) (G.θg true) (G.θg_internal false).1 G.closing_ports_order (G.θg_internal true).2 ρg hρg hρglt
  let pg : C(Interval,Plane) := ⟨fun t=>Rg (g t),by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (Rg.continuousAt (hRgs.symm ▸ (hGstrip t).1)).comp g.continuous.continuousAt⟩
  have hpgInjective : Function.Injective pg := by
    intro t u he
    apply hg.injective
    exact Rg.injOn (hRgs.symm ▸ (hGstrip t).1) (hRgs.symm ▸ (hGstrip u).1) he
  have hpgArc := hIntervalPlaneArc pg hpgInjective
  have hpgProper : Set.range pg \ {pg 0,pg 1} ⊆ Plane.openSquare 0 1 := by
    rintro x ⟨⟨t,rfl⟩,hx⟩
    have ht0 : t≠0 := by intro he; exact hx (by rw [he]; simp)
    have ht1 : t≠1 := by intro he; exact hx (by rw [he]; simp)
    have ht0r : 0<(t:ℝ) := lt_of_le_of_ne t.property.1 (by exact fun he=>ht0 (Subtype.ext he.symm))
    have ht1r : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (by exact fun he=>ht1 (Subtype.ext he))
    have hlong := hGproper t ht0r ht1r
    have hnormal := (hGstrip t).2
    have hgap : 0<(G.θg true:ℝ)-(G.θg false:ℝ) := sub_pos.mpr G.closing_ports_order
    have hlongR : |Rg (g t) 0|<1 := by
      rw [(hRgCoord (g t)).1,abs_lt]
      constructor
      · apply (lt_div_iff₀ hgap).mpr
        linarith [hlong.1]
      · apply (div_lt_iff₀ hgap).mpr
        linarith [hlong.2]
    have hnormalR : |Rg (g t) 1|<1 := by
      rw [(hRgCoord (g t)).2,abs_div,abs_of_pos hρg]
      exact (div_lt_one hρg).mpr hnormal
    change pg t ∈ Plane.openSquare 0 1
    exact mem_openSquare_zero_one.mpr (max_lt hlongR hnormalR)
  let Qg : Set S := {x | x ∈ Rg.source ∧ Rg x ∈ Plane.closedSquare 0 1}
  let Vg : Set S := {x | x ∈ Rg.source ∧ Rg x ∈ Plane.openSquare 0 1}
  have hgapg : 0<(G.θg true:ℝ)-(G.θg false:ℝ) := sub_pos.mpr G.closing_ports_order
  have hQgData (x : S) (hx : x ∈ Qg) :
      ∃ ugPoint : Interval, ∃ wgPoint : Set.Icc (-1:ℝ) 1,
        ugPoint ∈ Set.Icc (G.θg false) (G.θg true) ∧ |(wgPoint:ℝ)|≤ρg ∧
        G.M (ugPoint,wgPoint)=x ∧
        Rg x 0=(2*(ugPoint:ℝ)-(G.θg false:ℝ)-(G.θg true:ℝ))/((G.θg true:ℝ)-(G.θg false:ℝ)) ∧
        Rg x 1=(wgPoint:ℝ)/ρg := by
    have hs : x ∈ Eg.source := hRgs ▸ hx.1
    rw [hEgs] at hs
    obtain ⟨⟨ugPoint,wgPoint⟩,hu,he⟩ := hs
    have hEcoords : Eg x=Plane.mk ugPoint wgPoint := by
      rw [← he]
      exact hgcoord (ugPoint,wgPoint) hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
    have hR0 := (hRgCoord x).1
    have hR1 := (hRgCoord x).2
    rw [hEcoords] at hR0 hR1
    change Rg x 0=(2*(ugPoint:ℝ)-(G.θg false:ℝ)-(G.θg true:ℝ))/((G.θg true:ℝ)-(G.θg false:ℝ)) at hR0
    change Rg x 1=(wgPoint:ℝ)/ρg at hR1
    have hnorm := mem_closedSquare_zero_one.mp hx.2
    have hlong := abs_le.mp ((Plane.abs_zero_le_supNorm (Rg x)).trans hnorm)
    have hnormal := (Plane.abs_one_le_supNorm (Rg x)).trans hnorm
    have hul : (G.θg false:ℝ)≤ugPoint := by
      rw [hR0] at hlong
      have hh := (le_div_iff₀ hgapg).mp hlong.1
      linarith
    have hur : (ugPoint:ℝ)≤G.θg true := by
      rw [hR0] at hlong
      have hh := (div_le_iff₀ hgapg).mp hlong.2
      linarith
    have hw : |(wgPoint:ℝ)|≤ρg := by
      rw [hR1,abs_div,abs_of_pos hρg] at hnormal
      exact (div_le_one hρg).mp hnormal
    exact ⟨ugPoint,wgPoint,⟨hul,hur⟩,hw,he,hR0,hR1⟩
  have hCurveBoundaryG (x : S) (hxQ : x ∈ Qg) (hxV : x ∉ Vg) (hxd : x ∈ A.d.image) :
      x=g 0 ∨ x=g 1 := by
    obtain ⟨ugPoint,wgPoint,hu,hw,he,hR0,hR1⟩ := hQgData x hxQ
    have hnorm := mem_closedSquare_zero_one.mp hxQ.2
    have hno : ¬ Plane.supNorm (Rg x)<1 := by
      intro hn
      exact hxV ⟨hxQ.1,mem_openSquare_zero_one.mpr hn⟩
    have hlongle := (Plane.abs_zero_le_supNorm (Rg x)).trans hnorm
    have hnormalle := (Plane.abs_one_le_supNorm (Rg x)).trans hnorm
    have hlongOrNormal : |Rg x 0|=1 ∨ |Rg x 1|=1 := by
      by_cases hl : |Rg x 0|<1
      · right
        apply le_antisymm hnormalle
        by_contra hn
        exact hno (max_lt hl (lt_of_not_ge hn))
      · exact Or.inl (le_antisymm hlongle (le_of_not_gt hl))
    rcases hlongOrNormal with hl|hn
    · have hlsign : Rg x 0=1 ∨ Rg x 0=-1 := by
        by_cases hp : 0≤Rg x 0
        · exact Or.inl (by rwa [abs_of_nonneg hp] at hl)
        · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge hp)] at hl; linarith)
      have huend : ugPoint=G.θg false ∨ ugPoint=G.θg true := by
        rcases hlsign with hright|hleft
        · right
          apply Subtype.ext
          have hh := (div_eq_iff hgapg.ne').mp (hR0.symm.trans hright)
          linarith
        · left
          apply Subtype.ext
          have hh := (div_eq_iff hgapg.ne').mp (hR0.symm.trans hleft)
          linarith
      rcases huend with hue|hue
      · have hwa : wgPoint=A.z := (hSideClosing A hvSideClosing false wgPoint hw).mp (by rw [← hue,he];exact hxd)
        exact Or.inl (by rw [← he,hue,hwa,← hg0])
      · have hwa : wgPoint=A.z := (hSideClosing A hvSideClosing true wgPoint hw).mp (by rw [← hue,he];exact hxd)
        exact Or.inr (by rw [← he,hue,hwa,← hg1])
    · have hnsign : Rg x 1=1 ∨ Rg x 1=-1 := by
        by_cases hp : 0≤Rg x 1
        · exact Or.inl (by rwa [abs_of_nonneg hp] at hn)
        · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge hp)] at hn; linarith)
      have hwW : wgPoint ∈ Set.range Wg := by
        rcases hnsign with hplus|hminus
        · refine ⟨true,?_⟩
          apply Subtype.ext
          have hh := (div_eq_iff hρg.ne').mp (hR1.symm.trans hplus)
          change ρg=(wgPoint:ℝ)
          linarith
        · refine ⟨false,?_⟩
          apply Subtype.ext
          have hh := (div_eq_iff hρg.ne').mp (hR1.symm.trans hminus)
          change -ρg=(wgPoint:ℝ)
          linarith
      exact (Set.disjoint_left.mp hAdAvoidY hxd ⟨(ugPoint,wgPoint),⟨hu,hwW⟩,he⟩).elim
  have hQgCompact : IsCompact Qg := by
    have hQgeq : Qg=Rg.symm '' Plane.closedSquare 0 1 := by
      ext x
      constructor
      · intro hx
        exact ⟨Rg x,hx.2,Rg.left_inv hx.1⟩
      · rintro ⟨z,hz,rfl⟩
        exact ⟨Rg.map_target (hRgTarget hz),by rw [Rg.right_inv (hRgTarget hz)];exact hz⟩
    rw [hQgeq]
    exact (isCompact_closedSquare 0 1).image_of_continuousOn (Rg.symm.continuousOn.mono hRgTarget)
  have hVgOpen : IsOpen Vg := Rg.isOpen_inter_preimage (Plane.isOpen_openSquare 0 1)
  have hVgQg : Vg ⊆ Qg := fun _ hx=>⟨hx.1,Plane.openSquare_subset_closedSquare 0 1 hx.2⟩
  have hQgBand : Qg ⊆ G.M '' (Set.Icc (G.θg false) (G.θg true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))) := by
    intro x hx
    obtain ⟨u,w,hu,_hw,he,_hc⟩ := hQgData x hx
    exact ⟨(u,w),⟨hu,Set.mem_univ _⟩,he⟩
  have hTrackOutsideQg : T ⊆ Qgᶜ := by
    rintro x ⟨⟨u,w⟩,hu,he⟩ hxQ
    have hxN : x ∈ G.N '' (Set.Icc (G.θf false) (G.θf true) ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1))) :=
      ⟨(u,w),⟨hu.1,Set.mem_univ _⟩,he⟩
    exact Set.disjoint_left.mp hBands hxN (hQgBand hxQ)
  have hCapNoClosingPort (k j : Bool) (t : Interval) (ht : t<(1:Interval)) :
      A.C k t≠G.M (G.θg j,A.z) := by
    intro he
    have hhe : A.C k t=A.C j 1 := he.trans (A.closing_port j).symm
    by_cases hkj : k=j
    · subst j
      exact ht.ne ((A.embedding k).injective hhe)
    · have hxk := Set.mem_range_self (f:=A.C k) t
      have hxj : A.C k t ∈ Set.range (A.C j) := ⟨1,hhe.symm⟩
      cases k <;> cases j
      · exact hkj rfl
      · exact Set.disjoint_left.mp A.caps_disjoint hxk hxj
      · exact Set.disjoint_left.mp A.caps_disjoint hxj hxk
      · exact hkj rfl
  have hCapsClosingOutside (k : Bool) :
      (A.C k '' Set.Ico (0:Interval) 1) ⊆ Qgᶜ := by
    have hCapPartition : A.C k '' Set.Ico (0:Interval) 1 ⊆ Vg ∪ Qgᶜ := by
      rintro x ⟨t,ht,rfl⟩
      by_cases hxQ : A.C k t ∈ Qg
      · left
        by_contra hxV
        rcases hCurveBoundaryG _ hxQ hxV (A.subset k (Set.mem_range_self t)).2 with he|he
        · exact hCapNoClosingPort k false t ht.2 (he.trans hg0)
        · exact hCapNoClosingPort k true t ht.2 (he.trans hg1)
      · exact Or.inr hxQ
    have hCapConnected : IsPreconnected (A.C k '' Set.Ico (0:Interval) 1) :=
      isPreconnected_Ico.image (A.C k) (A.C k).continuous.continuousOn
    rcases hCapConnected.subset_or_subset hVgOpen hQgCompact.isClosed.isOpen_compl
      (Set.disjoint_left.mpr (fun _ hxV hxQ=>hxQ (hVgQg hxV))) hCapPartition with hin|hout
    · have hstart : A.C k 0 ∈ A.C k '' Set.Ico (0:Interval) 1 := ⟨0,⟨le_rfl,by norm_num⟩,rfl⟩
      exact (hTrackOutsideQg (hTrackPort k) ((A.first_port k) ▸ hVgQg (hin hstart))).elim
    · exact hout
  have hClosingInQg : Set.range g ⊆ Qg := by
    rintro x ⟨t,rfl⟩
    refine ⟨hRgs.symm ▸ (hGstrip t).1,?_⟩
    by_cases ht0 : t=0
    · rw [ht0]
      have hnorm : |Rg (g 0) 1|<1 := by
        rw [(hRgCoord (g 0)).2,abs_div,abs_of_pos hρg]
        exact (div_lt_one hρg).mpr (hGstrip 0).2
      have hlong : Rg (g 0) 0=-1 := by
        have hs := (hGstrip 0).1
        rw [hg0,hEgs] at hs
        obtain ⟨z,hz,he⟩ := hs
        have heq := G.closing_embedding.injective he
        subst z
        have hE := hgcoord (G.θg false,A.z) hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
        rw [hg0,(hRgCoord _).1,hE]
        change (2*(G.θg false:ℝ)-(G.θg false:ℝ)-(G.θg true:ℝ))/((G.θg true:ℝ)-(G.θg false:ℝ))=-1
        apply (div_eq_iff hgapg.ne').mpr
        ring
      exact mem_closedSquare_zero_one.mpr (by rw [Plane.supNorm,hlong];norm_num;exact hnorm.le)
    · by_cases ht1 : t=1
      · rw [ht1]
        have hnorm : |Rg (g 1) 1|<1 := by
          rw [(hRgCoord (g 1)).2,abs_div,abs_of_pos hρg]
          exact (div_lt_one hρg).mpr (hGstrip 1).2
        have hlong : Rg (g 1) 0=1 := by
          have hs := (hGstrip 1).1
          rw [hg1,hEgs] at hs
          obtain ⟨z,hz,he⟩ := hs
          have heq := G.closing_embedding.injective he
          subst z
          have hE := hgcoord (G.θg true,A.z) hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
          rw [hg1,(hRgCoord _).1,hE]
          change (2*(G.θg true:ℝ)-(G.θg false:ℝ)-(G.θg true:ℝ))/((G.θg true:ℝ)-(G.θg false:ℝ))=1
          apply (div_eq_iff hgapg.ne').mpr
          ring
        exact mem_closedSquare_zero_one.mpr (by rw [Plane.supNorm,hlong];norm_num;exact hnorm.le)
      · exact Plane.openSquare_subset_closedSquare 0 1
          (hpgProper ⟨Set.mem_range_self t,by
            simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
            exact ⟨fun he=>ht0 (hpgInjective he),fun he=>ht1 (hpgInjective he)⟩⟩)
  have hWholeClosingSquareIntersection : Qg ∩ dfirst.image=Set.range g := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [hFirstExactImage] at hx
      rcases hx.2 with ((hxT|hxg)|hxC0)|hxC1
      · exact (hTrackOutsideQg hxT hx.1).elim
      · exact hxg
      · obtain ⟨t,rfl⟩ := hxC0
        by_cases ht : t=1
        · rw [ht,A.closing_port,← hg0]
          exact Set.mem_range_self 0
        · exact (hCapsClosingOutside false ⟨t,⟨t.property.1,
            lt_of_le_of_ne (show t≤(1:Interval) from t.property.2) ht⟩,rfl⟩ hx.1).elim
      · obtain ⟨t,rfl⟩ := hxC1
        by_cases ht : t=1
        · rw [ht,A.closing_port,← hg1]
          exact Set.mem_range_self 1
        · exact (hCapsClosingOutside true ⟨t,⟨t.property.1,
            lt_of_le_of_ne (show t≤(1:Interval) from t.property.2) ht⟩,rfl⟩ hx.1).elim
    · intro x hx
      exact ⟨hClosingInQg hx,by rw [hFirstExactImage];exact Or.inl (Or.inl (Or.inr hx))⟩
  have hMcoords (u : Interval) (z : Set.Icc (-1:ℝ) 1) (hs : G.M (u,z) ∈ Eg.source) :
      Eg (G.M (u,z))=Plane.mk u z := by
    rw [hEgs] at hs
    obtain ⟨z,hz,he⟩ := hs
    have heq := G.closing_embedding.injective he
    subst z
    exact hgcoord (u,z) hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  have hEgPort (k : Bool) : Eg (G.M (G.θg k,A.z))=Plane.mk (G.θg k) A.z := by
    apply hMcoords
    cases k
    · exact hg0 ▸ (hGstrip 0).1
    · exact hg1 ▸ (hGstrip 1).1
  have hAzSmall : |(A.z:ℝ)|<ρg := by
    have he := congrArg (fun qg : Plane=>qg 1) (hEgPort false)
    have hfE : Eg (g 0) 1=(A.z:ℝ) := by rw [hg0];exact he
    exact hfE ▸ (hGstrip 0).2
  have hAzUnit : |(A.z:ℝ)|<1 := hAzSmall.trans hρglt
  have hAzNormal : |(A.z:ℝ)/ρg|<1 := by
    rw [abs_div,abs_of_pos hρg]
    exact (div_lt_one hρg).mpr hAzSmall
  have hpg0 : pg 0=Plane.mk (-1) ((A.z:ℝ)/ρg) := by
    ext j
    fin_cases j
    · change Rg (g 0) 0=-1
      rw [(hRgCoord _).1,hg0,hEgPort]
      change (2*(G.θg false:ℝ)-(G.θg false:ℝ)-(G.θg true:ℝ))/((G.θg true:ℝ)-(G.θg false:ℝ))=-1
      apply (div_eq_iff hgapg.ne').mpr
      ring
    · change Rg (g 0) 1=(A.z:ℝ)/ρg
      rw [(hRgCoord _).2,hg0,hEgPort]
      rfl
  have hpg1 : pg 1=Plane.mk 1 ((A.z:ℝ)/ρg) := by
    ext j
    fin_cases j
    · change Rg (g 1) 0=1
      rw [(hRgCoord _).1,hg1,hEgPort]
      change (2*(G.θg true:ℝ)-(G.θg false:ℝ)-(G.θg true:ℝ))/((G.θg true:ℝ)-(G.θg false:ℝ))=1
      apply (div_eq_iff hgapg.ne').mpr
      ring
    · change Rg (g 1) 1=(A.z:ℝ)/ρg
      rw [(hRgCoord _).2,hg1,hEgPort]
      rfl
  have hpg0Boundary : pg 0 ∈ modelCurve := by
    change Plane.supNorm (pg 0)=1
    rw [hpg0]
    change max |(-1:ℝ)| |(A.z:ℝ)/ρg|=1
    norm_num
    exact hAzNormal.le
  have hpg1Boundary : pg 1 ∈ modelCurve := by
    change Plane.supNorm (pg 1)=1
    rw [hpg1]
    change max |(1:ℝ)| |(A.z:ℝ)/ρg|=1
    norm_num
    exact hAzNormal.le
  obtain ⟨qgsrc,hqgsrc,hqgsrc0,hqgsrc1,hqgsrcRange,hqgsrcVal⟩ := source_affine_subinterval
    (G.θg false) (G.θg true) G.closing_ports_order
  have hMsource (u : Interval) (hu : u ∈ Set.Icc (G.θg false) (G.θg true)) : G.M (u,A.z) ∈ Rg.source := by
    rw [hRgs,hEgs]
    exact ⟨(u,A.z),⟨(G.θg_internal false).1.trans_le hu.1,
      (show (u:ℝ)≤(G.θg true:ℝ) from hu.2).trans_lt (G.θg_internal true).2,
      (abs_lt.mp hAzUnit).1,(abs_lt.mp hAzUnit).2⟩,rfl⟩
  let qg : C(Interval,Plane) := ⟨fun t=>Rg (G.M (qgsrc t,A.z)),by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hMc : ContinuousAt (fun u : Interval=>G.M (qgsrc u,A.z)) t :=
      (G.closing_embedding.continuous.comp (hqgsrc.continuous.prodMk continuous_const)).continuousAt
    have hRgc : ContinuousAt Rg (G.M (qgsrc t,A.z)) :=
      Rg.continuousAt (hMsource (qgsrc t) (hqgsrcRange ▸ Set.mem_range_self t))
    exact hRgc.comp (f:=fun u : Interval=>G.M (qgsrc u,A.z)) hMc⟩
  have hqgInjective : Function.Injective qg := by
    intro t u he
    apply hqgsrc.injective
    have hh := Rg.injOn (hMsource _ (hqgsrcRange ▸ Set.mem_range_self t))
      (hMsource _ (hqgsrcRange ▸ Set.mem_range_self u)) he
    exact congrArg Prod.fst (G.closing_embedding.injective hh)
  have hqg0 : qg 0=pg 0 := by change Rg (G.M (qgsrc 0,A.z))=Rg (g 0);rw [hqgsrc0,hg0]
  have hqg1 : qg 1=pg 1 := by change Rg (G.M (qgsrc 1,A.z))=Rg (g 1);rw [hqgsrc1,hg1]
  have hqgArc : IsArcBetween (Set.range qg) (pg 0) (pg 1) := by
    rw [← hqg0,← hqg1]
    exact hIntervalPlaneArc qg hqgInjective
  have hqgCoordinates (t : Interval) : qg t 0=2*(t:ℝ)-1 ∧ qg t 1=(A.z:ℝ)/ρg := by
    have hE := hMcoords (qgsrc t) A.z (hRgs ▸ hMsource _ (hqgsrcRange ▸ Set.mem_range_self t))
    constructor
    · change Rg (G.M (qgsrc t,A.z)) 0=_
      rw [(hRgCoord _).1,hE]
      change (2*(qgsrc t:ℝ)-(G.θg false:ℝ)-(G.θg true:ℝ))/((G.θg true:ℝ)-(G.θg false:ℝ))=2*(t:ℝ)-1
      rw [hqgsrcVal]
      apply (div_eq_iff hgapg.ne').mpr
      ring
    · change Rg (G.M (qgsrc t,A.z)) 1=(A.z:ℝ)/ρg
      rw [(hRgCoord _).2,hE]
      rfl
  have hqgProper : Set.range qg \ {pg 0,pg 1} ⊆ Plane.openSquare 0 1 := by
    rintro x ⟨⟨t,rfl⟩,hx⟩
    have ht0 : t≠0 := by intro he; exact hx (by rw [he,hqg0];simp)
    have ht1 : t≠1 := by intro he; exact hx (by rw [he,hqg1];simp)
    have ht0r : 0<(t:ℝ) := lt_of_le_of_ne t.property.1 (fun he=>ht0 (Subtype.ext he.symm))
    have ht1r : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (fun he=>ht1 (Subtype.ext he))
    apply mem_openSquare_zero_one.mpr
    rw [Plane.supNorm,(hqgCoordinates t).1,(hqgCoordinates t).2,max_lt_iff]
    refine ⟨?_,hAzNormal⟩
    rw [abs_lt]
    constructor <;> linarith
  have hPullOldG : {x : S | x ∈ Rg.source ∧ Rg x ∈ Set.range pg}=Set.range g := by
    ext x
    constructor
    · rintro ⟨hs,⟨t,ht⟩⟩
      exact ⟨t,Rg.injOn (hRgs.symm ▸ (hGstrip t).1) hs ht⟩
    · rintro ⟨t,rfl⟩
      exact ⟨hRgs.symm ▸ (hGstrip t).1,Set.mem_range_self t⟩
  obtain ⟨Hclosing,dfinal,hClosingAmbient,hClosingFinalMapImage,hClosingImage,hClosingSupport⟩ :=
    source_curve_surface_crosscut_replacement S dfirst Rg hRgTarget (Set.range pg) (Set.range qg) (pg 0) (pg 1)
      hpgArc hqgArc hpg0Boundary hpg1Boundary hpgProper hqgProper
      (hWholeClosingSquareIntersection.trans hPullOldG.symm)
  let Tg := G.M '' (Set.Icc (G.θg false) (G.θg true) ×ˢ {A.z})
  have hPullNewG : {x : S | x ∈ Rg.source ∧ Rg x ∈ Set.range qg}=Tg := by
    ext x
    constructor
    · rintro ⟨hs,⟨t,ht⟩⟩
      have hu := hqgsrcRange ▸ Set.mem_range_self t
      exact ⟨(qgsrc t,A.z),⟨hu,Set.mem_singleton _⟩,
        Rg.injOn (hMsource (qgsrc t) hu) hs ht⟩
    · rintro ⟨⟨u,z⟩,⟨hu,hw⟩,he⟩
      have hwa : z=A.z := Set.mem_singleton_iff.mp hw
      subst z
      obtain ⟨t,ht⟩ := hqgsrcRange.symm ▸ hu
      refine ⟨he ▸ hMsource u hu,⟨t,?_⟩⟩
      change Rg (G.M (qgsrc t,A.z))=Rg x
      rw [ht,he]
  have hClosingTrackPort (k : Bool) : G.M (G.θg k,A.z) ∈ Tg := by
    refine ⟨(G.θg k,A.z),⟨?_,Set.mem_singleton _⟩,rfl⟩
    cases k
    · exact ⟨le_rfl,G.closing_ports_order.le⟩
    · exact ⟨G.closing_ports_order.le,le_rfl⟩
  have hCapClosingIntersection (k : Bool) (x : S)
      (hxC : x ∈ Set.range (A.C k)) (hxg : x ∈ Set.range g) :
      x=G.M (G.θg k,A.z) := by
    obtain ⟨t,rfl⟩ := hxC
    by_cases ht : t=1
    · rw [ht,A.closing_port]
    · have ht1 : t<(1:Interval) :=
        lt_of_le_of_ne (show t≤(1:Interval) from t.property.2) ht
      exact (hCapsClosingOutside k ⟨t,⟨t.property.1,ht1⟩,rfl⟩ (hClosingInQg hxg)).elim
  rw [hPullOldG,hPullNewG] at hClosingImage
  have hFinalExactImage : dfinal.image=T ∪ Tg ∪ Set.range (A.C false) ∪ Set.range (A.C true) := by
    rw [hClosingImage]
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with ⟨hx,hxnot⟩|hx
      · rw [hFirstExactImage] at hx
        rcases hx with ((hxT|hxg)|hx0)|hx1
        · exact Or.inl (Or.inl (Or.inl hxT))
        · exact (hxnot hxg).elim
        · exact Or.inl (Or.inr hx0)
        · exact Or.inr hx1
      · exact Or.inl (Or.inl (Or.inr hx))
    · intro x hx
      rcases hx with ((hxT|hxTg)|hx0)|hx1
      · exact Or.inl ⟨by rw [hFirstExactImage];exact Or.inl (Or.inl (Or.inl hxT)),
          fun hxg=>hTrackOutsideQg hxT (hClosingInQg hxg)⟩
      · exact Or.inr hxTg
      · by_cases hxg : x ∈ Set.range g
        · exact Or.inr ((hCapClosingIntersection false x hx0 hxg).symm ▸ hClosingTrackPort false)
        · exact Or.inl ⟨by rw [hFirstExactImage];exact Or.inl (Or.inr hx0),hxg⟩
      · by_cases hxg : x ∈ Set.range g
        · exact Or.inr ((hCapClosingIntersection true x hx1 hxg).symm ▸ hClosingTrackPort true)
        · exact Or.inl ⟨by rw [hFirstExactImage];exact Or.inr hx1,hxg⟩
  have hSourceToFirstAmbient := hAmbientRelTrans (B.boundary i).image A.d.image dfirst.image
    A.ambient hFirstAmbient
  have hSourceToFinalAmbient := hAmbientRelTrans (B.boundary i).image dfirst.image dfinal.image
    hSourceToFirstAmbient hClosingAmbient
  let Pfinal : SourceFirstReturnBudgetTracks D B i := {
    F:=G,caps:=A,first_middle:=P.first_middle,closing_middle:=P.closing_middle }
  have hFinalTrace : dfinal.image=Pfinal.trace := by
    rw [hFinalExactImage]
    have hT : T=(fun u=>G.N (u,A.w)) '' Set.Icc (G.θf false) (G.θf true) := by
      ext x
      constructor
      · rintro ⟨⟨u,w⟩,⟨hu,hw⟩,he⟩
        have hwa : w=A.w := Set.mem_singleton_iff.mp hw
        subst w
        exact ⟨u,hu,he⟩
      · rintro ⟨u,hu,he⟩
        exact ⟨(u,A.w),⟨hu,Set.mem_singleton _⟩,he⟩
    have hTg : Tg=(fun u=>G.M (u,A.z)) '' Set.Icc (G.θg false) (G.θg true) := by
      ext x
      constructor
      · rintro ⟨⟨u,w⟩,⟨hu,hw⟩,he⟩
        have hwa : w=A.z := Set.mem_singleton_iff.mp hw
        subst w
        exact ⟨u,hu,he⟩
      · rintro ⟨u,hu,he⟩
        exact ⟨(u,A.z),⟨hu,Set.mem_singleton _⟩,he⟩
    rw [hT,hTg]
    rfl
  obtain ⟨had,hbd⟩ := source_first_return_budget_trace_transverse S D B ht i Pfinal dfinal hFinalTrace
  have hbudget := source_first_return_whole_trace_budget D B ht i Pfinal
  refine ⟨dfinal,hSourceToFinalAmbient,hbd,had,?_,?_⟩
  · have hb : (b.image ∩ dfinal.image).ncard≤1 := by
      rw [Set.inter_comm,hFinalTrace]
      exact hbudget.2.2.2.1
    rwa [Set.ncard_eq_toFinset_card _ hbd.1] at hb
  · have ha : (a.image ∩ dfinal.image).ncard≤(source_surgery_retained_crossings B i).ncard+1 := by
      rw [Set.inter_comm,hFinalTrace]
      exact hbudget.2.2.1
    rwa [Set.ncard_eq_toFinset_card _ had.1] at ha

end CurveComplex
