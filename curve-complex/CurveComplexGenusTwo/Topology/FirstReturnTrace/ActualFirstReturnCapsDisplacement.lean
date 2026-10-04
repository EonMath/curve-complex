import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnCapsWithRadius
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualChartSupportedTranslationBound
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualTwoChartDisplacement
set_option maxHeartbeats 3000000
namespace CurveComplex
open Set Topology Schoenflies
/-- Actual whole closed-curve cap attachment with arbitrarily small common
widths and all-time whole-chart displacement control for its chosen isotopy. -/
theorem source_framed_first_return_caps_with_displacement
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool)
    (F : SourceFirstReturnFramedStrips D B i) (rmax : ℝ) (hrmax : 0<rmax) :
    ∃ A : SourceFirstReturnAttachedCaps F,
      (∀ k, ‖A.v k‖<rmax) ∧
      (∀ k t x, x ∈ (F.E k).source → 1/2 ≤ ‖F.E k x‖ → A.H.map (t,x)=x) ∧
      ∀ k t x, x ∈ (F.E k).source →
        ‖F.E k (A.H.map (t,x))-F.E k x‖ ≤ ‖A.v k‖ := by
  classical
  let h : Bool → ℝ := fun k => min (F.E k (D.first (F.θf k)) 1) (F.E k (B.closing i (F.θg k)) 0)
  have hh (k) : 0<h k := lt_min (F.first_height k).1 (F.closing_height k).1
  let r : ℝ := min rmax (min (1/32) (min (h false) (h true)/4))
  have hr : 0<r := lt_min hrmax (lt_min (by norm_num) (div_pos (lt_min (hh false) (hh true)) (by norm_num)))
  have hrold : r ≤ min (1/32) (min (h false) (h true)/4) := min_le_right _ _
  obtain ⟨w,z,hw,hz,v,hvc,hv,hvn,hv0,hv1⟩ :=
    source_two_corner_signed_frame_widths F.α F.β
      (fun k=>(F.corner_positive k).1) (fun k=>(F.corner_positive k).2.1) r hr
  have hvquarter (k) : ‖v k‖<1/4 := (hv k).trans_le (by
    have hh := min_le_left (1/32:ℝ) (min (h false) (h true)/4)
    linarith)
  have hvheight (k) : ‖v k‖<h k/4 := (hv k).trans_le (by
    have hh := min_le_right (1/32:ℝ) (min (h false) (h true)/4)
    have hl : min (h false) (h true)≤h k := by cases k; exact min_le_left _ _; exact min_le_right _ _
    linarith)
  let P : Bool → Plane → Prop := fun _ x => (x 0=0 ∧ 0≤x 1) ∨ (0≤x 0 ∧ x 1=0)
  obtain ⟨H,d,hd,hrel,hfix,hsource,hmove,htrace,hfar,hdisp⟩ :=
    source_two_disjoint_closed_curve_chart_translations_with_displacement S (B.boundary i) F.E F.square
      (F.disjoint.mono subset_closure subset_closure) P F.branch_trace v hvquarter
  have hlocal (k) (x : S) (hx : x ∈ (F.E k).source) (hn : ‖F.E k x-v k‖≤1/4) :
      x ∈ d.image ↔ (F.E k x 0=v k 0 ∧ v k 1≤F.E k x 1) ∨
        (v k 0≤F.E k x 0 ∧ F.E k x 1=v k 1) := by
    rw [htrace k x hx hn]
    change ((F.E k x 0-v k 0=0 ∧ 0≤F.E k x 1-v k 1) ∨
      (0≤F.E k x 0-v k 0 ∧ F.E k x 1-v k 1=0)) ↔ _
    simp only [sub_eq_zero,sub_nonneg]
  have hcap (k) := source_translated_cap_attaches_with_open_neighborhood d (F.E k) (F.square k)
    D.first (B.closing i) F.N F.M (F.θf k) (F.θg k) (F.ηf k) (F.ηg k) (F.α k) (F.β k)
    (F.first_framing k) (F.closing_framing k) (F.θf k) (F.θg k)
    (by simpa using (F.corner_positive k).2.2.1) (by simpa using (F.corner_positive k).2.2.2)
    w z (F.first_height k) (F.closing_height k)
    (by rw [← hvc k]; exact hvheight k)
    (by
      intro x hx hn
      have hl := hlocal k x hx (by rw [hvc k]; exact hn)
      rw [hvc k] at hl
      exact hl)
  choose C hC hCs hC0 hC1 hCnorm hCimage using hcap
  have hshape (k) (x : S) (hx : x ∈ Set.range (C k)) :
      (F.E k x 0=v k 0 ∧ v k 1≤F.E k x 1) ∨ (v k 0≤F.E k x 0 ∧ F.E k x 1=v k 1) :=
    (hlocal k x (hCs k hx).1 (by rw [hvc k]; exact (hCnorm k x hx).le)).mp (hCs k hx).2
  have hcounts (k) := source_translated_corner_contact_bounds a b (F.E k) (Set.range (C k))
    (fun _ hx=>(hCs k hx).1) (v k) (hvn k).1 (hvn k).2
    (F.target_axis k) (F.current_axis k) (hshape k)
  let U : Set S := (closure (F.E false).source ∪ closure (F.E true).source)ᶜ
  have hU : IsOpen U := (isClosed_closure.union isClosed_closure).isOpen_compl
  have hUR : source_surgery_retained_crossings B i ⊆ U := by
    intro x hx
    rintro (hh | hh)
    · exact Set.disjoint_left.mp (F.retained_disjoint false) hh hx
    · exact Set.disjoint_left.mp (F.retained_disjoint true) hh hx
  have hUout (x : S) (hx : x ∈ U) : x ∉ (F.E false).source ∪ (F.E true).source := by
    rintro (hh | hh)
    · exact hx (Or.inl (subset_closure hh))
    · exact hx (Or.inr (subset_closure hh))
  have hUtrace (x : S) (hx : x ∈ U) : x ∈ d.image ↔ x ∈ (B.boundary i).image := by
    rw [hd]
    exact source_supported_curve_image_outside H (B.boundary i).image
      ((F.E false).source ∪ (F.E true).source) hfix x (hUout x hx)
  let V : Bool → Set S := fun k => (F.E k).source ∩ (F.E k) ⁻¹' {x : Plane | ‖x-v k‖<1/4}
  have hVo (k) : IsOpen (V k) := (F.E k).isOpen_inter_preimage (isOpen_lt (by fun_prop) continuous_const)
  have hCV (k) : Set.range (C k) ⊆ V k := fun x hx => ⟨(hCs k hx).1,by
    change ‖F.E k x-v k‖<1/4
    rw [hvc k]; exact hCnorm k x hx⟩
  refine ⟨{
    w:=w,z:=z,width_nonzero:=⟨hw,hz⟩,v:=v,displacement:=hvc,displacement_nonzero:=hvn,
    H:=H,d:=d,image:=hd,ambient:=hrel,fixed:=hfix,source_preserved:=hsource,affine:=hmove,local_trace:=hlocal,
    C:=C,embedding:=hC,subset:=hCs,first_port:=hC0,closing_port:=hC1,
    open_ball:=fun k x hx=> by rw [hvc k]; exact hCnorm k x hx,
    shape:=hshape,caps_disjoint:=?_,start_avoids_target:=(hcounts false).2.2.2.2.1 hv0,
    start_avoids_current:=(hcounts false).2.2.2.2.2 hv1,
    target_finite:=fun k=>(hcounts k).1,current_finite:=fun k=>(hcounts k).2.1,
    target_budget:=fun k=>(hcounts k).2.2.1,current_budget:=fun k=>(hcounts k).2.2.2.1,
    target_crosses:=?_,current_crosses:=?_,U:=U,remote_open:=hU,retained_subset:=hUR,
    remote_fixed:=fun t x hx=>hfix t x (hUout x hx),remote_trace:=hUtrace,
    retained_crosses:=fun p hp=>source_crossing_transfer_local_trace
      (source_raw_branch_retained_crossings D B ht i p hp) U hU (hUR hp) hUtrace
  },?_,hfar,hdisp⟩
  · exact (F.disjoint.mono subset_closure subset_closure).mono
      (fun _ hx=>(hCs false hx).1) (fun _ hx=>(hCs true hx).1)
  · intro k p hp
    exact source_translated_corner_vertical_crossing a d (F.E k) (V k) (hVo k)
      (fun _ hx=>hx.1) (v k) (hvn k).1 (F.target_axis k)
      (fun x hx=>hlocal k x hx.1 hx.2.le) p ⟨⟨hCV k hp.1,(hCs k hp.1).2⟩,hp.2⟩
  · intro k p hp
    exact source_translated_corner_horizontal_crossing b d (F.E k) (V k) (hVo k)
      (fun _ hx=>hx.1) (v k) (hvn k).2 (F.current_axis k)
      (fun x hx=>hlocal k x hx.1 hx.2.le) p ⟨⟨hCV k hp.1,(hCs k hp.1).2⟩,hp.2⟩

  · intro k
    exact (hv k).trans_le (min_le_left _ _)
end CurveComplex

#print axioms CurveComplex.source_framed_first_return_caps_with_displacement
