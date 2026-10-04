import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualLocalCapMiddleIncidence
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualTranslatedCapOpenLocalization
namespace CurveComplex
open Set Topology Schoenflies

def source_first_middle_far_parameters
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    {D : SourceFirstReturnBoundary a b} {B : SourceTwoSurgeryBranches D} {i : Bool}
    (F : SourceFirstReturnFramedStrips D B i) (k : Bool) : Set Interval :=
  Set.Icc (F.θf false) (F.θf true) ∩ {u | F.ηf k/2≤|(u:ℝ)-(F.θf k:ℝ)|}

def source_closing_middle_far_parameters
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    {D : SourceFirstReturnBoundary a b} {B : SourceTwoSurgeryBranches D} {i : Bool}
    (F : SourceFirstReturnFramedStrips D B i) (k : Bool) : Set Interval :=
  Set.Icc (F.θg false) (F.θg true) ∩ {u | F.ηg k/2≤|(u:ℝ)-(F.θg k:ℝ)|}

/-- Actual open cap neighborhoods have CLOSED supports avoiding the entire
remote middle center arcs. The original raw cap is constructed and its source
prefix/suffix is decoded before normal separation and radius selection. -/
theorem source_raw_caps_remote_middle_separation
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (i : Bool)
    (F : SourceFirstReturnFramedStrips D B i) :
    ∃ W : Bool → Set S, (∀ k, IsOpen (W k)) ∧
      (∀ k x, x ∈ (F.E k).source →
        (F.E k x 0=0 ∧ 0≤F.E k x 1 ∧ F.E k x 1≤F.E k (D.first (F.θf k)) 1) ∨
        (0≤F.E k x 0 ∧ F.E k x 0≤F.E k (B.closing i (F.θg k)) 0 ∧ F.E k x 1=0) → x ∈ W k) ∧
      (∀ k u, u ∈ source_first_middle_far_parameters F k → D.first u ∉ closure (W k)) ∧
      (∀ k u, u ∈ source_closing_middle_far_parameters F k → B.closing i u ∉ closure (W k)) ∧
      ∃ r : Bool → ℝ, (∀ k, 0<r k) ∧
        ∀ k (v : Plane), ‖v‖<r k → ∀ x ∈ (F.E k).source,
          (F.E k x 0=v 0 ∧ v 1≤F.E k x 1 ∧ F.E k x 1≤F.E k (D.first (F.θf k)) 1) ∨
          (v 0≤F.E k x 0 ∧ F.E k x 0≤F.E k (B.closing i (F.θg k)) 0 ∧ F.E k x 1=v 1) → x ∈ W k := by
  classical
  have hproduce (k : Bool) : ∃ W : Set S, IsOpen W ∧
      (∀ x, x ∈ (F.E k).source →
        (F.E k x 0=0 ∧ 0≤F.E k x 1 ∧ F.E k x 1≤F.E k (D.first (F.θf k)) 1) ∨
        (0≤F.E k x 0 ∧ F.E k x 0≤F.E k (B.closing i (F.θg k)) 0 ∧ F.E k x 1=0) → x ∈ W) ∧
      (∀ u ∈ source_first_middle_far_parameters F k, D.first u ∉ closure W) ∧
      (∀ u ∈ source_closing_middle_far_parameters F k, B.closing i u ∉ closure W) := by
    obtain ⟨c,hc,hcs,hcnorm,hc0,hc1,hcv,hcimage⟩ :=
      source_translated_corner_embedded_cap_with_heights (B.boundary i) (F.E k) (F.square k)
        (F.E k (D.first (F.θf k)) 1) (F.E k (B.closing i (F.θg k)) 0)
        (F.first_height k) (F.closing_height k) 0
        (by rw [norm_zero]; exact div_pos (lt_min (F.first_height k).1 (F.closing_height k).1) (by norm_num))
        (by intro x hx _hn; exact F.branch_trace k x hx)
    have hfirsteq (u : Interval) (hu : u ∈ Set.Icc (F.θf false) (F.θf true))
        (hx : D.first u ∈ Set.range c) : u=F.θf k := by
      have hs := (hcs hx).1
      have haxis := (F.target_axis k _ hs).mp (D.first_subset (Set.mem_range_self u))
      have hshape := hcimage ▸ hx
      have hlong : 0≤F.E k (D.first u) 1 ∧ F.E k (D.first u) 1≤F.E k (D.first (F.θf k)) 1 := by
        rcases hshape with hh|hh
        · exact hh.2.2
        · have he : F.E k (D.first u) 1=0 := hh.2.2.2
          rw [he]
          exact ⟨le_rfl,(F.first_height k).1.le⟩
      have hp := (source_first_return_first_ports_exact_source_order D B i F k u).mpr
        ⟨hs,haxis,hlong.1,hlong.2⟩
      cases k
      · exact le_antisymm hp hu.1
      · exact le_antisymm hu.2 hp
    have hclosingeq (u : Interval) (hu : u ∈ Set.Icc (F.θg false) (F.θg true))
        (hx : B.closing i u ∈ Set.range c) : u=F.θg k := by
      have hs := (hcs hx).1
      have hcurrent : B.closing i u ∈ b.image := by
        rw [← B.closing_cover]
        cases i
        · exact Or.inl (Set.mem_range_self u)
        · exact Or.inr (Set.mem_range_self u)
      have haxis := (F.current_axis k _ hs).mp hcurrent
      have hshape := hcimage ▸ hx
      have hlong : 0≤F.E k (B.closing i u) 0 ∧ F.E k (B.closing i u) 0≤F.E k (B.closing i (F.θg k)) 0 := by
        rcases hshape with hh|hh
        · have he : F.E k (B.closing i u) 0=0 := hh.2.1
          rw [he]
          exact ⟨le_rfl,(F.closing_height k).1.le⟩
        · exact ⟨hh.2.1,hh.2.2.1⟩
      have hp := (source_first_return_closing_ports_exact_source_order D B i F k u).mpr
        ⟨hs,haxis,hlong.1,hlong.2⟩
      cases k
      · exact le_antisymm hp hu.1
      · exact le_antisymm hu.2 hp
    let K := D.first '' source_first_middle_far_parameters F k ∪ B.closing i '' source_closing_middle_far_parameters F k
    have hKc : IsCompact K :=
      ((isClosed_Icc.inter (isClosed_le continuous_const (by fun_prop))).isCompact.image D.first.continuous).union
      ((isClosed_Icc.inter (isClosed_le continuous_const (by fun_prop))).isCompact.image (B.closing i).continuous)
    have hcapK : Set.range c ⊆ Kᶜ := by
      intro x hx
      rintro (⟨u,hu,rfl⟩|⟨u,hu,rfl⟩)
      · have he := hfirsteq u hu.1 hx
        have hh : F.ηf k/2≤|(u:ℝ)-(F.θf k:ℝ)| := hu.2
        rw [he,sub_self,abs_zero] at hh
        linarith [(F.corner_positive k).2.2.1]
      · have he := hclosingeq u hu.1 hx
        have hh : F.ηg k/2≤|(u:ℝ)-(F.θg k:ℝ)| := hu.2
        rw [he,sub_self,abs_zero] at hh
        linarith [(F.corner_positive k).2.2.2]
    obtain ⟨W,hW,hcW,hclW⟩ := normal_exists_closure_subset
      (isCompact_range c.continuous).isClosed hKc.isClosed.isOpen_compl hcapK
    refine ⟨W,hW,?_,?_,?_⟩
    · intro x hx hshape
      apply hcW
      rw [hcimage]
      exact hshape.elim (fun hh=>Or.inl ⟨hx,hh⟩) (fun hh=>Or.inr ⟨hx,hh⟩)
    · intro u hu hmem
      exact hclW hmem (Or.inl ⟨u,hu,rfl⟩)
    · intro u hu hmem
      exact hclW hmem (Or.inr ⟨u,hu,rfl⟩)
  choose W hW hlegs hfirst hclosing using hproduce
  choose r hr hr32 hrh hsmall using fun k=>source_translated_truncated_corner_trace_in_open (F.E k) (F.square k)
    (F.E k (D.first (F.θf k)) 1) (F.E k (B.closing i (F.θg k)) 0)
    (F.first_height k) (F.closing_height k) (W k) (hW k) (hlegs k)
  exact ⟨W,hW,hlegs,hfirst,hclosing,r,hr,hsmall⟩
end CurveComplex
#print axioms CurveComplex.source_raw_caps_remote_middle_separation
