import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnAttachedCaps
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualInitialAxisPortImage
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualInternalAxisPortAccess
set_option maxHeartbeats 3000000
namespace CurveComplex
open Set Topology Schoenflies
/-- Produce the ordered ACTUAL original first-arc parameters whose whole
ambient translate is the two selected nonzero whole-strip ports. -/
theorem source_first_return_actual_old_first_ports
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (i : Bool)
    (F : SourceFirstReturnFramedStrips D B i) :
    ∃ r : ℝ, 0<r ∧ ∀ A : SourceFirstReturnAttachedCaps F,
      (∀ k, ‖A.v k‖<r) → ∃ u : Bool → Interval,
        (u false:ℝ)<u true ∧ ∀ k,
        0<(u k:ℝ) ∧ (u k:ℝ)<1 ∧
        |(u k:ℝ)-(F.θf k:ℝ)|<F.ηf k ∧
        D.first (u k) ∈ (F.E k).source ∧
        F.E k (D.first (u k))=Plane.mk 0 (F.E k (D.first (F.θf k)) 1-A.v k 1) ∧
        A.H.finalMap (D.first (u k))=F.N (F.θf k,A.w) := by
  classical
  let gap : ℝ := (F.θf true:ℝ)-(F.θf false:ℝ)
  have hgap : 0<gap := sub_pos.mpr F.first_ports_order
  let δ : Bool → ℝ := fun k=>min (F.ηf k) (gap/4)
  have hδ (k) : 0<δ k := lt_min (F.corner_positive k).2.2.1 (div_pos hgap (by norm_num))
  have hlocal (k) (u : Interval) (hu : |(u:ℝ)-(F.θf k:ℝ)|<δ k) :
      D.first u ∈ (F.E k).source ∧ F.E k (D.first u) 0=0 := by
    have hh := F.first_framing k u ⟨0,by norm_num⟩ (hu.trans_le (min_le_left _ _))
    rw [F.first_center] at hh
    exact ⟨hh.1,(F.target_axis k _ hh.1).mp (D.first_subset (Set.mem_range_self u))⟩
  choose rk hrk haccess using fun k=>source_internal_axis_port_coordinate_access D.first D.first_embedded (F.E k) (F.θf k)
    (δ k) (F.θf_internal k) (hδ k) (hlocal k)
  let R : Bool → ℝ := fun k=>min (rk k) (F.E k (D.first (F.θf k)) 1/2)
  have hR (k) : 0<R k := lt_min (hrk k) (div_pos (F.first_height k).1 (by norm_num))
  let r : ℝ := min (R false) (R true)
  have hr : 0<r := lt_min (hR false) (hR true)
  have hrR (k : Bool) : r≤R k := by cases k; exact min_le_left _ _; exact min_le_right _ _
  refine ⟨r,hr,?_⟩
  intro A hv
  have hcoordsmall (k) : |A.v k 1|<R k := by
    have hc : |A.v k 1|≤‖A.v k‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A.v k) 1
    exact hc.trans_lt ((hv k).trans_le (hrR k))
  have hpoints (k) : ∃ u : Interval,
      0<(u:ℝ) ∧ (u:ℝ)<1 ∧ |(u:ℝ)-(F.θf k:ℝ)|<δ k ∧
      D.first u ∈ (F.E k).source ∧
      F.E k (D.first u)=Plane.mk 0 (F.E k (D.first (F.θf k)) 1-A.v k 1) ∧
      A.H.finalMap (D.first u)=F.N (F.θf k,A.w) := by
    let y : ℝ := F.E k (D.first (F.θf k)) 1-A.v k 1
    have hy : |y-F.E k (D.first (F.θf k)) 1|<rk k := by
      have he : y-F.E k (D.first (F.θf k)) 1= -A.v k 1 := by dsimp [y]; ring
      rw [he,abs_neg]
      exact (hcoordsmall k).trans_le (min_le_left _ _)
    obtain ⟨u,hu0,hu1,hunear,hucoord⟩ := haccess k y hy
    have huE := (hlocal k u hunear).1
    have hypositive : 0<y := by
      have hvh := (hcoordsmall k).trans_le (min_le_right _ _)
      have hupper := le_abs_self (A.v k 1)
      dsimp [y]
      linarith [(F.first_height k).1]
    have hynorm : ‖F.E k (D.first u)‖≤1/4 := by
      rw [hucoord]
      simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
      rw [Real.sqrt_sq_eq_abs,abs_of_pos hypositive]
      have hvh := (hcoordsmall k).trans_le (min_le_right _ _)
      have hlower := neg_le_abs (A.v k 1)
      dsimp [y]
      linarith [(F.first_height k).2]
    obtain ⟨hportE,hportcoord⟩ := F.first_framing k (F.θf k) A.w
      (by simpa using (F.corner_positive k).2.2.1)
    have hv0 : A.v k 0=F.α k*(A.w:ℝ) := by
      have hh := congrArg (fun q : Plane=>q 0) (A.displacement k)
      exact hh
    have hport : A.H.finalMap (D.first u)=F.N (F.θf k,A.w) := by
      apply (F.E k).injOn (A.source_preserved k ⟨1,by norm_num⟩ _ huE) hportE
      rw [A.affine k ⟨1,by norm_num⟩ _ huE hynorm,hucoord,hportcoord]
      ext j
      fin_cases j
      · change 0+1*A.v k 0=F.α k*(A.w:ℝ)
        simpa only [zero_add,one_mul] using hv0
      · change y+1*A.v k 1=F.E k (D.first (F.θf k)) 1
        dsimp [y]
        ring
    exact ⟨u,hu0,hu1,hunear,huE,hucoord,hport⟩
  choose u hu0 hu1 hunear huE hucoord huport using hpoints
  refine ⟨u,?_,?_⟩
  · have hf := (hunear false).trans_le (min_le_right _ _)
    have ht := (hunear true).trans_le (min_le_right _ _)
    rw [abs_lt] at hf ht
    dsimp [gap] at hf ht
    linarith
  · intro k
    exact ⟨hu0 k,hu1 k,(hunear k).trans_le (min_le_left _ _),huE k,hucoord k,huport k⟩
end CurveComplex

#print axioms CurveComplex.source_first_return_actual_old_first_ports
