import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnAttachedCaps
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualInitialAxisPortImage
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualInternalAxisPortAccess
set_option maxHeartbeats 3000000
namespace CurveComplex
open Set Topology Schoenflies
/-- Produce the ordered ACTUAL original closing-arc parameters whose whole
ambient translate is the two selected nonzero whole-strip ports. -/
theorem source_first_return_actual_old_closing_ports
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (i : Bool)
    (F : SourceFirstReturnFramedStrips D B i) :
    ∃ r : ℝ, 0<r ∧ ∀ A : SourceFirstReturnAttachedCaps F,
      (∀ k, ‖A.v k‖<r) → ∃ u : Bool → Interval,
        (u false:ℝ)<u true ∧ ∀ k,
        0<(u k:ℝ) ∧ (u k:ℝ)<1 ∧
        |(u k:ℝ)-(F.θg k:ℝ)|<F.ηg k ∧
        (B.closing i) (u k) ∈ (F.E k).source ∧
        F.E k ((B.closing i) (u k))=Plane.mk (F.E k ((B.closing i) (F.θg k)) 0-A.v k 0) 0 ∧
        A.H.finalMap ((B.closing i) (u k))=F.M (F.θg k,A.z) := by
  have hHorizontalAccess
      (f : C(Interval,S)) (hf : IsEmbedding f)
      (E : OpenPartialHomeomorph S Plane) (θ : Interval) (η : ℝ)
      (hθ : 0<(θ:ℝ) ∧ (θ:ℝ)<1) (hη : 0<η)
      (hlocal : ∀ u : Interval, |(u:ℝ)-(θ:ℝ)|<η →
        f u ∈ E.source ∧ E (f u) 1=0) :
      ∃ r : ℝ, 0<r ∧ ∀ y : ℝ, |y-E (f θ) 0|<r →
        ∃ u : Interval, 0<(u:ℝ) ∧ (u:ℝ)<1 ∧
          |(u:ℝ)-(θ:ℝ)|<η ∧ E (f u)=Plane.mk y 0 := by
    let J : Plane ≃ₜ Plane := {
      toEquiv := {
        toFun := fun x=>Plane.mk (x 1) (x 0)
        invFun := fun x=>Plane.mk (x 1) (x 0)
        left_inv := by intro x; ext j; fin_cases j <;> rfl
        right_inv := by intro x; ext j; fin_cases j <;> rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let G : OpenPartialHomeomorph S Plane := E.trans J.toOpenPartialHomeomorph
    have hGs : G.source=E.source := by simp [G]
    have hg (u : Interval) (hu : |(u:ℝ)-(θ:ℝ)|<η) :
        f u ∈ G.source ∧ G (f u) 0=0 :=
      ⟨hGs.symm ▸ (hlocal u hu).1,(hlocal u hu).2⟩
    obtain ⟨r,hr,haccess⟩ := source_internal_axis_port_coordinate_access f hf G θ η hθ hη hg
    refine ⟨r,hr,?_⟩
    intro y hy
    obtain ⟨u,hu0,hu1,hunear,hucoord⟩ := haccess y hy
    refine ⟨u,hu0,hu1,hunear,?_⟩
    have h0 := congrArg (fun q : Plane=>q 0) hucoord
    have h1 := congrArg (fun q : Plane=>q 1) hucoord
    change E (f u) 1=0 at h0
    change E (f u) 0=y at h1
    ext j
    fin_cases j
    · exact h1
    · exact h0
  classical
  let gap : ℝ := (F.θg true:ℝ)-(F.θg false:ℝ)
  have hgap : 0<gap := sub_pos.mpr F.closing_ports_order
  let δ : Bool → ℝ := fun k=>min (F.ηg k) (gap/4)
  have hδ (k) : 0<δ k := lt_min (F.corner_positive k).2.2.2 (div_pos hgap (by norm_num))
  have hlocal (k) (u : Interval) (hu : |(u:ℝ)-(F.θg k:ℝ)|<δ k) :
      (B.closing i) u ∈ (F.E k).source ∧ F.E k ((B.closing i) u) 1=0 := by
    have hh := F.closing_framing k u ⟨0,by norm_num⟩ (hu.trans_le (min_le_left _ _))
    rw [F.closing_center] at hh
    have hxb : (B.closing i) u ∈ b.image := by
      rw [← B.closing_cover]
      cases i
      · exact Or.inl (Set.mem_range_self u)
      · exact Or.inr (Set.mem_range_self u)
    exact ⟨hh.1,(F.current_axis k _ hh.1).mp hxb⟩
  choose rk hrk haccess using fun k=>hHorizontalAccess (B.closing i) (B.closing_embedded i) (F.E k) (F.θg k)
    (δ k) (F.θg_internal k) (hδ k) (hlocal k)
  let R : Bool → ℝ := fun k=>min (rk k) (F.E k ((B.closing i) (F.θg k)) 0/2)
  have hR (k) : 0<R k := lt_min (hrk k) (div_pos (F.closing_height k).1 (by norm_num))
  let r : ℝ := min (R false) (R true)
  have hr : 0<r := lt_min (hR false) (hR true)
  have hrR (k : Bool) : r≤R k := by cases k; exact min_le_left _ _; exact min_le_right _ _
  refine ⟨r,hr,?_⟩
  intro A hv
  have hcoordsmall (k) : |A.v k 0|<R k := by
    have hc : |A.v k 0|≤‖A.v k‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A.v k) 0
    exact hc.trans_lt ((hv k).trans_le (hrR k))
  have hpoints (k) : ∃ u : Interval,
      0<(u:ℝ) ∧ (u:ℝ)<1 ∧ |(u:ℝ)-(F.θg k:ℝ)|<δ k ∧
      (B.closing i) u ∈ (F.E k).source ∧
      F.E k ((B.closing i) u)=Plane.mk (F.E k ((B.closing i) (F.θg k)) 0-A.v k 0) 0 ∧
      A.H.finalMap ((B.closing i) u)=F.M (F.θg k,A.z) := by
    let y : ℝ := F.E k ((B.closing i) (F.θg k)) 0-A.v k 0
    have hy : |y-F.E k ((B.closing i) (F.θg k)) 0|<rk k := by
      have he : y-F.E k ((B.closing i) (F.θg k)) 0= -A.v k 0 := by dsimp [y]; ring
      rw [he,abs_neg]
      exact (hcoordsmall k).trans_le (min_le_left _ _)
    obtain ⟨u,hu0,hu1,hunear,hucoord⟩ := haccess k y hy
    have huE := (hlocal k u hunear).1
    have hypositive : 0<y := by
      have hvh := (hcoordsmall k).trans_le (min_le_right _ _)
      have hupper := le_abs_self (A.v k 0)
      dsimp [y]
      linarith [(F.closing_height k).1]
    have hynorm : ‖F.E k ((B.closing i) u)‖≤1/4 := by
      rw [hucoord]
      simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
      rw [Real.sqrt_sq_eq_abs,abs_of_pos hypositive]
      have hvh := (hcoordsmall k).trans_le (min_le_right _ _)
      have hlower := neg_le_abs (A.v k 0)
      dsimp [y]
      linarith [(F.closing_height k).2]
    obtain ⟨hportE,hportcoord⟩ := F.closing_framing k (F.θg k) A.z
      (by simpa using (F.corner_positive k).2.2.2)
    have hv1 : A.v k 1=F.β k*(A.z:ℝ) := by
      have hh := congrArg (fun q : Plane=>q 1) (A.displacement k)
      exact hh
    have hport : A.H.finalMap ((B.closing i) u)=F.M (F.θg k,A.z) := by
      apply (F.E k).injOn (A.source_preserved k ⟨1,by norm_num⟩ _ huE) hportE
      rw [A.affine k ⟨1,by norm_num⟩ _ huE hynorm,hucoord,hportcoord]
      ext j
      fin_cases j
      · change y+1*A.v k 0=F.E k ((B.closing i) (F.θg k)) 0
        dsimp [y]
        ring
      · change 0+1*A.v k 1=F.β k*(A.z:ℝ)
        simpa only [zero_add,one_mul] using hv1
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

#print axioms CurveComplex.source_first_return_actual_old_closing_ports
