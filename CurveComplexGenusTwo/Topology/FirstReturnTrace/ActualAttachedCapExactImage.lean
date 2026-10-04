import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualAttachedCapHeightBounds
namespace CurveComplex
open Set Topology Schoenflies
/-- Recover the ENTIRE exact truncated cap image from the original actual
attached-cap record; no reverse cap-image inclusion is a premise. -/
theorem source_attached_cap_truncation_exact_image
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {D : SourceFirstReturnBoundary a b}
    {B : SourceTwoSurgeryBranches D} {i : Bool}
    {F : SourceFirstReturnFramedStrips D B i}
    (A : SourceFirstReturnAttachedCaps F) :
    ∀ k, Set.range (A.C k) = {x : S | x ∈ (F.E k).source ∧
      ((F.E k x 0=A.v k 0 ∧ A.v k 1≤F.E k x 1 ∧
          F.E k x 1≤F.E k (D.first (F.θf k)) 1) ∨
       (A.v k 0≤F.E k x 0 ∧ F.E k x 0≤F.E k (B.closing i (F.θg k)) 0 ∧
          F.E k x 1=A.v k 1))} := by
  intro k
  let E := F.E k
  let c := A.C k
  let v := A.v k
  let z : C(Interval,ℝ) := ⟨fun t=>(E (c t) 0-v 0)-(E (c t) 1-v 1),by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hE : ContinuousAt (fun t : Interval=>E (c t)) t :=
      (E.continuousAt (A.subset k (Set.mem_range_self t)).1).comp c.continuous.continuousAt
    have h0 : ContinuousAt (fun t : Interval=>E (c t) 0) t := (show Continuous (fun x : Plane=>x 0) by fun_prop).continuousAt.comp hE
    have h1 : ContinuousAt (fun t : Interval=>E (c t) 1) t := (show Continuous (fun x : Plane=>x 1) by fun_prop).continuousAt.comp hE
    exact (h0.sub continuousAt_const).sub (h1.sub continuousAt_const)⟩
  have hC0 : E (c 0)=Plane.mk (v 0) (E (D.first (F.θf k)) 1) := by
    rw [A.first_port]
    have hh := (F.first_framing k (F.θf k) A.w
      (by simpa using (F.corner_positive k).2.2.1)).2
    have hv : v 0=F.α k*(A.w:ℝ) := congrArg (fun q : Plane=>q 0) (A.displacement k)
    rw [hv]
    exact hh
  have hC1 : E (c 1)=Plane.mk (E (B.closing i (F.θg k)) 0) (v 1) := by
    rw [A.closing_port]
    have hh := (F.closing_framing k (F.θg k) A.z
      (by simpa using (F.corner_positive k).2.2.2)).2
    have hv : v 1=F.β k*(A.z:ℝ) := congrArg (fun q : Plane=>q 1) (A.displacement k)
    rw [hv]
    exact hh
  have hz0 : z 0=v 1-E (D.first (F.θf k)) 1 := by
    change (E (c 0) 0-v 0)-(E (c 0) 1-v 1)=_
    rw [hC0]
    change (v 0-v 0)-(E (D.first (F.θf k)) 1-v 1)=_
    ring
  have hz1 : z 1=E (B.closing i (F.θg k)) 0-v 0 := by
    change (E (c 1) 0-v 0)-(E (c 1) 1-v 1)=_
    rw [hC1]
    change (E (B.closing i (F.θg k)) 0-v 0)-(v 1-v 1)=_
    ring
  have hheight0 : v 1≤E (D.first (F.θf k)) 1 := by
    have hh := A.shape k (c 0) (Set.mem_range_self 0)
    change (E (c 0) 0=v 0 ∧ v 1≤E (c 0) 1) ∨ (v 0≤E (c 0) 0 ∧ E (c 0) 1=v 1) at hh
    rw [hC0] at hh
    rcases hh with hh|hh
    · exact hh.2
    · exact hh.2.ge
  have hheight1 : v 0≤E (B.closing i (F.θg k)) 0 := by
    have hh := A.shape k (c 1) (Set.mem_range_self 1)
    change (E (c 1) 0=v 0 ∧ v 1≤E (c 1) 1) ∨ (v 0≤E (c 1) 0 ∧ E (c 1) 1=v 1) at hh
    rw [hC1] at hh
    rcases hh with hh|hh
    · exact hh.1.ge
    · exact hh.1
  apply Set.ext
  intro x
  constructor
  · intro hx
    exact ⟨(A.subset k hx).1,source_attached_cap_truncation_heights A k x hx⟩
  · intro hx
    let l : ℝ := (E x 0-v 0)-(E x 1-v 1)
    have hbetween : l ∈ Set.Icc (z 0) (z 1) := by
      rw [hz0,hz1]
      change v 1-E (D.first (F.θf k)) 1≤l ∧ l≤E (B.closing i (F.θg k)) 0-v 0
      rcases hx.2 with hxv|hxh
      · change E x 0=v 0 ∧ v 1≤E x 1 ∧ E x 1≤E (D.first (F.θf k)) 1 at hxv
        dsimp [l]
        constructor <;> linarith [hxv.1,hxv.2.1,hxv.2.2]
      · change v 0≤E x 0 ∧ E x 0≤E (B.closing i (F.θg k)) 0 ∧ E x 1=v 1 at hxh
        dsimp [l]
        constructor <;> linarith [hxh.1,hxh.2.1,hxh.2.2]
    have hlimage : l ∈ z '' Set.Icc (0:Interval) 1 :=
      intermediate_value_Icc (by norm_num) z.continuous.continuousOn hbetween
    obtain ⟨t,_ht,he⟩ := hlimage
    have hct := A.shape k (c t) (Set.mem_range_self t)
    have hxs : (E x 0=v 0 ∧ v 1≤E x 1) ∨ (v 0≤E x 0 ∧ E x 1=v 1) := by
      rcases hx.2 with hxv|hxh
      · exact Or.inl ⟨hxv.1,hxv.2.1⟩
      · exact Or.inr ⟨hxh.1,hxh.2.2⟩
    have hEeq : E (c t)=E x := by
      change (E (c t) 0-v 0)-(E (c t) 1-v 1)=(E x 0-v 0)-(E x 1-v 1) at he
      change (E (c t) 0=v 0 ∧ v 1≤E (c t) 1) ∨ (v 0≤E (c t) 0 ∧ E (c t) 1=v 1) at hct
      ext j
      fin_cases j
      · change E (c t) 0=E x 0
        rcases hct with hh|hh <;> rcases hxs with hg|hg <;> linarith [hh.1,hh.2,hg.1,hg.2]
      · change E (c t) 1=E x 1
        rcases hct with hh|hh <;> rcases hxs with hg|hg <;> linarith [hh.1,hh.2,hg.1,hg.2]
    exact ⟨t,E.injOn (A.subset k (Set.mem_range_self t)).1 hx.1 hEeq⟩
end CurveComplex
