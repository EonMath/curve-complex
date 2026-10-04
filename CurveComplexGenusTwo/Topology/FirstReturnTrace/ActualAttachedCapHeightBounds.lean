import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnAttachedCaps
namespace CurveComplex
open Set Topology Schoenflies
/-- Derive the exact truncation heights of every attached cap from its actual
embedding, shifted L trace and endpoint attachment. No cap-image bound is an
input: the scalar coordinate on the L is forced strictly monotone. -/
theorem source_attached_cap_truncation_heights
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {D : SourceFirstReturnBoundary a b}
    {B : SourceTwoSurgeryBranches D} {i : Bool}
    {F : SourceFirstReturnFramedStrips D B i} (A : SourceFirstReturnAttachedCaps F) :
    ∀ k x, x ∈ Set.range (A.C k) →
      (F.E k x 0=A.v k 0 ∧ A.v k 1≤F.E k x 1 ∧ F.E k x 1≤F.E k (D.first (F.θf k)) 1) ∨
      (A.v k 0≤F.E k x 0 ∧ F.E k x 0≤F.E k (B.closing i (F.θg k)) 0 ∧ F.E k x 1=A.v k 1) := by
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
  have hzi : Function.Injective z := by
    intro s t he
    apply A.embedding k |>.injective
    apply E.injOn (A.subset k (Set.mem_range_self s)).1 (A.subset k (Set.mem_range_self t)).1
    have hs := A.shape k (c s) (Set.mem_range_self s)
    have ht := A.shape k (c t) (Set.mem_range_self t)
    change (E (c s) 0-v 0)-(E (c s) 1-v 1)=(E (c t) 0-v 0)-(E (c t) 1-v 1) at he
    change (E (c s) 0=v 0 ∧ v 1≤E (c s) 1) ∨ (v 0≤E (c s) 0 ∧ E (c s) 1=v 1) at hs
    change (E (c t) 0=v 0 ∧ v 1≤E (c t) 1) ∨ (v 0≤E (c t) 0 ∧ E (c t) 1=v 1) at ht
    ext j
    fin_cases j
    · change E (c s) 0=E (c t) 0
      rcases hs with hs|hs <;> rcases ht with ht|ht <;> linarith [hs.1,hs.2,ht.1,ht.2]
    · change E (c s) 1=E (c t) 1
      rcases hs with hs|hs <;> rcases ht with ht|ht <;> linarith [hs.1,hs.2,ht.1,ht.2]
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
  have hz01 : z 0<z 1 := lt_of_le_of_ne (by rw [hz0,hz1]; linarith)
    (fun hh=>by have he := hzi hh; norm_num at he)
  have hzm : StrictMono z := by
    rcases z.continuous.strictMono_of_inj_boundedOrder' hzi with hm|hm
    · exact hm
    · exact (not_lt_of_gt hz01 (hm (by norm_num : (0:Interval)<1))).elim
  rintro x ⟨t,rfl⟩
  have hlo := hzm.monotone (show (0:Interval)≤t from t.property.1)
  have hhi := hzm.monotone (show t≤(1:Interval) from t.property.2)
  rw [hz0] at hlo
  rw [hz1] at hhi
  change v 1-E (D.first (F.θf k)) 1≤(E (c t) 0-v 0)-(E (c t) 1-v 1) at hlo
  change (E (c t) 0-v 0)-(E (c t) 1-v 1)≤E (B.closing i (F.θg k)) 0-v 0 at hhi
  rcases A.shape k (c t) (Set.mem_range_self t) with hh|hh
  · have hx0 : E (c t) 0=v 0 := hh.1
    exact Or.inl ⟨hh.1,hh.2,by change E (c t) 1≤E (D.first (F.θf k)) 1; linarith⟩
  · have hx1 : E (c t) 1=v 1 := hh.2
    exact Or.inr ⟨hh.1,by change E (c t) 0≤E (B.closing i (F.θg k)) 0; linarith,hh.2⟩
end CurveComplex
#print axioms CurveComplex.source_attached_cap_truncation_heights
