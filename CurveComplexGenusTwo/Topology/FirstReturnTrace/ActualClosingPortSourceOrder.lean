import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualAxisSegmentSourcePrefix
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnFramedStrips
namespace CurveComplex
open Set Topology Schoenflies
/-- Actual first-return corner ports delimit their entire original source
prefix/suffix. The positive chart segment is decoded from the raw L trace;
no prefix chart-containment or source-order assumption is supplied. -/
theorem source_first_return_closing_ports_exact_source_order
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (i : Bool)
    (F : SourceFirstReturnFramedStrips D B i) :
    ∀ k (t : Interval), (if k then F.θg k≤t else t≤F.θg k) ↔
      B.closing i t ∈ (F.E k).source ∧ F.E k (B.closing i t) 1=0 ∧
        0≤F.E k (B.closing i t) 0 ∧ F.E k (B.closing i t) 0≤F.E k (B.closing i (F.θg k)) 0 := by
  classical

  let J : Plane ≃ₜ Plane := {
    toEquiv := {
      toFun := fun x=>Plane.mk (x 1) (x 0)
      invFun := fun x=>Plane.mk (x 1) (x 0)
      left_inv := by intro x; ext j; fin_cases j <;> rfl
      right_inv := by intro x; ext j; fin_cases j <;> rfl }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let G : Bool → OpenPartialHomeomorph S Plane := fun k=>(F.E k).trans J.toOpenPartialHomeomorph
  have hGs (k) : (G k).source=(F.E k).source := by simp [G]
  have hpoint (k) : (if k then D.finish else D.start) ∈ (G k).source ∧ G k (if k then D.finish else D.start)=0 := by
    refine ⟨(hGs k).symm ▸ (F.point k).1,?_⟩
    change J (F.E k (if k then D.finish else D.start))=0
    rw [(F.point k).2]
    ext j
    fin_cases j <;> rfl
  have hsquare (k) : Plane.closedSquare 0 1 ⊆ (G k).target := by
    intro x hx
    have hj : J.symm x ∈ (F.E k).target := F.square k (by
      rw [mem_closedSquare_zero_one] at hx ⊢
      change max |x 1| |x 0|≤1
      rw [max_comm]
      exact hx)
    have hp : (F.E k).symm (J.symm x) ∈ (G k).source := (hGs k).symm ▸ (F.E k).map_target hj
    have he : G k ((F.E k).symm (J.symm x))=x := by
      change J (F.E k ((F.E k).symm (J.symm x)))=x
      rw [(F.E k).right_inv hj,J.apply_symm_apply]
    exact he ▸ (G k).map_source hp
  have hcurrentaxis (k) (x : S) (hx : x ∈ (G k).source) : x ∈ b.image ↔ G k x 0=0 :=
    F.current_axis k x ((hGs k) ▸ hx)
  have htargetaxis (k) (x : S) (hx : x ∈ (G k).source) : x ∈ a.image ↔ G k x 1=0 :=
    F.target_axis k x ((hGs k) ▸ hx)
  have hbranch (k) (x : S) (hx : x ∈ (G k).source) : x ∈ (B.boundary i).image ↔
      (G k x 0=0 ∧ 0≤G k x 1) ∨ (0≤G k x 0 ∧ G k x 1=0) := by
    change x ∈ (B.boundary i).image ↔
      (F.E k x 1=0 ∧ 0≤F.E k x 0) ∨ (0≤F.E k x 1 ∧ F.E k x 0=0)
    rw [F.branch_trace k x ((hGs k) ▸ hx)]
    tauto
  let rev : C(Interval,Interval) := ⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩
  let f : Bool → C(Interval,S) := fun k=>if k then (B.closing i).comp rev else B.closing i
  let u : Bool → Interval := fun k=>if k then unitInterval.symmHomeomorph (F.θg k) else F.θg k
  let v : Bool → Interval → Interval := fun k t=>if k then unitInterval.symmHomeomorph t else t
  have hf (k) : IsEmbedding (f k) := by
    cases k
    · exact (B.closing_embedded i)
    · exact (B.closing_embedded i).comp unitInterval.symmHomeomorph.isEmbedding
  have hfrange (k) : Set.range (f k)=Set.range (B.closing i) := by
    cases k
    · rfl
    · exact unitInterval.symmHomeomorph.surjective.range_comp (B.closing i)
  have hf0 (k) : f k 0=(if k then D.finish else D.start) := by
    cases k <;> simp [f,rev,B.closing_zero,B.closing_one]
  have hfu (k) : f k (u k)=B.closing i (F.θg k) := by
    cases k
    · rfl
    · change B.closing i (unitInterval.symmHomeomorph (unitInterval.symmHomeomorph (F.θg true)))=B.closing i (F.θg true)
      congr 1
      apply Subtype.ext
      change 1-(1-(F.θg true:ℝ))=(F.θg true:ℝ)
      ring
  have hfv (k) (t : Interval) : f k (v k t)=B.closing i t := by
    cases k
    · rfl
    · change B.closing i (unitInterval.symmHomeomorph (unitInterval.symmHomeomorph t))=B.closing i t
      congr 1
      apply Subtype.ext
      change 1-(1-(t:ℝ))=(t:ℝ)
      ring
  have hvorder (k) (t : Interval) : v k t≤u k ↔ (if k then F.θg k≤t else t≤F.θg k) := by
    cases k
    · rfl
    · change (1-(t:ℝ)≤1-(F.θg true:ℝ)) ↔ (F.θg true:ℝ)≤(t:ℝ)
      constructor <;> intro h <;> linarith
  have hport (k) : B.closing i (F.θg k) ∈ (G k).source := by
    have hh := (F.closing_framing k (F.θg k) ⟨0,by norm_num⟩
      (by simpa using (F.corner_positive k).2.2.2)).1
    rw [F.closing_center] at hh
    exact (hGs k).symm ▸ hh
  have hsegment (k) (x : S) (hx : x ∈ (G k).source) (hx0 : G k x 0=0)
      (hxlo : 0≤G k x 1) (_hxhi : G k x 1≤G k (B.closing i (F.θg k)) 1) : x ∈ Set.range (f k) := by
    rw [hfrange]
    by_cases he : G k x 1=0
    · have hEx : G k x=G k (if k then D.finish else D.start) := by
        rw [(hpoint k).2]
        ext j
        fin_cases j
        · exact hx0
        · exact he
      have hh := (G k).injOn hx (hpoint k).1 hEx
      rw [hh]
      cases k
      · exact ⟨0,B.closing_zero i⟩
      · exact ⟨1,B.closing_one i⟩
    · have hraw : x ∈ (B.boundary i).image := (hbranch k x hx).mpr (Or.inl ⟨hx0,hxlo⟩)
      rw [B.boundary_image] at hraw
      rcases hraw with hfirst|hclose
      · have hxa : x ∈ a.image := D.first_subset hfirst
        exact (he ((htargetaxis k x hx).mp hxa)).elim
      · exact hclose
  have hprefix (k) := source_axis_segment_is_initial_source_prefix (f k) (hf k) (G k) (u k)
    (by rw [hf0]; exact (hpoint k).1) (by rw [hf0]; exact (hpoint k).2)
    (by rw [hfu]; exact hport k)
    (by rw [hfu]; exact (hcurrentaxis k _ (hport k)).mp (by
      rw [← B.closing_cover]
      cases i
      · exact Or.inl (Set.mem_range_self _)
      · exact Or.inr (Set.mem_range_self _)))
    (by rw [hfu]; exact F.closing_height k) (hsquare k)
    (by intro x hx hx0 hxlo hxhi; rw [hfu] at hxhi; exact hsegment k x hx hx0 hxlo hxhi)
  intro k t
  constructor
  · intro ht
    have hx : f k (v k t) ∈ (f k) '' Set.Icc (0:Interval) (u k) :=
      ⟨v k t,⟨(v k t).property.1,(hvorder k t).mpr ht⟩,rfl⟩
    rw [(hprefix k).1] at hx
    rw [hfu k,hfv k t] at hx
    change B.closing i t ∈ (G k).source ∧ G k (B.closing i t) 0=0 ∧
      0≤G k (B.closing i t) 1 ∧ G k (B.closing i t) 1≤G k (B.closing i (F.θg k)) 1 at hx
    exact ⟨(hGs k) ▸ hx.1,hx.2⟩
  · intro ht
    apply (hvorder k t).mp
    apply (hprefix k).2.2 (v k t)
    · rw [hfv]; exact (hGs k).symm ▸ ht.1
    · rw [hfv]; exact ht.2.1
    · rw [hfv]; exact ht.2.2.1
    · rw [hfv,hfu]; exact ht.2.2.2
end CurveComplex
#print axioms CurveComplex.source_first_return_closing_ports_exact_source_order
