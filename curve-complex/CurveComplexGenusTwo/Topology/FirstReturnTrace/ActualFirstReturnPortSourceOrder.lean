import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualAxisSegmentSourcePrefix
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnFramedStrips
namespace CurveComplex
open Set Topology Schoenflies
/-- Actual first-return corner ports delimit their entire original source
prefix/suffix. The positive chart segment is decoded from the raw L trace;
no prefix chart-containment or source-order assumption is supplied. -/
theorem source_first_return_first_ports_exact_source_order
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (i : Bool)
    (F : SourceFirstReturnFramedStrips D B i) :
    ∀ k (t : Interval), (if k then F.θf k≤t else t≤F.θf k) ↔
      D.first t ∈ (F.E k).source ∧ F.E k (D.first t) 0=0 ∧
        0≤F.E k (D.first t) 1 ∧ F.E k (D.first t) 1≤F.E k (D.first (F.θf k)) 1 := by
  classical
  let rev : C(Interval,Interval) := ⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩
  let f : Bool → C(Interval,S) := fun k=>if k then D.first.comp rev else D.first
  let u : Bool → Interval := fun k=>if k then unitInterval.symmHomeomorph (F.θf k) else F.θf k
  let v : Bool → Interval → Interval := fun k t=>if k then unitInterval.symmHomeomorph t else t
  have hf (k) : IsEmbedding (f k) := by
    cases k
    · exact D.first_embedded
    · exact D.first_embedded.comp unitInterval.symmHomeomorph.isEmbedding
  have hfrange (k) : Set.range (f k)=Set.range D.first := by
    cases k
    · rfl
    · exact unitInterval.symmHomeomorph.surjective.range_comp D.first
  have hf0 (k) : f k 0=(if k then D.finish else D.start) := by
    cases k <;> simp [f,rev,D.first_zero,D.first_one]
  have hfu (k) : f k (u k)=D.first (F.θf k) := by
    cases k
    · rfl
    · change D.first (unitInterval.symmHomeomorph (unitInterval.symmHomeomorph (F.θf true)))=D.first (F.θf true)
      congr 1
      apply Subtype.ext
      change 1-(1-(F.θf true:ℝ))=(F.θf true:ℝ)
      ring
  have hfv (k) (t : Interval) : f k (v k t)=D.first t := by
    cases k
    · rfl
    · change D.first (unitInterval.symmHomeomorph (unitInterval.symmHomeomorph t))=D.first t
      congr 1
      apply Subtype.ext
      change 1-(1-(t:ℝ))=(t:ℝ)
      ring
  have hvorder (k) (t : Interval) : v k t≤u k ↔ (if k then F.θf k≤t else t≤F.θf k) := by
    cases k
    · rfl
    · change (1-(t:ℝ)≤1-(F.θf true:ℝ)) ↔ (F.θf true:ℝ)≤(t:ℝ)
      constructor <;> intro h <;> linarith
  have hport (k) : D.first (F.θf k) ∈ (F.E k).source := by
    have hh := (F.first_framing k (F.θf k) ⟨0,by norm_num⟩
      (by simpa using (F.corner_positive k).2.2.1)).1
    rw [F.first_center] at hh
    exact hh
  have hsegment (k) (x : S) (hx : x ∈ (F.E k).source) (hx0 : F.E k x 0=0)
      (hxlo : 0≤F.E k x 1) (_hxhi : F.E k x 1≤F.E k (D.first (F.θf k)) 1) : x ∈ Set.range (f k) := by
    rw [hfrange]
    by_cases he : F.E k x 1=0
    · have hEx : F.E k x=F.E k (if k then D.finish else D.start) := by
        rw [(F.point k).2]
        ext j
        fin_cases j
        · exact hx0
        · exact he
      have hh := (F.E k).injOn hx (F.point k).1 hEx
      rw [hh]
      cases k
      · exact ⟨0,D.first_zero⟩
      · exact ⟨1,D.first_one⟩
    · have hraw : x ∈ (B.boundary i).image := (F.branch_trace k x hx).mpr (Or.inl ⟨hx0,hxlo⟩)
      rw [B.boundary_image] at hraw
      rcases hraw with hfirst|hclose
      · exact hfirst
      · have hxb : x ∈ b.image := by
          rw [← B.closing_cover]
          cases i
          · exact Or.inl hclose
          · exact Or.inr hclose
        exact (he ((F.current_axis k x hx).mp hxb)).elim
  have hprefix (k) := source_axis_segment_is_initial_source_prefix (f k) (hf k) (F.E k) (u k)
    (by rw [hf0]; exact (F.point k).1) (by rw [hf0]; exact (F.point k).2)
    (by rw [hfu]; exact hport k)
    (by rw [hfu]; exact (F.target_axis k _ (hport k)).mp (D.first_subset (Set.mem_range_self _)))
    (by rw [hfu]; exact F.first_height k) (F.square k)
    (by intro x hx hx0 hxlo hxhi; rw [hfu] at hxhi; exact hsegment k x hx hx0 hxlo hxhi)
  intro k t
  constructor
  · intro ht
    have hx : f k (v k t) ∈ (f k) '' Set.Icc (0:Interval) (u k) :=
      ⟨v k t,⟨(v k t).property.1,(hvorder k t).mpr ht⟩,rfl⟩
    rw [(hprefix k).1] at hx
    rw [hfu k,hfv k t] at hx
    exact hx
  · intro ht
    apply (hvorder k t).mp
    apply (hprefix k).2.2 (v k t)
    · rw [hfv]; exact ht.1
    · rw [hfv]; exact ht.2.1
    · rw [hfv]; exact ht.2.2.1
    · rw [hfv,hfu]; exact ht.2.2.2
end CurveComplex
#print axioms CurveComplex.source_first_return_first_ports_exact_source_order
