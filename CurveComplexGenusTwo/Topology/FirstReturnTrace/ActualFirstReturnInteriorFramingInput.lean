import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualCornerPortAxisCharts
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualRetainedFramingParameters
namespace CurveComplex
open Set Topology Schoenflies
/-- Produce actual strictly INTERNAL corner framing data for both whole
source center arcs. The normalized charts retain the original corner normal
coordinates, so an interior-only finite framing producer suffices. -/
theorem source_first_return_interior_corner_framing_input
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ E : Bool → OpenPartialHomeomorph S Plane,
      (∀ k, (if k then D.finish else D.start) ∈ (E k).source ∧
        E k (if k then D.finish else D.start)=0) ∧
      (∀ k, Plane.closedSquare 0 1 ⊆ (E k).target) ∧
      Disjoint (closure (E false).source) (closure (E true).source) ∧
      (∀ k, Disjoint (closure (E k).source) (source_surgery_retained_crossings B i)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ a.image ↔ E k x 0=0)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ b.image ↔ E k x 1=0)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ (B.boundary i).image ↔
        (E k x 0=0 ∧ 0≤E k x 1) ∨ (0≤E k x 0 ∧ E k x 1=0))) ∧
      ∃ θf θg : Bool → Interval,
        Function.Injective θf ∧ Function.Injective θg ∧
        (∀ k, 0<(θf k:ℝ) ∧ (θf k:ℝ)<1) ∧
        (∀ k, 0<(θg k:ℝ) ∧ (θg k:ℝ)<1) ∧
        (θf false:ℝ)<1/3 ∧ (2/3:ℝ)<θf true ∧
        (θg false:ℝ)<1/3 ∧ (2/3:ℝ)<θg true ∧
        (∀ k, 0<E k (D.first (θf k)) 1 ∧ E k (D.first (θf k)) 1≤1/8) ∧
        (∀ k, 0<E k (B.closing i (θg k)) 0 ∧ E k (B.closing i (θg k)) 0≤1/8) ∧
        ∃ F G : Bool → OpenPartialHomeomorph S Plane,
          (∀ k, (F k).source=(E k).source ∧ (G k).source=(E k).source) ∧
          (∀ k, D.first (θf k) ∈ (F k).source ∧ F k (D.first (θf k))=0) ∧
          (∀ k, B.closing i (θg k) ∈ (G k).source ∧ G k (B.closing i (θg k))=0) ∧
          (∀ k u, D.first u ∈ (F k).source → F k (D.first u) 1=0) ∧
          (∀ k u, B.closing i u ∈ (G k).source → G k (B.closing i u) 1=0) ∧
          (∀ k x, F k x=Plane.mk (E k x 1-E k (D.first (θf k)) 1) (E k x 0)) ∧
          (∀ k x, G k x=Plane.mk (E k x 0-E k (B.closing i (θg k)) 0) (E k x 1)) := by
  classical
  obtain ⟨E,hp,hsquare,hdis,hER,ha,hb,hraw,hford,hgord⟩ :=
    source_first_return_ordered_port_corner_squares S D B ht i
  obtain ⟨θf,θg,hθf,hθg,hfp,hgp⟩ :=
    source_first_return_small_ports_in_corner_charts S D B i E hp ha hb hraw
      (fun _ => 1/4) (fun _ => 1/4) (by intro k; norm_num) (by intro k; norm_num)
      (1/16) (by norm_num)
  have hfl : (θf false:ℝ)<1/3 := hford false _ (hfp false).1
  have hfr : (2/3:ℝ)<θf true := hford true _ (hfp true).1
  have hgl : (θg false:ℝ)<1/3 := hgord false _ (hgp false).1
  have hgr : (2/3:ℝ)<θg true := hgord true _ (hgp true).1
  have hfi : Function.Injective θf := by
    intro k l he
    cases k <;> cases l
    · rfl
    · have hh := congrArg (fun u : Interval => (u:ℝ)) he; linarith
    · have hh := congrArg (fun u : Interval => (u:ℝ)) he; linarith
    · rfl
  have hgi : Function.Injective θg := by
    intro k l he
    cases k <;> cases l
    · rfl
    · have hh := congrArg (fun u : Interval => (u:ℝ)) he; linarith
    · have hh := congrArg (fun u : Interval => (u:ℝ)) he; linarith
    · rfl
  choose F G hFs hGs hFp hGq hF0 hG0 hFcoords hGcoords using fun k =>
    source_corner_port_axis_charts (E k) (D.first (θf k)) (B.closing i (θg k))
      (hfp k).1 (hgp k).1 (hfp k).2.1 (hgp k).2.2.1
  have hheightf (k) : 0<E k (D.first (θf k)) 1 ∧ E k (D.first (θf k)) 1≤1/8 := by
    refine ⟨(hfp k).2.2.1,?_⟩
    have hn := (Plane.abs_one_le_supNorm (E k (D.first (θf k)))).trans
      (Plane.supNorm_le_norm (E k (D.first (θf k))))
    have hh := (hfp k).2.2.2
    exact ((le_abs_self _).trans hn).trans (hh.le.trans (by norm_num))
  have hheightg (k) : 0<E k (B.closing i (θg k)) 0 ∧ E k (B.closing i (θg k)) 0≤1/8 := by
    refine ⟨(hgp k).2.1,?_⟩
    have hn := (Plane.abs_zero_le_supNorm (E k (B.closing i (θg k)))).trans
      (Plane.supNorm_le_norm (E k (B.closing i (θg k))))
    have hh := (hgp k).2.2.2
    exact ((le_abs_self _).trans hn).trans (hh.le.trans (by norm_num))
  refine ⟨E,hp,hsquare,hdis,hER,ha,hb,hraw,θf,θg,hfi,hgi,
    (fun k => ⟨(hθf k).1,(hθf k).2.1⟩),(fun k => ⟨(hθg k).1,(hθg k).2.1⟩),
    hfl,hfr,hgl,hgr,hheightf,hheightg,F,G,(fun k => ⟨hFs k,hGs k⟩),
    (fun k => ⟨hFp k,hF0 k⟩),(fun k => ⟨hGq k,hG0 k⟩),?_,?_,hFcoords,hGcoords⟩
  · intro k u hu
    have hs : D.first u ∈ (E k).source := hFs k ▸ hu
    have hz := (ha k _ hs).mp (D.first_subset (Set.mem_range_self u))
    rw [hFcoords]
    exact hz
  · intro k u hu
    have hs : B.closing i u ∈ (E k).source := hGs k ▸ hu
    have hm : B.closing i u ∈ b.image := by
      rw [← B.closing_cover]
      cases i
      · exact Or.inl (Set.mem_range_self u)
      · exact Or.inr (Set.mem_range_self u)
    have hz := (hb k _ hs).mp hm
    rw [hGcoords]
    exact hz
end CurveComplex
#print axioms CurveComplex.source_first_return_interior_corner_framing_input
