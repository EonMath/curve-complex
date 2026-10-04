import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualAttachedCapHeightBounds
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnPortSourceOrder
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualClosingPortSourceOrder
namespace CurveComplex
open Set Topology Schoenflies
/-- Actual cap/first-middle incidence within the produced framing window is
exactly the designated port. Parameter order is derived from the raw source
branch, and the cap truncation bound from its actual embedding. -/
theorem source_attached_cap_first_middle_local_port
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {D : SourceFirstReturnBoundary a b}
    {B : SourceTwoSurgeryBranches D} {i : Bool}
    {F : SourceFirstReturnFramedStrips D B i} (A : SourceFirstReturnAttachedCaps F)
    (k : Bool) (u : Interval)
    (hu : u ∈ Set.Icc (F.θf false) (F.θf true))
    (hwindow : |(u:ℝ)-(F.θf k:ℝ)|<F.ηf k) :
    F.N (u,A.w) ∈ Set.range (A.C k) ↔ u=F.θf k := by
  constructor
  · intro hx
    obtain ⟨hs,hcoords⟩ := F.first_framing k u A.w hwindow
    have hsource : D.first u ∈ (F.E k).source := by
      have hh := (F.first_framing k u ⟨0,by norm_num⟩ hwindow).1
      rw [F.first_center] at hh
      exact hh
    have haxis : F.E k (D.first u) 0=0 := (F.target_axis k _ hsource).mp (D.first_subset (Set.mem_range_self u))
    have hraw : D.first u ∈ (B.boundary i).image := by rw [B.boundary_image]; exact Or.inl (Set.mem_range_self u)
    have hnon : 0≤F.E k (D.first u) 1 := by
      rcases (F.branch_trace k _ hsource).mp hraw with hh|hh
      · exact hh.2
      · exact hh.2 ▸ le_rfl
    have hC0coords : F.E k (A.C k 0) 1=F.E k (D.first (F.θf k)) 1 := by
      rw [A.first_port]
      have hh := (F.first_framing k (F.θf k) A.w
        (by simpa using (F.corner_positive k).2.2.1)).2
      have he := congrArg (fun q : Plane=>q 1) hh
      exact he
    have hvheight : A.v k 1≤F.E k (D.first (F.θf k)) 1 := by
      rcases A.shape k (A.C k 0) (Set.mem_range_self 0) with hh|hh
      · exact hh.2.trans_eq hC0coords
      · exact (hh.2.symm.trans hC0coords).le
    have hNlong : F.E k (F.N (u,A.w)) 1=F.E k (D.first u) 1 := by
      have he := congrArg (fun q : Plane=>q 1) hcoords
      exact he
    have hupper : F.E k (D.first u) 1≤F.E k (D.first (F.θf k)) 1 := by
      rcases source_attached_cap_truncation_heights A k _ hx with hh|hh
      · exact hNlong ▸ hh.2.2
      · exact hNlong ▸ hh.2.2 ▸ hvheight
    have horder := (source_first_return_first_ports_exact_source_order D B i F k u).mpr
      ⟨hsource,haxis,hnon,hupper⟩
    cases k
    · exact le_antisymm horder hu.1
    · exact le_antisymm hu.2 horder
  · intro he
    rw [he,← A.first_port]
    exact Set.mem_range_self 0

/-- The actual closing-middle cap incidence in its framing window is also
exactly its designated port; this is proved in the original source parameters. -/
theorem source_attached_cap_closing_middle_local_port
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {D : SourceFirstReturnBoundary a b}
    {B : SourceTwoSurgeryBranches D} {i : Bool}
    {F : SourceFirstReturnFramedStrips D B i} (A : SourceFirstReturnAttachedCaps F)
    (k : Bool) (u : Interval)
    (hu : u ∈ Set.Icc (F.θg false) (F.θg true))
    (hwindow : |(u:ℝ)-(F.θg k:ℝ)|<F.ηg k) :
    F.M (u,A.z) ∈ Set.range (A.C k) ↔ u=F.θg k := by
  constructor
  · intro hx
    obtain ⟨hs,hcoords⟩ := F.closing_framing k u A.z hwindow
    have hsource : B.closing i u ∈ (F.E k).source := by
      have hh := (F.closing_framing k u ⟨0,by norm_num⟩ hwindow).1
      rw [F.closing_center] at hh
      exact hh
    have hclosing : B.closing i u ∈ b.image := by
      rw [← B.closing_cover]
      cases i
      · exact Or.inl (Set.mem_range_self u)
      · exact Or.inr (Set.mem_range_self u)
    have haxis : F.E k (B.closing i u) 1=0 := (F.current_axis k _ hsource).mp hclosing
    have hraw : B.closing i u ∈ (B.boundary i).image := by rw [B.boundary_image]; exact Or.inr (Set.mem_range_self u)
    have hnon : 0≤F.E k (B.closing i u) 0 := by
      rcases (F.branch_trace k _ hsource).mp hraw with hh|hh
      · exact hh.1 ▸ le_rfl
      · exact hh.1
    have hC1coords : F.E k (A.C k 1) 0=F.E k (B.closing i (F.θg k)) 0 := by
      rw [A.closing_port]
      have hh := (F.closing_framing k (F.θg k) A.z
        (by simpa using (F.corner_positive k).2.2.2)).2
      have he := congrArg (fun q : Plane=>q 0) hh
      exact he
    have hvheight : A.v k 0≤F.E k (B.closing i (F.θg k)) 0 := by
      rcases A.shape k (A.C k 1) (Set.mem_range_self 1) with hh|hh
      · exact (hh.1.symm.trans hC1coords).le
      · exact hh.1.trans_eq hC1coords
    have hMlong : F.E k (F.M (u,A.z)) 0=F.E k (B.closing i u) 0 := by
      have he := congrArg (fun q : Plane=>q 0) hcoords
      exact he
    have hupper : F.E k (B.closing i u) 0≤F.E k (B.closing i (F.θg k)) 0 := by
      rcases source_attached_cap_truncation_heights A k _ hx with hh|hh
      · exact hMlong ▸ hh.1 ▸ hvheight
      · exact hMlong ▸ hh.2.1
    have horder := (source_first_return_closing_ports_exact_source_order D B i F k u).mpr
      ⟨hsource,haxis,hnon,hupper⟩
    cases k
    · exact le_antisymm horder hu.1
    · exact le_antisymm hu.2 horder
  · intro he
    rw [he,← A.closing_port]
    exact Set.mem_range_self 1
end CurveComplex
#print axioms CurveComplex.source_attached_cap_first_middle_local_port
#print axioms CurveComplex.source_attached_cap_closing_middle_local_port
