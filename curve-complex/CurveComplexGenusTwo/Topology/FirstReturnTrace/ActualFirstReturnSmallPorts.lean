import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualEndpointPortSelection
namespace CurveComplex
open Set Topology Schoenflies
/-- Select actual first/closing ports in arbitrary framed endpoint windows of
the given genuine corner charts. Both longitudinal chart heights are positive
and arbitrarily small. Source parameters remain in their original coordinates. -/
theorem source_first_return_small_ports_in_corner_charts
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (i : Bool)
    (E : Bool → OpenPartialHomeomorph S Plane)
    (hp : ∀ k, (if k then D.finish else D.start) ∈ (E k).source ∧
      E k (if k then D.finish else D.start)=0)
    (ha : ∀ k x, x ∈ (E k).source → (x ∈ a.image ↔ E k x 0=0))
    (hb : ∀ k x, x ∈ (E k).source → (x ∈ b.image ↔ E k x 1=0))
    (hraw : ∀ k x, x ∈ (E k).source → (x ∈ (B.boundary i).image ↔
      (E k x 0=0 ∧ 0≤E k x 1) ∨ (0≤E k x 0 ∧ E k x 1=0)))
    (ηf ηg : Bool → ℝ) (hηf : ∀ k, 0<ηf k) (hηg : ∀ k, 0<ηg k)
    (r : ℝ) (hr : 0<r) :
    ∃ θf θg : Bool → Interval,
      (∀ k, 0<(θf k:ℝ) ∧ (θf k:ℝ)<1 ∧
        |(θf k:ℝ)-(if k then 1 else 0)|<ηf k) ∧
      (∀ k, 0<(θg k:ℝ) ∧ (θg k:ℝ)<1 ∧
        |(θg k:ℝ)-(if k then 1 else 0)|<ηg k) ∧
      (∀ k, D.first (θf k) ∈ (E k).source ∧
        E k (D.first (θf k)) 0=0 ∧ 0<E k (D.first (θf k)) 1 ∧
        ‖E k (D.first (θf k))‖<r) ∧
      (∀ k, B.closing i (θg k) ∈ (E k).source ∧
        0<E k (B.closing i (θg k)) 0 ∧ E k (B.closing i (θg k)) 1=0 ∧
        ‖E k (B.closing i (θg k))‖<r) := by
  classical
  let rev : C(Interval,Interval) := ⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩
  let f : Bool → C(Interval,S) := fun k => if k then D.first.comp rev else D.first
  let g : Bool → C(Interval,S) := fun k => if k then (B.closing i).comp rev else B.closing i
  have hf (k) : IsEmbedding (f k) := by
    cases k
    · exact D.first_embedded
    · exact D.first_embedded.comp unitInterval.symmHomeomorph.isEmbedding
  have hg (k) : IsEmbedding (g k) := by
    cases k
    · exact B.closing_embedded i
    · exact (B.closing_embedded i).comp unitInterval.symmHomeomorph.isEmbedding
  have hf0 (k) : f k 0=(if k then D.finish else D.start) := by
    cases k <;> simp [f,rev,D.first_zero,D.first_one]
  have hg0 (k) : g k 0=(if k then D.finish else D.start) := by
    cases k <;> simp [g,rev,B.closing_zero,B.closing_one]
  choose uf huf0 huf1 hufη hufE hufnorm hufne using fun k =>
    source_embedded_arc_endpoint_small_port (f k) (hf k) (E k)
      (by rw [hf0]; exact (hp k).1) (by rw [hf0]; exact (hp k).2)
      (ηf k) r (hηf k) hr
  choose ug hug0 hug1 hugη hugE hugnorm hugne using fun k =>
    source_embedded_arc_endpoint_small_port (g k) (hg k) (E k)
      (by rw [hg0]; exact (hp k).1) (by rw [hg0]; exact (hp k).2)
      (ηg k) r (hηg k) hr
  let θf : Bool → Interval := fun k => if k then unitInterval.symmHomeomorph (uf k) else uf k
  let θg : Bool → Interval := fun k => if k then unitInterval.symmHomeomorph (ug k) else ug k
  have hfp (k) : D.first (θf k)=f k (uf k) := by cases k <;> rfl
  have hgp (k) : B.closing i (θg k)=g k (ug k) := by cases k <;> rfl
  refine ⟨θf,θg,?_,?_,?_,?_⟩
  · intro k
    cases k
    · exact ⟨huf0 false,huf1 false,by simpa [θf,abs_of_pos (huf0 false)] using hufη false⟩
    · change 0<1-(uf true:ℝ) ∧ 1-(uf true:ℝ)<1 ∧ |1-(uf true:ℝ)-1|<ηf true
      exact ⟨by linarith [huf1 true],by linarith [huf0 true],by simpa [abs_of_pos (huf0 true)] using hufη true⟩
  · intro k
    cases k
    · exact ⟨hug0 false,hug1 false,by simpa [θg,abs_of_pos (hug0 false)] using hugη false⟩
    · change 0<1-(ug true:ℝ) ∧ 1-(ug true:ℝ)<1 ∧ |1-(ug true:ℝ)-1|<ηg true
      exact ⟨by linarith [hug1 true],by linarith [hug0 true],by simpa [abs_of_pos (hug0 true)] using hugη true⟩
  · intro k
    have hs : D.first (θf k) ∈ (E k).source := hfp k ▸ hufE k
    have hz : E k (D.first (θf k)) 0=0 :=
      (ha k _ hs).mp (D.first_subset (Set.mem_range_self _))
    have hshape := (hraw k _ hs).mp (by rw [B.boundary_image]; exact Or.inl (Set.mem_range_self _))
    have hnonneg : 0≤E k (D.first (θf k)) 1 := by
      rcases hshape with hh | hh
      · exact hh.2
      · exact hh.2 ▸ le_rfl
    have hne : E k (D.first (θf k)) 1≠0 := by
      intro he
      apply hufne k
      rw [← hfp k]
      ext j
      fin_cases j
      · exact hz
      · exact he
    exact ⟨hs,hz,lt_of_le_of_ne hnonneg hne.symm,hfp k ▸ hufnorm k⟩
  · intro k
    have hs : B.closing i (θg k) ∈ (E k).source := hgp k ▸ hugE k
    have hbmem : B.closing i (θg k) ∈ b.image := by
      rw [← B.closing_cover]
      cases i
      · exact Or.inl (Set.mem_range_self _)
      · exact Or.inr (Set.mem_range_self _)
    have hz : E k (B.closing i (θg k)) 1=0 := (hb k _ hs).mp hbmem
    have hshape := (hraw k _ hs).mp (by rw [B.boundary_image]; exact Or.inr (Set.mem_range_self _))
    have hnonneg : 0≤E k (B.closing i (θg k)) 0 := by
      rcases hshape with hh | hh
      · exact hh.1 ▸ le_rfl
      · exact hh.1
    have hne : E k (B.closing i (θg k)) 0≠0 := by
      intro he
      apply hugne k
      rw [← hgp k]
      ext j
      fin_cases j
      · exact he
      · exact hz
    exact ⟨hs,lt_of_le_of_ne hnonneg hne.symm,hz,hgp k ▸ hugnorm k⟩
end CurveComplex
#print axioms CurveComplex.source_first_return_small_ports_in_corner_charts
