import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.LocalEndpointSlide

namespace CoherentEndpointMotion
open CurveComplex Set Topology Schoenflies

/-- Actual original-Q free-boundary position relative to a closed protected
graph. Only initial disjointness from the moving arc is assumed; both finite
contact and separated free endpoints are produced by supported ambient moves. -/
theorem original_proper_arcs_graph_relative_free_boundary_finite_position
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target) :
    let Q : Set S := ((chartAt Plane x).symm '' Metric.ball ((chartAt Plane x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt Plane x).symm ''
      Metric.sphere ((chartAt Plane x) x) R}
    ∀ (a b : C(Interval,↥Q)), IsEmbedding a → IsEmbedding b →
      (a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B) →
      (∀ s ∈ Ioo (0:Interval) 1, a s ∉ B ∧ b s ∉ B) →
      ∀ G : Set ↥Q, IsClosed G → Disjoint (range b) G →
      ∃ q : C(Interval,↥Q), ∃ H : AmbientIsotopy ↥Q,
        IsEmbedding q ∧ (q 0 ∈ B ∧ q 1 ∈ B) ∧
        (∀ s ∈ Ioo (0:Interval) 1, q s ∉ B) ∧
        Disjoint ({a 0,a 1} : Set ↥Q) {q 0,q 1} ∧
        (range a ∩ range q).Finite ∧
        (∀ t, (fun y => H.map (t,y)) '' B = B) ∧
        H.finalMap '' range b = range q ∧
        (∀ t y, y ∈ G → H.map (t,y) = y) := by
  classical
  intro Q B a b ha hb hends hi G hG hbg
  letI : ClosedSurface S := Classical.choice hS.2.1
  let pb : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
    ⟨b,hb,hends.2.2.1,hends.2.2.2,fun s hs => (hi s hs).2⟩
  obtain ⟨E,hE,hEcenter,hEend,hEint,hEopen⟩ :=
    CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
      S x R g hg hS hR htarget pb
  obtain ⟨N,hN,hNcenter,hNend,hNint,hNopen,hNG⟩ :=
    proper_signed_strip_narrow_in_open B Gᶜ hG.isOpen_compl b
      (fun y hy h => Set.disjoint_left.mp hbg hy h)
      E hE hEcenter hEend hEint hEopen
  obtain ⟨D,p,hD,hp,hDcenter,hDB,hDopen,hDrange⟩ :=
    signed_strip_normalize_with_center B b N hN hNcenter hNend hNint hNopen
  obtain ⟨w,H0,hw,hw0,hw1,hH0B,hH0move,hH0outside⟩ :=
    strip_rail_endpoint_slide_avoiding_finite_set B D hD hDopen hDB p hp
      {a 0,a 1} ((Set.finite_singleton (a 1)).insert (a 0))
  have hH0G : ∀ t y, y ∈ G → H0.map (t,y) = y := by
    intro t y hy
    apply hH0outside
    intro hyD
    rw [hDrange] at hyD
    exact hNG hyD hy
  obtain ⟨e,he⟩ := H0.homeomorphism_at 1
  have heB : e '' B = B := by simpa only [← he] using hH0B 1
  let b' : C(Interval,↥Q) := (⟨e,e.continuous⟩ : C(↥Q,↥Q)).comp b
  have hb' : IsEmbedding b' := e.isEmbedding.comp hb
  have hb'ends : b' 0 ∈ B ∧ b' 1 ∈ B :=
    ⟨(boundary_preserving_homeomorph_mem B e heB _).mpr hends.2.2.1,
      (boundary_preserving_homeomorph_mem B e heB _).mpr hends.2.2.2⟩
  have hb'i : ∀ s ∈ Ioo (0:Interval) 1, b' s ∉ B := by
    intro s hs h
    exact (hi s hs).2 ((boundary_preserving_homeomorph_mem B e heB _).mp h)
  have hb'rail (s : Interval) : b' s = D (s,w) := by
    change e (b s) = D (s,w)
    rw [he,← hDcenter s]
    exact hH0move s
  have hsep : Disjoint ({a 0,a 1} : Set ↥Q) {b' 0,b' 1} := by
    apply Set.disjoint_left.mpr
    intro y hyA hyB
    rcases hyB with hyB | hyB
    · apply hw0
      rw [← hb'rail 0,← hyB]
      exact hyA
    · apply hw1
      rw [← hb'rail 1,← hyB]
      exact hyA
  have hb'G : Disjoint (range b') G := by
    apply Set.disjoint_left.mpr
    rintro y ⟨s,rfl⟩ hy
    have hefix : e (b' s) = b' s := (he (b' s)).trans (hH0G 1 (b' s) hy)
    have hes : e (b s) = b' s := rfl
    have heq : b s = b' s := e.injective (hes.trans hefix.symm)
    exact Set.disjoint_left.mp hbg (Set.mem_range_self s) (heq.symm ▸ hy)
  obtain ⟨q,K,hq,hq0,hq1,hqi,hKfix,hKmove,hfinite,hKG⟩ :=
    original_proper_arcs_separated_endpoints_graph_relative_finite_ambient_position
      S g hg hS x R hR htarget a b' ha hb'
      ⟨hends.1,hends.2.1,hb'ends.1,hb'ends.2⟩
      (fun s hs => ⟨(hi s hs).1,hb'i s hs⟩) hsep G hG hb'G
  have hKB : ∀ t, (fun y => K.map (t,y)) '' B = B := by
    intro t
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change K.map (t,z) ∈ B
      rw [hKfix t z hz]
      exact hz
    · intro hy
      exact ⟨y,hy,hKfix t y hy⟩
  have hqsep : Disjoint ({a 0,a 1} : Set ↥Q) {q 0,q 1} := by rw [hq0,hq1]; exact hsep
  have hH0range : H0.finalMap '' range b = range b' := by
    rw [← Set.range_comp]
    congr 1
    funext s
    exact (he (b s)).symm
  refine ⟨q,H0.compose K,hq,?_,hqi,hqsep,hfinite,
    boundary_preserving_motion_compose B H0 K hH0B hKB,?_,?_⟩
  · rw [hq0,hq1]
    exact hb'ends
  · rw [AmbientIsotopy.compose_finalMap,Set.image_comp,hH0range,hKmove]
  · intro t y hy
    change K.map (t,H0.map (t,y)) = y
    rw [hH0G t y hy,hKG t y hy]

/-- Instantiate the actual supported position producer at an induction stage.
The closed protected graph and its clearance are derived from the finite
processed labels and the current disjoint family. -/
theorem original_finite_disjoint_family_selected_arc_relative_position
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target) :
    let Q : Set S := ((chartAt Plane x).symm '' Metric.ball ((chartAt Plane x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt Plane x).symm ''
      Metric.sphere ((chartAt Plane x) x) R}
    ∀ {I : Type} [Fintype I] (a : I → C(Interval,↥Q)) (b : C(Interval,↥Q)),
      (∀ i, IsEmbedding (a i)) → IsEmbedding b →
      (∀ i, a i 0 ∈ B ∧ a i 1 ∈ B) → (b 0 ∈ B ∧ b 1 ∈ B) →
      (∀ i s, s ∈ Ioo (0:Interval) 1 → a i s ∉ B) →
      (∀ s ∈ Ioo (0:Interval) 1, b s ∉ B) →
      (∀ i j, i ≠ j → Disjoint (range (a i)) (range (a j))) →
      ∀ (P : Finset I) (i : I), i ∉ P →
      ∃ q : C(Interval,↥Q), ∃ H : AmbientIsotopy ↥Q,
        IsEmbedding q ∧ (q 0 ∈ B ∧ q 1 ∈ B) ∧
        (∀ s ∈ Ioo (0:Interval) 1, q s ∉ B) ∧
        Disjoint ({b 0,b 1} : Set ↥Q) {q 0,q 1} ∧
        (range b ∩ range q).Finite ∧
        (∀ t, (fun y => H.map (t,y)) '' B = B) ∧
        H.finalMap '' range (a i) = range q ∧
        (∀ j ∈ P, ∀ t y, y ∈ range (a j) → H.map (t,y) = y) := by
  classical
  intro Q B I _ a b ha hb haends hbends hai hbi hdis P i hiP
  letI : ClosedSurface S := Classical.choice hS.2.1
  let G : Set ↥Q := ⋃ j : ↥P, range (a j.val)
  have hG : IsClosed G := isClosed_iUnion_of_finite
    (fun j => (isCompact_range (a j.val).continuous).isClosed)
  have haG : Disjoint (range (a i)) G := by
    apply Set.disjoint_left.mpr
    intro y hyi hyG
    obtain ⟨j,hyj⟩ := Set.mem_iUnion.mp hyG
    have hij : i ≠ j.val := fun he => hiP (he.symm ▸ j.property)
    exact Set.disjoint_left.mp (hdis i j.val hij) hyi hyj
  obtain ⟨q,H,hq,hqends,hqi,hsep,hfin,hHB,hmove,hHG⟩ :=
    original_proper_arcs_graph_relative_free_boundary_finite_position S g hg hS x R hR
      htarget b (a i) hb (ha i) ⟨hbends.1,hbends.2,(haends i).1,(haends i).2⟩
      (fun s hs => ⟨hbi s hs,hai i s hs⟩) G hG haG
  refine ⟨q,H,hq,hqends,hqi,hsep,hfin,hHB,hmove,?_⟩
  intro j hj t y hy
  exact hHG t y (Set.mem_iUnion.mpr ⟨⟨j,hj⟩,hy⟩)

end CoherentEndpointMotion
