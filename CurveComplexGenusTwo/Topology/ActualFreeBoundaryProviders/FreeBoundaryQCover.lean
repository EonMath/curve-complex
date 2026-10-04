import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalSeparatingCoverPROVED
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryStripFinitePosition

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies RegionalEmbeddedFamily

/-- A closed set in a connected space is connected if its nonempty frontier is. -/
theorem closed_set_connected_of_connected_frontier
    {X : Type} [TopologicalSpace X] [ConnectedSpace X]
    (F : Set X) (hF : IsClosed F) (hfr : IsConnected (frontier F)) :
    IsConnected F := by
  refine ⟨hfr.nonempty.mono hF.frontier_subset,?_⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hF]
  intro U V hU hV hcov hdis
  have hfcover : frontier F ⊆ U ∪ V := hF.frontier_subset.trans hcov
  have hside := isPreconnected_iff_subset_of_disjoint_closed.mp hfr.isPreconnected
    U V hU hV hfcover (by rw [hdis.inter_eq,inter_empty])
  have select (U V : Set X) (hU : IsClosed U) (hV : IsClosed V)
      (hcov : F ⊆ U ∪ V) (hdis : Disjoint U V) (hfrU : frontier F ⊆ U) : F ⊆ U := by
    have he : F ∩ V = interior F \ U := by
      ext x
      constructor
      · rintro ⟨hxF,hxV⟩
        have hxU : x ∉ U := fun hxU => Set.disjoint_left.mp hdis hxU hxV
        refine ⟨?_,hxU⟩
        by_contra hn
        exact hxU (hfrU ⟨subset_closure hxF,hn⟩)
      · rintro ⟨hxF,hxU⟩
        exact ⟨interior_subset hxF,(hcov (interior_subset hxF)).resolve_left hxU⟩
    have hcl : IsClopen (F ∩ V) := ⟨hF.inter hV,he ▸ isOpen_interior.sdiff hU⟩
    rcases isClopen_iff.mp hcl with he0 | he1
    · intro x hxF
      rcases hcov hxF with hxU | hxV
      · exact hxU
      · exact False.elim (by have h : x ∈ F ∩ V := ⟨hxF,hxV⟩; rw [he0] at h; exact h)
    · obtain ⟨x,hx⟩ := hfr.nonempty
      have hxV : x ∈ V := (show x ∈ F ∩ V from he1 ▸ Set.mem_univ x).2
      exact False.elim (Set.disjoint_left.mp hdis (hfrU hx) hxV)
  exact hside.elim (fun h => Or.inl (select U V hU hV hcov hdis h))
    (fun h => Or.inr (select V U hV hU (by simpa only [union_comm] using hcov) hdis.symm h))

/-- Build the genuine universal cover of the literal deleted-disk complement.
The full lift of the given proper arc separates, including its boundary endpoints. -/
theorem actual_Q_proper_arc_separating_cover
    (S : Type) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ a : C(Interval, ↥Q), IsEmbedding a → a 0 ∈ B → a 1 ∈ B →
      (∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B) →
      ∃ top : TopologicalSpace (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y),
        letI := top
        SimplyConnectedSpace (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y) ∧
        T2Space (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y) ∧
        IsCoveringMap (Sigma.fst : (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y) → ↥Q) ∧
        Function.Surjective
          (Sigma.fst : (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y) → ↥Q) ∧
        ∀ A : C(Interval, (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y)),
          (∀ t, (A t).1 = a t) →
          ∃ U V : Set (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y),
            IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range A)ᶜ ∧
            frontier U = range A ∧ frontier V = range A := by
  classical
  intro Q B a ha ha0 ha1 hint
  let : ClosedSurface S := Classical.choice hS.2.1
  let E := chartAt (EuclideanSpace ℝ (Fin 2)) x
  have hQ : IsClosed Q := (E.symm.isOpen_image_of_subset_source Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans htarget)).isClosed_compl
  have hfront : frontier Q = E.symm '' Metric.sphere (E x) R :=
    chart_deleted_disk_complement_frontier E (E x) R hR htarget
  obtain ⟨c,hc⟩ := contact_chart_sphere_is_curve S E (E x) R hR htarget
  have hconn : IsConnected Q := closed_set_connected_of_connected_frontier Q hQ (by
    rw [hfront,← hc]
    exact isConnected_range c.embedded.continuous)
  let : ConnectedSpace ↥Q := isConnected_iff_connectedSpace.mp hconn
  have hbasis := contact_finite_circle_frontier_contractible_basis Q hQ (fun _ : Unit => c)
    (fun i j hij => False.elim (hij (Subsingleton.elim i j)))
    (by simpa only [Set.iUnion_const,hc] using hfront)
  obtain ⟨top,hsc,ht2,hcov,hsurj⟩ := contact_path_class_universal_cover hbasis (a 0)
  let X := Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y
  let : TopologicalSpace X := top
  let : SimplyConnectedSpace X := hsc
  let : T2Space X := ht2
  have hXbasis := contact_local_homeomorph_contractible_basis (Sigma.fst : X → ↥Q)
    hcov.isLocalHomeomorph hbasis
  let : StronglyLocallyContractibleSpace X := ⟨fun z => by
    rw [Filter.hasBasis_self]
    intro V hV
    obtain ⟨W,hWV,hW,hzW⟩ := mem_nhds_iff.mp hV
    obtain ⟨A,hzA,hA,hAW,hcA⟩ := hXbasis z W hW hzW
    exact ⟨A,hA.mem_nhds hzA,hcA,hAW.trans hWV⟩⟩
  let aProper : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
    ⟨a,ha,ha0,ha1,hint⟩
  obtain ⟨N,hN,hcenter,_,_,hopen⟩ :=
    CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
      S x R g hg hS hR htarget aProper
  refine ⟨top,hsc,ht2,hcov,hsurj,?_⟩
  intro A hA
  obtain ⟨M,hM,hMc,hMo⟩ := contact_cover_lifts_proper_strip
    (Sigma.fst : X → ↥Q) hcov N hN hopen a hcenter A hA
  have hsep := contact_simply_connected_proper_strip_separates M hM hMo.1
  simpa only [hMc] using hsep

end CoherentEndpointMotion.FreeBoundaryContactRepair
