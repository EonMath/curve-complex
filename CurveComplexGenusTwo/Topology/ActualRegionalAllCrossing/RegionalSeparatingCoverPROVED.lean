import CurveComplexGenusTwo.Topology.ActualRegionalContactGeometry.RegionalFiniteContactGeometry
import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalStripCoverSeparation

open CurveComplex Set Topology Schoenflies

theorem source_actual_regional_proper_arc_separating_universal_cover
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image)
    (a : C(Interval, ↥F)) (ha : Topology.IsEmbedding a)
    (ha0 : (a 0).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
    (ha1 : (a 1).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
    (haClear : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (a t).val ∉ frontier F) :
    ∃ top : TopologicalSpace (Σ y : ↥F, Path.Homotopic.Quotient (a 0) y),
      letI := top
      SimplyConnectedSpace (Σ y : ↥F, Path.Homotopic.Quotient (a 0) y) ∧
      T2Space (Σ y : ↥F, Path.Homotopic.Quotient (a 0) y) ∧
      IsCoveringMap (Sigma.fst : (Σ y : ↥F, Path.Homotopic.Quotient (a 0) y) → ↥F) ∧
      Function.Surjective
        (Sigma.fst : (Σ y : ↥F, Path.Homotopic.Quotient (a 0) y) → ↥F) ∧
      ∀ A : C(Interval, (Σ y : ↥F, Path.Homotopic.Quotient (a 0) y)),
        (∀ t, (A t).1 = a t) →
        ∃ U V : Set (Σ y : ↥F, Path.Homotopic.Quotient (a 0) y),
          IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
          U ∪ V = (Set.range A)ᶜ ∧
          frontier U = Set.range A ∧ frontier V = Set.range A := by
  classical
  have _ := hregular
  let : ClosedSurface S := Classical.choice hS.2.1
  let : ConnectedSpace ↥F := isConnected_iff_connectedSpace.mp hFconnected
  obtain ⟨c₀,hc₀⟩ := RegionalEmbeddedFamily.contact_chart_sphere_is_curve
    S (chartAt (EuclideanSpace ℝ (Fin 2)) x)
    ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R hR htarget
  let d : Option J → Curve S := fun i => i.elim c₀ (fun j => (c j).val)
  have hd : ∀ i j, i ≠ j → Disjoint (d i).image (d j).image := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => simpa only [d,Option.elim_none,Option.elim_some,hc₀] using (hbaseDisjoint j).symm
    | some i =>
      cases j with
      | none => simpa only [d,Option.elim_none,Option.elim_some,hc₀] using hbaseDisjoint i
      | some j => exact hdisjoint i j (fun he => hij (congrArg Option.some he))
  have hdf : frontier F = ⋃ i, (d i).image := by
    rw [hfrontier]
    ext y
    constructor
    · rintro (hy | hy)
      · exact Set.mem_iUnion.mpr ⟨none,by change y ∈ c₀.image; rwa [hc₀]⟩
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hy
        exact Set.mem_iUnion.mpr ⟨some i,hi⟩
    · intro hy
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hy
      cases i with
      | none => exact Or.inl (by change y ∈ c₀.image at hi; rwa [hc₀] at hi)
      | some i => exact Or.inr (Set.mem_iUnion.mpr ⟨i,hi⟩)
  have hbasis := RegionalEmbeddedFamily.contact_finite_circle_frontier_contractible_basis
    F hFcompact.isClosed d hd hdf
  obtain ⟨top,hsc,ht2,hcov,hsurj⟩ :=
    RegionalEmbeddedFamily.contact_path_class_universal_cover hbasis (a 0)
  let X := Σ y : ↥F, Path.Homotopic.Quotient (a 0) y
  let : TopologicalSpace X := top
  let : SimplyConnectedSpace X := hsc
  let : T2Space X := ht2
  have hXbasis := RegionalEmbeddedFamily.contact_local_homeomorph_contractible_basis
    (Sigma.fst : X → ↥F) hcov.isLocalHomeomorph hbasis
  let : StronglyLocallyContractibleSpace X := ⟨fun z => by
    rw [Filter.hasBasis_self]
    intro V hV
    obtain ⟨W,hWV,hW,hzW⟩ := mem_nhds_iff.mp hV
    obtain ⟨A,hzA,hA,hAW,hcA⟩ := hXbasis z W hW hzW
    exact ⟨A,hA.mem_nhds hzA,hcA,hAW.trans hWV⟩⟩
  obtain ⟨N,hN,hcenter,_,_,hopen⟩ := regional_original_proper_arc_has_F_strip
    S g hg hS x R hR htarget F hFcompact hbase houtside J c hbaseDisjoint hfrontier
    a ha ha0 ha1 haClear
  refine ⟨top,hsc,ht2,hcov,hsurj,?_⟩
  intro A hA
  obtain ⟨M,hM,hMc,hMo,_hproj⟩ := RegionalEmbeddedFamily.contact_cover_lifts_proper_strip
    (Sigma.fst : X → ↥F) hcov N hN hopen a hcenter A hA
  have hsep := RegionalEmbeddedFamily.contact_simply_connected_proper_strip_separates M hM hMo
  simpa only [hMc] using hsep
