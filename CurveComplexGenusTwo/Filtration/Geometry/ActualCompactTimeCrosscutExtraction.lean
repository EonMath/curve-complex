import CurveComplexGenusTwo.Topology.Smoothing.MarkedIntervalCrosscutChartProof
import CurveComplexGenusTwo.Topology.GeometricPosition.IntervalSubdivision
import CurveComplexGenusTwo.Intersection.SphereRegionTransport
import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects

open Set Topology Schoenflies CurveComplex

namespace CurveComplex

/-- Compact time extracts a finite subdivision of actual chart receipts. The
chart support avoids the moving compact obstacle throughout each time slab. -/
theorem compact_time_chart_support_subdivision
    {S K L I : Type} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace L] [CompactSpace L]
    (f : C(Interval × K, S)) (g : C(Interval × L, S))
    (U C : I → Set S) (hU : ∀ i, IsOpen (U i))
    (hC : ∀ i, IsCompact (C i))
    (hcover : ∀ t : Interval, ∃ i,
      (∀ x, f (t, x) ∈ U i) ∧ (∀ y, g (t, y) ∉ C i)) :
    ∃ n : ℕ, 0 < n ∧ ∃ chart : Fin n → I,
      ∀ k : Fin n, ∀ t : Interval,
        (k.val : ℝ) / n ≤ t.val → t.val ≤ (k.val + 1 : ℝ) / n →
        (∀ x, f (t, x) ∈ U (chart k)) ∧
        (∀ y, g (t, y) ∉ C (chart k)) := by
  let V : I → Set Interval := fun i =>
    {t | Set.range (f.curry t) ⊆ U i} ∩
    {t | Set.range (g.curry t) ⊆ (C i)ᶜ}
  have hV : ∀ i, IsOpen (V i) := by
    intro i
    exact ((ContinuousMap.isOpen_setOfPred_range_subset (hU i)).preimage
      f.curry.continuous).inter
      ((ContinuousMap.isOpen_setOfPred_range_subset (hC i).isClosed.isOpen_compl).preimage
        g.curry.continuous)
  have hcov : ∀ t, ∃ i, (ContinuousMap.id Interval) t ∈ V i := by
    intro t
    obtain ⟨i, hi, hj⟩ := hcover t
    exact ⟨i, (Set.range_subset_iff.mpr hi), (Set.range_subset_iff.mpr hj)⟩
  obtain ⟨n, hn, chart, hc⟩ := position_interval_subdivision
    (ContinuousMap.id Interval) V hV hcov
  refine ⟨n, hn, chart, ?_⟩
  intro k t hlo hhi
  have ht := hc k t hlo hhi
  exact ⟨Set.range_subset_iff.mp ht.1, Set.range_subset_iff.mp ht.2⟩

end CurveComplex

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The next actual representative's interior is disjoint from the whole
protected support graph, including its marked endpoints. -/
theorem actual_next_arc_disjoint_support_graph
    (M : HyperellipticModel E S) {F : Finset (EssentialArcClass M)}
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (J : Finset (EssentialArcClass M)) (u : {w // w ∈ F}) (hu : u.val ∉ J) :
    Disjoint (arcInterior M (r u)) (actualObjectTrace M r J) := by
  apply Set.disjoint_left.mpr
  intro x hxu hxJ
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hxJ
  obtain ⟨hwJ, hxw⟩ := Set.mem_iUnion.mp hw
  have huw : u ≠ w := by
    intro he
    exact hu (he.symm ▸ hwJ)
  exact Set.disjoint_left.mp (hd u w huw) hxu ⟨hxw, hxu.2⟩

/-- An actual interior core remains free of marks and of the transported
protected graph under the ambient isotopy witnessing its quotient class. -/
theorem actual_isotopy_core_avoids_moving_graph
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (P : Set S) (hP : Disjoint (arcInterior M a) P)
    (H : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → H.map (t, z) = z)
    (t s : Interval) (hs0 : 0 < s.val) (hs1 : s.val < 1) :
    H.map (t, a.val.map s) ∉ M.cover.branch ∧
      H.map (t, a.val.map s) ∉ (fun z => H.map (t, z)) '' P := by
  have ha : a.val.map s ∉ M.cover.branch := by
    intro hb
    rcases a.val.marked_only_at_ends s hb with he | he
    · have hval : s.val = 0 := congrArg (fun u : Interval => u.val) he
      linarith
    · have hval : s.val = 1 := congrArg (fun u : Interval => u.val) he
      linarith
  obtain ⟨e, he⟩ := H.homeomorphism_at t
  have hinj : Function.Injective (fun z => H.map (t, z)) := by
    intro x y hxy
    apply e.injective
    simpa only [he] using hxy
  constructor
  · intro hb
    have hz := hm t (H.map (t, a.val.map s)) hb
    have heq := hinj hz
    exact ha (heq.symm ▸ hb)
  · rintro ⟨z, hz, heq⟩
    have heq' := hinj heq
    exact Set.disjoint_left.mp hP ⟨Set.mem_range_self s, ha⟩ (heq' ▸ hz)

/-- The actual square support of an open partial chart is compact. -/
theorem actual_crosscut_chart_square_support_compact
    (M : HyperellipticModel E S) (e : OpenPartialHomeomorph S Plane)
    (he : Plane.closedSquare 0 1 ⊆ e.target) :
    IsCompact (e.symm '' Plane.closedSquare 0 1) := by
  exact (isCompact_closedSquare 0 1).image_of_continuousOn
    (e.continuousOn_symm.mono he)

/-- A real interior core produces a straightening chart inside the complement
of all marks and the currently transported protected graph. -/
theorem actual_isotopy_core_crosscut_chart
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (P : Set S) (hPc : IsCompact P) (hP : Disjoint (arcInterior M a) P)
    (H : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → H.map (t, z) = z)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    (t : Interval) :
    let γ : Interval → S := fun s => H.map (t, a.val.map s)
    let q := γ ∘ Set.projIcc 0 1 zero_le_one
    ∃ e : OpenPartialHomeomorph S Plane,
      Plane.closedSquare 0 1 ⊆ e.target ∧
      q '' Set.Icc α β ⊆ e.source ∧
      e (q α) = Plane.mk (-1) 0 ∧ e (q β) = Plane.mk 1 0 ∧
      (∀ z ∈ e.source, z ∉ M.cover.branch ∧
        z ∉ (fun z => H.map (t, z)) '' P) ∧
      (∀ z ∈ e.source, z ∈ Set.range γ ↔ e z 1 = 0) ∧
      {z : S | z ∈ e.source ∧ e z ∈ Plane.closedSquare 0 1} ∩ Set.range γ =
        q '' Set.Icc α β := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let γ : Interval → S := fun s => H.map (t, a.val.map s)
  have hγ : Continuous γ :=
    H.map.continuous.comp (continuous_const.prodMk a.val.continuous)
  obtain ⟨h, hh⟩ := H.homeomorphism_at t
  have hc : ∀ s u, γ s = γ u → s = u ∨
      (s = (0 : Interval) ∧ u = (1 : Interval)) ∨
      (s = (1 : Interval) ∧ u = (0 : Interval)) := by
    intro s u hsu
    apply a.val.injective_except_loop_closure s u
    apply h.injective
    simpa only [hh] using hsu
  let Q : Set S := (fun z => H.map (t, z)) '' P
  have hQc : IsCompact Q := hPc.image
    (H.map.continuous.comp (continuous_const.prodMk continuous_id))
  let W : Set S := (M.cover.branch : Set S)ᶜ ∩ Qᶜ
  have hW : IsOpen W :=
    M.cover.branch.finite_toSet.isClosed.isOpen_compl.inter hQc.isClosed.isOpen_compl
  let p := a.val.map (0 : Interval)
  let e₀ : OpenPartialHomeomorph S Plane :=
    ((M.planeToSphere_isOpenEmbedding p).toOpenPartialHomeomorph).symm
  have he₀ : ∀ z, z ≠ p → z ∈ e₀.source := by
    intro z hz
    simp only [e₀, OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨M.puncturedPlane p ⟨z, hz⟩,
      congrArg Subtype.val ((M.puncturedPlane p).symm_apply_apply ⟨z, hz⟩)⟩
  have hsub : (γ ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc α β ⊆ W ∩ e₀.source := by
    rintro z ⟨s, hs, rfl⟩
    have hsI : s ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hproj : Set.projIcc 0 1 zero_le_one s = ⟨s, hsI⟩ :=
      Set.projIcc_of_mem _ hsI
    have hav := actual_isotopy_core_avoids_moving_graph M a P hP H hm t
      ⟨s, hsI⟩ (by linarith [hs.1]) (by linarith [hs.2])
    change γ (Set.projIcc 0 1 zero_le_one s) ∈ W ∩ e₀.source
    rw [hproj]
    refine ⟨hav, he₀ _ ?_⟩
    intro heq
    apply hav.1
    change γ ⟨s, hsI⟩ ∈ M.cover.branch
    rw [heq]
    exact a.val.start_marked
  obtain ⟨e, hes, het, hcore, hleft, hright, haxis, htrace⟩ :=
    actual_interval_subarc_crosscut_chart γ hγ hc α β hα hαβ hβ e₀ W hW hsub
  exact ⟨e, het, hcore, hleft, hright, fun z hz => (hes hz).1, haxis, htrace⟩

/-- Quotient equality produces the ambient witness and a finite time cover by
actual straightening charts. Each chart's square support is disjoint from the
transported compact graph throughout its whole slab. No finite sequence,
chart cover, or relative ambient witness is assumed. -/
theorem actual_same_class_finite_core_crosscut_subdivision
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hab : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b)
    (P : Set S) (hPc : IsCompact P) (hP : Disjoint (arcInterior M a) P)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) :
    ∃ H : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → H.map (t, z) = z) ∧
      H.finalMap '' a.val.image = b.val.image ∧
      ∃ n : ℕ, 0 < n ∧ ∃ ref : Fin n → Interval,
      ∃ chart : Fin n → OpenPartialHomeomorph S Plane,
        ∀ k : Fin n,
          Plane.closedSquare 0 1 ⊆ (chart k).target ∧
          (chart k) (H.map (ref k, a.val.map (Set.projIcc 0 1 zero_le_one α))) =
            Plane.mk (-1) 0 ∧
          (chart k) (H.map (ref k, a.val.map (Set.projIcc 0 1 zero_le_one β))) =
            Plane.mk 1 0 ∧
          (∀ z ∈ (chart k).source, z ∉ M.cover.branch) ∧
          (∀ z ∈ (chart k).source,
            z ∈ Set.range (fun s => H.map (ref k, a.val.map s)) ↔
              (chart k) z 1 = 0) ∧
          (∀ t : Interval, (k.val : ℝ) / n ≤ t.val →
            t.val ≤ (k.val + 1 : ℝ) / n →
            ((fun s => H.map (t, a.val.map (Set.projIcc 0 1 zero_le_one s))) ''
              Set.Icc α β ⊆ (chart k).source) ∧
            Disjoint ((fun z => H.map (t, z)) '' P)
              ((chart k).symm '' Plane.closedSquare 0 1)) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨H, hm, hend⟩ := (Quotient.exact hab : MarkedIsotopyRel M a.val.image b.val.image)
  have hx : ∀ t : Interval, ∃ e : OpenPartialHomeomorph S Plane,
      Plane.closedSquare 0 1 ⊆ e.target ∧
      ((fun s => H.map (t, a.val.map (Set.projIcc 0 1 zero_le_one s))) ''
        Set.Icc α β ⊆ e.source) ∧
      e (H.map (t, a.val.map (Set.projIcc 0 1 zero_le_one α))) = Plane.mk (-1) 0 ∧
      e (H.map (t, a.val.map (Set.projIcc 0 1 zero_le_one β))) = Plane.mk 1 0 ∧
      (∀ z ∈ e.source, z ∉ M.cover.branch ∧
        z ∉ (fun z => H.map (t, z)) '' P) ∧
      (∀ z ∈ e.source, z ∈ Set.range (fun s => H.map (t, a.val.map s)) ↔ e z 1 = 0) := by
    intro t
    obtain ⟨e, he, hcore, hleft, hright, havoid, haxis, htrace⟩ :=
      actual_isotopy_core_crosscut_chart M a P hPc hP H hm α β hα hαβ hβ t
    exact ⟨e, he, hcore, hleft, hright, havoid, haxis⟩
  choose e he hcore hleft hright havoid haxis using hx
  let K := Set.Icc α β
  letI : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace P := isCompact_iff_compactSpace.mp hPc
  let f : C(Interval × K, S) :=
    ⟨fun z => H.map (z.1, a.val.map (Set.projIcc 0 1 zero_le_one z.2.val)),
      H.map.continuous.comp (continuous_fst.prodMk
        (a.val.continuous.comp (continuous_projIcc.comp
          (continuous_subtype_val.comp continuous_snd))))⟩
  let g : C(Interval × P, S) :=
    ⟨fun z => H.map (z.1, z.2.val),
      H.map.continuous.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd))⟩
  let C : Interval → Set S := fun t => (e t).symm '' Plane.closedSquare 0 1
  have hC : ∀ t, IsCompact (C t) :=
    fun t => actual_crosscut_chart_square_support_compact M (e t) (he t)
  have hcover : ∀ t : Interval, ∃ i : Interval,
      (∀ x : K, f (t, x) ∈ (e i).source) ∧
      (∀ y : P, g (t, y) ∉ C i) := by
    intro t
    refine ⟨t, fun x => hcore t ⟨x.val, x.property, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hsrc := (e t).map_target (he t hz)
    have hn := (havoid t ((e t).symm z) hsrc).2
    apply hn
    rw [hzy]
    exact ⟨y.val, y.property, rfl⟩
  obtain ⟨n, hn, ref, href⟩ := compact_time_chart_support_subdivision f g
    (fun t => (e t).source) C (fun t => (e t).open_source) hC hcover
  refine ⟨H, hm, hend, n, hn, ref, fun k => e (ref k), ?_⟩
  intro k
  refine ⟨he _, hleft _, hright _, fun z hz => (havoid _ z hz).1, haxis _, ?_⟩
  intro t hlo hhi
  obtain ⟨hf, hg⟩ := href k t hlo hhi
  constructor
  · rintro z ⟨s, hs, rfl⟩
    exact hf ⟨s, hs⟩
  · apply Set.disjoint_left.mpr
    rintro z ⟨y, hy, rfl⟩ hz
    exact hg ⟨y, hy⟩ hz

/-- The concrete whole-family application supplies compactness and obstacle
disjointness from the original actual support data, rather than assuming them
as new geometric certificates. -/
theorem actual_support_finite_core_crosscut_subdivision
    (M : HyperellipticModel E S) {F : Finset (EssentialArcClass M)}
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
    (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (J : Finset (EssentialArcClass M)) (u : {w // w ∈ F}) (hu : u.val ∉ J)
    (b : EssentialMarkedArc M) (hb : Quotient.mk (essentialArcSetoid M) b = u.val)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) :
    ∃ H : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → H.map (t, z) = z) ∧
      H.finalMap '' (r u).val.image = b.val.image ∧
      ∃ n : ℕ, 0 < n ∧ ∃ ref : Fin n → Interval,
      ∃ chart : Fin n → OpenPartialHomeomorph S Plane,
        ∀ k : Fin n,
          Plane.closedSquare 0 1 ⊆ (chart k).target ∧
          (chart k) (H.map (ref k, (r u).val.map (Set.projIcc 0 1 zero_le_one α))) =
            Plane.mk (-1) 0 ∧
          (chart k) (H.map (ref k, (r u).val.map (Set.projIcc 0 1 zero_le_one β))) =
            Plane.mk 1 0 ∧
          (∀ z ∈ (chart k).source, z ∉ M.cover.branch) ∧
          (∀ z ∈ (chart k).source,
            z ∈ Set.range (fun s => H.map (ref k, (r u).val.map s)) ↔
              (chart k) z 1 = 0) ∧
          (∀ t : Interval, (k.val : ℝ) / n ≤ t.val →
            t.val ≤ (k.val + 1 : ℝ) / n →
            ((fun s => H.map (t, (r u).val.map (Set.projIcc 0 1 zero_le_one s))) ''
              Set.Icc α β ⊆ (chart k).source) ∧
            Disjoint ((fun z => H.map (t, z)) '' actualObjectTrace M r J)
              ((chart k).symm '' Plane.closedSquare 0 1)) := by
  exact actual_same_class_finite_core_crosscut_subdivision M (r u) b
    ((hr u).trans hb.symm) (actualObjectTrace M r J)
    (actualObjectTrace_compact M r J)
    (actual_next_arc_disjoint_support_graph M r hd J u hu) α β hα hαβ hβ

end CurveComplex.HyperellipticModel

#print axioms CurveComplex.compact_time_chart_support_subdivision
#print axioms CurveComplex.HyperellipticModel.actual_next_arc_disjoint_support_graph
#print axioms CurveComplex.HyperellipticModel.actual_isotopy_core_avoids_moving_graph
#print axioms CurveComplex.HyperellipticModel.actual_crosscut_chart_square_support_compact
#print axioms CurveComplex.HyperellipticModel.actual_isotopy_core_crosscut_chart
#print axioms CurveComplex.HyperellipticModel.actual_same_class_finite_core_crosscut_subdivision
#print axioms CurveComplex.HyperellipticModel.actual_support_finite_core_crosscut_subdivision
