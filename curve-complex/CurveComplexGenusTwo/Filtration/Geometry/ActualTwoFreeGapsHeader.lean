import CurveComplexGenusTwo.Filtration.Geometry.ActualObjectCircleHeader
import CurveComplexGenusTwo.Filtration.Geometry.ActualBadGraphNowhereDenseHeader
import CurveComplexGenusTwo.Filtration.Geometry.GapRefinementHeaders
import CurveComplexGenusTwo.Dependencies.ChartClosure
import CurveComplexGenusTwo.Intersection.SphereChart
namespace CurveComplex.HyperellipticModel
open Set CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualTwoFreeGapsHeader_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
theorem actual_two_disjoint_free_gaps (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : badVertices (actualArcLabels M) σ = σ) (hne : σ.Nonempty) :
    ∃ O P : Finset (EssentialArcClass M), ∃ U V : Set S,
      O ∈ actualObjectFamily M σ ∧ P ∈ actualObjectFamily M σ ∧
      IsComplementComponent (actualObjectTrace M r O) U ∧
      IsComplementComponent (actualObjectTrace M r P) V ∧
      IsComplementComponent (⋃ v, (r v).val.image) U ∧
      IsComplementComponent (⋃ v, (r v).val.image) V ∧
      (∀ Q ∈ actualObjectFamily M σ, Q ≠ O → ¬ actualObjectTrace M r Q ⊆ closure U) ∧
      (∀ Q ∈ actualObjectFamily M σ, Q ≠ P → ¬ actualObjectTrace M r Q ⊆ closure V) ∧
      Disjoint U V := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have htwo : ∀ O : Finset (EssentialArcClass M), O ∈ actualObjectFamily M σ →
    ∃ U V : Set S,
      IsComplementComponent (actualObjectTrace M r O) U ∧
      IsComplementComponent (actualObjectTrace M r O) V ∧
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ≠ V := by
    intro O hO
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    have hjregions : ∀ (c : CurveComplex.SpherePort.JordanCurve)
        (P : CurveComplex.SpherePort.Chart c),
      ∃ SU SV : Set CurveComplex.SpherePort.Sphere,
        IsComplementComponent c.image SU ∧ IsComplementComponent c.image SV ∧
        IsOpen SU ∧ IsOpen SV ∧ Disjoint SU SV ∧ SU ≠ SV ∧
        SU ∪ SV = c.imageᶜ ∧ frontier SU = c.image ∧ frontier SV = c.image := by
      intro c P
      classical
      let C := P.planeImage c
      have hC : Schoenflies.IsJordanCurve C := CurveComplex.SpherePort.chart_image_jordan c P
      have hsep := Schoenflies.jordan_curve_theorem hC
      let F : OnePoint Schoenflies.Plane ≃ₜ CurveComplex.SpherePort.Sphere :=
        CurveComplex.SpherePort.chartOnePoint c P
      let B : Set (OnePoint Schoenflies.Plane) := OnePoint.some '' C
      let U : Set (OnePoint Schoenflies.Plane) := OnePoint.some '' Schoenflies.inside C
      let V : Set (OnePoint Schoenflies.Plane) :=
        {OnePoint.infty} ∪ OnePoint.some '' Schoenflies.outside C
      have hBimage : F '' B = c.image := by
        ext x
        constructor
        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
          obtain ⟨y, hy, hzy⟩ := hz
          change (P.plane.symm z).val ∈ c.image
          rw [← hzy, P.plane.symm_apply_apply]
          exact hy
        · intro hx
          let y : {x : CurveComplex.SpherePort.Sphere // x ≠ P.puncture} :=
            ⟨x, fun he => P.avoids (he ▸ hx)⟩
          refine ⟨OnePoint.some (P.plane y), ⟨P.plane y, ⟨y, hx, rfl⟩, rfl⟩, ?_⟩
          change (P.plane.symm (P.plane y)).val = x
          rw [P.plane.symm_apply_apply]
      have hdisj : Disjoint U V := by
        rw [Set.disjoint_left]
        intro x hx hy
        cases x with
        | infty => simpa [U] using hx
        | coe z =>
          have hzU : z ∈ Schoenflies.inside C := by simpa [U] using hx
          have hzV : z ∈ Schoenflies.outside C := by simpa [V] using hy
          exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hzU hzV
      have hcover : U ∪ V = Bᶜ := by
        ext x
        cases x with
        | infty => simp [U, V, B]
        | coe z =>
          have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
          simpa [U, V, B] using hz
      have hclU0 : closure U = OnePoint.some '' closure (Schoenflies.inside C) := by
        have hk : IsCompact (closure (Schoenflies.inside C)) :=
          Metric.isCompact_of_isClosed_isBounded isClosed_closure hsep.isBounded_inside.closure
        apply Set.Subset.antisymm
        · exact closure_minimal (Set.image_mono subset_closure) (hk.image OnePoint.continuous_coe).isClosed
        · exact image_closure_subset_closure_image OnePoint.continuous_coe
      have hclU : closure U = U ∪ B := by
        rw [hclU0, (Schoenflies.IsRegionOf.inside C).closure_eq hsep, Set.image_union]
      have hclV : closure V = V ∪ B := by
        change closure (CurveComplex.SpherePort.compactifiedOutside (Schoenflies.outside C)) = _
        rw [CurveComplex.SpherePort.closure_compactifiedOutside,
          (Schoenflies.IsRegionOf.outside C).closure_eq hsep]
        simp only [CurveComplex.SpherePort.compactifiedOutside, Set.image_union]
        exact Set.union_assoc _ _ _ |>.symm
      have hUcomp : closure U = Vᶜ := by
        rw [hclU]
        ext x
        cases x with
        | infty => simp [U, V, B]
        | coe z =>
          have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
          have hd : z ∈ Schoenflies.inside C → z ∉ Schoenflies.outside C :=
            fun hz => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz
          have hi : z ∈ Schoenflies.inside C → z ∉ C := fun hz => Schoenflies.inside_subset_compl hz
          have ho : z ∈ Schoenflies.outside C → z ∉ C := fun hz => Schoenflies.outside_subset_compl hz
          have hz' : z ∈ Schoenflies.inside C ∨ z ∈ C ↔ z ∉ Schoenflies.outside C := by
            simp only [Set.mem_union, Set.mem_compl_iff] at hz
            tauto
          simpa [U, V, B] using hz'
      have hVcomp : closure V = Uᶜ := by
        rw [hclV]
        ext x
        cases x with
        | infty => simp [U, V, B]
        | coe z =>
          have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
          have hd : z ∈ Schoenflies.inside C → z ∉ Schoenflies.outside C :=
            fun hz => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz
          have hi : z ∈ Schoenflies.inside C → z ∉ C := fun hz => Schoenflies.inside_subset_compl hz
          have ho : z ∈ Schoenflies.outside C → z ∉ C := fun hz => Schoenflies.outside_subset_compl hz
          have hz' : z ∈ Schoenflies.outside C ∨ z ∈ C ↔ z ∉ Schoenflies.inside C := by
            simp only [Set.mem_union, Set.mem_compl_iff] at hz
            tauto
          simpa [U, V, B] using hz'
      have hopenU : IsOpen U := by
        rw [← compl_compl U, ← hVcomp]
        exact isClosed_closure.isOpen_compl
      have hopenV : IsOpen V := by
        rw [← compl_compl V, ← hUcomp]
        exact isClosed_closure.isOpen_compl
      have hintU : interior (closure U) = U := by
        rw [hUcomp, interior_compl, hVcomp, compl_compl]
      have hintV : interior (closure V) = V := by
        rw [hVcomp, interior_compl, hUcomp, compl_compl]
      have hboundU : frontier U = B := by
        rw [hopenU.frontier_eq, hclU]
        ext x
        have hn : x ∈ U → x ∉ B := fun hx => (Set.ext_iff.mp hcover x).mp (Or.inl hx)
        simp only [Set.mem_sdiff, Set.mem_union]
        tauto
      have hboundV : frontier V = B := by
        rw [hopenV.frontier_eq, hclV]
        ext x
        have hn : x ∈ V → x ∉ B := fun hx => (Set.ext_iff.mp hcover x).mp (Or.inr hx)
        simp only [Set.mem_sdiff, Set.mem_union]
        tauto
    
      have hconnU : IsConnected U := hsep.isConnected_inside.image
        OnePoint.some OnePoint.continuous_coe.continuousOn
      have hconnV0 : IsConnected (OnePoint.some '' Schoenflies.outside C) :=
        hsep.isConnected_outside.image OnePoint.some OnePoint.continuous_coe.continuousOn
      have hinfty : (OnePoint.infty : OnePoint Schoenflies.Plane) ∈
          closure (OnePoint.some '' Schoenflies.outside C) := by
        by_contra hn
        have hsub : closure (OnePoint.some '' Schoenflies.outside C) ⊆ Set.range OnePoint.some := by
          intro x hx
          cases x with
          | infty => exact False.elim (hn hx)
          | coe y => exact ⟨y, rfl⟩
        have hk := OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isCompact_preimage'
          isClosed_closure.isCompact hsub
        apply hsep.not_isBounded_outside
        exact hk.isBounded.subset (fun x hx => subset_closure ⟨x, hx, rfl⟩)
      have hconnV : IsConnected V := hconnV0.subset_closure Set.subset_union_right (by
        rintro x (hx | hx)
        · exact Set.mem_singleton_iff.mp hx ▸ hinfty
        · exact subset_closure hx)
      let SU := F '' U
      let SV := F '' V
      have hsconnU : IsConnected SU := hconnU.image F F.continuous.continuousOn
      have hsconnV : IsConnected SV := hconnV.image F F.continuous.continuousOn
      have hsopenU : IsOpen SU := F.isOpenMap U hopenU
      have hsopenV : IsOpen SV := F.isOpenMap V hopenV
      have hsdisj : Disjoint SU SV := (Set.disjoint_image_iff F.injective).mpr hdisj
      have hscover : SU ∪ SV = c.imageᶜ := by
        rw [← Set.image_union, hcover, F.image_compl, hBimage]
      have hsboundU : frontier SU = c.image := by
        rw [← F.image_frontier, hboundU, hBimage]
      have hsboundV : frontier SV = c.image := by
        rw [← F.image_frontier, hboundV, hBimage]
      have hmaximal : ∀ T R : Set CurveComplex.SpherePort.Sphere, IsConnected T →
          IsOpen T → IsOpen R → Disjoint T R → T ∪ R = c.imageᶜ →
          IsComplementComponent c.image T := by
        intro T R hT hTopen hRopen hTR hc
        refine ⟨hT.nonempty, hT, (fun x hx => hc ▸ Or.inl hx), ?_⟩
        intro W hW hTW hWc
        have hsplit := hW.isPreconnected.subset_or_subset hTopen hRopen hTR (hc.symm ▸ hWc)
        rcases hsplit with hWT | hWR
        · exact Set.Subset.antisymm hWT hTW
        · obtain ⟨x, hx⟩ := hT.nonempty
          exact False.elim (Set.disjoint_left.mp hTR hx (hWR (hTW hx)))
      have hcU := hmaximal SU SV hsconnU hsopenU hsopenV hsdisj hscover
      have hcV := hmaximal SV SU hsconnV hsopenV hsopenU hsdisj.symm
        ((Set.union_comm SV SU).trans hscover)
      have hdistinct : SU ≠ SV := by
        intro heq
        obtain ⟨x, hx⟩ := hsconnU.nonempty
        exact Set.disjoint_left.mp hsdisj hx (heq ▸ hx)
      exact ⟨SU, SV, hcU, hcV, hsopenU, hsopenV, hsdisj, hdistinct,
        hscover, hsboundU, hsboundV⟩
    have hcomponent : ∀ (g : CurveComplex.SpherePort.Sphere ≃ₜ S)
        {A U : Set CurveComplex.SpherePort.Sphere},
        IsComplementComponent A U → IsComplementComponent (g '' A) (g '' U) := by
      intro g A U hU
      rcases hU with ⟨hne, hconn, hsub, hmax⟩
      refine ⟨hne.image g, hconn.image g g.continuous.continuousOn, ?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
        exact hsub hx (g.injective heq ▸ hy)
      · intro V hV hUV hVA
        have hUV' : U ⊆ g.symm '' V := by
          intro x hx
          exact ⟨g x, hUV ⟨x, hx, rfl⟩, g.symm_apply_apply x⟩
        have hVA' : g.symm '' V ⊆ Aᶜ := by
          rintro _ ⟨x, hx, rfl⟩ ha
          exact hVA hx ⟨g.symm x, ha, g.apply_symm_apply x⟩
        have hEq := hmax (g.symm '' V) (hV.image g.symm g.symm.continuous.continuousOn)
          hUV' hVA'
        calc
          V = g '' (g.symm '' V) := by
            ext x
            simp only [Set.mem_image]
            constructor
            · intro hx; exact ⟨g.symm x, ⟨x, hx, rfl⟩, g.apply_symm_apply x⟩
            · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
          _ = g '' U := congrArg (fun W : Set CurveComplex.SpherePort.Sphere => g '' W) hEq
  
  
    simp only [actualObjectFamily, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hO
    rcases hO with ⟨v, ⟨hv, hl⟩, rfl⟩ | ⟨v, ⟨_, _, hc⟩, rfl⟩
    · let a := (r ⟨v, hv⟩).val
      have hloop : a.map 0 = a.map 1 := by
        have hc : (markedArcEndset a).card = 1 := by
          rw [markedArcEndset_eq_classEndpoints, hr]
          exact hl
        by_contra hn
        have hc2 : (markedArcEndset a).card = 2 := Finset.card_pair hn
        omega
      let J : CurveComplex.SpherePort.JordanCurve := {
        map := M.sphere ∘ a.map
        continuous := M.sphere.continuous.comp a.continuous
        injective_except_ends := fun t u h => a.injective_except_loop_closure t u (M.sphere.injective h)
        closed := congrArg M.sphere hloop }
      have hJ : J.image = M.sphere '' actualObjectTrace M r {v} := by
        rw [actualObjectTrace_loop M r hv]
        exact Set.range_comp M.sphere a.map
      obtain ⟨p, hpmark, hpne⟩ := Finset.exists_mem_ne
        (by rw [M.cover.branch_card]; norm_num : 1 < M.cover.branch.card) (a.map 0)
      have hpJ : M.sphere p ∉ J.image := by
        rintro ⟨t, ht⟩
        have htp : a.map t = p := M.sphere.injective ht
        have htm : a.map t ∈ M.cover.branch := by simpa only [htp] using hpmark
        rcases a.marked_only_at_ends t htm with ht | ht
        · exact hpne (htp.symm.trans (congrArg a.map ht))
        · exact hpne ((htp.symm.trans (congrArg a.map ht)).trans hloop.symm)
      let P : CurveComplex.SpherePort.Chart J := {
        puncture := M.sphere p
        avoids := hpJ
        plane := puncturedSpherePlane (M.sphere p) }
      obtain ⟨U, V, hU, hV, _, _, hdisj, hne, _⟩ := hjregions J P
      have hback : M.sphere.symm '' J.image = actualObjectTrace M r {v} := by
        rw [hJ, ← image_comp, M.sphere.symm_comp_self, image_id]
      have hcU := hcomponent M.sphere.symm hU
      have hcV := hcomponent M.sphere.symm hV
      rw [hback] at hcU hcV
      letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
      have htraceClosed : IsClosed (actualObjectTrace M r {v}) :=
        (actualObjectTrace_compact M r {v}).isClosed
      refine ⟨M.sphere.symm '' U, M.sphere.symm '' V, hcU, hcV,
        complementComponent_open htraceClosed hcU, complementComponent_open htraceClosed hcV,
        (Set.disjoint_image_iff M.sphere.symm.injective).mpr hdisj, ?_⟩
      exact fun he => hne ((Set.image_injective.mpr M.sphere.symm.injective) he)
    ·
      obtain ⟨J, hJsub⟩ := actualEndpointObject_contains_JordanCircle M r hr hd v hc
      have hecard : (classEndpoints M v).card < M.cover.branch.card := by
        rw [M.cover.branch_card]
        rcases classEndpoints_card M v with h | h <;> omega
      obtain ⟨p, hpmark, hpends⟩ := Finset.exists_mem_notMem_of_card_lt_card hecard
      have hptrace : p ∉ actualObjectTrace M r (actualEndpointFibre M σ v) := by
        intro hx
        exact hpends (actualObjectTrace_endpoint_mark M r hr v hx hpmark)
      have hpJ : M.sphere p ∉ J.image := by
        intro hx
        obtain ⟨x, hx, he⟩ := hJsub hx
        exact hptrace (M.sphere.injective he ▸ hx)
      let P : CurveComplex.SpherePort.Chart J := {
        puncture := M.sphere p
        avoids := hpJ
        plane := puncturedSpherePlane (M.sphere p) }
      obtain ⟨SU, SV, hSU, hSV, hoSU, hoSV, hdSUV, _, _⟩ := hjregions J P
      let G := M.sphere '' actualObjectTrace M r (actualEndpointFibre M σ v)
      have hGclosed : IsClosed G :=
        ((actualObjectTrace_compact M r (actualEndpointFibre M σ v)).image M.sphere.continuous).isClosed
      have hGnd : IsNowhereDense G :=
        M.sphere.isEmbedding.isInducing.isNowhereDense_image
          ((actual_bad_graph_nowhereDense M r hr hd hbad).mono
            (actualObjectTrace_subset_graph M r (actualEndpointFibre M σ v)))
      obtain ⟨U, V, hU, hV, _, _, hdisj, hne⟩ :=
        two_complementComponents_refinement hJsub hSU hSV hoSU hoSV hdSUV
          (hGclosed.isNowhereDense_iff.mp hGnd)
      have hback : M.sphere.symm '' G = actualObjectTrace M r (actualEndpointFibre M σ v) := by
        rw [← image_comp, M.sphere.symm_comp_self, image_id]
      have hcU := hcomponent M.sphere.symm hU
      have hcV := hcomponent M.sphere.symm hV
      rw [hback] at hcU hcV
      letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
      have htraceClosed : IsClosed (actualObjectTrace M r (actualEndpointFibre M σ v)) :=
        (actualObjectTrace_compact M r (actualEndpointFibre M σ v)).isClosed
      refine ⟨M.sphere.symm '' U, M.sphere.symm '' V, hcU, hcV,
        complementComponent_open htraceClosed hcU, complementComponent_open htraceClosed hcV,
        (Set.disjoint_image_iff M.sphere.symm.injective).mpr hdisj, ?_⟩
      exact fun he => hne ((Set.image_injective.mpr M.sphere.symm.injective) he)
  have hnonfree : ∀ O : Finset (EssentialArcClass M), O ∈ actualObjectFamily M σ →
    ∀ g : Set S, IsComplementComponent (actualObjectTrace M r O) g →
    (∃ P ∈ actualObjectFamily M σ, P ≠ O ∧ actualObjectTrace M r P ⊆ closure g) →
    ∃ P ∈ actualObjectFamily M σ, ∃ h : Set S,
      IsComplementComponent (actualObjectTrace M r P) h ∧ h ⊂ g := by
    intro O hO g hgap hnfree
    have hboundary : ∀ O : Finset (EssentialArcClass M), O ∈ actualObjectFamily M σ →
      ∀ g : Set S, IsComplementComponent (actualObjectTrace M r O) g → (frontier g).Infinite := by
      intro O hO g hgap
      classical
      letI : T2Space S := M.sphere.symm.t2Space
      letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
      have hopen : IsOpen g := complementComponent_open
        (actualObjectTrace_compact M r O).isClosed hgap
      have hconnected := actualObjectTrace_connected M r hr hO
      have htraceNontriv : (actualObjectTrace M r O).Nontrivial := by
        obtain ⟨x, hx⟩ := hconnected.nonempty
        obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hx
        obtain ⟨huO, _⟩ := Set.mem_iUnion.mp hu
        exact (markedArc_image_nontrivial M (r u).val).mono
          (fun y hy => Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨huO, hy⟩⟩)
      have hfinite : ∀ (F : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)),
          F.Finite → ∀ v ∈ F, IsPreconnected Fᶜ := by
        intro F hF v hv
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
        let e := stereographic' 2 v
        have he : Topology.IsOpenEmbedding e.symm := e.symm.isOpenEmbedding (by simp [e])
        have hr : Set.range e.symm = {v}ᶜ := by
          simpa [e] using e.symm.image_source_eq_target
        have hpre : (e.symm ⁻¹' F).Finite := hF.preimage he.injective.injOn
        have hc := hpre.countable.isConnected_compl_of_one_lt_rank
          (by rw [← Module.finrank_eq_rank]; norm_num : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)))
        have hi : e.symm '' (e.symm ⁻¹' F)ᶜ = Fᶜ := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact hy
          · intro hx
            have hxv : x ≠ v := fun h => hx (h ▸ hv)
            have hxr : x ∈ Set.range e.symm := by rwa [hr]
            obtain ⟨y, rfl⟩ := hxr
            exact ⟨y, hx, rfl⟩
        rw [← hi]
        exact hc.isPreconnected.image _ he.continuous.continuousOn
      intro hf
      have hc : IsPreconnected ((frontier g)ᶜ) := by
        by_cases hn : (frontier g).Nonempty
        · obtain ⟨x, hx⟩ := hn
          let F := M.sphere '' frontier g
          have hF : F.Finite := hf.image _
          have hv : M.sphere x ∈ F := ⟨x, hx, rfl⟩
          have hpre := hfinite F hF (M.sphere x) hv
          have heq : M.sphere.symm '' Fᶜ = (frontier g)ᶜ := by
            ext y
            constructor
            · rintro ⟨z, hz, rfl⟩ hy
              exact hz ⟨M.sphere.symm z, hy, M.sphere.apply_symm_apply z⟩
            · intro hy
              refine ⟨M.sphere y, ?_, M.sphere.symm_apply_apply y⟩
              rintro ⟨z, hz, hzy⟩
              exact hy (M.sphere.injective hzy ▸ hz)
          rw [← heq]
          exact hpre.image _ M.sphere.symm.continuous.continuousOn
        · have he : frontier g = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
          rw [he, Set.compl_empty]
          letI : PreconnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
            isPreconnected_iff_preconnectedSpace.mp
              (isConnected_sphere (E := EuclideanSpace ℝ (Fin 3))
                (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num : (0 : ℝ) ≤ 1)).isPreconnected
          have hh := isPreconnected_univ.image M.sphere.symm M.sphere.symm.continuous.continuousOn
          simpa using hh
      have hsub : (frontier g)ᶜ ⊆ g := by
        apply hc.subset_of_closure_inter_subset hopen
        · obtain ⟨x, hx⟩ := hgap.1
          exact ⟨x, fun hxfr => (hopen.frontier_eq ▸ hxfr).2 hx, hx⟩
        · intro x hx
          by_contra hn
          exact hx.2 (hopen.frontier_eq ▸ ⟨hx.1, hn⟩)
      have hOsub : actualObjectTrace M r O ⊆ frontier g := by
        intro x hx
        by_contra hxf
        exact hgap.2.2.1 (hsub hxf) hx
      exact (hconnected.isPreconnected.infinite_of_nontrivial
        htraceNontriv) (hf.subset hOsub)
    have hopen : ∀ O : Finset (EssentialArcClass M), ∀ g : Set S,
        IsComplementComponent (actualObjectTrace M r O) g → IsOpen g := by
      intro O g hg
      exact complementComponent_open (actualObjectTrace_compact M r O).isClosed hg
    have hfront : ∀ O : Finset (EssentialArcClass M), ∀ g : Set S,
        IsComplementComponent (actualObjectTrace M r O) g → frontier g ⊆ actualObjectTrace M r O := by
      intro O g hg
      exact complementComponent_frontier_subset (actualObjectTrace_compact M r O).isClosed hg
    obtain ⟨P, hP, hne, hPg⟩ := hnfree
    obtain ⟨k, ⟨hk, _, hOk⟩, _⟩ := actualOtherObject_in_unique_gap M r hr hd hP hO hne
    obtain ⟨U, V, hU, hV, _, _, _, hUV⟩ := htwo P hP
    obtain ⟨h, hh, hhk⟩ : ∃ h : Set S,
        IsComplementComponent (actualObjectTrace M r P) h ∧ h ≠ k := by
      by_cases hUk : U = k
      · exact ⟨V, hV, fun hVk => hUV (hUk.trans hVk.symm)⟩
      · exact ⟨U, hU, hUk⟩
    have hdisj : Disjoint h k := complementComponents_disjoint hh hk hhk
    have hdisjcl : Disjoint h (closure k) := hdisj.closure_right (hopen P h hh)
    have hsubcompl : h ⊆ (actualObjectTrace M r O)ᶜ := by
      intro x hx hxO
      exact Set.disjoint_left.mp hdisjcl hx (hOk hxO)
    have hboundarynotO : ∃ y ∈ frontier h, y ∉ actualObjectTrace M r O := by
      by_contra hn
      push_neg at hn
      have hsub : frontier h ⊆ actualObjectTrace M r P ∩ actualObjectTrace M r O :=
        fun y hy => ⟨hfront P h hh hy, hn y hy⟩
      have hi := (actualDistinctObjectTraces_intersection M r hr hd hP hO hne).1
      exact hboundary P hP h hh (hi.finite.subset hsub)
    obtain ⟨y, hyh, hyO⟩ := hboundarynotO
    have hyg : y ∈ g := by
      have hycl := hPg (hfront P h hh hyh)
      by_contra hyng
      have hyfg : y ∈ frontier g := (hopen O g hgap).frontier_eq ▸ ⟨hycl, hyng⟩
      exact hyO (hfront O g hgap hyfg)
    have hmeet : (g ∩ h).Nonempty := Set.Nonempty.of_closure
      ⟨y, (hopen O g hgap).inter_closure ⟨hyg, frontier_subset_closure hyh⟩⟩
    obtain ⟨x, hxg, hxh⟩ := hmeet
    have hgeq : g = connectedComponentIn (actualObjectTrace M r O)ᶜ x :=
      (hgap.2.2.2 _ (isConnected_connectedComponentIn_iff.mpr (hgap.2.2.1 hxg))
        (hgap.2.1.isPreconnected.subset_connectedComponentIn hxg hgap.2.2.1)
        (connectedComponentIn_subset _ _)).symm
    have hsub : h ⊆ g := by
      rw [hgeq]
      exact hh.2.1.isPreconnected.subset_connectedComponentIn hxh hsubcompl
    refine ⟨P, hP, h, hh, hsub, ?_⟩
    intro hback
    exact hh.2.2.1 (hback hyg) (hfront P h hh hyh)
  let gap (O : Finset (EssentialArcClass M)) (g : Set S) : Prop :=
    O ∈ actualObjectFamily M σ ∧ IsComplementComponent (actualObjectTrace M r O) g
  let free (O : Finset (EssentialArcClass M)) (g : Set S) : Prop := gap O g ∧
    ∀ P ∈ actualObjectFamily M σ, P ≠ O → ¬ actualObjectTrace M r P ⊆ closure g
  have hsame : ∀ O (g h : Set S), gap O g → gap O h → g ⊆ h → g = h := by
    intro O g h hg hh hsub
    exact (hg.2.2.2.2 h hh.2.2.1 hsub hh.2.2.2.1).symm
  let candidates : Set S → Finset (Finset (EssentialArcClass M)) := fun g =>
    σ.powerset.filter (fun O => ∃ h, gap O h ∧ h ⊆ g)
  have hdesc : ∀ n : ℕ, ∀ g : Set S, (candidates g).card = n →
      ∀ O, gap O g → ∃ P h, free P h ∧ h ⊆ g := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro g hgn O hg
      by_cases hfree : free O g
      · exact ⟨O, g, hfree, Set.Subset.refl g⟩
      have hn : ¬ ∀ P ∈ actualObjectFamily M σ, P ≠ O →
          ¬ actualObjectTrace M r P ⊆ closure g := fun hf => hfree ⟨hg, hf⟩
      push_neg at hn
      obtain ⟨P, hP, h, hh, hhg, hgh⟩ := hnonfree O hg.1 g hg.2 hn
      have hcsub : candidates h ⊆ candidates g := by
        intro Q hQ
        obtain ⟨hQv, j, hj, hjh⟩ := Finset.mem_filter.mp hQ
        exact Finset.mem_filter.mpr ⟨hQv, j, hj, hjh.trans hhg⟩
      have hOm : O ∈ candidates g :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (actualObjectFamily_subset M σ hg.1),
          g, hg, Set.Subset.refl g⟩
      have hOn : O ∉ candidates h := by
        intro hO
        obtain ⟨_, j, hj, hjh⟩ := Finset.mem_filter.mp hO
        have hjg : j = g := hsame O j g hj hg (hjh.trans hhg)
        exact hgh (hjg ▸ hjh)
      have hlt : (candidates h).card < n := by
        rw [← hgn]
        apply Finset.card_lt_card
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hcsub, fun heq => hOn (heq ▸ hOm)⟩
      obtain ⟨Q, j, hj, hjh⟩ := ih (candidates h).card hlt h rfl P ⟨hP, hh⟩
      exact ⟨Q, j, hj, hjh.trans hhg⟩
  obtain ⟨a, ha⟩ := hne
  obtain ⟨O, hO, _⟩ := actualObjectFamily_cover M σ hbad ha
  obtain ⟨g, h, hg, hh, _, _, hdisj, _⟩ := htwo O hO
  obtain ⟨O₁, g₁, hg₁, hg₁g⟩ := hdesc (candidates g).card g rfl O ⟨hO, hg⟩
  obtain ⟨O₂, g₂, hg₂, hg₂h⟩ := hdesc (candidates h).card h rfl O ⟨hO, hh⟩
  exact ⟨O₁, O₂, g₁, g₂, hg₁.1.1, hg₂.1.1, hg₁.1.2, hg₂.1.2,
    actual_free_gap_is_face M hbad r hr hd hg₁.1.1 hg₁.1.2 hg₁.2,
    actual_free_gap_is_face M hbad r hr hd hg₂.1.1 hg₂.1.2 hg₂.2,
    hg₁.2, hg₂.2, hdisj.mono hg₁g hg₂h⟩
end CurveComplex.HyperellipticModel
