import RegionalUnpositionedFiniteLabelDescent
import C0CarriedBoundaryAnnulus
import BarycentricRelativeBridge
import FiniteLabelDescentTriangulatedDisk
import C0SourceBoundaryComparisonConstructors
import C0FiniteTriangulatedDisk
import C0SeamTransport
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.Basic
import CurveComplexGenusTwo.Foundations.EdgeHomotopy
import CurveComplexGenusTwo.Foundations.RealizationCW

attribute [local instance 2000] instDecidable_c0RelativeCarrierScaffold instDecidableEq_c0RelativeCarrierScaffold
attribute [local instance 3000] instDecidableEqFin
namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex
noncomputable local instance (priority := 5000) (S : Type) [TopologicalSpace S] : DecidableEq (Vertex S) := Classical.decEq _

noncomputable local instance (priority := 4000) {V : Type*}
    (D : AbstractSimplicialComplex V) : DecidableEq (C0RelativeCarrier.Face D) :=
  @Subtype.instDecidableEq (Finset V) (fun σ => σ ∈ D.faces)
    (fun a b => @Finset.decidableEq V (instDecidableEq_c0RelativeCarrierScaffold V) a b)

-- Exact finite based-loop surgery subgoal of the original approved Harer endpoint.
theorem source_c0_finite_curve_loop_surgery
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (v : Vertex S)
    (p : Path (realizationVertex (curveComplex S 0) v ((curveComplex S 0).singleton_mem v))
      (realizationVertex (curveComplex S 0) v ((curveComplex S 0).singleton_mem v)))
    (hp : IsFiniteAffineEdgePath (curveComplex S 0) p) :
    Path.Homotopic p (Path.refl _) := by
  classical
  have hRadialFillToBased
      {X : Type} [TopologicalSpace X] {a : X} (q : Path a a)
      (F : C(CurveComplex.FiniteArcDisk.ClosedDisk,X))
      (γ : C(unitInterval,CurveComplex.FiniteArcDisk.ClosedDisk))
      (hseam : γ 0 = γ 1)
      (A : ContinuousMap.HomotopyWith q.toContinuousMap (F.comp γ)
        (fun r : C(unitInterval,X) => r 0 = r 1)) :
      Path.Homotopic q (Path.refl a) := by
    let center : CurveComplex.FiniteArcDisk.ClosedDisk := ⟨0,by simp⟩
    have hscaled (t : unitInterval) (z : CurveComplex.FiniteArcDisk.ClosedDisk) :
        (1-(t:ℝ)) • z.val ∈ Metric.closedBall
          (0 : CurveComplex.FiniteArcDisk.DiskPlane) 1 := by
      rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr t.property.2)]
      have hz : ‖z.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using z.property
      nlinarith [norm_nonneg z.val,t.property.1]
    let H : ContinuousMap.HomotopyWith (F.comp γ)
        (ContinuousMap.const unitInterval (F center))
        (fun r : C(unitInterval,X) => r 0 = r 1) := {
      toFun := fun u => F ⟨(1-(u.1:ℝ)) • (γ u.2).val,hscaled u.1 (γ u.2)⟩
      continuous_toFun := F.continuous.comp
        (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp (γ.continuous.comp continuous_snd))).subtype_mk _)
      map_zero_left := by intro t; simp
      map_one_left := by intro t; simp [center]
      prop' := by intro t; change F _ = F _; congr 1; apply Subtype.ext
                  exact congrArg (fun z => (1-(t:ℝ)) • z.val) hseam }
    exact C0RelativeCarrier.based_loop_nullhomotopic_of_seam_preserving_free_contraction
      q (F center) (A.trans H)
  have hActualDiskTransportToBased
      {X : Type} [TopologicalSpace X] {a : X} (q : Path a a)
      (M : CurveComplex.FiniteArcDisk.FiniteDiskModel)
      (L : PreAbstractSimplicialComplex (Fin M.vertexCount))
      (e : RealizationPoint (C0RelativeCarrier.barycentricSubdivision M.complex) ≃ₜ
        RealizationPoint M.complex)
      (j : RealizationPoint (C0RelativeCarrier.boundarySubdivision M.complex L) ≃ₜ
        RealizationPoint M.boundary)
      (hj : ∀ y, e (fullToAmbient (C0RelativeCarrier.barycentricSubdivision M.complex)
        (fun σ : C0RelativeCarrier.Face M.complex => σ.val ∈ L.faces) y) =
          M.boundaryInclusion (j y))
      (b : C(RealizationPoint (C0RelativeCarrier.boundarySubdivision M.complex L),X))
      (γ : C(unitInterval,RealizationPoint (C0RelativeCarrier.boundarySubdivision M.complex L)))
      (hγ : γ 0 = γ 1)
      (f : C(RealizationPoint (C0RelativeCarrier.barycentricSubdivision M.complex),X))
      (hf : ∀ y, f (fullToAmbient (C0RelativeCarrier.barycentricSubdivision M.complex)
        (fun σ : C0RelativeCarrier.Face M.complex => σ.val ∈ L.faces) y) = b y)
      (A : ContinuousMap.HomotopyWith q.toContinuousMap (b.comp γ)
        (fun r : C(unitInterval,X) => r 0 = r 1)) :
      Path.Homotopic q (Path.refl a) := by
    let F : C(CurveComplex.FiniteArcDisk.ClosedDisk,X) :=
      f.comp ((⟨e.symm,e.symm.continuous⟩ : C(RealizationPoint M.complex,_)).comp
        (⟨M.diskHome.symm,M.diskHome.symm.continuous⟩ : C(CurveComplex.FiniteArcDisk.ClosedDisk,_)))
    let δ : C(unitInterval,CurveComplex.FiniteArcDisk.ClosedDisk) :=
      (⟨M.diskHome,M.diskHome.continuous⟩ : C(RealizationPoint M.complex,_)).comp
        (M.boundaryInclusion.comp
          ((⟨j,j.continuous⟩ : C(RealizationPoint (C0RelativeCarrier.boundarySubdivision M.complex L),_)).comp γ))
    have hδ : δ 0 = δ 1 := congrArg
      (fun y => M.diskHome (M.boundaryInclusion (j y))) hγ
    have hBoundaryLiteral : b.comp γ = F.comp δ := by
      ext t
      change b (γ t) = f (e.symm (M.diskHome.symm
        (M.diskHome (M.boundaryInclusion (j (γ t))))))
      rw [M.diskHome.symm_apply_apply, ← hj (γ t), e.symm_apply_apply, hf]
    exact hRadialFillToBased q F δ hδ (A.cast rfl hBoundaryLiteral)
  obtain ⟨n,z,E,hx,hy,hAffine,hpEq⟩ := hp
  by_cases hn : n = 0
  · subst n
    have heq : p = Path.refl _ := by
      ext t
      rw [hpEq]
      simp [Path.concat_zero, ← hx]
    exact heq ▸ Path.Homotopic.refl _
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let Fv := CurveComplex.C0BoundaryCorrespondence.loopSupport S v n z
  obtain ⟨x,R,hR,htarget,G,⟨C⟩⟩ :=
    CurveComplex.C0BoundaryCorrespondence.SourceConstructors.source_c0_finite_support_bordered_regions_and_arc_comparison_exists
        S g hg hS Fv
  -- Literal Q geometry reused from the frozen original body.
  letI : ClosedSurface S := Classical.choice hS.2.1
  letI : Nonempty S := hS.1
  let D : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm '' Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
  let chart := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let center := chart x
  let O : Set S := chart.symm '' Metric.ball center R
  let Q := ↥Oᶜ
  let boundaryCircle : Set S := chart.symm '' Metric.sphere center R
  have hballTarget : Metric.ball center R ⊆ chart.target :=
    Metric.ball_subset_closedBall.trans htarget
  have hOopen : IsOpen O :=
    chart.symm.isOpen_image_of_subset_source Metric.isOpen_ball hballTarget
  have hQcompact : IsCompact (Oᶜ : Set S) := hOopen.isClosed_compl.isCompact
  have hOD : O ⊆ D := Set.image_mono Metric.ball_subset_closedBall
  have hBoundaryInQ : boundaryCircle ⊆ Oᶜ := by
    rintro y ⟨z, hz, rfl⟩ ⟨u, hu, heq⟩
    have hzTarget : z ∈ chart.target := htarget (Metric.sphere_subset_closedBall hz)
    have huTarget : u ∈ chart.target := hballTarget hu
    have huz : u = z := chart.symm.injOn huTarget hzTarget heq
    rw [huz] at hu
    have hdist := Metric.mem_sphere.mp hz
    exact (ne_of_lt (Metric.mem_ball.mp hu)) hdist
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp hQcompact
  let boundaryQ : Set Q := {y | y.val ∈ boundaryCircle}
  have hSphereConnected : IsConnected (Metric.sphere center R) :=
    isConnected_sphere
      (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num) center hR.le
  have hBoundaryConnected : IsConnected boundaryCircle := by
    exact hSphereConnected.image chart.symm
      (chart.symm.continuousOn.mono (Metric.sphere_subset_closedBall.trans htarget))
  have hclosureO : closure O = D := by
    have hDc : IsCompact D :=
      (isCompact_closedBall center R).image_of_continuousOn (chart.symm.continuousOn.mono htarget)
    have hcb : closure (Metric.ball center R) = Metric.closedBall center R :=
      closure_ball center (ne_of_gt hR)
    have hc : ContinuousOn chart.symm (closure (Metric.ball center R)) := by
      rw [hcb]
      exact chart.symm.continuousOn.mono htarget
    apply Set.Subset.antisymm (closure_minimal hOD hDc.isClosed)
    change chart.symm '' Metric.closedBall center R ⊆ closure (chart.symm '' Metric.ball center R)
    rw [← hcb]
    exact hc.image_closure
  have hfrontierO : frontier O = boundaryCircle := by
    rw [hOopen.frontier_eq, hclosureO]
    ext y
    constructor
    · rintro ⟨⟨z,hz,rfl⟩, hn⟩
      refine ⟨z, Metric.mem_sphere.mpr ?_, rfl⟩
      apply le_antisymm (Metric.mem_closedBall.mp hz)
      apply not_lt.mp
      intro hb
      exact hn ⟨z,Metric.mem_ball.mpr hb,rfl⟩
    · intro hy
      exact ⟨(Set.image_mono Metric.sphere_subset_closedBall) hy, hBoundaryInQ hy⟩
  have hremoveDiskConnected (C : Set S) (hC : IsConnected C) (hDC : D ⊆ C) :
      IsConnected (C \ O) := by
    have hbF : boundaryCircle ⊆ C \ O := fun y hy =>
      ⟨hDC ((Set.image_mono Metric.sphere_subset_closedBall) hy), hBoundaryInQ hy⟩
    refine ⟨hBoundaryConnected.nonempty.mono hbF, ?_⟩
    intro U V hU hV hcover hUne hVne
    by_contra hn
    have hside : boundaryCircle ⊆ U ∨ boundaryCircle ⊆ V := by
      by_cases hbu : boundaryCircle ⊆ U
      · exact Or.inl hbu
      · right
        intro y hy
        by_contra hyv
        have hyU : y ∈ U := (hcover (hbF hy)).resolve_right hyv
        obtain ⟨z,hz,hzu⟩ := Set.not_subset.mp hbu
        have hzV : z ∈ V := (hcover (hbF hz)).resolve_left hzu
        obtain ⟨w,hw⟩ := hBoundaryConnected.isPreconnected U V hU hV
          (fun z hz => hcover (hbF hz)) ⟨y,hy,hyU⟩ ⟨z,hz,hzV⟩
        exact hn ⟨w,hbF hw.1,hw.2⟩
    have hkill (U V : Set S) (hU : IsOpen U) (hV : IsOpen V)
        (hcover : C \ O ⊆ U ∪ V)
        (hUne : ((C \ O) ∩ U).Nonempty) (hVne : ((C \ O) ∩ V).Nonempty)
        (hn : ¬ ((C \ O) ∩ (U ∩ V)).Nonempty) (hbu : boundaryCircle ⊆ U) : False := by
      have hDc : IsClosed D := by rw [← hclosureO]; exact isClosed_closure
      have hVo : IsOpen (V \ D) := hV.sdiff hDc
      have hVout (y : S) (hy : y ∈ (C \ O) ∩ V) : y ∉ D := by
        intro hyD
        have hyb : y ∈ boundaryCircle := by
          rw [← hfrontierO, hOopen.frontier_eq, hclosureO]
          exact ⟨hyD,hy.1.2⟩
        exact hn ⟨y,hy.1,hbu hyb,hy.2⟩
      have hcCover : C ⊆ (U ∪ O) ∪ (V \ D) := by
        intro y hy
        by_cases hyo : y ∈ O
        · exact Or.inl (Or.inr hyo)
        · rcases hcover ⟨hy,hyo⟩ with hu | hv
          · exact Or.inl (Or.inl hu)
          · exact Or.inr ⟨hv,hVout y ⟨⟨hy,hyo⟩,hv⟩⟩
      obtain ⟨u,hu⟩ := hUne
      obtain ⟨v,hv⟩ := hVne
      obtain ⟨y,hy⟩ := hC.isPreconnected (U ∪ O) (V \ D)
        (hU.union hOopen) hVo hcCover ⟨u,hu.1.1,Or.inl hu.2⟩
        ⟨v,hv.1.1,hv.2,hVout v hv⟩
      have hyo : y ∉ O := fun hh => hy.2.2.2 (hOD hh)
      have hyU : y ∈ U := hy.2.1.resolve_right hyo
      exact hn ⟨y,⟨hy.1,hyo⟩,hyU,hy.2.2.1⟩
    rcases hside with hbu | hbv
    · exact hkill U V hU hV hcover hUne hVne hn hbu
    · apply hkill V U hV hU (fun y hy => (hcover hy).symm) hVne hUne _ hbv
      intro hh
      obtain ⟨y,hy⟩ := hh
      exact hn ⟨y,hy.1,hy.2.2,hy.2.1⟩
  have hQconnected : IsConnected (Oᶜ : Set S) := by
    simpa only [Set.compl_eq_univ_sdiff] using
      hremoveDiskConnected Set.univ isConnected_univ (Set.subset_univ D)
  have hQfrontier : frontier (Oᶜ : Set S) = boundaryCircle := by
    simpa only [frontier_compl] using hfrontierO
  have hDclosed : IsClosed D := by
    rw [← hclosureO]
    exact isClosed_closure
  have hBoundaryExterior : boundaryCircle ⊆ closure Dᶜ := by
    rintro y ⟨z, hz, rfl⟩
    have hzT := htarget (Metric.sphere_subset_closedBall hz)
    have hzCl : z ∈ closure (Metric.closedBall center R)ᶜ := by
      have hf : z ∈ frontier (Metric.closedBall center R) := by
        rw [frontier_closedBall center (ne_of_gt hR)]
        exact hz
      rw [frontier_eq_closure_inter_closure] at hf
      exact hf.2
    have hzCT : z ∈ closure (chart.target ∩ (Metric.closedBall center R)ᶜ) :=
      chart.open_target.inter_closure ⟨hzT, hzCl⟩
    apply (chart.symm.continuousOn z hzT).mono Set.inter_subset_left |>.mem_closure hzCT
    intro u hu
    rintro ⟨v, hv, heq⟩
    have huv : v = u := chart.symm.injOn (htarget hv) hu.1 heq
    exact hu.2 (huv ▸ hv)
  have hQregular : closure (interior (Oᶜ : Set S)) = Oᶜ := by
    apply Set.Subset.antisymm hOopen.isClosed_compl.closure_interior_subset
    intro y hy
    have hDout : Dᶜ ⊆ interior (Oᶜ : Set S) :=
      interior_maximal (Set.compl_subset_compl.mpr hOD) hDclosed.isOpen_compl
    by_cases hyD : y ∈ D
    · have hyB : y ∈ boundaryCircle := by
        rw [← hfrontierO,hOopen.frontier_eq,hclosureO]
        exact ⟨hyD,hy⟩
      exact closure_mono hDout (hBoundaryExterior hyB)
    · exact subset_closure (hDout hyD)
  have hLiteralQIntrinsicRangeBridge
      (hfront : frontier (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.openDisk S x R)ᶜ =
        CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryCircle S x R) :
      ∃ e : CurveComplex.C0BoundaryCorrespondence.IntrinsicEssentialArc S x R
          (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.openDisk S x R)ᶜ ≃
          CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.EssentialProperArc S x R,
        (∀ a t, (e a).val.val t = a.val.val t) ∧
        ∀ a b, CurveComplex.C0BoundaryCorrespondence.intrinsicArcRel S x R
            (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.openDisk S x R)ᶜ a b ↔
          CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.arcRel S x R (e a) (e b) := by
    let forward : CurveComplex.C0BoundaryCorrespondence.IntrinsicEssentialArc S x R
        (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.openDisk S x R)ᶜ →
        CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.EssentialProperArc S x R := fun a =>
      ⟨⟨a.val.val,a.val.property.1,a.val.property.2.1,a.val.property.2.2.1,
        fun t ht => by simpa only [hfront, CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ, Set.mem_setOf_eq] using a.val.property.2.2.2 t ht⟩,a.property⟩
    let backward : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.EssentialProperArc S x R →
        CurveComplex.C0BoundaryCorrespondence.IntrinsicEssentialArc S x R
        (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.openDisk S x R)ᶜ := fun a =>
      ⟨⟨a.val.val,a.val.property.1,a.val.property.2.1,a.val.property.2.2.1,
        fun t ht => by simpa only [hfront, CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ, Set.mem_setOf_eq] using a.val.property.2.2.2 t ht⟩,a.property⟩
    let e := Equiv.mk forward backward (fun a => by apply Subtype.ext; apply Subtype.ext; rfl)
      (fun a => by apply Subtype.ext; apply Subtype.ext; rfl)
    refine ⟨e,(fun _ _ => rfl),?_⟩
    intro a b
    constructor
    · rintro ⟨H,hB,hF,hRange⟩
      exact ⟨H,hB,hRange⟩
    · rintro ⟨H,hB,hRange⟩
      refine ⟨H,hB,?_,hRange⟩
      simpa only [hfront] using hB
  obtain ⟨qArcEquiv,hArcLiteral,hArcRelation⟩ := hLiteralQIntrinsicRangeBridge hQfrontier
  let qVertexEquiv := Quot.congr qArcEquiv hArcRelation
  have hArcRange (a : CurveComplex.C0BoundaryCorrespondence.IntrinsicEssentialArc S x R Oᶜ) :
      Set.range (qArcEquiv a).val.val = Set.range a.val.val := by
    exact congrArg Set.range (funext (hArcLiteral a))
  have hLiteralCommonFamilyFaceBridge
      (τ : Finset (CurveComplex.C0BoundaryCorrespondence.IntrinsicArcVertex S x R Oᶜ)) :
      (∃ rep : ↥τ → CurveComplex.C0BoundaryCorrespondence.IntrinsicEssentialArc S x R Oᶜ,
        (∀ u, Quot.mk (CurveComplex.C0BoundaryCorrespondence.intrinsicArcRel S x R Oᶜ) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)) ↔
      (∃ rep : ↥τ → CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.EssentialProperArc S x R,
        (∀ u, Quot.mk (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.arcRel S x R)
          (rep u) = qVertexEquiv u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)) := by
    constructor
    · rintro ⟨rep,hclasses,hdisjoint⟩
      refine ⟨fun u => qArcEquiv (rep u),?_,?_⟩
      · intro u
        rw [← hclasses u]
        rfl
      · intro u w huw
        simpa only [hArcRange] using hdisjoint u w huw
    · rintro ⟨rep,hclasses,hdisjoint⟩
      refine ⟨fun u => qArcEquiv.symm (rep u),?_,?_⟩
      · intro u
        apply qVertexEquiv.injective
        change Quot.mk (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.arcRel S x R)
          (qArcEquiv (qArcEquiv.symm (rep u))) = qVertexEquiv u.val
        rw [qArcEquiv.apply_symm_apply,hclasses]
      · intro u w huw
        have hu := hArcRange (qArcEquiv.symm (rep u))
        have hw := hArcRange (qArcEquiv.symm (rep w))
        rw [qArcEquiv.apply_symm_apply] at hu hw
        rw [← hu,← hw]
        exact hdisjoint u w huw
  have hActualSourceArcAnchor
      (bc : CurveComplex.C0BoundaryCorrespondence.BoundaryCorrespondence S x R G C v n z E p) :
      Nonempty (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.EssentialProperArc S x R) := by
    let first : Fin bc.curveWord.edgeCount := ⟨0,bc.curve_nonempty⟩
    exact ⟨C.includedArc _ (bc.curve_edge_compatible first) (bc.edgeArc first)⟩
  have hN6DiskFill
      (bc : CurveComplex.C0BoundaryCorrespondence.BoundaryCorrespondence S x R G C v n z E p)
      (allowed : OriginalBoundaryArc.ArcVertex S x R → Prop)
      (d : CurveComplex.FiniteArcDisk.LabelledDisk bc.arcDomain
        (OriginalBoundaryArc.arcComplex S x R) bc.arcLabel bc.arcWord allowed) :
      Path.Homotopic p (Path.refl _) := by
    let D₁ := d.disk.complex
    let L : PreAbstractSimplicialComplex (Fin d.disk.vertexCount) :=
      d.disk.boundary.toPreAbstractSimplicialComplex.map (fun u => u.val)
    have hLD : ∀ σ ∈ L.faces, σ ∈ D₁.faces := by
      rintro σ ⟨τ, hτ, rfl⟩
      exact d.disk.boundary_faces τ hτ
    obtain ⟨e, he_weight, he_boundary⟩ :=
      C0RelativeCarrier.finite_barycentric_realization_homeomorph_relative D₁ L hLD
    obtain ⟨_, _, j, hj, hγ, _, _, b, hb, ⟨A⟩⟩ :=
      CurveComplex.C0BoundaryCorrespondence.CarriedAnnulus.source_c0_boundary_correspondence_carried_annulus
        S g hg hS x R hR htarget v n z E p G C bc allowed d e
          (by
            intro a w
            rw [he_weight]
            apply Finset.sum_congr rfl
            intro σ _
            by_cases hw : w ∈ σ.val <;> simp only [hw, ite_true, ite_false])
          he_boundary
    let P : C0RelativeCarrier.Face D₁ → Vertex S → Prop := fun σ w =>
      OriginalArcFaceCarriers.faceCarrier S x R (σ.val.image d.label) w
    have hanti : ∀ σ τ : C0RelativeCarrier.Face D₁, σ.val ⊆ τ.val →
        ∀ w : Vertex S, P τ w → P σ w := by
      intro σ τ hστ w hw
      exact OriginalArcFaceCarriers.faceCarrier_antitone S x R _ _
        (Finset.image_mono d.label hστ) w hw
    have hcontract : ∀ σ : C0RelativeCarrier.Face D₁,
        ContractibleSpace (RealizationPoint (fullSubcomplex (curveComplex S 0) (P σ))) := by
      intro σ
      have hdec : (inferInstance : DecidableEq (Vertex S)) =
          (fun a b => Quotient.decidableEq a b) := Subsingleton.elim _ _
      exact Eq.mpr
        (congrArg (fun inst : DecidableEq (Vertex S) =>
          ContractibleSpace (RealizationPoint
            (@fullSubcomplex (Vertex S) inst (curveComplex S 0) (P σ)))) hdec)
        (OriginalArcFaceCarriers.nonempty_small_faceCarrier_contractible
          S x R g hg hS hR htarget (σ.val.image d.label)
          (d.label_faces σ.val σ.property) (d.label_image_card σ.val σ.property))
    obtain ⟨f, hf, _⟩ := C0RelativeCarrier.finite_antitone_full_carrier_relative_extension
      D₁ d.disk.face_card L hLD (curveComplex S 0) P hanti hcontract b hb
    exact hActualDiskTransportToBased p d.disk L e j hj b _ hγ f hf A
  have hAlignment : CurveComplex.C0BoundaryCorrespondence.FaceSystemAlignment S x R := by
    intro τ a b ha hb had hbd
    by_cases hne : τ.Nonempty
    · exact OriginalArcFaceCarriers.simultaneousRepresentatives_alignment
        S x R g hg hS hR htarget τ ⟨hne, a, ha, had⟩
        ⟨a, ha, had⟩ ⟨b, hb, hbd⟩
    · let H : AmbientIsotopy (OriginalBoundaryArc.Q S x R) :=
        { map := ⟨fun u => u.2, continuous_snd⟩
          homeomorphism_at := fun _ => ⟨Homeomorph.refl _, fun _ => rfl⟩
          at_zero := fun _ => rfl }
      refine ⟨H, ?_, ?_⟩
      · intro t
        exact Set.image_id _
      · intro u
        exact (hne ⟨u.val, u.property⟩).elim
  have hN5 : (n = 0 ∧ p = Path.refl _) ∨ Nonempty
      (CurveComplex.C0BoundaryCorrespondence.BoundaryCorrespondence S x R G C v n z E p) := by
    exact CurveComplex.C0BoundaryCorrespondence.source_c0_curve_to_arc_boundary_correspondence
      S x R g hg hS v p ⟨n, z, E, hx, hy, hAffine, hpEq⟩
      n z E hx hy hAffine hpEq hR htarget G C hAlignment
  obtain ⟨bc⟩ := hN5.resolve_left (fun hzero => hn hzero.1)
  obtain ⟨aQ⟩ := hActualSourceArcAnchor bc
  have hFaceEquiv
      (τ : Finset (CurveComplex.C0BoundaryCorrespondence.IntrinsicArcVertex S x R Oᶜ)) :
      τ ∈ CurveComplex.C0BoundaryCorrespondence.intrinsicArcFaces S x R Oᶜ ↔
        τ.image qVertexEquiv ∈ (OriginalBoundaryArc.arcComplex S x R).faces := by
    constructor
    · rintro ⟨hne, hrep⟩
      obtain ⟨rep, hclass, hd⟩ := (hLiteralCommonFamilyFaceBridge τ).mp hrep
      let inv : ↥(τ.image qVertexEquiv) → ↥τ := fun u =>
        ⟨qVertexEquiv.symm u.val, by
          obtain ⟨w, hw, he⟩ := Finset.mem_image.mp u.property
          simpa only [← he, qVertexEquiv.symm_apply_apply] using hw⟩
      refine ⟨hne.image _, fun u => rep (inv u), ?_, ?_⟩
      · intro u
        exact (hclass (inv u)).trans (qVertexEquiv.apply_symm_apply u.val)
      · intro u w huw
        apply hd
        intro he
        apply huw
        apply Subtype.ext
        exact qVertexEquiv.symm.injective (congrArg Subtype.val he)
    · rintro ⟨hne, rep, hclass, hd⟩
      refine ⟨Finset.image_nonempty.mp hne, (hLiteralCommonFamilyFaceBridge τ).mpr ?_⟩
      let f : ↥τ → ↥(τ.image qVertexEquiv) := fun u =>
        ⟨qVertexEquiv u.val, Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩⟩
      refine ⟨fun u => rep (f u), fun u => hclass (f u), ?_⟩
      intro u w huw
      apply hd
      intro he
      apply huw
      apply Subtype.ext
      exact qVertexEquiv.injective (congrArg Subtype.val he)
  let labels0 : Fin bc.arcDomainCount →
      CurveComplex.C0BoundaryCorrespondence.IntrinsicArcVertex S x R Oᶜ :=
    fun i => qVertexEquiv.symm (bc.arcLabel i)
  let aF := qArcEquiv.symm aQ
  have hlabels0 : ∀ σ, σ ∈ bc.arcDomain.faces →
      σ.image labels0 ∈ CurveComplex.C0BoundaryCorrespondence.intrinsicArcFaces S x R Oᶜ := by
    intro σ hσ
    apply (hFaceEquiv _).mpr
    have him : (σ.image labels0).image qVertexEquiv = σ.image bc.arcLabel := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro i _
      exact qVertexEquiv.apply_symm_apply _
    rw [him]
    exact bc.arcLabel_faces σ hσ
  have hN0 : ∃ (steps : ℕ) (labels : ℕ → Fin bc.arcDomainCount →
        CurveComplex.C0BoundaryCorrespondence.IntrinsicArcVertex S x R Oᶜ),
      labels 0 = labels0 ∧
      (∀ t ≤ steps, ∀ σ, σ ∈ bc.arcDomain.faces →
        σ.image (labels t) ∈ CurveComplex.C0BoundaryCorrespondence.intrinsicArcFaces S x R Oᶜ) ∧
      (∀ t < steps, ∀ σ, σ ∈ bc.arcDomain.faces →
        σ.image (labels t) ∪ σ.image (labels (t + 1)) ∈
          CurveComplex.C0BoundaryCorrespondence.intrinsicArcFaces S x R Oᶜ) ∧
      (∀ σ, σ ∈ bc.arcDomain.faces →
        insert (Quot.mk (CurveComplex.C0BoundaryCorrespondence.intrinsicArcRel S x R Oᶜ) aF)
          (σ.image (labels steps)) ∈
            CurveComplex.C0BoundaryCorrespondence.intrinsicArcFaces S x R Oᶜ) := by
    exact regional_original_finite_label_descent_exists
      S g hg hS x R hR htarget Oᶜ hQcompact hQconnected hBoundaryInQ
      (Set.Subset.refl _) hQregular (Fin 0) (fun i => Fin.elim0 i)
      (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
      (by simpa only [Set.iUnion_of_empty, Set.union_empty] using hQfrontier)
      (Fin bc.arcDomainCount) bc.arcDomain labels0 aF hlabels0
  obtain ⟨steps, labels, hzero, hfaces, hcommon, hterminal⟩ := hN0
  let arcLabels : ℕ → Fin bc.arcDomainCount → OriginalBoundaryArc.ArcVertex S x R :=
    fun t i => qVertexEquiv (labels t i)
  have himage (σ : Finset (Fin bc.arcDomainCount)) (t : ℕ) :
      (σ.image (labels t)).image qVertexEquiv = σ.image (arcLabels t) := by
    exact Finset.image_image
  have harcZero : arcLabels 0 = bc.arcLabel := by
    funext i
    change qVertexEquiv (labels 0 i) = bc.arcLabel i
    rw [hzero]
    exact qVertexEquiv.apply_symm_apply _
  have harcFaces : ∀ t ≤ steps, ∀ σ, σ ∈ bc.arcDomain.faces →
      σ.image (arcLabels t) ∈ (OriginalBoundaryArc.arcComplex S x R).faces := by
    intro t ht σ hσ
    simpa only [himage] using (hFaceEquiv _).mp (hfaces t ht σ hσ)
  have harcCommon : ∀ t < steps, ∀ σ, σ ∈ bc.arcDomain.faces →
      σ.image (arcLabels t) ∪ σ.image (arcLabels (t + 1)) ∈
        (OriginalBoundaryArc.arcComplex S x R).faces := by
    intro t ht σ hσ
    simpa only [Finset.image_union, himage] using (hFaceEquiv _).mp (hcommon t ht σ hσ)
  have hanchor : qVertexEquiv
      (Quot.mk (CurveComplex.C0BoundaryCorrespondence.intrinsicArcRel S x R Oᶜ) aF) =
        Quot.mk (OriginalBoundaryArc.arcRel S x R) aQ := by
    change Quot.mk _ (qArcEquiv (qArcEquiv.symm aQ)) = _
    rw [qArcEquiv.apply_symm_apply]
  have harcTerminal : ∀ σ, σ ∈ bc.arcDomain.faces →
      insert (Quot.mk (OriginalBoundaryArc.arcRel S x R) aQ) (σ.image (arcLabels steps)) ∈
        (OriginalBoundaryArc.arcComplex S x R).faces := by
    intro σ hσ
    simpa only [Finset.image_insert, hanchor, himage] using (hFaceEquiv _).mp (hterminal σ hσ)
  obtain ⟨d⟩ := CurveComplex.FiniteArcDisk.finite_label_descent_triangulated_disk
    bc.arcDomain (OriginalBoundaryArc.arcComplex S x R) bc.arcLabel bc.arcWord
    arcLabels steps (Quot.mk (OriginalBoundaryArc.arcRel S x R) aQ)
    harcZero harcFaces harcCommon harcTerminal
  exact hN6DiskFill bc _ d

end CurveComplexGenusTwo.SourceTopology
