import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.ProperPairDiagram

open Set Topology Schoenflies Filter Metric
open CurveComplex.SphereGapFinish
namespace CurveComplex.HyperellipticModel

/-- Sending a compactification's unique infinity point to the inversion pole
produces a proper closed embedding after inversion. -/
theorem onePoint_injective_inversion_closedEmbedding
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (q : C(OnePoint X,Plane)) (hq : Function.Injective q) :
    IsClosedEmbedding (fun x : X => invert (q OnePoint.infty) (q (OnePoint.some x))) := by
  let p := q OnePoint.infty
  have hne (x : X) : q (OnePoint.some x) ≠ p := by
    intro h
    have he := hq h
    exact OnePoint.coe_ne_infty x he
  have hc : Continuous (fun x : X => invert p (q (OnePoint.some x))) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hqx : ContinuousAt (fun z : X => q (OnePoint.some z)) x := (q.continuous.comp OnePoint.continuous_coe).continuousAt
    exact (continuousAt_invert (hne x)).comp (f := fun z : X => q (OnePoint.some z)) hqx
  have hi : Function.Injective (fun x : X => invert p (q (OnePoint.some x))) := by
    intro x y h
    exact OnePoint.coe_injective (hq (invert_injective p h))
  have ht : Tendsto (fun x : X => q (OnePoint.some x)) (cocompact X) (𝓝 p) := by
    have h := OnePoint.continuousAt_infty'.mp q.continuous.continuousAt
    simpa only [coclosedCompact_eq_cocompact,Function.comp_def] using h
  have hd : Tendsto (fun x : X => dist (q (OnePoint.some x)) p) (cocompact X) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using ht.dist (tendsto_const_nhds (x := p)),Filter.Eventually.of_forall ?_⟩
    intro x
    exact dist_pos.mpr (hne x)
  have hp : IsProperMap (fun x : X => invert p (q (OnePoint.some x))) := by
    apply isProperMap_iff_tendsto_cocompact.mpr
    refine ⟨hc,tendsto_cocompact_of_tendsto_dist_comp_atTop p ?_⟩
    simpa only [dist_invert_center,Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hd
  exact IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr ⟨hc,hi,hp.isClosedMap⟩

/-- Invert a proper embedding away from an actual avoided pole, including the
single compactification point. -/
noncomputable def invertedProperCompactification {X : Type} [TopologicalSpace X]
    (h : C(X,Plane)) (a : Plane) : OnePoint X → Plane :=
  invertAtInfinity a ∘ OnePoint.map h

theorem invertedProperCompactification_continuous
    {X : Type} [TopologicalSpace X] [T2Space X]
    (h : C(X,Plane)) (hh : IsProperMap h) (a : Plane) (ha : a ∉ range h) :
    Continuous (invertedProperCompactification h a) := by
  have hmap : Continuous (OnePoint.map h) := by
    apply OnePoint.continuous_map h.continuous
    simpa only [coclosedCompact_eq_cocompact] using (isProperMap_iff_tendsto_cocompact.mp hh).2
  apply continuous_iff_continuousAt.mpr
  intro z
  cases z with
  | infty => exact (invertAtInfinity_continuousAt_infty a).comp hmap.continuousAt
  | coe x =>
    apply OnePoint.continuousAt_coe.mpr
    change ContinuousAt (fun x => invert a (h x)) x
    exact (continuousAt_invert (fun he => ha ⟨x,he⟩)).comp h.continuous.continuousAt

theorem invertedProperCompactification_injective
    {X : Type} [TopologicalSpace X]
    (h : C(X,Plane)) (hh : Function.Injective h) (a : Plane) (ha : a ∉ range h) :
    Function.Injective (invertedProperCompactification h a) := by
  intro x y hxy
  cases x with
  | infty =>
    cases y with
    | infty => rfl
    | coe y =>
      change a = invert a (h y) at hxy
      exact False.elim (ha ⟨y,invert_eq_center_iff.mp hxy.symm⟩)
  | coe x =>
    cases y with
    | infty =>
      change invert a (h x) = a at hxy
      exact False.elim (ha ⟨x,invert_eq_center_iff.mp hxy⟩)
    | coe y =>
      exact congrArg OnePoint.some (hh (invert_injective a hxy))

noncomputable def pairPlaneHomeomorph : (ℝ × ℝ) ≃ₜ Plane :=
  (Homeomorph.piFinTwo (fun _ : Fin 2 => ℝ)).symm.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.symm

noncomputable def standardClosedStrip : C(ℝ × unitInterval,Plane) :=
  ⟨fun z => Plane.mk z.1 z.2,by fun_prop⟩

noncomputable def standardBoundaryLine (w : ℝ) : C(ℝ,Plane) :=
  ⟨fun s => Plane.mk s w,by fun_prop⟩

theorem standardClosedStrip_closedEmbedding : IsClosedEmbedding standardClosedStrip := by
  have he : IsClosedEmbedding (Prod.map (id : ℝ → ℝ) (Subtype.val : unitInterval → ℝ)) :=
    IsClosedEmbedding.id.prodMap isClosed_Icc.isClosedEmbedding_subtypeVal
  exact pairPlaneHomeomorph.isClosedEmbedding.comp he

theorem standardBoundaryLine_closedEmbedding (w : ℝ) : IsClosedEmbedding (standardBoundaryLine w) := by
  have hi : IsClosedEmbedding (fun s : ℝ => (s,w)) := by
    apply IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
    refine ⟨by fun_prop,fun x y he => congrArg Prod.fst he,?_⟩
    intro K hK
    have he : (fun s : ℝ => (s,w)) '' K = K ×ˢ {w} := by aesop
    rw [he]
    exact hK.prod isClosed_singleton
  exact pairPlaneHomeomorph.isClosedEmbedding.comp hi

theorem standardBoundaryLine_disjoint :
    Disjoint (range (standardBoundaryLine 0)) (range (standardBoundaryLine 1)) := by
  apply disjoint_left.mpr
  rintro z ⟨u,rfl⟩ ⟨v,he⟩
  have h := congrArg (fun z : Plane => z 1) he
  norm_num [standardBoundaryLine] at h

theorem standardClosedStrip_diagram_membership
    (d : ProperPairDiagram (standardBoundaryLine 0) (standardBoundaryLine 1))
    (z : ℝ × unitInterval) :
    standardClosedStrip z ≠ d.pole ∧
      invert d.pole (standardClosedStrip z) ∈ twoTriangleRegion d.A d.B d.P := by
  have hline (u w : ℝ) :
      AffineMap.lineMap (standardBoundaryLine 0 u) (standardBoundaryLine 1 u) w = Plane.mk u w := by
    ext i
    fin_cases i <;> simp [standardBoundaryLine,AffineMap.lineMap_apply_module,Plane.mk]
    all_goals ring
  have hh := d.cover z.1 z.1 (by
    intro w hw hz
    rcases hz with ⟨u,he⟩ | ⟨u,he⟩
    · rw [hline] at he
      have he' := congrArg (fun z : Plane => z 1) he
      change 0=w at he'
      linarith [hw.1]
    · rw [hline] at he
      have he' := congrArg (fun z : Plane => z 1) he
      change 1=w at he'
      linarith [hw.2]) z.2 z.2.property
  simpa only [hline,standardClosedStrip,ContinuousMap.coe_mk] using hh

theorem ProperPairDiagram.pole_mem {F G : C(ℝ,Plane)} (d : ProperPairDiagram F G) :
    d.pole ∈ twoTriangleRegion d.A d.B d.P := by
  apply Or.inl
  exact frontier_subset_closure ((jordan_curve_theorem (d.jordan 0)).frontier_inside.symm ▸
    (show d.pole ∈ d.A 0 ∪ d.P ∪ d.B 0 from Or.inl (Or.inl (d.arcA 0).left_mem)))

theorem ProperPairDiagram.boundary_mem {F G : C(ℝ,Plane)} (d : ProperPairDiagram F G) :
    insert d.pole (invert d.pole '' range F) ∪ insert d.pole (invert d.pole '' range G) ⊆
      twoTriangleRegion d.A d.B d.P := by
  rw [← d.boundaryA,← d.boundaryB]
  have hc (i : Fin 2) : d.A i ∪ d.P ∪ d.B i ⊆ twoTriangleRegion d.A d.B d.P := by
    intro z hz
    have hh := frontier_subset_closure ((jordan_curve_theorem (d.jordan i)).frontier_inside.symm ▸ hz)
    fin_cases i
    · exact Or.inl hh
    · exact Or.inr hh
  rintro z ((hz | hz) | (hz | hz))
  · exact hc 0 (Or.inl (Or.inl hz))
  · exact hc 1 (Or.inl (Or.inl hz))
  · exact hc 0 (Or.inr hz)
  · exact hc 1 (Or.inr hz)

/-- Actual proper strip construction, with both boundary ranges prescribed. -/
theorem proper_disjoint_lines_range_strip
    (F G : C(ℝ,Plane)) (hF : IsClosedEmbedding F) (hG : IsClosedEmbedding G)
    (hdis : Disjoint (range F) (range G)) :
    ∃ H : C(ℝ × unitInterval,Plane), IsClosedEmbedding H ∧
      range (fun s => H (s,0)) = range F ∧ range (fun s => H (s,1)) = range G := by
  obtain ⟨d⟩ := proper_pair_diagram_exists (standardBoundaryLine 0) (standardBoundaryLine 1)
    (standardBoundaryLine_closedEmbedding 0) (standardBoundaryLine_closedEmbedding 1)
    standardBoundaryLine_disjoint
  obtain ⟨e⟩ := proper_pair_diagram_exists F G hF hG hdis
  obtain ⟨f,g,hfg,hpole,hFA,hGB⟩ := proper_pair_diagram_homeomorphism d e
  have ha : d.pole ∉ range standardClosedStrip := by
    rintro ⟨z,hz⟩
    exact (standardClosedStrip_diagram_membership d z).1 hz
  let q₀ : C(OnePoint (ℝ × unitInterval),Plane) :=
    ⟨invertedProperCompactification standardClosedStrip d.pole,
      invertedProperCompactification_continuous standardClosedStrip standardClosedStrip_closedEmbedding.isProperMap d.pole ha⟩
  have hq₀i : Function.Injective q₀ := invertedProperCompactification_injective
    standardClosedStrip standardClosedStrip_closedEmbedding.injective d.pole ha
  have hq₀mem (z : OnePoint (ℝ × unitInterval)) : q₀ z ∈ twoTriangleRegion d.A d.B d.P := by
    cases z with
    | infty => exact d.pole_mem
    | coe z => exact (standardClosedStrip_diagram_membership d z).2
  let q : C(OnePoint (ℝ × unitInterval),Plane) :=
    ⟨f ∘ q₀,hfg.continuousOn.comp_continuous q₀.continuous hq₀mem⟩
  have hqi : Function.Injective q := by
    intro z w he
    exact hq₀i (hfg.injOn (hq₀mem z) (hq₀mem w) he)
  have hqp : q OnePoint.infty = e.pole := hpole
  have hH : IsClosedEmbedding (fun z : ℝ × unitInterval => invert e.pole (q (OnePoint.some z))) := by
    simpa only [hqp] using onePoint_injective_inversion_closedEmbedding q hqi
  let H : C(ℝ × unitInterval,Plane) := ⟨_,hH.continuous⟩
  have hHval (z : ℝ × unitInterval) : H z = invert e.pole (f (invert d.pole (standardClosedStrip z))) := rfl
  have boundary (w : unitInterval) (L : C(ℝ,Plane)) (hL : e.pole ∉ range L)
      (hstd : ∀ s, standardClosedStrip (s,w) = standardBoundaryLine (w:ℝ) s)
      (hsrc : insert d.pole (invert d.pole '' range (standardBoundaryLine (w:ℝ))) ⊆ twoTriangleRegion d.A d.B d.P)
      (heq : f '' insert d.pole (invert d.pole '' range (standardBoundaryLine (w:ℝ))) =
        insert e.pole (invert e.pole '' range L)) :
      range (fun s => H (s,w)) = range L := by
    ext z
    constructor
    · rintro ⟨s,rfl⟩
      have hz := heq ▸ mem_image_of_mem f
        (show invert d.pole (standardBoundaryLine (w:ℝ) s) ∈
          insert d.pole (invert d.pole '' range (standardBoundaryLine (w:ℝ))) from
          Or.inr ⟨_,mem_range_self s,rfl⟩)
      have hne : f (invert d.pole (standardBoundaryLine (w:ℝ) s)) ≠ e.pole := by
        intro he
        have hh := hfg.injOn (hsrc (Or.inr ⟨_,mem_range_self s,rfl⟩)) d.pole_mem (he.trans hpole.symm)
        exact (standardClosedStrip_diagram_membership d (s,w)).1
          ((hstd s).trans (invert_eq_center_iff.mp hh))
      rcases hz with hz | ⟨v,hv,he⟩
      · exact False.elim (hne hz)
      · change H (s,w) ∈ range L
        rw [hHval,hstd,← he,invert_invert]
        exact hv
    · intro hz
      have hz' : invert e.pole z ∈ insert e.pole (invert e.pole '' range L) := Or.inr ⟨z,hz,rfl⟩
      obtain ⟨v,hv,he⟩ := heq.symm ▸ hz'
      rcases hv with rfl | ⟨u,⟨s,rfl⟩,rfl⟩
      · exact False.elim (hL (invert_eq_center_iff.mp (hpole.symm.trans he).symm ▸ hz))
      · refine ⟨s,?_⟩
        change H (s,w) = z
        rw [hHval,hstd,he,invert_invert]
  refine ⟨H,hH,?_,?_⟩
  · exact boundary 0 F e.poleF (fun _ => rfl)
      (fun z hz => d.boundary_mem (Or.inl hz)) hFA
  · exact boundary 1 G e.poleG (fun _ => rfl)
      (fun z hz => d.boundary_mem (Or.inr hz)) hGB

end CurveComplex.HyperellipticModel
