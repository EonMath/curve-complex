import CurveComplexGenusTwo.Hyperbolic.OriginalG1.G1OriginalGenusAdaptersPROVED
import CurveComplexGenusTwo.Topology.ActualCutRecognition.ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Topology.ActualCutRecognition.ActualMain12SeparatingRegions
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualNonseparatingEssential
import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.SideCollapse

open Set Topology CurveComplex CurveComplex.Hyperbolic

private theorem punctured_circle_connected (p : Circle) :
    ConnectedSpace {z : Circle // z ≠ p} := by
  letI : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  let v : Metric.sphere (0 : ℂ) 1 := p
  let s := stereographic' 1 v
  have hs : s.source = {z : Circle | z ≠ p} := by
    rw [stereographic'_source]
    ext z
    simp only [mem_compl_iff, mem_singleton_iff, mem_setOf_eq]
    rfl
  have ht : s.target = univ := stereographic'_target v
  let q : {z : Circle // z ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 1) :=
    (Homeomorph.setCongr hs.symm).trans
      (s.toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)))
  exact (q.connectedSpace_iff).2 inferInstance

private theorem punctured_torus_connected :
    IsConnected ({((1,1) : Circle × Circle)}ᶜ) := by
  letI : ConnectedSpace {z : Circle // z ≠ 1} := punctured_circle_connected 1
  let A : Set (Circle × Circle) := {z | z.1 ≠ 1}
  let B : Set (Circle × Circle) := {z | z.2 ≠ 1}
  have hA : IsConnected A := by
    have hc : Continuous (fun z : {x : Circle // x ≠ 1} × Circle =>
        ((z.1 : Circle), z.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hr : range (fun z : {x : Circle // x ≠ 1} × Circle =>
        ((z.1 : Circle), z.2)) = A := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact x.1.property
      · intro hz
        exact ⟨(⟨z.1, hz⟩, z.2), rfl⟩
    rw [← hr]
    exact isConnected_range hc
  have hB : IsConnected B := by
    have hc : Continuous (fun z : Circle × {x : Circle // x ≠ 1} =>
        (z.1, (z.2 : Circle))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have hr : range (fun z : Circle × {x : Circle // x ≠ 1} =>
        (z.1, (z.2 : Circle))) = B := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2.property
      · intro hz
        exact ⟨(z.1, ⟨z.2, hz⟩), rfl⟩
    rw [← hr]
    exact isConnected_range hc
  have hi : (A ∩ B).Nonempty := ⟨(-1,-1), by
    constructor
    · change (-1 : Circle) ≠ 1
      exact fun h => (show (-1 : ℂ) ≠ 1 by norm_num) (congrArg Subtype.val h)
    · change (-1 : Circle) ≠ 1
      exact fun h => (show (-1 : ℂ) ≠ 1 by norm_num) (congrArg Subtype.val h)⟩
  have hu : A ∪ B = ({((1,1) : Circle × Circle)}ᶜ) := by
    ext z
    simp only [A, B, mem_union, mem_setOf_eq, mem_compl_iff,
      mem_singleton_iff, Prod.ext_iff]
    tauto
  rw [← hu]
  exact IsConnected.union hi hA hB

theorem punctured_torus_side_connected {E : Type} [TopologicalSpace E]
    (V : Set E) (e : V ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) :
    IsConnected V := by
  have hT : ConnectedSpace {z : Circle × Circle // z ≠ (1,1)} := by
    apply isConnected_iff_connectedSpace.mp
    change IsConnected {z : Circle × Circle | z ≠ (1,1)}
    simpa only [Set.compl_singleton_eq] using punctured_torus_connected
  have hV : ConnectedSpace V := (e.connectedSpace_iff).2 hT
  exact isConnected_iff_connectedSpace.mpr hV

private theorem horizontal_punctured_torus_complement_connected :
    IsConnected {z : Circle × Circle | z ≠ (1,1) ∧ z.2 ≠ -1} := by
  have hnotopen : ¬ IsOpen ({1} : Set Circle) := by
    intro ho
    have hclopen : IsClopen ({1} : Set Circle) := ⟨isClosed_singleton, ho⟩
    have heq := hclopen.eq_univ (show ({1} : Set Circle).Nonempty from ⟨1, by simp⟩)
    have hm : (-1 : Circle) ∈ ({1} : Set Circle) := heq.symm ▸ Set.mem_univ _
    have hne : (-1 : Circle) ≠ 1 :=
      fun h => (show (-1 : ℂ) ≠ 1 by norm_num) (congrArg Subtype.val h)
    exact hne (Set.mem_singleton_iff.mp hm)
  have hdense : Dense ({1}ᶜ : Set Circle) :=
    dense_compl_singleton_iff_not_open.mpr hnotopen
  have hconn (p : Circle) : IsConnected ({p}ᶜ : Set Circle) := by
    have hh : ConnectedSpace {z : Circle // z ≠ p} := punctured_circle_connected p
    have h := isConnected_iff_connectedSpace.mpr hh
    change IsConnected {z : Circle | z ≠ p} at h
    simpa only [Set.compl_singleton_eq] using h
  let A : Set (Circle × Circle) := ({1}ᶜ : Set Circle) ×ˢ ({-1}ᶜ : Set Circle)
  let T : Set (Circle × Circle) := {z | z ≠ (1,1) ∧ z.2 ≠ -1}
  have hA : IsConnected A := (hconn 1).prod (hconn (-1))
  have hAT : A ⊆ T := by
    rintro z ⟨hx, hy⟩
    refine ⟨?_, hy⟩
    intro hz
    exact hx (congrArg Prod.fst hz)
  have hTc : T ⊆ closure A := by
    intro z hz
    rw [show A = ({1}ᶜ : Set Circle) ×ˢ ({-1}ᶜ : Set Circle) from rfl,
      closure_prod_eq]
    exact ⟨hdense.closure_eq.symm ▸ Set.mem_univ _,
      subset_closure hz.2⟩
  exact hA.subset_closure hAT hTc

private theorem prescribed_side_curve_connected_complement {E : Type}
    [TopologicalSpace E] (V : Set E)
    (e : V ≃ₜ {z : Circle × Circle // z ≠ (1,1)})
    (Q : C(E,Circle × Circle)) (hQ : ∀ x : V, Q x.val = (e x).val) :
    ∃ d : Curve E, d.image ⊆ V ∧ IsConnected (V \ d.image) ∧
      ∀ z : Circle, Q (d.map z)=(z,-1) := by
  classical
  let j : Circle → {z : Circle × Circle // z ≠ (1,1)} :=
    fun z => ⟨(z,-1), by
      intro h
      exact (show (-1 : ℂ) ≠ 1 by norm_num)
        (congrArg Subtype.val (congrArg Prod.snd h))⟩
  have hj : IsEmbedding j := by
    have hcont : Continuous j :=
      (continuous_id.prodMk continuous_const).subtype_mk _
    have hinj : Function.Injective j := by
      intro x y h
      exact congrArg (fun p : {z : Circle × Circle // z ≠ (1,1)} => p.val.1) h
    exact (hcont.isClosedEmbedding hinj).isEmbedding
  let f : Circle → E := fun z => (e.symm (j z)).val
  have hf : IsEmbedding f :=
    IsEmbedding.subtypeVal.comp (e.symm.isEmbedding.comp hj)
  let d : Curve E := ⟨f,hf⟩
  have hdq (z : Circle) : Q (d.map z)=(z,-1) := by
    change Q ((e.symm (j z)).val)=(z,-1)
    rw [hQ]
    change (e (e.symm (j z))).val=(z,-1)
    rw [e.apply_symm_apply]
  have hdV : d.image ⊆ V := by
    rintro x ⟨z,rfl⟩
    exact (e.symm (j z)).property
  let T : Set (Circle × Circle) :=
    {z | z ≠ (1,1) ∧ z.2 ≠ -1}
  letI : ConnectedSpace T :=
    isConnected_iff_connectedSpace.mp horizontal_punctured_torus_complement_connected
  let k : T → E := fun z => (e.symm ⟨z.val,z.property.1⟩).val
  have hk : Continuous k := by
    apply continuous_subtype_val.comp
    apply e.symm.continuous.comp
    exact continuous_subtype_val.subtype_mk _
  have hr : range k = V \ d.image := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      refine ⟨(e.symm ⟨z.val,z.property.1⟩).property, ?_⟩
      rintro ⟨w,hw⟩
      have he : e ⟨(e.symm ⟨z.val,z.property.1⟩).val,
          (e.symm ⟨z.val,z.property.1⟩).property⟩ = j w := by
        have he0 : e.symm ⟨z.val,z.property.1⟩ = e.symm (j w) :=
          Subtype.ext hw.symm
        simpa only [e.apply_symm_apply] using congrArg e he0
      have hz : z.val = (w,-1) :=
        congrArg Subtype.val ((e.apply_symm_apply ⟨z.val,z.property.1⟩).symm.trans he)
      exact z.property.2 (congrArg Prod.snd hz)
    · rintro ⟨hxV,hxD⟩
      let y := e ⟨x,hxV⟩
      have hy : y.val.2 ≠ -1 := by
        intro hh
        apply hxD
        refine ⟨y.val.1, ?_⟩
        change (e.symm (j y.val.1)).val = x
        have hjy : j y.val.1 = y := Subtype.ext (Prod.ext rfl hh.symm)
        rw [hjy]
        exact congrArg Subtype.val (e.symm_apply_apply ⟨x,hxV⟩)
      refine ⟨⟨y.val,y.property,hy⟩, ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x,hxV⟩)
  refine ⟨d, hdV, ?_,hdq⟩
  rw [← hr]
  exact isConnected_range hk

private theorem complementary_two_side_partition_connected {E : Type}
    [TopologicalSpace E] (F A B U V : Set E)
    (hA : IsConnected A) (hB : IsConnected B)
    (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hAB : A ∪ B = F)
    (hcover : U ∪ V = F) (hUne : U.Nonempty) (hVne : V.Nonempty) :
    IsConnected U := by
  have hAsub : A ⊆ U ∪ V := by
    rw [hcover, ← hAB]
    exact subset_union_left
  have hBsub : B ⊆ U ∪ V := by
    rw [hcover, ← hAB]
    exact subset_union_right
  have hAd := hA.isPreconnected.subset_or_subset hU hV hUV hAsub
  have hBd := hB.isPreconnected.subset_or_subset hU hV hUV hBsub
  have hUAB : U ⊆ A ∪ B := by rw [hAB, ← hcover]; exact subset_union_left
  have hVAB : V ⊆ A ∪ B := by rw [hAB, ← hcover]; exact subset_union_right
  rcases hAd with hAU | hAV <;> rcases hBd with hBU | hBV
  · have hVU : V ⊆ U := by
      intro x hx
      rcases hVAB hx with ha | hb
      · exact hAU ha
      · exact hBU hb
    obtain ⟨x,hx⟩ := hVne
    exact False.elim (Set.disjoint_left.mp hUV (hVU hx) hx)
  · have hUA : U = A := by
      apply subset_antisymm
      · intro x hx
        rcases hUAB hx with ha | hb
        · exact ha
        · exact False.elim (Set.disjoint_left.mp hUV hx (hBV hb))
      · exact hAU
    simpa [hUA] using hA
  · have hUB : U = B := by
      apply subset_antisymm
      · intro x hx
        rcases hUAB hx with ha | hb
        · exact False.elim (Set.disjoint_left.mp hUV hx (hAV ha))
        · exact hb
      · exact hBU
    simpa [hUB] using hB
  · have hUVsub : U ⊆ V := by
      intro x hx
      rcases hUAB hx with ha | hb
      · exact hAV ha
      · exact hBV hb
    obtain ⟨x,hx⟩ := hUne
    exact False.elim (Set.disjoint_left.mp hUV hx (hUVsub hx))

theorem glued_curve_complement_connected {E : Type}
    [TopologicalSpace E] [T2Space E]
    (c d : Curve E) (U V : Set E)
    (hUV : Disjoint U V)
    (hcover : U ∪ V = c.imageᶜ)
    (hfrontU : frontier U = c.image)
    (hfrontV : frontier V = c.image)
    (hdV : d.image ⊆ V)
    (hUconn : IsConnected U)
    (hVconn : IsConnected (V \ d.image)) :
    IsConnected d.imageᶜ := by
  have hcd : c.image ⊆ d.imageᶜ := by
    intro x hx hd
    have hxV : x ∈ V := hdV hd
    have hxC : x ∈ c.imageᶜ := hcover ▸ Or.inr hxV
    exact hxC hx
  have hcU : c.image ⊆ closure U := by
    rw [← hfrontU]
    exact frontier_subset_closure
  have hcV : c.image ⊆ closure V := by
    rw [← hfrontV]
    exact frontier_subset_closure
  have hdclosed : IsClosed d.image :=
    (isCompact_range d.embedded.continuous).isClosed
  have hcVd : c.image ⊆ closure (V \ d.image) := by
    intro x hx
    apply mem_closure_iff_nhds.mpr
    intro W hW
    have hWD : W ∩ d.imageᶜ ∈ 𝓝 x :=
      Filter.inter_mem hW (hdclosed.isOpen_compl.mem_nhds (hcd hx))
    obtain ⟨y,hyWD,hyV⟩ := mem_closure_iff_nhds.mp (hcV hx) _ hWD
    refine ⟨y,hyWD.1,⟨hyV,hyWD.2⟩⟩
  have hUc : IsConnected (U ∪ c.image) := by
    apply hUconn.subset_closure subset_union_left
    exact union_subset subset_closure hcU
  have hVdc : IsConnected ((V \ d.image) ∪ c.image) := by
    apply hVconn.subset_closure subset_union_left
    exact union_subset subset_closure hcVd
  have hi : ((U ∪ c.image) ∩ ((V \ d.image) ∪ c.image)).Nonempty :=
    ⟨c.map 1, Or.inr ⟨1,rfl⟩, Or.inr ⟨1,rfl⟩⟩
  have hconn := IsConnected.union hi hUc hVdc
  have heq : (U ∪ c.image) ∪ ((V \ d.image) ∪ c.image) = d.imageᶜ := by
    ext x
    constructor
    · rintro ((hxU | hxC) | hxV | hxC)
      · intro hd
        exact Set.disjoint_left.mp hUV hxU (hdV hd)
      · exact hcd hxC
      · exact hxV.2
      · exact hcd hxC
    · intro hx
      by_cases hc : x ∈ c.image
      · exact Or.inl (Or.inr hc)
      · have hUV : x ∈ U ∪ V := hcover ▸ hc
        rcases hUV with hu | hv
        · exact Or.inl (Or.inl hu)
        · exact Or.inr (Or.inl ⟨hv,hx⟩)
  rw [← heq]
  exact hconn

private theorem actual_topological_nondividing_in_prescribed_side
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c : Curve E)
    (hcdiv : DividingCurve c)
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
    (hfrontU : frontier U = c.image) (hfrontV : frontier V = c.image)
    (eV : Nonempty (V ≃ₜ {z : Circle × Circle // z ≠ (1,1)})) :
    ∃ e : V ≃ₜ {z : Circle × Circle // z ≠ (1,1)},
    ∃ d : Curve E, ∃ Q : C(E,Circle × Circle),
      ¬ DividingCurve d ∧ d.image ⊆ V ∧
      IsConnected U ∧ IsConnected (V \ d.image) ∧
      (∀ z : Circle, Q (d.map z)=(z,-1)) ∧
      (∀ x : V, Q x.val=(e x).val) ∧
      (∀ x : E, x ∉ V → Q x=(1,1)) := by
  obtain ⟨e⟩ := eV
  have ht2 : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    letI : MetricSpace E := H.metric
    infer_instance
  rw [H.compatible] at ht2
  letI : T2Space E := ht2
  obtain ⟨Q,hqV,hqout⟩ := actual_punctured_torus_side_torus_coordinate V hV e
  obtain ⟨d,hdV,hVconn,hdq⟩ :=
    prescribed_side_curve_connected_complement V e Q hqV
  have hUne : U.Nonempty := by
    by_contra h
    have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hc : c.map 1 ∈ frontier U := hfrontU.symm ▸ ⟨1,rfl⟩
    simpa [he] using hc
  have hVne : V.Nonempty := ⟨d.map 1, hdV ⟨1,rfl⟩⟩
  have hsep : ¬ Nonseparating c := hcdiv
  obtain ⟨A,B,hAopen,hBopen,hAconn,hBconn,hAB,hABcover,_,_⟩ :=
    source_separating_curve_actual_complementary_regions E M.genusTwo c hsep
  have hUconn : IsConnected U :=
    complementary_two_side_partition_connected c.imageᶜ A B U V
      hAconn hBconn hU hV hUV hABcover hcover hUne hVne
  have hdconn : IsConnected d.imageᶜ :=
    glued_curve_complement_connected c d U V hUV hcover hfrontU hfrontV
      hdV hUconn hVconn
  exact ⟨e,d,Q,by intro h;exact h hdconn,hdV,hUconn,hVconn,hdq,hqV,hqout⟩

theorem actual_topological_essential_in_prescribed_side
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c : Curve E)
    (hcdiv : DividingCurve c)
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
    (hfrontU : frontier U = c.image) (hfrontV : frontier V = c.image)
    (eV : Nonempty (V ≃ₜ {z : Circle × Circle // z ≠ (1,1)})) :
    ∃ e : V ≃ₜ {z : Circle × Circle // z ≠ (1,1)},
    ∃ d : Curve E, ∃ Q : C(E,Circle × Circle),
      Essential d ∧ ¬ DividingCurve d ∧ d.image ⊆ V ∧
      IsConnected U ∧ IsConnected (V \ d.image) ∧
      (∀ z : Circle, Q (d.map z)=(z,-1)) ∧
      (∀ x : V, Q x.val=(e x).val) ∧
      (∀ x : E, x ∉ V → Q x=(1,1)) := by
  obtain ⟨e,d,Q,hdnondiv,hdV,hUconn,hVconn,hdq,hqV,hqout⟩ :=
    actual_topological_nondividing_in_prescribed_side M H c hcdiv
      U V hU hV hUV hcover hfrontU hfrontV eV
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hdessential : Essential d :=
    source_nonseparating_curve_essential E d (Classical.not_not.mp hdnondiv)
  exact ⟨e,d,Q,hdessential,hdnondiv,hdV,hUconn,hVconn,hdq,hqV,hqout⟩

theorem actual_nondividing_of_ambient_isotopy
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (d g : Curve E) (hd : ¬ DividingCurve d)
    (hrel : AmbientIsotopy.Rel d.image g.image) :
    ¬ DividingCurve g := by
  obtain ⟨F,hF⟩ := hrel
  obtain ⟨e,he⟩ := F.homeomorphism_at ⟨1,by norm_num⟩
  have heq : (e : E → E) = F.finalMap := funext he
  have himage : e '' d.image = g.image := by
    rw [heq]
    exact hF
  have hcompl : e '' d.imageᶜ = g.imageᶜ := by
    rw [← himage, e.image_compl]
  have hconn : IsConnected d.imageᶜ := Classical.not_not.mp hd
  have : IsConnected (e '' d.imageᶜ) := hconn.image e e.continuous.continuousOn
  change ¬ ¬ IsConnected g.imageᶜ
  exact not_not.mpr (hcompl ▸ this)

theorem actual_geodesic_lies_in_one_given_cut_side
    {E : Type} [TopologicalSpace E]
    (c g : Curve E) (U V : Set E)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = c.imageᶜ)
    (hdis : Disjoint c.image g.image) :
    g.image ⊆ U ∨ g.image ⊆ V := by
  have hsubset : g.image ⊆ U ∪ V := by
    rw [hcover]
    exact hdis.subset_compl_left
  have hconn : IsPreconnected g.image :=
    (isConnected_range g.embedded.continuous).isPreconnected
  rcases hsubset (by exact ⟨1,rfl⟩ : g.map 1 ∈ g.image) with hu | hv
  · left
    exact hconn.subset_left_of_subset_union hU hV hUV hsubset
      ⟨g.map 1,⟨⟨1,rfl⟩,hu⟩⟩
  · right
    exact hconn.subset_right_of_subset_union hU hV hUV hsubset
      ⟨g.map 1,⟨⟨1,rfl⟩,hv⟩⟩

#print axioms actual_topological_nondividing_in_prescribed_side
#print axioms actual_topological_essential_in_prescribed_side
#print axioms actual_nondividing_of_ambient_isotopy
#print axioms actual_geodesic_lies_in_one_given_cut_side
#print axioms punctured_torus_side_connected
#print axioms glued_curve_complement_connected
