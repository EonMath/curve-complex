import CurveComplexGenusTwo.Topology.ActualCutRecognition.ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.ActualCutRecognition.ActualEssentialGenusTwoCutSideHomologyComplete
import CurveComplexGenusTwo.Topology.ActualCutRecognition.ActualCutSideRecognition
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisChart

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The actual separating cut in Haas–Susskind Theorem1. The pieces are open
subsets of the original E with exactly the given curve as frontier. Their
homeomorphism type is stated concretely; no metric or symmetry is certified. -/
theorem actual_dividing_essential_curve_two_one_holed_tori
    (M : HyperellipticModel E S) (c : Curve E)
    (hc : Essential c) (hdiv : DividingCurve c) :
    ∃ U V : Set E,
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      U ∪ V = c.imageᶜ ∧ frontier U = c.image ∧ frontier V = c.image ∧
      Nonempty (U ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) ∧
      Nonempty (V ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  letI : LocallyConnectedSpace E :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
  have hclosed : IsClosed c.image :=
    (isCompact_range c.embedded.continuous).isClosed
  have hopen : IsOpen c.imageᶜ := hclosed.isOpen_compl
  have hnonempty : c.imageᶜ.Nonempty := by
    obtain ⟨W, Z, hp, e, hW, hZ, hzero, haxis⟩ :=
      CurveComplex.LocalSurgery.embedded_curve_has_local_axis_chart c
        (c.map 1) ⟨1, rfl⟩
    have hz : (0, 0) ∈ Z := by
      rw [← hzero]
      exact (e ⟨c.map 1, hp⟩).property
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hZ (0, 0) hz
    have hq : (r / 2, 0) ∈ Z := by
      apply hball
      change dist (r / 2, (0 : ℝ)) (0, 0) < r
      rw [Prod.dist_eq]
      have hhalf : 0 < r / 2 := by linarith
      simp only [Real.dist_eq, sub_zero, sub_self, abs_zero]
      rw [abs_of_pos hhalf, max_eq_left (le_of_lt hhalf)]
      linarith
    let x := e.symm ⟨(r / 2, 0), hq⟩
    refine ⟨x.val, ?_⟩
    intro hx
    have heq : ((e ⟨x.val, x.property⟩ : Z) : ℝ × ℝ) = (r / 2, 0) := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨(r / 2, 0), hq⟩)
    have hh := (haxis x.val x.property).mp hx
    rw [heq] at hh
    linarith
  obtain ⟨x, hx⟩ := hnonempty
  let U := connectedComponentIn c.imageᶜ x
  let V := c.imageᶜ \ U
  have hU : IsOpen U := hopen.connectedComponentIn
  have hxU : x ∈ U := mem_connectedComponentIn hx
  have hUsub : U ⊆ c.imageᶜ := connectedComponentIn_subset _ _
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hCopen : IsOpen (connectedComponentIn c.imageᶜ z) :=
      hopen.connectedComponentIn
    apply Filter.mem_of_superset (hCopen.mem_nhds (mem_connectedComponentIn hz.1))
    intro w hw
    refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
    intro hwU
    have h1 := connectedComponentIn_eq hw
    have h2 := connectedComponentIn_eq hwU
    have hzU : z ∈ U := by
      change z ∈ connectedComponentIn c.imageᶜ x
      rw [h2, ← h1]
      exact mem_connectedComponentIn hz.1
    exact hz.2 hzU
  have hUV : Disjoint U V := by
    exact Set.disjoint_left.mpr (fun z hzU hzV => hzV.2 hzU)
  have hcover : U ∪ V = c.imageᶜ := by
    ext z
    constructor
    · rintro (hzU | hzV)
      · exact hUsub hzU
      · exact hzV.1
    · intro hz
      by_cases hzU : z ∈ U
      · exact Or.inl hzU
      · exact Or.inr ⟨hz, hzU⟩
  have hVnonempty : V.Nonempty := by
    by_contra hnone
    have hVempty : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hnone
    have hF : c.imageᶜ = U := by simpa [hVempty] using hcover.symm
    apply hdiv
    rw [hF]
    exact isConnected_connectedComponentIn_iff.mpr hx
  have hfrontierSubset : ∀ A B : Set E,
      IsOpen A → IsOpen B → Disjoint A B → A ∪ B = c.imageᶜ →
      frontier A ⊆ c.image := by
    intro A B hA hB hAB hcoverAB z hz
    by_contra hzc
    have hzF : z ∈ c.imageᶜ := hzc
    rw [← hcoverAB] at hzF
    rcases hzF with hzA | hzB
    · have hn : z ∉ interior A := hz.2
      exact hn (hA.interior_eq.symm ▸ hzA)
    · obtain ⟨w, hwB, hwA⟩ :=
        mem_closure_iff.mp hz.1 B hB hzB
      exact Set.disjoint_left.mp hAB hwA hwB
  have hfrontierU : frontier U ⊆ c.image :=
    hfrontierSubset U V hU hV hUV hcover
  have hfrontierV : frontier V ⊆ c.image :=
    hfrontierSubset V U hV hU hUV.symm (by simpa [union_comm] using hcover)
  obtain ⟨e, he, hcore⟩ :=
    CurveComplex.LocalSurgery.actual_original_essential_circle_has_annular_collar
      E 2 (by omega) M.genusTwo ⟨c, hc⟩
  let T := Set.Ioo (-1 : ℝ) 1
  let Iplus : Set T := {t | 0 < t.val}
  let Iminus : Set T := {t | t.val < 0}
  have hplusImage : Subtype.val '' Iplus = Set.Ioo (0 : ℝ) 1 := by
    ext t
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨hr, r.property.2⟩
    · intro ht
      exact ⟨⟨t, ⟨by linarith [ht.1], ht.2⟩⟩, ht.1, rfl⟩
  have hminusImage : Subtype.val '' Iminus = Set.Ioo (-1 : ℝ) 0 := by
    ext t
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r.property.1, hr⟩
    · intro ht
      exact ⟨⟨t, ⟨ht.1, by linarith [ht.2]⟩⟩, ht.2, rfl⟩
  have hplusConnected : IsPreconnected Iplus := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hplusImage]
    exact isPreconnected_Ioo
  have hminusConnected : IsPreconnected Iminus := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hminusImage]
    exact isPreconnected_Ioo
  let Kplus := e '' (Iplus ×ˢ (Set.univ : Set Circle))
  let Kminus := e '' (Iminus ×ˢ (Set.univ : Set Circle))
  have hKplusConnected : IsPreconnected Kplus :=
    (hplusConnected.prod isPreconnected_univ).image e e.continuous.continuousOn
  have hKminusConnected : IsPreconnected Kminus :=
    (hminusConnected.prod isPreconnected_univ).image e e.continuous.continuousOn
  have hnoncore : ∀ p : T × Circle, p.1.val ≠ 0 → e p ∈ c.imageᶜ := by
    intro p hne hpc
    obtain ⟨w, hw⟩ := hpc
    have heq : e p = e (⟨0, by norm_num [T]⟩, w) := by
      rw [hcore]
      exact hw.symm
    have htime := congrArg (fun q : T × Circle => q.1.val) (he.injective heq)
    exact hne htime
  have hKplusSub : Kplus ⊆ c.imageᶜ := by
    rintro y ⟨p, hp, rfl⟩
    exact hnoncore p (ne_of_gt hp.1)
  have hKminusSub : Kminus ⊆ c.imageᶜ := by
    rintro y ⟨p, hp, rfl⟩
    exact hnoncore p (ne_of_lt hp.1)
  have hzeroPlus : (⟨0, by norm_num [T]⟩ : T) ∈ closure Iplus := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change (0 : ℝ) ∈ closure (Subtype.val '' Iplus)
    rw [hplusImage, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, by norm_num [T]⟩
  have hzeroMinus : (⟨0, by norm_num [T]⟩ : T) ∈ closure Iminus := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change (0 : ℝ) ∈ closure (Subtype.val '' Iminus)
    rw [hminusImage, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
    exact ⟨by norm_num, le_rfl⟩
  have hcoreClosure : ∀ (I : Set T) (hz : (⟨0, by norm_num [T]⟩ : T) ∈ closure I),
      c.image ⊆ closure (e '' (I ×ˢ (Set.univ : Set Circle))) := by
    intro I hz y hy
    obtain ⟨w, rfl⟩ := hy
    let f : T → E := fun t => e (t, w)
    have hf : Continuous f :=
      e.continuous.comp (continuous_id.prodMk continuous_const)
    have hm : f ⟨0, by norm_num [T]⟩ ∈ closure (f '' I) :=
      mem_closure_image hf.continuousAt hz
    have hsub : f '' I ⊆ e '' (I ×ˢ (Set.univ : Set Circle)) := by
      rintro z ⟨t, ht, rfl⟩
      exact ⟨(t, w), ⟨ht, Set.mem_univ _⟩, rfl⟩
    have hmem := closure_mono hsub hm
    simpa only [f, hcore] using hmem
  have hcorePlus : c.image ⊆ closure Kplus := hcoreClosure Iplus hzeroPlus
  have hcoreMinus : c.image ⊆ closure Kminus := hcoreClosure Iminus hzeroMinus
  have hfullFrontier : ∀ A B : Set E,
      IsOpen A → IsOpen B → Disjoint A B → A ∪ B = c.imageᶜ →
      A.Nonempty → frontier A = c.image := by
    intro A B hA hB hAB hcoverAB hAne
    have hAsub : A ⊆ c.imageᶜ := by
      intro z hz
      rw [← hcoverAB]
      exact Or.inl hz
    have hAproper : A ≠ Set.univ := by
      intro hAU
      have hm : c.map 1 ∈ A := by rw [hAU]; trivial
      exact hAsub hm ⟨1, rfl⟩
    obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr ⟨hAne, hAproper⟩
    have hzcore := hfrontierSubset A B hA hB hAB hcoverAB hz
    obtain ⟨w, hw⟩ := hzcore
    have hzrange : z ∈ Set.range e := by
      exact ⟨(⟨0, by norm_num [T]⟩, w), (hcore w).trans hw⟩
    obtain ⟨y, hyrange, hyA⟩ := mem_closure_iff.mp hz.1 (Set.range e)
      he.isOpen_range hzrange
    obtain ⟨p, rfl⟩ := hyrange
    have htime : p.1.val ≠ 0 := by
      intro hpzero
      have hp : p.1 = (⟨0, by norm_num [T]⟩ : T) := Subtype.ext hpzero
      have hycore : e p ∈ c.image := by
        have heq : e p = c.map p.2 := by
          calc e p = e (p.1, p.2) := rfl
            _ = e (⟨0, by norm_num [T]⟩, p.2) := by rw [hp]
            _ = c.map p.2 := hcore p.2
        exact ⟨p.2, heq.symm⟩
      exact hAsub hyA hycore
    have hchoose : ∀ K : Set E, IsPreconnected K → K ⊆ c.imageᶜ →
        c.image ⊆ closure K → e p ∈ K → c.image ⊆ closure A := by
      intro K hK hKF hcoreK hpK
      have hsplit : K ⊆ A ∨ K ⊆ B :=
        IsPreconnected.subset_or_subset hA hB hAB
          (by simpa [hcoverAB] using hKF) hK
      rcases hsplit with hKA | hKB
      · exact hcoreK.trans (closure_mono hKA)
      · exact False.elim (Set.disjoint_left.mp hAB hyA (hKB hpK))
    have hcoreA : c.image ⊆ closure A := by
      rcases lt_or_gt_of_ne htime with hnegative | hpositive
      · exact hchoose Kminus hKminusConnected hKminusSub hcoreMinus
          ⟨p, ⟨hnegative, Set.mem_univ _⟩, rfl⟩
      · exact hchoose Kplus hKplusConnected hKplusSub hcorePlus
          ⟨p, ⟨hpositive, Set.mem_univ _⟩, rfl⟩
    apply Set.Subset.antisymm (hfrontierSubset A B hA hB hAB hcoverAB)
    intro y hy
    refine ⟨hcoreA hy, ?_⟩
    intro hyinterior
    exact hAsub (interior_subset hyinterior) hy
  have hfrontiers : frontier U = c.image ∧ frontier V = c.image :=
    ⟨hfullFrontier U V hU hV hUV hcover ⟨x, hxU⟩,
      hfullFrontier V U hV hU hUV.symm (by simpa [union_comm] using hcover) hVnonempty⟩
  have hrestOpen : ∀ z ∈ c.imageᶜ,
      IsOpen (c.imageᶜ \ connectedComponentIn c.imageᶜ z) := by
    intro z hz
    rw [isOpen_iff_mem_nhds]
    intro w hw
    have hWopen : IsOpen (connectedComponentIn c.imageᶜ w) := hopen.connectedComponentIn
    apply Filter.mem_of_superset (hWopen.mem_nhds (mem_connectedComponentIn hw.1))
    intro q hq
    refine ⟨connectedComponentIn_subset _ _ hq, ?_⟩
    intro hqz
    have h1 := connectedComponentIn_eq hq
    have h2 := connectedComponentIn_eq hqz
    apply hw.2
    rw [h2, ← h1]
    exact mem_connectedComponentIn hw.1
  have hcomponentHalf : ∀ z ∈ c.imageᶜ,
      Kplus ⊆ connectedComponentIn c.imageᶜ z ∨
      Kminus ⊆ connectedComponentIn c.imageᶜ z := by
    intro z hz
    let C := connectedComponentIn c.imageᶜ z
    let R := c.imageᶜ \ C
    have hCopen : IsOpen C := hopen.connectedComponentIn
    have hRopen : IsOpen R := hrestOpen z hz
    have hCsub : C ⊆ c.imageᶜ := connectedComponentIn_subset _ _
    have hCR : Disjoint C R :=
      Set.disjoint_left.mpr (fun q hqC hqR => hqR.2 hqC)
    have hCRcover : C ∪ R = c.imageᶜ := by
      ext q
      simp only [R, Set.mem_union, Set.mem_sdiff]
      exact ⟨fun h => h.elim (fun hq => hCsub hq) And.left,
        fun h => by by_cases hC : q ∈ C; exact Or.inl hC; exact Or.inr ⟨h, hC⟩⟩
    have hfront : frontier C = c.image :=
      hfullFrontier C R hCopen hRopen hCR hCRcover ⟨z, mem_connectedComponentIn hz⟩
    have hcorefront : c.map 1 ∈ frontier C := by
      rw [hfront]
      exact ⟨1, rfl⟩
    have hcorerange : c.map 1 ∈ Set.range e :=
      ⟨(⟨0, by norm_num [T]⟩, 1), hcore 1⟩
    obtain ⟨q, hqrange, hqC⟩ := mem_closure_iff.mp hcorefront.1
      (Set.range e) he.isOpen_range hcorerange
    obtain ⟨p, rfl⟩ := hqrange
    have htime : p.1.val ≠ 0 := by
      intro htime
      have ht : p.1 = (⟨0, by norm_num [T]⟩ : T) := Subtype.ext htime
      have hpimage : e p ∈ c.image := by
        refine ⟨p.2, ?_⟩
        calc c.map p.2 = e (⟨0, by norm_num [T]⟩, p.2) := (hcore p.2).symm
          _ = e p := by rw [← ht]
      exact hCsub hqC hpimage
    have hchoose : ∀ K : Set E, IsPreconnected K → K ⊆ c.imageᶜ →
        e p ∈ K → K ⊆ C := by
      intro K hK hKF hpK
      rcases IsPreconnected.subset_or_subset hCopen hRopen hCR
        (by simpa [hCRcover] using hKF) hK with hKC | hKR
      · exact hKC
      · exact False.elim (Set.disjoint_left.mp hCR hqC (hKR hpK))
    rcases lt_or_gt_of_ne htime with hnegative | hpositive
    · exact Or.inr (hchoose Kminus hKminusConnected hKminusSub
        ⟨p, ⟨hnegative, Set.mem_univ _⟩, rfl⟩)
    · exact Or.inl (hchoose Kplus hKplusConnected hKplusSub
        ⟨p, ⟨hpositive, Set.mem_univ _⟩, rfl⟩)
  have hplusNonempty : Kplus.Nonempty :=
    ⟨e (⟨1 / 2, by norm_num [T]⟩, 1),
      ⟨(⟨1 / 2, by norm_num [T]⟩, 1), ⟨by norm_num [T, Iplus], Set.mem_univ _⟩, rfl⟩⟩
  have hminusNonempty : Kminus.Nonempty :=
    ⟨e (⟨-1 / 2, by norm_num [T]⟩, 1),
      ⟨(⟨-1 / 2, by norm_num [T]⟩, 1), ⟨by norm_num [T, Iminus], Set.mem_univ _⟩, rfl⟩⟩
  have hcomponentDisjoint : ∀ z ∈ V, Disjoint (connectedComponentIn c.imageᶜ z) U := by
    intro z hz
    apply Set.disjoint_left.mpr
    intro q hqz hqU
    have h1 := connectedComponentIn_eq hqz
    have h2 := connectedComponentIn_eq hqU
    apply hz.2
    change z ∈ connectedComponentIn c.imageᶜ x
    rw [h2, ← h1]
    exact mem_connectedComponentIn hz.1
  have hforcedHalf : ∀ K L : Set E, K.Nonempty → K ⊆ U →
      ∀ z ∈ V, (K ⊆ connectedComponentIn c.imageᶜ z ∨
        L ⊆ connectedComponentIn c.imageᶜ z) → L ⊆ connectedComponentIn c.imageᶜ z := by
    intro K L hK hKU z hz hsplit
    rcases hsplit with hKC | hLC
    · obtain ⟨q, hq⟩ := hK
      exact False.elim (Set.disjoint_left.mp (hcomponentDisjoint z hz) (hKC hq) (hKU hq))
    · exact hLC
  obtain ⟨y, hy⟩ := hVnonempty
  have hsameComponent : ∀ z ∈ V,
      connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ y := by
    intro z hz
    rcases hcomponentHalf x hx with hplusU | hminusU
    · have hmz := hforcedHalf Kplus Kminus hplusNonempty hplusU z hz (hcomponentHalf z hz.1)
      have hmy := hforcedHalf Kplus Kminus hplusNonempty hplusU y hy (hcomponentHalf y hy.1)
      obtain ⟨q, hq⟩ := hminusNonempty
      exact (connectedComponentIn_eq (hmz hq)).trans (connectedComponentIn_eq (hmy hq)).symm
    · have hpz := hforcedHalf Kminus Kplus hminusNonempty hminusU z hz (hcomponentHalf z hz.1).symm
      have hpy := hforcedHalf Kminus Kplus hminusNonempty hminusU y hy (hcomponentHalf y hy.1).symm
      obtain ⟨q, hq⟩ := hplusNonempty
      exact (connectedComponentIn_eq (hpz hq)).trans (connectedComponentIn_eq (hpy hq)).symm
  have hVcomponent : V = connectedComponentIn c.imageᶜ y := by
    apply Set.Subset.antisymm
    · intro z hz
      rw [← hsameComponent z hz]
      exact mem_connectedComponentIn hz.1
    · intro z hz
      exact ⟨connectedComponentIn_subset _ _ hz,
        fun hzU => Set.disjoint_left.mp (hcomponentDisjoint y hy) hz hzU⟩
  have hUconnected : IsConnected U := isConnected_connectedComponentIn_iff.mpr hx
  have hVconnected : IsConnected V := by
    rw [hVcomponent]
    exact isConnected_connectedComponentIn_iff.mpr hy.1
  have hclassification :
      Nonempty (U ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) ∧
      Nonempty (V ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) := by
    obtain ⟨hUone, hVone⟩ :=
      actual_essential_genus_two_cut_side_homology M c hc U V hU hV
        hUconnected hVconnected hUV hcover hfrontiers.1 hfrontiers.2
    constructor
    · exact actual_rank_two_cut_side_punctured_torus_recognition M c hc U V
        hU hV hUconnected hVconnected hUV hcover hfrontiers.1 hfrontiers.2 hUone
    · exact actual_rank_two_cut_side_punctured_torus_recognition M c hc V U
        hV hU hVconnected hUconnected hUV.symm
        (by rw [union_comm]; exact hcover) hfrontiers.2 hfrontiers.1 hVone
  exact ⟨U, V, hU, hV, hUV, hcover, hfrontiers.1, hfrontiers.2,
    hclassification.1, hclassification.2⟩

end CurveComplex.Hyperbolic
