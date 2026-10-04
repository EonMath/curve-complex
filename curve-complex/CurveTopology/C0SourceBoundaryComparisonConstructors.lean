import C0CurveToArcBoundaryCorrespondence
import CurveComplexGenusTwo.Topology.ActualOriginalRegionalArc.SourceActualRegionEssentialProperArc
import CurveComplexGenusTwo.Topology.ActualCurveMinimum.OriginalFiniteMinimalActualReturningConsumer
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualCurveDensity
import CurveComplexGenusTwo.Topology.Smoothing.EndpointCoordinateDisks

set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

/-! Source-facing construction obligations for the approved N5 data bundles.
The regional geometry and comparison are produced together for the same chosen
regions. No instance of G or C, descent success, alignment, or filling is input.
-/
open Set Topology Schoenflies CurveComplexGenusTwo.SourceTopology
namespace CurveComplex.C0BoundaryCorrespondence.SourceConstructors
open CurveComplex.C0BoundaryCorrespondence
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

/-- Prepared original caller: use the actual simultaneous curve family and
its compatible-pair separation, with the original chart closed disk missing
every chosen image. Produce all G/C fields for one common region family,
retaining the exact original representatives. No arbitrary-G comparison
producer is asserted. -/
theorem source_c0_prepared_bordered_regions_and_arc_comparison_exists
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (Fv : Finset (Vertex S))
    (r : ↥Fv → EssentialCurve S)
    (hr : ∀ w, Quotient.mk (essentialCurveSetoid S) (r w) = w.val)
    (hzeroPosition : ∀ u w : ↥Fv, u ≠ w → geometricIntersection u.val w.val = 0 →
      Disjoint (r u).val.image (r w).val.image)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (hchosenAvoid : ∀ w : ↥Fv, Disjoint
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
      (r w).val.image) :
    ∃ G : ActualBorderedRegions S x R Fv,
      G.representative = r ∧ Nonempty (RegionalArcComparison S x R G) := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  letI : Nonempty S := hS.1
  let source_r : (w : Vertex S) → w ∈ Fv → EssentialCurve S := fun w hw => r ⟨w,hw⟩
  have source_hr : ∀ w hw, Quotient.mk (essentialCurveSetoid S) (source_r w hw) = w :=
    fun w hw => hr ⟨w,hw⟩
  have source_zeroPosition (u w : ↥Fv) (huw : u.val ≠ w.val)
      (hz : geometricIntersection u.val w.val = 0) :
      Disjoint (source_r u.val u.property).val.image (source_r w.val w.property).val.image :=
    hzeroPosition u w (fun he => huw (congrArg Subtype.val he)) hz
  have source_chosenAvoid (w : Vertex S) (hw : w ∈ Fv) :
      Disjoint ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
        (source_r w hw).val.image := hchosenAvoid ⟨w,hw⟩
  let D : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
  let P := ↥Dᶜ
  have hPopen : IsOpen Dᶜ := by
    have hDc : IsCompact D :=
      (isCompact_closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R).image_of_continuousOn
        ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.continuousOn.mono htarget)
    exact hDc.isClosed.isOpen_compl
  have hcompatibleNeighborhoods :
      ∃ N : ↥Fv → Set S,
        (∀ i, IsOpen (N i) ∧ (source_r i.val i.property).val.image ⊆ N i ∧ N i ⊆ Dᶜ) ∧
        ∀ i j, i ≠ j → geometricIntersection i.val j.val = 0 → Disjoint (N i) (N j) := by
    have hsep (i j : ↥Fv) (hij : i ≠ j ∧ geometricIntersection i.val j.val = 0) :
        ∃ U V : Set S, IsOpen U ∧ IsOpen V ∧
          (source_r i.val i.property).val.image ⊆ U ∧
          (source_r j.val j.property).val.image ⊆ V ∧ Disjoint U V := by
      apply SeparatedNhds.of_isCompact_isCompact
        (isCompact_range (source_r i.val i.property).val.embedded.continuous)
        (isCompact_range (source_r j.val j.property).val.embedded.continuous)
      apply source_zeroPosition i j _ hij.2
      intro he
      exact hij.1 (Subtype.ext he)
    choose U V hU hV hcU hcV hUV using hsep
    let N : ↥Fv → Set S := fun i => Dᶜ ∩
      (⋂ j, ⋂ h : i ≠ j ∧ geometricIntersection i.val j.val = 0, U i j h) ∩
      (⋂ j, ⋂ h : j ≠ i ∧ geometricIntersection j.val i.val = 0, V j i h)
    refine ⟨N, ?_, ?_⟩
    · intro i
      refine ⟨(hPopen.inter (isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun h => hU i j h)).inter
        (isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun h => hV j i h), ?_,
        fun _ hy => hy.1.1⟩
      intro y hy
      refine ⟨⟨?_, Set.mem_iInter.mpr fun j => Set.mem_iInter.mpr fun h => hcU i j h hy⟩,
        Set.mem_iInter.mpr fun j => Set.mem_iInter.mpr fun h => hcV j i h hy⟩
      exact Set.disjoint_right.mp (source_chosenAvoid i.val i.property) hy
    · intro i j hij hz
      apply (hUV i j ⟨hij,hz⟩).mono
      · intro y hy
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hy.1.2 j) ⟨hij,hz⟩
      · intro y hy
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hy.2 i) ⟨hij,hz⟩
  obtain ⟨compatibleN, hcompatibleN, hcompatibleDisjoint⟩ := hcompatibleNeighborhoods
  have hfaceNeighborhoods (σ : Finset ↥Fv)
      (hz : ∀ i j : ↥σ, i ≠ j → geometricIntersection i.val.val j.val.val = 0) :
      ∃ N : ↥σ → Set S,
        (∀ i, IsOpen (N i) ∧ (source_r i.val.val i.val.property).val.image ⊆ N i ∧ N i ⊆ Dᶜ) ∧
        ∀ i j, i ≠ j → Disjoint (N i) (N j) := by
    refine ⟨fun i => compatibleN i.val, fun i => hcompatibleN i.val, ?_⟩
    intro i j hij
    apply hcompatibleDisjoint i.val j.val _ (hz i j hij)
    intro he
    exact hij (Subtype.ext he)
  have hcollarInNeighborhood (b : EssentialCurve S) (N : Set S)
      (hN : IsOpen N) (hbN : b.val.image ⊆ N) :
      ∃ (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (U : Set (Set.Ioo (-1 : ℝ) 1)),
        Topology.IsOpenEmbedding E ∧
        (∀ w, E (⟨0, by norm_num⟩, w) = b.val.map w) ∧
        IsOpen U ∧ (⟨0, by norm_num⟩ : Set.Ioo (-1 : ℝ) 1) ∈ U ∧
        E '' (U ×ˢ Set.univ) ⊆ N := by
    obtain ⟨E, hE, hcore⟩ :=
      CurveComplex.LocalSurgery.actual_original_essential_circle_has_annular_collar
        S g hg hS b
    have hprod : ({⟨0, by norm_num⟩} : Set (Set.Ioo (-1 : ℝ) 1)) ×ˢ
        (Set.univ : Set Circle) ⊆ E ⁻¹' N := by
      rintro ⟨t, w⟩ ⟨ht, hw⟩
      have ht0 : t = ⟨0, by norm_num⟩ := Set.mem_singleton_iff.mp ht
      change E (t, w) ∈ N
      rw [ht0, hcore]
      exact hbN (Set.mem_range_self w)
    obtain ⟨U, V, hU, hV, hzero, huniv, hUV⟩ := generalized_tube_lemma
      isCompact_singleton isCompact_univ (hN.preimage E.continuous) hprod
    refine ⟨E, U, hE, hcore, hU, hzero (Set.mem_singleton _), ?_⟩
    rintro y ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
    exact hUV ⟨ht, huniv (Set.mem_univ w)⟩
  have hcollarThin (b : EssentialCurve S) (N : Set S)
      (hN : IsOpen N) (hbN : b.val.image ⊆ N) :
      ∃ (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (δ : ℝ),
        Topology.IsOpenEmbedding E ∧
        (∀ w, E (⟨0, by norm_num⟩, w) = b.val.map w) ∧
        0 < δ ∧ δ < 1 ∧
        ∀ (t : Set.Ioo (-1 : ℝ) 1) (w : Circle), |(t : ℝ)| ≤ δ → E (t, w) ∈ N := by
    obtain ⟨E, U, hE, hcore, hU, hzero, hEN⟩ := hcollarInNeighborhood b N hN hbN
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU _ hzero
    let δ := min (ε / 2) (1 / 2)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨E, δ, hE, hcore, hδ, lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
    intro t w ht
    apply hEN
    refine ⟨(t, w), ⟨hεU ?_, Set.mem_univ _⟩, rfl⟩
    change dist (t : ℝ) (0 : ℝ) < ε
    simpa only [Real.dist_eq, sub_zero] using lt_of_le_of_lt ht hδε
  have hfaceCollars (σ : Finset ↥Fv)
      (hz : ∀ i j : ↥σ, i ≠ j → geometricIntersection i.val.val j.val.val = 0) :
      ∃ (E : ↥σ → C(Set.Ioo (-1 : ℝ) 1 × Circle, S))
        (U : ↥σ → Set (Set.Ioo (-1 : ℝ) 1)),
        (∀ i, Topology.IsOpenEmbedding (E i) ∧
          (∀ w, E i (⟨0, by norm_num⟩, w) = (source_r i.val.val i.val.property).val.map w) ∧
          IsOpen (U i) ∧ (⟨0, by norm_num⟩ : Set.Ioo (-1 : ℝ) 1) ∈ U i ∧
          E i '' (U i ×ˢ Set.univ) ⊆ Dᶜ) ∧
        ∀ i j, i ≠ j → Disjoint
          (E i '' (U i ×ˢ Set.univ)) (E j '' (U j ×ˢ Set.univ)) := by
    obtain ⟨N, hN, hdN⟩ := hfaceNeighborhoods σ hz
    choose E U hE hcore hU hzero hEN using fun i =>
      hcollarInNeighborhood (source_r i.val.val i.val.property) (N i) (hN i).1 (hN i).2.1
    refine ⟨E, U, ?_, ?_⟩
    · intro i
      exact ⟨hE i, hcore i, hU i, hzero i, (hEN i).trans (hN i).2.2⟩
    · intro i j hij
      exact (hdN i j hij).mono (hEN i) (hEN j)
  have hwidthSlide (ρ a : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (ha : |a| < ρ) :
      ∃ H : AmbientIsotopy (Set.Ioo (-1 : ℝ) 1 × Circle),
        (∀ w, H.finalMap (⟨0, by norm_num⟩, w) =
          (⟨a, by constructor <;> linarith [(abs_lt.mp ha).1, (abs_lt.mp ha).2]⟩, w)) ∧
        ∀ t z, ρ ≤ |(z.1 : ℝ)| → H.map (t,z) = z := by
    let bump : ℝ → ℝ := fun x => max (ρ - |x|) 0
    let f : Interval → ℝ → ℝ := fun t x => x + ((t : ℝ) * a / ρ) * bump x
    have hf : Continuous (fun z : Interval × ℝ => f z.1 z.2) := by
      dsimp [f, bump]
      fun_prop
    have hfix (t : Interval) (x : ℝ) (hx : ρ ≤ |x|) : f t x = x := by
      simp [f, bump, max_eq_right (sub_nonpos.mpr hx)]
    have hmono (t : Interval) : StrictMono (f t) := by
      have hs : |(t : ℝ) * a / ρ| < 1 := by
        rw [abs_div, abs_mul, abs_of_nonneg t.property.1, abs_of_pos hρ]
        apply (div_lt_one hρ).mpr
        nlinarith [t.property.2, abs_nonneg a]
      intro x y hxy
      have hb : |bump y - bump x| ≤ y - x := by
        calc
          |bump y - bump x| ≤ |(ρ - |y|) - (ρ - |x|)| := abs_max_sub_max_le_abs _ _ _
          _ = abs (abs y - abs x) := by
            rw [show (ρ - |y|) - (ρ - |x|) = -(|y| - |x|) by ring, abs_neg]
          _ ≤ |y - x| := abs_abs_sub_abs_le_abs_sub y x
          _ = y - x := abs_of_pos (sub_pos.mpr hxy)
      have hprod := mul_le_mul_of_nonneg_left hb (abs_nonneg ((t : ℝ)*a/ρ))
      have hneg := neg_abs_le (((t : ℝ)*a/ρ) * (bump y - bump x))
      rw [abs_mul] at hneg
      dsimp [f]
      nlinarith [sub_pos.mpr hxy]
    have hsurj (t : Interval) : Function.Surjective (f t) := by
      intro y
      let L := min y (-ρ)
      let U := max y ρ
      have hL : ρ ≤ |L| := by
        have hh : L ≤ -ρ := min_le_right _ _
        linarith [neg_le_abs L]
      have hU : ρ ≤ |U| := (le_max_right _ _).trans (le_abs_self U)
      have hLU : L ≤ U := (min_le_left _ _).trans (le_max_left _ _)
      have hy : y ∈ Set.Icc (f t L) (f t U) := by
        rw [hfix t L hL, hfix t U hU]
        exact ⟨min_le_left _ _, le_max_left _ _⟩
      obtain ⟨x, hx, he⟩ := intermediate_value_Icc hLU
        ((hf.comp (continuous_const.prodMk continuous_id)).continuousOn) hy
      exact ⟨x, he⟩
    have hbound (t : Interval) (x : Set.Ioo (-1 : ℝ) 1) : f t x.val ∈ Set.Ioo (-1 : ℝ) 1 := by
      have hm := hmono t x.property.1
      have hp := hmono t x.property.2
      rw [hfix t (-1) (by simpa using hρ1.le)] at hm
      rw [hfix t 1 (by simpa using hρ1.le)] at hp
      exact ⟨hm, hp⟩
    let width : Interval → Set.Ioo (-1 : ℝ) 1 → Set.Ioo (-1 : ℝ) 1 :=
      fun t x => ⟨f t x.val, hbound t x⟩
    have hwc : Continuous (fun z : Interval × Set.Ioo (-1 : ℝ) 1 => width z.1 z.2) :=
      (hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    have hwmono (t : Interval) : StrictMono (width t) := fun x y hxy => hmono t hxy
    have hwsurj (t : Interval) : Function.Surjective (width t) := by
      intro y
      obtain ⟨x, hx⟩ := hsurj t y.val
      have hxlo : -1 < x := by
        apply (hmono t).lt_iff_lt.mp
        rw [hfix t (-1) (by simpa using hρ1.le), hx]
        exact y.property.1
      have hxhi : x < 1 := by
        apply (hmono t).lt_iff_lt.mp
        rw [hfix t 1 (by simpa using hρ1.le), hx]
        exact y.property.2
      exact ⟨⟨x, hxlo, hxhi⟩, Subtype.ext hx⟩
    let H : AmbientIsotopy (Set.Ioo (-1 : ℝ) 1 × Circle) := {
      map := ⟨fun z => (width z.1 z.2.1, z.2.2),
        (hwc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
          (continuous_snd.comp continuous_snd)⟩
      homeomorphism_at := by
        intro t
        let q := (hwmono t).orderIsoOfRightInverse (width t)
          (fun y => Classical.choose (hwsurj t y)) (fun y => Classical.choose_spec (hwsurj t y))
        refine ⟨q.toHomeomorph.prodCongr (Homeomorph.refl Circle), fun z => rfl⟩
      at_zero := by
        intro z
        apply Prod.ext
        · apply Subtype.ext
          simp [width, f]
        · rfl }
    refine ⟨H, ?_, ?_⟩
    · intro w
      apply Prod.ext
      · apply Subtype.ext
        change f ⟨1, by norm_num⟩ 0 = a
        simp [f, bump, max_eq_left hρ.le, ne_of_gt hρ]
      · rfl
    · intro t z hz
      apply Prod.ext
      · apply Subtype.ext
        exact hfix t z.1.val hz
      · rfl
  have hcompactCollarGeometry
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
      ∃ (B V : Set S) (cminus cplus : Curve S),
        IsCompact B ∧ IsOpen V ∧ V ⊆ B ∧
        Set.range (fun w : Circle => E (⟨0, by norm_num⟩, w)) ⊆ V ∧
        frontier V ⊆ cminus.image ∪ cplus.image ∧
        Disjoint cminus.image cplus.image ∧
        B = E '' {z | |(z.1 : ℝ)| ≤ δ} ∧
        V = E '' {z | |(z.1 : ℝ)| < δ} ∧
        cminus.map = (fun w => E (⟨-δ, by constructor <;> linarith⟩, w)) ∧
        cplus.map = (fun w => E (⟨δ, by constructor <;> linarith⟩, w)) := by
    let tm : Set.Ioo (-1 : ℝ) 1 := ⟨-δ, by constructor <;> linarith⟩
    let tp : Set.Ioo (-1 : ℝ) 1 := ⟨δ, by constructor <;> linarith⟩
    let cm : Curve S := ⟨fun w => E (tm, w), hE.isEmbedding.comp (isEmbedding_prodMkRight tm)⟩
    let cp : Curve S := ⟨fun w => E (tp, w), hE.isEmbedding.comp (isEmbedding_prodMkRight tp)⟩
    let K : Set (Set.Ioo (-1 : ℝ) 1 × Circle) := {z | |(z.1 : ℝ)| ≤ δ}
    let W : Set (Set.Ioo (-1 : ℝ) 1 × Circle) := {z | |(z.1 : ℝ)| < δ}
    let f : Set.Icc (-δ) δ → Set.Ioo (-1 : ℝ) 1 := fun t =>
      ⟨t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    have hK : IsCompact K := by
      have heq : K = (f '' Set.univ) ×ˢ (Set.univ : Set Circle) := by
        ext z
        constructor
        · intro hz
          refine ⟨⟨⟨z.1.val, abs_le.mp hz⟩, Set.mem_univ _, ?_⟩, Set.mem_univ _⟩
          exact Subtype.ext rfl
        · rintro ⟨⟨t, ht, he⟩, hw⟩
          have hv : t.val = z.1.val := congrArg Subtype.val he
          exact abs_le.mpr (hv ▸ t.property)
      rw [heq]
      exact (isCompact_univ.image hf).prod isCompact_univ
    have hW : IsOpen W := isOpen_Iio.preimage
      (continuous_abs.comp (continuous_subtype_val.comp continuous_fst))
    have hB : IsCompact (E '' K) := hK.image E.continuous
    have hV : IsOpen (E '' W) := hE.isOpenMap W hW
    have hVB : E '' W ⊆ E '' K := Set.image_mono (by
      intro z hz
      change |(z.1 : ℝ)| ≤ δ
      change |(z.1 : ℝ)| < δ at hz
      exact hz.le)
    refine ⟨E '' K, E '' W, cm, cp, hB, hV, hVB, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · rintro y ⟨w, rfl⟩
      exact ⟨(⟨0, by norm_num⟩, w), by simpa [W] using hδ, rfl⟩
    · intro y hy
      have hyB : y ∈ E '' K :=
        (closure_minimal hVB hB.isClosed) hy.1
      obtain ⟨⟨t, w⟩, ht, rfl⟩ := hyB
      have hn : ¬ |(t : ℝ)| < δ := by
        intro hh
        apply hy.2
        rw [hV.interior_eq]
        exact ⟨(t,w), hh, rfl⟩
      have habs : |(t : ℝ)| = δ := le_antisymm ht (not_lt.mp hn)
      rcases (abs_eq hδ.le).mp habs with hp | hm
      · right
        exact ⟨w, congrArg (fun u => E (u,w)) (Subtype.ext hp).symm⟩
      · left
        exact ⟨w, congrArg (fun u => E (u,w)) (Subtype.ext hm).symm⟩
    · apply Set.disjoint_left.mpr
      rintro y ⟨u, hu⟩ ⟨w, hw⟩
      have he := hE.injective (hu.trans hw.symm)
      have ht := congrArg (fun z : Set.Ioo (-1 : ℝ) 1 × Circle => (z.1 : ℝ)) he
      change -δ = δ at ht
      linarith
  have hbandClosure
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
      closure (E '' {z | |(z.1 : ℝ)| < δ}) = E '' {z | |(z.1 : ℝ)| ≤ δ} := by
    let tm : Set.Ioo (-1 : ℝ) 1 := ⟨-δ, by constructor <;> linarith⟩
    let tp : Set.Ioo (-1 : ℝ) 1 := ⟨δ, by constructor <;> linarith⟩
    have hw : {z : Set.Ioo (-1 : ℝ) 1 × Circle | |(z.1 : ℝ)| < δ} =
        Set.Ioo tm tp ×ˢ Set.univ := by
      ext z
      change |(z.1 : ℝ)| < δ ↔ (-δ < (z.1 : ℝ) ∧ (z.1 : ℝ) < δ) ∧ True
      simp only [abs_lt, and_true]
    have hk : {z : Set.Ioo (-1 : ℝ) 1 × Circle | |(z.1 : ℝ)| ≤ δ} =
        Set.Icc tm tp ×ˢ Set.univ := by
      ext z
      change |(z.1 : ℝ)| ≤ δ ↔ (-δ ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ δ) ∧ True
      simp only [abs_le, and_true]
    have hneq : tm ≠ tp := by
      intro he
      have hv := congrArg Subtype.val he
      change -δ = δ at hv
      linarith
    have hc : closure {z : Set.Ioo (-1 : ℝ) 1 × Circle | |(z.1 : ℝ)| < δ} =
        {z : Set.Ioo (-1 : ℝ) 1 × Circle | |(z.1 : ℝ)| ≤ δ} := by
      rw [hw, closure_prod_eq, closure_Ioo hneq, closure_univ, hk]
    obtain ⟨B,V,cm,cp,hB,hV,hVB,hcenter,hfront,hdist,hBdef,hVdef,hm,hp⟩ :=
      hcompactCollarGeometry E hE δ hδ hδ1
    apply Set.Subset.antisymm
    · rw [← hVdef, ← hBdef]
      exact closure_minimal hVB hB.isClosed
    · rw [← hc]
      exact image_closure_subset_closure_image E.continuous
  have hbandFrontierExact
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
      frontier (E '' {z | |(z.1 : ℝ)| ≤ δ}) =
        Set.range (fun w : Circle => E (⟨-δ, by constructor <;> linarith⟩, w)) ∪
        Set.range (fun w : Circle => E (⟨δ, by constructor <;> linarith⟩, w)) := by
    let tm : Set.Ioo (-1 : ℝ) 1 := ⟨-δ, by constructor <;> linarith⟩
    let tp : Set.Ioo (-1 : ℝ) 1 := ⟨δ, by constructor <;> linarith⟩
    let K : Set (Set.Ioo (-1 : ℝ) 1 × Circle) := {z | |(z.1 : ℝ)| ≤ δ}
    have hK : K = Set.Icc tm tp ×ˢ Set.univ := by
      ext z
      change |(z.1 : ℝ)| ≤ δ ↔ (-δ ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ δ) ∧ True
      simp only [abs_le, and_true]
    have horder : tm ≤ tp := by change -δ ≤ δ; linarith
    have hfrontK : frontier K = ({tm,tp} : Set (Set.Ioo (-1 : ℝ) 1)) ×ˢ Set.univ := by
      rw [hK, frontier_prod_eq]
      simp only [frontier_univ, Set.prod_empty, Set.empty_union, frontier_Icc horder, closure_univ]
    have hpre : E ⁻¹' (E '' K) = K := by
      ext z
      constructor
      · rintro ⟨w,hw,he⟩
        exact (hE.injective he) ▸ hw
      · intro hz
        exact ⟨z,hz,rfl⟩
    have hreverse : E '' frontier K ⊆ frontier (E '' K) := by
      rintro y ⟨z,hz,rfl⟩
      have hh := E.continuous.frontier_preimage_subset (E '' K)
      rw [hpre] at hh
      exact hh hz
    have hside : E '' frontier K = Set.range (fun w : Circle => E (tm,w)) ∪
        Set.range (fun w : Circle => E (tp,w)) := by
      rw [hfrontK]
      ext y
      constructor
      · rintro ⟨⟨t,w⟩,⟨ht,hw⟩,rfl⟩
        rcases Set.mem_insert_iff.mp ht with hm | hp
        · exact Or.inl ⟨w,congrArg (fun t => E (t,w)) hm.symm⟩
        · exact Or.inr ⟨w,congrArg (fun t => E (t,w)) (Set.mem_singleton_iff.mp hp).symm⟩
      · rintro (⟨w,rfl⟩|⟨w,rfl⟩)
        · exact ⟨(tm,w),⟨Set.mem_insert _ _,Set.mem_univ _⟩,rfl⟩
        · exact ⟨(tp,w),⟨Set.mem_insert_of_mem _ (Set.mem_singleton _),Set.mem_univ _⟩,rfl⟩
    obtain ⟨B,V,cm,cp,hB,hV,hVB,hcenter,hfront,hdist,hBdef,hVdef,hm,hp⟩ :=
      hcompactCollarGeometry E hE δ hδ hδ1
    apply Set.Subset.antisymm
    · rw [← hbandClosure E hE δ hδ hδ1]
      have hh := frontier_closure_subset.trans hfront
      rw [hVdef] at hh
      change frontier (closure (E '' {z | |(z.1 : ℝ)| < δ})) ⊆ _
      change frontier (closure (E '' {z | |(z.1 : ℝ)| < δ})) ⊆
        Set.range cm.map ∪ Set.range cp.map at hh
      rw [hm,hp] at hh
      exact hh
    · rw [← hside]
      exact hreverse
  have hupperOneSidedCollar
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
      (N : Set S) (hN : IsOpen N)
      (hBN : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ N)
      (A : Set S)
      (hBA : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ A)
      (hNA : N ∩ A ⊆ E '' {z | |(z.1 : ℝ)| ≤ δ}) (z0 : S) :
      (closure (connectedComponentIn Aᶜ z0) ∩
        Set.range (fun w : Circle => E (⟨δ, by constructor <;> linarith⟩, w))).Nonempty →
      ∃ η : ℝ, 0 < η ∧ δ + η < 1 ∧
        E '' {z | δ < (z.1 : ℝ) ∧ (z.1 : ℝ) < δ + η} ⊆
          connectedComponentIn Aᶜ z0 ∧
        Set.range (fun w : Circle => E (⟨δ, by constructor <;> linarith⟩, w)) ⊆
          closure (connectedComponentIn Aᶜ z0) := by
    let tm : Set.Ioo (-1 : ℝ) 1 := ⟨δ, by constructor <;> linarith⟩
    have hp : ({tm} : Set (Set.Ioo (-1 : ℝ) 1)) ×ˢ (Set.univ : Set Circle) ⊆ E ⁻¹' N := by
      rintro ⟨t,w⟩ ⟨ht,hw⟩
      have he : t = tm := Set.mem_singleton_iff.mp ht
      apply hBN
      refine ⟨(t,w),?_,rfl⟩
      rw [he]
      change |δ| ≤ δ
      rw [abs_of_pos hδ]
    obtain ⟨U,V,hU,hV,hmU,huniv,hUV⟩ := generalized_tube_lemma
      isCompact_singleton isCompact_univ (hN.preimage E.continuous) hp
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU tm (hmU (Set.mem_singleton _))
    let η := min (ε / 2) (min (δ / 2) ((1-δ)/2))
    have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
    have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηδ : η < δ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    have hη1 : η < 1-δ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
    let tp : Set.Ioo (-1 : ℝ) 1 := ⟨δ+η,by constructor <;> linarith⟩
    have hmtp : tm < tp := by change δ < δ+η; linarith
    let T : Set (Set.Ioo (-1 : ℝ) 1 × Circle) := {z | |(z.1 : ℝ)-δ| < η}
    have hTo : IsOpen T := isOpen_Iio.preimage
      (continuous_abs.comp ((continuous_subtype_val.comp continuous_fst).sub continuous_const))
    have hTN : E '' T ⊆ N := by
      rintro y ⟨⟨t,w⟩,ht,rfl⟩
      apply hUV
      refine ⟨hεU ?_,huniv (Set.mem_univ _)⟩
      change |(t : ℝ)-δ| < ε
      exact ht.trans hηε
    let W : Set (Set.Ioo (-1 : ℝ) 1 × Circle) := Set.Ioo tm tp ×ˢ Set.univ
    have hWT : W ⊆ T := by
      rintro ⟨t,w⟩ ⟨ht,hw⟩
      change |(t : ℝ)-δ| < η
      have htδ : δ < (t : ℝ) := ht.1
      rw [abs_of_pos (sub_pos.mpr htδ)]
      change (t : ℝ)-δ < η
      have hh : (t : ℝ) < δ+η := ht.2
      linarith
    have hWA : E '' W ⊆ Aᶜ := by
      rintro y ⟨⟨t,w⟩,⟨ht,hw⟩,rfl⟩ hyA
      have hyN := hTN ⟨(t,w),hWT ⟨ht,hw⟩,rfl⟩
      obtain ⟨z,hz,he⟩ := hNA ⟨hyN,hyA⟩
      have hez : z = (t,w) := hE.injective he
      rw [hez] at hz
      have hδt : δ < (t : ℝ) := ht.1
      have htpos : 0 < (t : ℝ) := hδ.trans hδt
      change |(t : ℝ)| ≤ δ at hz
      rw [abs_of_pos htpos] at hz
      exact (not_le.mpr hδt) hz
    have hintervalConnected : IsConnected (Set.Ioo tm tp) := by
      let F : Set.Ioo δ (δ+η) → Set.Ioo (-1 : ℝ) 1 := fun z =>
        ⟨z.val,by constructor <;> linarith [z.property.1,z.property.2]⟩
      have hF : Continuous F := continuous_subtype_val.subtype_mk _
      letI : ConnectedSpace (Set.Ioo δ (δ+η)) :=
        isConnected_iff_connectedSpace.mp (isConnected_Ioo (by linarith))
      have hrange : Set.range F = Set.Ioo tm tp := by
        ext t
        constructor
        · rintro ⟨z,rfl⟩
          exact z.property
        · intro ht
          exact ⟨⟨t.val,ht⟩,Subtype.ext rfl⟩
      rw [← hrange]
      exact isConnected_range hF
    have hWconnected : IsConnected (E '' W) :=
      (hintervalConnected.prod (isConnected_univ : IsConnected (Set.univ : Set Circle))).image
        E E.continuous.continuousOn
    intro hmeet
    obtain ⟨y,hyC,w,hyw⟩ := hmeet
    have hyT : y ∈ E '' T := by
      rw [← hyw]
      exact ⟨(tm,w),by change |δ-δ| < η; simpa using hη,rfl⟩
    obtain ⟨z,hzT,hzC⟩ := (mem_closure_iff.mp hyC) (E '' T) (hE.isOpenMap T hTo) hyT
    obtain ⟨⟨t,u⟩,ht,hz⟩ := hzT
    have hznotB : ¬ |(t : ℝ)| ≤ δ := by
      intro hle
      apply connectedComponentIn_subset Aᶜ z0 hzC
      rw [← hz]
      exact hBA ⟨(t,u),hle,rfl⟩
    have htt : δ-η < (t : ℝ) ∧ (t : ℝ) < δ+η := by
      change |(t : ℝ)-δ| < η at ht
      have hh := abs_lt.mp ht
      constructor <;> linarith
    have htpos : 0 < (t : ℝ) := by linarith [htt.1]
    have htδ : δ < (t : ℝ) := by
      rw [abs_of_pos htpos] at hznotB
      exact not_le.mp hznotB
    have hzW : z ∈ E '' W := ⟨(t,u),⟨⟨htδ,htt.2⟩,Set.mem_univ _⟩,hz⟩
    have hWC : E '' W ⊆ connectedComponentIn Aᶜ z0 := by
      have hh := hWconnected.isPreconnected.subset_connectedComponentIn hzW hWA
      rw [← connectedComponentIn_eq hzC] at hh
      exact hh
    refine ⟨η,hη,by linarith,?_,?_⟩
    · rintro y ⟨⟨t,w⟩,ht,rfl⟩
      exact hWC ⟨(t,w),⟨ht,Set.mem_univ _⟩,rfl⟩
    rintro y ⟨w,rfl⟩
    apply closure_mono hWC
    apply image_closure_subset_closure_image E.continuous
    refine ⟨(tm,w),?_,rfl⟩
    rw [closure_prod_eq,closure_Ioo hmtp.ne,closure_univ]
    exact ⟨⟨le_refl tm,hmtp.le⟩,Set.mem_univ _⟩
  have hupperCircleRetention
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
      (N : Set S) (hN : IsOpen N)
      (hBN : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ N)
      (A : Set S)
      (hBA : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ A)
      (hNA : N ∩ A ⊆ E '' {z | |(z.1 : ℝ)| ≤ δ}) (z0 : S) :
      (closure (connectedComponentIn Aᶜ z0) ∩
        Set.range (fun w : Circle => E (⟨δ, by constructor <;> linarith⟩, w))).Nonempty →
      Set.range (fun w : Circle => E (⟨δ, by constructor <;> linarith⟩, w)) ⊆
        closure (connectedComponentIn Aᶜ z0) := by
    intro hm
    obtain ⟨η,hη,hη1,hstrip,hcircle⟩ :=
      hupperOneSidedCollar E hE δ hδ hδ1 N hN hBN A hBA hNA z0 hm
    exact hcircle
  have hlowerOneSidedCollar
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
      (N : Set S) (hN : IsOpen N)
      (hBN : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ N)
      (A : Set S)
      (hBA : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ A)
      (hNA : N ∩ A ⊆ E '' {z | |(z.1 : ℝ)| ≤ δ}) (z0 : S) :
      (closure (connectedComponentIn Aᶜ z0) ∩
        Set.range (fun w : Circle => E (⟨-δ, by constructor <;> linarith⟩, w))).Nonempty →
      ∃ η : ℝ, 0 < η ∧ δ + η < 1 ∧
        E '' {z | -δ - η < (z.1 : ℝ) ∧ (z.1 : ℝ) < -δ} ⊆
          connectedComponentIn Aᶜ z0 ∧
        Set.range (fun w : Circle => E (⟨-δ, by constructor <;> linarith⟩, w)) ⊆
          closure (connectedComponentIn Aᶜ z0) := by
    let f : Set.Ioo (-1 : ℝ) 1 × Circle → Set.Ioo (-1 : ℝ) 1 × Circle := fun z =>
      (⟨-z.1.val,by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩,z.2)
    have hf : Continuous f :=
      ((continuous_neg.comp (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk
        continuous_snd
    have hff : Function.Involutive f := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        exact neg_neg z.1.val
      · rfl
    let rev : (Set.Ioo (-1 : ℝ) 1 × Circle) ≃ₜ (Set.Ioo (-1 : ℝ) 1 × Circle) := {
      toFun := f
      invFun := f
      left_inv := hff
      right_inv := hff
      continuous_toFun := hf
      continuous_invFun := hf }
    let E' : C(Set.Ioo (-1 : ℝ) 1 × Circle,S) := E.comp ⟨rev,rev.continuous⟩
    have hE' : Topology.IsOpenEmbedding E' := hE.comp rev.isOpenEmbedding
    have heq : E' '' {z | |(z.1 : ℝ)| ≤ δ} = E '' {z | |(z.1 : ℝ)| ≤ δ} := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        refine ⟨f z,?_,rfl⟩
        change |-z.1.val| ≤ δ
        change |z.1.val| ≤ δ at hz
        simpa only [abs_neg] using hz
      · rintro ⟨z,hz,rfl⟩
        refine ⟨f z,?_,?_⟩
        · change |-z.1.val| ≤ δ
          change |z.1.val| ≤ δ at hz
          simpa only [abs_neg] using hz
        · exact congrArg E (hff z)
    intro hm
    have hBN' : E' '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ N := by rw [heq]; exact hBN
    have hBA' : E' '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ A := by rw [heq]; exact hBA
    have hNA' : N ∩ A ⊆ E' '' {z | |(z.1 : ℝ)| ≤ δ} := by rw [heq]; exact hNA
    obtain ⟨η,hη,hη1,hstrip,hcircle⟩ :=
      hupperOneSidedCollar E' hE' δ hδ hδ1 N hN hBN' A hBA' hNA' z0 hm
    refine ⟨η,hη,hη1,?_,hcircle⟩
    rintro y ⟨⟨t,w⟩,ht,rfl⟩
    have hfmem : δ < ((f (t,w)).1 : ℝ) ∧ ((f (t,w)).1 : ℝ) < δ+η := by
      change δ < -(t : ℝ) ∧ -(t : ℝ) < δ+η
      constructor <;> linarith [ht.1,ht.2]
    apply hstrip
    refine ⟨f (t,w),hfmem,?_⟩
    exact congrArg E (hff (t,w))
  have hlowerCircleRetention
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
      (N : Set S) (hN : IsOpen N)
      (hBN : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ N)
      (A : Set S)
      (hBA : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ A)
      (hNA : N ∩ A ⊆ E '' {z | |(z.1 : ℝ)| ≤ δ}) (z0 : S) :
      (closure (connectedComponentIn Aᶜ z0) ∩
        Set.range (fun w : Circle => E (⟨-δ, by constructor <;> linarith⟩, w))).Nonempty →
      Set.range (fun w : Circle => E (⟨-δ, by constructor <;> linarith⟩, w)) ⊆
        closure (connectedComponentIn Aᶜ z0) := by
    intro hm
    obtain ⟨η,hη,hη1,hstrip,hcircle⟩ :=
      hlowerOneSidedCollar E hE δ hδ hδ1 N hN hBN A hBA hNA z0 hm
    exact hcircle
  have hupperHalfspaceChart
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
      (N : Set S) (hN : IsOpen N)
      (hBN : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ N)
      (A : Set S)
      (hBA : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ A)
      (hNA : N ∩ A ⊆ E '' {z | |(z.1 : ℝ)| ≤ δ}) (z0 : S) :
      (closure (connectedComponentIn Aᶜ z0) ∩
        Set.range (fun w : Circle => E (⟨δ, by constructor <;> linarith⟩, w))).Nonempty →
      ∃ ε : ℝ, 0 < ε ∧ δ + ε < 1 ∧
        ∀ z : Set.Ioo (-1 : ℝ) 1 × Circle, |(z.1 : ℝ)-δ| < ε →
          (E z ∈ closure (connectedComponentIn Aᶜ z0) ↔ δ ≤ (z.1 : ℝ)) := by
    intro hm
    obtain ⟨η,hη,hη1,hstrip,hcircle⟩ :=
      hupperOneSidedCollar E hE δ hδ hδ1 N hN hBN A hBA hNA z0 hm
    let ε := min η (δ/2)
    have hε : 0 < ε := lt_min hη (by positivity)
    have hεη : ε ≤ η := min_le_left _ _
    have hεδ : ε < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    refine ⟨ε,hε,by linarith,?_⟩
    intro z hz
    have hbox := abs_lt.mp hz
    constructor
    · intro hy
      by_contra hn
      have htδ : (z.1 : ℝ) < δ := not_le.mp hn
      let V : Set (Set.Ioo (-1 : ℝ) 1 × Circle) := {u | |(u.1 : ℝ)| < δ}
      have hVo : IsOpen V := isOpen_Iio.preimage
        (continuous_abs.comp (continuous_subtype_val.comp continuous_fst))
      have hVA : E '' V ⊆ A := by
        rintro y ⟨u,hu,rfl⟩
        apply hBA
        refine ⟨u,?_,rfl⟩
        change |(u.1 : ℝ)| ≤ δ
        change |(u.1 : ℝ)| < δ at hu
        exact hu.le
      have hzV : z ∈ V := by
        change |(z.1 : ℝ)| < δ
        apply abs_lt.mpr
        constructor <;> linarith [hbox.1]
      have hyI : E z ∈ interior A :=
        interior_maximal hVA (hE.isOpenMap V hVo) ⟨z,hzV,rfl⟩
      have hyCl : E z ∈ closure Aᶜ :=
        closure_mono (connectedComponentIn_subset Aᶜ z0) hy
      rw [closure_compl] at hyCl
      exact hyCl hyI
    · intro ht
      rcases eq_or_lt_of_le ht with he | hlt
      · apply hcircle
        refine ⟨z.2,?_⟩
        apply congrArg E
        apply Prod.ext
        · apply Subtype.ext
          exact he
        · rfl
      · apply subset_closure
        apply hstrip
        refine ⟨z,⟨hlt,?_⟩,rfl⟩
        linarith [hbox.2]
  have hlowerHalfspaceChart
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
      (N : Set S) (hN : IsOpen N)
      (hBN : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ N)
      (A : Set S)
      (hBA : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ A)
      (hNA : N ∩ A ⊆ E '' {z | |(z.1 : ℝ)| ≤ δ}) (z0 : S) :
      (closure (connectedComponentIn Aᶜ z0) ∩
        Set.range (fun w : Circle => E (⟨-δ, by constructor <;> linarith⟩, w))).Nonempty →
      ∃ ε : ℝ, 0 < ε ∧ δ + ε < 1 ∧
        ∀ z : Set.Ioo (-1 : ℝ) 1 × Circle, |(z.1 : ℝ)+δ| < ε →
          (E z ∈ closure (connectedComponentIn Aᶜ z0) ↔ (z.1 : ℝ) ≤ -δ) := by
    let f : Set.Ioo (-1 : ℝ) 1 × Circle → Set.Ioo (-1 : ℝ) 1 × Circle := fun z =>
      (⟨-z.1.val,by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩,z.2)
    have hf : Continuous f :=
      ((continuous_neg.comp (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk
        continuous_snd
    have hff : Function.Involutive f := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        exact neg_neg z.1.val
      · rfl
    let rev : (Set.Ioo (-1 : ℝ) 1 × Circle) ≃ₜ (Set.Ioo (-1 : ℝ) 1 × Circle) := {
      toFun := f
      invFun := f
      left_inv := hff
      right_inv := hff
      continuous_toFun := hf
      continuous_invFun := hf }
    let E' : C(Set.Ioo (-1 : ℝ) 1 × Circle,S) := E.comp ⟨rev,rev.continuous⟩
    have hE' : Topology.IsOpenEmbedding E' := hE.comp rev.isOpenEmbedding
    have heq : E' '' {z | |(z.1 : ℝ)| ≤ δ} = E '' {z | |(z.1 : ℝ)| ≤ δ} := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        refine ⟨f z,?_,rfl⟩
        change |-z.1.val| ≤ δ
        change |z.1.val| ≤ δ at hz
        simpa only [abs_neg] using hz
      · rintro ⟨z,hz,rfl⟩
        refine ⟨f z,?_,?_⟩
        · change |-z.1.val| ≤ δ
          change |z.1.val| ≤ δ at hz
          simpa only [abs_neg] using hz
        · exact congrArg E (hff z)
    intro hm
    have hBN' : E' '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ N := by rw [heq]; exact hBN
    have hBA' : E' '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ A := by rw [heq]; exact hBA
    have hNA' : N ∩ A ⊆ E' '' {z | |(z.1 : ℝ)| ≤ δ} := by rw [heq]; exact hNA
    obtain ⟨ε,hε,hε1,hchart⟩ :=
      hupperHalfspaceChart E' hE' δ hδ hδ1 N hN hBN' A hBA' hNA' z0 hm
    refine ⟨ε,hε,hε1,?_⟩
    intro z hz
    have hbox : |((f z).1 : ℝ)-δ| < ε := by
      change |-(z.1 : ℝ)-δ| < ε
      have he : -(z.1 : ℝ)-δ = -((z.1 : ℝ)+δ) := by ring
      rw [he,abs_neg]
      exact hz
    have hh := hchart (f z) hbox
    have hEf : E' (f z) = E z := congrArg E (hff z)
    rw [hEf] at hh
    change (E z ∈ closure (connectedComponentIn Aᶜ z0) ↔ δ ≤ -(z.1 : ℝ)) at hh
    constructor
    · intro hy
      have ht := hh.mp hy
      linarith
    · intro ht
      apply hh.mpr
      linarith
  have hfaceRegularNeighborhoods (σ : Finset ↥Fv)
      (hz : ∀ i j : ↥σ, i ≠ j → geometricIntersection i.val.val j.val.val = 0) :
      ∃ (B V : ↥σ → Set S) (cm cp : ↥σ → Curve S),
        (∀ i, IsCompact (B i) ∧ IsOpen (V i) ∧ V i ⊆ B i ∧
          (source_r i.val.val i.val.property).val.image ⊆ V i ∧ B i ⊆ Dᶜ ∧
          frontier (V i) ⊆ (cm i).image ∪ (cp i).image ∧
          Disjoint (cm i).image (cp i).image) ∧
        ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
    obtain ⟨N, hN, hdN⟩ := hfaceNeighborhoods σ hz
    choose E δ hE hcore hδ hδ1 hEN using fun i =>
      hcollarThin (source_r i.val.val i.val.property) (N i) (hN i).1 (hN i).2.1
    choose B V cm cp hB hV hVB hcenter hfront hdist hBdef hVdef hmmap hpmap using fun i =>
      hcompactCollarGeometry (E i) (hE i) (δ i) (hδ i) (hδ1 i)
    have hBN (i : ↥σ) : B i ⊆ N i := by
      rw [hBdef i]
      rintro y ⟨⟨t,w⟩, ht, rfl⟩
      exact hEN i t w ht
    refine ⟨B, V, cm, cp, ?_, ?_⟩
    · intro i
      refine ⟨hB i, hV i, hVB i, ?_, (hBN i).trans (hN i).2.2, hfront i, hdist i⟩
      intro y hy
      obtain ⟨w, rfl⟩ := hy
      apply hcenter i
      exact ⟨w, hcore i w⟩
    · intro i j hij
      exact (hdN i j hij).mono (hBN i) (hBN j)
  -- An actual uniformly compactly supported punctured isotopy caps by identity.
  have hopenSupported (U : Set S) (hUopen : IsOpen U) (H : AmbientIsotopy ↥U) (K : Set S)
      (hK : IsCompact K) (hKP : K ⊆ U)
      (hfix : ∀ t (y : ↥U), y.val ∉ K → H.map (t, y) = y) :
      ∃ G : AmbientIsotopy S,
        (∀ t (y : ↥U), G.map (t, y.val) = (H.map (t, y)).val) ∧
        (∀ t y, y ∉ U → G.map (t, y) = y) := by
    let F : Interval × S → S := fun z =>
      if hz : z.2 ∈ U then (H.map (z.1, ⟨z.2, hz⟩)).val else z.2
    have hFin (t : Interval) (y : ↥U) : F (t, y.val) = (H.map (t, y)).val := by
      dsimp [F]
      rw [dif_pos y.property]
    have hFout (t : Interval) (y : S) (hy : y ∉ K) : F (t, y) = y := by
      dsimp [F]
      split_ifs with hyP
      · exact congrArg Subtype.val (hfix t ⟨y, hyP⟩ hy)
      · rfl
    let A : Set (Interval × S) := {z | z.2 ∈ U}
    let B : Set (Interval × S) := {z | z.2 ∉ K}
    have hAo : IsOpen A := hUopen.preimage continuous_snd
    have hBo : IsOpen B := hK.isClosed.isOpen_compl.preimage continuous_snd
    have hcover : A ∪ B = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      by_cases hz : z.2 ∈ K
      · exact Or.inl (hKP hz)
      · exact Or.inr hz
    have hcontA : ContinuousOn F A := by
      rw [continuousOn_iff_continuous_restrict]
      let k : A → Interval × ↥U := fun z => (z.val.1, ⟨z.val.2, z.property⟩)
      have hk : Continuous k :=
        (continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
      have heq : (fun z : A => F z.val) = fun z => (H.map (k z)).val := by
        funext z
        exact hFin z.val.1 ⟨z.val.2, z.property⟩
      change Continuous (fun z : A => F z.val)
      rw [heq]
      exact continuous_subtype_val.comp (H.map.continuous.comp hk)
    have hcontB : ContinuousOn F B :=
      continuous_snd.continuousOn.congr (fun z hz => hFout z.1 z.2 hz)
    have hcont : Continuous F := by
      rw [← continuousOn_univ, ← hcover]
      exact hcontA.union_of_isOpen hcontB hAo hBo
    have hhomeo (t : Interval) : ∃ e : S ≃ₜ S, ∀ y, e y = F (t, y) := by
      obtain ⟨e, he⟩ := H.homeomorphism_at t
      have hi : Function.Injective (fun y => F (t, y)) := by
        intro y z hyz
        change F (t, y) = F (t, z) at hyz
        by_cases hy : y ∈ U
        · by_cases hz : z ∈ U
          · have h := hyz
            rw [hFin t ⟨y, hy⟩, hFin t ⟨z, hz⟩] at h
            have hh : e ⟨y, hy⟩ = e ⟨z, hz⟩ :=
              (he _).trans ((Subtype.ext h).trans (he _).symm)
            exact congrArg Subtype.val (e.injective hh)
          · have h := hyz
            rw [hFin t ⟨y, hy⟩] at h
            have hzout : F (t, z) = z := by simp only [F, dif_neg hz]
            rw [hzout] at h
            exact False.elim (hz (h ▸ (H.map (t, ⟨y, hy⟩)).property))
        · by_cases hz : z ∈ U
          · have h := hyz
            rw [hFin t ⟨z, hz⟩] at h
            have hyout : F (t, y) = y := by simp only [F, dif_neg hy]
            rw [hyout] at h
            exact False.elim (hy (h.symm ▸ (H.map (t, ⟨z, hz⟩)).property))
          · simpa only [F, dif_neg hy, dif_neg hz] using hyz
      have hs : Function.Surjective (fun y => F (t, y)) := by
        intro y
        by_cases hy : y ∈ U
        · refine ⟨(e.symm ⟨y, hy⟩).val, ?_⟩
          change F (t, (e.symm ⟨y, hy⟩).val) = y
          rw [hFin, ← he, e.apply_symm_apply]
        · refine ⟨y, ?_⟩
          simp only [F, dif_neg hy]
      let eS := (hcont.comp (continuous_const.prodMk continuous_id)).homeoOfEquivCompactToT2
        (f := Equiv.ofBijective (fun y => F (t, y)) ⟨hi, hs⟩)
      exact ⟨eS, fun _ => rfl⟩
    let G : AmbientIsotopy S := {
      map := ⟨F, hcont⟩
      homeomorphism_at := hhomeo
      at_zero := by
        intro y
        change F (⟨0, by norm_num⟩, y) = y
        by_cases hy : y ∈ U
        · rw [hFin _ ⟨y, hy⟩]
          exact congrArg Subtype.val (H.at_zero ⟨y, hy⟩)
        · simp only [F, dif_neg hy] }
    refine ⟨G, hFin, ?_⟩
    intro t y hy
    have hyn : y ∉ U := hy
    change F (t, y) = y
    simp only [F, dif_neg hyn]
  have hcapSupported (H : AmbientIsotopy P) (K : Set S)
      (hK : IsCompact K) (hKP : K ⊆ Dᶜ)
      (hfix : ∀ t (y : P), y.val ∉ K → H.map (t, y) = y) :
      ∃ G : AmbientIsotopy S,
        (∀ t (y : P), G.map (t, y.val) = (H.map (t, y)).val) ∧
        (∀ t y, y ∈ D → G.map (t, y) = y) := by
    obtain ⟨G, hG, hout⟩ := hopenSupported Dᶜ hPopen H K hK hKP hfix
    exact ⟨G, hG, fun t y hy => hout t y (fun hh => hh hy)⟩
  have hslideCollar
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
      (a : Set.Ioo (-1 : ℝ) 1) (ha : |(a : ℝ)| < ρ) :
      AmbientIsotopy.Rel
        (Set.range (fun w : Circle => E (⟨0, by norm_num⟩, w)))
        (Set.range (fun w : Circle => E (a, w))) := by
    obtain ⟨H, hHcore, hHfix⟩ := hwidthSlide ρ a.val hρ hρ1 ha
    obtain ⟨K, V, cm, cp, hK, hV, hVK, hcenter, hfront, hdist, hKdef, hVdef, hmmap, hpmap⟩ :=
      hcompactCollarGeometry E hE ρ hρ hρ1
    let q := hE.isEmbedding.toHomeomorph
    let J : AmbientIsotopy ↥(Set.range E) := {
      map := ⟨fun z => q (H.map (z.1, q.symm z.2)),
        q.continuous.comp (H.map.continuous.comp
          (continuous_fst.prodMk (q.symm.continuous.comp continuous_snd)))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨h, hh⟩ := H.homeomorphism_at t
        exact ⟨(q.symm.trans h).trans q, fun y => congrArg q (hh (q.symm y))⟩
      at_zero := by
        intro y
        change q (H.map (⟨0, by norm_num⟩, q.symm y)) = y
        rw [H.at_zero, q.apply_symm_apply] }
    have hKrange : K ⊆ Set.range E := by
      rw [hKdef]
      exact Set.image_subset_range _ _
    have hJfix : ∀ t (y : ↥(Set.range E)), y.val ∉ K → J.map (t, y) = y := by
      intro t y hy
      have hn : ¬ |((q.symm y).1 : ℝ)| ≤ ρ := by
        intro hle
        apply hy
        rw [hKdef]
        refine ⟨q.symm y, hle, ?_⟩
        exact congrArg Subtype.val (q.apply_symm_apply y)
      change q (H.map (t, q.symm y)) = y
      rw [hHfix t (q.symm y) (not_le.mp hn).le, q.apply_symm_apply]
    obtain ⟨G, hG, hout⟩ := hopenSupported (Set.range E) hE.isOpen_range J K hK hKrange hJfix
    have hGcore (w : Circle) : G.finalMap (E (⟨0, by norm_num⟩, w)) = E (a, w) := by
      let z : Set.Ioo (-1 : ℝ) 1 × Circle := (⟨0, by norm_num⟩, w)
      have hh := hG ⟨1, by norm_num⟩ (q z)
      change G.finalMap (E z) = E (H.finalMap (q.symm (q z))) at hh
      rw [q.symm_apply_apply, hHcore] at hh
      exact hh
    refine ⟨G, ?_⟩
    ext y
    constructor
    · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, (hGcore w).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨E (⟨0, by norm_num⟩, w), ⟨w, rfl⟩, hGcore w⟩
  have hoffsetEssential (b : EssentialCurve S)
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (hcore : ∀ w, E (⟨0, by norm_num⟩, w) = b.val.map w)
      (t : Set.Ioo (-1 : ℝ) 1) :
      ∃ c : EssentialCurve S, c.val.map = (fun w => E (t,w)) ∧
        Quotient.mk (essentialCurveSetoid S) c = Quotient.mk (essentialCurveSetoid S) b := by
    have ht : |(t : ℝ)| < 1 := abs_lt.mpr t.property
    let ρ : ℝ := (|(t : ℝ)| + 1) / 2
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
    have htρ : |(t : ℝ)| < ρ := by dsimp [ρ]; linarith
    have hrel := hslideCollar E hE ρ hρ hρ1 t htρ
    let c : Curve S := ⟨fun w => E (t,w), hE.isEmbedding.comp (isEmbedding_prodMkRight t)⟩
    have hc : Set.range (fun w : Circle => E (⟨0, by norm_num⟩, w)) = b.val.image := by
      have he : (fun w : Circle => E (⟨0, by norm_num⟩, w)) = b.val.map := funext hcore
      rw [he]
      rfl
    rw [hc] at hrel
    have hrel' : AmbientIsotopy.Rel b.val.image c.image := hrel
    let ce : EssentialCurve S := ⟨c, (essential_isotopy_invariant hrel').mp b.property⟩
    exact ⟨ce, rfl, (Quotient.sound hrel').symm⟩
  have hfiniteEssentialCollars :
      ∃ (B V : ↥Fv → Set S) (cm cp : ↥Fv → EssentialCurve S),
        (∀ i, IsCompact (B i) ∧ IsOpen (V i) ∧ V i ⊆ B i ∧
          (source_r i.val i.property).val.image ⊆ V i ∧ B i ⊆ Dᶜ ∧
          frontier (V i) ⊆ (cm i).val.image ∪ (cp i).val.image ∧
          Disjoint (cm i).val.image (cp i).val.image ∧
          Quotient.mk (essentialCurveSetoid S) (cm i) = i.val ∧
          Quotient.mk (essentialCurveSetoid S) (cp i) = i.val) ∧
        (∀ i j, i ≠ j → geometricIntersection i.val j.val = 0 → Disjoint (B i) (B j)) ∧
        (∀ i, B i = closure (V i)) ∧
        (∀ i, frontier (B i) = (cm i).val.image ∪ (cp i).val.image) ∧
        (∀ i, B i ⊆ compatibleN i) ∧
        (∀ i, ∃ (E : C(Set.Ioo (-1 : ℝ) 1 × Circle,S)) (δ : ℝ)
          (hδ : 0 < δ) (hδ1 : δ < 1),
          Topology.IsOpenEmbedding E ∧
          B i = E '' {z | |(z.1 : ℝ)| ≤ δ} ∧
          V i = E '' {z | |(z.1 : ℝ)| < δ} ∧
          (cm i).val.map = (fun w => E (⟨-δ,by constructor <;> linarith⟩,w)) ∧
          (cp i).val.map = (fun w => E (⟨δ,by constructor <;> linarith⟩,w)) ∧
          ∀ w, E (⟨0,by norm_num⟩,w) = (source_r i.val i.property).val.map w) ∧
        ∀ i (A : Set S), B i ⊆ A → compatibleN i ∩ A ⊆ B i → ∀ z0 : S,
          ((closure (connectedComponentIn Aᶜ z0) ∩ (cm i).val.image).Nonempty →
            (cm i).val.image ⊆ closure (connectedComponentIn Aᶜ z0)) ∧
          ((closure (connectedComponentIn Aᶜ z0) ∩ (cp i).val.image).Nonempty →
            (cp i).val.image ⊆ closure (connectedComponentIn Aᶜ z0)) := by
    let N := compatibleN
    have hN := hcompatibleN
    have hdN := hcompatibleDisjoint
    choose E δ hE hcore hδ hδ1 hEN using fun i =>
      hcollarThin (source_r i.val i.property) (N i) (hN i).1 (hN i).2.1
    choose B V cm0 cp0 hB hV hVB hcenter hfront hdist hBdef hVdef hmmap hpmap using fun i =>
      hcompactCollarGeometry (E i) (hE i) (δ i) (hδ i) (hδ1 i)
    let tm (i : ↥Fv) : Set.Ioo (-1 : ℝ) 1 := ⟨-δ i, by constructor <;> linarith [hδ i,hδ1 i]⟩
    let tp (i : ↥Fv) : Set.Ioo (-1 : ℝ) 1 := ⟨δ i, by constructor <;> linarith [hδ i,hδ1 i]⟩
    choose cm hcmmap hcmclass using fun i => hoffsetEssential
      (source_r i.val i.property) (E i) (hE i) (hcore i) (tm i)
    choose cp hcpmap hcpclass using fun i => hoffsetEssential
      (source_r i.val i.property) (E i) (hE i) (hcore i) (tp i)
    have hmi (i : ↥Fv) : (cm i).val.image = (cm0 i).image := by
      change Set.range (cm i).val.map = Set.range (cm0 i).map
      rw [hcmmap i, hmmap i]
    have hpi (i : ↥Fv) : (cp i).val.image = (cp0 i).image := by
      change Set.range (cp i).val.map = Set.range (cp0 i).map
      rw [hcpmap i, hpmap i]
    have hBN (i : ↥Fv) : B i ⊆ N i := by
      rw [hBdef i]
      rintro y ⟨⟨t,w⟩, ht, rfl⟩
      exact hEN i t w ht
    refine ⟨B, V, cm, cp, ?_, ?_, ?_, ?_, hBN, ?_, ?_⟩
    · intro i
      refine ⟨hB i, hV i, hVB i, ?_, (hBN i).trans (hN i).2.2, ?_, ?_,
        (hcmclass i).trans (source_hr i.val i.property),
        (hcpclass i).trans (source_hr i.val i.property)⟩
      · intro y hy
        obtain ⟨w,rfl⟩ := hy
        exact hcenter i ⟨w,hcore i w⟩
      · rw [hmi i,hpi i]
        exact hfront i
      · rw [hmi i,hpi i]
        exact hdist i
    · intro i j hij hz
      exact (hdN i j hij hz).mono (hBN i) (hBN j)
    · intro i
      rw [hBdef i, hVdef i]
      exact (hbandClosure (E i) (hE i) (δ i) (hδ i) (hδ1 i)).symm
    · intro i
      change frontier (B i) = Set.range (cm i).val.map ∪ Set.range (cp i).val.map
      rw [hBdef i, hcmmap i, hcpmap i]
      exact hbandFrontierExact (E i) (hE i) (δ i) (hδ i) (hδ1 i)
    · intro i
      exact ⟨E i,δ i,hδ i,hδ1 i,hE i,hBdef i,hVdef i,hcmmap i,hcpmap i,hcore i⟩
    · intro i A hBA hNA z0
      have hBN' : E i '' {z | |(z.1 : ℝ)| ≤ δ i} ⊆ N i := by
        rw [← hBdef i]
        exact hBN i
      have hBA' : E i '' {z | |(z.1 : ℝ)| ≤ δ i} ⊆ A := by
        rw [← hBdef i]
        exact hBA
      have hNA' : N i ∩ A ⊆ E i '' {z | |(z.1 : ℝ)| ≤ δ i} := by
        rw [← hBdef i]
        exact hNA
      constructor
      · change (closure (connectedComponentIn Aᶜ z0) ∩ Set.range (cm i).val.map).Nonempty →
          Set.range (cm i).val.map ⊆ closure (connectedComponentIn Aᶜ z0)
        rw [hcmmap i]
        exact hlowerCircleRetention (E i) (hE i) (δ i) (hδ i) (hδ1 i)
          (N i) (hN i).1 hBN' A hBA' hNA' z0
      · change (closure (connectedComponentIn Aᶜ z0) ∩ Set.range (cp i).val.map).Nonempty →
          Set.range (cp i).val.map ⊆ closure (connectedComponentIn Aᶜ z0)
        rw [hcpmap i]
        exact hupperCircleRetention (E i) (hE i) (δ i) (hδ i) (hδ1 i)
          (N i) (hN i).1 hBN' A hBA' hNA' z0
  obtain ⟨finiteBands, finiteBandInteriors, finiteMinus, finitePlus,
    hfiniteBands, hfiniteBandsDisjoint, hfiniteBandsRegular, hfiniteBandsExactFrontier, hfiniteBandNeighborhoods,
    hfiniteCollarCoordinates, hfiniteCircleRetention⟩ := hfiniteEssentialCollars
  letI : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
  have hcomponentFrontier (A : Set S) (hA : IsClosed A) (z0 : S) :
      frontier (connectedComponentIn Aᶜ z0) ⊆ frontier A := by
    let C := connectedComponentIn Aᶜ z0
    have hCo : IsOpen C := hA.isOpen_compl.connectedComponentIn
    intro y hy
    have hyA : y ∈ A := by
      by_contra hya
      let V := connectedComponentIn Aᶜ y
      have hVo : IsOpen V := hA.isOpen_compl.connectedComponentIn
      have hyV : y ∈ V := mem_connectedComponentIn hya
      obtain ⟨w, hwV, hwC⟩ := (mem_closure_iff.mp hy.1) V hVo hyV
      have heq : C = V := (connectedComponentIn_eq hwC).trans (connectedComponentIn_eq hwV).symm
      apply hy.2
      rw [hCo.interior_eq]
      exact heq.symm ▸ hyV
    rw [frontier_eq_closure_inter_closure]
    exact ⟨hA.closure_eq.symm ▸ hyA,
      closure_mono (connectedComponentIn_subset Aᶜ z0) hy.1⟩
  let bandsInS (σ : Finset ↥Fv) : Set S := ⋃ w ∈ σ, finiteBands w
  have hbandsClosed (σ : Finset ↥Fv) : IsClosed (bandsInS σ) :=
    isClosed_biUnion_finset fun w hw => (hfiniteBands w).1.isClosed
  have hbandFrontier (w : ↥Fv) :
      frontier (finiteBands w) ⊆ (finiteMinus w).val.image ∪ (finitePlus w).val.image := by
    rw [hfiniteBandsRegular w]
    exact frontier_closure_subset.trans (hfiniteBands w).2.2.2.2.2.1
  have hbandsFrontier (σ : Finset ↥Fv) :
      frontier (bandsInS σ) ⊆
        ⋃ w ∈ σ, (finiteMinus w).val.image ∪ (finitePlus w).val.image := by
    intro y hy
    obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp (σ.frontier_biUnion_subset finiteBands hy)
    exact Set.mem_iUnion₂.mpr ⟨w, hw, hbandFrontier w hyw⟩
  have hxD : x ∈ D := by
    refine ⟨(chartAt (EuclideanSpace ℝ (Fin 2)) x) x, ?_, ?_⟩
    · exact Metric.mem_closedBall.mpr (by simpa using hR.le)
    · exact (chartAt (EuclideanSpace ℝ (Fin 2)) x).left_inv (ChartedSpace.mem_chart_source x)
  have hDconnected : IsConnected D :=
    (Metric.isConnected_closedBall hR.le).image
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.continuousOn.mono htarget)
  have hDoutside (σ : Finset ↥Fv) : D ⊆ (bandsInS σ)ᶜ := by
    intro y hy
    intro hyBAll
    obtain ⟨w, hw, hyB⟩ := Set.mem_iUnion₂.mp hyBAll
    exact ((hfiniteBands w).2.2.2.2.1 hyB) hy
  let surfaceComponent (σ : Finset ↥Fv) := connectedComponentIn (bandsInS σ)ᶜ x
  let closedSurfaceRegion (σ : Finset ↥Fv) := closure (surfaceComponent σ)
  have hDcomponent (σ : Finset ↥Fv) : D ⊆ surfaceComponent σ :=
    hDconnected.isPreconnected.subset_connectedComponentIn hxD (hDoutside σ)
  have hsurfaceComponentOpen (σ : Finset ↥Fv) : IsOpen (surfaceComponent σ) :=
    (hbandsClosed σ).isOpen_compl.connectedComponentIn
  have hclosedSurfaceRegion (σ : Finset ↥Fv) :
      IsCompact (closedSurfaceRegion σ) ∧ IsConnected (closedSurfaceRegion σ) ∧
      D ⊆ closedSurfaceRegion σ ∧
      frontier (closedSurfaceRegion σ) ⊆
        ⋃ w ∈ σ, (finiteMinus w).val.image ∪ (finitePlus w).val.image := by
    exact ⟨isClosed_closure.isCompact,
      (isConnected_connectedComponentIn_iff.mpr (hDoutside σ hxD)).closure,
      (hDcomponent σ).trans subset_closure,
      frontier_closure_subset.trans ((hcomponentFrontier _ (hbandsClosed σ) x).trans
        (hbandsFrontier σ))⟩
  -- One fixed band per original finite vertex now works for EVERY original
  -- simplex, so union of bands is monotone under inclusion of systems.
  have hfaceEssentialNeighborhoods (σ : Finset ↥Fv)
      (hz : ∀ i j : ↥σ, i ≠ j → geometricIntersection i.val.val j.val.val = 0) :
      ∃ (B V : ↥σ → Set S) (cm cp : ↥σ → EssentialCurve S),
        (∀ i, IsCompact (B i) ∧ IsOpen (V i) ∧ V i ⊆ B i ∧
          (source_r i.val.val i.val.property).val.image ⊆ V i ∧ B i ⊆ Dᶜ ∧
          frontier (V i) ⊆ (cm i).val.image ∪ (cp i).val.image ∧
          Disjoint (cm i).val.image (cp i).val.image ∧
          Quotient.mk (essentialCurveSetoid S) (cm i) = i.val.val ∧
          Quotient.mk (essentialCurveSetoid S) (cp i) = i.val.val) ∧
        ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
    refine ⟨fun i => finiteBands i.val, fun i => finiteBandInteriors i.val,
      fun i => finiteMinus i.val, fun i => finitePlus i.val,
      fun i => hfiniteBands i.val, ?_⟩
    intro i j hij
    apply hfiniteBandsDisjoint i.val j.val _ (hz i j hij)
    intro he
    exact hij (Subtype.ext he)
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let center := e x
  let O : Set S := e.symm '' Metric.ball center R
  let Q := ↥Oᶜ
  let boundaryCircle : Set S := e.symm '' Metric.sphere center R
  have hballTarget : Metric.ball center R ⊆ e.target :=
    Metric.ball_subset_closedBall.trans htarget
  have hOopen : IsOpen O :=
    e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hballTarget
  have hQcompact : IsCompact (Oᶜ : Set S) := hOopen.isClosed_compl.isCompact
  have hOD : O ⊆ D := Set.image_mono Metric.ball_subset_closedBall
  have hBoundaryInQ : boundaryCircle ⊆ Oᶜ := by
    rintro y ⟨z, hz, rfl⟩ ⟨u, hu, heq⟩
    have hzTarget : z ∈ e.target := htarget (Metric.sphere_subset_closedBall hz)
    have huTarget : u ∈ e.target := hballTarget hu
    have huz : u = z := e.symm.injOn huTarget hzTarget heq
    rw [huz] at hu
    have hdist := Metric.mem_sphere.mp hz
    exact (ne_of_lt (Metric.mem_ball.mp hu)) hdist
  have hBoundaryAvoid (w : ↥Fv) :
      Disjoint boundaryCircle (source_r w.val w.property).val.image := by
    exact (source_chosenAvoid w.val w.property).mono_left
      (Set.image_mono Metric.sphere_subset_closedBall)
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp hQcompact
  let boundaryQ : Set Q := {y | y.val ∈ boundaryCircle}
  have hSphereConnected : IsConnected (Metric.sphere center R) :=
    isConnected_sphere
      (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num) center hR.le
  have hBoundaryConnected : IsConnected boundaryCircle := by
    exact hSphereConnected.image e.symm
      (e.symm.continuousOn.mono (Metric.sphere_subset_closedBall.trans htarget))
  have hclosureO : closure O = D := by
    have hDc : IsCompact D :=
      (isCompact_closedBall center R).image_of_continuousOn (e.symm.continuousOn.mono htarget)
    have hcb : closure (Metric.ball center R) = Metric.closedBall center R :=
      closure_ball center (ne_of_gt hR)
    have hc : ContinuousOn e.symm (closure (Metric.ball center R)) := by
      rw [hcb]
      exact e.symm.continuousOn.mono htarget
    apply Set.Subset.antisymm (closure_minimal hOD hDc.isClosed)
    change e.symm '' Metric.closedBall center R ⊆ closure (e.symm '' Metric.ball center R)
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
  let borderedRegion (σ : Finset ↥Fv) : Set S := closedSurfaceRegion σ \ O
  have hborderedRegion (σ : Finset ↥Fv) :
      IsCompact (borderedRegion σ) ∧ IsConnected (borderedRegion σ) ∧
      boundaryCircle ⊆ borderedRegion σ ∧ borderedRegion σ ⊆ Oᶜ ∧
      frontier (borderedRegion σ) ⊆ boundaryCircle ∪
        ⋃ w ∈ σ, (finiteMinus w).val.image ∪ (finitePlus w).val.image := by
    have hC := hclosedSurfaceRegion σ
    refine ⟨hC.1.diff hOopen, hremoveDiskConnected _ hC.2.1 hC.2.2.1, ?_,
      fun y hy => hy.2, ?_⟩
    · intro y hy
      exact ⟨hC.2.2.1 ((Set.image_mono Metric.sphere_subset_closedBall) hy), hBoundaryInQ hy⟩
    · intro y hy
      rcases frontier_inter_subset (closedSurfaceRegion σ) Oᶜ hy with hf | ho
      · exact Or.inr (hC.2.2.2 hf.1)
      · exact Or.inl (by simpa only [frontier_compl, hfrontierO] using ho.2)
  -- The actual region is regular closed; its interior is dense even at the
  -- original coordinate boundary. This rules out a merely attached frontier.
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
    have hzCT : z ∈ closure (e.target ∩ (Metric.closedBall center R)ᶜ) :=
      e.open_target.inter_closure ⟨hzT, hzCl⟩
    apply (e.symm.continuousOn z hzT).mono Set.inter_subset_left |>.mem_closure hzCT
    intro u hu
    rintro ⟨v, hv, heq⟩
    have huv : v = u := e.symm.injOn (htarget hv) hu.1 heq
    exact hu.2 (huv ▸ hv)
  have hborderedRegular (σ : Finset ↥Fv) :
      closure (surfaceComponent σ ∩ Dᶜ) = borderedRegion σ := by
    apply Set.Subset.antisymm
    · apply closure_minimal _ (hborderedRegion σ).1.isClosed
      intro y hy
      exact ⟨subset_closure hy.1, fun ho => hy.2 (hOD ho)⟩
    · intro y hy
      by_cases hyD : y ∈ D
      · have hyB : y ∈ boundaryCircle := by
          rw [← hfrontierO, hOopen.frontier_eq, hclosureO]
          exact ⟨hyD, hy.2⟩
        exact (hsurfaceComponentOpen σ).inter_closure
          ⟨hDcomponent σ hyD, hBoundaryExterior hyB⟩
      · exact hDclosed.isOpen_compl.closure_inter ⟨hy.1, hyD⟩
  have hborderedInteriorDense (σ : Finset ↥Fv) :
      closure (interior (borderedRegion σ)) = borderedRegion σ := by
    apply Set.Subset.antisymm (hborderedRegion σ).1.isClosed.closure_interior_subset
    rw [← hborderedRegular σ]
    apply closure_mono
    apply interior_maximal subset_closure
      ((hsurfaceComponentOpen σ).inter hDclosed.isOpen_compl)
  have hborderedCoordinateBoundary (σ : Finset ↥Fv) (y : S)
      (hyC : y ∈ surfaceComponent σ) (hyE : y ∈ e.source) :
      y ∈ borderedRegion σ ↔ R ≤ dist (e y) center := by
    constructor
    · intro hy
      apply not_lt.mp
      intro hlt
      apply hy.2
      exact ⟨e y,Metric.mem_ball.mpr hlt,e.left_inv hyE⟩
    · intro hd
      refine ⟨subset_closure hyC,?_⟩
      rintro ⟨z,hz,heq⟩
      have hzT : z ∈ e.target := hballTarget hz
      have hzy : z = e y := by
        have hh := congrArg e heq
        rw [e.right_inv hzT] at hh
        exact hh
      rw [hzy] at hz
      exact (not_lt.mpr hd) (Metric.mem_ball.mp hz)
  have hborderedBoundary (σ : Finset ↥Fv) : boundaryCircle ⊆ frontier (borderedRegion σ) := by
    intro y hy
    have hyF : y ∈ borderedRegion σ := (hborderedRegion σ).2.2.1 hy
    apply (mem_frontier_iff_notMem_interior hyF).mpr
    intro hi
    have hyO : y ∈ frontier Oᶜ := by simpa only [frontier_compl, hfrontierO] using hy
    exact hyO.2 (interior_mono (hborderedRegion σ).2.2.2.1 hi)
  have hborderedRegionAntitone : Antitone borderedRegion := by
    intro σ τ hστ
    apply Set.sdiff_subset_sdiff_left
    apply closure_mono
    apply connectedComponentIn_mono
    intro y hy hyσ
    obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp hyσ
    exact hy (Set.mem_iUnion₂.mpr ⟨w,hστ hw,hyw⟩)
  have hregionAvoidsOriginal (σ : Finset ↥Fv) (w : ↥Fv) (hw : w ∈ σ) :
      Disjoint (borderedRegion σ) (source_r w.val w.property).val.image := by
    apply Set.disjoint_left.mpr
    intro y hy hycurve
    have hyV : y ∈ finiteBandInteriors w := (hfiniteBands w).2.2.2.1 hycurve
    obtain ⟨z,hzV,hzC⟩ := (mem_closure_iff.mp hy.1) (finiteBandInteriors w)
      (hfiniteBands w).2.1 hyV
    have hzB : z ∈ bandsInS σ :=
      Set.mem_iUnion₂.mpr ⟨w,hw,(hfiniteBands w).2.2.1 hzV⟩
    exact (connectedComponentIn_subset (bandsInS σ)ᶜ x hzC) hzB
  have hfaceLocalBand (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (w : ↥Fv) (hw : w ∈ σ) : compatibleN w ∩ bandsInS σ ⊆ finiteBands w := by
    intro y hy
    obtain ⟨j,hj,hyj⟩ := Set.mem_iUnion₂.mp hy.2
    by_cases hjw : j = w
    · exact hjw ▸ hyj
    · have hwj : w ≠ j := fun h => hjw h.symm
      exact False.elim (Set.disjoint_left.mp
        (hcompatibleDisjoint w j hwj (hz w hw j hj hwj)) hy.1 (hfiniteBandNeighborhoods j hyj))
  have hBandInRegionFrontier (σ : Finset ↥Fv) (w : ↥Fv) (hw : w ∈ σ) :
      closedSurfaceRegion σ ∩ finiteBands w ⊆ frontier (borderedRegion σ) := by
    have hVout : finiteBandInteriors w ⊆ (closedSurfaceRegion σ)ᶜ := by
      intro y hyV hyC
      obtain ⟨z,hzV,hzC⟩ := (mem_closure_iff.mp hyC) (finiteBandInteriors w)
        (hfiniteBands w).2.1 hyV
      exact (connectedComponentIn_subset (bandsInS σ)ᶜ x hzC)
        (Set.mem_iUnion₂.mpr ⟨w,hw,(hfiniteBands w).2.2.1 hzV⟩)
    have hBout : finiteBands w ⊆ closure (closedSurfaceRegion σ)ᶜ := by
      rw [hfiniteBandsRegular w]
      exact closure_mono hVout
    intro y hy
    have hyO : y ∉ O := fun hh => ((hfiniteBands w).2.2.2.2.1 hy.2) (hOD hh)
    have hyF : y ∈ borderedRegion σ := ⟨hy.1,hyO⟩
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hyF, closure_mono ?_ (hBout hy.2)⟩
    intro z hz hzf
    exact hz hzf.1
  have hessentialSidesInBand (w : ↥Fv) :
      (finiteMinus w).val.image ∪ (finitePlus w).val.image ⊆ finiteBands w := by
    intro y hy
    have hyf : y ∈ frontier (finiteBands w) := by rw [hfiniteBandsExactFrontier w]; exact hy
    have hyc := frontier_subset_closure hyf
    rw [(hfiniteBands w).1.isClosed.closure_eq] at hyc
    exact hyc
  have hwholeFrontierSides (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (w : ↥Fv) (hw : w ∈ σ) :
      ((frontier (borderedRegion σ) ∩ (finiteMinus w).val.image).Nonempty →
        (finiteMinus w).val.image ⊆ frontier (borderedRegion σ)) ∧
      ((frontier (borderedRegion σ) ∩ (finitePlus w).val.image).Nonempty →
        (finitePlus w).val.image ⊆ frontier (borderedRegion σ)) := by
    have hBA : finiteBands w ⊆ bandsInS σ := fun y hy => Set.mem_iUnion₂.mpr ⟨w,hw,hy⟩
    have hret := hfiniteCircleRetention w (bandsInS σ) hBA (hfaceLocalBand σ hz w hw) x
    have hFrontInF : frontier (borderedRegion σ) ⊆ borderedRegion σ := by
      intro y hy
      have hh := frontier_subset_closure hy
      rw [(hborderedRegion σ).1.isClosed.closure_eq] at hh
      exact hh
    constructor
    · intro hmeet y hy
      obtain ⟨z,hzf,hzm⟩ := hmeet
      have hwhole := hret.1 ⟨z,(hFrontInF hzf).1,hzm⟩
      exact hBandInRegionFrontier σ w hw ⟨hwhole hy,hessentialSidesInBand w (Or.inl hy)⟩
    · intro hmeet y hy
      obtain ⟨z,hzf,hzp⟩ := hmeet
      have hwhole := hret.2 ⟨z,(hFrontInF hzf).1,hzp⟩
      exact hBandInRegionFrontier σ w hw ⟨hwhole hy,hessentialSidesInBand w (Or.inr hy)⟩
  let retainedMinus (σ : Finset ↥Fv) := σ.filter fun w =>
    (frontier (borderedRegion σ) ∩ (finiteMinus w).val.image).Nonempty
  let retainedPlus (σ : Finset ↥Fv) := σ.filter fun w =>
    (frontier (borderedRegion σ) ∩ (finitePlus w).val.image).Nonempty
  have hborderedFrontierExact (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0) :
      frontier (borderedRegion σ) = boundaryCircle ∪
        (⋃ w ∈ retainedMinus σ, (finiteMinus w).val.image) ∪
        (⋃ w ∈ retainedPlus σ, (finitePlus w).val.image) := by
    ext y
    constructor
    · intro hy
      rcases (hborderedRegion σ).2.2.2.2 hy with hb | hs
      · exact Or.inl (Or.inl hb)
      · obtain ⟨w,hw,hm|hp⟩ := Set.mem_iUnion₂.mp hs
        · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr
            ⟨w,Finset.mem_filter.mpr ⟨hw,⟨y,hy,hm⟩⟩,hm⟩))
        · exact Or.inr (Set.mem_iUnion₂.mpr
            ⟨w,Finset.mem_filter.mpr ⟨hw,⟨y,hy,hp⟩⟩,hp⟩)
    · rintro ((hb|hm)|hp)
      · exact hborderedBoundary σ hb
      · obtain ⟨w,hw,hym⟩ := Set.mem_iUnion₂.mp hm
        have hh := Finset.mem_filter.mp hw
        exact (hwholeFrontierSides σ hz w hh.1).1 hh.2 hym
      · obtain ⟨w,hw,hyp⟩ := Set.mem_iUnion₂.mp hp
        have hh := Finset.mem_filter.mp hw
        exact (hwholeFrontierSides σ hz w hh.1).2 hh.2 hyp
  have hretainedNonempty (σ : Finset ↥Fv) (hne : σ.Nonempty)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0) :
      (retainedMinus σ).Nonempty ∨ (retainedPlus σ).Nonempty := by
    by_contra hn
    have hm : retainedMinus σ = ∅ := Finset.not_nonempty_iff_eq_empty.mp
      (fun hh => hn (Or.inl hh))
    have hp : retainedPlus σ = ∅ := Finset.not_nonempty_iff_eq_empty.mp
      (fun hh => hn (Or.inr hh))
    have hf : frontier (borderedRegion σ) = boundaryCircle := by
      simpa [hm,hp] using hborderedFrontierExact σ hz
    have hQc : IsConnected (Oᶜ : Set S) := by
      have heq : (Set.univ : Set S) \ O = Oᶜ := by
        ext y
        simp only [Set.mem_sdiff,Set.mem_univ,Set.mem_compl_iff,true_and]
      rw [← heq]
      exact hremoveDiskConnected Set.univ (isConnected_univ : IsConnected (Set.univ : Set S))
        (Set.subset_univ D)
    letI : ConnectedSpace Q := isConnected_iff_connectedSpace.mp hQc
    let FQ : Set Q := Subtype.val ⁻¹' borderedRegion σ
    have hFQc : IsClosed FQ := (hborderedRegion σ).1.isClosed.preimage continuous_subtype_val
    have hFQo : IsOpen FQ := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      have hyS : y.val ∈ borderedRegion σ := hy
      by_cases hyb : y.val ∈ boundaryCircle
      · have hyD : y.val ∈ D := (Set.image_mono Metric.sphere_subset_closedBall) hyb
        have hyC : y.val ∈ surfaceComponent σ := hDcomponent σ hyD
        apply Filter.mem_of_superset
          (((hsurfaceComponentOpen σ).preimage continuous_subtype_val).mem_nhds hyC)
        intro z hzC
        exact ⟨subset_closure hzC,z.property⟩
      · have hyi : y.val ∈ interior (borderedRegion σ) := by
          by_contra hyn
          exact hyb (hf ▸ (mem_frontier_iff_notMem_interior hyS).mpr hyn)
        apply Filter.mem_of_superset
          ((isOpen_interior.preimage continuous_subtype_val).mem_nhds hyi)
        intro z hz
        change z.val ∈ borderedRegion σ
        exact interior_subset hz
    have hFQN : FQ.Nonempty := by
      obtain ⟨z,hz⟩ := (hborderedRegion σ).2.1.nonempty
      exact ⟨⟨z,(hborderedRegion σ).2.2.2.1 hz⟩,hz⟩
    have hu : FQ = Set.univ := IsClopen.eq_univ ⟨hFQc,hFQo⟩ hFQN
    obtain ⟨w,hw⟩ := hne
    let z := (source_r w.val w.property).val.map (1 : Circle)
    have hzD : z ∉ D := by
      intro hh
      exact Set.disjoint_left.mp (source_chosenAvoid w.val w.property) hh (Set.mem_range_self _)
    let q : Q := ⟨z,fun ho => hzD (hOD ho)⟩
    have hq : q ∈ FQ := hu.symm ▸ Set.mem_univ q
    exact Set.disjoint_left.mp (hregionAvoidsOriginal σ w hw) hq (Set.mem_range_self _)
  let frontierIndices (σ : Finset ↥Fv) := ↥(retainedMinus σ) ⊕ ↥(retainedPlus σ)
  let frontierCurves (σ : Finset ↥Fv) : frontierIndices σ → EssentialCurve S :=
    Sum.elim (fun w => finiteMinus w.val) (fun w => finitePlus w.val)
  have hfrontierFamilyExact (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0) :
      frontier (borderedRegion σ) = boundaryCircle ∪
        ⋃ i : frontierIndices σ, (frontierCurves σ i).val.image := by
    rw [hborderedFrontierExact σ hz]
    ext y
    constructor
    · rintro ((hb|hm)|hp)
      · exact Or.inl hb
      · obtain ⟨w,hw,hy⟩ := Set.mem_iUnion₂.mp hm
        exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl ⟨w,hw⟩,hy⟩)
      · obtain ⟨w,hw,hy⟩ := Set.mem_iUnion₂.mp hp
        exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inr ⟨w,hw⟩,hy⟩)
    · rintro (hb|hi)
      · exact Or.inl (Or.inl hb)
      · obtain ⟨i,hy⟩ := Set.mem_iUnion.mp hi
        rcases i with ⟨w,hw⟩ | ⟨w,hw⟩
        · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨w,hw,hy⟩))
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨w,hw,hy⟩)
  have hfrontierFamilyNonempty (σ : Finset ↥Fv) (hne : σ.Nonempty)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0) :
      Nonempty (frontierIndices σ) := by
    rcases hretainedNonempty σ hne hz with ⟨w,hw⟩ | ⟨w,hw⟩
    · exact ⟨Sum.inl ⟨w,hw⟩⟩
    · exact ⟨Sum.inr ⟨w,hw⟩⟩
  have hfrontierFamilyClasses (σ : Finset ↥Fv) (i : frontierIndices σ) :
      ∃ w ∈ σ, Quotient.mk (essentialCurveSetoid S) (frontierCurves σ i) = w.val := by
    rcases i with w | w
    · rcases hfiniteBands w.val with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
      exact ⟨w.val,(Finset.mem_filter.mp w.property).1,h8⟩
    · rcases hfiniteBands w.val with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
      exact ⟨w.val,(Finset.mem_filter.mp w.property).1,h9⟩
  have hfrontierFamilyDisjoint (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0) :
      ∀ i j : frontierIndices σ, i ≠ j →
        Disjoint (frontierCurves σ i).val.image (frontierCurves σ j).val.image := by
    have hd (i j : ↥Fv) (hi : i ∈ σ) (hj : j ∈ σ) (hij : i ≠ j) :
        Disjoint (finiteBands i) (finiteBands j) := hfiniteBandsDisjoint i j hij (hz i hi j hj hij)
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · by_cases he : i.val = j.val
      · exact False.elim (hij (congrArg Sum.inl (Subtype.ext he)))
      · exact (hd i.val j.val (Finset.mem_filter.mp i.property).1
          (Finset.mem_filter.mp j.property).1 he).mono
          (fun y hy => hessentialSidesInBand i.val (Or.inl hy))
          (fun y hy => hessentialSidesInBand j.val (Or.inl hy))
    · by_cases he : i.val = j.val
      · change Disjoint (finiteMinus i.val).val.image (finitePlus j.val).val.image
        rw [← he]
        exact (hfiniteBands i.val).2.2.2.2.2.2.1
      · exact (hd i.val j.val (Finset.mem_filter.mp i.property).1
          (Finset.mem_filter.mp j.property).1 he).mono
          (fun y hy => hessentialSidesInBand i.val (Or.inl hy))
          (fun y hy => hessentialSidesInBand j.val (Or.inr hy))
    · by_cases he : i.val = j.val
      · change Disjoint (finitePlus i.val).val.image (finiteMinus j.val).val.image
        rw [← he]
        exact (hfiniteBands i.val).2.2.2.2.2.2.1.symm
      · exact (hd i.val j.val (Finset.mem_filter.mp i.property).1
          (Finset.mem_filter.mp j.property).1 he).mono
          (fun y hy => hessentialSidesInBand i.val (Or.inr hy))
          (fun y hy => hessentialSidesInBand j.val (Or.inl hy))
    · by_cases he : i.val = j.val
      · exact False.elim (hij (congrArg Sum.inr (Subtype.ext he)))
      · exact (hd i.val j.val (Finset.mem_filter.mp i.property).1
          (Finset.mem_filter.mp j.property).1 he).mono
          (fun y hy => hessentialSidesInBand i.val (Or.inr hy))
          (fun y hy => hessentialSidesInBand j.val (Or.inr hy))
  -- Actual coordinate charts are retained from the SAME chosen global bands.
  -- On the open exterior of the coordinate disk they are literal half-space
  -- charts for the actual bordered region, not merely abstract side circles.
  have hretainedCoordinateCharts (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (w : ↥Fv) (hw : w ∈ σ) :
      ∃ (E : C(Set.Ioo (-1 : ℝ) 1 × Circle,S)) (δ : ℝ)
        (hδ : 0 < δ) (hδ1 : δ < 1), Topology.IsOpenEmbedding E ∧
        finiteBands w = E '' {z | |(z.1 : ℝ)| ≤ δ} ∧
        (finiteMinus w).val.map = (fun u => E (⟨-δ,by constructor <;> linarith⟩,u)) ∧
        (finitePlus w).val.map = (fun u => E (⟨δ,by constructor <;> linarith⟩,u)) ∧
        (∀ u, E (⟨0,by norm_num⟩,u) = (source_r w.val w.property).val.map u) ∧
        ((frontier (borderedRegion σ) ∩ (finiteMinus w).val.image).Nonempty →
          ∃ ε : ℝ, 0 < ε ∧ δ+ε < 1 ∧
            ∀ z, |(z.1 : ℝ)+δ| < ε → E z ∈ Dᶜ →
              (E z ∈ borderedRegion σ ↔ (z.1 : ℝ) ≤ -δ)) ∧
        ((frontier (borderedRegion σ) ∩ (finitePlus w).val.image).Nonempty →
          ∃ ε : ℝ, 0 < ε ∧ δ+ε < 1 ∧
            ∀ z, |(z.1 : ℝ)-δ| < ε → E z ∈ Dᶜ →
              (E z ∈ borderedRegion σ ↔ δ ≤ (z.1 : ℝ))) := by
    obtain ⟨E,δ,hδ,hδ1,hE,hB,hV,hm,hp,hcore⟩ := hfiniteCollarCoordinates w
    have hBN : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ compatibleN w := by
      rw [← hB]
      exact hfiniteBandNeighborhoods w
    have hBA : E '' {z | |(z.1 : ℝ)| ≤ δ} ⊆ bandsInS σ := by
      rw [← hB]
      intro y hy
      exact Set.mem_iUnion₂.mpr ⟨w,hw,hy⟩
    have hNA : compatibleN w ∩ bandsInS σ ⊆ E '' {z | |(z.1 : ℝ)| ≤ δ} := by
      rw [← hB]
      exact hfaceLocalBand σ hz w hw
    have hfrontC : frontier (borderedRegion σ) ⊆ closedSurfaceRegion σ := by
      intro y hy
      have hyF : y ∈ borderedRegion σ := by
        have hh := frontier_subset_closure hy
        rw [(hborderedRegion σ).1.isClosed.closure_eq] at hh
        exact hh
      exact hyF.1
    refine ⟨E,δ,hδ,hδ1,hE,hB,hm,hp,hcore,?_,?_⟩
    · intro hmeet
      have hmC : (closure (connectedComponentIn (bandsInS σ)ᶜ x) ∩
          Set.range (fun u : Circle => E (⟨-δ,by constructor <;> linarith⟩,u))).Nonempty := by
        obtain ⟨y,hyF,hyc⟩ := hmeet
        refine ⟨y,hfrontC hyF,?_⟩
        change y ∈ Set.range (fun u => E (⟨-δ,by constructor <;> linarith⟩,u))
        rw [← hm]
        exact hyc
      obtain ⟨ε,hε,hε1,hchart⟩ := hlowerHalfspaceChart E hE δ hδ hδ1
        (compatibleN w) (hcompatibleN w).1 hBN (bandsInS σ) hBA hNA x hmC
      refine ⟨ε,hε,hε1,?_⟩
      intro z hz hzD
      have hzO : E z ∉ O := fun ho => hzD (hOD ho)
      simpa only [borderedRegion,Set.mem_diff,hzO,not_false_eq_true,and_true,closedSurfaceRegion,
        surfaceComponent] using hchart z hz
    · intro hmeet
      have hpC : (closure (connectedComponentIn (bandsInS σ)ᶜ x) ∩
          Set.range (fun u : Circle => E (⟨δ,by constructor <;> linarith⟩,u))).Nonempty := by
        obtain ⟨y,hyF,hyc⟩ := hmeet
        refine ⟨y,hfrontC hyF,?_⟩
        change y ∈ Set.range (fun u => E (⟨δ,by constructor <;> linarith⟩,u))
        rw [← hp]
        exact hyc
      obtain ⟨ε,hε,hε1,hchart⟩ := hupperHalfspaceChart E hE δ hδ hδ1
        (compatibleN w) (hcompatibleN w).1 hBN (bandsInS σ) hBA hNA x hpC
      refine ⟨ε,hε,hε1,?_⟩
      intro z hz hzD
      have hzO : E z ∉ O := fun ho => hzD (hOD ho)
      simpa only [borderedRegion,Set.mem_diff,hzO,not_false_eq_true,and_true,closedSurfaceRegion,
        surfaceComponent] using hchart z hz
  -- Curve-side fibers of the actual subsurface comparison. Their cone point
  -- comes from a retained frontier circle, and has the original core curve as
  -- an actual representative outside the region.
  have hfrontierBandWitness (β : Finset ↥Fv) (i : frontierIndices β) :
      ∃ w ∈ β, Quotient.mk (essentialCurveSetoid S) (frontierCurves β i) = w.val ∧
        (frontierCurves β i).val.image ⊆ finiteBands w := by
    rcases i with i | i
    · exact ⟨i.val,(Finset.mem_filter.mp i.property).1,
        (hfiniteBands i.val).2.2.2.2.2.2.2.1,
        fun y hy => hessentialSidesInBand i.val (Or.inl hy)⟩
    · exact ⟨i.val,(Finset.mem_filter.mp i.property).1,
        (hfiniteBands i.val).2.2.2.2.2.2.2.2,
        fun y hy => hessentialSidesInBand i.val (Or.inr hy)⟩
  have hBoundaryQConnected : IsConnected boundaryQ := by
    have heq : Subtype.val '' boundaryQ = boundaryCircle := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, hBoundaryInQ hy⟩, hy, rfl⟩
    refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    · obtain ⟨y, hy⟩ := hBoundaryConnected.nonempty
      exact ⟨⟨y, hBoundaryInQ hy⟩, hy⟩
    · rw [heq]
      exact hBoundaryConnected.isPreconnected
  obtain ⟨qBoundary, hqBoundary⟩ := hBoundaryQConnected.nonempty
  let ProperArc := {a : C(Interval, Q) //
    Topology.IsEmbedding a ∧
      a ⟨0, by norm_num⟩ ∈ boundaryQ ∧
      a ⟨1, by norm_num⟩ ∈ boundaryQ ∧
      ∀ t ∈ Set.Ioo (0 : Interval) 1, a t ∉ boundaryQ}
  -- Boundary parallelism is witnessed by an ACTUAL embedded disk, not a
  -- desired nullhomotopy in the arc or curve complex.
  let boundaryParallel (a : ProperArc) : Prop :=
    ∃ b : C(Interval, Q), Topology.IsEmbedding b ∧
      (∀ t, b t ∈ boundaryQ) ∧
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, Q),
        Topology.IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range a.val ∪ Set.range b
  let EssentialProperArc := {a : ProperArc // ¬ boundaryParallel a}
  let arcRel (a b : EssentialProperArc) : Prop :=
    ∃ H : AmbientIsotopy Q,
      (∀ t, (fun y => H.map (t, y)) '' boundaryQ = boundaryQ) ∧
      H.finalMap '' Set.range a.val.val = Set.range b.val.val
  let ArcVertex := Quot arcRel
  -- The source arc complex uses actual simultaneous disjoint representatives.
  let arcFaces : Set (Finset ArcVertex) := {σ | σ.Nonempty ∧
    ∃ rep : ↥σ → EssentialProperArc,
      (∀ w, Quot.mk arcRel (rep w) = w.val) ∧
      ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
  let A : AbstractSimplicialComplex ArcVertex := {
    faces := arcFaces
    isRelLowerSet_faces := by
      intro σ hσ
      refine ⟨hσ.1, ?_⟩
      intro τ hτσ hne
      obtain ⟨rep, hr, hd⟩ := hσ.2
      refine ⟨hne, (fun w => rep ⟨w.val, hτσ w.property⟩), ?_, ?_⟩
      · intro w
        exact hr ⟨w.val, hτσ w.property⟩
      · intro u w huw
        apply hd
        intro he
        exact huw (Subtype.ext (congrArg (fun z : ↥σ => z.val) he))
    singleton_mem := by
      intro w
      obtain ⟨a, ha⟩ := Quot.exists_rep w
      refine ⟨Finset.singleton_nonempty w, (fun _ => a), ?_, ?_⟩
      · intro z
        exact ha.trans (Finset.mem_singleton.mp z.property).symm
      · intro u z huz
        exact False.elim (huz (Subtype.ext
          ((Finset.mem_singleton.mp u.property).trans
            (Finset.mem_singleton.mp z.property).symm))) }
  let regionInQ (σ : Finset ↥Fv) : C(↥(borderedRegion σ),Q) := {
    toFun := fun y => ⟨y.val,(hborderedRegion σ).2.2.2.1 y.property⟩
    continuous_toFun := continuous_subtype_val.subtype_mk _ }
  have hregionInQEmbedding (σ : Finset ↥Fv) : Topology.IsEmbedding (regionInQ σ) := by
    apply Topology.IsEmbedding.of_comp (regionInQ σ).continuous continuous_subtype_val
    exact Topology.IsEmbedding.subtypeVal
  let RegionProperArc (σ : Finset ↥Fv) :=
    {a : C(Interval,↥(borderedRegion σ)) // Topology.IsEmbedding a ∧
      (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
      (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
      ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier (borderedRegion σ)}
  let regionBoundaryParallel (σ : Finset ↥Fv) (a : RegionProperArc σ) : Prop :=
    ∃ b : C(Interval,↥(borderedRegion σ)), Topology.IsEmbedding b ∧
      (∀ t, (b t).val ∈ boundaryCircle) ∧
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥(borderedRegion σ)),
        Topology.IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range a.val ∪ Set.range b
  let IntrinsicEssentialArc (σ : Finset ↥Fv) :=
    {a : RegionProperArc σ // ¬ regionBoundaryParallel σ a}
  let intrinsicArcRel (σ : Finset ↥Fv) (a b : IntrinsicEssentialArc σ) : Prop :=
    ∃ H : AmbientIsotopy ↥(borderedRegion σ),
      (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
        {y | y.val ∈ boundaryCircle}) ∧
      (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier (borderedRegion σ)} =
        {y | y.val ∈ frontier (borderedRegion σ)}) ∧
      H.finalMap '' Set.range a.val.val = Set.range b.val.val
  let IntrinsicArcVertex (σ : Finset ↥Fv) := Quot (intrinsicArcRel σ)
  let intrinsicArcFaces (σ : Finset ↥Fv) : Set (Finset (IntrinsicArcVertex σ)) :=
    {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc σ,
      (∀ u, Quot.mk (intrinsicArcRel σ) (rep u) = u.val) ∧
      ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
  let intrinsicArcComplex (σ : Finset ↥Fv) : AbstractSimplicialComplex (IntrinsicArcVertex σ) := {
    faces := intrinsicArcFaces σ
    isRelLowerSet_faces := by
      intro τ hτ
      refine ⟨hτ.1,?_⟩
      intro μ hμτ hne
      obtain ⟨rep,hclass,hd⟩ := hτ.2
      refine ⟨hne,(fun u => rep ⟨u.val,hμτ u.property⟩),?_,?_⟩
      · intro u
        exact hclass ⟨u.val,hμτ u.property⟩
      · intro u w huw
        apply hd
        intro he
        exact huw (Subtype.ext (congrArg (fun z : ↥τ => z.val) he))
    singleton_mem := by
      intro u
      obtain ⟨a,ha⟩ := Quot.exists_rep u
      refine ⟨Finset.singleton_nonempty u,(fun _ => a),?_,?_⟩
      · intro z
        exact ha.trans (Finset.mem_singleton.mp z.property).symm
      · intro z w hzw
        exact False.elim (hzw (Subtype.ext
          ((Finset.mem_singleton.mp z.property).trans (Finset.mem_singleton.mp w.property).symm))) }
  have hessentialArcRestricts (σ : Finset ↥Fv) (a : EssentialProperArc)
      (hcontained : ∀ t, (a.val.val t).val ∈ borderedRegion σ)
      (hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
        (a.val.val t).val ∉ frontier (borderedRegion σ)) :
      ∃ b : RegionProperArc σ,
        (regionInQ σ).comp b.val = a.val.val ∧ ¬ regionBoundaryParallel σ b := by
    let bmap : C(Interval,↥(borderedRegion σ)) := {
      toFun := fun t => ⟨(a.val.val t).val,hcontained t⟩
      continuous_toFun :=
        (continuous_subtype_val.comp a.val.val.continuous).subtype_mk _ }
    have hbembed : Topology.IsEmbedding bmap := by
      apply Topology.IsEmbedding.of_comp bmap.continuous continuous_subtype_val
      have hemb : Topology.IsEmbedding (fun t : Interval => (a.val.val t).val) :=
        Topology.IsEmbedding.subtypeVal.comp a.val.property.1
      exact hemb
    let b : RegionProperArc σ := ⟨bmap,hbembed,a.val.property.2.1,
      a.val.property.2.2.1,hproper⟩
    have heq : (regionInQ σ).comp b.val = a.val.val := by
      ext t
      rfl
    refine ⟨b,heq,?_⟩
    rintro ⟨c,hc,hcb,d,hd,hboundary⟩
    apply a.property
    refine ⟨(regionInQ σ).comp c,(hregionInQEmbedding σ).comp hc,?_,
      (regionInQ σ).comp d,(hregionInQEmbedding σ).comp hd,?_⟩
    · exact hcb
    · rw [ContinuousMap.coe_comp,Set.image_comp,hboundary,Set.image_union,
        ← Set.range_comp,← Set.range_comp]
      rw [← heq]
      rfl
  have hregionArcAvoidsCurves (σ : Finset ↥Fv) (a : EssentialProperArc)
      (hcontained : ∀ t, (a.val.val t).val ∈ borderedRegion σ)
      (w : ↥Fv) (hw : w ∈ σ) :
      Disjoint (Set.range (fun t => (a.val.val t).val))
        (source_r w.val w.property).val.image := by
    apply (hregionAvoidsOriginal σ w hw).mono_left
    rintro y ⟨t,rfl⟩
    exact hcontained t
  have hproperArcRegionMonotone {σ τ : Finset ↥Fv} (hστ : σ ⊆ τ)
      (a : EssentialProperArc)
      (hc : ∀ t, (a.val.val t).val ∈ borderedRegion τ)
      (hp : ∀ t ∈ Set.Ioo (0 : Interval) 1,
        (a.val.val t).val ∉ frontier (borderedRegion τ)) :
      (∀ t, (a.val.val t).val ∈ borderedRegion σ) ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1,
        (a.val.val t).val ∉ frontier (borderedRegion σ)) := by
    refine ⟨fun t => hborderedRegionAntitone hστ (hc t),?_⟩
    intro t ht hf
    have hi : (a.val.val t).val ∈ interior (borderedRegion τ) := by
      by_contra hn
      exact hp t ht ((mem_frontier_iff_notMem_interior (hc t)).mpr hn)
    exact hf.2 (interior_mono (hborderedRegionAntitone hστ) hi)
  -- A fiber system retains simultaneous actual representatives. A full
  -- subcomplex on individually realizable classes would not give this data.
  let regionArcSystem (σ : Finset ↥Fv) (τ : Finset ArcVertex) : Prop :=
    τ.Nonempty ∧ ∃ rep : ↥τ → EssentialProperArc,
      (∀ u, Quot.mk arcRel (rep u) = u.val) ∧
      (∀ u, (∀ t, ((rep u).val.val t).val ∈ borderedRegion σ) ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1,
          ((rep u).val.val t).val ∉ frontier (borderedRegion σ)) ∧
      ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)
  have hregionArcSystemFace (σ : Finset ↥Fv) (τ : Finset ArcVertex)
      (h : regionArcSystem σ τ) : τ ∈ A.faces := by
    obtain ⟨hne,rep,hclass,hproper,hd⟩ := h
    exact ⟨hne,rep,hclass,hd⟩
  have hregionArcSystemMonotone {σ σ' : Finset ↥Fv} (hσσ' : σ ⊆ σ')
      (τ : Finset ArcVertex) : regionArcSystem σ' τ → regionArcSystem σ τ := by
    rintro ⟨hne,rep,hclass,hproper,hd⟩
    refine ⟨hne,rep,hclass,?_,hd⟩
    intro u
    exact hproperArcRegionMonotone hσσ' (rep u) (hproper u).1 (hproper u).2
  have hregionArcSystemRestricts (σ : Finset ↥Fv) (τ : Finset ArcVertex)
      (h : regionArcSystem σ τ) :
      ∃ (rep : ↥τ → EssentialProperArc) (brep : ↥τ → RegionProperArc σ),
        (∀ u, Quot.mk arcRel (rep u) = u.val) ∧
        (∀ u, (regionInQ σ).comp (brep u).val = (rep u).val.val ∧
          ¬ regionBoundaryParallel σ (brep u)) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (brep u).val) (Set.range (brep w).val) := by
    obtain ⟨hne,rep,hclass,hproper,hd⟩ := h
    choose brep hbrep using fun u =>
      hessentialArcRestricts σ (rep u) (hproper u).1 (hproper u).2
    refine ⟨rep,brep,hclass,hbrep,?_⟩
    intro u w huw
    apply Set.disjoint_left.mpr
    rintro y ⟨t,rfl⟩ ⟨s,hs⟩
    have htQ := ContinuousMap.congr_fun (hbrep u).1 t
    have hsQ := ContinuousMap.congr_fun (hbrep w).1 s
    have he : (rep w).val.val s = (rep u).val.val t :=
      hsQ.symm.trans ((congrArg (regionInQ σ) hs).trans htQ)
    exact Set.disjoint_left.mp (hd u w huw) (Set.mem_range_self t) ⟨s,he⟩
  have hregionArcSystemIntrinsicFace (σ : Finset ↥Fv) (τ : Finset ArcVertex)
      (h : regionArcSystem σ τ) :
      ∃ μ : Finset (IntrinsicArcVertex σ), μ ∈ (intrinsicArcComplex σ).faces ∧
        ∃ (rep : ↥τ → EssentialProperArc) (brep : ↥τ → IntrinsicEssentialArc σ),
          (∀ u, Quot.mk arcRel (rep u) = u.val) ∧
          (∀ u, (regionInQ σ).comp (brep u).val.val = (rep u).val.val) ∧
          μ = Finset.univ.image (fun u => Quot.mk (intrinsicArcRel σ) (brep u)) := by
    obtain ⟨rep,b,hclass,hb,hd⟩ := hregionArcSystemRestricts σ τ h
    let brep : ↥τ → IntrinsicEssentialArc σ := fun u => ⟨b u,(hb u).2⟩
    let vertex : ↥τ → IntrinsicArcVertex σ := fun u => Quot.mk (intrinsicArcRel σ) (brep u)
    let μ := Finset.univ.image vertex
    have hne : μ.Nonempty := Finset.image_nonempty.mpr
      (by obtain ⟨u,hu⟩ := h.1; exact ⟨⟨u,hu⟩,Finset.mem_univ _⟩)
    have hchoice (w : ↥μ) : ∃ u : ↥τ, vertex u = w.val := by
      obtain ⟨u,hu,he⟩ := Finset.mem_image.mp w.property
      exact ⟨u,he⟩
    choose idx hidx using hchoice
    have hface : μ ∈ (intrinsicArcComplex σ).faces := by
      refine ⟨hne,(fun w => brep (idx w)),hidx,?_⟩
      intro u w huw
      apply hd (idx u) (idx w)
      intro he
      apply huw
      apply Subtype.ext
      exact (hidx u).symm.trans ((congrArg vertex he).trans (hidx w))
    exact ⟨μ,hface,rep,brep,hclass,(fun u => (hb u).1),rfl⟩
  have hregionBoundaryRelativeInterior (σ : Finset ↥Fv) :
      boundaryQ ⊆ interior (Subtype.val ⁻¹' borderedRegion σ : Set Q) := by
    intro y hy
    have hU : IsOpen (Subtype.val ⁻¹' surfaceComponent σ : Set Q) :=
      (hsurfaceComponentOpen σ).preimage continuous_subtype_val
    have hUF : (Subtype.val ⁻¹' surfaceComponent σ : Set Q) ⊆
        Subtype.val ⁻¹' borderedRegion σ := by
      intro z hz
      exact ⟨subset_closure hz,z.property⟩
    apply interior_maximal hUF hU
    exact hDcomponent σ ((Set.image_mono Metric.sphere_subset_closedBall) hy)
  have hregionArcRelativeInterior (σ : Finset ↥Fv) (a : EssentialProperArc)
      (hc : ∀ t, (a.val.val t).val ∈ borderedRegion σ)
      (hp : ∀ t ∈ Set.Ioo (0 : Interval) 1,
        (a.val.val t).val ∉ frontier (borderedRegion σ)) :
      ∀ t, a.val.val t ∈ interior (Subtype.val ⁻¹' borderedRegion σ : Set Q) := by
    intro t
    have hpoint : (a.val.val t).val ∈ boundaryCircle ∨
        (a.val.val t).val ∉ frontier (borderedRegion σ) := by
      by_cases ht0 : (t : ℝ) = 0
      · have ht : t = (0 : Interval) := Subtype.ext ht0
        subst t
        exact Or.inl a.val.property.2.1
      · by_cases ht1 : (t : ℝ) = 1
        · have ht : t = (1 : Interval) := Subtype.ext ht1
          subst t
          exact Or.inl a.val.property.2.2.1
        · right
          apply hp t
          constructor
          · change (0 : ℝ) < (t : ℝ)
            exact lt_of_le_of_ne t.property.1 (fun he => ht0 he.symm)
          · change (t : ℝ) < (1 : ℝ)
            exact lt_of_le_of_ne t.property.2 ht1
    rcases hpoint with hb | hn
    · exact hregionBoundaryRelativeInterior σ hb
    · have hi : (a.val.val t).val ∈ interior (borderedRegion σ) := by
        by_contra hni
        exact hn ((mem_frontier_iff_notMem_interior (hc t)).mpr hni)
      apply interior_maximal (Set.preimage_mono interior_subset)
        (isOpen_interior.preimage continuous_subtype_val)
      exact hi
  have hregionArcSystemNeighborhood (σ : Finset ↥Fv) (τ : Finset ArcVertex)
      (h : regionArcSystem σ τ) :
      ∃ (rep : ↥τ → EssentialProperArc) (U : Set Q),
        (∀ u, Quot.mk arcRel (rep u) = u.val) ∧
        (∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)) ∧
        IsOpen U ∧ IsCompact (closure U) ∧ boundaryQ ⊆ U ∧
        IsConnected (boundaryQ ∪ ⋃ u, Set.range (rep u).val.val) ∧
        (∀ u, Set.range (rep u).val.val ⊆ U) ∧
        closure U ⊆ interior (Subtype.val ⁻¹' borderedRegion σ : Set Q) ∧
        ∀ w ∈ σ, Disjoint (Subtype.val '' closure U) (source_r w.val w.property).val.image := by
    obtain ⟨hne,rep,hclass,hproper,hd⟩ := h
    letI : Nonempty ↥τ := hne.to_subtype
    let K : Set Q := boundaryQ ∪ ⋃ u : ↥τ, Set.range (rep u).val.val
    have hbClosed : IsClosed boundaryQ := by
      change IsClosed (Subtype.val ⁻¹' boundaryCircle : Set Q)
      rw [← hfrontierO]
      exact isClosed_frontier.preimage continuous_subtype_val
    have hK : IsCompact K := hbClosed.isCompact.union
      (isCompact_iUnion fun u => isCompact_range (rep u).val.val.continuous)
    have hKconnected : IsConnected K := by
      have hcommon : (⋂ u : ↥τ, boundaryQ ∪ Set.range (rep u).val.val).Nonempty :=
        ⟨qBoundary,Set.mem_iInter.mpr fun u => Or.inl hqBoundary⟩
      have hpieces (u : ↥τ) : IsPreconnected (boundaryQ ∪ Set.range (rep u).val.val) :=
        hBoundaryQConnected.isPreconnected.union'
          ⟨(rep u).val.val 0,(rep u).val.property.2.1,Set.mem_range_self _⟩
          (isConnected_range (rep u).val.val.continuous).isPreconnected
      refine ⟨⟨qBoundary,Or.inl hqBoundary⟩,?_⟩
      have hh := isPreconnected_iUnion hcommon hpieces
      have heq : (⋃ u : ↥τ, boundaryQ ∪ Set.range (rep u).val.val) = K := by
        ext y
        simp only [K,Set.mem_iUnion,Set.mem_union,exists_or]
        simp
      rw [heq] at hh
      exact hh
    have hKI : K ⊆ interior (Subtype.val ⁻¹' borderedRegion σ : Set Q) := by
      rintro y (hy | hy)
      · exact hregionBoundaryRelativeInterior σ hy
      · obtain ⟨u,t,rfl⟩ := Set.mem_iUnion.mp hy
        exact hregionArcRelativeInterior σ (rep u) (hproper u).1 (hproper u).2 t
    obtain ⟨U,hU,hKU,hUI⟩ := hK.exists_isOpen_closure_subset
      (isOpen_interior.mem_nhdsSet.mpr hKI)
    refine ⟨rep,U,hclass,hd,hU,isClosed_closure.isCompact,
      fun y hy => hKU (Or.inl hy),hKconnected,?_,hUI,?_⟩
    · intro u y hy
      exact hKU (Or.inr (Set.mem_iUnion.mpr ⟨u,hy⟩))
    · intro w hw
      apply (hregionAvoidsOriginal σ w hw).mono_left
      rintro y ⟨z,hz,rfl⟩
      have hzF : z ∈ (Subtype.val ⁻¹' borderedRegion σ : Set Q) := interior_subset (hUI hz)
      exact hzF
  have hfrontierIsotopyComponent (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (H : AmbientIsotopy ↥(borderedRegion σ))
      (hbase : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
        {y | y.val ∈ boundaryCircle})
      (hfull : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier (borderedRegion σ)} =
        {y | y.val ∈ frontier (borderedRegion σ)})
      (i : frontierIndices σ) (y : ↥(borderedRegion σ))
      (hy : y.val ∈ (frontierCurves σ i).val.image) :
      ∀ t, (H.map (t,y)).val ∈ (frontierCurves σ i).val.image := by
    let f : C(Interval,S) := ⟨fun t => (H.map (t,y)).val,
      continuous_subtype_val.comp (H.map.continuous.comp (continuous_id.prodMk continuous_const))⟩
    have hKi (j : frontierIndices σ) : IsClosed ((frontierCurves σ j).val.image) :=
      (isCompact_range (frontierCurves σ j).val.embedded.continuous).isClosed
    have hyNotBase : y.val ∉ boundaryCircle := by
      obtain ⟨w,hw,hclass,hcb⟩ := hfrontierBandWitness σ i
      intro hb
      exact ((hfiniteBands w).2.2.2.2.1 (hcb hy))
        ((Set.image_mono Metric.sphere_subset_closedBall) hb)
    have hf (t : Interval) : f t ∈ ⋃ j : frontierIndices σ, (frontierCurves σ j).val.image := by
      have hyF : y.val ∈ frontier (borderedRegion σ) := by
        rw [hfrontierFamilyExact σ hz]
        exact Or.inr (Set.mem_iUnion.mpr ⟨i,hy⟩)
      have htF : (H.map (t,y)).val ∈ frontier (borderedRegion σ) := by
        have hh : H.map (t,y) ∈
            (fun z => H.map (t,z)) '' {z | z.val ∈ frontier (borderedRegion σ)} :=
          ⟨y,hyF,rfl⟩
        rw [hfull t] at hh
        exact hh
      have htNotBase : (H.map (t,y)).val ∉ boundaryCircle := by
        intro hb
        have hh : H.map (t,y) ∈
            (fun z => H.map (t,z)) '' {z | z.val ∈ boundaryCircle} := by
          rw [hbase t]
          exact hb
        obtain ⟨z,hzB,hzy⟩ := hh
        obtain ⟨e,he⟩ := H.homeomorphism_at t
        have hze : z = y := e.injective ((he z).trans (hzy.trans (he y).symm))
        exact hyNotBase (hze ▸ hzB)
      rw [hfrontierFamilyExact σ hz] at htF
      exact htF.resolve_left htNotBase
    let V : Set S := ⋃ j : {j : frontierIndices σ // j ≠ i}, (frontierCurves σ j.val).val.image
    have hV : IsClosed V := isClosed_iUnion_of_finite fun j => hKi j.val
    let A : Set Interval := f ⁻¹' (frontierCurves σ i).val.image
    have hAc : IsClosed A := (hKi i).preimage f.continuous
    have hcompl : Aᶜ = f ⁻¹' V := by
      ext t
      constructor
      · intro ht
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hf t)
        have hji : j ≠ i := by
          intro he
          have hi : f t ∈ (frontierCurves σ i).val.image := by simpa only [he] using hj
          exact ht hi
        exact Set.mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩
      · intro ht
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ht
        intro hi
        exact Set.disjoint_left.mp (hfrontierFamilyDisjoint σ hz j.val i j.property) hj hi
    have hAo : IsOpen A := by
      rw [← compl_compl A,hcompl]
      exact (hV.preimage f.continuous).isOpen_compl
    have hAne : A.Nonempty := by
      refine ⟨0,?_⟩
      change (H.map (⟨0,by norm_num⟩,y)).val ∈ (frontierCurves σ i).val.image
      rw [H.at_zero]
      exact hy
    have hAu : A = Set.univ := IsClopen.eq_univ ⟨hAc,hAo⟩ hAne
    intro t
    have htA : t ∈ A := hAu.symm ▸ Set.mem_univ t
    exact htA
  have hfrontierIsotopyCircleImage (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (H : AmbientIsotopy ↥(borderedRegion σ))
      (hbase : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
        {y | y.val ∈ boundaryCircle})
      (hfull : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier (borderedRegion σ)} =
        {y | y.val ∈ frontier (borderedRegion σ)})
      (i : frontierIndices σ) (t : Interval) :
      (fun y => H.map (t,y)) '' {y | y.val ∈ (frontierCurves σ i).val.image} =
        {y | y.val ∈ (frontierCurves σ i).val.image} := by
    ext y
    constructor
    · rintro ⟨z,hzC,rfl⟩
      exact hfrontierIsotopyComponent σ hz H hbase hfull i z hzC t
    · intro hy
      have hyF : y.val ∈ frontier (borderedRegion σ) := by
        rw [hfrontierFamilyExact σ hz]
        exact Or.inr (Set.mem_iUnion.mpr ⟨i,hy⟩)
      have hpre : y ∈ (fun z => H.map (t,z)) '' {z | z.val ∈ frontier (borderedRegion σ)} := by
        rw [hfull t]
        exact hyF
      obtain ⟨z,hzF,hzy⟩ := hpre
      change H.map (t,z) = y at hzy
      rw [hfrontierFamilyExact σ hz] at hzF
      rcases hzF with hzB | hzC
      · have hyB : y.val ∈ boundaryCircle := by
          have hh : H.map (t,z) ∈ (fun u => H.map (t,u)) '' {u | u.val ∈ boundaryCircle} :=
            ⟨z,hzB,rfl⟩
          rw [hbase t,hzy] at hh
          exact hh
        obtain ⟨w,hw,hclass,hcB⟩ := hfrontierBandWitness σ i
        exact False.elim (((hfiniteBands w).2.2.2.2.1 (hcB hy))
          ((Set.image_mono Metric.sphere_subset_closedBall) hyB))
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hzC
        by_cases hji : j = i
        · exact ⟨z,hji ▸ hj,hzy⟩
        · have hyj := hfrontierIsotopyComponent σ hz H hbase hfull j z hj t
          rw [hzy] at hyj
          exact False.elim (Set.disjoint_left.mp (hfrontierFamilyDisjoint σ hz j i hji) hyj hy)
  have hfrontierCircleParam (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (i : frontierIndices σ) :
      ∃ c : C(Circle,↥(borderedRegion σ)),
        ∀ w, (c w).val = (frontierCurves σ i).val.map w := by
    have hcF (w : Circle) : (frontierCurves σ i).val.map w ∈ borderedRegion σ := by
      have hf : (frontierCurves σ i).val.map w ∈ frontier (borderedRegion σ) := by
        rw [hfrontierFamilyExact σ hz]
        exact Or.inr (Set.mem_iUnion.mpr ⟨i,Set.mem_range_self _⟩)
      have hh := frontier_subset_closure hf
      rw [(hborderedRegion σ).1.isClosed.closure_eq] at hh
      exact hh
    exact ⟨⟨fun w => ⟨(frontierCurves σ i).val.map w,hcF w⟩,
      (frontierCurves σ i).val.embedded.continuous.subtype_mk _⟩,fun w => rfl⟩
  have hfrontierCircleIsotopy (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (H : AmbientIsotopy ↥(borderedRegion σ))
      (hbase : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
        {y | y.val ∈ boundaryCircle})
      (hfull : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier (borderedRegion σ)} =
        {y | y.val ∈ frontier (borderedRegion σ)})
      (i : frontierIndices σ) (c : C(Circle,↥(borderedRegion σ)))
      (hparam : ∀ w, (c w).val = (frontierCurves σ i).val.map w) :
      ∃ B : AmbientIsotopy Circle, ∀ t w, c (B.map (t,w)) = H.map (t,c w) := by
    have hce : Topology.IsEmbedding c := by
      apply Topology.IsEmbedding.of_comp c.continuous continuous_subtype_val
      have heq : (fun w => (c w).val) = (frontierCurves σ i).val.map := funext hparam
      change Topology.IsEmbedding (fun w => (c w).val)
      rw [heq]
      exact (frontierCurves σ i).val.embedded
    have hRange : Set.range c = {y | y.val ∈ (frontierCurves σ i).val.image} := by
      ext y
      constructor
      · rintro ⟨w,rfl⟩
        exact ⟨w,(hparam w).symm⟩
      · rintro ⟨w,hw⟩
        refine ⟨w,Subtype.ext ?_⟩
        exact (hparam w).trans hw
    let q : Circle ≃ₜ ↥(Set.range c) := hce.toHomeomorph
    have hmem (t : Interval) (w : Circle) : H.map (t,c w) ∈ Set.range c := by
      rw [hRange]
      apply hfrontierIsotopyComponent σ hz H hbase hfull i (c w)
      exact ⟨w,(hparam w).symm⟩
    let bm : C(Interval × Circle,Circle) := {
      toFun := fun z => q.symm ⟨H.map (z.1,c z.2),hmem z.1 z.2⟩
      continuous_toFun := q.symm.continuous.comp
        ((H.map.continuous.comp (continuous_fst.prodMk (c.continuous.comp continuous_snd))).subtype_mk _) }
    have hb (t : Interval) (w : Circle) : c (bm (t,w)) = H.map (t,c w) := by
      have hh := q.apply_symm_apply ⟨H.map (t,c w),hmem t w⟩
      exact congrArg Subtype.val hh
    have hhomeo (t : Interval) : ∃ e : Circle ≃ₜ Circle, ∀ w, e w = bm (t,w) := by
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      have heImage : e '' Set.range c = Set.range c := by
        have heFun : (e : ↥(borderedRegion σ) → ↥(borderedRegion σ)) = fun y => H.map (t,y) :=
          funext he
        rw [heFun,hRange]
        exact hfrontierIsotopyCircleImage σ hz H hbase hfull i t
      have hiff (y : ↥(borderedRegion σ)) : y ∈ Set.range c ↔ e y ∈ Set.range c := by
        constructor
        · intro hy
          rw [← heImage]
          exact ⟨y,hy,rfl⟩
        · intro hy
          rw [← heImage] at hy
          obtain ⟨z,hz,heq⟩ := hy
          exact e.injective heq ▸ hz
      let eR : ↥(Set.range c) ≃ₜ ↥(Set.range c) := e.subtype hiff
      refine ⟨q.trans (eR.trans q.symm),?_⟩
      intro w
      apply congrArg q.symm
      apply Subtype.ext
      exact he (c w)
    refine ⟨{map := bm,homeomorphism_at := hhomeo,at_zero := ?_},hb⟩
    intro w
    apply hce.injective
    rw [hb,H.at_zero]
  have hAnnularBoundaryMotion (B : AmbientIsotopy Circle) :
      ∃ G : AmbientIsotopy (Interval × Circle),
        (∀ t w, G.map (t,(0,w)) = (0,B.map (t,w))) ∧
        (∀ t w, G.map (t,(1,w)) = (1,w)) ∧
        ∀ t y, (G.map (t,y)).1 = y.1 := by
    let scale (t s : Interval) : Interval := ⟨(1-(s:ℝ))*(t:ℝ),by
      constructor <;> nlinarith [s.property.1,s.property.2,t.property.1,t.property.2]⟩
    have hs : Continuous (fun z : Interval × Interval => scale z.1 z.2) := by
      dsimp [scale]
      fun_prop
    let F : Interval × (Interval × Circle) → Interval × Circle := fun z =>
      (z.2.1,B.map (scale z.1 z.2.1,z.2.2))
    have hF : Continuous F :=
      (continuous_fst.comp continuous_snd).prodMk
        (B.map.continuous.comp
          ((hs.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
            (continuous_snd.comp continuous_snd)))
    have hhomeo (t : Interval) :
        ∃ e : (Interval × Circle) ≃ₜ (Interval × Circle), ∀ y, e y = F (t,y) := by
      have hi : Function.Injective (fun y => F (t,y)) := by
        rintro ⟨s,w⟩ ⟨u,v⟩ heq
        have hsu : s = u := congrArg Prod.fst heq
        subst u
        obtain ⟨e,he⟩ := B.homeomorphism_at (scale t s)
        have hwv : w = v :=
          e.injective ((he w).trans ((congrArg Prod.snd heq).trans (he v).symm))
        exact congrArg (fun z : Circle => (s,z)) hwv
      have hsur : Function.Surjective (fun y => F (t,y)) := by
        rintro ⟨s,w⟩
        obtain ⟨e,he⟩ := B.homeomorphism_at (scale t s)
        refine ⟨(s,e.symm w),Prod.ext rfl ?_⟩
        change B.map (scale t s,e.symm w) = w
        rw [← he,e.apply_symm_apply]
      let e := (hF.comp (continuous_const.prodMk continuous_id)).homeoOfEquivCompactToT2
        (f := Equiv.ofBijective (fun y => F (t,y)) ⟨hi,hsur⟩)
      exact ⟨e,fun y => rfl⟩
    have hscale0 (s : Interval) : scale ⟨0,by norm_num⟩ s = ⟨0,by norm_num⟩ :=
      Subtype.ext (by change (1-(s:ℝ))*0 = 0; ring)
    let G : AmbientIsotopy (Interval × Circle) := {
      map := ⟨F,hF⟩
      homeomorphism_at := hhomeo
      at_zero := by
        rintro ⟨s,w⟩
        change (s,B.map (scale ⟨0,by norm_num⟩ s,w)) = (s,w)
        rw [hscale0,B.at_zero] }
    refine ⟨G,?_,?_,fun t y => rfl⟩
    · intro t w
      have ht : scale t 0 = t := Subtype.ext (by change (1-0)*(t:ℝ) = (t:ℝ); ring)
      change (0,B.map (scale t 0,w)) = (0,B.map (t,w))
      rw [ht]
    · intro t w
      have ht : scale t 1 = ⟨0,by norm_num⟩ := Subtype.ext (by change (1-1)*(t:ℝ) = 0; ring)
      change (1,B.map (scale t 1,w)) = (1,w)
      rw [ht,B.at_zero]
  have hActualPositiveExteriorCollar (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (w : ↥Fv) (hw : w ∈ retainedPlus σ) :
      ∃ L : C(Interval × Circle,Q), Topology.IsEmbedding L ∧
        (∀ u, (L (0,u)).val = (finitePlus w).val.map u) ∧
        (∀ y, (L y).val ∈ borderedRegion σ ↔ y.1 = 0) ∧
        (∀ y, (L y).val ∈ finiteBands w) ∧
        (∀ u, L (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range L)) ∧
        IsOpen (L '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1}) := by
    have hwσ := (Finset.mem_filter.mp hw).1
    have hmeet := (Finset.mem_filter.mp hw).2
    obtain ⟨E,δ,hδ,hδ1,hE,hB,hm,hp,hcore,hminus,hplus⟩ :=
      hretainedCoordinateCharts σ hz w hwσ
    obtain ⟨η,hη,hη1,hchart⟩ := hplus hmeet
    let ε : ℝ := min η δ / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεη : ε < η := by
      have hh := min_le_left η δ
      dsimp [ε]
      linarith
    have hεδ : ε < δ := by
      have hh := min_le_right η δ
      dsimp [ε]
      linarith
    let radial (s : Interval) : Set.Ioo (-1 : ℝ) 1 :=
      ⟨δ-ε*(s:ℝ),by constructor <;> nlinarith [s.property.1,s.property.2]⟩
    have hrad : Continuous radial := by dsimp [radial]; fun_prop
    let f : C(Interval × Circle,S) :=
      ⟨fun y => E (radial y.1,y.2),E.continuous.comp
        ((hrad.comp continuous_fst).prodMk continuous_snd)⟩
    have hfB (y : Interval × Circle) : f y ∈ finiteBands w := by
      rw [hB]
      refine ⟨(radial y.1,y.2),?_,rfl⟩
      change |δ-ε*(y.1:ℝ)| ≤ δ
      rw [abs_le]
      constructor <;> nlinarith [y.1.property.1,y.1.property.2]
    have hfD (y : Interval × Circle) : f y ∉ D :=
      (hfiniteBands w).2.2.2.2.1 (hfB y)
    let L : C(Interval × Circle,Q) :=
      ⟨fun y => ⟨f y,fun ho => hfD y (hOD ho)⟩,f.continuous.subtype_mk _⟩
    have hLi : Function.Injective L := by
      rintro ⟨s,u⟩ ⟨t,v⟩ heq
      have he : (radial s,u) = (radial t,v) :=
        hE.injective (congrArg Subtype.val heq)
      have hst : s = t := by
        apply Subtype.ext
        have hh := congrArg (fun z => (z.1:ℝ)) he
        change δ-ε*(s:ℝ) = δ-ε*(t:ℝ) at hh
        nlinarith
      have huv : u = v := congrArg (fun z : Set.Ioo (-1 : ℝ) 1 × Circle => z.2) he
      exact Prod.ext hst huv
    have hstrict : IsOpen (L '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1}) := by
      let W : Set (Set.Ioo (-1 : ℝ) 1 × Circle) :=
        {z | δ-ε < (z.1:ℝ) ∧ (z.1:ℝ) < δ}
      have hWo : IsOpen W := by
        change IsOpen ({z : Set.Ioo (-1 : ℝ) 1 × Circle | δ-ε < (z.1:ℝ)} ∩
          {z : Set.Ioo (-1 : ℝ) 1 × Circle | (z.1:ℝ) < δ})
        exact (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).inter
          (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const)
      have heq : L '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1} =
          Subtype.val ⁻¹' (E '' W) := by
        ext q
        constructor
        · rintro ⟨y,hy,he⟩
          change 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1 at hy
          refine ⟨(radial y.1,y.2),?_,congrArg Subtype.val he⟩
          change δ-ε < δ-ε*(y.1:ℝ) ∧ δ-ε*(y.1:ℝ) < δ
          constructor <;> nlinarith
        · rintro ⟨z,hz,he⟩
          change δ-ε < (z.1:ℝ) ∧ (z.1:ℝ) < δ at hz
          have ht0 : 0 < (δ-(z.1:ℝ))/ε := div_pos (by linarith) hε
          have ht1 : (δ-(z.1:ℝ))/ε < 1 := by
            apply (div_lt_iff₀ hε).mpr
            linarith
          let t : Interval := ⟨(δ-(z.1:ℝ))/ε,ht0.le,ht1.le⟩
          have source_hr : radial t = z.1 := by
            apply Subtype.ext
            change δ-ε*((δ-(z.1:ℝ))/ε) = (z.1:ℝ)
            field_simp
            <;> ring
          refine ⟨(t,z.2),⟨ht0,ht1⟩,Subtype.ext ?_⟩
          change E (radial t,z.2) = q.val
          rw [source_hr]
          exact he
      rw [heq]
      exact (hE.isOpenMap W hWo).preimage continuous_subtype_val
    have hseam (u : Circle) :
        L (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range L) := by
      let W : Set (Set.Ioo (-1 : ℝ) 1 × Circle) := {z | |(z.1:ℝ)-δ| < ε/2}
      have hWo : IsOpen W := isOpen_lt (by fun_prop) continuous_const
      let T : Set Q := Subtype.val ⁻¹' (E '' W ∩ Dᶜ)
      have hTo : IsOpen T := ((hE.isOpenMap W hWo).inter hPopen).preimage continuous_subtype_val
      have hTsub : T ⊆ {q : Q | q.val ∈ borderedRegion σ} ∪ Set.range L := by
        rintro q ⟨⟨z,hz,heq⟩,hqD⟩
        change |(z.1:ℝ)-δ| < ε/2 at hz
        have hzabs : |(z.1:ℝ)-δ| < η := by
          change |(z.1:ℝ)-δ| < ε/2 at hz
          linarith
        have hzD : E z ∉ D := heq.symm ▸ hqD
        by_cases hside : δ ≤ (z.1:ℝ)
        · left
          change q.val ∈ borderedRegion σ
          rw [← heq]
          exact (hchart z hzabs hzD).mpr hside
        · right
          have hwidth := abs_lt.mp hz
          let t : Interval := ⟨(δ-(z.1:ℝ))/ε,by
            constructor
            · exact div_nonneg (by linarith) hε.le
            · apply (div_le_iff₀ hε).mpr
              linarith⟩
          have source_hr : radial t = z.1 := by
            apply Subtype.ext
            change δ-ε*((δ-(z.1:ℝ))/ε) = (z.1:ℝ)
            field_simp
            <;> ring
          refine ⟨(t,z.2),Subtype.ext ?_⟩
          change E (radial t,z.2) = q.val
          rw [source_hr]
          exact heq
      have hmem : L (0,u) ∈ T := by
        refine ⟨⟨(radial 0,u),?_,rfl⟩,hfD (0,u)⟩
        change |δ-ε*0-δ| < ε/2
        simpa using half_pos hε
      exact (interior_maximal hTsub hTo) hmem
    refine ⟨L,(L.continuous.isClosedEmbedding hLi).isEmbedding,?_,?_,hfB,hseam,hstrict⟩
    · intro u
      change E (radial 0,u) = (finitePlus w).val.map u
      rw [hp]
      congr 1
      exact Prod.ext (Subtype.ext (by change δ-ε*0 = δ; ring)) rfl
    · intro y
      have hclose : |(radial y.1:ℝ)-δ| < η := by
        change |δ-ε*(y.1:ℝ)-δ| < η
        rw [abs_lt]
        constructor <;> nlinarith [y.1.property.1,y.1.property.2]
      have hh := hchart (radial y.1,y.2) hclose (hfD y)
      change E (radial y.1,y.2) ∈ borderedRegion σ ↔ y.1 = 0
      rw [hh]
      change δ ≤ δ-ε*(y.1:ℝ) ↔ y.1 = 0
      constructor
      · intro hh
        apply Subtype.ext
        change (y.1:ℝ) = 0
        nlinarith [y.1.property.1]
      · intro hh
        rw [hh]
        change δ ≤ δ-ε*0
        linarith
  have hActualNegativeExteriorCollar (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (w : ↥Fv) (hw : w ∈ retainedMinus σ) :
      ∃ L : C(Interval × Circle,Q), Topology.IsEmbedding L ∧
        (∀ u, (L (0,u)).val = (finiteMinus w).val.map u) ∧
        (∀ y, (L y).val ∈ borderedRegion σ ↔ y.1 = 0) ∧
        (∀ y, (L y).val ∈ finiteBands w) ∧
        (∀ u, L (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range L)) ∧
        IsOpen (L '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1}) := by
    have hwσ := (Finset.mem_filter.mp hw).1
    have hmeet := (Finset.mem_filter.mp hw).2
    obtain ⟨E,δ,hδ,hδ1,hE,hB,hm,hp,hcore,hminus,hplus⟩ :=
      hretainedCoordinateCharts σ hz w hwσ
    obtain ⟨η,hη,hη1,hchart⟩ := hminus hmeet
    let ε : ℝ := min η δ / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεη : ε < η := by
      have hh := min_le_left η δ
      dsimp [ε]
      linarith
    have hεδ : ε < δ := by
      have hh := min_le_right η δ
      dsimp [ε]
      linarith
    let radial (s : Interval) : Set.Ioo (-1 : ℝ) 1 :=
      ⟨-δ+ε*(s:ℝ),by constructor <;> nlinarith [s.property.1,s.property.2]⟩
    have hrad : Continuous radial := by dsimp [radial]; fun_prop
    let f : C(Interval × Circle,S) :=
      ⟨fun y => E (radial y.1,y.2),E.continuous.comp
        ((hrad.comp continuous_fst).prodMk continuous_snd)⟩
    have hfB (y : Interval × Circle) : f y ∈ finiteBands w := by
      rw [hB]
      refine ⟨(radial y.1,y.2),?_,rfl⟩
      change |-δ+ε*(y.1:ℝ)| ≤ δ
      rw [abs_le]
      constructor <;> nlinarith [y.1.property.1,y.1.property.2]
    have hfD (y : Interval × Circle) : f y ∉ D :=
      (hfiniteBands w).2.2.2.2.1 (hfB y)
    let L : C(Interval × Circle,Q) :=
      ⟨fun y => ⟨f y,fun ho => hfD y (hOD ho)⟩,f.continuous.subtype_mk _⟩
    have hLi : Function.Injective L := by
      rintro ⟨s,u⟩ ⟨t,v⟩ heq
      have he : (radial s,u) = (radial t,v) :=
        hE.injective (congrArg Subtype.val heq)
      have hst : s = t := by
        apply Subtype.ext
        have hh := congrArg (fun z => (z.1:ℝ)) he
        change -δ+ε*(s:ℝ) = -δ+ε*(t:ℝ) at hh
        nlinarith
      have huv : u = v := congrArg (fun z : Set.Ioo (-1 : ℝ) 1 × Circle => z.2) he
      exact Prod.ext hst huv
    have hstrict : IsOpen (L '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1}) := by
      let W : Set (Set.Ioo (-1 : ℝ) 1 × Circle) :=
        {z | -δ < (z.1:ℝ) ∧ (z.1:ℝ) < -δ+ε}
      have hWo : IsOpen W := by
        change IsOpen ({z : Set.Ioo (-1 : ℝ) 1 × Circle | -δ < (z.1:ℝ)} ∩
          {z : Set.Ioo (-1 : ℝ) 1 × Circle | (z.1:ℝ) < -δ+ε})
        exact (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).inter
          (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const)
      have heq : L '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1} =
          Subtype.val ⁻¹' (E '' W) := by
        ext q
        constructor
        · rintro ⟨y,hy,he⟩
          change 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1 at hy
          refine ⟨(radial y.1,y.2),?_,congrArg Subtype.val he⟩
          change -δ < -δ+ε*(y.1:ℝ) ∧ -δ+ε*(y.1:ℝ) < -δ+ε
          constructor <;> nlinarith
        · rintro ⟨z,hz,he⟩
          change -δ < (z.1:ℝ) ∧ (z.1:ℝ) < -δ+ε at hz
          have ht0 : 0 < ((z.1:ℝ)+δ)/ε := div_pos (by linarith) hε
          have ht1 : ((z.1:ℝ)+δ)/ε < 1 := by
            apply (div_lt_iff₀ hε).mpr
            linarith
          let t : Interval := ⟨((z.1:ℝ)+δ)/ε,ht0.le,ht1.le⟩
          have source_hr : radial t = z.1 := by
            apply Subtype.ext
            change -δ+ε*(((z.1:ℝ)+δ)/ε) = (z.1:ℝ)
            field_simp
            <;> ring
          refine ⟨(t,z.2),⟨ht0,ht1⟩,Subtype.ext ?_⟩
          change E (radial t,z.2) = q.val
          rw [source_hr]
          exact he
      rw [heq]
      exact (hE.isOpenMap W hWo).preimage continuous_subtype_val
    have hseam (u : Circle) :
        L (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range L) := by
      let W : Set (Set.Ioo (-1 : ℝ) 1 × Circle) := {z | |(z.1:ℝ)+δ| < ε/2}
      have hWo : IsOpen W := isOpen_lt (by fun_prop) continuous_const
      let T : Set Q := Subtype.val ⁻¹' (E '' W ∩ Dᶜ)
      have hTo : IsOpen T := ((hE.isOpenMap W hWo).inter hPopen).preimage continuous_subtype_val
      have hTsub : T ⊆ {q : Q | q.val ∈ borderedRegion σ} ∪ Set.range L := by
        rintro q ⟨⟨z,hz,heq⟩,hqD⟩
        change |(z.1:ℝ)+δ| < ε/2 at hz
        have hzabs : |(z.1:ℝ)+δ| < η := by
          change |(z.1:ℝ)+δ| < ε/2 at hz
          linarith
        have hzD : E z ∉ D := heq.symm ▸ hqD
        by_cases hside : (z.1:ℝ) ≤ -δ
        · left
          change q.val ∈ borderedRegion σ
          rw [← heq]
          exact (hchart z hzabs hzD).mpr hside
        · right
          have hwidth := abs_lt.mp hz
          let t : Interval := ⟨((z.1:ℝ)+δ)/ε,by
            constructor
            · exact div_nonneg (by linarith) hε.le
            · apply (div_le_iff₀ hε).mpr
              linarith⟩
          have source_hr : radial t = z.1 := by
            apply Subtype.ext
            change -δ+ε*(((z.1:ℝ)+δ)/ε) = (z.1:ℝ)
            field_simp
            <;> ring
          refine ⟨(t,z.2),Subtype.ext ?_⟩
          change E (radial t,z.2) = q.val
          rw [source_hr]
          exact heq
      have hmem : L (0,u) ∈ T := by
        refine ⟨⟨(radial 0,u),?_,rfl⟩,hfD (0,u)⟩
        change |-δ+ε*0+δ| < ε/2
        simpa using half_pos hε
      exact (interior_maximal hTsub hTo) hmem
    refine ⟨L,(L.continuous.isClosedEmbedding hLi).isEmbedding,?_,?_,hfB,hseam,hstrict⟩
    · intro u
      change E (radial 0,u) = (finiteMinus w).val.map u
      rw [hm]
      congr 1
      exact Prod.ext (Subtype.ext (by change -δ+ε*0 = -δ; ring)) rfl
    · intro y
      have hclose : |(radial y.1:ℝ)+δ| < η := by
        change |-δ+ε*(y.1:ℝ)+δ| < η
        rw [abs_lt]
        constructor <;> nlinarith [y.1.property.1,y.1.property.2]
      have hh := hchart (radial y.1,y.2) hclose (hfD y)
      change E (radial y.1,y.2) ∈ borderedRegion σ ↔ y.1 = 0
      rw [hh]
      change -δ+ε*(y.1:ℝ) ≤ -δ ↔ y.1 = 0
      constructor
      · intro hh
        apply Subtype.ext
        change (y.1:ℝ) = 0
        nlinarith [y.1.property.1]
      · intro hh
        rw [hh]
        change -δ+ε*0 ≤ -δ
        linarith
  have hActualEmbeddedAnnularMotion (L : C(Interval × Circle,Q))
      (hL : Topology.IsEmbedding L) (B : AmbientIsotopy Circle) :
      ∃ A : AmbientIsotopy ↥(Set.range L),
        (∀ t u, (A.map (t,⟨L (0,u),Set.mem_range_self _⟩)).val = L (0,B.map (t,u))) ∧
        ∀ t u, (A.map (t,⟨L (1,u),Set.mem_range_self _⟩)).val = L (1,u) := by
    obtain ⟨G,hinner,houter,hradial⟩ := hAnnularBoundaryMotion B
    let q : (Interval × Circle) ≃ₜ ↥(Set.range L) := hL.toHomeomorph
    let A : AmbientIsotopy ↥(Set.range L) := {
      map := ⟨fun z => q (G.map (z.1,q.symm z.2)),
        q.continuous.comp (G.map.continuous.comp
          (continuous_fst.prodMk (q.symm.continuous.comp continuous_snd)))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨e,he⟩ := G.homeomorphism_at t
        refine ⟨q.symm.trans (e.trans q),?_⟩
        intro y
        exact congrArg q (he (q.symm y))
      at_zero := by
        intro y
        change q (G.map (⟨0,by norm_num⟩,q.symm y)) = y
        rw [G.at_zero,q.apply_symm_apply] }
    have hq (y : Interval × Circle) : q y = ⟨L y,Set.mem_range_self _⟩ := rfl
    have hact (t : Interval) (y : Interval × Circle) :
        (A.map (t,⟨L y,Set.mem_range_self _⟩)).val = L (G.map (t,y)) := by
      change (q (G.map (t,q.symm ⟨L y,Set.mem_range_self _⟩))).val = _
      rw [← hq,q.symm_apply_apply]
      rfl
    refine ⟨A,?_,?_⟩
    · intro t u
      rw [hact,hinner]
    · intro t u
      rw [hact,houter]
  have hActualEssentialFrontierCollar (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (i : frontierIndices σ) :
      ∃ L : C(Interval × Circle,Q), Topology.IsEmbedding L ∧
        (∀ u, (L (0,u)).val = (frontierCurves σ i).val.map u) ∧
        (∀ y, (L y).val ∈ borderedRegion σ ↔ y.1 = 0) ∧
        (∀ u, L (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range L)) ∧
        IsOpen (L '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1}) := by
    cases i with
    | inl j =>
      obtain ⟨L,hL,hzero,hout,hband,hseam,hstrict⟩ := hActualNegativeExteriorCollar σ hz j.val j.property
      exact ⟨L,hL,hzero,hout,hseam,hstrict⟩
    | inr j =>
      obtain ⟨L,hL,hzero,hout,hband,hseam,hstrict⟩ := hActualPositiveExteriorCollar σ hz j.val j.property
      exact ⟨L,hL,hzero,hout,hseam,hstrict⟩
  have hIntrinsicBoundaryActualCollarMotion (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (H : AmbientIsotopy ↥(borderedRegion σ))
      (hbase : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
        {y | y.val ∈ boundaryCircle})
      (hfull : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier (borderedRegion σ)} =
        {y | y.val ∈ frontier (borderedRegion σ)})
      (i : frontierIndices σ) (c : C(Circle,↥(borderedRegion σ)))
      (hparam : ∀ u, (c u).val = (frontierCurves σ i).val.map u) :
      ∃ (L : C(Interval × Circle,Q)) (hL : Topology.IsEmbedding L)
        (A : AmbientIsotopy ↥(Set.range L)),
        (∀ u, (L (0,u)).val = (frontierCurves σ i).val.map u) ∧
        (∀ y, (L y).val ∈ borderedRegion σ ↔ y.1 = 0) ∧
        (∀ t u, (A.map (t,⟨L (0,u),Set.mem_range_self _⟩)).val.val =
          (H.map (t,c u)).val) ∧
        ∀ t u, (A.map (t,⟨L (1,u),Set.mem_range_self _⟩)).val = L (1,u) := by
    obtain ⟨L,hL,hzero,houtside,hseam,hstrict⟩ := hActualEssentialFrontierCollar σ hz i
    obtain ⟨B,hB⟩ := hfrontierCircleIsotopy σ hz H hbase hfull i c hparam
    obtain ⟨A,hinner,houter⟩ := hActualEmbeddedAnnularMotion L hL B
    refine ⟨L,hL,A,hzero,houtside,?_,houter⟩
    intro t u
    have hi := congrArg Subtype.val (hinner t u)
    have hb := congrArg Subtype.val (hB t u)
    rw [hzero] at hi
    rw [hparam] at hb
    exact hi.trans hb
  have hActualExteriorCollarNarrowing (σ : Finset ↥Fv)
      (L : C(Interval × Circle,Q)) (hL : Topology.IsEmbedding L)
      (houtside : ∀ y, (L y).val ∈ borderedRegion σ ↔ y.1 = 0)
      (hseam : ∀ u, L (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range L))
      (hstrict : IsOpen (L '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1}))
      (U : Set Q) (hU : IsOpen U) (hzero : ∀ u, L (0,u) ∈ U) :
      ∃ K : C(Interval × Circle,Q), Topology.IsEmbedding K ∧
        (∀ u, K (0,u) = L (0,u)) ∧ Set.range K ⊆ U ∧
        Set.range K ⊆ Set.range L ∧
        (∀ y, (K y).val ∈ borderedRegion σ ↔ y.1 = 0) ∧
        (∀ u, K (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range K)) ∧
        IsOpen (K '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1}) := by
    have hprod : ({0} : Set Interval) ×ˢ (Set.univ : Set Circle) ⊆ L ⁻¹' U := by
      rintro ⟨s,u⟩ ⟨hs,hu⟩
      have hs0 : s = 0 := hs
      subst s
      exact hzero u
    obtain ⟨V,W,hV,hW,h0,hall,hVW⟩ := generalized_tube_lemma
      (isCompact_singleton (x := (0 : Interval))) isCompact_univ
      (hU.preimage L.continuous) hprod
    obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp hV 0 (h0 (Set.mem_singleton _))
    let b : ℝ := min η 1 / 2
    have hb : 0 < b := by dsimp [b]; positivity
    have hbη : b < η := by
      have hh := min_le_left η 1
      dsimp [b]
      linarith
    have hb1 : b < 1 := by
      have hh := min_le_right η 1
      dsimp [b]
      linarith
    let ρ (s : Interval) : Interval := ⟨b*(s:ℝ),by
      constructor <;> nlinarith [s.property.1,s.property.2]⟩
    have hρ : Continuous ρ := by dsimp [ρ]; fun_prop
    have hρ0 : ρ 0 = 0 := Subtype.ext (by change b*0 = 0; ring)
    have hρzero (s : Interval) : ρ s = 0 ↔ s = 0 := by
      constructor
      · intro hh
        apply Subtype.ext
        have hv := congrArg Subtype.val hh
        change b*(s:ℝ) = 0 at hv
        change (s:ℝ) = 0
        nlinarith
      · intro hh
        rw [hh,hρ0]
    have hρV (s : Interval) : ρ s ∈ V := by
      apply hball
      change dist (ρ s) (0 : Interval) < η
      rw [Subtype.dist_eq]
      change dist (b*(s:ℝ)) 0 < η
      rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg hb.le s.property.1)]
      nlinarith [s.property.2]
    let K : C(Interval × Circle,Q) :=
      ⟨fun y => L (ρ y.1,y.2),L.continuous.comp
        ((hρ.comp continuous_fst).prodMk continuous_snd)⟩
    have hKi : Function.Injective K := by
      rintro ⟨s,u⟩ ⟨t,v⟩ heq
      have hh : (ρ s,u) = (ρ t,v) := hL.injective heq
      have hst : s = t := by
        apply Subtype.ext
        have hv := congrArg (fun z : Interval × Circle => (z.1:ℝ)) hh
        change b*(s:ℝ) = b*(t:ℝ) at hv
        nlinarith
      have huv : u = v := congrArg (fun z : Interval × Circle => z.2) hh
      exact Prod.ext hst huv
    let Far : Set Q := L '' {y | b ≤ (y.1:ℝ)}
    have hFarc : IsClosed Far := by
      have hs : IsClosed {y : Interval × Circle | b ≤ (y.1:ℝ)} :=
        isClosed_le continuous_const (by fun_prop)
      exact (hs.isCompact.image L.continuous).isClosed
    have hzeroFar (u : Circle) : L (0,u) ∉ Far := by
      rintro ⟨y,hy,he⟩
      have hh : y = (0,u) := hL.injective he
      subst y
      change b ≤ 0 at hy
      linarith
    have hnewseam (u : Circle) :
        K (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range K) := by
      let T : Set Q := interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range L) \ Far
      have hTo : IsOpen T := isOpen_interior.inter hFarc.isOpen_compl
      have hTsub : T ⊆ {q : Q | q.val ∈ borderedRegion σ} ∪ Set.range K := by
        intro q hq
        rcases interior_subset hq.1 with hqF | hqL
        · exact Or.inl hqF
        · obtain ⟨y,hy⟩ := hqL
          have hyb : (y.1:ℝ) < b := by
            by_contra hn
            exact hq.2 ⟨y,le_of_not_gt hn,hy⟩
          let t : Interval := ⟨(y.1:ℝ)/b,by
            constructor
            · exact div_nonneg y.1.property.1 hb.le
            · exact ((div_le_iff₀ hb).mpr (by linarith))⟩
          have hrt : ρ t = y.1 := by
            apply Subtype.ext
            change b*((y.1:ℝ)/b) = (y.1:ℝ)
            field_simp
          right
          refine ⟨(t,y.2),?_⟩
          change L (ρ t,y.2) = q
          rw [hrt]
          exact hy
      have hmem : K (0,u) ∈ T := by
        change L (ρ 0,u) ∈ T
        rw [hρ0]
        exact ⟨hseam u,hzeroFar u⟩
      exact (interior_maximal hTsub hTo) hmem
    have hnewstrict : IsOpen (K '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1}) := by
      have heq : K '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1} =
          (L '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1}) \ Far := by
        ext q
        constructor
        · rintro ⟨y,hy,he⟩
          change 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1 at hy
          refine ⟨⟨(ρ y.1,y.2),?_,he⟩,?_⟩
          · change 0 < b*(y.1:ℝ) ∧ b*(y.1:ℝ) < 1
            constructor <;> nlinarith
          · rintro ⟨z,hz,hzq⟩
            have hh : z = (ρ y.1,y.2) := hL.injective (hzq.trans he.symm)
            subst z
            change b ≤ b*(y.1:ℝ) at hz
            nlinarith
        · rintro ⟨⟨y,hy,he⟩,hFar⟩
          change 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1 at hy
          have hyb : (y.1:ℝ) < b := by
            by_contra hn
            exact hFar ⟨y,le_of_not_gt hn,he⟩
          have ht0 : 0 < (y.1:ℝ)/b := div_pos hy.1 hb
          have ht1 : (y.1:ℝ)/b < 1 := (div_lt_iff₀ hb).mpr (by linarith)
          let t : Interval := ⟨(y.1:ℝ)/b,ht0.le,ht1.le⟩
          have hrt : ρ t = y.1 := by
            apply Subtype.ext
            change b*((y.1:ℝ)/b) = (y.1:ℝ)
            field_simp
          refine ⟨(t,y.2),⟨ht0,ht1⟩,?_⟩
          change L (ρ t,y.2) = q
          rw [hrt]
          exact he
      rw [heq]
      exact hstrict.inter hFarc.isOpen_compl
    refine ⟨K,(K.continuous.isClosedEmbedding hKi).isEmbedding,?_,?_,?_,?_,hnewseam,hnewstrict⟩
    · intro u
      change L (ρ 0,u) = L (0,u)
      rw [hρ0]
    · rintro z ⟨y,rfl⟩
      exact hVW ⟨hρV y.1,hall (Set.mem_univ y.2)⟩
    · rintro z ⟨y,rfl⟩
      exact ⟨(ρ y.1,y.2),rfl⟩
    · intro y
      exact (houtside (ρ y.1,y.2)).trans (hρzero y.1)
  have hActualSimultaneousExteriorCollars (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0) :
      ∃ K : frontierIndices σ → C(Interval × Circle,Q),
        (∀ i, Topology.IsEmbedding (K i) ∧
          (∀ u, (K i (0,u)).val = (frontierCurves σ i).val.map u) ∧
          (∀ y, (K i y).val ∈ borderedRegion σ ↔ y.1 = 0) ∧
          (∀ u, K i (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range (K i))) ∧
          IsOpen (K i '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1})) ∧
        ∀ i j, i ≠ j → Disjoint (Set.range (K i)) (Set.range (K j)) := by
    choose L hL hzero hout hseam hstrict using hActualEssentialFrontierCollar σ hz
    let C : frontierIndices σ → Set Q := fun i => Set.range (fun u : Circle => L i (0,u))
    have hcompact (i : frontierIndices σ) : IsCompact (C i) :=
      isCompact_range ((L i).continuous.comp (continuous_const.prodMk continuous_id))
    have hdisj (i j : frontierIndices σ) (hij : i ≠ j) : Disjoint (C i) (C j) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨u,hu⟩ ⟨v,hv⟩
      apply Set.disjoint_left.mp (hfrontierFamilyDisjoint σ hz i j hij)
      · exact ⟨u,(hzero i u).symm.trans (congrArg Subtype.val hu)⟩
      · exact ⟨v,(hzero j v).symm.trans (congrArg Subtype.val hv)⟩
    have hsep (i j : frontierIndices σ) (hij : i ≠ j) :
        ∃ U V : Set Q, IsOpen U ∧ IsOpen V ∧ C i ⊆ U ∧ C j ⊆ V ∧ Disjoint U V :=
      SeparatedNhds.of_isCompact_isCompact (hcompact i) (hcompact j) (hdisj i j hij)
    choose U V hU hV hcU hcV hUV using hsep
    let N : frontierIndices σ → Set Q := fun i =>
      (⋂ j, ⋂ h : i ≠ j, U i j h) ∩ (⋂ j, ⋂ h : j ≠ i, V j i h)
    have hN (i : frontierIndices σ) : IsOpen (N i) ∧ C i ⊆ N i := by
      refine ⟨(isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun h => hU i j h).inter
        (isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun h => hV j i h),?_⟩
      intro y hy
      exact ⟨Set.mem_iInter.mpr fun j => Set.mem_iInter.mpr fun h => hcU i j h hy,
        Set.mem_iInter.mpr fun j => Set.mem_iInter.mpr fun h => hcV j i h hy⟩
    have hdN (i j : frontierIndices σ) (hij : i ≠ j) : Disjoint (N i) (N j) := by
      apply (hUV i j hij).mono
      · intro y hy
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hy.1 j) hij
      · intro y hy
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hy.2 i) hij
    choose K hK hKzero hKU hKL hKout hKseam hKstrict using fun i =>
      hActualExteriorCollarNarrowing σ (L i) (hL i) (hout i) (hseam i) (hstrict i) (N i) (hN i).1
        (fun u => (hN i).2 (Set.mem_range_self u))
    refine ⟨K,?_,?_⟩
    · intro i
      refine ⟨hK i,?_,hKout i,hKseam i,hKstrict i⟩
      intro u
      rw [hKzero i u]
      exact hzero i u
    · intro i j hij
      exact (hdN i j hij).mono (hKU i) (hKU j)
  have hActualCoherentExteriorCollarMotions (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (H : AmbientIsotopy ↥(borderedRegion σ))
      (hbase : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
        {y | y.val ∈ boundaryCircle})
      (hfull : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier (borderedRegion σ)} =
        {y | y.val ∈ frontier (borderedRegion σ)}) :
      ∃ (K : frontierIndices σ → C(Interval × Circle,Q))
        (A : ∀ i, AmbientIsotopy ↥(Set.range (K i)))
        (c : frontierIndices σ → C(Circle,↥(borderedRegion σ))),
        (∀ i, Topology.IsEmbedding (K i) ∧
          (∀ u, (K i (0,u)).val = (frontierCurves σ i).val.map u) ∧
          (∀ y, (K i y).val ∈ borderedRegion σ ↔ y.1 = 0) ∧
          (∀ u, K i (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range (K i))) ∧
          IsOpen (K i '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1})) ∧
        (∀ i j, i ≠ j → Disjoint (Set.range (K i)) (Set.range (K j))) ∧
        (∀ i u, (c i u).val = (frontierCurves σ i).val.map u) ∧
        (∀ i t u, ((A i).map (t,⟨K i (0,u),Set.mem_range_self _⟩)).val.val =
          (H.map (t,c i u)).val) ∧
        ∀ i t u, ((A i).map (t,⟨K i (1,u),Set.mem_range_self _⟩)).val = K i (1,u) := by
    obtain ⟨K,hK,hdK⟩ := hActualSimultaneousExteriorCollars σ hz
    choose c hc using hfrontierCircleParam σ hz
    choose B hB using fun i => hfrontierCircleIsotopy σ hz H hbase hfull i (c i) (hc i)
    choose A hinner houter using fun i => hActualEmbeddedAnnularMotion (K i) (hK i).1 (B i)
    refine ⟨K,A,c,hK,hdK,hc,?_,houter⟩
    intro i t u
    have hi := congrArg Subtype.val (hinner i t u)
    have hb := congrArg Subtype.val (hB i t u)
    rw [(hK i).2.1] at hi
    rw [hc i] at hb
    exact hi.trans hb
  have hActualCollarSeamCover (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (K : frontierIndices σ → C(Interval × Circle,Q))
      (hK : ∀ i, Topology.IsEmbedding (K i) ∧
        (∀ u, (K i (0,u)).val = (frontierCurves σ i).val.map u) ∧
        (∀ y, (K i y).val ∈ borderedRegion σ ↔ y.1 = 0) ∧
        (∀ u, K i (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range (K i))) ∧
        IsOpen (K i '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1})) :
      ({q : Q | q.val ∈ borderedRegion σ} ⊆
        interior ({q : Q | q.val ∈ borderedRegion σ} ∪ ⋃ i, Set.range (K i))) ∧
      ∀ i y, K i y ∉ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ ⋃ j, Set.range (K j)) →
        y.1 = 1 := by
    let FQ : Set Q := {q | q.val ∈ borderedRegion σ}
    let T : Set Q := FQ ∪ ⋃ i, Set.range (K i)
    have hFT : FQ ⊆ T := Set.subset_union_left
    have hKT (i : frontierIndices σ) : Set.range (K i) ⊆ T :=
      fun q hq => Or.inr (Set.mem_iUnion.mpr ⟨i,hq⟩)
    have hFinside : FQ ⊆ interior T := by
      intro q hq
      by_cases hf : q.val ∈ frontier (borderedRegion σ)
      · rw [hfrontierFamilyExact σ hz] at hf
        rcases hf with hb | hc
        · have hi : q ∈ interior FQ := hregionBoundaryRelativeInterior σ hb
          exact interior_mono hFT hi
        · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hc
          obtain ⟨u,hu⟩ := hi
          have hpoint : K i (0,u) = q := Subtype.ext (((hK i).2.1 u).trans hu)
          have hsub : FQ ∪ Set.range (K i) ⊆ T :=
            Set.union_subset hFT (hKT i)
          exact hpoint ▸ interior_mono hsub ((hK i).2.2.2.1 u)
      · have hiS : q.val ∈ interior (borderedRegion σ) := by
          by_contra hn
          exact hf ((mem_frontier_iff_notMem_interior (show q.val ∈ borderedRegion σ from hq)).mpr hn)
        have hiQ : q ∈ interior FQ := by
          apply interior_maximal (Set.preimage_mono interior_subset)
            (isOpen_interior.preimage continuous_subtype_val)
          exact hiS
        exact interior_mono hFT hiQ
    refine ⟨hFinside,?_⟩
    intro i y hn
    by_contra hy1
    by_cases hy0 : y.1 = 0
    · have hmem : (K i y).val ∈ borderedRegion σ := ((hK i).2.2.1 y).mpr hy0
      exact hn (hFinside hmem)
    · have ht0 : 0 < (y.1:ℝ) := by
        apply lt_of_le_of_ne y.1.property.1
        intro he
        exact hy0 (Subtype.ext he.symm)
      have ht1 : (y.1:ℝ) < 1 := by
        apply lt_of_le_of_ne y.1.property.2
        intro he
        exact hy1 (Subtype.ext he)
      have hsub : K i '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1} ⊆ T :=
        fun q hq => hKT i (Set.image_subset_range _ _ hq)
      exact hn ((interior_maximal hsub (hK i).2.2.2.2) ⟨y,⟨ht0,ht1⟩,rfl⟩)
  have hActualJointMotionPasting (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (K : frontierIndices σ → C(Interval × Circle,Q))
      (hK : ∀ i, Topology.IsEmbedding (K i) ∧
        (∀ u, (K i (0,u)).val = (frontierCurves σ i).val.map u) ∧
        (∀ y, (K i y).val ∈ borderedRegion σ ↔ y.1 = 0) ∧
        (∀ u, K i (0,u) ∈ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ Set.range (K i))) ∧
        IsOpen (K i '' {y | 0 < (y.1:ℝ) ∧ (y.1:ℝ) < 1}))
      (hdK : ∀ i j, i ≠ j → Disjoint (Set.range (K i)) (Set.range (K j)))
      (H : AmbientIsotopy ↥(borderedRegion σ))
      (A : ∀ i, AmbientIsotopy ↥(Set.range (K i)))
      (c : frontierIndices σ → C(Circle,↥(borderedRegion σ)))
      (hc : ∀ i u, (c i u).val = (frontierCurves σ i).val.map u)
      (hinner : ∀ i t u, ((A i).map (t,⟨K i (0,u),Set.mem_range_self _⟩)).val.val =
        (H.map (t,c i u)).val)
      (houter : ∀ i t u, ((A i).map (t,⟨K i (1,u),Set.mem_range_self _⟩)).val = K i (1,u)) :
      ∃ G : C(Interval × Q,Q),
        (∀ t y, G (t,regionInQ σ y) = regionInQ σ (H.map (t,y))) ∧
        (∀ i t q, G (t,q.val) = ((A i).map (t,q)).val) ∧
        (∀ t q, q ∉ interior ({q : Q | q.val ∈ borderedRegion σ} ∪ ⋃ i, Set.range (K i)) →
          G (t,q) = q) ∧
        ∀ q, G (⟨0,by norm_num⟩,q) = q := by
    let FQ : Set Q := {q | q.val ∈ borderedRegion σ}
    let T : Set Q := FQ ∪ ⋃ i, Set.range (K i)
    let R : Set Q := (interior T)ᶜ
    obtain ⟨hFinside,hRestOuter⟩ := hActualCollarSeamCover σ hz K hK
    let f0 : C((Prod.snd ⁻¹' FQ : Set (Interval × Q)),Q) := {
      toFun := fun z => regionInQ σ (H.map (z.val.1,⟨z.val.2.val,z.property⟩))
      continuous_toFun := (regionInQ σ).continuous.comp (H.map.continuous.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _))) }
    let fR : C((Prod.snd ⁻¹' R : Set (Interval × Q)),Q) :=
      ⟨fun z => z.val.2,continuous_snd.comp continuous_subtype_val⟩
    let fi (i : frontierIndices σ) : C((Prod.snd ⁻¹' Set.range (K i) : Set (Interval × Q)),Q) := {
      toFun := fun z => ((A i).map (z.val.1,⟨z.val.2,z.property⟩)).val
      continuous_toFun := continuous_subtype_val.comp ((A i).map.continuous.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _))) }
    have hFC (i : frontierIndices σ) (t : Interval) (q : Q)
        (hqF : q ∈ FQ) (hqK : q ∈ Set.range (K i)) :
        f0 ⟨(t,q),hqF⟩ = fi i ⟨(t,q),hqK⟩ := by
      have hqKcopy := hqK
      obtain ⟨⟨s,u⟩,hy⟩ := hqKcopy
      have hyF : (K i (s,u)).val ∈ borderedRegion σ := by
        rw [congrArg Subtype.val hy]
        exact hqF
      have hs : s = 0 := ((hK i).2.2.1 (s,u)).mp hyF
      subst s
      have hqparam : q.val = (frontierCurves σ i).val.map u :=
        (congrArg Subtype.val hy).symm.trans ((hK i).2.1 u)
      have hreg : (⟨q.val,hqF⟩ : ↥(borderedRegion σ)) = c i u :=
        Subtype.ext (hqparam.trans (hc i u).symm)
      have harg : (⟨q,hqK⟩ : ↥(Set.range (K i))) =
          ⟨K i (0,u),Set.mem_range_self _⟩ := Subtype.ext hy.symm
      apply Subtype.ext
      change (H.map (t,⟨q.val,hqF⟩)).val = ((A i).map (t,⟨q,hqK⟩)).val.val
      rw [hreg,harg]
      exact (hinner i t u).symm
    have hRC (i : frontierIndices σ) (t : Interval) (q : Q)
        (hqR : q ∈ R) (hqK : q ∈ Set.range (K i)) :
        fi i ⟨(t,q),hqK⟩ = fR ⟨(t,q),hqR⟩ := by
      have hqKcopy := hqK
      obtain ⟨⟨s,u⟩,hy⟩ := hqKcopy
      have hs : s = 1 := hRestOuter i (s,u) (by rw [hy]; exact hqR)
      subst s
      have harg : (⟨q,hqK⟩ : ↥(Set.range (K i))) =
          ⟨K i (1,u),Set.mem_range_self _⟩ := Subtype.ext hy.symm
      change ((A i).map (t,⟨q,hqK⟩)).val = q
      rw [harg,houter]
      exact hy
    let C : Option (Option (frontierIndices σ)) → Set Q := fun
      | none => FQ
      | some none => R
      | some (some i) => Set.range (K i)
    let P : Option (Option (frontierIndices σ)) → Set (Interval × Q) :=
      fun j => Prod.snd ⁻¹' C j
    let φ : ∀ j, C(P j,Q) := fun
      | none => f0
      | some none => fR
      | some (some i) => fi i
    have hagree : ∀ i j z (hi : z ∈ P i) (hj : z ∈ P j),
        φ i ⟨z,hi⟩ = φ j ⟨z,hj⟩ := by
      intro i j z hi hj
      rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j)
      · rfl
      · exact False.elim (hj (hFinside hi))
      · exact hFC j z.1 z.2 hi hj
      · exact False.elim (hi (hFinside hj))
      · rfl
      · exact (hRC j z.1 z.2 hi hj).symm
      · exact (hFC i z.1 z.2 hj hi).symm
      · exact hRC i z.1 z.2 hj hi
      · by_cases hij : i = j
        · subst j
          rfl
        · exact False.elim (Set.disjoint_left.mp (hdK i j hij) hi hj)
    have hCcover (q : Q) : ∃ j, q ∈ C j := by
      by_cases hq : q ∈ FQ
      · exact ⟨none,hq⟩
      · by_cases hk : q ∈ ⋃ i, Set.range (K i)
        · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hk
          exact ⟨some (some i),hi⟩
        · refine ⟨some none,?_⟩
          intro hi
          rcases interior_subset hi with hF | hK
          · exact hq hF
          · exact hk hK
    have hcover : ⋃ j, P j = Set.univ :=
      Set.iUnion_eq_univ_iff.mpr (fun z => hCcover z.2)
    have hclosed : ∀ j, IsClosed (P j) := by
      intro j
      rcases j with _ | (_ | i)
      · exact ((hborderedRegion σ).1.isClosed.preimage continuous_subtype_val).preimage continuous_snd
      · exact isOpen_interior.isClosed_compl.preimage continuous_snd
      · exact (isCompact_range (K i).continuous).isClosed.preimage continuous_snd
    let f : Interval × Q → Q := Set.liftCover P (fun j => φ j) hagree hcover
    have hf : Continuous f := by
      apply (locallyFinite_of_finite P).continuous hcover hclosed
      intro j
      rw [continuousOn_iff_continuous_domRestrict]
      change Continuous (fun z : P j => f z.val)
      have he : (fun z : P j => f z.val) = φ j := funext (fun z => Set.liftCover_coe z)
      rw [he]
      exact (φ j).continuous
    let G : C(Interval × Q,Q) := ⟨f,hf⟩
    have hreg (t : Interval) (y : ↥(borderedRegion σ)) :
        G (t,regionInQ σ y) = regionInQ σ (H.map (t,y)) := by
      have hh := Set.liftCover_of_mem (S := P) (f := fun j => φ j)
        (hf := hagree) (hS := hcover) (i := none) (x := (t,regionInQ σ y)) y.property
      exact hh
    have hcollar (i : frontierIndices σ) (t : Interval) (q : ↥(Set.range (K i))) :
        G (t,q.val) = ((A i).map (t,q)).val := by
      exact Set.liftCover_of_mem (S := P) (f := fun j => φ j)
        (hf := hagree) (hS := hcover) (i := some (some i)) q.property
    have hrest (t : Interval) (q : Q) (hq : q ∈ R) : G (t,q) = q := by
      exact Set.liftCover_of_mem (S := P) (f := fun j => φ j)
        (hf := hagree) (hS := hcover) (i := some none) hq
    refine ⟨G,hreg,hcollar,hrest,?_⟩
    intro q
    obtain ⟨j,hj⟩ := hCcover q
    rcases j with _ | (_ | i)
    · let y : ↥(borderedRegion σ) := ⟨q.val,hj⟩
      have he : regionInQ σ y = q := Subtype.ext rfl
      rw [← he,hreg,H.at_zero]
    · exact hrest ⟨0,by norm_num⟩ q hj
    · have hh := hcollar i ⟨0,by norm_num⟩ ⟨q,hj⟩
      rw [(A i).at_zero] at hh
      exact hh
  have hIntrinsicFrontierCircleIff (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (H : AmbientIsotopy ↥(borderedRegion σ))
      (hbase : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
        {y | y.val ∈ boundaryCircle})
      (hfull : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier (borderedRegion σ)} =
        {y | y.val ∈ frontier (borderedRegion σ)})
      (i : frontierIndices σ) (t : Interval) (z : ↥(borderedRegion σ)) :
      (H.map (t,z)).val ∈ (frontierCurves σ i).val.image ↔
        z.val ∈ (frontierCurves σ i).val.image := by
    constructor
    · intro hh
      have ht : H.map (t,z) ∈ {y | y.val ∈ (frontierCurves σ i).val.image} := hh
      rw [← hfrontierIsotopyCircleImage σ hz H hbase hfull i t] at ht
      obtain ⟨y,hy,heq⟩ := ht
      change H.map (t,y) = H.map (t,z) at heq
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      have hyz : y = z := e.injective ((he y).trans (heq.trans (he z).symm))
      exact hyz ▸ hy
    · intro hzΓ
      exact hfrontierIsotopyComponent σ hz H hbase hfull i z hzΓ t
  have hActualCollarInnerPreserved (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (H : AmbientIsotopy ↥(borderedRegion σ))
      (hbase : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
        {y | y.val ∈ boundaryCircle})
      (hfull : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier (borderedRegion σ)} =
        {y | y.val ∈ frontier (borderedRegion σ)})
      (i : frontierIndices σ) (L : C(Interval × Circle,Q))
      (hzero : ∀ u, (L (0,u)).val = (frontierCurves σ i).val.map u)
      (hout : ∀ y, (L y).val ∈ borderedRegion σ ↔ y.1 = 0)
      (A : AmbientIsotopy ↥(Set.range L)) (c : C(Circle,↥(borderedRegion σ)))
      (hc : ∀ u, (c u).val = (frontierCurves σ i).val.map u)
      (hinner : ∀ t u, (A.map (t,⟨L (0,u),Set.mem_range_self _⟩)).val.val =
        (H.map (t,c u)).val) :
      ∀ t q, (A.map (t,q)).val.val ∈ borderedRegion σ ↔ q.val.val ∈ borderedRegion σ := by
    intro t q
    constructor
    · intro haq
      obtain ⟨⟨s,u⟩,hy⟩ := (A.map (t,q)).property
      have hys : (L (s,u)).val ∈ borderedRegion σ := by
        rw [congrArg Subtype.val hy]
        exact haq
      have hs : s = 0 := (hout (s,u)).mp hys
      subst s
      have hqA : (A.map (t,q)).val.val = (frontierCurves σ i).val.map u :=
        (congrArg Subtype.val hy).symm.trans (hzero u)
      have htarg : c u ∈ {y | y.val ∈ (frontierCurves σ i).val.image} :=
        ⟨u,(hc u).symm⟩
      rw [← hfrontierIsotopyCircleImage σ hz H hbase hfull i t] at htarg
      obtain ⟨z,hzΓ,hHz⟩ := htarg
      change H.map (t,z) = c u at hHz
      obtain ⟨v,hv⟩ := hzΓ
      have hcv : c v = z := Subtype.ext ((hc v).trans hv)
      have hvA : (A.map (t,⟨L (0,v),Set.mem_range_self _⟩)).val.val =
          (frontierCurves σ i).val.map u := by
        rw [hinner,hcv,hHz,hc]
      have haeq : A.map (t,q) = A.map (t,⟨L (0,v),Set.mem_range_self _⟩) :=
        Subtype.ext (Subtype.ext (hqA.trans hvA.symm))
      obtain ⟨e,he⟩ := A.homeomorphism_at t
      have hqv : q = ⟨L (0,v),Set.mem_range_self _⟩ :=
        e.injective ((he q).trans (haeq.trans (he _).symm))
      rw [hqv]
      exact (hout (0,v)).mpr rfl
    · intro hq
      obtain ⟨⟨s,u⟩,hy⟩ := q.property
      have hys : (L (s,u)).val ∈ borderedRegion σ := by
        rw [congrArg Subtype.val hy]
        exact hq
      have hs : s = 0 := (hout (s,u)).mp hys
      subst s
      have hqu : q = ⟨L (0,u),Set.mem_range_self _⟩ := Subtype.ext hy.symm
      rw [hqu]
      have hh := (H.map (t,c u)).property
      rw [← hinner t u] at hh
      exact hh
  have hActualWholeQIsotopyExtension (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (H : AmbientIsotopy ↥(borderedRegion σ))
      (hbase : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
        {y | y.val ∈ boundaryCircle})
      (hfull : ∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier (borderedRegion σ)} =
        {y | y.val ∈ frontier (borderedRegion σ)}) :
      ∃ E : AmbientIsotopy Q,
        (∀ t y, E.map (t,regionInQ σ y) = regionInQ σ (H.map (t,y))) ∧
        ∀ t, (fun q => E.map (t,q)) '' boundaryQ = boundaryQ := by
    obtain ⟨K,A,c,hK,hdK,hc,hinner,houter⟩ :=
      hActualCoherentExteriorCollarMotions σ hz H hbase hfull
    obtain ⟨G,hreg,hcol,hrest,hzero⟩ :=
      hActualJointMotionPasting σ hz K hK hdK H A c hc hinner houter
    obtain ⟨hFinside,hRestOuter⟩ := hActualCollarSeamCover σ hz K hK
    let FQ : Set Q := {q | q.val ∈ borderedRegion σ}
    let T : Set Q := FQ ∪ ⋃ i, Set.range (K i)
    let R : Set Q := (interior T)ᶜ
    have hchoice (q : Q) : q ∈ FQ ∨ (∃ i, q ∈ Set.range (K i)) ∨ q ∈ R := by
      by_cases hf : q ∈ FQ
      · exact Or.inl hf
      · right
        by_cases hk : ∃ i, q ∈ Set.range (K i)
        · exact Or.inl hk
        · right
          intro hi
          rcases interior_subset hi with hF | hK
          · exact hf hF
          · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hK
            exact hk ⟨i,hi⟩
    have hInner (i : frontierIndices σ) :=
      hActualCollarInnerPreserved σ hz H hbase hfull i (K i)
        (hK i).2.1 (hK i).2.2.1 (A i) (c i) (hc i) (hinner i)
    have hRegion (t : Interval) (q : Q) : G (t,q) ∈ FQ ↔ q ∈ FQ := by
      rcases hchoice q with hF | (⟨i,hqK⟩ | hR)
      · have he : regionInQ σ (⟨q.val,hF⟩ : ↥(borderedRegion σ)) = q := Subtype.ext rfl
        constructor
        · intro _
          exact hF
        · intro _
          rw [← he,hreg]
          exact (H.map (t,⟨q.val,hF⟩)).property
      · change (G (t,q)).val ∈ borderedRegion σ ↔ q.val ∈ borderedRegion σ
        rw [hcol i t ⟨q,hqK⟩]
        exact hInner i t ⟨q,hqK⟩
      · rw [hrest t q hR]
    have hCollar (i : frontierIndices σ) (t : Interval) (q : Q) :
        G (t,q) ∈ Set.range (K i) ↔ q ∈ Set.range (K i) := by
      constructor
      · intro htK
        rcases hchoice q with hF | (⟨j,hqJ⟩ | hR)
        · let z : ↥(borderedRegion σ) := ⟨q.val,hF⟩
          have he : regionInQ σ z = q := Subtype.ext rfl
          have hGq : G (t,q) = regionInQ σ (H.map (t,z)) := by rw [← he,hreg]
          have hGF : G (t,q) ∈ FQ := (hRegion t q).mpr hF
          obtain ⟨⟨s,u⟩,hy⟩ := htK
          have hyF : (K i (s,u)).val ∈ borderedRegion σ := by
            rw [congrArg Subtype.val hy]
            exact hGF
          have hs : s = 0 := ((hK i).2.2.1 (s,u)).mp hyF
          subst s
          have hHΓ : (H.map (t,z)).val ∈ (frontierCurves σ i).val.image :=
            ⟨u,((hK i).2.1 u).symm.trans
              ((congrArg Subtype.val hy).trans (congrArg Subtype.val hGq))⟩
          have hzΓ := (hIntrinsicFrontierCircleIff σ hz H hbase hfull i t z).mp hHΓ
          obtain ⟨v,hv⟩ := hzΓ
          exact ⟨(0,v),Subtype.ext (((hK i).2.1 v).trans hv)⟩
        · by_cases hji : j = i
          · exact hji ▸ hqJ
          · have hGJ : G (t,q) ∈ Set.range (K j) := by
              rw [hcol j t ⟨q,hqJ⟩]
              exact ((A j).map (t,⟨q,hqJ⟩)).property
            exact False.elim (Set.disjoint_left.mp (hdK j i hji) hGJ htK)
        · rw [hrest t q hR] at htK
          exact htK
      · intro hqK
        rw [hcol i t ⟨q,hqK⟩]
        exact ((A i).map (t,⟨q,hqK⟩)).property
    have hRest (t : Interval) (q : Q) : G (t,q) ∈ R ↔ q ∈ R := by
      constructor
      · intro hGR
        rcases hchoice q with hF | (⟨i,hqK⟩ | hR)
        · exact False.elim (hGR (hFinside ((hRegion t q).mpr hF)))
        · have hGK : G (t,q) ∈ Set.range (K i) := (hCollar i t q).mpr hqK
          obtain ⟨⟨s,u⟩,hy⟩ := hGK
          have hs : s = 1 := hRestOuter i (s,u) (by rw [hy]; exact hGR)
          subst s
          let qi : ↥(Set.range (K i)) := ⟨q,hqK⟩
          let qo : ↥(Set.range (K i)) := ⟨K i (1,u),Set.mem_range_self _⟩
          have hAq : (A i).map (t,qi) = qo :=
            Subtype.ext ((hcol i t qi).symm.trans hy.symm)
          have hAo : (A i).map (t,qo) = qo := Subtype.ext (houter i t u)
          obtain ⟨e,he⟩ := (A i).homeomorphism_at t
          have hqi : qi = qo := e.injective
            ((he qi).trans (hAq.trans (hAo.symm.trans (he qo).symm)))
          have hqG : q = G (t,q) := (congrArg Subtype.val hqi).trans hy
          rw [hqG]
          exact hGR
        · exact hR
      · intro hR
        rw [hrest t q hR]
        exact hR
    have hsur (t : Interval) : Function.Surjective (fun q => G (t,q)) := by
      intro q
      rcases hchoice q with hF | (⟨i,hqK⟩ | hR)
      · let z : ↥(borderedRegion σ) := ⟨q.val,hF⟩
        obtain ⟨e,he⟩ := H.homeomorphism_at t
        refine ⟨regionInQ σ (e.symm z),?_⟩
        change G (t,regionInQ σ (e.symm z)) = q
        rw [hreg,← he,e.apply_symm_apply]
        exact Subtype.ext rfl
      · obtain ⟨e,he⟩ := (A i).homeomorphism_at t
        let z : ↥(Set.range (K i)) := ⟨q,hqK⟩
        refine ⟨(e.symm z).val,?_⟩
        change G (t,(e.symm z).val) = q
        rw [hcol,← he,e.apply_symm_apply]
      · exact ⟨q,hrest t q hR⟩
    have hinj (t : Interval) : Function.Injective (fun q => G (t,q)) := by
      intro q source_r heq
      change G (t,q) = G (t,source_r) at heq
      rcases hchoice source_r with hF | (⟨i,hrK⟩ | hR)
      · have hrGF : G (t,source_r) ∈ FQ := (hRegion t source_r).mpr hF
        have hqF : q ∈ FQ := (hRegion t q).mp (heq.symm ▸ hrGF)
        let zq : ↥(borderedRegion σ) := ⟨q.val,hqF⟩
        let zr : ↥(borderedRegion σ) := ⟨source_r.val,hF⟩
        have hq : regionInQ σ zq = q := Subtype.ext rfl
        have source_hr : regionInQ σ zr = source_r := Subtype.ext rfl
        have hmaps : H.map (t,zq) = H.map (t,zr) := by
          apply (hregionInQEmbedding σ).injective
          rw [← hreg,← hreg,hq,source_hr]
          exact heq
        obtain ⟨e,he⟩ := H.homeomorphism_at t
        have hz : zq = zr := e.injective ((he zq).trans (hmaps.trans (he zr).symm))
        have hzval : q.val = source_r.val := congrArg (fun y : ↥(borderedRegion σ) => y.val) hz
        exact Subtype.ext hzval
      · have hqK : q ∈ Set.range (K i) := (hCollar i t q).mp
          (heq.symm ▸ (hCollar i t source_r).mpr hrK)
        let zq : ↥(Set.range (K i)) := ⟨q,hqK⟩
        let zr : ↥(Set.range (K i)) := ⟨source_r,hrK⟩
        have hmaps : (A i).map (t,zq) = (A i).map (t,zr) := by
          apply Subtype.ext
          exact (hcol i t zq).symm.trans (heq.trans (hcol i t zr))
        obtain ⟨e,he⟩ := (A i).homeomorphism_at t
        have hz : zq = zr := e.injective ((he zq).trans (hmaps.trans (he zr).symm))
        exact congrArg Subtype.val hz
      · have hqR : q ∈ R := (hRest t q).mp (heq.symm ▸ (hRest t source_r).mpr hR)
        exact (hrest t q hqR).symm.trans (heq.trans (hrest t source_r hR))
    have hhomeo (t : Interval) : ∃ e : Q ≃ₜ Q, ∀ q, e q = G (t,q) := by
      let e := (G.continuous.comp (continuous_const.prodMk continuous_id)).homeoOfEquivCompactToT2
        (f := Equiv.ofBijective (fun q => G (t,q)) ⟨hinj t,hsur t⟩)
      exact ⟨e,fun q => rfl⟩
    let E : AmbientIsotopy Q := {map := G,homeomorphism_at := hhomeo,at_zero := hzero}
    refine ⟨E,hreg,?_⟩
    intro t
    ext q
    constructor
    · rintro ⟨z,hz,heq⟩
      have hzF : z ∈ FQ := interior_subset (hregionBoundaryRelativeInterior σ hz)
      let y : ↥(borderedRegion σ) := ⟨z.val,hzF⟩
      have he : regionInQ σ y = z := Subtype.ext rfl
      have hHy : H.map (t,y) ∈ {y | y.val ∈ boundaryCircle} := by
        rw [← hbase t]
        exact ⟨y,hz,rfl⟩
      rw [← heq]
      change (G (t,z)).val ∈ boundaryCircle
      rw [← he,hreg]
      exact hHy
    · intro hq
      have hqF : q ∈ FQ := interior_subset (hregionBoundaryRelativeInterior σ hq)
      let y : ↥(borderedRegion σ) := ⟨q.val,hqF⟩
      have hy : y ∈ {y | y.val ∈ boundaryCircle} := hq
      rw [← hbase t] at hy
      obtain ⟨z,hz,hzq⟩ := hy
      change H.map (t,z) = y at hzq
      refine ⟨regionInQ σ z,hz,?_⟩
      change G (t,regionInQ σ z) = q
      rw [hreg,hzq]
      exact Subtype.ext rfl
  have hIntrinsicRelationClassTransport (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (a b : EssentialProperArc) (ra rb : IntrinsicEssentialArc σ)
      (ha : (regionInQ σ).comp ra.val.val = a.val.val)
      (hb : (regionInQ σ).comp rb.val.val = b.val.val)
      (hrel : intrinsicArcRel σ ra rb) :
      arcRel a b ∧ Quot.mk arcRel a = Quot.mk arcRel b := by
    obtain ⟨H,hbase,hfull,hfinal⟩ := hrel
    obtain ⟨E,hE,hboundary⟩ := hActualWholeQIsotopyExtension σ hz H hbase hfull
    have hcomm : E.finalMap ∘ regionInQ σ = (regionInQ σ) ∘ H.finalMap := by
      funext y
      exact hE ⟨1,by norm_num⟩ y
    have hrangea : Set.range a.val.val = (regionInQ σ) '' Set.range ra.val.val := by
      rw [← ha]
      change Set.range ((regionInQ σ) ∘ ra.val.val) = _
      rw [Set.range_comp]
    have hrangeb : Set.range b.val.val = (regionInQ σ) '' Set.range rb.val.val := by
      rw [← hb]
      change Set.range ((regionInQ σ) ∘ rb.val.val) = _
      rw [Set.range_comp]
    have hfinalQ : E.finalMap '' Set.range a.val.val = Set.range b.val.val := by
      rw [hrangea,← Set.image_comp,hcomm,Set.image_comp,hfinal,hrangeb]
    have hrelQ : arcRel a b := ⟨E,hboundary,hfinalQ⟩
    exact ⟨hrelQ,Quot.sound hrelQ⟩
  have hActualEssentialCurveDiskAvoidance (b : EssentialCurve S)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
      (hd : Topology.IsEmbedding d)
      (hb : Disjoint b.val.image
        (d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1})) :
      Disjoint b.val.image (Set.range d) := by
    let K : Set S := Set.range d
    let U : Set S := interior K
    have hKc : IsClosed K := (isCompact_range d.continuous).isClosed
    have hKI : ∀ y ∈ K, y ∉ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} →
        y ∈ U := by
      rintro y ⟨z,rfl⟩ hn
      change d z ∈ interior (Set.range d)
      rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd]
      have hdist : dist z.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 := z.property
      have hlt : dist z.val (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
        apply lt_of_le_of_ne hdist
        intro he
        exact hn ⟨z,he,rfl⟩
      exact ⟨z,hlt,rfl⟩
    apply Set.disjoint_left.mpr
    intro y hyb hyd
    have hyU : y ∈ U := hKI y hyd (fun hbdy => Set.disjoint_left.mp hb hyb hbdy)
    have hcurveU : b.val.image ⊆ U := by
      apply (isConnected_range b.val.embedded.continuous).isPreconnected.subset_of_closure_inter_subset
        isOpen_interior ⟨y,hyb,hyU⟩
      intro z hz
      have hzK : z ∈ K := closure_minimal interior_subset hKc hz.1
      exact hKI z hzK (fun hbdy => Set.disjoint_left.mp hb hz.2 hbdy)
    obtain ⟨e,he,hboundary,hsub⟩ := CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
      b.val d hd (hcurveU.trans interior_subset)
    exact b.property ⟨e,he,hboundary⟩
  have hActualEmbeddedDiskInteriorData
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
      (hd : Topology.IsEmbedding d) :
      IsPreconnected (interior (Set.range d)) ∧
        closure (interior (Set.range d)) = Set.range d := by
    let Plane := EuclideanSpace ℝ (Fin 2)
    let B0 : Set (Metric.closedBall (0 : Plane) 1) := {z | z.val ∈ Metric.ball (0 : Plane) 1}
    have hIm : Subtype.val '' B0 = Metric.ball (0 : Plane) 1 := by
      ext z
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact hu
      · intro hz
        exact ⟨⟨z,Metric.ball_subset_closedBall hz⟩,hz,rfl⟩
    have hB0cl : closure B0 = Set.univ := by
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image B0,hIm,
        closure_ball (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)]
      ext z
      exact iff_of_true z.property (Set.mem_univ z)
    let j : C(Metric.ball (0 : Plane) 1,Metric.closedBall (0 : Plane) 1) :=
      ⟨fun z => ⟨z.val,Metric.ball_subset_closedBall z.property⟩,continuous_subtype_val.subtype_mk _⟩
    have hj : Set.range j = B0 := by
      ext z
      constructor
      · rintro ⟨u,rfl⟩
        exact u.property
      · intro hz
        exact ⟨⟨z.val,hz⟩,Subtype.ext rfl⟩
    letI : ConnectedSpace (Metric.ball (0 : Plane) 1) :=
      Subtype.connectedSpace (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1))
    have hrange : Set.range (d.comp j) = interior (Set.range d) := by
      change Set.range (d ∘ j) = _
      rw [Set.range_comp,hj,CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd]
    refine ⟨hrange ▸ (isConnected_range (d.comp j).continuous).isPreconnected,?_⟩
    rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd]
    change closure (d '' B0) = Set.range d
    rw [(d.continuous.isClosedEmbedding hd.injective).closure_image_eq B0,hB0cl,Set.image_univ]
  have hActualFrontierBaseDisjoint (σ : Finset ↥Fv) (i : frontierIndices σ) :
      Disjoint (frontierCurves σ i).val.image boundaryCircle := by
    apply Set.disjoint_left.mpr
    intro y hyΓ hyB
    obtain ⟨w,hw,hclass,hcb⟩ := hfrontierBandWitness σ i
    exact ((hfiniteBands w).2.2.2.2.1 (hcb hyΓ))
      ((Set.image_mono Metric.sphere_subset_closedBall) hyB)
  have hActualRegionArcAvoidsEssentialFrontier (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (a : RegionProperArc σ) (i : frontierIndices σ) :
      ∀ t, (a.val t).val ∉ (frontierCurves σ i).val.image := by
    intro t htΓ
    by_cases ht0 : (t:ℝ) = 0
    · have he : t = ⟨0,by norm_num⟩ := Subtype.ext ht0
      subst t
      exact Set.disjoint_left.mp (hActualFrontierBaseDisjoint σ i) htΓ a.property.2.1
    · by_cases ht1 : (t:ℝ) = 1
      · have he : t = ⟨1,by norm_num⟩ := Subtype.ext ht1
        subst t
        exact Set.disjoint_left.mp (hActualFrontierBaseDisjoint σ i) htΓ a.property.2.2.1
      · have htI : t ∈ Set.Ioo (0 : Interval) 1 := by
          constructor
          · change (0:ℝ) < (t:ℝ)
            exact lt_of_le_of_ne t.property.1 (fun he => ht0 he.symm)
          · change (t:ℝ) < (1:ℝ)
            exact lt_of_le_of_ne t.property.2 ht1
        apply a.property.2.2.2 t htI
        exact (Set.ext_iff.mp (hfrontierFamilyExact σ hz) ((a.val t).val)).mpr
          (Or.inr (Set.mem_iUnion.mpr ⟨i,htΓ⟩))
  have hActualRegionBoundaryDiskContainment (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (a : RegionProperArc σ) (b : C(Interval,Q))
      (hb : ∀ t, b t ∈ boundaryQ)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q))
      (hd : Topology.IsEmbedding d)
      (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range ((regionInQ σ).comp a.val) ∪ Set.range b) :
      ∀ z, (d z).val ∈ borderedRegion σ := by
    let ds : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
      ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
    have hds : Topology.IsEmbedding ds := Topology.IsEmbedding.subtypeVal.comp hd
    have hΓdisk (i : frontierIndices σ) : Disjoint (frontierCurves σ i).val.image (Set.range ds) := by
      apply hActualEssentialCurveDiskAvoidance (frontierCurves σ i) ds hds
      apply Set.disjoint_left.mpr
      rintro y hyΓ ⟨z,hzbdy,hy⟩
      have hzb : d z ∈ Set.range ((regionInQ σ).comp a.val) ∪ Set.range b := by
        rw [← hboundary]
        exact ⟨z,hzbdy,rfl⟩
      rcases hzb with ha | hb'
      · obtain ⟨t,ht⟩ := ha
        apply hActualRegionArcAvoidsEssentialFrontier σ hz a i t
        change (((regionInQ σ).comp a.val) t).val ∈ (frontierCurves σ i).val.image
        rw [ht]
        change ds z ∈ (frontierCurves σ i).val.image
        rw [hy]
        exact hyΓ
      · obtain ⟨t,ht⟩ := hb'
        have hyB : y ∈ boundaryCircle := by
          rw [← hy]
          change (d z).val ∈ boundaryCircle
          rw [← ht]
          exact hb t
        exact Set.disjoint_left.mp (hActualFrontierBaseDisjoint σ i) hyΓ hyB
    let U : Set S := interior (Set.range ds)
    obtain ⟨hUpre,hUclosure⟩ := hActualEmbeddedDiskInteriorData ds hds
    have hUQ : U ⊆ interior Oᶜ := by
      apply interior_maximal _ isOpen_interior
      intro y hy
      obtain ⟨z,hz⟩ := interior_subset hy
      exact hz ▸ (show ds z ∈ Oᶜ from (d z).property)
    have hUoff : Disjoint U (frontier (borderedRegion σ)) := by
      apply Set.disjoint_left.mpr
      intro y hyU hyF
      rw [hfrontierFamilyExact σ hz] at hyF
      rcases hyF with hyB | hyΓ
      · have hyFO : y ∈ frontier Oᶜ := by rw [frontier_compl,hfrontierO]; exact hyB
        exact Set.disjoint_left.mp disjoint_interior_frontier (hUQ hyU) hyFO
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hyΓ
        exact Set.disjoint_left.mp (hΓdisk i) hi (interior_subset hyU)
    let tm : Interval := ⟨1/2,by norm_num⟩
    let y : S := (a.val tm).val
    have hyI : y ∈ interior (borderedRegion σ) := by
      by_contra hn
      have hf : y ∈ frontier (borderedRegion σ) :=
        (mem_frontier_iff_notMem_interior (a.val tm).property).mpr hn
      have htm : tm ∈ Set.Ioo (0 : Interval) 1 := by
        constructor
        · change (0 : ℝ) < 1/2
          norm_num
        · change (1/2 : ℝ) < 1
          norm_num
      exact a.property.2.2.2 tm htm hf
    have hyD : y ∈ Set.range ds := by
      have hya : ((regionInQ σ).comp a.val) tm ∈
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
        rw [hboundary]
        exact Or.inl (Set.mem_range_self tm)
      obtain ⟨z,hz,he⟩ := hya
      exact ⟨z,congrArg Subtype.val he⟩
    have hycl : y ∈ closure U := hUclosure.symm ▸ hyD
    obtain ⟨w,hwF,hwU⟩ := mem_closure_iff.mp hycl _ isOpen_interior hyI
    have hUF : U ⊆ interior (borderedRegion σ) := by
      apply hUpre.subset_of_closure_inter_subset isOpen_interior ⟨w,hwU,hwF⟩
      intro z hz'
      have hzF : z ∈ borderedRegion σ :=
        closure_minimal interior_subset (hborderedRegion σ).1.isClosed hz'.1
      by_contra hn
      exact Set.disjoint_left.mp hUoff hz'.2 ((mem_frontier_iff_notMem_interior hzF).mpr hn)
    have hDF : Set.range ds ⊆ borderedRegion σ := by
      rw [← hUclosure]
      exact closure_minimal (hUF.trans interior_subset) (hborderedRegion σ).1.isClosed
    intro z
    exact hDF (Set.mem_range_self z)
  have hIntrinsicEssentialArcIncludes (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0)
      (a : IntrinsicEssentialArc σ) :
      ∃ qa : EssentialProperArc, qa.val.val = (regionInQ σ).comp a.val.val := by
    let qa : ProperArc := ⟨(regionInQ σ).comp a.val.val,
      (hregionInQEmbedding σ).comp a.val.property.1,
      a.val.property.2.1,a.val.property.2.2.1,by
        intro t ht hB
        apply a.val.property.2.2.2 t ht
        exact (Set.ext_iff.mp (hfrontierFamilyExact σ hz) ((a.val.val t).val)).mpr (Or.inl hB)⟩
    have hessential : ¬ boundaryParallel qa := by
      rintro ⟨b,hb,hb0,d,hd,hboundary⟩
      have hdb := hActualRegionBoundaryDiskContainment σ hz a.val b hb0 d hd hboundary
      have hbb (t : Interval) : (b t).val ∈ borderedRegion σ :=
        (hborderedRegion σ).2.2.1 (hb0 t)
      let br : C(Interval,↥(borderedRegion σ)) :=
        ⟨fun t => ⟨(b t).val,hbb t⟩,(continuous_subtype_val.comp b.continuous).subtype_mk _⟩
      let dr : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥(borderedRegion σ)) :=
        ⟨fun z => ⟨(d z).val,hdb z⟩,(continuous_subtype_val.comp d.continuous).subtype_mk _⟩
      have hbr : Topology.IsEmbedding br :=
        (Topology.IsEmbedding.subtypeVal.comp hb).codRestrict _ hbb
      have hdr : Topology.IsEmbedding dr :=
        (Topology.IsEmbedding.subtypeVal.comp hd).codRestrict _ hdb
      have hbr0 : ∀ t, (br t).val ∈ boundaryCircle := hb0
      have hboundaryR : dr '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range a.val.val ∪ Set.range br := by
        apply (Set.image_injective.mpr (hregionInQEmbedding σ).injective)
        rw [Set.image_union,← Set.range_comp,← Set.range_comp,← Set.image_comp]
        change d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range ((regionInQ σ).comp a.val.val) ∪ Set.range b
        exact hboundary
      exact a.property ⟨br,hbr,hbr0,dr,hdr,hboundaryR⟩
    exact ⟨⟨qa,hessential⟩,rfl⟩
  have hIntrinsicClassFaceMap (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0) :
      ∃ f : IntrinsicArcVertex σ → ArcVertex,
        (∀ a : IntrinsicEssentialArc σ, ∃ qa : EssentialProperArc,
          qa.val.val = (regionInQ σ).comp a.val.val ∧
          f (Quot.mk (intrinsicArcRel σ) a) = Quot.mk arcRel qa) ∧
        ∀ τ ∈ (intrinsicArcComplex σ).faces, τ.image f ∈ A.faces ∧
          regionArcSystem σ (τ.image f) := by
    choose included hIncluded using hIntrinsicEssentialArcIncludes σ hz
    have hrespect (a b : IntrinsicEssentialArc σ) (h : intrinsicArcRel σ a b) :
        Quot.mk arcRel (included a) = Quot.mk arcRel (included b) :=
      (hIntrinsicRelationClassTransport σ hz (included a) (included b) a b
        (hIncluded a).symm (hIncluded b).symm h).2
    let f : IntrinsicArcVertex σ → ArcVertex :=
      Quot.lift (fun a => Quot.mk arcRel (included a)) hrespect
    have hf (a : IntrinsicEssentialArc σ) :
        f (Quot.mk (intrinsicArcRel σ) a) = Quot.mk arcRel (included a) := rfl
    refine ⟨f,(fun a => ⟨included a,hIncluded a,hf a⟩),?_⟩
    intro τ hτ
    obtain ⟨hne,rep,hclass,hd⟩ := hτ
    let μ := τ.image f
    have hpre (u : ↥μ) : ∃ v : ↥τ, f v.val = u.val := by
      obtain ⟨v,hv,he⟩ := Finset.mem_image.mp u.property
      exact ⟨⟨v,hv⟩,he⟩
    choose pre hpre using hpre
    let qrep : ↥μ → EssentialProperArc := fun u => included (rep (pre u))
    have hsys : regionArcSystem σ μ := by
      refine ⟨Finset.image_nonempty.mpr hne,qrep,?_,?_,?_⟩
      · intro u
        change Quot.mk arcRel (included (rep (pre u))) = u.val
        rw [← hf,hclass,hpre]
      · intro u
        constructor
        · intro t
          have ht := ContinuousMap.congr_fun (hIncluded (rep (pre u))) t
          have hv := congrArg Subtype.val ht
          change ((qrep u).val.val t).val ∈ borderedRegion σ
          rw [hv]
          exact ((rep (pre u)).val.val t).property
        · intro t htI
          have ht := ContinuousMap.congr_fun (hIncluded (rep (pre u))) t
          have hv := congrArg Subtype.val ht
          change ((qrep u).val.val t).val ∉ frontier (borderedRegion σ)
          rw [hv]
          exact (rep (pre u)).val.property.2.2.2 t htI
      · intro u v huv
        have hpuv : pre u ≠ pre v := by
          intro he
          apply huv
          apply Subtype.ext
          exact (hpre u).symm.trans ((congrArg (fun z : ↥τ => f z.val) he).trans (hpre v))
        apply Set.disjoint_left.mpr
        rintro q ⟨t,ht⟩ ⟨s,hs⟩
        have het := ContinuousMap.congr_fun (hIncluded (rep (pre u))) t
        have hes := ContinuousMap.congr_fun (hIncluded (rep (pre v))) s
        have hregion : (rep (pre u)).val.val t = (rep (pre v)).val.val s := by
          apply (hregionInQEmbedding σ).injective
          exact het.symm.trans (ht.trans (hs.symm.trans hes))
        exact Set.disjoint_left.mp (hd (pre u) (pre v) hpuv)
          (Set.mem_range_self t) ⟨s,hregion.symm⟩
    exact ⟨hregionArcSystemFace σ μ hsys,hsys⟩
  have hActualIntrinsicFaceImageComparison (σ : Finset ↥Fv)
      (hz : ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0) :
      ∃ f : IntrinsicArcVertex σ → ArcVertex,
        (∀ a : IntrinsicEssentialArc σ, ∃ qa : EssentialProperArc,
          qa.val.val = (regionInQ σ).comp a.val.val ∧
          f (Quot.mk (intrinsicArcRel σ) a) = Quot.mk arcRel qa) ∧
        (∀ μ ∈ (intrinsicArcComplex σ).faces, μ.image f ∈ A.faces ∧
          regionArcSystem σ (μ.image f)) ∧
        ∀ τ, regionArcSystem σ τ ↔
          ∃ μ ∈ (intrinsicArcComplex σ).faces, μ.image f = τ := by
    obtain ⟨f,hdata,hforward⟩ := hIntrinsicClassFaceMap σ hz
    refine ⟨f,hdata,hforward,?_⟩
    intro τ
    constructor
    · intro hτ
      obtain ⟨μ,hμ,rep,brep,hclass,hinclude,hμdef⟩ := hregionArcSystemIntrinsicFace σ τ hτ
      have hclasses (u : ↥τ) : f (Quot.mk (intrinsicArcRel σ) (brep u)) = u.val := by
        obtain ⟨qa,hqa,hfqa⟩ := hdata (brep u)
        have hqr : qa = rep u := Subtype.ext (Subtype.ext (hqa.trans (hinclude u)))
        rw [hqr,hclass] at hfqa
        exact hfqa
      refine ⟨μ,hμ,?_⟩
      have hμf : μ.image f = (Finset.univ : Finset ↥τ).image Subtype.val := by
        rw [hμdef,Finset.image_image]
        congr 1
        funext u
        exact hclasses u
      rw [hμf]
      ext v
      simp only [Finset.mem_image,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨u,rfl⟩
        exact u.property
      · intro hv
        exact ⟨⟨v,hv⟩,rfl⟩
    · rintro ⟨μ,hμ,himage⟩
      exact himage ▸ (hforward μ hμ).2
  have hActualOriginalRegionalEssentialArcNonempty (σ : Finset ↥Fv) (hne : σ.Nonempty)
      (hz : ∀ i∈σ,∀ j∈σ,i≠j → geometricIntersection i.val j.val=0) :
      Nonempty (IntrinsicEssentialArc σ) := by
    letI : Nonempty (frontierIndices σ) := hfrontierFamilyNonempty σ hne hz
    have hbaseclear (i : frontierIndices σ) :
        Disjoint (frontierCurves σ i).val.image boundaryCircle := by
      apply Set.disjoint_left.mpr
      intro y hy hyB
      have hyD : y∈D := (Set.image_mono Metric.sphere_subset_closedBall) hyB
      rcases i with i | i
      · exact ((hfiniteBands i.val).2.2.2.2.1
          (hessentialSidesInBand i.val (Or.inl hy))) hyD
      · exact ((hfiniteBands i.val).2.2.2.2.1
          (hessentialSidesInBand i.val (Or.inr hy))) hyD
    obtain ⟨a,ha,h0,h1,hmid,hess⟩ :=
      source_actual_region_essential_proper_arc S g hg hS x R hR htarget
        (borderedRegion σ) (hborderedRegion σ).1 (hborderedRegion σ).2.1
        (hborderedRegion σ).2.2.1 (hborderedRegion σ).2.2.2.1
        (hborderedInteriorDense σ) (frontierIndices σ) (frontierCurves σ)
        (hfrontierFamilyDisjoint σ hz) hbaseclear (hfrontierFamilyExact σ hz)
    let ra : RegionProperArc σ := ⟨a,ha,h0,h1,hmid⟩
    exact ⟨⟨ra,hess⟩⟩
  have hrepInterior (w : ↥Fv) : (r w).val.image ⊆ interior (openDisk S x R)ᶜ := by
    intro y hy
    apply interior_maximal (compl_subset_compl.mpr hOD) hPopen
    exact Set.disjoint_right.mp (hchosenAvoid w) hy
  let frontierEquiv (σ : Finset ↥Fv) := Fintype.equivFin (frontierIndices σ)
  let G : ActualBorderedRegions S x R Fv := {
    representative := r
    representative_class := hr
    representative_disjoint := hzeroPosition
    representative_interior := hrepInterior
    region := borderedRegion
    compact := fun σ => (hborderedRegion σ).1
    connected := fun σ => (hborderedRegion σ).2.1
    contains_boundary := fun σ => (hborderedRegion σ).2.2.1
    outside := fun σ => (hborderedRegion σ).2.2.2.1
    regular_closed := hborderedInteriorDense
    boundary_on_frontier := hborderedBoundary
    antitone := fun σ τ hστ => hborderedRegionAntitone hστ
    avoids_original := hregionAvoidsOriginal
    frontierCount := fun σ => Fintype.card (frontierIndices σ)
    frontierCurve := fun σ i => frontierCurves σ ((frontierEquiv σ).symm i)
    frontier_disjoint := by
      intro σ hσ i j hij
      exact hfrontierFamilyDisjoint σ hσ _ _ (fun he => hij ((frontierEquiv σ).symm.injective he))
    frontier_boundary_disjoint := fun σ i => hActualFrontierBaseDisjoint σ ((frontierEquiv σ).symm i)
    frontier_exact := by
      intro σ hσ
      rw [hfrontierFamilyExact σ hσ]
      congr 1
      ext y
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i,hi⟩
        exact ⟨frontierEquiv σ i,by simpa only [Equiv.symm_apply_apply] using hi⟩
      · rintro ⟨i,hi⟩
        exact ⟨(frontierEquiv σ).symm i,hi⟩
    frontier_nonempty := by
      intro σ hne hσ
      letI : Nonempty (frontierIndices σ) := hfrontierFamilyNonempty σ hne hσ
      exact Fintype.card_pos }
  let comparisonClass (σ : Finset ↥Fv) (hσ : Compatible S Fv σ) :
      IntrinsicArcVertex σ → ArcVertex :=
    Classical.choose (hActualIntrinsicFaceImageComparison σ hσ)
  have hcomparison (σ : Finset ↥Fv) (hσ : Compatible S Fv σ) :=
    Classical.choose_spec (hActualIntrinsicFaceImageComparison σ hσ)
  let comparisonArc (σ : Finset ↥Fv) (hσ : Compatible S Fv σ)
      (a : IntrinsicEssentialArc σ) : EssentialProperArc :=
    Classical.choose ((hcomparison σ hσ).1 a)
  have hcomparisonArc (σ : Finset ↥Fv) (hσ : Compatible S Fv σ)
      (a : IntrinsicEssentialArc σ) :=
    Classical.choose_spec ((hcomparison σ hσ).1 a)
  let C : RegionalArcComparison S x R G := {
    complex := intrinsicArcComplex
    faces_exact := fun σ => rfl
    includedArc := comparisonArc
    included_literal := by
      intro σ hσ a t
      exact congrArg Subtype.val (ContinuousMap.congr_fun (hcomparisonArc σ hσ a).1 t)
    classMap := comparisonClass
    classMap_mk := fun σ hσ a => (hcomparisonArc σ hσ a).2
    faceMap := fun σ hσ μ hμ => (hcomparison σ hσ).2.1 μ hμ
    faceReflection := fun σ hσ τ => (hcomparison σ hσ).2.2 τ
    essential_restrict := by
      intro σ a hc hp
      obtain ⟨b,he,hb⟩ := hessentialArcRestricts σ a hc hp
      refine ⟨⟨b,hb⟩,?_⟩
      intro t
      exact congrArg Subtype.val (ContinuousMap.congr_fun he t)
    proper_monotone := by
      intro σ τ hστ a hproper
      exact hproperArcRegionMonotone hστ a hproper.1 hproper.2
    essential_nonempty := hActualOriginalRegionalEssentialArcNonempty }
  exact ⟨G,rfl,⟨C⟩⟩

theorem source_c0_finite_support_bordered_regions_and_arc_comparison_exists
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (Fv : Finset (Vertex S)) :
    ∃ (x : S) (R : ℝ), 0 < R ∧
      (Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) ∧
      ∃ G : ActualBorderedRegions S x R Fv,
        Nonempty (RegionalArcComparison S x R G) := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  letI : Nonempty S := hS.1
  have hfiniteComplement (F : Finset (Curve S)) :
      IsOpen (⋂ c ∈ F, c.imageᶜ) ∧ Dense (⋂ c ∈ F, c.imageᶜ) := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert c F hc ih =>
      have ho : IsOpen c.imageᶜ :=
        (isCompact_range c.embedded.continuous).isClosed.isOpen_compl
      simpa only [← Finset.mem_coe, Finset.coe_insert, Set.biInter_insert] using
        And.intro (ho.inter ih.1)
          ((source_curve_complement_dense c).inter_of_isOpen_left ih.2 ho)
  have hpunctureRegion (F : Finset (Curve S)) :
      ∃ (x : S) (U : Set S), IsOpen U ∧ x ∈ U ∧
        ∀ c ∈ F, Disjoint U c.image := by
    obtain ⟨x, hx⟩ := (hfiniteComplement F).2.nonempty
    refine ⟨x, ⋂ c ∈ F, c.imageᶜ, (hfiniteComplement F).1, hx, ?_⟩
    intro c hc
    apply Set.disjoint_left.mpr
    intro y hy hyc
    exact (Set.mem_iInter.mp (Set.mem_iInter.mp hy c) hc) hyc
  have hpunctureDisk (F : Finset (Curve S)) :
      ∃ (x : S) (R : ℝ), 0 < R ∧
        Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
          (chartAt (EuclideanSpace ℝ (Fin 2)) x).target ∧
        ∀ c ∈ F, Disjoint
          ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
            Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
          c.image := by
    obtain ⟨x, U, hU, hxU, hav⟩ := hpunctureRegion F
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
    obtain ⟨R, hR, ht, hD, _⟩ :=
      HyperellipticModel.coordinate_disk_inside x (U ∩ e.source)
        (hU.inter e.open_source) ⟨hxU, ChartedSpace.mem_chart_source x⟩
        Set.inter_subset_right
    refine ⟨x, R, hR, ht, ?_⟩
    intro c hc
    exact (hav c hc).mono_left (hD.trans Set.inter_subset_left)
  obtain ⟨r₀, hr₀, hminimal⟩ :=
    exists_finite_simultaneous_minimal_representatives S g hg hS Fv
  let r : ↥Fv → EssentialCurve S := fun w => r₀ w.val w.property
  have hr (w : ↥Fv) :
      Quotient.mk (essentialCurveSetoid S) (r w) = w.val :=
    hr₀ w.val w.property
  have hzeroPosition (u w : ↥Fv) (huw : u ≠ w)
      (hz : geometricIntersection u.val w.val = 0) :
      Disjoint (r u).val.image (r w).val.image := by
    have huv : u.val ≠ w.val := fun he => huw (Subtype.ext he)
    obtain ⟨ht, hc⟩ := hminimal u.val u.property w.val w.property huv
    have he : ht.1.toFinset = ∅ := Finset.card_eq_zero.mp (hc.trans hz)
    rw [Set.disjoint_left]
    intro y hyu hyw
    have hy : y ∈ ht.1.toFinset := ht.1.mem_toFinset.mpr ⟨hyu, hyw⟩
    simpa only [he, Finset.notMem_empty] using hy
  let Fc : Finset (Curve S) :=
    Finset.univ.image fun w : ↥Fv => (r w).val
  obtain ⟨x, R, hR, htarget, havoid⟩ := hpunctureDisk Fc
  have hchosenAvoid (w : ↥Fv) :
      Disjoint
        ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
        (r w).val.image := by
    exact havoid _ (Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩)
  -- Apply the exact paid prepared constructor to this original family and disk.
  have hprepared :
      ∀ (r' : ↥Fv → EssentialCurve S),
        (∀ w, Quotient.mk (essentialCurveSetoid S) (r' w) = w.val) →
        (∀ u w : ↥Fv, u ≠ w → geometricIntersection u.val w.val = 0 →
          Disjoint (r' u).val.image (r' w).val.image) →
        ∀ (x' : S) (R' : ℝ), 0 < R' →
          (Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x') x') R' ⊆
            (chartAt (EuclideanSpace ℝ (Fin 2)) x').target) →
          (∀ w : ↥Fv, Disjoint
            ((chartAt (EuclideanSpace ℝ (Fin 2)) x').symm ''
              Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x') x') R')
            (r' w).val.image) →
          ∃ G : ActualBorderedRegions S x' R' Fv,
            G.representative = r' ∧ Nonempty (RegionalArcComparison S x' R' G) := by
    exact source_c0_prepared_bordered_regions_and_arc_comparison_exists S g hg hS Fv
  obtain ⟨G, _hGr, hC⟩ := hprepared r hr hzeroPosition x R hR htarget hchosenAvoid
  exact ⟨x, R, hR, htarget, G, hC⟩

end CurveComplex.C0BoundaryCorrespondence.SourceConstructors
