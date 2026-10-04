import C0FaceCarrierEqualityExact
import OriginalThreeEssentialProperArcsShrinkingEssentialFrontierCollar
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.TerminalAnnulusMotionPROVED
import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2

open Set Topology CurveComplex
open scoped Manifold ContDiff
attribute [local instance] instDecidable_originalArcFaceCurveCarriers
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers
open OriginalBoundaryArc
variable (S : Type) [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (x : S) (R : ℝ)

theorem nonempty_small_faceCarrier_has_universal_curve
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (τ : Finset (ArcVertex S x R)) (hτ : τ ∈ (arcComplex S x R).faces)
    (hcard : τ.card ≤ 3) :
    ∃ c : EssentialCurve S,
      faceCarrier S x R τ (Quotient.mk (essentialCurveSetoid S) c) ∧
      ∀ v : Vertex S, faceCarrier S x R τ v →
        geometricIntersection (Quotient.mk (essentialCurveSetoid S) c) v = 0 := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  have hcompat {S : Type} [TopologicalSpace S] [T2Space S]
      (E : C(Interval × Circle, S))
      (hE : IsOpenEmbedding (fun z : Set.Ioo (0 : ℝ) 1 × Circle =>
        E (⟨z.1.val, ⟨z.1.property.1.le, z.1.property.2.le⟩⟩, z.2)))
      (c d : EssentialCurve S)
      (hc : c.val.image = Set.range (fun z => E (⟨1/2, by norm_num⟩, z)))
      (hd : ∀ z, E (0, z) ∉ d.val.image) :
      geometricIntersection (Quotient.mk (essentialCurveSetoid S) c)
        (Quotient.mk (essentialCurveSetoid S) d) = 0 := by
    let e : Set.Ioo (0 : ℝ) 1 × Circle → S := fun z =>
      E (⟨z.1.val, ⟨z.1.property.1.le,z.1.property.2.le⟩⟩,z.2)
    have hlevel (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
        IsEmbedding (fun z : Circle => E (⟨r,⟨hr0.le,hr1.le⟩⟩,z)) := by
      let f : Circle → Set.Ioo (0 : ℝ) 1 × Circle := fun z => (⟨r,hr0,hr1⟩,z)
      have hf : IsEmbedding f := ((continuous_const.prodMk continuous_id).isClosedEmbedding
        (fun z w he => congrArg Prod.snd he)).isEmbedding
      exact hE.isEmbedding.comp hf
    let level (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : Curve S :=
      ⟨fun z => E (⟨r,⟨hr0.le,hr1.le⟩⟩,z),hlevel r hr0 hr1⟩
    have hstep (r : ℝ) (hr0 : 0 < r) (hrh : r ≤ 1/2) :
        AmbientIsotopy.Rel (level (r*(2/3)) (by positivity) (by nlinarith)).image
          (level r hr0 (by linarith)).image := by
      let q : Interval → Set.Ioo (0 : ℝ) 1 := fun u =>
        ⟨r/3+r*u.val, by constructor <;> nlinarith [u.property.1,u.property.2]⟩
      have hqc : Continuous q := by fun_prop
      have hqi : Function.Injective q := by
        intro u v huv
        have h := congrArg Subtype.val huv
        dsimp [q] at h
        apply Subtype.ext
        nlinarith
      have hqe : IsEmbedding q := (hqc.isClosedEmbedding hqi).isEmbedding
      let B : Circle × Interval → S := fun z => e (q z.2,z.1)
      have hBe : IsEmbedding B := hE.isEmbedding.comp
        ((hqe.prodMap IsEmbedding.id).comp (Homeomorph.prodComm Circle Interval).isEmbedding)
      have himage : B '' (Set.univ ×ˢ Set.Ioo (0 : Interval) 1) =
          e '' ({w : Set.Ioo (0 : ℝ) 1 | r/3 < w.val ∧ w.val < 4*r/3} ×ˢ Set.univ) := by
        ext y
        constructor
        · rintro ⟨⟨z,u⟩,⟨_,hu0,hu1⟩,rfl⟩
          refine ⟨(q u,z),⟨?_,Set.mem_univ _⟩,rfl⟩
          dsimp [q]
          have h0 : (0:ℝ) < u.val := hu0
          have h1 : u.val < 1 := hu1
          constructor <;> nlinarith
        · rintro ⟨⟨w,z⟩,⟨⟨hw0,hw1⟩,_⟩,rfl⟩
          let u : Interval := ⟨(w.val-r/3)/r, by
            constructor
            · exact le_of_lt ((div_pos_iff).mpr (Or.inl ⟨by linarith,hr0⟩))
            · apply (div_le_iff₀ hr0).mpr
              linarith⟩
          refine ⟨(z,u),⟨Set.mem_univ _,?_,?_⟩,?_⟩
          · change (0:ℝ) < (w.val-r/3)/r
            exact div_pos (by linarith) hr0
          · change (w.val-r/3)/r < 1
            apply (div_lt_iff₀ hr0).mpr
            linarith
          · change e (q u,z) = e (w,z)
            congr 1
            refine Prod.ext ?_ rfl
            apply Subtype.ext
            dsimp [q,u]
            field_simp
            <;> ring
      have hBo : IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0 : Interval) 1)) := by
        rw [himage]
        apply hE.isOpenMap
        exact ((isOpen_lt continuous_const continuous_subtype_val).inter
          (isOpen_lt continuous_subtype_val continuous_const)).prod isOpen_univ
      have hfirst : Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩)) =
          (level (r*(2/3)) (by positivity) (by nlinarith)).image := by
        apply congrArg Set.range
        funext z
        change E (_,z) = E (_,z)
        congr 1
        refine Prod.ext ?_ rfl
        apply Subtype.ext
        dsimp [q]
        ring
      have hsecond : Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩)) =
          (level r hr0 (by linarith)).image := by
        apply congrArg Set.range
        funext z
        change E (_,z) = E (_,z)
        congr 1
        refine Prod.ext ?_ rfl
        apply Subtype.ext
        dsimp [q]
        ring
      obtain ⟨H,J,hH,_⟩ := G3Review.actual_collared_annulus_ambient_alignment
        (level (r*(2/3)) (by positivity) (by nlinarith))
        (level r hr0 (by linarith)) B hBe hfirst hsecond hBo
      exact ⟨H,hH⟩
    let r : ℕ → ℝ := fun n => (1/2)*(2/3)^n
    have hr0 (n : ℕ) : 0 < r n := by dsimp [r]; positivity
    have hrh (n : ℕ) : r n ≤ 1/2 := by
      have h := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 2/3)
        (by norm_num : (2/3:ℝ) ≤ 1) (n := n)
      dsimp [r]
      nlinarith
    have hr1 (n : ℕ) : r n < 1 := lt_of_le_of_lt (hrh n) (by norm_num)
    have hrc (n : ℕ) : AmbientIsotopy.Rel (level (r n) (hr0 n) (hr1 n)).image c.val.image := by
      induction n with
      | zero =>
        have himage : (level (r 0) (hr0 0) (hr1 0)).image = c.val.image := by
          simpa [r,level,Curve.image] using hc.symm
        rw [himage]
        exact ambientIsotopy_equivalence.refl _
      | succ n ih =>
        have he : r (n+1) = r n*(2/3) := by dsimp [r]; rw [pow_succ]; ring
        have hs := hstep (r n) (hr0 n) (hrh n)
        have hs' : AmbientIsotopy.Rel (level (r (n+1)) (hr0 (n+1)) (hr1 (n+1))).image
            (level (r n) (hr0 n) (hr1 n)).image := by simpa only [he] using hs
        exact ambientIsotopy_equivalence.trans hs' ih
    have hdc : IsClosed d.val.image := (isCompact_range d.val.embedded.continuous).isClosed
    obtain ⟨U,V,hU,hV,hzero,huniv,hUV⟩ := generalized_tube_lemma
      (isCompact_singleton (x := (0 : Interval))) (isCompact_univ (X := Circle))
      (hdc.isOpen_compl.preimage E.continuous)
      (show ({0} : Set Interval) ×ˢ (Set.univ : Set Circle) ⊆ E ⁻¹' d.val.imageᶜ by
        rintro ⟨t,z⟩ ⟨ht,_⟩
        have ht0 : t = 0 := Set.mem_singleton_iff.mp ht
        change E (t,z) ∉ d.val.image
        simpa only [ht0] using hd z)
    let rn (n : ℕ) : Interval := ⟨r n,⟨(hr0 n).le,(hr1 n).le⟩⟩
    have hrt : Filter.Tendsto r Filter.atTop (𝓝 0) := by
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num : (2/3:ℝ) < 1)
      simpa [r] using hp.const_mul (1/2 : ℝ)
    have hrnt : Filter.Tendsto rn Filter.atTop (𝓝 (0 : Interval)) :=
      tendsto_subtype_rng.mpr hrt
    have hev : ∀ᶠ n in Filter.atTop, rn n ∈ U := hrnt (hU.mem_nhds (hzero (Set.mem_singleton _)))
    obtain ⟨n,hn⟩ := Filter.Eventually.exists hev
    let cn : EssentialCurve S := ⟨level (r n) (hr0 n) (hr1 n),
      (essential_isotopy_invariant (hrc n)).mpr c.property⟩
    have hdis : Disjoint cn.val.image d.val.image := by
      apply Set.disjoint_left.mpr
      rintro y ⟨z,rfl⟩ hy
      exact hUV ⟨hn,huniv (Set.mem_univ z)⟩ hy
    have hclass : Quotient.mk (essentialCurveSetoid S) cn =
        Quotient.mk (essentialCurveSetoid S) c := Quotient.sound (hrc n)
    rw [← hclass]
    exact geometricIntersection_eq_zero_of_disjoint_representatives cn d hdis
  obtain ⟨hτne, ⟨r⟩⟩ := (simultaneousRepresentatives_face_iff S x R τ).mp hτ
  have hn : 0 < τ.card := Finset.card_pos.mpr hτne
  let e : Fin τ.card ≃ ↥τ := (Fintype.equivFinOfCardEq (Fintype.card_coe τ)).symm
  let a : Fin τ.card → C(Interval, Q S x R) := fun i => (r.arc (e i)).val.val
  have hemb : ∀ i, IsEmbedding (a i) := fun i => (r.arc (e i)).val.property.1
  have hend : ∀ i, (a i 0).val ∈ boundaryCircle S x R ∧
      (a i 1).val ∈ boundaryCircle S x R :=
    fun i => ⟨(r.arc (e i)).val.property.2.1, (r.arc (e i)).val.property.2.2.1⟩
  have hint : ∀ i t, t ∈ Set.Ioo (0 : Interval) 1 → (a i t).val ∉ boundaryCircle S x R :=
    fun i => (r.arc (e i)).val.property.2.2.2
  have hpair : ∀ i j, i ≠ j → Disjoint (Set.range (a i)) (Set.range (a j)) := by
    intro i j hij
    exact r.disjoint (e i) (e j) (fun h => hij (e.injective h))
  have hess : ∀ i, ¬ ∃ b : C(Interval, Q S x R), IsEmbedding b ∧
      (∀ t, (b t).val ∈ boundaryCircle S x R) ∧
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, Q S x R),
        IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range (a i) ∪ Set.range b := fun i => (r.arc (e i)).property
  obtain ⟨E, hE, hzero, hpositive, c, hc⟩ :=
    ThreeArcCut.original_nonempty_at_most_three_essential_proper_arcs_shrinking_essential_frontier_collar
      S g hg hS x R hR htarget τ.card hn hcard a hemb hend hint hpair hess
  have hhalf : (⟨1/2, by norm_num⟩ : Interval) ∈ Set.Ioo 0 1 := by
    change (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1
    norm_num
  have hcQ : c.val.image ⊆ interior ((openDisk S x R)ᶜ) := by
    rw [hc]
    exact (hpositive _ hhalf).1
  have hca : ∀ u : ↥τ, Disjoint c.val.image
      (Set.range (fun t : Interval => ((r.arc u).val.val t).val)) := by
    intro u
    rw [hc]
    simpa only [a, e.apply_symm_apply] using (hpositive _ hhalf).2 (e.symm u)
  -- Separately owned equality; no extra premise in the protected public head.
  have hcarrierEq : faceCarrier S x R τ = actualFamilyCarrier S x R r.arc := by
    exact faceCarrier_eq_actualFamilyCarrier S x R g hg hS hR htarget τ hτ r
  refine ⟨c, ⟨r, c, rfl, hcQ, hca⟩, ?_⟩
  intro v hv
  rw [hcarrierEq] at hv
  obtain ⟨d, hdv, hdQ, hda⟩ := hv
  rw [← hdv]
  apply hcompat E hE c d hc
  intro z hzd
  rcases hzero z with hzB | hza
  · have hdint := hdQ hzd
    rw [exterior_interior_eq_complement_chart_closed_disk S g hS x R hR htarget] at hdint
    exact hdint (Or.inr hzB)
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hza
    exact Set.disjoint_left.mp (hda (e i)) hzd hi

end CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers
