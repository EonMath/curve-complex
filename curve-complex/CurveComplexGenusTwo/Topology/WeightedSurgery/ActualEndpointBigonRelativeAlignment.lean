import CurveComplexGenusTwo.Filtration.Geometry.ActualEndpointBigonEnlargement
import CurveComplexGenusTwo.Filtration.Geometry.ActualCompactTimeCrosscutExtraction

noncomputable section
open Set Topology Schoenflies CurveComplex

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

noncomputable local instance instDecidableEqEssentialArcClass_endpointBigonRelativeAlignment (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/-- A target-dependent WHOLE bigon repair fixes a closed protected graph even
when that graph shares the marked endpoints. The enlarged crosscut chart is
constructed from the old and prescribed target sides; it is not assumed. -/
theorem actual_endpoint_bigon_relative_alignment
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (P : Set S) (hPc : IsClosed P)
    (hAP : Disjoint (arcInterior M a) P) (hBP : Disjoint (arcInterior M b) P)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (A B : Set Plane) (p q : Plane)
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hwhole : A ∪ B = modelCurve)
    (haImage : a.val.image = f '' A) (hbImage : b.val.image = f '' B)
    (hp : f p ∈ M.cover.branch) (hq : f q ∈ M.cover.branch)
    (hboundary : ∀ z ∈ modelCurve, f z ∈ M.cover.branch → z = p ∨ z = q)
    (hinside : ∀ z ∈ Plane.openSquare 0 1,
      f z ∉ M.cover.branch ∧ f z ∉ P) :
    ∃ H : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → H.map (t, z) = z) ∧
      (∀ t z, z ∈ P → H.map (t, z) = z) ∧
      H.finalMap '' a.val.image = b.val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let F : Set Plane := f ⁻¹' ((M.cover.branch : Set S) ∪ P)
  have hFc : IsClosed F :=
    (M.cover.branch.finite_toSet.isClosed.union hPc).preimage hf.continuous
  have hpF : p ∈ F := Or.inl hp
  have hqF : q ∈ F := Or.inl hq
  have hFb : ∀ z ∈ F, z ∈ modelCurve → z = p ∨ z = q := by
    intro z hz hzC
    rcases hz with hzm | hzP
    · exact hboundary z hzC hzm
    · have hzAB : z ∈ A ∪ B := hwhole.symm ▸ hzC
      have hzm : f z ∈ M.cover.branch := by
        by_contra hzn
        rcases hzAB with hzA | hzB
        · have hza : f z ∈ a.val.image := haImage.symm ▸ Set.mem_image_of_mem f hzA
          exact Set.disjoint_left.mp hAP ⟨hza, hzn⟩ hzP
        · have hzb : f z ∈ b.val.image := hbImage.symm ▸ Set.mem_image_of_mem f hzB
          exact Set.disjoint_left.mp hBP ⟨hzb, hzn⟩ hzP
      exact hboundary z hzC hzm
  have hFi : Disjoint (Plane.openSquare 0 1) F := by
    apply Set.disjoint_left.mpr
    intro z hz hzF
    exact hzF.elim (hinside z hz).1 (hinside z hz).2
  obtain ⟨φ, hφp, hφq, hA', hB', hAi, hBi, hfree⟩ :=
    actual_endpoint_preserving_bigon_enlargement A B p q hA hB hwhole F hFc hpF hqF hFb hFi
  have hcancel (C : Set Plane) : (f ∘ φ) '' (φ.symm '' C) = f '' C := by
    rw [Set.image_image]
    simp only [Function.comp_apply, φ.apply_symm_apply]
  have hnew : Topology.IsOpenEmbedding (f ∘ φ) := hf.comp φ.isOpenEmbedding
  have hpC : p ∈ modelCurve := hwhole ▸ Or.inl hA.left_mem
  have hqC : q ∈ modelCurve := hwhole ▸ Or.inl hA.right_mem
  have havoid : ∀ z ∈ Plane.openSquare 0 1,
      (f ∘ φ) z ∉ M.cover.branch ∧ (f ∘ φ) z ∉ P := by
    intro z hz
    exact ⟨fun hm => hfree z hz (Or.inl hm), fun hP => hfree z hz (Or.inr hP)⟩
  exact actual_crosscut_isotopy_fixing_graph M P a b (f ∘ φ) hnew
    (φ.symm '' A) (φ.symm '' B) p q hA' hB' hpC hqC hAi hBi
    (haImage.trans (hcancel A).symm) (hbImage.trans (hcancel B).symm) havoid

/-- The actual target representative is disjoint from the original protected
graph when its T-family is disjoint and the J restriction is literally aligned.
This is derived from the original family data, not a graph-clearance premise. -/
theorem actual_target_arc_disjoint_aligned_graph
    (M : HyperellipticModel E S) (J T F : Finset (EssentialArcClass M))
    (hJT : J ⊆ T) (hTF : T ⊆ F)
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (rT : {w // w ∈ T} → EssentialMarkedArc M)
    (hdT : ∀ w z, w ≠ z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (haligned : ∀ w : {w // w ∈ T}, w.val ∈ J →
      r ⟨w.val, hTF w.property⟩ = rT w)
    (u : {w // w ∈ T}) (hu : u.val ∉ J) :
    Disjoint (arcInterior M (rT u)) (actualObjectTrace M r J) := by
  apply Set.disjoint_left.mpr
  intro z hz hzP
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hzP
  obtain ⟨hvJ, hzv⟩ := Set.mem_iUnion.mp hv
  let vT : {w // w ∈ T} := ⟨v.val, hJT hvJ⟩
  have huv : u ≠ vT := by
    intro he
    exact hu (congrArg Subtype.val he ▸ hvJ)
  have heF : (⟨vT.val, hTF vT.property⟩ : {w // w ∈ F}) = v := Subtype.ext rfl
  have hrv : r v = rT vT := by simpa only [heF] using haligned vT hvJ
  have hzvT : z ∈ (rT vT).val.image := hrv ▸ hzv
  exact Set.disjoint_left.mp (hdT u vT huv) hz ⟨hzvT, hz.2⟩

/-- A target-dependent endpoint-sensitive bigon repair advances the ORIGINAL
whole-family support alignment. No internal core cover, relative ambient
isotopy, or finite replacement sequence is supplied as an input. -/
theorem actual_support_endpoint_bigon_alignment_step
    (M : HyperellipticModel E S) (J T F : Finset (EssentialArcClass M))
    (hJT : J ⊆ T) (hTF : T ⊆ F)
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
    (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (rT : {w // w ∈ T} → EssentialMarkedArc M)
    (hrT : ∀ w, Quotient.mk (essentialArcSetoid M) (rT w) = w.val)
    (hdT : ∀ w z, w ≠ z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (haligned : ∀ w : {w // w ∈ T}, w.val ∈ J →
      r ⟨w.val, hTF w.property⟩ = rT w)
    (u : {w // w ∈ T}) (hu : u.val ∉ J)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (A B : Set Plane) (p q : Plane)
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hwhole : A ∪ B = modelCurve)
    (haImage : (r ⟨u.val, hTF u.property⟩).val.image = f '' A)
    (hbImage : (rT u).val.image = f '' B)
    (hp : f p ∈ M.cover.branch) (hq : f q ∈ M.cover.branch)
    (hboundary : ∀ z ∈ modelCurve, f z ∈ M.cover.branch → z = p ∨ z = q)
    (hinside : ∀ z ∈ Plane.openSquare 0 1,
      f z ∉ M.cover.branch ∧ f z ∉ actualObjectTrace M r J) :
    ∃ H : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → H.map (t, z) = z) ∧
      (∀ t z, z ∈ actualObjectTrace M r J → H.map (t, z) = z) ∧
      ∃ r' : {w // w ∈ F} → EssentialMarkedArc M,
        (∀ w, Quotient.mk (essentialArcSetoid M) (r' w) = w.val) ∧
        (∀ w z, w ≠ z → Disjoint (arcInterior M (r' w)) (arcInterior M (r' z))) ∧
        (∀ w : {w // w ∈ T}, w.val ∈ insert u.val J →
          r' ⟨w.val, hTF w.property⟩ = rT w) ∧
        ∀ w, (r' w).val.image = H.finalMap '' (r w).val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let uF : {w // w ∈ F} := ⟨u.val, hTF u.property⟩
  obtain ⟨H, hm, hP, hmove⟩ := actual_endpoint_bigon_relative_alignment M
    (r uF) (rT u) (actualObjectTrace M r J) (actualObjectTrace_compact M r J).isClosed
    (actual_next_arc_disjoint_support_graph M r hd J uF hu)
    (actual_target_arc_disjoint_aligned_graph M J T F hJT hTF r rT hdT haligned u hu)
    f hf A B p q hA hB hwhole haImage hbImage hp hq hboundary hinside
  obtain ⟨s, hs, himage, hdisj, hpres⟩ :=
    actual_marked_family_transport_fixing_graph M r hd H hm (actualObjectTrace M r J) hP
  have hnew : (s uF).val.image = (rT u).val.image := (himage uF).trans hmove
  have hold (w : {w // w ∈ F}) (hw : w.val ∈ J) :
      (s w).val.image = (r w).val.image := by
    apply hpres w
    intro z hz
    exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, hz⟩⟩
  let J' := insert u.val J
  have hJ'T : J' ⊆ T := Finset.insert_subset u.property hJT
  have hJ'F : J' ⊆ F := hJ'T.trans hTF
  let rJ : {w // w ∈ J'} → EssentialMarkedArc M :=
    fun w => rT ⟨w.val, hJ'T w.property⟩
  have hrJ : ∀ w, Quotient.mk (essentialArcSetoid M) (rJ w) = w.val := fun w => hrT _
  have himages : ∀ w : {w // w ∈ J'},
      (s ⟨w.val, hJ'F w.property⟩).val.image = (rJ w).val.image := by
    intro w
    rcases Finset.mem_insert.mp w.property with hwu | hwJ
    · have heF : (⟨w.val, hJ'F w.property⟩ : {w // w ∈ F}) = uF := Subtype.ext hwu
      have heT : (⟨w.val, hJ'T w.property⟩ : {w // w ∈ T}) = u := Subtype.ext hwu
      simpa only [rJ, heF, heT] using hnew
    · exact (hold _ hwJ).trans
        (congrArg (fun a : EssentialMarkedArc M => a.val.image)
          (haligned ⟨w.val, hJ'T w.property⟩ hwJ))
  obtain ⟨r', hr', hd', hrestrict, hkeep⟩ :=
    actual_family_literal_restriction_of_aligned_images M J' F hJ'F s
      (fun w => (hs w).trans (hr w)) hdisj rJ hrJ himages
  refine ⟨H, hm, hP, r', hr', hd', ?_, fun w => (hkeep w).trans (himage w)⟩
  intro w hw
  exact hrestrict ⟨w.val, hw⟩

#print axioms actual_endpoint_bigon_relative_alignment
#print axioms actual_target_arc_disjoint_aligned_graph
#print axioms actual_support_endpoint_bigon_alignment_step

end CurveComplex.HyperellipticModel
