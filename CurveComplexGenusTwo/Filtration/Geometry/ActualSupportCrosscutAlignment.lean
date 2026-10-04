import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import CurveComplexGenusTwo.Topology.CrosscutIsotopy
import CurveComplexGenusTwo.Topology.ChartLift
import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
import CurveComplexGenusTwo.Topology.RestrictedLink.TwoInteriorArcHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualGapArcLinkHeaders

namespace CurveComplex.HyperellipticModel

open Set Schoenflies

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

noncomputable local instance actualSupportCrosscutAlignmentSurfaceDecidableEq : DecidableEq S := Classical.decEq _
noncomputable local instance actualSupportCrosscutAlignmentDecidableEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/-- A concrete complementary crosscut move produces an ambient marked isotopy
that fixes every already aligned arc in the protected graph pointwise. -/
theorem actual_crosscut_isotopy_fixing_graph (M : HyperellipticModel E S)
    (P : Set S) (a b : EssentialMarkedArc M)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (A B : Set Plane) (x y : Plane)
    (hA : IsArcBetween A x y) (hB : IsArcBetween B x y)
    (hx : x ∈ modelCurve) (hy : y ∈ modelCurve)
    (hAi : A \ {x, y} ⊆ Plane.openSquare 0 1)
    (hBi : B \ {x, y} ⊆ Plane.openSquare 0 1)
    (haImage : a.val.image = f '' A) (hbImage : b.val.image = f '' B)
    (havoid : ∀ z ∈ Plane.openSquare 0 1,
      f z ∉ M.cover.branch ∧ f z ∉ P) :
    ∃ H : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → H.map (t, z) = z) ∧
      (∀ t z, z ∈ P → H.map (t, z) = z) ∧
      H.finalMap '' a.val.image = b.val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  obtain ⟨R, H, hR, hHA, hHR, hHout⟩ :=
    CurveComplex.position_crosscut_supported_isotopy A B x y hA hB hx hy hAi hBi
  let J : Plane ≃ₜ range f := hf.isEmbedding.toHomeomorph
  let e : range f ≃ₜ (univ : Set Plane) :=
    J.symm.trans (Homeomorph.Set.univ Plane).symm
  have he (u : range f) : (e u : Plane) = J.symm u := rfl
  have hJ (u : range f) : f (J.symm u) = u.val :=
    congrArg Subtype.val (J.apply_symm_apply u)
  have hfix : ∀ t z, z ∉ Plane.closedSquare 0 1 → H.map (t, z) = z := by
    intro t z hz
    apply hHout t z
    intro hin
    exact hz (mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hin).le)
  obtain ⟨K, G, hcoord, hGU, hGout⟩ := CurveComplex.position_surface_chart_lift S
    (range f) univ hf.isOpenMap.isOpen_range e (Plane.closedSquare 0 1)
    (isCompact_closedSquare 0 1) (subset_univ _) H hfix
  have hgfix (Q : Set S)
      (hq : ∀ z ∈ Plane.openSquare 0 1, f z ∉ Q) :
      ∀ t z, z ∈ Q → G.map (t, z) = z := by
    intro t z hz
    by_cases hr : z ∈ range f
    · let u : range f := ⟨z, hr⟩
      have hK : K.map (t, u) = u := by
        apply e.injective
        apply Subtype.ext
        have hout : (e u : Plane) ∉ Plane.openSquare 0 1 := by
          intro hin
          exact hq _ hin (by rw [he, hJ]; exact hz)
        exact (hcoord t u).trans (hHout t _ hout)
      exact (hGU t u).trans (congrArg Subtype.val hK)
    · exact hGout t z hr
  refine ⟨G, hgfix (M.cover.branch : Set S) (fun z hz => (havoid z hz).1),
    hgfix P (fun z hz => (havoid z hz).2), ?_⟩
  rw [haImage, hbImage]
  ext z
  constructor
  · rintro ⟨w, ⟨t, ht, rfl⟩, hw⟩
    let u : range f := J t
    refine ⟨(e (K.finalMap u) : Plane), ?_, ?_⟩
    · have hc := hcoord (⟨1, by norm_num⟩ : Interval) u
      change (e (K.finalMap u) : Plane) = H.finalMap (e u : Plane) at hc
      have heu : (e u : Plane) = t := by simp [he, u]
      rw [hc, heu]
      exact hHA ▸ mem_image_of_mem H.finalMap ht
    · rw [he, hJ]
      exact (hGU (⟨1, by norm_num⟩ : Interval) u).symm.trans hw
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨z, hz, hzt⟩ := (show t ∈ H.finalMap '' A from hHA.symm ▸ ht)
    let u : range f := J z
    let v : range f := J t
    have heu : (e u : Plane) = z := by simp [he, u]
    have hev : (e v : Plane) = t := by simp [he, v]
    have hKv : K.finalMap u = v := by
      apply e.injective
      apply Subtype.ext
      have hc := hcoord (⟨1, by norm_num⟩ : Interval) u
      change (e (K.finalMap u) : Plane) = H.finalMap (e u : Plane) at hc
      rw [hc, heu, hzt, hev]
    refine ⟨f z, mem_image_of_mem f hz, ?_⟩
    change G.map ((⟨1, by norm_num⟩ : Interval), u.val) = v.val
    rw [hGU]
    exact congrArg Subtype.val hKv

/-- Transport by a produced ambient marked isotopy retains literal quotient
classes and fixes the images of every protected actual arc. -/
theorem actual_marked_family_transport_fixing_graph (M : HyperellipticModel E S)
    {I : Type} (r : I → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (H : AmbientIsotopy S)
    (hm : ∀ t z, z ∈ M.cover.branch → H.map (t, z) = z)
    (P : Set S) (hP : ∀ t z, z ∈ P → H.map (t, z) = z) :
    ∃ s : I → EssentialMarkedArc M,
      (∀ i, Quotient.mk (essentialArcSetoid M) (s i) =
        Quotient.mk (essentialArcSetoid M) (r i)) ∧
      (∀ i, (s i).val.image = H.finalMap '' (r i).val.image) ∧
      (∀ i j, i ≠ j → Disjoint (arcInterior M (s i)) (arcInterior M (s j))) ∧
      ∀ i, (r i).val.image ⊆ P → (s i).val.image = (r i).val.image := by
  obtain ⟨g, hg⟩ := H.homeomorphism_at (⟨1, by norm_num⟩ : Interval)
  have hgfix : ∀ z, z ∈ M.cover.branch → g z = z :=
    fun z hz => (hg z).trans (hm _ z hz)
  let s : I → EssentialMarkedArc M := fun i => (r i).transport g hgfix
  have himage (i) : (s i).val.image = H.finalMap '' (r i).val.image := by
    change ((r i).val.transport g hgfix).image = _
    rw [MarkedArc.transport_image]
    exact congrArg (fun f : S → S => f '' (r i).val.image) (funext hg)
  refine ⟨s, ?_, himage, ?_, ?_⟩
  · intro i
    symm
    apply Quotient.sound
    exact ⟨H, hm, (himage i).symm⟩
  · intro i j hij
    exact arcInterior_transport_disjoint (r i) (r j) g hgfix (hd i j hij)
  · intro i hi
    rw [himage i]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [AmbientIsotopy.finalMap, hP _ x (hi hx)] using hx
    · intro hz
      exact ⟨z, hz, hP _ z (hi hz)⟩

/-- Once the images on an arbitrary finite support have been aligned by actual
ambient moves, representative replacement makes the restriction literally equal
to the prescribed family, preserving essentiality and all disjointness. -/
theorem actual_family_literal_restriction_of_aligned_images (M : HyperellipticModel E S)
    (T F : Finset (EssentialArcClass M)) (hsub : T ⊆ F)
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
    (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (rT : {w // w ∈ T} → EssentialMarkedArc M)
    (hrT : ∀ w, Quotient.mk (essentialArcSetoid M) (rT w) = w.val)
    (himages : ∀ w : {w // w ∈ T}, (r ⟨w.val, hsub w.property⟩).val.image =
      (rT w).val.image) :
    ∃ r' : {w // w ∈ F} → EssentialMarkedArc M,
      (∀ w, Quotient.mk (essentialArcSetoid M) (r' w) = w.val) ∧
      (∀ w z, w ≠ z → Disjoint (arcInterior M (r' w)) (arcInterior M (r' z))) ∧
      (∀ w : {w // w ∈ T}, r' ⟨w.val, hsub w.property⟩ = rT w) ∧
      ∀ w, (r' w).val.image = (r w).val.image := by
  classical
  let r' : {w // w ∈ F} → EssentialMarkedArc M :=
    fun w => if h : w.val ∈ T then rT ⟨w.val, h⟩ else r w
  have himage (w : {w // w ∈ F}) : (r' w).val.image = (r w).val.image := by
    dsimp only [r']
    split_ifs with hw
    · exact (himages ⟨w.val, hw⟩).symm
    · rfl
  refine ⟨r', ?_, ?_, ?_, himage⟩
  · intro w
    dsimp only [r']
    split_ifs with hw
    · exact hrT _
    · exact hr _
  · intro w z hwz
    change Disjoint ((r' w).val.image \ (M.cover.branch : Set S))
      ((r' z).val.image \ (M.cover.branch : Set S))
    rw [himage w, himage z]
    exact hd w z hwz
  · intro w
    simp only [r', dite_eq_left w.property]

/-- One actual complement-crosscut step adds the next support vertex to the
literal aligned family and retains every previously aligned representative. -/
theorem actual_support_crosscut_alignment_step (M : HyperellipticModel E S)
    (T F J : Finset (EssentialArcClass M)) (hTF : T ⊆ F) (hJT : J ⊆ T)
    (u : {w // w ∈ T})
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
    (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (rT : {w // w ∈ T} → EssentialMarkedArc M)
    (hrT : ∀ w, Quotient.mk (essentialArcSetoid M) (rT w) = w.val)
    (haligned : ∀ w : {w // w ∈ T}, w.val ∈ J →
      r ⟨w.val, hTF w.property⟩ = rT w)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (A B : Set Plane) (x y : Plane)
    (hA : IsArcBetween A x y) (hB : IsArcBetween B x y)
    (hx : x ∈ modelCurve) (hy : y ∈ modelCurve)
    (hAi : A \ {x, y} ⊆ Plane.openSquare 0 1)
    (hBi : B \ {x, y} ⊆ Plane.openSquare 0 1)
    (haImage : (r ⟨u.val, hTF u.property⟩).val.image = f '' A)
    (hbImage : (rT u).val.image = f '' B)
    (havoid : ∀ z ∈ Plane.openSquare 0 1,
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
  let uF : {w // w ∈ F} := ⟨u.val, hTF u.property⟩
  obtain ⟨H, hm, hP, hmove⟩ := actual_crosscut_isotopy_fixing_graph M
    (actualObjectTrace M r J) (r uF) (rT u) f hf A B x y hA hB hx hy
    hAi hBi haImage hbImage havoid
  obtain ⟨s, hs, himage, hdisj, hpres⟩ :=
    actual_marked_family_transport_fixing_graph M r hd H hm (actualObjectTrace M r J) hP
  have hnew : (s uF).val.image = (rT u).val.image :=
    (himage uF).trans hmove
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
  have hrJ : ∀ w, Quotient.mk (essentialArcSetoid M) (rJ w) = w.val :=
    fun w => hrT _
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
  refine ⟨H, hm, hP, r', hr', hd', ?_, ?_⟩
  · intro w hw
    exact hrestrict ⟨w.val, hw⟩
  · intro w
    exact (hkeep w).trans (himage w)

/-- Chronological finite composition of the actual ambient alignment steps. -/
def supportPrefixIsotopy (steps : ℕ → AmbientIsotopy S) : ℕ → AmbientIsotopy S
  | 0 => AmbientIsotopy.identity S
  | n + 1 => (supportPrefixIsotopy steps n).compose (steps n)

/-- Deterministic induction assembles the actual produced local ambient moves.
Its inputs are individual move receipts, never a global system isotopy or cone. -/
theorem actual_support_ambient_steps_assemble (M : HyperellipticModel E S)
    {I : Type} (r : ℕ → I → EssentialMarkedArc M)
    (steps : ℕ → AmbientIsotopy S) (n : ℕ)
    (hm : ∀ j < n, ∀ t z, z ∈ M.cover.branch → (steps j).map (t, z) = z)
    (hstep : ∀ j < n, ∀ i,
      (steps j).finalMap '' (r j i).val.image = (r (j + 1) i).val.image) :
    ∃ H : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → H.map (t, z) = z) ∧
      ∀ i, H.finalMap '' (r 0 i).val.image = (r n i).val.image := by
  have hmarks : ∀ k : ℕ,
      (∀ j < k, ∀ t z, z ∈ M.cover.branch → (steps j).map (t, z) = z) →
      ∀ t z, z ∈ M.cover.branch → (supportPrefixIsotopy steps k).map (t, z) = z := by
    intro k
    induction k with
    | zero => intro h t z hz; rfl
    | succ k ih =>
      intro h t z hz
      change (steps k).map (t, (supportPrefixIsotopy steps k).map (t, z)) = z
      rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)) t z hz]
      exact h k (Nat.lt_succ_self k) t z hz
  have himages : ∀ k : ℕ,
      (∀ j < k, ∀ i,
        (steps j).finalMap '' (r j i).val.image = (r (j + 1) i).val.image) →
      ∀ i, (supportPrefixIsotopy steps k).finalMap '' (r 0 i).val.image =
        (r k i).val.image := by
    intro k
    induction k with
    | zero => intro h i; exact Set.image_id _
    | succ k ih =>
      intro h i
      rw [supportPrefixIsotopy, AmbientIsotopy.compose_finalMap, Set.image_comp]
      rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)) i]
      exact h k (Nat.lt_succ_self k) i
  exact ⟨supportPrefixIsotopy steps n, hmarks n hm, himages n hstep⟩

/-- The two-mark face genuinely produces a fixed actual apex representative.
This construction does not assume vertex existence or a cone certificate. -/
theorem actual_two_mark_face_apex (M : HyperellipticModel E S)
    {k : ℕ} (T : ActualStratum M k)
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hrT : ∀ w, Quotient.mk (essentialArcSetoid M) (rT w) = w.val)
    (hdT : ∀ w z, w ≠ z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (U : Set S) (hUG : IsComplementComponent (⋃ w, (rT w).val.image) U)
    (e : Plane ≃ₜ U) (p q : S) (hp : p ∈ U) (hq : q ∈ U)
    (hpB : p ∈ M.cover.branch) (hqB : q ∈ M.cover.branch) (hpq : p ≠ q)
    (hmarks : ∀ z ∈ U, z ∈ M.cover.branch → z = p ∨ z = q) :
    ∃ a : EssentialMarkedArc M,
      a.val.map 0 = p ∧ a.val.map 1 = q ∧ a.val.image ⊆ U ∧
      classEndpoints M (Quotient.mk (essentialArcSetoid M) a) = {p, q} ∧
      ({Quotient.mk (essentialArcSetoid M) a} : Finset (EssentialArcClass M)) ∈
        actualRestrictedLink M T := by
  classical
  obtain ⟨a, ha0, ha1, haU⟩ :=
    actual_two_interior_marks_arc M U e p q hp hq hpB hqB hpq hmarks
  have hne : a.val.map 0 ≠ a.val.map 1 := by rw [ha0, ha1]; exact hpq
  have hint : arcInterior M a ⊆ U := fun z hz => haU hz.1
  have hvertex := actual_gap_arc_link_vertex M T.val rT hrT hdT T.property.2.2
    U hUG.2.2.1 a hne hint (Or.inl (ha0.symm ▸ hp))
  refine ⟨a, ha0, ha1, haU, ?_, hvertex⟩
  change ({a.val.map 0, a.val.map 1} : Finset S) = {p, q}
  rw [ha0, ha1]

end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.actual_crosscut_isotopy_fixing_graph
#print axioms CurveComplex.HyperellipticModel.actual_marked_family_transport_fixing_graph
#print axioms CurveComplex.HyperellipticModel.actual_family_literal_restriction_of_aligned_images
#print axioms CurveComplex.HyperellipticModel.actual_support_crosscut_alignment_step
#print axioms CurveComplex.HyperellipticModel.actual_support_ambient_steps_assemble
#print axioms CurveComplex.HyperellipticModel.actual_two_mark_face_apex
