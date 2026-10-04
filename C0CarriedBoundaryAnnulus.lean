import C0FaceCarrierContractibleExact
import CarrierExtension
import C0CurveToArcBoundaryCorrespondence
import OriginalArcFaceCurveCarriers
import C0RelativeCarrierScaffold

/-! Head A of c0_N6_source_assembly/PLAN.md. The actual boundary precomplex
is the image of N1's boundary faces, not the full complex on boundary vertices.
No new operative definition or assumed successful carried map is introduced. -/
open Set
open scoped BigOperators
attribute [local instance 2000] instDecidable_c0RelativeCarrierScaffold
  instDecidableEq_c0RelativeCarrierScaffold
attribute [local instance 3000] instDecidableEqFin
attribute [local instance 3000]
  CurveComplex.C0BoundaryCorrespondence.instDecidableEqVertex_c0CurveToArcBoundaryCorrespondence
  CurveComplex.C0BoundaryCorrespondence.instDecidableEqArcVertex_c0CurveToArcBoundaryCorrespondence
set_option autoImplicit false
namespace CurveComplex.C0BoundaryCorrespondence.CarriedAnnulus
open CurveComplex.C0BoundaryCorrespondence
open CurveComplex.FiniteArcDisk
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc
open C0RelativeCarrier

noncomputable local instance (priority := 4000) {V : Type*}
    (D : AbstractSimplicialComplex V) : DecidableEq (Face D) :=
  @Subtype.instDecidableEq (Finset V) (fun σ => σ ∈ D.faces)
    (fun a b => @Finset.decidableEq V (instDecidableEq_c0RelativeCarrierScaffold V) a b)

/-- Construct both the carried boundary map and an annulus from the original p.
The same returned j defines gamma and intertwines the exact e with the actual
N1 boundary inclusion. All closed N1 word pieces, including the initial
constant piece, are retained. Repeated labels and zero-length blocks are allowed.
Small-carrier geometry is an independent proof dependency, never a premise. -/
theorem source_c0_boundary_correspondence_carried_annulus
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (v : Vertex S) (n : ℕ)
    (z : Fin (n + 1) → RealizationPoint (curveComplex S 0))
    (E : (k : Fin n) → Path (z k.castSucc) (z k.succ))
    (p : Path (realizationVertex (curveComplex S 0) v ((curveComplex S 0).singleton_mem v))
      (realizationVertex (curveComplex S 0) v ((curveComplex S 0).singleton_mem v)))
    (G : ActualBorderedRegions S x R (loopSupport S v n z))
    (C : RegionalArcComparison S x R G)
    (bc : BoundaryCorrespondence S x R G C v n z E p)
    (allowed : ArcVertex S x R → Prop)
    (d : LabelledDisk bc.arcDomain (arcComplex S x R) bc.arcLabel bc.arcWord allowed) :
    let D := d.disk.complex
    let L : PreAbstractSimplicialComplex (Fin d.disk.vertexCount) :=
      d.disk.boundary.toPreAbstractSimplicialComplex.map (fun u => u.val)
    ∀ (e : RealizationPoint (barycentricSubdivision D) ≃ₜ RealizationPoint D),
      (∀ a w, (e a).weight w =
        ∑ σ : Face D, if w ∈ σ.val then a.weight σ / (σ.val.card : ℝ) else 0) →
      (e '' Set.range (fullToAmbient (barycentricSubdivision D)
          (fun σ : Face D => σ.val ∈ L.faces)) =
        {a : RealizationPoint D | ∃ σ ∈ L.faces, ∀ w ∉ σ, a.weight w = 0}) →
      let inc := fullToAmbient (barycentricSubdivision D)
        (fun σ : Face D => σ.val ∈ L.faces)
      let P : Face D → Vertex S → Prop := fun σ w =>
        CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R
          (σ.val.image d.label) w
      (∀ σ : Face D, ∀ w : Vertex S,
        FaceCurveCarrier S x R (σ.val.image d.label) w ↔ P σ w) ∧
      (∀ (k : Fin bc.curveWord.edgeCount) (t : unitInterval),
        bc.curveWord.edge k t ∈ fullSupportLocus (curveComplex S 0)
          (CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R
            {bc.junction k.succ})) ∧
      ∃ j : RealizationPoint (boundarySubdivision D L) ≃ₜ RealizationPoint d.disk.boundary,
        (∀ y, e (inc y) = d.disk.boundaryInclusion (j y)) ∧
        let gamma : C(unitInterval, RealizationPoint (boundarySubdivision D L)) :=
          (⟨j.symm, j.symm.continuous⟩ : C(RealizationPoint d.disk.boundary,
            RealizationPoint (boundarySubdivision D L))).comp
            (d.boundaryParam.comp (⟨d.reparam.symm, d.reparam.symm.continuous⟩ :
              C(unitInterval, unitInterval)))
        gamma 0 = gamma 1 ∧
        (∀ t : unitInterval, d.realizationMap (e (inc (gamma t))) = bc.arcWord.loop t) ∧
        (∀ k : Fin (bc.arcWord.edgeCount + 1),
          j '' Set.range (fun t : unitInterval => gamma (d.wordPieceTime k t)) =
            ⋃ σ ∈ d.boundaryBlock k, CurveComplex.faceCarrier d.disk.boundary σ) ∧
        ∃ b : C(RealizationPoint (boundarySubdivision D L), RealizationPoint (curveComplex S 0)),
          (∀ (Γ : Finset {σ : Face D // σ.val ∈ L.faces})
              (hΓ : Γ ∈ (boundarySubdivision D L).faces),
            ∀ σ₀ ∈ Γ, (∀ τ ∈ Γ, σ₀.val.val ⊆ τ.val.val) →
              ∀ y : FiniteSimplex Γ,
                b (faceInclusion (boundarySubdivision D L) Γ hΓ y) ∈
                  fullSupportLocus (curveComplex S 0) (P σ₀.val)) ∧
          Nonempty (ContinuousMap.HomotopyWith p.toContinuousMap (b.comp gamma)
            (fun q : C(unitInterval, RealizationPoint (curveComplex S 0)) => q 0 = q 1)) := by
  set_option maxHeartbeats 8000000 in
    all_goals
      intro D L e he_weight he_boundary inc P
      have hcarrier (τ : Finset (ArcVertex S x R)) (hne : τ.Nonempty)
          (w : Vertex S) : FaceCurveCarrier S x R τ w ↔
            CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R τ w := by
        constructor
        · rintro ⟨_, rep, hc, hd, c, hcw, hcQ, hca⟩
          exact ⟨⟨rep, hc, hd⟩, c, hcw, hcQ, hca⟩
        · rintro ⟨r, c, hcw, hcQ, hca⟩
          exact ⟨hne, r.arc, r.class_eq, r.disjoint, c, hcw, hcQ, hca⟩
      have hedge : ∀ (k : Fin bc.curveWord.edgeCount) (t : unitInterval),
          bc.curveWord.edge k t ∈ fullSupportLocus (curveComplex S 0)
            (CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R
              {bc.junction k.succ}) := by
        intro k t w hw
        have hl := (hcarrier _ (Finset.singleton_nonempty _) _).mp (bc.junction_left k)
        have hr := (hcarrier _ (Finset.singleton_nonempty _) _).mp (bc.junction_right k)
        have hleft : bc.curveWord.vertex k.castSucc ≠ w := by
          intro hh
          exact hw (hh ▸ hl)
        have hright : bc.curveWord.vertex k.succ ≠ w := by
          intro hh
          exact hw (hh ▸ hr)
        simpa only [id_eq, ite_eq_right hleft, ite_eq_right hright, mul_zero, add_zero] using
          bc.curveWord.edge_weight k t w
      refine ⟨?_, hedge, ?_⟩
      · intro σ w
        exact hcarrier _ ((d.label_faces σ.val σ.property).1) w
      · have hboundary_range : Set.range d.disk.boundaryInclusion =
            {a : RealizationPoint D | ∃ σ ∈ L.faces, ∀ w ∉ σ, a.weight w = 0} := by
          ext a
          constructor
          · rintro ⟨q, rfl⟩
            obtain ⟨τ, hτ, hz, hs⟩ := q.liesInFace
            refine ⟨τ.image Subtype.val, ?_, ?_⟩
            · exact ⟨τ, hτ, rfl⟩
            · intro w hw
              rw [d.disk.boundaryInclusion_weight]
              apply Finset.sum_eq_zero
              intro b hb
              by_cases heq : b.val = w
              · rw [ite_eq_left heq]
                apply hz
                intro hbt
                exact hw (Finset.mem_image.mpr ⟨b, hbt, heq⟩)
              · exact ite_eq_right heq
          · rintro ⟨σ, hσ, hz⟩
            obtain ⟨τ, hτ, rfl⟩ := hσ
            have hsum : ∑ w ∈ τ.image Subtype.val, a.weight w = 1 := by
              obtain ⟨ρ, hρ, hρz, hρs⟩ := a.liesInFace
              have h1 : (∑ w ∈ τ.image Subtype.val, a.weight w) = ∑ w, a.weight w := by
                apply Finset.sum_subset (Finset.subset_univ _)
                intro w _ hw
                exact hz w hw
              have h2 : (∑ w ∈ ρ, a.weight w) = ∑ w, a.weight w := by
                apply Finset.sum_subset (Finset.subset_univ _)
                intro w _ hw
                exact hρz w hw
              exact h1.trans (h2.symm.trans hρs)
            let q : RealizationPoint d.disk.boundary :=
              { weight := fun b => a.weight b.val
                nonneg := fun b => a.nonneg b.val
                liesInFace := ⟨τ, hτ, (by
                  intro b hb
                  apply hz
                  intro hm
                  obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hm
                  exact hb ((Subtype.val_injective heq) ▸ hc)), (by
                  rw [Finset.sum_image Subtype.val_injective.injOn] at hsum
                  exact hsum)⟩ }
            refine ⟨q, ?_⟩
            apply RealizationPoint.ext
            funext w
            rw [d.disk.boundaryInclusion_weight]
            by_cases hw : w ∈ d.disk.boundaryVertices
            · have hsingle := Finset.sum_eq_single (⟨w, hw⟩ : ↥d.disk.boundaryVertices)
                  (s := Finset.univ) (f := fun b => if b.val = w then q.weight b else 0)
              rw [hsingle]
              · simp [q]
              · intro b _ hb
                exact ite_eq_right (fun heq => hb (Subtype.ext heq))
              · simp
            · have ha : a.weight w = 0 := by
                apply hz
                intro hm
                obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
                exact hw b.property
              rw [ha]
              apply Finset.sum_eq_zero
              intro b _
              exact ite_eq_right (fun (heq : b.val = w) => hw (heq ▸ b.property))
        have hinc_embedding : Topology.IsEmbedding inc := by
          exact (Topology.IsEmbedding.subtypeVal).comp
            (fullSubcomplexHomeomorphSupported (barycentricSubdivision D)
              (fun σ : Face D => σ.val ∈ L.faces)).isEmbedding
        have heinc_embedding : Topology.IsEmbedding (fun y => e (inc y)) :=
          e.isEmbedding.comp hinc_embedding
        have hrange : Set.range (fun y => e (inc y)) = Set.range d.disk.boundaryInclusion := by
          rw [Set.range_comp' e inc]
          exact he_boundary.trans hboundary_range.symm
        let j : RealizationPoint (boundarySubdivision D L) ≃ₜ
            RealizationPoint d.disk.boundary :=
          heinc_embedding.toHomeomorph.trans
            ((Homeomorph.setCongr hrange).trans
              d.disk.boundaryInclusion_closedEmbedding.isEmbedding.toHomeomorph.symm)
        have hj (y : RealizationPoint (boundarySubdivision D L)) :
            e (inc y) = d.disk.boundaryInclusion (j y) := by
          have hj' := d.disk.boundaryInclusion_closedEmbedding.isEmbedding.toHomeomorph.apply_symm_apply
            ((Homeomorph.setCongr hrange) (heinc_embedding.toHomeomorph y))
          exact (congrArg Subtype.val hj').symm
        refine ⟨j, hj, ?_⟩
        intro gamma
        have hgamma_seam : gamma 0 = gamma 1 := by
          change j.symm (d.boundaryParam (d.reparam.symm 0)) =
            j.symm (d.boundaryParam (d.reparam.symm 1))
          have hz : d.reparam.symm 0 = 0 := d.reparam.symm_apply_eq.mpr d.reparam_zero.symm
          have ho : d.reparam.symm 1 = 1 := d.reparam.symm_apply_eq.mpr d.reparam_one.symm
          rw [hz, ho, d.boundary_seam]
        have hgamma_word : ∀ t : unitInterval,
            d.realizationMap (e (inc (gamma t))) = bc.arcWord.loop t := by
          intro t
          rw [hj]
          change d.realizationMap (d.disk.boundaryInclusion
            (j (j.symm (d.boundaryParam (d.reparam.symm t))))) = _
          rw [j.apply_symm_apply, d.boundary_word, d.reparam.apply_symm_apply]
        have hgamma_blocks : ∀ k : Fin (bc.arcWord.edgeCount + 1),
            j '' Set.range (fun t : unitInterval => gamma (d.wordPieceTime k t)) =
              ⋃ σ ∈ d.boundaryBlock k, CurveComplex.faceCarrier d.disk.boundary σ := by
          intro k
          rw [d.boundaryBlock_exact]
          ext q
          simp only [Set.mem_image, Set.mem_range]
          constructor
          · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
            exact ⟨t, (j.apply_symm_apply _).symm⟩
          · rintro ⟨t, rfl⟩
            exact ⟨gamma (d.wordPieceTime k t), ⟨t, rfl⟩, j.apply_symm_apply _⟩
        refine ⟨hgamma_seam, hgamma_word, hgamma_blocks, ?_⟩
        have hLD : ∀ σ ∈ L.faces, σ ∈ D.faces := by
          rintro σ ⟨τ, hτ, rfl⟩
          exact d.disk.boundary_faces τ hτ
        have hlabel_face (σ : Face D) :
            σ.val.image d.label ∈ (arcComplex S x R).faces :=
          d.label_faces σ.val σ.property
        have hlabel_card (σ : Face D) : (σ.val.image d.label).card ≤ 3 :=
          d.label_image_card σ.val σ.property
        have hantitone : ∀ σ τ : Face D, σ.val ⊆ τ.val →
            ∀ w : Vertex S, P τ w → P σ w := by
          intro σ τ hστ w hw
          exact CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier_antitone
            S x R (σ.val.image d.label) (τ.val.image d.label)
            (Finset.image_mono d.label hστ) w hw
        have hgamma_fibers (t u : unitInterval) :
            gamma t = gamma u ↔ t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0) := by
          change j.symm (d.boundaryParam (d.reparam.symm t)) =
            j.symm (d.boundaryParam (d.reparam.symm u)) ↔ _
          rw [j.symm.injective.eq_iff, d.boundaryParam_fibers]
          simp only [d.reparam.symm.injective.eq_iff, Homeomorph.symm_apply_eq,
            d.reparam_zero, d.reparam_one]
        let K := boundarySubdivision D L
        have hboundary_face_card (δ : {σ : Face D // σ.val ∈ L.faces}) :
            δ.val.val.card ≤ 2 := by
          obtain ⟨τ, hτ, hδ⟩ := δ.property
          rw [← hδ]
          exact (Finset.card_image_le).trans (d.disk.boundary_face_card τ hτ)
        have hflag_card (Γ : Finset {σ : Face D // σ.val ∈ L.faces})
            (hΓ : Γ ∈ K.faces) : Γ.card ≤ 2 := by
          have hchain : ∀ δ ∈ Γ, ∀ η ∈ Γ, δ.val.val ⊆ η.val.val ∨ η.val.val ⊆ δ.val.val := by
            intro δ hδ η hη
            exact hΓ.2 δ.val (Finset.mem_image.mpr ⟨δ, hδ, rfl⟩)
              η.val (Finset.mem_image.mpr ⟨η, hη, rfl⟩)
          have hbound := Finset.card_le_card_of_injOn
            (s := Γ) (t := ({1, 2} : Finset ℕ)) (fun δ => δ.val.val.card)
            (by
              intro δ hδ
              have hp := Finset.card_pos.mpr (D.isRelLowerSet_faces δ.val.property).1
              have hle := hboundary_face_card δ
              simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
              rcases Nat.eq_or_lt_of_le hle with h | h
              · exact Or.inr h
              · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h) hp))
            (by
              intro δ hδ η hη heq
              apply Subtype.ext
              apply Subtype.ext
              rcases hchain δ hδ η hη with h | h
              · exact Finset.eq_of_subset_of_card_le h heq.ge
              · exact (Finset.eq_of_subset_of_card_le h heq.le).symm)
          simpa using hbound
        have hpositive_label_confinement (t : unitInterval)
            (τ : Finset (ArcVertex S x R))
            (hτ : bc.arcWord.loop t ∈ CurveComplex.faceCarrier (arcComplex S x R) τ)
            (δ : {σ : Face D // σ.val ∈ L.faces})
            (hδ : δ ∈ supportFinset K (gamma t)) : δ.val.val.image d.label ⊆ τ := by
          intro w hw
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
          by_contra hnot
          have hzero : (d.realizationMap (e (inc (gamma t)))).weight (d.label u) = 0 := by
            rw [hgamma_word]
            exact hτ (d.label u) hnot
          have hlabel_le : (e (inc (gamma t))).weight u ≤
              (d.realizationMap (e (inc (gamma t)))).weight (d.label u) := by
            rw [d.realizationMap_weight]
            have hle := Finset.single_le_sum
              (s := (Finset.univ : Finset (Fin d.disk.vertexCount)))
              (f := fun v => if d.label v = d.label u then (e (inc (gamma t))).weight v else 0)
              (fun v _ => by split_ifs; exact (e (inc (gamma t))).nonneg v; exact le_rfl) (Finset.mem_univ u)
            simpa using hle
          have hface_le : (inc (gamma t)).weight δ.val / (δ.val.val.card : ℝ) ≤
              (e (inc (gamma t))).weight u := by
            rw [he_weight]
            have hle := Finset.single_le_sum
              (s := (Finset.univ : Finset (Face D)))
              (f := fun σ => if u ∈ σ.val then (inc (gamma t)).weight σ / (σ.val.card : ℝ) else 0)
              (fun σ _ => by split_ifs; exact div_nonneg ((inc (gamma t)).nonneg σ) (Nat.cast_nonneg _); exact le_rfl) (Finset.mem_univ δ.val)
            simpa only [ite_eq_left hu] using hle
          have hpos : 0 < (gamma t).weight δ :=
            lt_of_le_of_ne ((gamma t).nonneg δ)
              (Ne.symm ((mem_supportFinset_iff K (gamma t) δ).mp hδ))
          have hcard : (0 : ℝ) < (δ.val.val.card : ℝ) := by
            exact_mod_cast Finset.card_pos.mpr (D.isRelLowerSet_faces δ.val.property).1
          have hinc : (inc (gamma t)).weight δ.val = (gamma t).weight δ :=
            fullToAmbient_weight_of_property (barycentricSubdivision D)
              (fun σ : Face D => σ.val ∈ L.faces) (gamma t) δ.val δ.property
          rw [hinc] at hface_le
          have hdiv := div_pos hpos hcard
          linarith
        have hsupport_label_singleton (t : unitInterval) (a : ArcVertex S x R)
            (ht : bc.arcWord.loop t = realizationVertex (arcComplex S x R) a
              ((arcComplex S x R).singleton_mem a))
            (δ : {σ : Face D // σ.val ∈ L.faces})
            (hδ : δ ∈ supportFinset K (gamma t)) : δ.val.val.image d.label = {a} := by
          have hsub : δ.val.val.image d.label ⊆ {a} := by
            apply hpositive_label_confinement t {a} _ δ hδ
            rw [ht]
            intro w hw
            have hwa : a ≠ w := by
              intro h
              exact hw (Finset.mem_singleton.mpr h.symm)
            exact faceInclusion_weight_of_not_mem (arcComplex S x R) {a}
              ((arcComplex S x R).singleton_mem a) _ w hw
          apply Finset.eq_of_subset_of_card_le hsub
          simpa using Nat.succ_le_of_lt (Finset.card_pos.mpr (hlabel_face δ.val).1)
        have hsupport_singleton (y : RealizationPoint K)
            (δ : {σ : Face D // σ.val ∈ L.faces})
            (hy : supportFinset K y = {δ}) :
            y = realizationVertex K δ (K.singleton_mem δ) := by
          have hz (w : {σ : Face D // σ.val ∈ L.faces}) (hw : w ≠ δ) : y.weight w = 0 := by
            by_contra hn
            have hm := (mem_supportFinset_iff K y w).mpr hn
            rw [hy] at hm
            exact hw (Finset.mem_singleton.mp hm)
          have hsum : ∑ w, y.weight w = 1 := by
            obtain ⟨ρ, hρ, hρz, hρs⟩ := y.liesInFace
            have heq : (∑ w ∈ ρ, y.weight w) = ∑ w, y.weight w := by
              apply Finset.sum_subset (Finset.subset_univ _)
              intro w _ hw
              exact hρz w hw
            exact heq.symm.trans hρs
          have hδ : y.weight δ = 1 := by
            rw [Finset.sum_eq_single δ] at hsum
            · exact hsum
            · intro w _ hw
              exact hz w hw
            · simp
          apply RealizationPoint.ext
          funext w
          rw [realizationVertex_weight]
          by_cases hw : w = δ
          · subst w
            simp [hδ]
          · rw [ite_eq_right hw, hz w hw]
        have hnonvertex_card (t : unitInterval)
            (ht : ∀ δ : {σ : Face D // σ.val ∈ L.faces},
              gamma t ≠ realizationVertex K δ (K.singleton_mem δ)) :
            (supportFinset K (gamma t)).card = 2 := by
          have hb := hflag_card _ (supportFinset_mem_faces K (gamma t))
          have hp := Finset.card_pos.mpr (supportFinset_nonempty K (gamma t))
          rcases Nat.eq_or_lt_of_le hb with h | h
          · exact h
          · have hc : (supportFinset K (gamma t)).card = 1 :=
              Nat.le_antisymm (Nat.le_of_lt_succ h) hp
            obtain ⟨δ, hδ⟩ := Finset.card_eq_one.mp hc
            exact False.elim (ht δ (hsupport_singleton _ δ hδ))
        have hvertex_fiber_finite (δ : {σ : Face D // σ.val ∈ L.faces}) :
            (gamma ⁻¹' {realizationVertex K δ (K.singleton_mem δ)}).Finite := by
          by_cases hn : (gamma ⁻¹' {realizationVertex K δ (K.singleton_mem δ)}).Nonempty
          · obtain ⟨t, ht⟩ := hn
            apply (Set.toFinite ({t, 0, 1} : Set unitInterval)).subset
            intro u hu
            have heq : gamma u = gamma t := hu.trans ht.symm
            rcases (hgamma_fibers u t).mp heq with rfl | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
          · have he : gamma ⁻¹' {realizationVertex K δ (K.singleton_mem δ)} = ∅ :=
              Set.not_nonempty_iff_eq_empty.mp hn
            rw [he]
            exact Set.finite_empty
        have hinterval_flag (a b : unitInterval) (hab : a < b)
            (hno : ∀ t ∈ Set.Ioo a b,
              ∀ δ : {σ : Face D // σ.val ∈ L.faces},
                gamma t ≠ realizationVertex K δ (K.singleton_mem δ)) :
            ∃ Γ : Finset {σ : Face D // σ.val ∈ L.faces},
              Γ ∈ K.faces ∧ Γ.card = 2 ∧
              (∀ t ∈ Set.Ioo a b, supportFinset K (gamma t) = Γ) ∧
              (∀ t ∈ Set.Icc a b, gamma t ∈ CurveComplex.faceCarrier K Γ) := by
          obtain ⟨t₀, ht₀a, ht₀b⟩ := exists_between hab
          let Γ := supportFinset K (gamma t₀)
          have hΓ : Γ ∈ K.faces := supportFinset_mem_faces K (gamma t₀)
          have hΓcard : Γ.card = 2 := hnonvertex_card t₀ (hno t₀ ⟨ht₀a, ht₀b⟩)
          let U : Finset {σ : Face D // σ.val ∈ L.faces} → Set unitInterval :=
            fun Δ => {t | ∀ δ ∈ Δ, 0 < (gamma t).weight δ}
          have hU (Δ : Finset {σ : Face D // σ.val ∈ L.faces}) : IsOpen (U Δ) := by
            have heq : U Δ = ⋂ δ ∈ Δ, {t | 0 < (gamma t).weight δ} := by ext t; simp [U]
            rw [heq]
            exact isOpen_biInter_finset fun δ _ =>
              isOpen_lt continuous_const ((continuous_weight K δ).comp gamma.continuous)
          have hUsupport (Δ : Finset {σ : Face D // σ.val ∈ L.faces}) (t : unitInterval)
              (ht : t ∈ U Δ) : Δ ⊆ supportFinset K (gamma t) := by
            intro δ hδ
            exact (mem_supportFinset_iff K (gamma t) δ).mpr (ne_of_gt (ht δ hδ))
          have hUeq (Δ : Finset {σ : Face D // σ.val ∈ L.faces}) (hc : Δ.card = 2)
              (t : unitInterval) (ht : t ∈ U Δ) : supportFinset K (gamma t) = Δ := by
            apply (Finset.eq_of_subset_of_card_le (hUsupport Δ t ht) ?_).symm
            rw [hc]
            exact hflag_card _ (supportFinset_mem_faces K (gamma t))
          let V : Set unitInterval := ⋃ Δ : {Δ : Finset {σ : Face D // σ.val ∈ L.faces} //
            Δ ∈ K.faces ∧ Δ.card = 2 ∧ Δ ≠ Γ}, U Δ.val
          have hV : IsOpen V := isOpen_iUnion fun Δ => hU Δ.val
          have hdisj : Disjoint (U Γ) V := by
            apply Set.disjoint_left.mpr
            intro t ht hv
            obtain ⟨Δ, hΔ⟩ := Set.mem_iUnion.mp hv
            exact Δ.property.2.2 ((hUeq Δ.val Δ.property.2.1 t hΔ).symm.trans
              (hUeq Γ hΓcard t ht))
          have hcover : Set.Ioo a b ⊆ U Γ ∪ V := by
            intro t ht
            let Δ := supportFinset K (gamma t)
            have hΔ : t ∈ U Δ := by
              intro δ hδ
              exact lt_of_le_of_ne ((gamma t).nonneg δ)
                (Ne.symm ((mem_supportFinset_iff K (gamma t) δ).mp hδ))
            by_cases heq : Δ = Γ
            · exact Or.inl (heq ▸ hΔ)
            · exact Or.inr (Set.mem_iUnion.mpr
                ⟨⟨Δ, supportFinset_mem_faces K (gamma t), hnonvertex_card t (hno t ht), heq⟩, hΔ⟩)
          have hne : (Set.Ioo a b ∩ U Γ).Nonempty := by
            refine ⟨t₀, ⟨ht₀a, ht₀b⟩, ?_⟩
            intro δ hδ
            exact lt_of_le_of_ne ((gamma t₀).nonneg δ)
              (Ne.symm ((mem_supportFinset_iff K (gamma t₀) δ).mp hδ))
          have hall : Set.Ioo a b ⊆ U Γ :=
            IsPreconnected.subset_left_of_subset_union (hU Γ) hV hdisj hcover hne isPreconnected_Ioo
          have hsame : ∀ t ∈ Set.Ioo a b, supportFinset K (gamma t) = Γ :=
            fun t ht => hUeq Γ hΓcard t (hall ht)
          refine ⟨Γ, hΓ, hΓcard, hsame, ?_⟩
          have hc : IsClosed (gamma ⁻¹' CurveComplex.faceCarrier K Γ) :=
            (isClosed_faceCarrier K Γ).preimage gamma.continuous
          have hsub : Set.Ioo a b ⊆ gamma ⁻¹' CurveComplex.faceCarrier K Γ := by
            intro t ht
            apply (mem_faceCarrier_iff_support_subset K Γ (gamma t)).mpr
            exact (hsame t ht).subset
          have hallclosed := hc.closure_subset_iff.mpr hsub
          rw [closure_Ioo (ne_of_lt hab)] at hallclosed
          exact hallclosed
        let vertexTimes : Set unitInterval := ⋃ δ : {σ : Face D // σ.val ∈ L.faces},
          gamma ⁻¹' {realizationVertex K δ (K.singleton_mem δ)}
        have hvertexTimes : vertexTimes.Finite := Set.finite_iUnion hvertex_fiber_finite
        let cuts : Finset unitInterval :=
          insert 0 (insert 1 (hvertexTimes.toFinset ∪ Finset.univ.image d.wordTimes))
        have hcut0 : (0 : unitInterval) ∈ cuts := Finset.mem_insert_self _ _
        have hcut1 : (1 : unitInterval) ∈ cuts :=
          Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        have hword_cut (k : Fin (bc.arcWord.edgeCount + 2)) : d.wordTimes k ∈ cuts :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)))
        have hvertex_cut (t : unitInterval) (δ : {σ : Face D // σ.val ∈ L.faces})
            (ht : gamma t = realizationVertex K δ (K.singleton_mem δ)) : t ∈ cuts :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_union_left _ (hvertexTimes.mem_toFinset.mpr (Set.mem_iUnion.mpr ⟨δ, ht⟩))))
        have hcutspos : 0 < cuts.card := Finset.card_pos.mpr ⟨0, hcut0⟩
        let r := cuts.card - 1
        have hcuts_card : cuts.card = r + 1 := (Nat.sub_add_cancel hcutspos).symm
        let a : Fin (r + 1) ↪o unitInterval := cuts.orderEmbOfFin hcuts_card
        have ha_mem (k : Fin (r + 1)) : a k ∈ cuts := cuts.orderEmbOfFin_mem hcuts_card k
        have ha_range (t : unitInterval) (ht : t ∈ cuts) : ∃ k, a k = t := by
          have h := cuts.range_orderEmbOfFin hcuts_card
          have ht' : t ∈ Set.range a := h.symm ▸ ht
          exact ht'
        have ha0 : a 0 = 0 := by
          obtain ⟨k, hk⟩ := ha_range 0 hcut0
          apply le_antisymm _ bot_le
          change a 0 ≤ 0
          rw [← hk]
          exact a.monotone (Fin.zero_le k)
        have ha1 : a (Fin.last r) = 1 := by
          obtain ⟨k, hk⟩ := ha_range 1 hcut1
          apply le_antisymm le_top
          change 1 ≤ a (Fin.last r)
          rw [← hk]
          exact a.monotone (Fin.le_last k)
        have hno_cut (i : Fin r) (t : unitInterval)
            (ht : t ∈ Set.Ioo (a i.castSucc) (a i.succ)) : t ∉ cuts := by
          intro hc
          obtain ⟨k, rfl⟩ := ha_range t hc
          have h1 : i.val < k.val := a.lt_iff_lt.mp ht.1
          have h2 : k.val < i.val + 1 := a.lt_iff_lt.mp ht.2
          exact Nat.not_lt_of_ge (Nat.succ_le_of_lt h1) h2
        have hcut_flag (i : Fin r) :
            ∃ Γ : Finset {σ : Face D // σ.val ∈ L.faces},
              Γ ∈ K.faces ∧ Γ.card = 2 ∧
              (∀ t ∈ Set.Ioo (a i.castSucc) (a i.succ), supportFinset K (gamma t) = Γ) ∧
              (∀ t ∈ Set.Icc (a i.castSucc) (a i.succ), gamma t ∈ CurveComplex.faceCarrier K Γ) := by
          apply hinterval_flag (a i.castSucc) (a i.succ) (a.strictMono (Fin.castSucc_lt_succ (i := i)))
          intro t ht δ heq
          exact hno_cut i t ht (hvertex_cut t δ heq)
        have hcut_word_piece (i : Fin r) :
            ∃ k : Fin (bc.arcWord.edgeCount + 1),
              d.wordTimes k.castSucc ≤ a i.castSucc ∧ a i.succ ≤ d.wordTimes k.succ := by
          let eligible : Finset (Fin (bc.arcWord.edgeCount + 2)) :=
            Finset.univ.filter (fun k => d.wordTimes k ≤ a i.castSucc)
          have hz : (0 : Fin (bc.arcWord.edgeCount + 2)) ∈ eligible := by
            simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [d.wordTimes_zero]
            exact bot_le
          let k := eligible.max' ⟨0, hz⟩
          have hk := Finset.mem_filter.mp (Finset.max'_mem eligible ⟨0, hz⟩)
          have hmax (l : Fin (bc.arcWord.edgeCount + 2)) (hl : d.wordTimes l ≤ a i.castSucc) : l ≤ k :=
            Finset.le_max' eligible l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
          have hkne : k ≠ Fin.last (bc.arcWord.edgeCount + 1) := by
            intro h
            have h1 : (1 : unitInterval) ≤ a i.castSucc := by
              have hh : d.wordTimes k ≤ a i.castSucc := hk.2
              simpa only [h, d.wordTimes_one] using hh
            have hlt := a.strictMono (Fin.castSucc_lt_succ (i := i))
            exact (not_lt_of_ge h1) (lt_of_lt_of_le hlt le_top)
          have hkv : k.val < bc.arcWord.edgeCount + 1 := by
            apply lt_of_le_of_ne (Nat.le_of_lt_succ k.isLt)
            intro heq
            exact hkne (Fin.ext heq)
          let l : Fin (bc.arcWord.edgeCount + 1) := ⟨k.val, hkv⟩
          have hlk : l.castSucc = k := Fin.ext rfl
          have hright : a i.castSucc < d.wordTimes l.succ := by
            apply lt_of_not_ge
            intro hle
            have hh := hmax l.succ hle
            have hlt : k < l.succ := by rw [← hlk]; exact Fin.castSucc_lt_succ
            exact (not_le_of_gt hlt) hh
          refine ⟨l, ?_, ?_⟩
          · rw [hlk]
            exact hk.2
          · apply le_of_not_gt
            intro hlt
            exact hno_cut i (d.wordTimes l.succ) ⟨hright, hlt⟩ (hword_cut l.succ)
        have hword_vertex (i : Fin (bc.arcWord.edgeCount + 1)) :
            bc.arcWord.loop (d.wordTimes i.succ) = bc.arcWord.point i := by
          rw [← (d.wordPieceTime i).target]
          refine Fin.cases ?_ (fun k => ?_) i
          · exact d.wordPiece_constant 1
          · rw [d.wordPiece_edge]
            exact (bc.arcWord.edge k).target
        have hword_vertex_labels (i : Fin (bc.arcWord.edgeCount + 1))
            (δ : {σ : Face D // σ.val ∈ L.faces})
            (hδ : δ ∈ supportFinset K (gamma (d.wordTimes i.succ))) :
            δ.val.val.image d.label = {bc.arcLabel (bc.arcWord.vertex i)} := by
          apply hsupport_label_singleton _ _ _ δ hδ
          rw [hword_vertex, bc.arcWord.point_eq]
        have hword_piece_support (k : Fin (bc.arcWord.edgeCount + 1)) :
            ∃ τ : Finset (ArcVertex S x R), τ.Nonempty ∧
              (∀ t : unitInterval, bc.arcWord.loop (d.wordPieceTime k t) ∈
                CurveComplex.faceCarrier (arcComplex S x R) τ) ∧
              ((k = 0 ∧ τ = {bc.arcLabel (bc.arcWord.vertex 0)}) ∨
                ∃ l : Fin bc.arcWord.edgeCount, k = l.succ ∧
                  τ = {bc.arcLabel (bc.arcWord.vertex l.castSucc), bc.arcLabel (bc.arcWord.vertex l.succ)}) := by
          refine Fin.cases ?_ (fun l => ?_) k
          · refine ⟨{bc.arcLabel (bc.arcWord.vertex 0)}, Finset.singleton_nonempty _, ?_, Or.inl ⟨rfl, rfl⟩⟩
            intro t w hw
            rw [d.wordPiece_constant, bc.arcWord.point_eq, realizationVertex_weight]
            exact ite_eq_right (fun heq => hw (Finset.mem_singleton.mpr heq))
          · refine ⟨{bc.arcLabel (bc.arcWord.vertex l.castSucc), bc.arcLabel (bc.arcWord.vertex l.succ)},
              Finset.insert_nonempty _ _, ?_, Or.inr ⟨l, rfl, rfl⟩⟩
            intro t w hw
            rw [d.wordPiece_edge, bc.arcWord.edge_weight]
            have hleft : bc.arcLabel (bc.arcWord.vertex l.castSucc) ≠ w := by
              intro heq
              exact hw (Finset.mem_insert.mpr (Or.inl heq.symm))
            have hright : bc.arcLabel (bc.arcWord.vertex l.succ) ≠ w := by
              intro heq
              exact hw (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr heq.symm)))
            simp only [ite_eq_right hleft, ite_eq_right hright, mul_zero, add_zero]
        have hleast (Γ : Finset {σ : Face D // σ.val ∈ L.faces}) (hΓ : Γ ∈ K.faces) :
            ∃ δ₀ ∈ Γ, ∀ η ∈ Γ, δ₀.val.val ⊆ η.val.val := by
          have hne : Γ.Nonempty := Finset.image_nonempty.mp hΓ.1
          obtain ⟨δ₀, hδ₀, hmin⟩ := Γ.exists_min_image (fun δ => δ.val.val.card) hne
          refine ⟨δ₀, hδ₀, ?_⟩
          intro η hη
          rcases hΓ.2 δ₀.val (Finset.mem_image.mpr ⟨δ₀, hδ₀, rfl⟩)
              η.val (Finset.mem_image.mpr ⟨η, hη, rfl⟩) with h | h
          · exact h
          · exact (Finset.eq_of_subset_of_card_le h (hmin η hη)).symm.subset
        have hclosed_support (b : C(RealizationPoint K, RealizationPoint (curveComplex S 0)))
            (hb : ∀ (Γ : Finset {σ : Face D // σ.val ∈ L.faces}) (hΓ : Γ ∈ K.faces),
              ∀ δ₀ ∈ Γ, (∀ η ∈ Γ, δ₀.val.val ⊆ η.val.val) →
                ∀ y : FiniteSimplex Γ, b (faceInclusion K Γ hΓ y) ∈
                  fullSupportLocus (curveComplex S 0) (P δ₀.val))
            (Γ : Finset {σ : Face D // σ.val ∈ L.faces}) (hΓ : Γ ∈ K.faces)
            (δ₀ : {σ : Face D // σ.val ∈ L.faces}) (hδ₀ : δ₀ ∈ Γ)
            (hmin : ∀ η ∈ Γ, δ₀.val.val ⊆ η.val.val)
            (y : RealizationPoint K) (hy : y ∈ CurveComplex.faceCarrier K Γ) :
            b y ∈ fullSupportLocus (curveComplex S 0) (P δ₀.val) := by
          rw [faceCarrier_eq_range_faceInclusion K Γ hΓ] at hy
          obtain ⟨u, rfl⟩ := hy
          exact hb Γ hΓ δ₀ hδ₀ hmin u
        have hcommon_carrier (Γ : Finset {σ : Face D // σ.val ∈ L.faces})
            (hΓ : Γ ∈ K.faces) (y : RealizationPoint K)
            (hy : y ∈ CurveComplex.faceCarrier K Γ)
            (δ : {σ : Face D // σ.val ∈ L.faces}) (hδ : δ ∈ supportFinset K y)
            (η : {σ : Face D // σ.val ∈ L.faces}) (hmin : ∀ θ ∈ Γ, η.val.val ⊆ θ.val.val) :
            fullSupportLocus (curveComplex S 0) (P δ.val) ⊆
              fullSupportLocus (curveComplex S 0) (P η.val) := by
          have hm := (mem_faceCarrier_iff_support_subset K Γ y).mp hy hδ
          intro z hz w hw
          exact hz w (fun hp => hw (hantitone η.val δ.val (hmin δ hm) w hp))
        have hoffset_mono : Monotone bc.offset := by
          apply Fin.monotone_iff_le_succ.mpr
          intro k
          rw [bc.offset_step]
          exact Nat.le_add_right _ _
        have hoffset_bound (k : Fin (bc.curveWord.edgeCount + 1)) :
            bc.offset k ≤ bc.arcWord.edgeCount := by
          rw [← bc.offset_last]
          exact hoffset_mono (Fin.le_last k)
        have hzero_word_blocks (hm : bc.arcWord.edgeCount = 0) :
            ∀ k : Fin bc.curveWord.edgeCount, bc.blockLength k = 0 := by
          intro k
          have h0 : bc.offset k.succ = 0 := Nat.eq_zero_of_le_zero (by simpa only [hm] using hoffset_bound k.succ)
          rw [bc.offset_step] at h0
          exact (Nat.add_eq_zero_iff.mp h0).2
        have hedge_occurrence (i : Fin bc.arcWord.edgeCount) :
            ∃ (k : Fin bc.curveWord.edgeCount) (j : Fin (bc.blockLength k)),
              bc.offset k.castSucc + j.val = i.val ∧
              bc.arcLabel (bc.arcWord.vertex i.castSucc) = bc.block k j.castSucc ∧
              bc.arcLabel (bc.arcWord.vertex i.succ) = bc.block k j.succ := by
          let eligible : Finset (Fin (bc.curveWord.edgeCount + 1)) :=
            Finset.univ.filter (fun k => bc.offset k ≤ i.val)
          have hz : (0 : Fin (bc.curveWord.edgeCount + 1)) ∈ eligible := by
            simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [bc.offset_zero]
            exact Nat.zero_le _
          let k := eligible.max' ⟨0, hz⟩
          have hk : bc.offset k ≤ i.val := (Finset.mem_filter.mp (Finset.max'_mem eligible ⟨0, hz⟩)).2
          have hmax (l : Fin (bc.curveWord.edgeCount + 1)) (hl : bc.offset l ≤ i.val) : l ≤ k :=
            Finset.le_max' eligible l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
          have hkne : k ≠ Fin.last bc.curveWord.edgeCount := by
            intro h
            rw [h, bc.offset_last] at hk
            exact (Nat.not_le_of_lt i.isLt) hk
          have hkv : k.val < bc.curveWord.edgeCount := by
            apply lt_of_le_of_ne (Nat.le_of_lt_succ k.isLt)
            intro heq
            exact hkne (Fin.ext heq)
          let l : Fin bc.curveWord.edgeCount := ⟨k.val, hkv⟩
          have hlk : l.castSucc = k := Fin.ext rfl
          have hright : i.val < bc.offset l.succ := by
            apply Nat.lt_of_not_ge
            intro hle
            have hh := hmax l.succ hle
            have hlt : k < l.succ := by rw [← hlk]; exact Fin.castSucc_lt_succ
            exact (not_le_of_gt hlt) hh
          have hleft : bc.offset l.castSucc ≤ i.val := by simpa only [hlk] using hk
          have hbound : i.val - bc.offset l.castSucc < bc.blockLength l := by
            apply Nat.sub_lt_left_of_lt_add hleft
            simpa only [bc.offset_step] using hright
          let j : Fin (bc.blockLength l) := ⟨i.val - bc.offset l.castSucc, hbound⟩
          have hi : bc.offset l.castSucc + j.val = i.val := Nat.add_sub_of_le hleft
          refine ⟨l, j, hi, ?_, ?_⟩
          · obtain ⟨q, hq, hlabel⟩ := bc.block_occurrences l j.castSucc
            have heq : q = i.castSucc := Fin.ext (hq.trans hi)
            exact heq ▸ hlabel
          · obtain ⟨q, hq, hlabel⟩ := bc.block_occurrences l j.succ
            have heq : q = i.succ := by
              apply Fin.ext
              exact hq.trans ((Nat.add_assoc _ _ _).symm.trans (congrArg (fun n => n + 1) hi))
            exact heq ▸ hlabel
        have hjunction_occurrence (k : Fin bc.curveWord.edgeCount) :
            ∃ i : Fin (bc.arcWord.edgeCount + 1),
              i.val = bc.offset k.succ ∧ bc.arcLabel (bc.arcWord.vertex i) = bc.junction k.succ := by
          obtain ⟨i, hi, hl⟩ := bc.block_occurrences k (Fin.last (bc.blockLength k))
          refine ⟨i, ?_, ?_⟩
          · exact hi.trans (bc.offset_step k).symm
          · exact hl.trans (bc.block_end k)
        have timing :
            ∀ (n : ℕ) (p : Fin (n + 1) → RealizationPoint (curveComplex S 0))
              (e : (k : Fin n) → Path (p k.castSucc) (p k.succ)),
              ∃ τ : Fin (n + 2) → EdgeTime,
                StrictMono (fun k => (τ k : ℝ)) ∧
                τ 0 = 0 ∧ τ (Fin.last (n + 1)) = 1 ∧
                (∀ t : EdgeTime,
                  (Path.concat p e) (Icc.convexComb (τ 0) (τ 1) t) = p 0) ∧
                ∀ (k : Fin n) (t : EdgeTime),
                  (Path.concat p e)
                    (Icc.convexComb (τ k.succ.castSucc) (τ k.succ.succ) t) = e k t := by
          let half : EdgeTime → EdgeTime := fun t =>
            ⟨(t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
          have half_affine (a b t : EdgeTime) :
              Icc.convexComb (half a) (half b) t = half (Icc.convexComb a b t) := by
            apply Subtype.ext
            dsimp [half, Icc.convexComb]
            ring
          have first_half {a b c : RealizationPoint (curveComplex S 0)} (f : Path a b) (g : Path b c) (t : EdgeTime) :
              (f.trans g) (half t) = f t := by
            rw [← Path.extend_extends' (f.trans g) (half t)]
            rw [Path.extend_trans_of_le_half _ _ (by dsimp [half]; linarith [t.property.2])]
            have he : (2 : ℝ) * (half t : ℝ) = (t : ℝ) := by dsimp [half]; ring
            rw [he, Path.extend_extends']
          have second_half {a b c : RealizationPoint (curveComplex S 0)} (f : Path a b) (g : Path b c) (t : EdgeTime) :
              (f.trans g) (Icc.convexComb (half 1) 1 t) = g t := by
            rw [← Path.extend_extends' (f.trans g) (Icc.convexComb (half 1) 1 t)]
            rw [Path.extend_trans_of_half_le _ _ (by
              dsimp [half, Icc.convexComb]; norm_num; linarith [t.property.1])]
            have he : (2 : ℝ) * (Icc.convexComb (half 1) 1 t : ℝ) - 1 = (t : ℝ) := by
              dsimp [half, Icc.convexComb]
              norm_num
              ring
            rw [he, Path.extend_extends']
          intro n
          induction n with
          | zero =>
              intro p e
              refine ⟨fun k => if k = 0 then 0 else 1, ?_, by simp, by simp, ?_, ?_⟩
              · apply Fin.strictMono_iff_lt_succ.mpr
                intro k
                have hk : k = 0 := Fin.eq_zero k
                subst k
                norm_num
              · intro t
                simp
              · intro k
                exact Fin.elim0 k
          | succ n ih =>
              intro p e
              obtain ⟨τ, hmono, hz, ho, hc, he⟩ :=
                ih (p ∘ Fin.castSucc) (fun k => e k.castSucc)
              let τ' : Fin (n + 3) → EdgeTime := Fin.lastCases 1 (fun k => half (τ k))
              have hcast (k : Fin (n + 2)) : τ' k.castSucc = half (τ k) := by
                simp [τ']
              have hlast : τ' (Fin.last (n + 2)) = 1 := by simp [τ']
              refine ⟨τ', ?_, ?_, hlast, ?_, ?_⟩
              · apply Fin.strictMono_iff_lt_succ.mpr
                intro k
                refine Fin.lastCases ?_ (fun j => ?_) k
                · rw [hcast, show (Fin.last (n + 1)).succ = Fin.last (n + 2) from rfl,
                    hlast, ho]
                  norm_num [half]
                · simp only [← Fin.castSucc_succ, hcast]
                  dsimp [half]
                  exact div_lt_div_of_pos_right (hmono (Fin.castSucc_lt_succ (i := j))) (by norm_num)
              · rw [show (0 : Fin (n + 3)) = (0 : Fin (n + 2)).castSucc from rfl,
                    hcast, hz]
                apply Subtype.ext
                dsimp [half]
                norm_num
              · intro t
                have hfirst0 : τ' 0 = half (τ 0) := hcast 0
                have hfirst1 : τ' 1 = half (τ 1) := hcast 1
                rw [hfirst0, hfirst1, half_affine, Path.concat_succ]
                exact (first_half (Path.concat (p ∘ Fin.castSucc) (fun k => e k.castSucc))
                  (e (Fin.last n)) _).trans (hc t)
              · intro k t
                refine Fin.lastCases ?_ (fun j => ?_) k
                · simp only [Fin.succ_last, hcast, hlast, ho]
                  rw [Path.concat_succ]
                  exact second_half (Path.concat (p ∘ Fin.castSucc) (fun k => e k.castSucc))
                    (e (Fin.last n)) t
                · simp only [← Fin.castSucc_succ, hcast]
                  rw [half_affine, Path.concat_succ]
                  exact (first_half (Path.concat (p ∘ Fin.castSucc) (fun k => e k.castSucc))
                    (e (Fin.last n)) _).trans (he j t)
        have hpiece_range (k : Fin (bc.arcWord.edgeCount + 1)) :
            Set.Icc (d.wordTimes k.castSucc) (d.wordTimes k.succ) ⊆
              Set.range (d.wordPieceTime k) := by
          have h := intermediate_value_univ (0 : unitInterval) 1 (d.wordPieceTime k).continuous
          simpa only [(d.wordPieceTime k).source, (d.wordPieceTime k).target] using h
        have htraversal_labels (i : Fin r)
            (Γ : Finset {σ : Face D // σ.val ∈ L.faces})
            (hΓ : ∀ t ∈ Set.Ioo (a i.castSucc) (a i.succ), supportFinset K (gamma t) = Γ)
            (k : Fin (bc.arcWord.edgeCount + 1))
            (hk : d.wordTimes k.castSucc ≤ a i.castSucc ∧ a i.succ ≤ d.wordTimes k.succ)
            (τ : Finset (ArcVertex S x R))
            (hτ : ∀ t : unitInterval, bc.arcWord.loop (d.wordPieceTime k t) ∈
              CurveComplex.faceCarrier (arcComplex S x R) τ) :
            ∀ δ ∈ Γ, δ.val.val.image d.label ⊆ τ := by
          obtain ⟨t, ht0, ht1⟩ := exists_between (a.strictMono (Fin.castSucc_lt_succ (i := i)))
          obtain ⟨u, hu⟩ := hpiece_range k ⟨hk.1.trans ht0.le, ht1.le.trans hk.2⟩
          intro δ hδ
          refine hpositive_label_confinement t τ ?_ δ ?_
          · rw [← hu]
            exact hτ u
          · rw [hΓ t ⟨ht0, ht1⟩]
            exact hδ
        have hblock_pair_carrier (i : Fin bc.arcWord.edgeCount) :
            ∃ k : Fin bc.curveWord.edgeCount,
              CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R
                {bc.arcLabel (bc.arcWord.vertex i.castSucc), bc.arcLabel (bc.arcWord.vertex i.succ)}
                (bc.curveWord.vertex k.castSucc) := by
          obtain ⟨k, j, _, hleft, hright⟩ := hedge_occurrence i
          refine ⟨k, ?_⟩
          rw [hleft, hright]
          exact (hcarrier _ (Finset.insert_nonempty _ _) _).mp (bc.block_edge_carrier k j)
        have hinitial_curve_carrier :
            CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R
              {bc.arcLabel (bc.arcWord.vertex 0)} (bc.curveWord.vertex 0) := by
          let k : Fin bc.curveWord.edgeCount := ⟨0, bc.curve_nonempty⟩
          obtain ⟨i, hi, hl⟩ := bc.block_occurrences k 0
          have hi0 : i = 0 := by
            apply Fin.ext
            simpa only [show k.castSucc = 0 from rfl, bc.offset_zero, Fin.val_zero, Nat.add_zero] using hi
          have ha : bc.arcLabel (bc.arcWord.vertex 0) = bc.block k 0 := hi0 ▸ hl
          rw [ha]
          exact (hcarrier _ (Finset.singleton_nonempty _) _).mp (bc.block_vertex_carrier k 0)
        have htraversal_curve_carrier (i : Fin r)
            (Γ : Finset {σ : Face D // σ.val ∈ L.faces})
            (hΓ : ∀ t ∈ Set.Ioo (a i.castSucc) (a i.succ), supportFinset K (gamma t) = Γ)
            (k : Fin (bc.arcWord.edgeCount + 1))
            (hk : d.wordTimes k.castSucc ≤ a i.castSucc ∧ a i.succ ≤ d.wordTimes k.succ) :
            ∃ c : Vertex S, ∀ δ ∈ Γ, P δ.val c := by
          obtain ⟨τ, hτne, hτ, hcase⟩ := hword_piece_support k
          have hsub := htraversal_labels i Γ hΓ k hk τ hτ
          rcases hcase with ⟨rfl, rfl⟩ | ⟨l, rfl, rfl⟩
          · refine ⟨bc.curveWord.vertex 0, ?_⟩
            intro δ hδ
            exact CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier_antitone
              S x R _ _ (hsub δ hδ) _ hinitial_curve_carrier
          · obtain ⟨c, hc⟩ := hblock_pair_carrier l
            refine ⟨bc.curveWord.vertex c.castSucc, ?_⟩
            intro δ hδ
            exact CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier_antitone
              S x R _ _ (hsub δ hδ) _ hc
        have hcontract : ∀ σ : Face D,
            ContractibleSpace (RealizationPoint (fullSubcomplex (curveComplex S 0) (P σ))) := by
          intro σ
          have hdec : (instDecidableEqVertex_c0CurveToArcBoundaryCorrespondence S :
              DecidableEq (Vertex S)) = (fun a b => Quotient.decidableEq a b) :=
            Subsingleton.elim _ _
          exact Eq.mpr
            (congrArg (fun inst : DecidableEq (Vertex S) =>
              ContractibleSpace (RealizationPoint
                (@fullSubcomplex (Vertex S) inst (curveComplex S 0) (P σ)))) hdec)
            (CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.nonempty_small_faceCarrier_contractible
              S x R g hg hS hR htarget
              (σ.val.image d.label) (hlabel_face σ) (hlabel_card σ))
        let L₀ : PreAbstractSimplicialComplex (Fin d.disk.vertexCount) :=
          { faces := ∅
            isRelLowerSet_faces := by intro σ hσ; exact False.elim hσ }
        have hempty : IsEmpty (RealizationPoint (boundarySubdivision D L₀)) := by
          refine ⟨?_⟩
          intro y
          obtain ⟨Γ, hΓ, _, _⟩ := y.liesInFace
          obtain ⟨δ, hδ⟩ := (boundarySubdivision D L₀).isRelLowerSet_faces hΓ |>.1
          exact δ.property
        let := hempty
        let b₀ : C(RealizationPoint (boundarySubdivision D L₀), RealizationPoint (curveComplex S 0)) :=
          ⟨fun y => isEmptyElim y, (continuous_iff_continuousAt.mpr (fun y => isEmptyElim y))⟩
        obtain ⟨f, _, hf⟩ := C0RelativeCarrier.finite_antitone_full_carrier_relative_extension
          D d.disk.face_card L₀ (by intro σ hσ; exact False.elim hσ)
          (curveComplex S 0) P hantitone hcontract b₀
          (by intro Γ hΓ δ hδ; exact False.elim δ.property)
        let b : C(RealizationPoint K, RealizationPoint (curveComplex S 0)) :=
          f.comp ⟨inc, fullToAmbient_continuous (barycentricSubdivision D)
            (fun σ : Face D => σ.val ∈ L.faces)⟩
        have hb : ∀ (Γ : Finset {σ : Face D // σ.val ∈ L.faces}) (hΓ : Γ ∈ K.faces),
            ∀ δ₀ ∈ Γ, (∀ η ∈ Γ, δ₀.val.val ⊆ η.val.val) →
              ∀ y : FiniteSimplex Γ, b (faceInclusion K Γ hΓ y) ∈
                fullSupportLocus (curveComplex S 0) (P δ₀.val) := by
          intro Γ hΓ δ₀ hδ₀ hmin y
          have hΓ' : Γ.image Subtype.val ∈ (barycentricSubdivision D).faces := hΓ
          have himage : inc (faceInclusion K Γ hΓ y) ∈
              CurveComplex.faceCarrier (barycentricSubdivision D) (Γ.image Subtype.val) := by
            intro σ hσ
            by_cases hL : σ.val ∈ L.faces
            · rw [fullToAmbient_weight_of_property (barycentricSubdivision D)
                (fun σ : Face D => σ.val ∈ L.faces) _ σ hL]
              apply faceInclusion_weight_of_not_mem
              intro hmem
              exact hσ (Finset.mem_image.mpr ⟨⟨σ, hL⟩, hmem, rfl⟩)
            · exact fullToAmbient_weight_of_not_property (barycentricSubdivision D)
                (fun σ : Face D => σ.val ∈ L.faces) _ σ hL
          rw [faceCarrier_eq_range_faceInclusion (barycentricSubdivision D) _ hΓ'] at himage
          obtain ⟨u, hu⟩ := himage
          change f (inc (faceInclusion K Γ hΓ y)) ∈ _
          rw [← hu]
          apply hf _ hΓ' δ₀.val (Finset.mem_image.mpr ⟨δ₀, hδ₀, rfl⟩)
          intro η hη
          obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hη
          exact hmin θ hθ
        have hcarrier_contractible (δ : Face D) :
            ContractibleSpace ↥(fullSupportLocus (curveComplex S 0) (P δ)) := by
          let := hcontract δ
          exact (fullSubcomplexHomeomorphSupported (curveComplex S 0) (P δ)).symm.contractibleSpace
        let least : RealizationPoint K → {σ : Face D // σ.val ∈ L.faces} := fun y =>
          Classical.choose (hleast (supportFinset K y) (supportFinset_mem_faces K y))
        have hleast_mem (y : RealizationPoint K) : least y ∈ supportFinset K y :=
          (Classical.choose_spec (hleast (supportFinset K y) (supportFinset_mem_faces K y))).1
        have hleast_min (y : RealizationPoint K) :
            ∀ η ∈ supportFinset K y, (least y).val.val ⊆ η.val.val :=
          (Classical.choose_spec (hleast (supportFinset K y) (supportFinset_mem_faces K y))).2
        have hbpoint (y : RealizationPoint K) :
            b y ∈ fullSupportLocus (curveComplex S 0) (P (least y).val) := by
          apply hclosed_support b hb (supportFinset K y) (supportFinset_mem_faces K y)
            (least y) (hleast_mem y) (hleast_min y) y
          exact (mem_faceCarrier_iff_support_subset K _ y).mpr (Finset.Subset.refl _)
        have hvertex_supported (δ : Face D) (c : Vertex S) (hc : P δ c) :
            realizationVertex (curveComplex S 0) c ((curveComplex S 0).singleton_mem c) ∈
              fullSupportLocus (curveComplex S 0) (P δ) := by
          intro w hw
          rw [realizationVertex_weight]
          split_ifs with heq
          · exact False.elim (hw (heq.symm ▸ hc))
          · rfl
        let vertical (y : RealizationPoint K) (c : Vertex S) (hc : P (least y).val c) :
            Path (realizationVertex (curveComplex S 0) c ((curveComplex S 0).singleton_mem c)) (b y) :=
          let _ := hcarrier_contractible (least y).val
          (PathConnectedSpace.somePath
            (⟨realizationVertex (curveComplex S 0) c ((curveComplex S 0).singleton_mem c),
              hvertex_supported (least y).val c hc⟩ : fullSupportLocus (curveComplex S 0) (P (least y).val))
            ⟨b y, hbpoint y⟩).map continuous_subtype_val
        have hvertical_support (y : RealizationPoint K) (c : Vertex S) (hc : P (least y).val c)
            (s : unitInterval) : vertical y c hc s ∈
              fullSupportLocus (curveComplex S 0) (P (least y).val) := by
          exact ((PathConnectedSpace.somePath
            (⟨realizationVertex (curveComplex S 0) c ((curveComplex S 0).singleton_mem c),
              hvertex_supported (least y).val c hc⟩ : fullSupportLocus (curveComplex S 0) (P (least y).val))
            ⟨b y, hbpoint y⟩) s).property
        have hvertical_incident (y : RealizationPoint K) (c : Vertex S) (hc : P (least y).val c)
            (Γ : Finset {σ : Face D // σ.val ∈ L.faces}) (hΓ : Γ ∈ K.faces)
            (hy : y ∈ CurveComplex.faceCarrier K Γ)
            (δ₀ : {σ : Face D // σ.val ∈ L.faces})
            (hmin : ∀ η ∈ Γ, δ₀.val.val ⊆ η.val.val) (s : unitInterval) :
            vertical y c hc s ∈ fullSupportLocus (curveComplex S 0) (P δ₀.val) := by
          exact hcommon_carrier Γ hΓ y hy (least y) (hleast_mem y) δ₀ hmin
            (hvertical_support y c hc s)
        have hvertical_seam (c : Vertex S)
            (h0 : P (least (gamma 0)).val c) (h1 : P (least (gamma 1)).val c)
            (s : unitInterval) :
            vertical (gamma 0) c h0 s = vertical (gamma 1) c h1 s := by
          have hdep : ∀ (y z : RealizationPoint K) (heq : y = z)
              (hy : P (least y).val c) (hz : P (least z).val c),
              vertical y c hy s = vertical z c hz s := by
            intro y z heq hy hz
            subst z
            rfl
          exact hdep (gamma 0) (gamma 1) hgamma_seam h0 h1
        have hb_junction (k : Fin bc.curveWord.edgeCount) :
            ∃ i : Fin (bc.arcWord.edgeCount + 1), i.val = bc.offset k.succ ∧
              b (gamma (d.wordTimes i.succ)) ∈ fullSupportLocus (curveComplex S 0)
                (CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R
                  {bc.junction k.succ}) := by
          obtain ⟨i, hi, hl⟩ := hjunction_occurrence k
          refine ⟨i, hi, ?_⟩
          have heq := hword_vertex_labels i (least (gamma (d.wordTimes i.succ)))
            (hleast_mem (gamma (d.wordTimes i.succ)))
          have hb' := hbpoint (gamma (d.wordTimes i.succ))
          change b (gamma (d.wordTimes i.succ)) ∈
            fullSupportLocus (curveComplex S 0)
              (CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R
                ((least (gamma (d.wordTimes i.succ))).val.val.image d.label)) at hb'
          simpa only [heq, hl] using hb'
        have square_fill (A : Set (RealizationPoint (curveComplex S 0)))
            (hA : ContractibleSpace A) (x₀ x₁ y₀ y₁ : A)
            (lo : Path x₀ x₁) (up : Path y₀ y₁)
            (vl : Path x₀ y₀) (vr : Path x₁ y₁) :
            ∃ H : C(unitInterval × unitInterval, A),
              (∀ t, H (0,t) = lo t) ∧ (∀ t, H (1,t) = up t) ∧
              (∀ s, H (s,0) = vl s) ∧ (∀ s, H (s,1) = vr s) := by
          let _ := hA
          let SS : Fin 4 → Set (CurveComplexGenusTwo.CWHurewicz.CellSphere 2) :=
            ![{z | z.val 0 = -1}, {z | z.val 0 = 1},
              {z | z.val 1 = -1}, {z | z.val 1 = 1}]
          have hnorm (z : CurveComplexGenusTwo.CWHurewicz.CellSphere 2) : ‖z.val‖ = 1 := by
            simpa only [Metric.mem_sphere, dist_zero_right] using z.property
          have hcover : ⋃ i, SS i = Set.univ := by
            ext z
            simp only [mem_univ, iff_true]
            by_contra hn
            have hn' : ∀ i, z ∉ SS i := by simpa only [mem_iUnion, not_exists] using hn
            have hcoord (i : Fin 2) : |z.val i| ≤ 1 := by
              simpa only [Real.norm_eq_abs, hnorm z] using (norm_le_pi_norm z.val i)
            have hc0 := hcoord 0
            have hc1 := hcoord 1
            have h0 := hn' 0
            have h1 := hn' 1
            have h2 := hn' 2
            have h3 := hn' 3
            change z.val 0 ≠ -1 at h0
            change z.val 0 ≠ 1 at h1
            change z.val 1 ≠ -1 at h2
            change z.val 1 ≠ 1 at h3
            have hlt : ‖z.val‖ < 1 := by
              rw [pi_norm_lt_iff (by norm_num : (0:ℝ)<1)]
              intro i
              fin_cases i <;> simp only [Real.norm_eq_abs, abs_lt]
              · exact ⟨lt_of_le_of_ne (abs_le.mp hc0).1 (Ne.symm h0),
                  lt_of_le_of_ne (abs_le.mp hc0).2 h1⟩
              · exact ⟨lt_of_le_of_ne (abs_le.mp hc1).1 (Ne.symm h2),
                  lt_of_le_of_ne (abs_le.mp hc1).2 h3⟩
            exact (not_lt_of_ge (hnorm z).ge) hlt
          have hclosed : ∀ i, IsClosed (SS i) := by
            intro i
            fin_cases i
            · exact isClosed_eq ((continuous_apply 0).comp continuous_subtype_val) continuous_const
            · exact isClosed_eq ((continuous_apply 0).comp continuous_subtype_val) continuous_const
            · exact isClosed_eq ((continuous_apply 1).comp continuous_subtype_val) continuous_const
            · exact isClosed_eq ((continuous_apply 1).comp continuous_subtype_val) continuous_const
          let ψ : Fin 4 → C(CurveComplexGenusTwo.CWHurewicz.CellSphere 2,A) :=
            ![⟨fun z => lo.extend ((z.val 1 + 1) / 2),
                lo.continuous_extend.comp ((((continuous_apply 1).comp continuous_subtype_val).add continuous_const).div_const 2)⟩,
              ⟨fun z => up.extend ((z.val 1 + 1) / 2),
                up.continuous_extend.comp ((((continuous_apply 1).comp continuous_subtype_val).add continuous_const).div_const 2)⟩,
              ⟨fun z => vl.extend ((z.val 0 + 1) / 2),
                vl.continuous_extend.comp ((((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2)⟩,
              ⟨fun z => vr.extend ((z.val 0 + 1) / 2),
                vr.continuous_extend.comp ((((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2)⟩]
          let φ : ∀ i : Fin 4, C(SS i, A) := fun i =>
            (ψ i).comp ⟨Subtype.val, continuous_subtype_val⟩
          have hcompat : ∀ i j (z : CurveComplexGenusTwo.CWHurewicz.CellSphere 2)
              (hi : z ∈ SS i) (hj : z ∈ SS j), φ i ⟨z,hi⟩ = φ j ⟨z,hj⟩ := by
            intro i j z hi hj
            fin_cases i <;> fin_cases j <;> norm_num [SS] at hi hj
            all_goals try (exfalso; linarith only [hi,hj])
            all_goals norm_num [φ, ψ, hi, hj]
          let f : C(CurveComplexGenusTwo.CWHurewicz.CellSphere 2,A) :=
            ⟨Set.liftCover SS (fun i => φ i) hcompat hcover, by
              apply (locallyFinite_of_finite SS).continuous hcover hclosed
              intro i
              rw [continuousOn_iff_continuous_domRestrict]
              change Continuous (fun z : SS i => Set.liftCover SS (fun i => φ i) hcompat hcover z.val)
              have he : (fun z : SS i => Set.liftCover SS (fun i => φ i) hcompat hcover z.val) = φ i := by
                funext z
                exact Set.liftCover_coe z
              rw [he]
              exact (φ i).continuous⟩
          have hf (i : Fin 4) (z : CurveComplexGenusTwo.CWHurewicz.CellSphere 2)
              (hi : z ∈ SS i) : f z = φ i ⟨z,hi⟩ := by
            change Set.liftCover SS (fun i => φ i) hcompat hcover z = _
            exact Set.liftCover_of_mem hi
          obtain ⟨y, hy⟩ := (id_nullhomotopic A).comp_left f
          obtain ⟨F,hF⟩ := CurveComplexGenusTwo.CWHurewicz.cellSphereMap_extends_cellDisk
            2 f y (Classical.choice hy)
          let E (q : unitInterval × unitInterval) : Fin 2 → ℝ :=
            ![2*(q.1:ℝ)-1, 2*(q.2:ℝ)-1]
          have hE (q : unitInterval × unitInterval) : E q ∈ Metric.closedBall 0 1 := by
            rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)]
            intro i
            fin_cases i <;> change |2 * _ - 1| ≤ (1:ℝ) <;> rw [abs_le]
            · constructor <;> linarith [q.1.property.1, q.1.property.2]
            · constructor <;> linarith [q.2.property.1, q.2.property.2]
          let ec : C(unitInterval × unitInterval, CurveComplexGenusTwo.CWHurewicz.CellDisk 2) :=
            ⟨fun q => ⟨E q,hE q⟩, by
              apply Continuous.subtype_mk
              apply continuous_pi
              intro i
              fin_cases i <;> dsimp [E] <;> fun_prop⟩
          have hEsphere (q : unitInterval × unitInterval)
              (i : Fin 2) (hi : |E q i| = 1) : E q ∈ Metric.sphere 0 1 := by
            rw [Metric.mem_sphere, dist_zero_right]
            apply le_antisymm
            · simpa only [Metric.mem_closedBall, dist_zero_right] using hE q
            · have hn := norm_le_pi_norm (E q) i
              simpa only [Real.norm_eq_abs, hi] using hn
          have heq (q : unitInterval × unitInterval) (i : Fin 4)
              (hs : E q ∈ Metric.sphere 0 1) (hside : (⟨E q,hs⟩ : CurveComplexGenusTwo.CWHurewicz.CellSphere 2) ∈ SS i) :
              (F.comp ec) q = φ i ⟨⟨E q,hs⟩,hside⟩ := (hF ⟨E q,hs⟩).trans (hf i _ hside)
          refine ⟨F.comp ec, ?_, ?_, ?_, ?_⟩
          · intro t
            have hs : E (0,t) ∈ Metric.sphere 0 1 := hEsphere (0,t) 0 (by norm_num [E])
            rw [heq (0,t) 0 hs (by norm_num [SS,E])]
            change lo.extend ((2*(t:ℝ)-1+1)/2) = lo t
            rw [show (2*(t:ℝ)-1+1)/2 = (t:ℝ) by ring, Path.extend_extends']
          · intro t
            have hs : E (1,t) ∈ Metric.sphere 0 1 := hEsphere (1,t) 0 (by norm_num [E])
            rw [heq (1,t) 1 hs (by norm_num [SS,E])]
            change up.extend ((2*(t:ℝ)-1+1)/2) = up t
            rw [show (2*(t:ℝ)-1+1)/2 = (t:ℝ) by ring, Path.extend_extends']
          · intro s
            have hs : E (s,0) ∈ Metric.sphere 0 1 := hEsphere (s,0) 1 (by norm_num [E])
            rw [heq (s,0) 2 hs (by norm_num [SS,E])]
            change vl.extend ((2*(s:ℝ)-1+1)/2) = vl s
            rw [show (2*(s:ℝ)-1+1)/2 = (s:ℝ) by ring, Path.extend_extends']
          · intro s
            have hs : E (s,1) ∈ Metric.sphere 0 1 := hEsphere (s,1) 1 (by norm_num [E])
            rw [heq (s,1) 3 hs (by norm_num [SS,E])]
            change vr.extend ((2*(s:ℝ)-1+1)/2) = vr s
            rw [show (2*(s:ℝ)-1+1)/2 = (s:ℝ) by ring, Path.extend_extends']
        have grid : ∀ (n : ℕ)
            (xs ys : Fin (n+1) → RealizationPoint (curveComplex S 0))
            (lo : ∀ i : Fin n, Path (xs i.castSucc) (xs i.succ))
            (up : ∀ i : Fin n, Path (ys i.castSucc) (ys i.succ))
            (vs : ∀ i : Fin (n+1), Path (xs i) (ys i))
            (cells : Fin n → C(unitInterval × unitInterval, RealizationPoint (curveComplex S 0))),
            (∀ i, (∀ t, cells i (0,t) = lo i t) ∧ (∀ t, cells i (1,t) = up i t) ∧
              (∀ s, cells i (s,0) = vs i.castSucc s) ∧ (∀ s, cells i (s,1) = vs i.succ s)) →
            ∃ H : C(unitInterval × unitInterval, RealizationPoint (curveComplex S 0)),
              (∀ t, H (0,t) = Path.concat xs lo t) ∧
              (∀ t, H (1,t) = Path.concat ys up t) ∧
              (∀ s, H (s,0) = vs 0 s) ∧ (∀ s, H (s,1) = vs (Fin.last n) s) := by
          intro n
          induction n with
          | zero =>
            intro xs ys lo up vs cells hcells
            refine ⟨⟨fun q => vs 0 q.1, (vs 0).continuous.comp continuous_fst⟩, ?_, ?_, ?_, ?_⟩
            · intro t; simp only [ContinuousMap.coe_mk, Path.source, Path.concat_zero, Path.refl_apply]
            · intro t; simp only [ContinuousMap.coe_mk, Path.target, Path.concat_zero, Path.refl_apply]
            · intro s; rfl
            · intro s; rfl
          | succ n ih =>
            intro xs ys lo up vs cells hcells
            obtain ⟨F,hF0,hF1,hFl,hFr⟩ := ih (xs ∘ Fin.castSucc) (ys ∘ Fin.castSucc)
              (fun i => lo i.castSucc) (fun i => up i.castSucc) (fun i => vs i.castSucc)
              (fun i => cells i.castSucc) (fun i => hcells i.castSucc)
            let G := cells (Fin.last n)
            have hG0 := (hcells (Fin.last n)).1
            have hG1 := (hcells (Fin.last n)).2.1
            have hGl := (hcells (Fin.last n)).2.2.1
            have hGr := (hcells (Fin.last n)).2.2.2
            let left (q : unitInterval × unitInterval) : unitInterval × unitInterval :=
              (q.1, Set.projIcc 0 1 zero_le_one (2*(q.2:ℝ)))
            let right (q : unitInterval × unitInterval) : unitInterval × unitInterval :=
              (q.1, Set.projIcc 0 1 zero_le_one (2*(q.2:ℝ)-1))
            have hleft : Continuous left := continuous_fst.prodMk
              (continuous_projIcc.comp (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))
            have hright : Continuous right := continuous_fst.prodMk
              (continuous_projIcc.comp ((continuous_const.mul
                (continuous_subtype_val.comp continuous_snd)).sub continuous_const))
            let H : C(unitInterval × unitInterval, RealizationPoint (curveComplex S 0)) :=
              ⟨fun q => if (q.2:ℝ) ≤ 1/2 then F (left q) else G (right q), by
                apply Continuous.if_le (F.continuous.comp hleft) (G.continuous.comp hright)
                  (continuous_subtype_val.comp continuous_snd) continuous_const
                intro q hq
                change (q.2:ℝ) = 1/2 at hq
                change F (left q) = G (right q)
                have hl : left q = (q.1,1) := by
                  change (q.1, Set.projIcc 0 1 zero_le_one (2*(q.2:ℝ))) = _
                  rw [show 2*(q.2:ℝ) = 1 by linarith only [hq], Set.projIcc_right]
                  rfl
                have hr : right q = (q.1,0) := by
                  change (q.1, Set.projIcc 0 1 zero_le_one (2*(q.2:ℝ)-1)) = _
                  rw [show 2*(q.2:ℝ)-1 = 0 by linarith only [hq], Set.projIcc_left]
                  rfl
                rw [hl,hr,hFr]
                exact (hGl q.1).symm⟩
            refine ⟨H, ?_, ?_, ?_, ?_⟩
            · intro t
              change (if (t:ℝ) ≤ 1/2 then F (0, Set.projIcc 0 1 zero_le_one (2*(t:ℝ)))
                else G (0, Set.projIcc 0 1 zero_le_one (2*(t:ℝ)-1))) = _
              simp only [hF0, show ∀ u, G (0,u) = lo (Fin.last n) u from hG0, Path.concat_succ]
              rfl
            · intro t
              change (if (t:ℝ) ≤ 1/2 then F (1, Set.projIcc 0 1 zero_le_one (2*(t:ℝ)))
                else G (1, Set.projIcc 0 1 zero_le_one (2*(t:ℝ)-1))) = _
              simp only [hF1, show ∀ u, G (1,u) = up (Fin.last n) u from hG1, Path.concat_succ]
              rfl
            · intro s
              change (if ((0:unitInterval):ℝ) ≤ 1/2 then F (left (s,0)) else G (right (s,0))) = _
              norm_num [left]
              exact hFl s
            · intro s
              change (if ((1:unitInterval):ℝ) ≤ 1/2 then F (left (s,1)) else G (right (s,1))) = _
              norm_num [right]
              exact hGr s
        let bp : Path (b (gamma 0)) (b (gamma 1)) :=
          { toContinuousMap := b.comp gamma, source' := rfl, target' := rfl }
        have retime_free {y₀ y₁ : RealizationPoint (curveComplex S 0)}
            (q : Path y₀ y₁) (hq : y₀ = y₁) (n : ℕ) (ts : Fin (n+1) → unitInterval)
            (h0 : ts 0 = 0) (h1 : ts (Fin.last n) = 1) :
            ContinuousMap.HomotopyWith q.toContinuousMap
              (Path.concat (q ∘ ts) (fun i => q.subpath (ts i.castSucc) (ts i.succ))).toContinuousMap
              (fun f : C(unitInterval, RealizationPoint (curveComplex S 0)) => f 0 = f 1) := by
          let F := (Path.Homotopy.concatSubpath q ts).symm
          have he : q (ts 0) = q (ts (Fin.last n)) := by
            rw [h0,h1,q.source,q.target,hq]
          let H : ContinuousMap.HomotopyWith
              (q.subpath (ts 0) (ts (Fin.last n))).toContinuousMap
              (Path.concat (q ∘ ts) (fun i => q.subpath (ts i.castSucc) (ts i.succ))).toContinuousMap
              (fun f : C(unitInterval, RealizationPoint (curveComplex S 0)) => f 0 = f 1) :=
            { toHomotopy := F.toHomotopy
              prop' := fun s => (F.source s).trans (he.trans (F.target s).symm) }
          exact H.cast (by ext t; simp only [Path.coe_toContinuousMap, Path.subpath,
            ContinuousMap.coe_mk, Function.comp_apply,h0,h1,Icc.convexComb_zero_one]) rfl
        have supported_square
            (A : Set (RealizationPoint (curveComplex S 0))) (hA : ContractibleSpace A)
            (x₀ x₁ y₀ y₁ : RealizationPoint (curveComplex S 0))
            (lo : Path x₀ x₁) (up : Path y₀ y₁) (vl : Path x₀ y₀) (vr : Path x₁ y₁)
            (hlo : ∀ t, lo t ∈ A) (hup : ∀ t, up t ∈ A)
            (hvl : ∀ t, vl t ∈ A) (hvr : ∀ t, vr t ∈ A) :
            ∃ H : C(unitInterval × unitInterval, RealizationPoint (curveComplex S 0)),
              (∀ t, H (0,t) = lo t) ∧ (∀ t, H (1,t) = up t) ∧
              (∀ s, H (s,0) = vl s) ∧ (∀ s, H (s,1) = vr s) := by
          let a₀ : A := ⟨x₀, by simpa only [lo.source] using hlo 0⟩
          let a₁ : A := ⟨x₁, by simpa only [lo.target] using hlo 1⟩
          let b₀ : A := ⟨y₀, by simpa only [up.source] using hup 0⟩
          let b₁ : A := ⟨y₁, by simpa only [up.target] using hup 1⟩
          let l : Path a₀ a₁ :=
            { toFun := fun t => ⟨lo t,hlo t⟩
              continuous_toFun := lo.continuous.subtype_mk _
              source' := Subtype.ext lo.source
              target' := Subtype.ext lo.target }
          let u : Path b₀ b₁ :=
            { toFun := fun t => ⟨up t,hup t⟩
              continuous_toFun := up.continuous.subtype_mk _
              source' := Subtype.ext up.source
              target' := Subtype.ext up.target }
          let v₀ : Path a₀ b₀ :=
            { toFun := fun t => ⟨vl t,hvl t⟩
              continuous_toFun := vl.continuous.subtype_mk _
              source' := Subtype.ext vl.source
              target' := Subtype.ext vl.target }
          let v₁ : Path a₁ b₁ :=
            { toFun := fun t => ⟨vr t,hvr t⟩
              continuous_toFun := vr.continuous.subtype_mk _
              source' := Subtype.ext vr.source
              target' := Subtype.ext vr.target }
          obtain ⟨F,hF0,hF1,hFl,hFr⟩ := square_fill A hA a₀ a₁ b₀ b₁ l u v₀ v₁
          refine ⟨(⟨Subtype.val,continuous_subtype_val⟩ : C(A,_)).comp F, ?_, ?_, ?_, ?_⟩
          · intro t; exact congrArg Subtype.val (hF0 t)
          · intro t; exact congrArg Subtype.val (hF1 t)
          · intro t; exact congrArg Subtype.val (hFl t)
          · intro t; exact congrArg Subtype.val (hFr t)
        have finish_grid (N : ℕ) (ts us : Fin (N+1) → unitInterval)
            (ht0 : ts 0 = 0) (ht1 : ts (Fin.last N) = 1)
            (hu0 : us 0 = 0) (hu1 : us (Fin.last N) = 1)
            (vs : ∀ i, Path (p (ts i)) (bp (us i)))
            (hseam : ∀ s, vs 0 s = vs (Fin.last N) s)
            (As : Fin N → Set (RealizationPoint (curveComplex S 0)))
            (hAs : ∀ i, ContractibleSpace (As i))
            (hs : ∀ i, (∀ t, p.subpath (ts i.castSucc) (ts i.succ) t ∈ As i) ∧
              (∀ t, bp.subpath (us i.castSucc) (us i.succ) t ∈ As i) ∧
              (∀ s, vs i.castSucc s ∈ As i) ∧ (∀ s, vs i.succ s ∈ As i)) :
            Nonempty (ContinuousMap.HomotopyWith p.toContinuousMap (b.comp gamma)
              (fun f : C(unitInterval, RealizationPoint (curveComplex S 0)) => f 0 = f 1)) := by
          have hc (i : Fin N) := supported_square (As i) (hAs i)
            (p (ts i.castSucc)) (p (ts i.succ)) (bp (us i.castSucc)) (bp (us i.succ))
            (p.subpath (ts i.castSucc) (ts i.succ)) (bp.subpath (us i.castSucc) (us i.succ))
            (vs i.castSucc) (vs i.succ) (hs i).1 (hs i).2.1 (hs i).2.2.1 (hs i).2.2.2
          choose cells hcells using hc
          obtain ⟨H,hH0,hH1,hHl,hHr⟩ := grid N (p ∘ ts) (bp ∘ us)
            (fun i => p.subpath (ts i.castSucc) (ts i.succ))
            (fun i => bp.subpath (us i.castSucc) (us i.succ)) vs cells hcells
          let F : ContinuousMap.HomotopyWith
              (Path.concat (p ∘ ts) (fun i => p.subpath (ts i.castSucc) (ts i.succ))).toContinuousMap
              (Path.concat (bp ∘ us) (fun i => bp.subpath (us i.castSucc) (us i.succ))).toContinuousMap
              (fun f : C(unitInterval, RealizationPoint (curveComplex S 0)) => f 0 = f 1) :=
            { toContinuousMap := H
              map_zero_left := hH0
              map_one_left := hH1
              prop' := fun s => (hHl s).trans ((hseam s).trans (hHr s).symm) }
          exact ⟨((retime_free p rfl N ts ht0 ht1).trans F).trans
            (retime_free bp (congrArg b hgamma_seam) N us hu0 hu1).symm⟩
        have traversal_data (i : Fin r)
            (Γ : Finset {σ : Face D // σ.val ∈ L.faces}) (hΓ : Γ ∈ K.faces)
            (hg : ∀ t ∈ Icc (a i.castSucc) (a i.succ), gamma t ∈ CurveComplex.faceCarrier K Γ)
            (c : Vertex S) (hc : ∀ δ ∈ Γ, P δ.val c) :
            ∃ (hc0 : P (least (gamma (a i.castSucc))).val c)
              (hc1 : P (least (gamma (a i.succ))).val c)
              (A : Set (RealizationPoint (curveComplex S 0))),
              ContractibleSpace A ∧
              (∀ t, (Path.refl (realizationVertex (curveComplex S 0) c
                ((curveComplex S 0).singleton_mem c))) t ∈ A) ∧
              (∀ t, bp.subpath (a i.castSucc) (a i.succ) t ∈ A) ∧
              (∀ s, vertical (gamma (a i.castSucc)) c hc0 s ∈ A) ∧
              (∀ s, vertical (gamma (a i.succ)) c hc1 s ∈ A) := by
          have hab : a i.castSucc ≤ a i.succ := (a.strictMono Fin.castSucc_lt_succ).le
          have hs0 := hg (a i.castSucc) ⟨le_rfl,hab⟩
          have hs1 := hg (a i.succ) ⟨hab,le_rfl⟩
          have hc0 := hc (least (gamma (a i.castSucc)))
            ((mem_faceCarrier_iff_support_subset K Γ _).mp hs0 (hleast_mem _))
          have hc1 := hc (least (gamma (a i.succ)))
            ((mem_faceCarrier_iff_support_subset K Γ _).mp hs1 (hleast_mem _))
          obtain ⟨δ,hδ,hmin⟩ := hleast Γ hΓ
          refine ⟨hc0,hc1,fullSupportLocus (curveComplex S 0) (P δ.val),
            hcarrier_contractible δ.val, ?_, ?_, ?_, ?_⟩
          · intro t
            exact hvertex_supported δ.val c (hc δ hδ)
          · intro t
            exact hclosed_support b hb Γ hΓ δ hδ hmin _
              (hg _ ⟨Icc.le_convexComb hab t,Icc.convexComb_le hab t⟩)
          · intro s
            exact hvertical_incident _ c hc0 Γ hΓ hs0 δ hmin s
          · intro s
            exact hvertical_incident _ c hc1 Γ hΓ hs1 δ hmin s
        have transfer_data (k : Fin bc.curveWord.edgeCount)
            (i : Fin (bc.arcWord.edgeCount+1))
            (hi : bc.arcLabel (bc.arcWord.vertex i) = bc.junction k.succ) :
            ∃ (hc0 : P (least (gamma (d.wordTimes i.succ))).val (bc.curveWord.vertex k.castSucc))
              (hc1 : P (least (gamma (d.wordTimes i.succ))).val (bc.curveWord.vertex k.succ))
              (A : Set (RealizationPoint (curveComplex S 0))),
              ContractibleSpace A ∧
              (∀ t, bc.curveWord.edge k t ∈ A) ∧
              (∀ t, bp.subpath (d.wordTimes i.succ) (d.wordTimes i.succ) t ∈ A) ∧
              (∀ s, vertical (gamma (d.wordTimes i.succ)) (bc.curveWord.vertex k.castSucc) hc0 s ∈ A) ∧
              (∀ s, vertical (gamma (d.wordTimes i.succ)) (bc.curveWord.vertex k.succ) hc1 s ∈ A) := by
          have heq := (hword_vertex_labels i (least (gamma (d.wordTimes i.succ))) (hleast_mem _)).trans
            (congrArg (fun a => ({a} : Finset (ArcVertex S x R))) hi)
          have heqp : P (least (gamma (d.wordTimes i.succ))).val =
              CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R {bc.junction k.succ} := by
            dsimp only [P]
            rw [heq]
          have hc0 : P (least (gamma (d.wordTimes i.succ))).val (bc.curveWord.vertex k.castSucc) := by
            rw [heqp]
            exact (hcarrier _ (Finset.singleton_nonempty _) _).mp (bc.junction_left k)
          have hc1 : P (least (gamma (d.wordTimes i.succ))).val (bc.curveWord.vertex k.succ) := by
            rw [heqp]
            exact (hcarrier _ (Finset.singleton_nonempty _) _).mp (bc.junction_right k)
          refine ⟨hc0,hc1,fullSupportLocus (curveComplex S 0) (P (least (gamma (d.wordTimes i.succ))).val),
            hcarrier_contractible _, ?_, ?_, ?_, ?_⟩
          · intro t; rw [heqp]; exact hedge k t
          · intro t
            rw [Path.subpath_self]
            exact hbpoint (gamma (d.wordTimes i.succ))
          · intro s; exact hvertical_support _ _ hc0 s
          · intro s; exact hvertical_support _ _ hc1 s
        obtain ⟨T,hTmono,hT0,hT1,hTinitial,hTedge⟩ :=
          timing bc.curveWord.edgeCount bc.curveWord.point bc.curveWord.edge
        have hpconcat (t : unitInterval) :
            p t = Path.concat bc.curveWord.point bc.curveWord.edge t := by
          have h := congrArg (fun q : C(unitInterval,RealizationPoint (curveComplex S 0)) => q t)
            bc.curve_loop_exact
          change bc.curveWord.loop t = p t at h
          rw [bc.curveWord.loop_eq] at h
          exact h.symm
        have hclock (k : Fin (bc.curveWord.edgeCount+1)) :
            p (T k.succ) = realizationVertex (curveComplex S 0)
              (bc.curveWord.vertex k) ((curveComplex S 0).singleton_mem _) := by
          apply Eq.trans ?_ (bc.curveWord.point_eq k)
          rw [hpconcat]
          refine Fin.cases ?_ (fun l => ?_) k
          · simpa only [Icc.convexComb_one, Fin.succ_zero_eq_one] using hTinitial 1
          · simpa only [Icc.convexComb_one, Path.target] using hTedge l 1
        have hclock_initial (t : unitInterval) :
            p.subpath 0 (T 1) t = realizationVertex (curveComplex S 0)
              (bc.curveWord.vertex 0) ((curveComplex S 0).singleton_mem _) := by
          change p (Icc.convexComb 0 (T 1) t) = _
          rw [hpconcat, ← hT0, hTinitial, bc.curveWord.point_eq]
          rfl
        have hclock_edge (k : Fin bc.curveWord.edgeCount) (t : unitInterval) :
            p.subpath (T k.castSucc.succ) (T k.succ.succ) t = bc.curveWord.edge k t := by
          change p (Icc.convexComb (T k.castSucc.succ) (T k.succ.succ) t) = _
          rw [hpconcat]
          exact hTedge k t
        have hword_mono : StrictMono d.wordTimes := d.wordTimes_strict
        let O (k : Fin (bc.curveWord.edgeCount+1)) : Fin (bc.arcWord.edgeCount+1) :=
          ⟨bc.offset k, Nat.lt_succ_of_le (hoffset_bound k)⟩
        let Q (k : Fin (bc.curveWord.edgeCount+1)) : unitInterval := d.wordTimes (O k).succ
        have hOmono : Monotone O := fun _ _ h => hoffset_mono h
        have hQmono : Monotone Q := fun _ _ h => hword_mono.monotone (Fin.succ_le_succ_iff.mpr (hOmono h))
        have hQlast : Q (Fin.last bc.curveWord.edgeCount) = 1 := by
          have he : (O (Fin.last bc.curveWord.edgeCount)).succ = Fin.last (bc.arcWord.edgeCount+1) := by
            apply Fin.ext
            change bc.offset (Fin.last bc.curveWord.edgeCount) + 1 = bc.arcWord.edgeCount + 1
            rw [bc.offset_last]
          exact (congrArg d.wordTimes he).trans d.wordTimes_one
        have hQ0 : Q 0 = d.wordTimes 1 := by
          apply congrArg d.wordTimes
          apply Fin.ext
          change bc.offset 0 + 1 = 1
          rw [bc.offset_zero]
        let J (k : Fin (bc.curveWord.edgeCount+1)) : Fin (r+1) :=
          Classical.choose (ha_range (Q k) (hword_cut (O k).succ))
        have hJ (k : Fin (bc.curveWord.edgeCount+1)) : a (J k) = Q k :=
          Classical.choose_spec (ha_range (Q k) (hword_cut (O k).succ))
        have hJmono : Monotone J := by
          intro k l h
          apply a.le_iff_le.mp
          rw [hJ,hJ]
          exact hQmono h
        have hJlast : J (Fin.last bc.curveWord.edgeCount) = Fin.last r := by
          apply a.injective
          rw [hJ,hQlast,ha1]
        have hblock_pair_specific (k : Fin bc.curveWord.edgeCount)
            (l : Fin bc.arcWord.edgeCount)
            (hl : bc.offset k.castSucc ≤ l.val) (hr : l.val < bc.offset k.succ) :
            CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R
              {bc.arcLabel (bc.arcWord.vertex l.castSucc),bc.arcLabel (bc.arcWord.vertex l.succ)}
              (bc.curveWord.vertex k.castSucc) := by
          have hj : l.val - bc.offset k.castSucc < bc.blockLength k :=
            Nat.sub_lt_left_of_lt_add hl (by simpa only [bc.offset_step] using hr)
          let j : Fin (bc.blockLength k) := ⟨l.val - bc.offset k.castSucc,hj⟩
          have he : bc.offset k.castSucc + j.val = l.val := Nat.add_sub_of_le hl
          obtain ⟨u,hu,hul⟩ := bc.block_occurrences k j.castSucc
          obtain ⟨v,hv,hvl⟩ := bc.block_occurrences k j.succ
          have hu' : u = l.castSucc := Fin.ext (hu.trans he)
          have hv' : v = l.succ := Fin.ext (hv.trans ((Nat.add_assoc _ _ _).symm.trans (congrArg (fun n=>n+1) he)))
          rw [hu'] at hul
          rw [hv'] at hvl
          rw [hul,hvl]
          exact (hcarrier _ (Finset.insert_nonempty _ _) _).mp (bc.block_edge_carrier k j)
        have hinitial_flag (i : Fin r)
            (Γ : Finset {σ : Face D // σ.val ∈ L.faces})
            (hΓ : ∀ t ∈ Ioo (a i.castSucc) (a i.succ), supportFinset K (gamma t) = Γ)
            (hi : a i.succ ≤ d.wordTimes 1) :
            ∀ δ ∈ Γ, P δ.val (bc.curveWord.vertex 0) := by
          have hpos : d.wordTimes (0 : Fin (bc.arcWord.edgeCount+2)) ≤ a i.castSucc := by
            rw [d.wordTimes_zero]
            exact bot_le
          have hsub := htraversal_labels i Γ hΓ 0 ⟨hpos,hi⟩
            {bc.arcLabel (bc.arcWord.vertex 0)} (by
              intro t w hw
              rw [d.wordPiece_constant,bc.arcWord.point_eq,realizationVertex_weight]
              exact ite_eq_right (fun heq => hw (Finset.mem_singleton.mpr heq)))
          intro δ hδ
          exact CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier_antitone
            S x R _ _ (hsub δ hδ) _ hinitial_curve_carrier
        have hblock_flag (k : Fin bc.curveWord.edgeCount) (i : Fin r)
            (Γ : Finset {σ : Face D // σ.val ∈ L.faces})
            (hΓ : ∀ t ∈ Ioo (a i.castSucc) (a i.succ), supportFinset K (gamma t) = Γ)
            (hl : Q k.castSucc ≤ a i.castSucc) (hr : a i.succ ≤ Q k.succ) :
            ∀ δ ∈ Γ, P δ.val (bc.curveWord.vertex k.castSucc) := by
          obtain ⟨w,hw⟩ := hcut_word_piece i
          have hwne : w ≠ 0 := by
            intro he
            subst w
            have hq : d.wordTimes 1 ≤ Q k.castSucc :=
              hword_mono.monotone (by change 1 ≤ bc.offset k.castSucc + 1; exact Nat.succ_le_succ (Nat.zero_le _))
            have hbad : a i.succ ≤ a i.castSucc := hw.2.trans (hq.trans hl)
            exact (not_le_of_gt (a.strictMono Fin.castSucc_lt_succ)) hbad
          obtain ⟨l,hlw⟩ := Fin.exists_succ_eq.mpr hwne
          subst w
          have hlo : bc.offset k.castSucc ≤ l.val := by
            have ht : d.wordTimes (O k.castSucc).succ < d.wordTimes l.succ.succ :=
              hl.trans_lt ((a.strictMono Fin.castSucc_lt_succ).trans_le hw.2)
            have hn := hword_mono.lt_iff_lt.mp ht
            exact Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hn)
          have hhi : l.val < bc.offset k.succ := by
            have ht : d.wordTimes l.succ.castSucc < d.wordTimes (O k.succ).succ :=
              hw.1.trans_lt ((a.strictMono Fin.castSucc_lt_succ).trans_le hr)
            have hn := hword_mono.lt_iff_lt.mp ht
            exact Nat.lt_of_succ_lt_succ hn
          have hpair := hblock_pair_specific k l hlo hhi
          have hsub := htraversal_labels i Γ hΓ l.succ hw
            {bc.arcLabel (bc.arcWord.vertex l.castSucc),bc.arcLabel (bc.arcWord.vertex l.succ)} (by
              intro t
              rw [d.wordPiece_edge]
              intro w hw
              have hL : bc.arcLabel (bc.arcWord.vertex l.castSucc) ≠ w := by
                intro he; exact hw (he ▸ Finset.mem_insert_self _ _)
              have hR : bc.arcLabel (bc.arcWord.vertex l.succ) ≠ w := by
                intro he; exact hw (he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
              simpa only [ite_eq_right hL,ite_eq_right hR,mul_zero,add_zero] using bc.arcWord.edge_weight l t w)
          intro δ hδ
          exact CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier_antitone
            S x R _ _ (hsub δ hδ) _ hpair
        have finite_trace {X : Type} (rel : X → X → Prop) {x y : X}
            (h : Relation.ReflTransGen rel x y) :
            ∃ (n : ℕ) (z : Fin (n+1) → X), z 0 = x ∧ z (Fin.last n) = y ∧
              ∀ i : Fin n, rel (z i.castSucc) (z i.succ) := by
          induction h with
          | refl => exact ⟨0,fun _=>x,rfl,rfl,fun i=>Fin.elim0 i⟩
          | @tail y z hyz hstep ih =>
            obtain ⟨n,w,hw0,hw1,hw⟩ := ih
            let w' : Fin (n+2) → X := Fin.lastCases z w
            refine ⟨n+1,w',?_,?_,?_⟩
            · change Fin.lastCases z w (Fin.castSucc (0 : Fin (n+1))) = x
              rw [Fin.lastCases_castSucc]
              exact hw0
            · exact Fin.lastCases_last
            · intro i
              refine Fin.lastCases ?_ (fun j=>?_) i
              · change rel (w' (Fin.last n).castSucc) (w' (Fin.last (n+1)))
                simpa only [w',Fin.lastCases_castSucc,Fin.lastCases_last,hw1] using hstep
              · simpa only [w',←Fin.castSucc_succ,Fin.lastCases_castSucc] using hw j
        let Node := {q : unitInterval × unitInterval × Vertex S //
          p q.1 = realizationVertex (curveComplex S 0) q.2.2 ((curveComplex S 0).singleton_mem _) ∧
            P (least (gamma q.2.1)).val q.2.2}
        let nodePath (q : Node) : Path (p q.val.1) (bp q.val.2.1) :=
          (vertical (gamma q.val.2.1) q.val.2.2 q.property.2).cast q.property.1 rfl
        let Step (q q' : Node) : Prop :=
          ∃ A : Set (RealizationPoint (curveComplex S 0)), ContractibleSpace A ∧
            (∀ t, p.subpath q.val.1 q'.val.1 t ∈ A) ∧
            (∀ t, bp.subpath q.val.2.1 q'.val.2.1 t ∈ A) ∧
            (∀ t, nodePath q t ∈ A) ∧ (∀ t, nodePath q' t ∈ A)
        let state (t : unitInterval) (k : Fin (bc.curveWord.edgeCount+1))
            (hc : P (least (gamma t)).val (bc.curveWord.vertex k)) : Node :=
          ⟨(T k.succ,t,bc.curveWord.vertex k),hclock k,hc⟩
        have state_time (t u : unitInterval) (k : Fin (bc.curveWord.edgeCount+1)) (he : t=u)
            (ht : P (least (gamma t)).val (bc.curveWord.vertex k))
            (hu : P (least (gamma u)).val (bc.curveWord.vertex k)) : state t k ht = state u k hu := by
          subst u
          rfl
        have horizontal_step (i : Fin r) (k : Fin (bc.curveWord.edgeCount+1))
            (hflag : ∀ Γ, Γ ∈ K.faces →
              (∀ t ∈ Ioo (a i.castSucc) (a i.succ), supportFinset K (gamma t) = Γ) →
              ∀ δ ∈ Γ, P δ.val (bc.curveWord.vertex k)) :
            ∃ (hc0 : P (least (gamma (a i.castSucc))).val (bc.curveWord.vertex k))
              (hc1 : P (least (gamma (a i.succ))).val (bc.curveWord.vertex k)),
              Step (state (a i.castSucc) k hc0) (state (a i.succ) k hc1) := by
          obtain ⟨Γ,hΓ,_,hopen,hclosed⟩ := hcut_flag i
          obtain ⟨hc0,hc1,A,hA,hlo,hup,hvl,hvr⟩ := traversal_data i Γ hΓ hclosed _ (hflag Γ hΓ hopen)
          refine ⟨hc0,hc1,A,hA,?_,hup,hvl,hvr⟩
          intro t
          change p.subpath (T k.succ) (T k.succ) t ∈ A
          rw [Path.subpath_self,Path.refl_apply,hclock]
          exact hlo t
        have horizontal_walk (k : Fin (bc.curveWord.edgeCount+1))
            (s t : Fin (r+1)) (hst : s ≤ t)
            (hflag : ∀ i : Fin r, s ≤ i.castSucc → i.succ ≤ t →
              ∀ Γ, Γ ∈ K.faces →
                (∀ u ∈ Ioo (a i.castSucc) (a i.succ), supportFinset K (gamma u) = Γ) →
                ∀ δ ∈ Γ, P δ.val (bc.curveWord.vertex k))
            (hs : P (least (gamma (a s))).val (bc.curveWord.vertex k))
            (ht : P (least (gamma (a t))).val (bc.curveWord.vertex k)) :
            Relation.ReflTransGen Step (state (a s) k hs) (state (a t) k ht) := by
          induction t using Fin.induction with
          | zero =>
            have he : s = 0 := le_antisymm hst (Fin.zero_le s)
            subst s
            exact Relation.ReflTransGen.refl
          | succ i ih =>
            by_cases he : s = i.succ
            · subst s; exact Relation.ReflTransGen.refl
            · have hsi : s ≤ i.castSucc := Fin.le_castSucc_iff.mpr (lt_of_le_of_ne hst he)
              obtain ⟨hci,hci',hstep⟩ := horizontal_step i k (hflag i hsi le_rfl)
              exact (ih hsi (fun j hj0 hj1 => hflag j hj0 (hj1.trans Fin.castSucc_lt_succ.le)) hci).tail hstep
        have transfer_step (k : Fin bc.curveWord.edgeCount) :
            ∃ (hl : P (least (gamma (Q k.succ))).val (bc.curveWord.vertex k.castSucc))
              (hr : P (least (gamma (Q k.succ))).val (bc.curveWord.vertex k.succ)),
              Step (state (Q k.succ) k.castSucc hl) (state (Q k.succ) k.succ hr) := by
          obtain ⟨i,hi,hi'⟩ := hjunction_occurrence k
          have he : i = O k.succ := Fin.ext hi
          rw [he] at hi'
          obtain ⟨hl,hr,A,hA,hlo,hup,hvl,hvr⟩ := transfer_data k (O k.succ) hi'
          refine ⟨hl,hr,A,hA,?_,hup,hvl,hvr⟩
          intro t
          change p.subpath (T k.castSucc.succ) (T k.succ.succ) t ∈ A
          rw [hclock_edge]
          exact hlo t
        have hjunction_state (k : Fin (bc.curveWord.edgeCount+1)) :
            P (least (gamma (Q k))).val (bc.curveWord.vertex k) := by
          refine Fin.cases ?_ (fun l=>?_) k
          · let l : Fin bc.curveWord.edgeCount := ⟨0,bc.curve_nonempty⟩
            obtain ⟨i,hi,hi'⟩ := bc.block_occurrences l 0
            have he : i = O 0 := Fin.ext (by
              simpa only [Fin.val_zero,Nat.add_zero,show l.castSucc = 0 from rfl] using hi)
            rw [he] at hi'
            have himage := (hword_vertex_labels (O 0) (least (gamma (Q 0))) (hleast_mem _)).trans
              (congrArg (fun a=>({a} : Finset (ArcVertex S x R))) hi')
            change CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R
              ((least (gamma (Q 0))).val.val.image d.label) (bc.curveWord.vertex 0)
            rw [himage]
            exact (hcarrier _ (Finset.singleton_nonempty _) _).mp (bc.block_vertex_carrier l 0)
          · obtain ⟨_,hr,_⟩ := transfer_step l
            exact hr
        let blockNode (k : Fin (bc.curveWord.edgeCount+1)) : Node := state (Q k) k (hjunction_state k)
        have block_walk (k : Fin (bc.curveWord.edgeCount+1)) :
            Relation.ReflTransGen Step (blockNode 0) (blockNode k) := by
          induction k using Fin.induction with
          | zero => exact Relation.ReflTransGen.refl
          | succ k ih =>
            obtain ⟨hcL,hcR,hstep⟩ := transfer_step k
            have hs : P (least (gamma (a (J k.castSucc)))).val (bc.curveWord.vertex k.castSucc) := by
              rw [hJ]; exact hjunction_state k.castSucc
            have ht : P (least (gamma (a (J k.succ)))).val (bc.curveWord.vertex k.castSucc) := by
              rw [hJ]; exact hcL
            have hwalk := horizontal_walk k.castSucc (J k.castSucc) (J k.succ)
              (hJmono Fin.castSucc_lt_succ.le) (by
                intro i hli hri Γ hΓ hopen
                apply hblock_flag k i Γ hopen
                · rw [← hJ]; exact a.monotone hli
                · rw [← hJ]; exact a.monotone hri) hs ht
            have heL : state (a (J k.castSucc)) k.castSucc hs = blockNode k.castSucc :=
              state_time _ _ _ (hJ _) hs (hjunction_state k.castSucc)
            have heR : state (a (J k.succ)) k.castSucc ht = state (Q k.succ) k.castSucc hcL :=
              state_time _ _ _ (hJ _) ht hcL
            rw [heL,heR] at hwalk
            exact ih.trans (hwalk.tail hstep)
        have hinitial_state : P (least (gamma 0)).val (bc.curveWord.vertex 0) := by
          have hw : bc.arcWord.loop 0 = realizationVertex (arcComplex S x R)
              (bc.arcLabel (bc.arcWord.vertex 0)) ((arcComplex S x R).singleton_mem _) := by
            have h := d.wordPiece_constant 0
            rw [(d.wordPieceTime 0).source] at h
            change bc.arcWord.loop (d.wordTimes 0) = bc.arcWord.point 0 at h
            rw [d.wordTimes_zero] at h
            exact h.trans (bc.arcWord.point_eq 0)
          have hl := hsupport_label_singleton 0 _ hw (least (gamma 0)) (hleast_mem _)
          change CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers.faceCarrier S x R
            ((least (gamma 0)).val.val.image d.label) (bc.curveWord.vertex 0)
          rw [hl]
          exact hinitial_curve_carrier
        let firstNode : Node := ⟨(0,0,bc.curveWord.vertex 0),
          by simpa only [bc.curve_base] using p.source, hinitial_state⟩
        have initial_lower_step : Step firstNode (state 0 0 hinitial_state) := by
          refine ⟨fullSupportLocus (curveComplex S 0) (P (least (gamma 0)).val),
            hcarrier_contractible _, ?_, ?_, ?_, ?_⟩
          · intro t
            change p.subpath 0 (T (Fin.succ 0)) t ∈ _
            rw [Fin.succ_zero_eq_one,hclock_initial]
            exact hvertex_supported _ _ hinitial_state
          · intro t
            change bp.subpath 0 0 t ∈ _
            rw [Path.subpath_self]
            exact hbpoint (gamma 0)
          · intro t; exact hvertical_support _ _ hinitial_state t
          · intro t; exact hvertical_support _ _ hinitial_state t
        have initial_upper_walk :
            Relation.ReflTransGen Step (state 0 0 hinitial_state) (blockNode 0) := by
          have hs : P (least (gamma (a 0))).val (bc.curveWord.vertex 0) := by
            rw [ha0]; exact hinitial_state
          have ht : P (least (gamma (a (J 0)))).val (bc.curveWord.vertex 0) := by
            rw [hJ]; exact hjunction_state 0
          have hwalk := horizontal_walk 0 0 (J 0) (Fin.zero_le _) (by
            intro i _ hri Γ _ hopen
            apply hinitial_flag i Γ hopen
            calc a i.succ ≤ a (J 0) := a.monotone hri
                 _ = d.wordTimes 1 := (hJ 0).trans hQ0) hs ht
          rw [state_time _ _ _ ha0 hs hinitial_state,
            state_time _ _ _ (hJ 0) ht (hjunction_state 0)] at hwalk
          exact hwalk
        have whole_walk : Relation.ReflTransGen Step firstNode
            (blockNode (Fin.last bc.curveWord.edgeCount)) :=
          (Relation.ReflTransGen.single initial_lower_step).trans
            (initial_upper_walk.trans (block_walk _))
        have hschedule : ∃ (N : ℕ) (ts us : Fin (N+1) → unitInterval),
            ts 0 = 0 ∧ ts (Fin.last N) = 1 ∧ us 0 = 0 ∧ us (Fin.last N) = 1 ∧
            ∃ (vs : ∀ i, Path (p (ts i)) (bp (us i)))
              (As : Fin N → Set (RealizationPoint (curveComplex S 0))),
              (∀ s, vs 0 s = vs (Fin.last N) s) ∧
              (∀ i, ContractibleSpace (As i)) ∧
              ∀ i, (∀ t, p.subpath (ts i.castSucc) (ts i.succ) t ∈ As i) ∧
                (∀ t, bp.subpath (us i.castSucc) (us i.succ) t ∈ As i) ∧
                (∀ s, vs i.castSucc s ∈ As i) ∧ (∀ s, vs i.succ s ∈ As i) := by
          obtain ⟨N,z,hz0,hz1,hz⟩ := finite_trace Step whole_walk
          have hcarriers (i : Fin N) := hz i
          choose As hAs hs using hcarriers
          let ts : Fin (N+1) → unitInterval := fun i => (z i).val.1
          let us : Fin (N+1) → unitInterval := fun i => (z i).val.2.1
          refine ⟨N,ts,us,?_,?_,?_,?_,fun i=>nodePath (z i),As,?_,hAs,hs⟩
          · change (z 0).val.1 = 0
            rw [hz0]
          · change (z (Fin.last N)).val.1 = 1
            rw [hz1]
            exact hT1
          · change (z 0).val.2.1 = 0
            rw [hz0]
          · change (z (Fin.last N)).val.2.1 = 1
            rw [hz1]
            exact hQlast
          · intro s
            have hdep : ∀ (y y' : RealizationPoint K) (c c' : Vertex S), y = y' → c = c' →
                ∀ (hc : P (least y).val c) (hc' : P (least y').val c'),
                vertical y c hc s = vertical y' c' hc' s := by
              intro y y' c c' hy hc h h'
              subst y'
              subst c'
              rfl
            change nodePath (z 0) s = nodePath (z (Fin.last N)) s
            rw [hz0,hz1]
            exact hdep _ _ _ _ (hgamma_seam.trans (congrArg gamma hQlast.symm))
              bc.curveWord.vertex_closed.symm firstNode.property.2
              (blockNode (Fin.last bc.curveWord.edgeCount)).property.2
        obtain ⟨N,ts,us,ht0,ht1,hu0,hu1,vs,As,hseam,hAs,hs⟩ := hschedule
        exact ⟨b, hb, finish_grid N ts us ht0 ht1 hu0 hu1 vs hseam As hAs hs⟩

end CurveComplex.C0BoundaryCorrespondence.CarriedAnnulus
