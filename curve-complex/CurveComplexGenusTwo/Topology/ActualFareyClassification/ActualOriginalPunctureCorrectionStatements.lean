import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalPuncturedSourceDefinitions
namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open CurveComplex

theorem puncture_corrected_winding_isotopy (p : Torus)
    (c : Curve (Punctured p)) (m n : ℤ) (hmn : m.gcd n = 1)
    (h : AmbientIsotopy.Rel (fill c).image
      (Set.range (torusWindingMap m n))) :
    ∃ (a : Torus) (d : Curve (Punctured p)),
      (∀ z : Circle, (d.map z).val = a * torusWindingMap m n z) ∧
      AmbientIsotopy.Rel c.image d.image := by
  classical
  obtain ⟨H, hH⟩ := h
  let a : Interval → Torus := fun t => p * (H.map (t, p))⁻¹
  have ac : Continuous a := continuous_const.mul
    (H.map.continuous.comp (continuous_id.prodMk continuous_const)).inv
  have fixes (t : Interval) : a t * H.map (t, p) = p := by
    simp [a, mul_assoc]
  have avoids (t : Interval) (x : Punctured p) : a t * H.map (t, x.val) ≠ p := by
    intro hx
    have he : H.map (t, x.val) = H.map (t, p) :=
      mul_left_cancel (hx.trans (fixes t).symm)
    obtain ⟨e, he'⟩ := H.homeomorphism_at t
    rw [← he', ← he'] at he
    exact x.property (e.injective he)
  let K : AmbientIsotopy (Punctured p) := {
    map := ⟨fun tx => ⟨a tx.1 * H.map (tx.1, tx.2.val), avoids tx.1 tx.2⟩,
      ((ac.comp continuous_fst).mul (H.map.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).subtype_mk _⟩
    homeomorphism_at := by
      intro t
      obtain ⟨e, he⟩ := H.homeomorphism_at t
      let g : Torus ≃ₜ Torus := e.trans (Homeomorph.mulLeft (a t))
      have gp : g p = p := by exact (congrArg (a t * ·) (he p)).trans (fixes t)
      let g' : Punctured p ≃ₜ Punctured p := g.subtype
        (fun x => by
          constructor
          · intro hx heq
            exact hx (g.injective (heq.trans gp.symm))
          · intro hx heq
            exact hx ((congrArg g heq).trans gp))
      exact ⟨g', fun x => by apply Subtype.ext; exact congrArg (a t * ·) (he x.val)⟩
    at_zero := by
      intro x
      apply Subtype.ext
      change a ⟨0, by norm_num⟩ * H.map (⟨0, by norm_num⟩, x.val) = x.val
      change p * (H.map (⟨0, by norm_num⟩, p))⁻¹ *
        H.map (⟨0, by norm_num⟩, x.val) = x.val
      rw [H.at_zero p, H.at_zero x.val]
      simp }
  let one : Interval := ⟨1, by norm_num⟩
  have hw (z : Circle) : a one * torusWindingMap m n z ≠ p := by
    have hz : torusWindingMap m n z ∈ H.finalMap '' (fill c).image := by
      rw [hH]
      exact ⟨z, rfl⟩
    obtain ⟨x, ⟨w, rfl⟩, hx⟩ := hz
    rw [← hx]
    exact avoids one (c.map w)
  let d : Curve (Punctured p) := {
    map := fun z => ⟨a one * torusWindingMap m n z, hw z⟩
    embedded := ((Homeomorph.mulLeft (a one)).isEmbedding.comp
      (torusWindingMap_isEmbedding hmn)).codRestrict {x : Torus | x ≠ p} hw }
  refine ⟨a one, d, fun z => rfl, K, ?_⟩
  apply Set.image_injective.mpr Subtype.val_injective
  rw [Set.image_image]
  change (fun x : Punctured p => a one * H.finalMap x.val) '' c.image =
    Subtype.val '' d.image
  rw [show (fun x : Punctured p => a one * H.finalMap x.val) =
    (fun x : Torus => a one * x) ∘ H.finalMap ∘ Subtype.val from rfl]
  rw [Set.image_comp, Set.image_comp]
  have hc : Subtype.val '' c.image = (fill c).image := by
    simp only [Curve.image, ← Set.range_comp']; rfl
  rw [hc, hH]
  simp only [Curve.image, ← Set.range_comp']
  rfl

end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
