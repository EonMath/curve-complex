import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actual_family_realign_to_representative (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (u : {v // v ∈ σ}) (a : EssentialMarkedArc M)
    (ha : Quotient.mk (essentialArcSetoid M) a = u.val) :
    ∃ s : {v // v ∈ σ} → EssentialMarkedArc M,
      (∀ v, Quotient.mk (essentialArcSetoid M) (s v) = v.val) ∧
      (s u).val.image = a.val.image ∧
      ∀ v w, v ≠ w → Disjoint (arcInterior M (s v)) (arcInterior M (s w)) := by
  classical
  have hrel : MarkedIsotopyRel M (r u).val.image a.val.image :=
    Quotient.exact ((hr u).trans ha.symm)
  obtain ⟨H, hmarks, hHa⟩ := hrel
  obtain ⟨h, hh⟩ := H.homeomorphism_at (1 : Interval)
  have hfinal : (h : S → S) = H.finalMap := funext hh
  have hfix : ∀ x, x ∈ M.cover.branch → h x = x :=
    fun x hx => (hh x).trans (hmarks 1 x hx)
  have hcomponent : ∀ (g : S ≃ₜ S) {A U : Set S},
      IsComplementComponent A U → IsComplementComponent (g '' A) (g '' U) := by
    intro g A U hU
    rcases hU with ⟨hne, hconn, hsub, hmax⟩
    refine ⟨hne.image g, hconn.image g g.continuous.continuousOn, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
      exact hsub hx (g.injective heq ▸ hy)
    · intro V hV hUV hVA
      have hUV' : U ⊆ g.symm '' V := by
        intro x hx
        exact ⟨g x, hUV ⟨x, hx, rfl⟩, g.symm_apply_apply x⟩
      have hVA' : g.symm '' V ⊆ Aᶜ := by
        rintro _ ⟨x, hx, rfl⟩ ha
        exact hVA hx ⟨g.symm x, ha, g.apply_symm_apply x⟩
      have hEq := hmax (g.symm '' V) (hV.image g.symm g.symm.continuous.continuousOn)
        hUV' hVA'
      calc
        V = g '' (g.symm '' V) := by
          ext x
          simp only [Set.mem_image]
          constructor
          · intro hx; exact ⟨g.symm x, ⟨x, hx, rfl⟩, g.apply_symm_apply x⟩
          · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
        _ = g '' U := congrArg (fun W : Set S => g '' W) hEq
  have htransport : ∀ c : EssentialMarkedArc M, ∃ d : EssentialMarkedArc M,
      Quotient.mk (essentialArcSetoid M) d = Quotient.mk (essentialArcSetoid M) c ∧
      d.val.image = h '' c.val.image := by
    intro c
    let d0 : MarkedArc M := {
      map := h ∘ c.val.map
      continuous := h.continuous.comp c.val.continuous
      injective_except_loop_closure := fun t u heq =>
        c.val.injective_except_loop_closure t u (h.injective heq)
      start_marked := by simpa only [Function.comp_apply, hfix _ c.val.start_marked] using c.val.start_marked
      end_marked := by simpa only [Function.comp_apply, hfix _ c.val.end_marked] using c.val.end_marked
      marked_only_at_ends := by
        intro t ht
        have heq : h (c.val.map t) = c.val.map t := h.injective (hfix _ ht)
        exact c.val.marked_only_at_ends t (heq ▸ ht) }
    have hdImage : d0.image = h '' c.val.image := Set.range_comp h c.val.map
    have hdEssential : IsEssentialMarkedArc M d0 := by
      rcases c.property with hn | hl
      · left
        exact fun heq => hn (h.injective heq)
      · right
        intro U hU
        rw [hdImage] at hU
        have hcomp := hcomponent h.symm hU
        have hback : h.symm '' (h '' c.val.image) = c.val.image := by
          ext x
          constructor
          · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
          · intro hx; exact ⟨h x, ⟨x, hx, rfl⟩, h.symm_apply_apply x⟩
        rw [hback] at hcomp
        obtain ⟨x, hxmark, hxU⟩ := hl (h.symm '' U) hcomp
        refine ⟨x, hxmark, ?_⟩
        obtain ⟨y, hy, heq⟩ := hxU
        have hyx : y = x := by
          calc
            y = h (h.symm y) := (h.apply_symm_apply y).symm
            _ = h x := congrArg h heq
            _ = x := hfix x hxmark
        exact hyx ▸ hy
    let d : EssentialMarkedArc M := ⟨d0, hdEssential⟩
    have hcd : Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) d := by
      apply Quotient.sound
      refine ⟨H, hmarks, ?_⟩
      change H.finalMap '' c.val.image = d0.image
      rw [hdImage, hfinal]
    exact ⟨d, hcd.symm, hdImage⟩
  choose s hsClass hsImage using fun v => htransport (r v)
  refine ⟨s, fun v => (hsClass v).trans (hr v), ?_, ?_⟩
  · rw [hsImage, hfinal]
    exact hHa
  · intro v w hvw
    apply Set.disjoint_left.mpr
    rintro x ⟨hxv, hxmark⟩ ⟨hxw, _⟩
    rw [hsImage] at hxv hxw
    obtain ⟨y, hy, hyx⟩ := hxv
    obtain ⟨z, hz, hzx⟩ := hxw
    have hyz : y = z := h.injective (hyx.trans hzx.symm)
    have hyn : y ∉ (M.cover.branch : Set S) := by
      intro hym
      exact hxmark ((hfix y hym).symm.trans hyx ▸ hym)
    exact Set.disjoint_left.mp (hd v w hvw) ⟨hy, hyn⟩ ⟨hyz ▸ hz, hyz ▸ hyn⟩

end CurveComplex.HyperellipticModel
