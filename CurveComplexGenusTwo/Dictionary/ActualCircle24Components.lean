import CurveComplexGenusTwo.Dictionary.ActualDictionaryEssential
import CurveComplexGenusTwo.Dictionary.DictionaryTwoMarkChart
import CurveComplexGenusTwo.TwoCellDiscPastingNamed
import CurveComplexGenusTwo.Dictionary.ScratchCoordinatePullback

open Set Topology Metric
set_option maxHeartbeats 12000000
namespace CurveComplex
theorem curve_of_simple_closed_lift {X : Type*} [TopologicalSpace X] [T2Space X]
    (l : C(Interval, X)) (hend : l 0 = l 1)
    (hcoll : ∀ s t, l s = l t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    ∃ c : Curve X, c.image = Set.range l := by
  let r := AddCircle.EndpointIdent (1 : ℝ) 0
  let j : Icc (0 : ℝ) (0 + 1) → Interval := fun t => ⟨t.val, by simpa using t.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hrespect : ∀ a b, r a b → l (j a) = l (j b) := by
    rintro a b ⟨⟩
    simpa [j] using hend
  let L : Quot r → X := Quot.lift (fun t => l (j t)) hrespect
  have hL : Continuous L := continuous_quot_lift _ (l.continuous.comp hj)
  have hLi : Function.Injective L := by
    intro a b
    induction a using Quot.inductionOn with | h a =>
      induction b using Quot.inductionOn with | h b =>
        intro hab
        rcases hcoll (j a) (j b) hab with he | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · apply congrArg (Quot.mk r)
          exact Subtype.ext (congrArg (fun t : Interval => t.val) he)
        · have ha' : a = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
          have hb' : b = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
          subst a; subst b
          exact Quot.sound AddCircle.EndpointIdent.mk
        · have ha' : a = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
          have hb' : b = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
          subst a; subst b
          exact (Quot.sound AddCircle.EndpointIdent.mk).symm
  let e : Circle ≃ₜ Quot r :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans
      (AddCircle.homeoIccQuot (1 : ℝ) 0)
  let c : Curve X := ⟨L ∘ e, ((hL.comp e.continuous).isClosedEmbedding (hLi.comp e.injective)).isEmbedding⟩
  refine ⟨c, ?_⟩
  change range (L ∘ e) = range l
  rw [e.surjective.range_comp]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quot.inductionOn with | h t =>
      exact ⟨j t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Quot.mk r ⟨t.val, by simpa only [zero_add] using t.property⟩, rfl⟩

end CurveComplex

namespace CurveComplex.HyperellipticModel
variable {E S X : Type} [TopologicalSpace E] [TopologicalSpace S] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A closed simple boundary lift yields actual two embedded components;
their existence is constructed, not supplied as a component hypothesis. -/
theorem components_of_closed_boundary_lift (M : HyperellipticModel E S)
    (a : PuncturedCircle M) (β : C(Interval,S))
    (hcoll : ∀ s t, β s = β t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hrange : Set.range β = a.image)
    (γ : C(Interval,E)) (hπ : ∀ t, M.cover.projection (γ t) = β t)
    (hclose : γ 0 = γ 1) :
    ∃ c d : Curve E,
      c.image ∪ d.image = M.cover.projection ⁻¹' a.image ∧
      Disjoint c.image d.image ∧ M.cover.deck '' c.image = d.image := by
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hγcoll : ∀ s t, γ s = γ t → s = t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
    intro s t he
    apply hcoll s t
    rw [← hπ,← hπ,he]
  obtain ⟨c,hc⟩ := CurveComplex.curve_of_simple_closed_lift γ hclose hγcoll
  let d : Curve E := ⟨M.cover.deck ∘ c.map,M.cover.deck.isEmbedding.comp c.embedded⟩
  have hd : d.image = M.cover.deck '' c.image := by
    change Set.range (M.cover.deck ∘ c.map) = M.cover.deck '' Set.range c.map
    exact Set.range_comp _ _
  have havoid (t) : M.cover.deck (γ t) ≠ γ t := by
    intro he
    have hb := (M.cover.fixed_iff_branch (γ t)).mp he
    rw [hπ] at hb
    have ht : β t ∈ a.image := hrange ▸ Set.mem_range_self t
    exact Set.disjoint_left.mp a.avoids_branch ht hb
  have hdisj : Disjoint c.image d.image := by
    rw [hd,hc]
    apply Set.disjoint_left.mpr
    rintro x ⟨s,rfl⟩ ⟨y,⟨t,rfl⟩,he⟩
    have hb : β s=β t := by rw [← hπ,← hπ,← he,M.cover.projection_deck]
    rcases hcoll s t hb with rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact havoid s he
    · exact havoid 0 (by rw [← hclose] at he; exact he)
    · exact havoid 0 (by rw [← hclose] at he; exact he)
  refine ⟨c,d,?_,hdisj,hd.symm⟩
  rw [hd,hc,← hrange]
  ext x
  constructor
  · rintro (⟨t,rfl⟩ | ⟨y,⟨t,rfl⟩,rfl⟩)
    · exact ⟨t,(hπ t).symm⟩
    · exact ⟨t,((M.cover.projection_deck _).trans (hπ t)).symm⟩
  · rintro ⟨t,ht⟩
    rcases (M.cover.fiber_pair (γ t) x).mp ((hπ t).trans ht) with he | he
    · exact Or.inl ⟨t,he.symm⟩
    · exact Or.inr ⟨γ t,⟨t,rfl⟩,he.symm⟩

/-- The two-cell one-mark disk decomposition produces the closed lift and
hence the actual two-component full preimage of its outer circle. -/
theorem two_cell_preimage_components (M : HyperellipticModel E S)
    (a : PuncturedCircle M) (K : Set X) (f : C(K,S)) (hf : IsEmbedding f)
    (u v : K) (P χ : Path u v) (Q : Path v u)
    (F : Fin 2 → C(Metric.closedBall (0 : Schoenflies.Plane) 1,S))
    (hF : ∀ i, IsEmbedding (F i))
    (m : Fin 2 → Metric.closedBall (0 : Schoenflies.Plane) 1)
    (hm : ∀ i, ‖(m i).val‖ < 1)
    (honly : ∀ i z, F i z ∈ M.cover.branch ↔ z=m i)
    (hcell0 : Set.range (fun t => f ((P.trans χ.symm) t)) = F 0 '' {z | ‖z.val‖=1})
    (hcell1 : Set.range (fun t => f ((χ.trans Q) t)) = F 1 '' {z | ‖z.val‖=1})
    (hcoll0 : ∀ s t, (P.trans χ.symm) s=(P.trans χ.symm) t →
      s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hcoll1 : ∀ s t, (χ.trans Q) s=(χ.trans Q) t →
      s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hcollOuter : ∀ s t, f ((P.trans Q) s)=f ((P.trans Q) t) →
      s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hOuterRange : Set.range (fun t => f ((P.trans Q) t)) = a.image) :
    ∃ c d : Curve E,
      c.image ∪ d.image = M.cover.projection ⁻¹' a.image ∧
      Disjoint c.image d.image ∧ M.cover.deck '' c.image = d.image := by
  let β : C(Interval,S) :=
    ⟨fun t => f ((P.trans Q) t),f.continuous.comp (P.trans Q).continuous⟩
  have hrange : Set.range β = a.image := hOuterRange
  obtain ⟨γ,hπ⟩ := M.exists_puncturedCircle_path_lift a β hrange
  have hclose := M.two_cell_disc_pasting_closed_lift K f hf u v P χ Q F hF m hm
    honly hcell0 hcell1 hcoll0 hcoll1 γ hπ
  exact M.components_of_closed_boundary_lift a β hcollOuter hrange γ hπ hclose.symm

theorem rectangle_two_marked_preimage_components
    (M : HyperellipticModel E S)
    (a : PuncturedCircle M)
    (a₀ b₀ c₀ d₀ : ℝ) (ha₀b₀ : a₀ < b₀) (hc₀d₀ : c₀ < d₀)
    (lo hi : Fin 2 → ℝ × ℝ)
    (hshape :
      (∃ k : ℝ, lo = ![(a₀,c₀),(k,c₀)] ∧ hi = ![(k,d₀),(b₀,d₀)] ∧ a₀ < k ∧ k < b₀) ∨
      (∃ k : ℝ, lo = ![(a₀,c₀),(a₀,k)] ∧ hi = ![(b₀,k),(b₀,d₀)] ∧ c₀ < k ∧ k < d₀))
    (f : C(Icc a₀ b₀ ×ˢ Icc c₀ d₀, S)) (hf : IsEmbedding f)
    (F : Fin 2 → C(Metric.closedBall (0 : Schoenflies.Plane) 1, S))
    (hF : ∀ i, IsEmbedding (F i))
    (m : Fin 2 → Metric.closedBall (0 : Schoenflies.Plane) 1)
    (hm : ∀ i, ‖(m i).val‖ < 1)
    (honly : ∀ i z, F i z ∈ M.cover.branch ↔ z = m i)
    (hcell : ∀ i,
      f '' {z : Icc a₀ b₀ ×ˢ Icc c₀ d₀ |
        z.val ∈ frontier (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)} =
        F i '' {z | ‖z.val‖ = 1})
    (houter :
      f '' {z : Icc a₀ b₀ ×ˢ Icc c₀ d₀ |
        z.val ∈ frontier (Icc a₀ b₀ ×ˢ Icc c₀ d₀)} = a.image)
    :
    ∃ c d : Curve E, c.image ∪ d.image = M.cover.projection ⁻¹' a.image ∧
      Disjoint c.image d.image ∧ M.cover.deck '' c.image = d.image := by
  obtain ⟨r, x, y, P, Q, χ, h0, h1, ho, hc0, hc1, hco⟩ :=
    rectangle_two_cell_crosscut_typed_clean a₀ b₀ c₀ d₀ ha₀b₀ hc₀d₀ lo hi hshape
  let K : Set (ℝ × ℝ) := Icc a₀ b₀ ×ˢ Icc c₀ d₀
  have hmapRange {u v : K} (δ : Path u v) (A : Set (ℝ × ℝ))
      (hδ : Set.range (fun t => (δ t).val) = A) :
      Set.range (fun t => f (δ t)) =
        f '' {z : K | z.val ∈ A} := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨δ t, Set.mem_ofPred_eq.mpr (hδ ▸ Set.mem_range_self t), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : w.val ∈ Set.range (fun t => (δ t).val) := by
        rw [hδ]
        exact hw
      rcases hw' with ⟨t, ht⟩
      have he : δ t = w := Subtype.ext ht
      exact ⟨t, by change f (δ t) = f w; rw [he]⟩
  let F' : Fin 2 → C(Metric.closedBall (0 : Schoenflies.Plane) 1, S) := fun i => F (r i)
  let m' : Fin 2 → Metric.closedBall (0 : Schoenflies.Plane) 1 := fun i => m (r i)
  have hF' : ∀ i, IsEmbedding (F' i) := by
    intro i
    exact hF (r i)
  have hm' : ∀ i, ‖(m' i).val‖ < 1 := by
    intro i
    exact hm (r i)
  have honly' : ∀ i z, F' i z ∈ M.cover.branch ↔ z = m' i := by
    intro i z
    exact honly (r i) z
  have hcell0 :
      Set.range (fun t => f ((P.trans χ.symm) t)) = F' 0 '' {z | ‖z.val‖ = 1} := by
    have hr := hmapRange (P.trans χ.symm)
      (frontier (Icc (lo (r 0)).1 (hi (r 0)).1 ×ˢ
        Icc (lo (r 0)).2 (hi (r 0)).2)) h0
    rw [hr]
    simpa [F', m'] using hcell (r 0)
  have hcell1 :
      Set.range (fun t => f ((χ.trans Q) t)) = F' 1 '' {z | ‖z.val‖ = 1} := by
    have hr := hmapRange (χ.trans Q)
      (frontier (Icc (lo (r 1)).1 (hi (r 1)).1 ×ˢ
        Icc (lo (r 1)).2 (hi (r 1)).2)) h1
    rw [hr]
    simpa [F', m'] using hcell (r 1)
  have hco' : ∀ s t, f ((P.trans Q) s) = f ((P.trans Q) t) →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    intro s t h
    apply hco s t
    exact hf.injective h
  have hOuterRange :
      Set.range (fun t => f ((P.trans Q) t)) = a.image := by
    have hr := hmapRange (P.trans Q) (frontier (Icc a₀ b₀ ×ˢ Icc c₀ d₀)) ho
    rw [hr]
    exact houter
  exact two_cell_preimage_components M a K f hf x y P χ Q F' hF' m' hm'
    honly' hcell0 hcell1 hc0 hc1 hco' hOuterRange


private theorem actualComponents_pullback_image_frontier (C : Set (ℝ × ℝ))
    (hCfront : frontier C ⊆ dictPullbackRect) :
    dictPullbackHomeomorph '' {x : dictPullbackRect | x.val ∈ frontier C} =
      {z : dictPullbackSquare | z.val ∈ frontier (dictPullbackEquiv '' C)} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change dictPullbackEquiv.toHomeomorph x.val ∈
      frontier (dictPullbackEquiv.toHomeomorph '' C)
    rw [← dictPullbackEquiv.toHomeomorph.image_frontier]
    exact ⟨x.val, hx, rfl⟩
  · intro hz
    change z.val ∈ frontier (dictPullbackEquiv.toHomeomorph '' C) at hz
    rw [← dictPullbackEquiv.toHomeomorph.image_frontier] at hz
    rcases hz with ⟨x, hx, hzx⟩
    refine ⟨⟨x, hCfront hx⟩, hx, ?_⟩
    · apply Subtype.ext
      exact hzx

private theorem actualComponents_pullback_image_square_frontier :
    dictPullbackHomeomorph '' {x : dictPullbackRect |
      x.val ∈ frontier ((Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1)} =
      {z : dictPullbackSquare | z.val ∈ frontier dictPullbackSquare} := by
  simpa [dictPullbackSquare, dictPullbackRect] using
    actualComponents_pullback_image_frontier
      ((Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1) (by
        intro x hx
        exact (isClosed_Icc.prod isClosed_Icc).frontier_subset hx)

theorem two_marked_disc_chart_preimage_components
    (M : HyperellipticModel E S)
    (a : PuncturedCircle M)
    (f : C(dictPullbackSquare, S))
    (hf : IsEmbedding f)
    (hboundary : ∀ z, z.val ∈ frontier dictPullbackSquare → f z ∉ M.cover.branch)
    (hcard : (by classical exact
      (M.cover.branch.filter (fun b => b ∈ f '' {z |
        z.val ∈ interior dictPullbackSquare})).card = 2))
    (houter : f '' {z : dictPullbackSquare | z.val ∈ frontier dictPullbackSquare} = a.image)
    :
    ∃ c d : Curve E, c.image ∪ d.image = M.cover.projection ⁻¹' a.image ∧
      Disjoint c.image d.image ∧ M.cover.deck '' c.image = d.image := by
  classical
  let g : C(dictPullbackRect, S) :=
    ⟨fun x => f (dictPullbackHomeomorph x),
      f.continuous.comp dictPullbackHomeomorph.continuous⟩
  have hg : IsEmbedding g := hf.comp dictPullbackHomeomorph.isEmbedding
  have hboundary' : ∀ x : dictPullbackRect, x.val ∈ frontier dictPullbackRect →
      g x ∉ M.cover.branch := by
    intro x hx
    apply hboundary (dictPullbackHomeomorph x)
    change dictPullbackHomeomorph x ∈
      {z : dictPullbackSquare | z.val ∈ frontier dictPullbackSquare}
    rw [← actualComponents_pullback_image_square_frontier]
    exact ⟨x, hx, rfl⟩
  have hcard' : (M.cover.branch.filter (fun b => b ∈ g '' {x : dictPullbackRect |
      x.val ∈ interior dictPullbackRect})).card = 2 := by
    have hmap (A : Set dictPullbackRect) :
        g '' A = f '' (dictPullbackHomeomorph '' A) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨dictPullbackHomeomorph x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    have hinterior : dictPullbackHomeomorph '' {x : dictPullbackRect |
        x.val ∈ interior dictPullbackRect} =
        {z : dictPullbackSquare | z.val ∈ interior dictPullbackSquare} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        change dictPullbackEquiv.toHomeomorph x.val ∈
          interior (dictPullbackEquiv.toHomeomorph '' dictPullbackRect)
        rw [← dictPullbackEquiv.toHomeomorph.image_interior]
        exact ⟨x.val, hx, rfl⟩
      · intro hz
        change z.val ∈ interior (dictPullbackEquiv.toHomeomorph '' dictPullbackRect) at hz
        rw [← dictPullbackEquiv.toHomeomorph.image_interior] at hz
        rcases hz with ⟨x, hx, hzx⟩
        refine ⟨⟨x, interior_subset hx⟩, hx, ?_⟩
        apply Subtype.ext
        exact hzx
    rw [hmap, hinterior]
    exact hcard
  obtain ⟨lo, hi, F, m, hdims, _hcover, hshape, hfamily⟩ :=
    two_marked_rectangle_disc_cells M f hf hboundary hcard
  choose hFi hmi honly hcell using hfamily
  have hcell' : ∀ i, g '' {x : dictPullbackRect | x.val ∈ frontier
      (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)} =
      F i '' {z | ‖z.val‖ = 1} := by
    intro i
    have himage : dictPullbackHomeomorph '' {x : dictPullbackRect | x.val ∈
        frontier (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)} =
        {z : dictPullbackSquare | z.val ∈ frontier
          (dictPullbackEquiv '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2))} := by
      apply actualComponents_pullback_image_frontier _
      intro x hx
      rcases hshape with ⟨k, hlo, hhi, hak, hkb⟩ | ⟨k, hlo, hhi, hck, hkd⟩
      · subst lo hi
        have hsub : ∀ i, (Icc ((![(-1,-1),(k,-1)] : Fin 2 → ℝ × ℝ) i).1
            ((![ (k,1),(1,1)] : Fin 2 → ℝ × ℝ) i).1 ×ˢ
            Icc ((![(-1,-1),(k,-1)] : Fin 2 → ℝ × ℝ) i).2
              ((![ (k,1),(1,1)] : Fin 2 → ℝ × ℝ) i).2) ⊆ dictPullbackRect := by
          intro j z hz
          fin_cases j <;> simp only [Set.mem_prod, Set.mem_Icc] at hz ⊢ <;>
            dsimp at hz ⊢ <;> constructor <;> constructor <;>
              linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
        exact hsub i ((isClosed_Icc.prod isClosed_Icc).frontier_subset hx)
      · subst lo hi
        have hsub : ∀ i, (Icc ((![(-1,-1),(-1,k)] : Fin 2 → ℝ × ℝ) i).1
            ((![ (1,k),(1,1)] : Fin 2 → ℝ × ℝ) i).1 ×ˢ
            Icc ((![(-1,-1),(-1,k)] : Fin 2 → ℝ × ℝ) i).2
              ((![ (1,k),(1,1)] : Fin 2 → ℝ × ℝ) i).2) ⊆ dictPullbackRect := by
          intro j z hz
          fin_cases j <;> simp only [Set.mem_prod, Set.mem_Icc] at hz ⊢ <;>
            dsimp at hz ⊢ <;> constructor <;> constructor <;>
              linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
        exact hsub i ((isClosed_Icc.prod isClosed_Icc).frontier_subset hx)
    have hmap (A : Set dictPullbackRect) :
        g '' A = f '' (dictPullbackHomeomorph '' A) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨dictPullbackHomeomorph x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [hmap, himage]
    exact (hcell i).symm
  have houter' : g '' {x : dictPullbackRect | x.val ∈ frontier dictPullbackRect} = a.image := by
    have hmap (A : Set dictPullbackRect) :
        g '' A = f '' (dictPullbackHomeomorph '' A) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨dictPullbackHomeomorph x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    have hfront : dictPullbackHomeomorph '' {x : dictPullbackRect |
        x.val ∈ frontier dictPullbackRect} =
        {z : dictPullbackSquare | z.val ∈ frontier dictPullbackSquare} := by
      simpa [dictPullbackRect] using actualComponents_pullback_image_square_frontier
    rw [hmap, hfront]
    exact houter
  have hrectangle : (∀ i, ‖(m i).val‖ < 1) := fun i => hmi i
  exact rectangle_two_marked_preimage_components M a (-1) 1 (-1) 1
    (by norm_num) (by norm_num) lo hi hshape g hg F hFi m hrectangle honly
    hcell' houter'



theorem components_of_two_mark_closed_side
    (M : HyperellipticModel E S) (a : PuncturedCircle M)
    (U : Set S)
    (d : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure U)
    (hcl : closure U = U ∪ a.image)
    (hdb : ∀ x, (d x : S) ∈ a.image ↔ ‖x.val‖ = 1)
    (hdi : ∀ x, (d x : S) ∈ U ↔ ‖x.val‖ < 1)
    (hcount : (by classical exact (M.cover.branch.filter (· ∈ U)).card = 2)) :
    ∃ c d : Curve E, c.image ∪ d.image = M.cover.projection ⁻¹' a.image ∧
      Disjoint c.image d.image ∧ M.cover.deck '' c.image = d.image := by
  have hrect (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
        (EuclideanSpace.equiv (Fin 2) ℝ).symm
    let K := e '' (Icc a b ×ˢ Icc c d)
    ∃ h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K,
      (∀ x, (h x : Schoenflies.Plane) ∈ interior K ↔ ‖x.val‖ < 1) ∧
      (∀ x, (h x : Schoenflies.Plane) ∈ frontier K ↔ ‖x.val‖ = 1) := by
    dsimp only
    let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm
    let K := e '' (Icc a b ×ˢ Icc c d)
    change ∃ h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K, _
    have hcompact : IsCompact K :=
      (isCompact_Icc.prod isCompact_Icc).image e.continuous
    have hconvex : Convex ℝ K :=
      ((convex_Icc a b).prod (convex_Icc c d)).linear_image e.toLinearEquiv.toLinearMap
    have hne : (interior K).Nonempty := by
      have hm : ((a + b) / 2, (c + d) / 2) ∈ interior (Icc a b ×ˢ Icc c d) := by
        rw [interior_prod_eq, interior_Icc, interior_Icc]
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      refine ⟨e ((a + b) / 2, (c + d) / 2), ?_⟩
      change e.toHomeomorph ((a + b) / 2, (c + d) / 2) ∈
        interior (e.toHomeomorph '' (Icc a b ×ˢ Icc c d))
      rw [← e.toHomeomorph.image_interior]
      exact mem_image_of_mem e hm
    obtain ⟨g, hgi, hgc, hgf⟩ :=
      exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconvex hne hcompact.isBounded
    have hgK : g '' K = Metric.closedBall (0 : Schoenflies.Plane) 1 := by
      simpa [hcompact.isClosed.closure_eq] using hgc
    let h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K :=
      (Homeomorph.sets g (by
        ext x
        constructor
        · intro hx
          rw [← hgK]
          exact mem_image_of_mem g hx
        · intro hx
          rw [← hgK] at hx
          rcases hx with ⟨y, hy, hxy⟩
          exact g.injective hxy ▸ hy)).symm
    refine ⟨h, ?_, ?_⟩
    · intro x
      change g.symm x.val ∈ interior K ↔ ‖x.val‖ < 1
      rw [← mem_ball_zero_iff]
      constructor
      · intro hx
        rw [← hgi]
        exact ⟨g.symm x.val, hx, g.apply_symm_apply x.val⟩
      · intro hx
        rw [← hgi] at hx
        rcases hx with ⟨y, hy, hyx⟩
        simpa [← hyx] using hy
    · intro x
      change g.symm x.val ∈ frontier K ↔ ‖x.val‖ = 1
      rw [← dist_zero_right x.val]
      change g.symm x.val ∈ frontier K ↔ x.val ∈ Metric.sphere (0 : Schoenflies.Plane) 1
      constructor
      · intro hx
        rw [← hgf]
        exact ⟨g.symm x.val, hx, g.apply_symm_apply x.val⟩
      · intro hx
        rw [← hgf] at hx
        rcases hx with ⟨y, hy, hyx⟩
        simpa [← hyx] using hy
  classical
  let fd : C(Metric.closedBall (0 : Schoenflies.Plane) 1, S) :=
    ⟨fun x => (d x : S), continuous_subtype_val.comp d.continuous⟩
  have hfd : IsEmbedding fd := IsEmbedding.subtypeVal.comp d.isEmbedding
  have hdbrange : fd '' {x | ‖x.val‖ = 1} = a.image := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hdb x).mpr hx
    · intro hy
      let yy : closure U := ⟨y, hcl.symm ▸ Or.inr hy⟩
      refine ⟨d.symm yy, ?_, ?_⟩
      · apply (hdb _).mp
        simpa only [d.apply_symm_apply] using hy
      · change (d (d.symm yy) : S) = y
        rw [d.apply_symm_apply]
  have hdinterior : fd '' {x | ‖x.val‖ < 1} = U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hdi x).mpr hx
    · intro hy
      let yy : closure U := ⟨y, subset_closure hy⟩
      refine ⟨d.symm yy, ?_, ?_⟩
      · apply (hdi _).mp
        simpa only [d.apply_symm_apply] using hy
      · change (d (d.symm yy) : S) = y
        rw [d.apply_symm_apply]
  obtain ⟨h, hi, hb⟩ := hrect (-1) 1 (-1) 1 (by norm_num) (by norm_num)
  change Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ dictPullbackSquare at h
  change ∀ x, (h x : Schoenflies.Plane) ∈ interior dictPullbackSquare ↔ ‖x.val‖ < 1 at hi
  change ∀ x, (h x : Schoenflies.Plane) ∈ frontier dictPullbackSquare ↔ ‖x.val‖ = 1 at hb
  let f : C(dictPullbackSquare, S) := fd.comp ⟨h.symm, h.symm.continuous⟩
  have hf : IsEmbedding f := hfd.comp h.symm.isEmbedding
  have hboundary (z : dictPullbackSquare) :
      f z ∈ a.image ↔ z.val ∈ frontier dictPullbackSquare := by
    change (d (h.symm z) : S) ∈ a.image ↔ _
    rw [hdb, ← hb, h.apply_symm_apply]
  have hbrange : f '' {z : dictPullbackSquare | z.val ∈ frontier dictPullbackSquare} = a.image := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hboundary z).mpr hz
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hdbrange.symm ▸ hy
      refine ⟨h x, (hb x).mpr hx, ?_⟩
      change fd (h.symm (h x)) = y
      rw [h.symm_apply_apply]
      exact hxy
  have hirange : f '' {z : dictPullbackSquare | z.val ∈ interior dictPullbackSquare} = U := by
    rw [← hdinterior]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨h.symm z, ?_, rfl⟩
      apply (hi _).mp
      change z.val ∈ interior dictPullbackSquare at hz
      simpa only [h.apply_symm_apply] using hz
    · rintro ⟨x, hx, rfl⟩
      refine ⟨h x, (hi x).mpr hx, ?_⟩
      change fd (h.symm (h x)) = fd x
      rw [h.symm_apply_apply]
  have havoid : ∀ z, z.val ∈ frontier dictPullbackSquare → f z ∉ M.cover.branch := by
    intro z hz hbranch
    exact Set.disjoint_left.mp a.avoids_branch ((hboundary z).mpr hz) hbranch
  have hcard : (M.cover.branch.filter (fun b => b ∈ f '' {z |
      z.val ∈ interior dictPullbackSquare})).card = 2 := by
    rw [hirange]
    exact hcount
  exact two_marked_disc_chart_preimage_components M a f hf havoid hcard hbrange

/-- The source-selected two-mark closed disk is produced for every Circle24 object,
including its exact boundary and interior coordinates. -/
theorem actual_circle24_two_mark_closed_side (M : HyperellipticModel E S)
    (a : Circle24 M) :
    ∃ U : Set S, ∃ d : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure U,
      IsOpen U ∧ IsConnected U ∧ closure U = U ∪ a.val.image ∧
      (∀ x, (d x : S) ∈ a.val.image ↔ ‖x.val‖ = 1) ∧
      (∀ x, (d x : S) ∈ U ↔ ‖x.val‖ < 1) ∧
      (by classical exact (M.cover.branch.filter (· ∈ U)).card = 2) := by
  classical
  have hsplit : SplitsMarked M a.val 2 4 := by
    rcases a.property with h | h
    · exact h
    · obtain ⟨U,V,hU,hV,hUc,hVc,hUn,hVn,hd,hu,h4,h2⟩ := h
      exact ⟨V,U,hV,hU,hVc,hUc,hVn,hUn,hd.symm,
        (Set.union_comm V U).trans hu,h2,h4⟩
  obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,dU,dV,hUb,hVb,hUi,hVi,hclU,hclV⟩ :=
    M.puncturedCircle_closedSides a.val
  obtain ⟨W,Z,hWo,hZo,hWc,hZc,hWn,hZn,hWZ,hWZcover,hWcount,hZcount⟩ := hsplit
  have hWsub : W ⊆ U ∪ V := by
    rw [hcover,← hWZcover]
    exact subset_union_left
  have hUsub : U ⊆ W ∪ Z := by
    rw [hWZcover,← hcover]
    exact subset_union_left
  have hVsub : V ⊆ W ∪ Z := by
    rw [hWZcover,← hcover]
    exact subset_union_right
  have hEq : W = U ∨ W = V := by
    rcases hWc.isPreconnected.subset_or_subset hUo hVo hUV hWsub with hWU | hWV
    · left
      apply Set.Subset.antisymm hWU
      rcases hUc.isPreconnected.subset_or_subset hWo hZo hWZ hUsub with hUW | hUZ
      · exact hUW
      · obtain ⟨x,hx⟩ := hWn
        exact False.elim (Set.disjoint_left.mp hWZ hx (hUZ (hWU hx)))
    · right
      apply Set.Subset.antisymm hWV
      rcases hVc.isPreconnected.subset_or_subset hWo hZo hWZ hVsub with hVW | hVZ
      · exact hVW
      · obtain ⟨x,hx⟩ := hWn
        exact False.elim (Set.disjoint_left.mp hWZ hx (hVZ (hWV hx)))
  rcases hEq with hEq | hEq
  · refine ⟨U,dU,hUo,hUc,hclU,hUb,hUi,?_⟩
    rwa [← hEq]
  · refine ⟨V,dV,hVo,hVc,hclV,hVb,hVi,?_⟩
    rwa [← hEq]

/-- Actual component existence for every source 2|4 circle, obtained from
its selected two-mark disk and the proved two-cell lifting calculation. -/
theorem actual_circle24_preimage_two_components (M : HyperellipticModel E S)
    (a : Circle24 M) :
    ∃ c d : Curve E,
      c.image ∪ d.image = M.cover.projection ⁻¹' a.val.image ∧
      Disjoint c.image d.image ∧ M.cover.deck '' c.image = d.image := by
  obtain ⟨U,d,hUo,hUc,hcl,hb,hi,hcount⟩ := M.actual_circle24_two_mark_closed_side a
  exact components_of_two_mark_closed_side M a.val U d hcl hb hi hcount

omit [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] in
/-- A finite disjoint union of two embedded curves has exactly those
curves as its connected components. -/
theorem disjoint_curve_connectedComponentIn [T2Space E]
    (c d : Curve E) (hd : Disjoint c.image d.image) (x : E) (hx : x ∈ c.image) :
    connectedComponentIn (c.image ∪ d.image) x = c.image := by
  have hc : IsClosed c.image := (isCompact_range c.embedded.continuous).isClosed
  have hd' : IsClosed d.image := (isCompact_range d.embedded.continuous).isClosed
  have hconn : IsPreconnected c.image := isPreconnected_range c.embedded.continuous
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hyc
    have hyd : y ∈ d.image := (connectedComponentIn_subset _ _ hy).resolve_left hyc
    have hxK : x ∈ connectedComponentIn (c.image ∪ d.image) x :=
      mem_connectedComponentIn (Or.inl hx)
    obtain ⟨z,hzK,hzc,hzd⟩ := isPreconnected_closed_iff.mp
      isPreconnected_connectedComponentIn c.image d.image hc hd'
      (connectedComponentIn_subset _ _) ⟨x,hxK,hx⟩ ⟨y,hy,hyd⟩
    exact Set.disjoint_left.mp hd hzc hzd
  · exact hconn.subset_connectedComponentIn hx subset_union_left

/-- Every actual 2|4 lift consists of two genuine connected components,
each mapping injectively onto the entire downstairs circle. -/
theorem actual_circle24_components_project_bijectively (M : HyperellipticModel E S)
    (a : Circle24 M) :
    ∃ c d : Curve E,
      c.image ∪ d.image = M.cover.projection ⁻¹' a.val.image ∧
      Disjoint c.image d.image ∧ M.cover.deck '' c.image = d.image ∧
      Set.BijOn M.cover.projection c.image a.val.image ∧
      Set.BijOn M.cover.projection d.image a.val.image ∧
      (∀ x ∈ c.image, connectedComponentIn (M.cover.projection ⁻¹' a.val.image) x = c.image) ∧
      (∀ x ∈ d.image, connectedComponentIn (M.cover.projection ⁻¹' a.val.image) x = d.image) := by
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨c,d,hunion,hdisj,hdeck⟩ := M.actual_circle24_preimage_two_components a
  have hreverse : M.cover.deck '' d.image = c.image := by
    rw [← hdeck,Set.image_image]
    have hi : (fun x : E => M.cover.deck (M.cover.deck x)) = id :=
      funext M.cover.deck_involution
    rw [hi,Set.image_id]
  have hbij (c d : Curve E)
      (hu : c.image ∪ d.image = M.cover.projection ⁻¹' a.val.image)
      (hd : Disjoint c.image d.image) (he : M.cover.deck '' c.image = d.image) :
      Set.BijOn M.cover.projection c.image a.val.image := by
    constructor
    · intro x hx
      have hh : x ∈ M.cover.projection ⁻¹' a.val.image := hu ▸ Or.inl hx
      exact hh
    constructor
    · intro x hx y hy hxy
      rcases (M.cover.fiber_pair x y).mp hxy with hh | hh
      · exact hh.symm
      · exact False.elim (Set.disjoint_left.mp hd hy (he ▸ ⟨x,hx,hh.symm⟩))
    · intro y hy
      obtain ⟨x,hxy⟩ := M.cover.projection_surjective y
      have hxpre : x ∈ M.cover.projection ⁻¹' a.val.image := by
        change M.cover.projection x ∈ a.val.image
        rw [hxy]
        exact hy
      have hx : x ∈ c.image ∪ d.image := hu.symm ▸ hxpre
      rcases hx with hx | hx
      · exact ⟨x,hx,hxy⟩
      · obtain ⟨z,hz,hzx⟩ := he.symm ▸ hx
        exact ⟨z,hz,(M.cover.projection_deck z).symm.trans
          ((congrArg M.cover.projection hzx).trans hxy)⟩
  refine ⟨c,d,hunion,hdisj,hdeck,hbij c d hunion hdisj hdeck,
    hbij d c ((Set.union_comm _ _).trans hunion) hdisj.symm hreverse,?_,?_⟩
  · intro x hx
    rw [← hunion]
    exact disjoint_curve_connectedComponentIn c d hdisj x hx
  · intro x hx
    rw [← hunion,Set.union_comm]
    exact disjoint_curve_connectedComponentIn d c hdisj.symm x hx

/-- Each actual 2|4 boundary component projects homeomorphically, with the
homeomorphism's underlying function exactly the covering projection. -/
theorem actual_circle24_component_projection_homeomorphs
    (M : HyperellipticModel E S) (a : Circle24 M) :
    ∃ c d : Curve E,
      c.image ∪ d.image = M.cover.projection ⁻¹' a.val.image ∧
      Disjoint c.image d.image ∧ M.cover.deck '' c.image = d.image ∧
      ∃ hc : c.image ≃ₜ a.val.image, ∃ hd : d.image ≃ₜ a.val.image,
        (∀ x, (hc x).val = M.cover.projection x.val) ∧
        (∀ x, (hd x).val = M.cover.projection x.val) := by
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨c,d,hu,hdisj,hdeck,hc,hd,hcc,hdc⟩ :=
    M.actual_circle24_components_project_bijectively a
  have make (c : Curve E) (hc : Set.BijOn M.cover.projection c.image a.val.image) :
      ∃ h : c.image ≃ₜ a.val.image, ∀ x, (h x).val = M.cover.projection x.val := by
    let : CompactSpace c.image :=
      isCompact_iff_compactSpace.mp (isCompact_range c.embedded.continuous)
    let e : c.image ≃ a.val.image := hc.equiv M.cover.projection
    have he : Continuous e :=
      (M.cover.projection_continuous.comp continuous_subtype_val).subtype_mk _
    exact ⟨he.homeoOfEquivCompactToT2,fun _ => rfl⟩
  obtain ⟨ec,hec⟩ := make c hc
  obtain ⟨ed,hed⟩ := make d hd
  exact ⟨c,d,hu,hdisj,hdeck,ec,ed,hec,hed⟩

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.two_cell_preimage_components
#print axioms CurveComplex.HyperellipticModel.actual_circle24_preimage_two_components
#print axioms CurveComplex.HyperellipticModel.actual_circle24_components_project_bijectively
#print axioms CurveComplex.HyperellipticModel.actual_circle24_component_projection_homeomorphs
