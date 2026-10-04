import CurveComplexGenusTwo.Topology.WeightedSurgery.OldLoopRawPartitionHeader
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import Mathlib.Topology.Subpath
import CurveComplexGenusTwo.Dictionary.JordanEssentiality
namespace CurveComplex.HyperellipticModel.ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_RawSpliceHelperHeaders_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

theorem rawSplices_exists (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P) :
    ∃ raw : Bool → MarkedArc M,
      (∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side) ∧
      (∀ side, (raw side).map ⟨0, by norm_num⟩ = anchor.val.map ⟨0, by norm_num⟩) ∧
      (∀ side, (raw side).map ⟨1, by norm_num⟩ = (P.rep x.selected).val.map
        (if side then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩)) := by
  have one : ∀ side : Bool, ∃ c : MarkedArc M,
      c.image = spliceTrace M anchor (P.rep x.selected) x.t x.s side ∧
      c.map 0 = anchor.val.map 0 ∧
      c.map 1 = (P.rep x.selected).val.map (if side then 1 else 0) := by
    intro side
    have concat : ∀ {p q r : S} (a : Path p q) (b : Path q r),
        Function.Injective a → Function.Injective b →
        (∀ t u, a t = b u → (t = 1 ∧ u = 0) ∨ (t = 0 ∧ u = 1)) →
        p ∈ M.cover.branch → r ∈ M.cover.branch →
        (∀ t, a t ∈ M.cover.branch → t = 0) →
        (∀ t, b t ∈ M.cover.branch → t = 1) →
        ∃ c : MarkedArc M, c.map = a.trans b := by
      intro p q r a b ha hb hc hp hr ham hbm
      let c := a.trans b
      have hinj : ∀ t u : Interval, c t = c u →
          t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0) := by
        intro t u he
        dsimp [c] at he
        rw [Path.trans_apply, Path.trans_apply] at he
        split_ifs at he with ht hu hu
        · left
          apply Subtype.ext
          have hv := congrArg Subtype.val (ha he)
          dsimp at hv
          linarith
        · rcases hc _ _ he with ⟨hat, hbu⟩ | ⟨hat, hbu⟩
          · have hv := congrArg Subtype.val hbu
            dsimp at hv
            have hult := lt_of_not_ge hu
            exfalso
            linarith
          · right; left
            constructor <;> apply Subtype.ext
            · have hv := congrArg Subtype.val hat
              dsimp at hv
              change t.val = 0
              linarith
            · have hv := congrArg Subtype.val hbu
              dsimp at hv
              change u.val = 1
              linarith
        · rcases hc _ _ he.symm with ⟨hau, hbt⟩ | ⟨hau, hbt⟩
          · have hv := congrArg Subtype.val hbt
            dsimp at hv
            have htlt := lt_of_not_ge ht
            exfalso
            linarith
          · right; right
            constructor <;> apply Subtype.ext
            · have hv := congrArg Subtype.val hbt
              dsimp at hv
              change t.val = 1
              linarith
            · have hv := congrArg Subtype.val hau
              dsimp at hv
              change u.val = 0
              linarith
        · left
          apply Subtype.ext
          have hv := congrArg Subtype.val (hb he)
          dsimp at hv
          linarith
      refine ⟨{
        map := c
        continuous := c.continuous
        injective_except_loop_closure := hinj
        start_marked := ?_
        end_marked := ?_
        marked_only_at_ends := ?_ }, rfl⟩
      · change c 0 ∈ M.cover.branch
        rw [c.source]
        exact hp
      · change c 1 ∈ M.cover.branch
        rw [c.target]
        exact hr
      · intro t ht
        dsimp [c] at ht
        rw [Path.trans_apply] at ht
        split_ifs at ht with h
        · left
          apply Subtype.ext
          have hv := congrArg Subtype.val (ham _ ht)
          dsimp at hv
          linarith
        · right
          apply Subtype.ext
          have hv := congrArg Subtype.val (hbm _ ht)
          dsimp at hv
          linarith
    let a : Path (anchor.val.map 0) (anchor.val.map 1) :=
      ⟨⟨anchor.val.map, anchor.val.continuous⟩, rfl, rfl⟩
    let old := P.rep x.selected
    let b : Path (old.val.map 0) (old.val.map 1) :=
      ⟨⟨old.val.map, old.val.continuous⟩, rfl, rfl⟩
    let e : Interval := if side then 1 else 0
    let k := Set.Icc.convexComb (0 : Interval) x.t
    let l := Set.Icc.convexComb x.s e
    have hk (u : Interval) : (k u).val = u.val * x.t.val := by simp [k]
    have hl (u : Interval) : (l u).val = (1-u.val)*x.s.val+u.val*e.val := rfl
    have hki : Function.Injective k := by
      intro t u he
      have hv := congrArg Subtype.val he
      rw [hk, hk] at hv
      apply Subtype.ext
      exact mul_right_cancel₀ (ne_of_gt x.t_interior.1) hv
    have hli : Function.Injective l := by
      intro t u he
      have hv := congrArg Subtype.val he
      rw [hl, hl] at hv
      apply Subtype.ext
      cases side <;> norm_num [e] at hv
      · rcases hv with hv | hv
        · exact hv
        · have hz := congrArg Subtype.val hv
          exact False.elim ((ne_of_gt x.s_interior.1) hz)
      · have hv' : t.val * (1-x.s.val) = u.val * (1-x.s.val) := by
          nlinarith [hv]
        exact mul_right_cancel₀ (ne_of_gt (sub_pos.mpr x.s_interior.2)) hv'
    have hklt (u : Interval) : (k u).val < 1 := by
      rw [hk]
      nlinarith [u.property.1, u.property.2, x.t_interior.1, x.t_interior.2]
    have hlex (u : Interval) :
        (side = true → 0 < (l u).val) ∧
        (side = false → (l u).val < 1) := by
      constructor
      · intro hs
        subst side
        rw [hl]
        change 0 < (1-u.val)*x.s.val+u.val*1
        nlinarith [u.property.1, u.property.2, x.s_interior.1, x.s_interior.2]
      · intro hs
        subst side
        rw [hl]
        change (1-u.val)*x.s.val+u.val*0 < 1
        nlinarith [u.property.1, u.property.2, x.s_interior.1, x.s_interior.2]
    let A := a.subpath 0 x.t
    let B := (b.subpath x.s e).cast x.same_point rfl
    have hAi : Function.Injective A := by
      intro t u he
      change anchor.val.map (k t) = anchor.val.map (k u) at he
      rcases anchor.val.injective_except_loop_closure _ _ he with he | he | he
      · exact hki he
      · have hv := congrArg Subtype.val he.2
        exact False.elim ((ne_of_lt (hklt u)) hv)
      · have hv := congrArg Subtype.val he.1
        exact False.elim ((ne_of_lt (hklt t)) hv)
    have hBi : Function.Injective B := by
      intro t u he
      change old.val.map (l t) = old.val.map (l u) at he
      rcases old.val.injective_except_loop_closure _ _ he with he | he | he
      · exact hli he
      · cases side
        · have hv := congrArg Subtype.val he.2
          exact False.elim ((ne_of_lt ((hlex u).2 rfl)) hv)
        · have hv := congrArg Subtype.val he.1
          exact False.elim ((ne_of_gt ((hlex t).1 rfl)) hv)
      · cases side
        · have hv := congrArg Subtype.val he.1
          exact False.elim ((ne_of_lt ((hlex t).2 rfl)) hv)
        · have hv := congrArg Subtype.val he.2
          exact False.elim ((ne_of_gt ((hlex u).1 rfl)) hv)
    have hAm : ∀ t, A t ∈ M.cover.branch → t = 0 := by
      intro t ht
      change anchor.val.map (k t) ∈ M.cover.branch at ht
      rcases anchor.val.marked_only_at_ends _ ht with he | he
      · apply hki
        simpa [k] using he
      · have hv := congrArg Subtype.val he
        exact False.elim ((ne_of_lt (hklt t)) hv)
    have hBm : ∀ t, B t ∈ M.cover.branch → t = 1 := by
      intro t ht
      change old.val.map (l t) ∈ M.cover.branch at ht
      rcases old.val.marked_only_at_ends _ ht with he | he
      · cases side
        · apply hli
          simpa [l,e] using he
        · have hv := congrArg Subtype.val he
          exact False.elim ((ne_of_gt ((hlex t).1 rfl)) hv)
      · cases side
        · have hv := congrArg Subtype.val he
          exact False.elim ((ne_of_lt ((hlex t).2 rfl)) hv)
        · apply hli
          simpa [l,e] using he
    have hcross : ∀ t u, A t = B u → (t = 1 ∧ u = 0) ∨ (t = 0 ∧ u = 1) := by
      intro t u he
      by_cases ht0 : t = 0
      · right
        refine ⟨ht0, hBm u ?_⟩
        rw [← he, ht0, A.source]
        exact anchor.val.start_marked
      by_cases ht1 : t = 1
      · left
        refine ⟨ht1, ?_⟩
        apply hBi
        rw [← he, ht1, A.target, B.source]
        rfl
      · have htpos : 0 < t.val := by
          have hn : t.val ≠ 0 := by intro h; exact ht0 (Subtype.ext h)
          exact lt_of_le_of_ne t.property.1 hn.symm
        have htlt : t.val < 1 := by
          have hn : t.val ≠ 1 := by intro h; exact ht1 (Subtype.ext h)
          exact lt_of_le_of_ne t.property.2 hn
        have hktpos : 0 < (k t).val := by rw [hk]; exact mul_pos htpos x.t_interior.1
        have hktlt : (k t).val < x.t.val := by
          rw [hk]
          nlinarith [x.t_interior.1]
        have hmark : anchor.val.map (k t) ∉ (M.cover.branch : Set S) := by
          intro hm
          rcases anchor.val.marked_only_at_ends _ hm with hm | hm
          · have hv := congrArg Subtype.val hm
            exact (ne_of_gt hktpos) hv
          · have hv := congrArg Subtype.val hm
            exact (ne_of_lt (hklt t)) hv
        change anchor.val.map (k t) = old.val.map (l u) at he
        exact False.elim (x.first x.selected (k t) hktpos hktlt ⟨⟨l u, he.symm⟩, hmark⟩)
    obtain ⟨c, hc⟩ := concat A B hAi hBi hcross anchor.val.start_marked
      (by cases side <;> simp only [e, Bool.false_eq_true, ↓reduceIte]
          · exact old.val.start_marked
          · exact old.val.end_marked) hAm hBm
    refine ⟨c, ?_, ?_, ?_⟩
    · change Set.range c.map = _
      rw [hc, Path.trans_range]
      change Set.range (a.subpath 0 x.t) ∪ Set.range (b.subpath x.s e) = _
      rw [Path.range_subpath, Path.range_subpath]
      simp only [spliceTrace]
      congr 1
      · congr 1
        ext r
        simp only [Set.mem_uIcc, Set.mem_setOf_eq]
        constructor
        · rintro (⟨_, h⟩ | ⟨_, h⟩)
          · exact h
          · exact h.trans x.t.property.1
        · intro h
          exact Or.inl ⟨r.property.1, h⟩
      · cases side <;> simp only [e, Bool.false_eq_true, ↓reduceIte]
        · congr 1
          ext r
          simp only [Set.mem_uIcc, Set.mem_setOf_eq]
          constructor
          · rintro (⟨_, h⟩ | ⟨_, h⟩)
            · exact h.trans x.s.property.1
            · exact h
          · intro h
            exact Or.inr ⟨r.property.1, h⟩
        · congr 1
          ext r
          simp only [Set.mem_uIcc, Set.mem_setOf_eq]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩)
            · exact h
            · exact x.s.property.2.trans h
          · intro h
            exact Or.inl ⟨h, r.property.2⟩
    · rw [hc]
      exact (A.trans B).source
    · rw [hc]
      exact (A.trans B).target
  choose raw ht hs he using one
  exact ⟨raw, ht, hs, he⟩

theorem rawSplices_essential_nonempty (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (raw : Bool → MarkedArc M)
    (htrace : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
    (hstart : ∀ side, (raw side).map ⟨0, by norm_num⟩ = anchor.val.map ⟨0, by norm_num⟩)
    (hend : ∀ side, (raw side).map ⟨1, by norm_num⟩ = (P.rep x.selected).val.map
      (if side then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩)) :
    ∃ side, IsEssentialMarkedArc M (raw side) := by
  have hstart01 : ∀ side, (raw side).map 0 = anchor.val.map 0 := by
    intro side; exact hstart side
  have hend01 : ∀ side, (raw side).map 1 = (P.rep x.selected).val.map
      (if side then 1 else 0) := by
    intro side; exact hend side
  by_cases hcase : (P.rep x.selected).val.map 0 ≠ (P.rep x.selected).val.map 1 ∨
      anchor.val.map 0 ≠ (P.rep x.selected).val.map 0
  · by_cases hf : (raw false).map 0 ≠ (raw false).map 1
    · exact ⟨false, Or.inl hf⟩
    · have hf' : (raw false).map 0 = (raw false).map 1 := not_ne_iff.mp hf
      have hbase : anchor.val.map 0 = (P.rep x.selected).val.map 0 := by
        simpa only [hstart01, hend01, Bool.false_eq_true, ↓reduceIte] using hf'
      have ht : (raw true).map 0 ≠ (raw true).map 1 := by
        intro he
        have hbase' : anchor.val.map 0 = (P.rep x.selected).val.map 1 := by
          simpa only [hstart01, hend01, ↓reduceIte] using he
        rcases hcase with hcase | hcase
        · exact hcase (hbase.symm.trans hbase')
        · exact hcase hbase
      exact ⟨true, Or.inl ht⟩
  · have hloop : (P.rep x.selected).val.map 0 = (P.rep x.selected).val.map 1 :=
      not_ne_iff.mp (not_or.mp hcase).1
    have hbase : anchor.val.map 0 = (P.rep x.selected).val.map 0 :=
      not_ne_iff.mp (not_or.mp hcase).2
    obtain ⟨D, i, U, initial_inside, components, frontiers, closed, partition, disj⟩ :=
      oldLoop_rawSplices_component_partition M anchor F P x hloop hbase raw htrace hstart hend
    have old_marks : ∀ j : Fin 2, ∃ b, b ∈ M.cover.branch ∧ b ∈ D.side j := by
      rcases (P.rep x.selected).property with hne | hall
      · exact False.elim (hne hloop)
      · intro j; exact hall (D.side j) (D.discs j).component
    have outside : ∃ c, c ∈ M.cover.branch ∧ c ∉ closure (D.side i) := by
      fin_cases i
      · obtain ⟨c, hc, hc1⟩ := old_marks 1
        refine ⟨c, hc, ?_⟩
        intro hcl
        rcases (D.discs 0).closure_eq ▸ hcl with hc0 | hcA
        · exact Set.disjoint_left.mp D.disjoint hc0 hc1
        · exact (D.discs 1).component.2.2.1 hc1 hcA
      · obtain ⟨c, hc, hc0⟩ := old_marks 0
        refine ⟨c, hc, ?_⟩
        intro hcl
        rcases (D.discs 1).closure_eq ▸ hcl with hc1 | hcA
        · exact Set.disjoint_left.mp D.disjoint hc0 hc1
        · exact (D.discs 0).component.2.2.1 hc0 hcA
    obtain ⟨b, hb, hbi⟩ := old_marks i
    have hbcut : b ∉ anchor.val.map '' Set.Icc (0 : Interval) x.t := by
      rintro ⟨r, hr, he⟩
      have hm : anchor.val.map r ∈ M.cover.branch := he ▸ hb
      rcases anchor.val.marked_only_at_ends r hm with h0 | h1
      · have hbA : b ∈ (P.rep x.selected).val.image := by
          refine ⟨0, ?_⟩
          exact hbase.symm.trans ((congrArg anchor.val.map h0).symm.trans he)
        exact (D.discs i).component.2.2.1 hbi hbA
      · have hv : r.val = 1 := congrArg Subtype.val h1
        have hr' : r.val ≤ x.t.val := hr.2
        linarith [x.t_interior.2]
    have hbu : b ∈ U false ∪ U true := partition ▸ ⟨hbi, hbcut⟩
    have certificate : ∀ (a : MarkedArc M), a.map 0 = a.map 1 →
        ∀ V : Set S, IsComplementComponent a.image V →
        (∃ b, b ∈ M.cover.branch ∧ b ∈ V) →
        (∃ c, c ∈ M.cover.branch ∧ c ∉ closure V) → IsEssentialMarkedArc M a := by
      intro a hloop U hU hin hout
      obtain ⟨D⟩ := markedLoop_disc_decomposition_exists M a hloop
      obtain ⟨j, hje⟩ := (D.all_components U).mp hU
      obtain ⟨b, hb, hbU⟩ := hin
      obtain ⟨c, hc, hcU⟩ := hout
      have hcA : c ∉ a.image := by
        intro hcA
        apply hcU
        rw [hje, (D.discs j).closure_eq]
        exact Or.inr hcA
      have hcside : c ∈ D.side 0 ∪ D.side 1 := D.complement.symm ▸ hcA
      have hall : ∀ i : Fin 2, ∃ z, z ∈ M.cover.branch ∧ z ∈ D.side i := by
        fin_cases j
        · have hb0 : b ∈ D.side 0 := hje ▸ hbU
          have hc1 : c ∈ D.side 1 := by
            rcases hcside with hc0 | hc1
            · exact False.elim (hcU (hje.symm ▸ subset_closure hc0))
            · exact hc1
          intro i
          fin_cases i
          · exact ⟨b, hb, hb0⟩
          · exact ⟨c, hc, hc1⟩
        · have hb1 : b ∈ D.side 1 := hje ▸ hbU
          have hc0 : c ∈ D.side 0 := by
            rcases hcside with hc0 | hc1
            · exact hc0
            · exact False.elim (hcU (hje.symm ▸ subset_closure hc1))
          intro i
          fin_cases i
          · exact ⟨c, hc, hc0⟩
          · exact ⟨b, hb, hb1⟩
      right
      intro V hV
      obtain ⟨i, rfl⟩ := (D.all_components V).mp hV
      exact hall i
    have essential : ∀ side, b ∈ U side → IsEssentialMarkedArc M (raw side) := by
      intro side hbU
      refine certificate (raw side) ?_ (U side) (components side) ⟨b, hb, hbU⟩ ?_
      · rw [hstart01, hend01, hbase]
        cases side
        · rfl
        · exact hloop
      · obtain ⟨c, hc, hcOut⟩ := outside
        exact ⟨c, hc, fun h => hcOut (closed side h)⟩
    rcases hbu with hf | ht
    · exact ⟨false, essential false hf⟩
    · exact ⟨true, essential true ht⟩



end CurveComplex.HyperellipticModel.ArcSurgery
