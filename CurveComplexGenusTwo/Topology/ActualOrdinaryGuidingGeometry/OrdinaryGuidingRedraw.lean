import OrdinaryContactGapMatching
import OrdinarySignedPieceFamily
import RegionalWeightedMovieDefinitions
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.GapMatchingTools
import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.CornerGeometryTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.DiskExteriorHalfTools

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open CurveComplex.BranchedDoubleCover
open scoped BigOperators
set_option autoImplicit false
noncomputable local instance ordinaryGuidingRedrawLocalDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- G2: select one common parameter and redraw inside the literal G1 chain. -/
theorem regional_ordinary_guiding_redraw_from_signed_pieces
    {S ι : Type} [TopologicalSpace S] [Fintype ι] [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (f : Option ι → C(Interval,↥F)) (v w : ι)
    (d : PairedBigonDisk F {y | y.val ∈ frontier F} (f (some v)) (f (some w)))
    (A B : Interval) (Edisk Eguide : OpenPartialHomeomorph S Plane)
    (hGuideSource : Eguide.source ⊆ Edisk.source)
    (hGuideInterior : Eguide.source ⊆ interior F)
    (hGuideAxis : ∀ y ∈ Eguide.source,
      y ∈ range (fun q => (f (some w) q).val) ↔ Eguide y 1 = 0)
    (ha : IsEmbedding (f (some v)))
    (D : OrdinarySignedPieceFamily F f v w d A B Edisk Eguide) :
    ∃ τ : Interval, 0 < τ.val ∧ τ.val < D.ε ∧
      ∃ gap : (k : Fin (D.m+1)) →
        Path (D.R ⟨k.val,by omega⟩ τ) (D.L ⟨k.val+1,by omega⟩ τ),
        (∀ k, IsEmbedding (gap k) ∧
          (∀ i : Option ι, Disjoint (range (gap k)) (range (f i))) ∧
          ∀ s : Interval, (gap k s).val ∈ Eguide.source ∧
            Eguide (gap k s).val =
              (1-s.val) • Eguide (D.R ⟨k.val,by omega⟩ τ).val +
                s.val • Eguide (D.L ⟨k.val+1,by omega⟩ τ).val) ∧
        ∃ n : Path (f (some v) D.l) (f (some v) D.r),
          IsEmbedding n ∧ range n ⊆ {y | y.val ∈ Edisk.source} ∧
          range n ∩ range (f (some v)) = {f (some v) D.l,f (some v) D.r} ∧
          Disjoint (range n) (range (f (some w))) ∧
          range n ⊆ (⋃ k : Fin (D.m+2), range (D.piece k τ)) ∪
            (⋃ k : Fin (D.m+1), range (gap k)) ∧
          (∀ i : Option ι, i ≠ some v → (range n ∩ range (f i)).Finite) ∧
          ∀ i : Option ι, i ≠ some v → i ≠ some w →
            (range n ∩ range (f i)).ncard ≤
              ((range d.second \ ({d.first 0,d.first 1} : Set ↥F)) ∩ range (f i)).ncard +
                (({d.first 0,d.first 1} : Set ↥F) ∩ range (f i)).ncard := by
  classical
  have actual_chart_continuous_arc
      (E : OpenPartialHomeomorph S Plane) (f : C(Interval,S))
      (hf : Topology.IsEmbedding f) (hS : ∀ t, f t ∈ E.source) :
      IsArcBetween (E '' Set.range f) (E (f 0)) (E (f 1)) := by
    let g : C(Interval,Plane) := ⟨fun t => E (f t),
      E.continuousOn.comp_continuous f.continuous hS⟩
    let F : ℝ → Plane := Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num) g
    have hF (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : F t = g ⟨t,ht⟩ := by
      simp only [F,Set.IccExtend,Function.comp_apply,Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) ht]
    have hcont : Continuous F := g.continuous.Icc_extend'
    have hinj : Set.InjOn F unitInterval := by
      intro x hx y hy hxy
      rw [hF x hx,hF y hy] at hxy
      have hh := hf.injective (E.injOn (hS ⟨x,hx⟩) (hS ⟨y,hy⟩) hxy)
      exact congrArg Subtype.val hh
    have hrange : F '' unitInterval = E '' Set.range f := by
      ext x
      constructor
      · rintro ⟨t,ht,rfl⟩
        exact ⟨f ⟨t,ht⟩,⟨⟨t,ht⟩,rfl⟩,(hF t ht).symm⟩
      · rintro ⟨_,⟨t,rfl⟩,rfl⟩
        exact ⟨t.val,t.property,hF t.val t.property⟩
    refine ⟨F,hcont.continuousOn,hinj,hrange,?_,?_⟩
    · exact hF 0 (by constructor <;> norm_num)
    · exact hF 1 (by constructor <;> norm_num)

  have actual_pullback_chart_arc
      (E : OpenPartialHomeomorph S Plane) (a b : S)
      (ha : a ∈ E.source) (hb : b ∈ E.source)
      (A : Set Plane) (hA : IsArcBetween A (E a) (E b)) (hAt : A ⊆ E.target) :
      ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
        Set.range f = E.symm '' A ∧ f 0 = a ∧ f 1 = b := by
    obtain ⟨F,hF,hFi,hFr,hF0,hF1⟩ := hA
    have hFt (t : Interval) : F t.val ∈ E.target :=
      hAt (hFr ▸ ⟨t.val,t.property,rfl⟩)
    have hFc : Continuous (fun t : Interval => F t.val) :=
      continuousOn_iff_continuous_domRestrict.mp hF
    let f : C(Interval,S) := ⟨fun t => E.symm (F t.val),
      E.symm.continuousOn.comp_continuous hFc hFt⟩
    have hfi : Function.Injective f := by
      intro x y he
      have hh := E.symm.injOn (hFt x) (hFt y) he
      exact Subtype.ext (hFi x.property y.property hh)
    refine ⟨f,(f.continuous.isClosedEmbedding hfi).isEmbedding,?_,?_,?_⟩
    · ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨F t.val,hFr ▸ ⟨t.val,t.property,rfl⟩,rfl⟩
      · rintro ⟨q,hq,rfl⟩
        rw [←hFr] at hq
        obtain ⟨t,ht,rfl⟩ := hq
        exact ⟨⟨t,ht⟩,rfl⟩
    · change E.symm (F 0) = a
      rw [hF0,E.left_inv ha]
    · change E.symm (F 1) = b
      rw [hF1,E.left_inv hb]

  have actual_finite_union_card_bound {X J : Type} [Fintype J]
      (A : J → Set X) (hA : ∀ j, (A j).Finite) :
      (⋃ j, A j).Finite ∧ (⋃ j, A j).ncard ≤ ∑ j, (A j).ncard := by
    classical
    have hF (F : Finset J) : (⋃ j ∈ F, A j).Finite ∧
        (⋃ j ∈ F, A j).ncard ≤ ∑ j ∈ F, (A j).ncard := by
      induction F using Finset.induction with
      | empty => simp
      | @insert j F hj ih =>
          have he : (⋃ k ∈ insert j F, A k) = A j ∪ ⋃ k ∈ F, A k := by
            ext x
            simp only [Set.mem_iUnion,Finset.mem_insert,Set.mem_union]
            aesop
          rw [he,Finset.sum_insert hj]
          exact ⟨(hA j).union ih.1,(Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih.2 _)⟩
    simpa using hF Finset.univ

  have actual_filter_indicator_card {J : Type} [Fintype J]
      (p : J → Prop) [DecidablePred p] :
      (∑ j, if p j then 1 else 0) = Nat.card {j : J // p j} := by
    classical
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    simp

  have hGaps : ∃ τ : Interval, 0 < τ.val ∧ τ.val < D.ε ∧
      ∃ gap : (k : Fin (D.m+1)) →
        Path (D.R ⟨k.val,by omega⟩ τ) (D.L ⟨k.val+1,by omega⟩ τ),
        ∀ k, IsEmbedding (gap k) ∧
          (∀ i : Option ι, Disjoint (range (gap k)) (range (f i))) ∧
          ∀ s : Interval, (gap k s).val ∈ Eguide.source ∧
            Eguide (gap k s).val =
              (1-s.val) • Eguide (D.R ⟨k.val,by omega⟩ τ).val +
                s.val • Eguide (D.L ⟨k.val+1,by omega⟩ τ).val := by
    let coordinates : Plane ≃L[ℝ] (ℝ × ℝ) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
    let U : Set S := Eguide.source
    let W : Set (ℝ × ℝ) := coordinates '' Eguide.target
    let e : ↥U ≃ₜ ↥W := Eguide.toHomeomorphSourceTarget.trans
      (coordinates.toHomeomorph.image Eguide.target)
    have he (y : ↥U) : (e y).val = coordinates (Eguide y.val) := rfl
    have hW : IsOpen W := coordinates.toHomeomorph.isOpenMap _ Eguide.open_target
    let J := {i : Option ι // i ≠ some w}
    let K : J → Set S := fun i => Subtype.val '' range (f i.val)
    have hK (j : J) : IsCompact (K j) := by
      exact (isCompact_range (f j.val).continuous).image continuous_subtype_val
    let G : Set S := range (fun q => (f (some w) q).val)
    have haxisGuide (y : ↥U) : y.val ∈ G ↔ (e y).val.2 = 0 := by
      exact hGuideAxis y.val y.property
    let left : Fin (D.m+1) → C(Interval,↥U) := fun k =>
      ⟨fun t => ⟨(D.rescaledL k t).val.val,(D.rescaledL k t).property⟩,
        (continuous_subtype_val.comp (continuous_subtype_val.comp (D.rescaledL k).continuous)).subtype_mk _⟩
    let right : Fin (D.m+1) → C(Interval,↥U) := fun k =>
      ⟨fun t => ⟨(D.rescaledR k t).val.val,(D.rescaledR k t).property⟩,
        (continuous_subtype_val.comp (continuous_subtype_val.comp (D.rescaledR k).continuous)).subtype_mk _⟩
    have hzero : intervalAffine 0 D.small 0 = 0 := by
      apply Subtype.ext
      simp [intervalAffine]
    have hleft (k : Fin (D.m+1)) (t : Interval) :
        (left k t).val = (D.R ⟨k.val,by omega⟩ (intervalAffine 0 D.small t)).val :=
      congrArg Subtype.val (D.rescale_eq k t).1
    have hright (k : Fin (D.m+1)) (t : Interval) :
        (right k t).val = (D.L ⟨k.val+1,by omega⟩ (intervalAffine 0 D.small t)).val :=
      congrArg Subtype.val (D.rescale_eq k t).2
    have hsmall (t : Interval) (ht : 0 < t.val) :
        0 < (intervalAffine 0 D.small t).val ∧ (intervalAffine 0 D.small t).val < D.ε := by
      change 0 < (1-t.val)*0+t.val*D.small.val ∧ (1-t.val)*0+t.val*D.small.val < D.ε
      constructor
      · nlinarith [D.small_pos]
      · have hle := mul_le_mul_of_nonneg_right t.property.2 D.small_pos.le
        nlinarith [D.small_bound]
    have hProduce (k : Fin (D.m+1)) : ∃ ρ : ℝ, 0 < ρ ∧
        ∀ t : Interval, 0 < t.val → t.val < ρ →
        ∃ q : Path (left k t).val (right k t).val,
          IsEmbedding q ∧ Disjoint (range q) G ∧
          (∀ j : J, Disjoint (range q) (K j)) ∧
          ∀ s : Interval, ∃ y : ↥U, y.val = q s ∧
            (e y).val = (1-s.val) • (e (left k t)).val + s.val • (e (right k t)).val := by
      apply actual_compact_family_contact_gap_matching K hK G U W hW e
        (D.gapA k) (D.gapL k) (D.gapR k) (D.gapB k)
        (D.gap_order k).1 (D.gap_order k).2.1 (D.gap_order k).2.2
        (L := left k) (R := right k) (σ := D.σ)
      · intro x hx
        let y : ↥U := ⟨Eguide.symm (Plane.mk x 0),Eguide.map_target (D.gap_axis k x hx).1⟩
        refine ⟨e y,?_,?_⟩
        · rw [he]
          change coordinates (Eguide (Eguide.symm (Plane.mk x 0))) = (x,0)
          rw [Eguide.right_inv (D.gap_axis k x hx).1]
          rfl
        · intro j
          rw [e.symm_apply_apply]
          exact (D.gap_axis k x hx).2 j.val j.property
      · exact haxisGuide
      · rw [he,hleft,hzero,(D.gap_zero k).1]
        rfl
      · rw [he,hright,hzero,(D.gap_zero k).2]
        rfl
      · exact D.sign_unit
      · intro t ht
        rw [he,he,hleft,hright]
        exact D.internal_sign _ (hsmall t ht).1 (hsmall t ht).2 k
    choose ρ hρ hq using hProduce
    have hcommon : ∃ μ : ℝ, 0 < μ ∧ ∀ k, μ ≤ ρ k := by
      have hs (s : Finset (Fin (D.m+1))) : ∃ μ : ℝ, 0 < μ ∧ ∀ k ∈ s, μ ≤ ρ k := by
        induction s using Finset.induction with
        | empty => exact ⟨1,by norm_num,by simp⟩
        | @insert k s hk ih =>
          obtain ⟨μ,hμ,hm⟩ := ih
          refine ⟨min (ρ k) μ,lt_min (hρ k) hμ,?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact min_le_left _ _
          · exact (min_le_right _ _).trans (hm j hj)
      simpa using hs Finset.univ
    obtain ⟨μ,hμ,hμρ⟩ := hcommon
    let t : Interval := ⟨min 1 μ / 2,by
      have hp := lt_min (by norm_num : (0:ℝ) < 1) hμ
      constructor
      · linarith
      · have hm := min_le_left (1:ℝ) μ; linarith⟩
    have ht : 0 < t.val := by
      change 0 < min 1 μ / 2
      exact div_pos (lt_min (by norm_num) hμ) (by norm_num)
    have htρ (k : Fin (D.m+1)) : t.val < ρ k := by
      have hm : min 1 μ ≤ ρ k := (min_le_right _ _).trans (hμρ k)
      change min 1 μ / 2 < ρ k
      have hp := lt_min (by norm_num : (0:ℝ) < 1) hμ
      linarith
    let τ := intervalAffine 0 D.small t
    have hτ : 0 < τ.val ∧ τ.val < D.ε := hsmall t ht
    have hqk (k : Fin (D.m+1)) := hq k t ht (htρ k)
    choose q hqEmb hqG hqK hqEq using hqk
    have hqS (k : Fin (D.m+1)) (s : Interval) : q k s ∈ Eguide.source := by
      obtain ⟨y,hy,heq⟩ := hqEq k s
      exact hy ▸ y.property
    have hqF (k : Fin (D.m+1)) (s : Interval) : q k s ∈ F :=
      interior_subset (hGuideInterior (hqS k s))
    let gap : (k : Fin (D.m+1)) → Path (D.R ⟨k.val,by omega⟩ τ)
        (D.L ⟨k.val+1,by omega⟩ τ) := fun k =>
      { toFun := fun s => ⟨q k s,hqF k s⟩
        continuous_toFun := (q k).continuous.subtype_mk _
        source' := Subtype.ext ((q k).source.trans (hleft k t))
        target' := Subtype.ext ((q k).target.trans (hright k t)) }
    refine ⟨τ,hτ.1,hτ.2,gap,?_⟩
    intro k
    refine ⟨((gap k).continuous.isClosedEmbedding (fun a b h =>
      (hqEmb k).injective (congrArg Subtype.val h))).isEmbedding,?_,?_⟩
    · intro i
      apply disjoint_left.mpr
      rintro y ⟨s,rfl⟩ hy
      by_cases hi : i = some w
      · subst i
        exact disjoint_left.mp (hqG k) ⟨s,rfl⟩
          (by obtain ⟨u,hu⟩ := hy; exact ⟨u,congrArg Subtype.val hu⟩)
      · exact disjoint_left.mp (hqK k ⟨i,hi⟩) ⟨s,rfl⟩ ⟨gap k s,hy,rfl⟩
    · intro s
      refine ⟨hqS k s,?_⟩
      obtain ⟨y,hy,heq⟩ := hqEq k s
      apply coordinates.injective
      rw [map_add,map_smul,map_smul]
      simp only [he] at heq
      rw [hleft,hright] at heq
      change coordinates (Eguide (q k s)) = _
      rwa [hy] at heq
  obtain ⟨τ,hτ,hτε,gap,hgap⟩ := hGaps
  refine ⟨τ,hτ,hτε,gap,hgap,?_⟩
  let C : Set ↥F := (⋃ k : Fin (D.m+2), range (D.piece k τ)) ∪
    (⋃ k : Fin (D.m+1), range (gap k))
  let E : ↥F → Plane := fun y => Eguide y.val
  have hCS : ∀ y ∈ C, y.val ∈ Eguide.source := by
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨k,hk⟩ := mem_iUnion.mp hy
      exact D.piece_in_guide τ hτ hτε k hk
    · obtain ⟨k,s,rfl⟩ := mem_iUnion.mp hy
      exact (hgap k).2.2 s |>.1
  have hpieces (k : Fin (D.m+2)) : range (D.piece k τ) ⊆ C :=
    fun y hy => Or.inl (mem_iUnion.mpr ⟨k,hy⟩)
  have hgaps (k : Fin (D.m+1)) : range (gap k) ⊆ C :=
    fun y hy => Or.inr (mem_iUnion.mpr ⟨k,hy⟩)
  have hpS (k : Fin (D.m+2)) (s : Interval) : (D.piece k τ s).val ∈ Eguide.source :=
    hCS _ (hpieces k ⟨s,rfl⟩)
  have hpArc (k : Fin (D.m+2)) :
      IsArcBetween (E '' range (D.piece k τ)) (E (D.L k τ)) (E (D.R k τ)) := by
    let p : C(Interval,S) := ⟨fun t => (D.piece k τ t).val,
      continuous_subtype_val.comp (D.piece k τ).continuous⟩
    have hp := actual_chart_continuous_arc Eguide p
      (IsEmbedding.subtypeVal.comp (D.piece_embedded τ hτ hτε k)) (hpS k)
    simpa [p, ← range_comp, Function.comp_def,
      (D.piece_endpoints τ hτ hτε k).1,(D.piece_endpoints τ hτ hτε k).2,E] using hp
  have hgArc (k : Fin (D.m+1)) :
      IsArcBetween (E '' range (gap k))
        (E (D.R ⟨k.val,by omega⟩ τ)) (E (D.L ⟨k.val+1,by omega⟩ τ)) := by
    let p : C(Interval,S) := ⟨fun t => (gap k t).val,
      continuous_subtype_val.comp (gap k).continuous⟩
    have hp := actual_chart_continuous_arc Eguide p
      (IsEmbedding.subtypeVal.comp (hgap k).1) (fun s => ((hgap k).2.2 s).1)
    simpa [p, ← range_comp, Function.comp_def, (gap k).source,(gap k).target,E] using hp
  have hL0 : D.L ⟨0,by omega⟩ τ = D.xL := (D.attachments τ hτ hτε).1
  have hRlast : D.R ⟨D.m+1,by omega⟩ τ = D.xR := (D.attachments τ hτ hτε).2
  have hxLS : D.xL.val ∈ Eguide.source := by
    rw [← hL0, ← (D.piece_endpoints τ hτ hτε ⟨0,by omega⟩).1]
    exact hpS _ 0
  have hxRS : D.xR.val ∈ Eguide.source := by
    rw [← hRlast, ← (D.piece_endpoints τ hτ hτε ⟨D.m+1,by omega⟩).2]
    exact hpS _ 1
  have hxLold : D.xL ∈ range (f (some v)) := by
    rcases D.orientation with ⟨hL,hR⟩ | ⟨hL,hR⟩ <;> rw [hL] <;> exact mem_range_self _
  have hxRold : D.xR ∈ range (f (some v)) := by
    rcases D.orientation with ⟨hL,hR⟩ | ⟨hL,hR⟩ <;> rw [hR] <;> exact mem_range_self _
  have hlr : D.l < D.r :=
    D.cuts.2.1.trans (D.cuts.2.2.1.trans D.cuts.2.2.2.1)
  have hne : D.xL ≠ D.xR := by
    rcases D.orientation with ⟨hL,hR⟩ | ⟨hL,hR⟩
    · rw [hL,hR]
      exact fun h => (ne_of_lt hlr) (ha.injective h)
    · rw [hL,hR]
      exact fun h => (ne_of_lt hlr) (ha.injective h).symm
  have hEne : E D.xL ≠ E D.xR := by
    intro h
    exact hne (Subtype.ext (Eguide.injOn hxLS hxRS h))
  have hEclear (y : ↥F) (hyS : y.val ∈ Eguide.source)
      (hy : y ∉ range (f (some v))) : E D.xL ≠ E y := by
    intro h
    exact hy ((Subtype.ext (Eguide.injOn hxLS hyS h)) ▸ hxLold)
  have hRne (k : Fin (D.m+2)) : E D.xL ≠ E (D.R k τ) := by
    by_cases hk : k.val = D.m+1
    · have he : k = ⟨D.m+1,by omega⟩ := Fin.ext hk
      rw [he,hRlast]
      exact hEne
    · let j : Fin (D.m+1) := ⟨k.val,by omega⟩
      exact hEclear _ (D.internal_source j τ).1
        ((D.internal_clear τ hτ hτε j (some v)).1)
  have hLne (k : Fin (D.m+1)) : E D.xL ≠ E (D.L ⟨k.val+1,Nat.succ_lt_succ k.isLt⟩ τ) :=
    by
      apply hEclear
      · exact (D.internal_source k τ).2
      · exact (D.internal_clear τ hτ hτε k (some v)).2
  have hjoin {P Q : Set Plane} {b c : Plane}
      (hP : IsArcBetween P (E D.xL) b) (hQ : IsArcBetween Q b c)
      (hPC : P ⊆ E '' C) (hQC : Q ⊆ E '' C) (hne : E D.xL ≠ c) :
      ∃ T ⊆ E '' C, IsArcBetween T (E D.xL) c := by
    obtain ⟨T,hT,hArc⟩ := exists_arc_in_union_of_arcs hP hQ hne
    exact ⟨T,hT.trans (union_subset hPC hQC),hArc⟩
  have hprefix (k : Fin (D.m+2)) : ∃ P ⊆ E '' C,
      IsArcBetween P (E D.xL) (E (D.R k τ)) := by
    induction k using Fin.strong_induction_on with
    | h k ih =>
      by_cases hk : k.val = 0
      · have he : k = ⟨0,by omega⟩ := Fin.ext hk
        rw [he]
        exact ⟨_,image_mono (hpieces _),hL0 ▸ hpArc _⟩
      · let j : Fin (D.m+2) := ⟨k.val-1,by omega⟩
        let z : Fin (D.m+1) := ⟨k.val-1,by have := k.isLt; omega⟩
        have hjk : j < k := by change k.val-1 < k.val; omega
        obtain ⟨P,hPC,hP⟩ := ih j hjk
        have hsucc : (⟨z.val+1,by omega⟩ : Fin (D.m+2)) = k := by
          apply Fin.ext
          dsimp [z]
          omega
        obtain ⟨Q,hQC,hQ⟩ := hjoin hP (hgArc z) hPC
          (image_mono (hgaps z)) (hLne z)
        rw [hsucc] at hQ
        exact hjoin hQ (hpArc k) hQC (image_mono (hpieces k)) (hRne k)
  obtain ⟨P,hPC,hP⟩ := hprefix ⟨D.m+1,by omega⟩
  rw [hRlast] at hP
  have hPS : P ⊆ Eguide.target := by
    rintro z hz
    obtain ⟨y,hy,rfl⟩ := hPC hz
    exact Eguide.map_source (hCS y hy)
  obtain ⟨p,hp,hpr,hp0,hp1⟩ := actual_pullback_chart_arc Eguide D.xL.val D.xR.val hxLS hxRS P hP hPS
  have hprC : ∀ t : Interval, ∃ y ∈ C, y.val = p t := by
    intro t
    have ht : p t ∈ Eguide.symm '' P := hpr ▸ mem_range_self t
    obtain ⟨z,hz,hzpt⟩ := ht
    obtain ⟨y,hy,hyz⟩ := hPC hz
    refine ⟨y,hy,?_⟩
    rw [← hzpt, ← hyz]
    exact (Eguide.left_inv (hCS y hy)).symm
  have hpF (t : Interval) : p t ∈ F := by
    obtain ⟨y,hy,he⟩ := hprC t
    exact he ▸ y.property
  let q : C(Interval,↥F) := ⟨fun t => ⟨p t,hpF t⟩,p.continuous.subtype_mk _⟩
  have hq : IsEmbedding q :=
    (q.continuous.isClosedEmbedding (fun x y h => hp.injective (congrArg Subtype.val h))).isEmbedding
  have hq0 : q 0 = D.xL := Subtype.ext hp0
  have hq1 : q 1 = D.xR := Subtype.ext hp1
  let z : Path D.xL D.xR := ⟨q,hq0,hq1⟩
  have hzC : range z ⊆ C := by
    rintro y ⟨t,rfl⟩
    obtain ⟨u,hu,he⟩ := hprC t
    exact (Subtype.ext he : u = z t) ▸ hu
  have hends : {D.xL,D.xR} = ({f (some v) D.l,f (some v) D.r} : Set ↥F) := by
    rcases D.orientation with ⟨hL,hR⟩ | ⟨hL,hR⟩
    · rw [hL,hR]
    · rw [hL,hR,pair_comm]
  have hn : ∃ n : Path (f (some v) D.l) (f (some v) D.r),
      IsEmbedding n ∧ range n ⊆ C := by
    rcases D.orientation with ⟨hL,hR⟩ | ⟨hL,hR⟩
    · exact ⟨z.cast hL.symm hR.symm,hq,hzC⟩
    · exact ⟨z.symm.cast hR.symm hL.symm,hq.comp unitInterval.symmHomeomorph.isEmbedding,by
        change range (z ∘ unitInterval.symmHomeomorph) ⊆ C
        rw [unitInterval.symmHomeomorph.surjective.range_comp]
        exact hzC⟩
  obtain ⟨n,hn,hnC⟩ := hn
  have hCmeet : C ∩ range (f (some v)) ⊆ {D.xL,D.xR} := by
    intro y hy
    rcases hy.1 with hyP | hyG
    · obtain ⟨k,hk⟩ := mem_iUnion.mp hyP
      by_cases hk0 : k.val = 0
      · have he : k = ⟨0,by omega⟩ := Fin.ext hk0
        rw [he] at hk
        exact Or.inl (mem_singleton_iff.mp ((D.selected_meet τ hτ hτε).1 ▸ ⟨hk,hy.2⟩))
      · by_cases hkLast : k.val = D.m+1
        · have he : k = ⟨D.m+1,by omega⟩ := Fin.ext hkLast
          rw [he] at hk
          exact Or.inr (mem_singleton_iff.mp ((D.selected_meet τ hτ hτε).2.1 ▸ ⟨hk,hy.2⟩))
        · let j : Fin D.m := ⟨k.val-1,by omega⟩
          have he : (⟨j.val+1,by omega⟩ : Fin (D.m+2)) = k := by
            apply Fin.ext
            dsimp [j]
            omega
          exact False.elim (disjoint_left.mp ((D.selected_meet τ hτ hτε).2.2 j)
            (by rwa [he]) hy.2)
    · obtain ⟨k,hk⟩ := mem_iUnion.mp hyG
      exact False.elim (disjoint_left.mp ((hgap k).2.1 (some v)) hk hy.2)
  have hCguide : Disjoint C (range (f (some w))) := by
    apply disjoint_left.mpr
    intro y hy hyw
    rcases hy with hyP | hyG
    · obtain ⟨k,hk⟩ := mem_iUnion.mp hyP
      exact disjoint_left.mp (D.guide_clear τ hτ hτε k) hk hyw
    · obtain ⟨k,hk⟩ := mem_iUnion.mp hyG
      exact disjoint_left.mp ((hgap k).2.1 (some w)) hk hyw
  have hCcontacts (i : Option ι) : C ∩ range (f i) =
      ⋃ k : Fin (D.m+2), range (D.piece k τ) ∩ range (f i) := by
    ext y
    constructor
    · intro hy
      rcases hy.1 with hyP | hyG
      · obtain ⟨k,hk⟩ := mem_iUnion.mp hyP
        exact mem_iUnion.mpr ⟨k,hk,hy.2⟩
      · obtain ⟨k,hk⟩ := mem_iUnion.mp hyG
        exact False.elim (disjoint_left.mp ((hgap k).2.1 i) hk hy.2)
    · intro hy
      obtain ⟨k,hk,hyi⟩ := mem_iUnion.mp hy
      exact ⟨hpieces k hk,hyi⟩
  have hCF (i : Option ι) (hi : i ≠ some v) : (C ∩ range (f i)).Finite := by
    rw [hCcontacts]
    exact finite_iUnion (fun k => D.piece_contacts_finite τ hτ hτε k i hi)
  refine ⟨n,hn,(fun y hy => hGuideSource (hCS y (hnC hy))),?_,
    hCguide.mono_left hnC,hnC,?_,?_⟩
  · apply Subset.antisymm
    · exact (inter_subset_inter_left _ hnC).trans (hCmeet.trans (le_of_eq hends))
    · rintro y (rfl | rfl)
      · exact ⟨⟨0,n.source⟩,mem_range_self _⟩
      · exact ⟨⟨1,n.target⟩,mem_range_self _⟩
  · intro i hi
    exact (hCF i hi).subset (inter_subset_inter_left _ hnC)
  · intro i hi hiw
    have hbound : (C ∩ range (f i)).ncard ≤ ∑ k : Fin (D.m+2),
        if D.site k ∈ range (f i) then 1 else 0 := by
      rw [hCcontacts]
      exact (actual_finite_union_card_bound _
        (fun k => D.piece_contacts_finite τ hτ hτε k i hi)).2.trans
        (Finset.sum_le_sum (fun k _ => D.piece_contacts_bound τ hτ hτε k i hi hiw))
    apply (ncard_le_ncard (inter_subset_inter_left _ hnC) (hCF i hi)).trans
    apply hbound.trans
    have hEvents : (∑ k : Fin D.m,
        if (D.label k).val ∈ range (f i) then 1 else 0) =
        ((range d.second \ ({d.first 0,d.first 1} : Set ↥F)) ∩ range (f i)).ncard := by
      let J := {k : Fin D.m // (D.label k).val ∈ range (f i)}
      let P := (range d.second \ ({d.first 0,d.first 1} : Set ↥F)) ∩ range (f i)
      let toPoint : J → P := fun k => ⟨(D.label k.val).val,(D.label k.val).property.1,k.property⟩
      have hInj : Function.Injective toPoint := by
        intro j k he
        have hv : (D.label j.val).val = (D.label k.val).val :=
          congrArg (fun q : P => q.val) he
        exact Subtype.ext (D.label.injective (Subtype.ext hv))
      have hSurj : Function.Surjective toPoint := by
        intro y
        let z : ↥((range d.second \ ({d.first 0,d.first 1} : Set ↥F)) ∩
            {p | ∃ j : Option ι, j ≠ some w ∧ p ∈ range (f j)}) :=
          ⟨y.val,y.property.1,⟨i,hiw,y.property.2⟩⟩
        obtain ⟨k,hk⟩ := D.label.surjective z
        refine ⟨⟨k,?_⟩,?_⟩
        · rw [hk]
          exact y.property.2
        · apply Subtype.ext
          change (D.label k).val = y.val
          rw [hk]
      exact (actual_filter_indicator_card _).trans
        (Nat.card_congr (Equiv.ofBijective toPoint ⟨hInj,hSurj⟩))
    have hCornerNe : f (some w) (min d.bStart d.bFinish) ≠
        f (some w) (max d.bStart d.bFinish) := by
      have hc := congrArg Set.ncard D.corners
      rw [ncard_pair d.corners_distinct] at hc
      intro he
      have hs : ({f (some w) (min d.bStart d.bFinish),
          f (some w) (max d.bStart d.bFinish)} : Set ↥F) =
          {f (some w) (min d.bStart d.bFinish)} := by rw [he]; simp
      rw [hs] at hc
      simp at hc
    have hpair (a b : ↥F) (hab : a ≠ b) :
        (if a ∈ range (f i) then 1 else 0) + (if b ∈ range (f i) then 1 else 0) =
          (({a,b} : Set ↥F) ∩ range (f i)).ncard := by
      by_cases hA : a ∈ range (f i) <;> by_cases hB : b ∈ range (f i)
      · have hSet : ({a,b} : Set ↥F) ∩ range (f i) = {a,b} := by
          ext y
          simp only [mem_inter_iff,mem_insert_iff,mem_singleton_iff]
          constructor
          · intro hy; exact hy.1
          · intro hy; exact ⟨hy, by rcases hy with rfl | rfl <;> assumption⟩
        rw [hSet,ncard_pair hab]
        simp [hA,hB]
      · have hSet : ({a,b} : Set ↥F) ∩ range (f i) = {a} := by
          ext y
          simp only [mem_inter_iff,mem_insert_iff,mem_singleton_iff]
          constructor
          · rintro ⟨hy,hyi⟩
            rcases hy with rfl | rfl
            · rfl
            · exact False.elim (hB hyi)
          · rintro rfl; exact ⟨Or.inl rfl,hA⟩
        rw [hSet,ncard_singleton]
        simp [hA,hB]
      · have hSet : ({a,b} : Set ↥F) ∩ range (f i) = {b} := by
          ext y
          simp only [mem_inter_iff,mem_insert_iff,mem_singleton_iff]
          constructor
          · rintro ⟨hy,hyi⟩
            rcases hy with rfl | rfl
            · exact False.elim (hA hyi)
            · rfl
          · rintro rfl; exact ⟨Or.inr rfl,hB⟩
        rw [hSet,ncard_singleton]
        simp [hA,hB]
      · have hSet : ({a,b} : Set ↥F) ∩ range (f i) = ∅ := by
          ext y
          simp only [mem_inter_iff,mem_insert_iff,mem_singleton_iff,mem_empty_iff_false]
          simp only [iff_false]
          rintro ⟨hy,hyi⟩
          rcases hy with rfl | rfl <;> contradiction
        rw [hSet,ncard_empty]
        simp [hA,hB]
    have hCorners : (if f (some w) (min d.bStart d.bFinish) ∈ range (f i) then 1 else 0) +
        (if f (some w) (max d.bStart d.bFinish) ∈ range (f i) then 1 else 0) =
          (({d.first 0,d.first 1} : Set ↥F) ∩ range (f i)).ncard := by
      rw [← D.corners]
      exact hpair _ _ hCornerNe
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_succ]
    change ((if D.site ⟨0,by omega⟩ ∈ range (f i) then 1 else 0) +
      ∑ k : Fin D.m, if D.site ⟨k.val+1,by omega⟩ ∈ range (f i) then 1 else 0) +
      (if D.site ⟨D.m+1,by omega⟩ ∈ range (f i) then 1 else 0) ≤ _
    simp only [D.site_left,D.site_right,D.site_event]
    rw [hEvents]
    omega
