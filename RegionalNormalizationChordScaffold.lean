import RegionalChordDefinitions
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.Analysis.Convex.StrictConvexSpace
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import CurveComplexGenusTwo.Topology.ActualFreeBoundarySupportedContactDrop.RegionalSupportedRestriction
import Mathlib.Analysis.Convex.GaugeRescale

open CurveComplex Set Topology Schoenflies RegionalChordNormalization
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem regional_finite_incident_whole_trace_disk
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
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
    ∀ (κ : Type) [Fintype κ] (a : κ → C(Interval,↥F)),
      (∀ i, IsEmbedding (a i)) →
      (∀ i j, i ≠ j → (range (a i) ∩ range (a j)).Finite) →
      ∀ p : ↥F,
      (∃ i j, i ≠ j ∧ p ∈ range (a i) ∩ range (a j)) →
      (∀ i, p ∈ range (a i) → ∃ τ ∈ Ioo (0 : Interval) 1, a i τ = p) →
      ∀ N : Set S, IsOpen N → p.val ∈ N → N ⊆ interior F →
      (∀ i j, i ≠ j → ∀ y ∈ range (a i) ∩ range (a j), y.val ∈ N → y = p) →
      let Inc := {i : κ // p ∈ range (a i)}
      ∃ (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
        (l r τ : Inc → Interval),
        let D := chartPull F e (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
        let U := chartPull F e (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
        let port : Inc × Bool → EuclideanSpace ℝ (Fin 2) := fun z =>
          e ((a z.1.val) (if z.2 then r z.1 else l z.1)).val
        e.source ⊆ N ∧ (p.val ∈ e.source ∧ e p.val = 0) ∧
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ e.target ∧
        (∀ i, 0 < l i ∧ l i < τ i ∧ τ i < r i ∧ r i < 1) ∧
        (∀ i, a i.val (τ i) = p) ∧
        (∀ i, D ∩ range (a i.val) = a i.val '' Icc (l i) (r i)) ∧
        (∀ i, U ∩ range (a i.val) = a i.val '' Ioo (l i) (r i)) ∧
        (∀ i, (fun t => e ((a i.val) t).val) '' Icc (l i) (r i) =
          segment ℝ (port (i,false)) 0 ∪ segment ℝ 0 (port (i,true))) ∧
        (∀ j, p ∉ range (a j) → Disjoint D (range (a j))) ∧
        (∀ z, port z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
        Function.Injective port := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  dsimp only
  intro κ _ a hEmb hFin p hInc hParam N hN hpN hNF hOnly
  let Inc := {i : κ // p ∈ range (a i)}
  letI : Fintype Inc := Fintype.ofFinite Inc
  let Away := {i : κ // p ∉ range (a i)}
  letI : Fintype Away := Fintype.ofFinite Away
  let f : Inc → C(Interval,S) := fun j =>
    ⟨fun t => (a j.val t).val, continuous_subtype_val.comp (a j.val).continuous⟩
  have hf (j : Inc) : IsEmbedding (f j) :=
    IsEmbedding.subtypeVal.comp (hEmb j.val)
  choose center hci hcenter using (fun j : Inc => hParam j.val j.property)
  have hfc (j : Inc) : f j (center j) = p.val := congrArg Subtype.val (hcenter j)
  let e₀ := chartAt Plane p.val
  let Q := (e₀.restr N).trans (Homeomorph.subRight (e₀ p.val)).toOpenPartialHomeomorph
  have hQs : Q.source = e₀.source ∩ N := by
    simp [Q,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.restr_source,hN.interior_eq]
  have hpQ : p.val ∈ Q.source := by rw [hQs];exact ⟨mem_chart_source _ _,hpN⟩
  have hQp : Q p.val = 0 := by change e₀ p.val - e₀ p.val = 0;exact sub_self _
  let U := Q.source
  have hU : IsOpen U := Q.open_source
  have hpU : p.val ∈ U := hpQ
  have hwindow (j : Inc) : ∃ l d : Interval,
      0 < l ∧ l < center j ∧ center j < d ∧ d < 1 ∧
      ∀ t ∈ Set.Icc l d, f j t ∈ U := by
    have hn : (f j) ⁻¹' U ∈ nhds (center j) :=
      (hU.preimage (f j).continuous).mem_nhds (by change f j (center j) ∈ U; rw [hfc];exact hpU)
    obtain ⟨l₀,d₀,hl,hd⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨0,(hci j).1⟩ ⟨1,(hci j).2⟩).mp hn
    obtain ⟨l,hll,hls⟩ := exists_between hl.1
    obtain ⟨d,hsd,hdd⟩ := exists_between hl.2
    refine ⟨l,d,(show (0:Interval) ≤ l₀ from bot_le).trans_lt hll,hls,hsd,
      hdd.trans_le (show d₀ ≤ (1:Interval) from le_top),?_⟩
    intro t ht
    exact hd ⟨hll.trans_le ht.1,ht.2.trans_lt hdd⟩
  choose left right hleft0 hleft hright hright1 hwindow using hwindow
  let tip : Inc × Bool → Interval := fun j => if j.2 then right j.1 else left j.1
  let param : Inc × Bool → C(Interval,Interval) := fun j => {
    toFun := fun t => ⟨(center j.1).val + ((tip j).val - (center j.1).val) * t.val,by
      have hc := (center j.1).property
      have ht := (tip j).property
      have h := t.property
      constructor
      · have ha : 0 ≤ (1-t.val)*(center j.1).val := mul_nonneg (by linarith [h.2]) hc.1
        have hb : 0 ≤ t.val*(tip j).val := mul_nonneg h.1 ht.1
        nlinarith
      · have ha : 0 ≤ (1-t.val)*(1-(center j.1).val) := mul_nonneg (by linarith [h.2]) (by linarith [hc.2])
        have hb : 0 ≤ t.val*(1-(tip j).val) := mul_nonneg h.1 (by linarith [ht.2])
        nlinarith⟩
    continuous_toFun := by fun_prop }
  have hparam0 (j : Inc × Bool) : param j 0 = center j.1 := Subtype.ext (by
    change (center j.1).val + ((tip j).val - (center j.1).val)*0 = (center j.1).val
    ring)
  have hparam1 (j : Inc × Bool) : param j 1 = tip j := Subtype.ext (by
    change (center j.1).val + ((tip j).val - (center j.1).val)*1 = (tip j).val
    ring)
  have htipne (j : Inc × Bool) : tip j ≠ center j.1 := by
    rcases j with ⟨j,k⟩
    cases k
    · exact (hleft j).ne
    · exact (hright j).ne.symm
  have hparami (j : Inc × Bool) : Function.Injective (param j) := by
    intro t u he
    apply Subtype.ext
    have heq := congrArg Subtype.val he
    change (center j.1).val + ((tip j).val - (center j.1).val)*t.val =
      (center j.1).val + ((tip j).val - (center j.1).val)*u.val at heq
    have hne : (tip j).val - (center j.1).val ≠ 0 := sub_ne_zero.mpr (fun hh =>
      htipne j (Subtype.ext hh))
    exact mul_left_cancel₀ hne (add_left_cancel heq)
  have hparamK (j : Inc × Bool) (t : Interval) :
      param j t ∈ Set.Icc (left j.1) (right j.1) := by
    rcases j with ⟨j,k⟩
    cases k
    · change (left j).val ≤ (center j).val + ((left j).val - (center j).val)*t.val ∧
        (center j).val + ((left j).val - (center j).val)*t.val ≤ (right j).val
      have hl : (left j).val < (center j).val := hleft j
      have hr : (center j).val < (right j).val := hright j
      constructor <;> nlinarith [t.property.1,t.property.2]
    · change (left j).val ≤ (center j).val + ((right j).val - (center j).val)*t.val ∧
        (center j).val + ((right j).val - (center j).val)*t.val ≤ (right j).val
      have hl : (left j).val < (center j).val := hleft j
      have hr : (center j).val < (right j).val := hright j
      constructor <;> nlinarith [t.property.1,t.property.2]
  let β : Inc × Bool → C(Interval,S) := fun j => (f j.1).comp (param j)
  have hβ (j : Inc × Bool) : IsEmbedding (β j) :=
    (hf j.1).comp (((param j).continuous.isClosedEmbedding (hparami j)).isEmbedding)
  have hβ0 (j : Inc × Bool) : β j 0 = p.val := by
    change f j.1 (param j 0) = p
    rw [hparam0,hfc]
  have hβU (j : Inc × Bool) (t : Interval) : β j t ∈ U :=
    hwindow j.1 _ (hparamK j t)
  have hβmeet (i j : Inc × Bool) (hij : i ≠ j) :
      Set.range (β i) ∩ Set.range (β j) = {p.val} := by
    apply Set.Subset.antisymm
    · rintro y ⟨⟨t,rfl⟩,⟨u,heu⟩⟩
      have he : f j.1 (param j u) = f i.1 (param i t) := heu
      have hpval : β i t = p.val := by
        by_cases hj : j.1 = i.1
        · have hpar : param j u = param i t := (hf i.1).injective (hj ▸ he)
          have hk : j.2 ≠ i.2 := fun hh => hij (Prod.ext hj hh).symm
          have hpt : param i t = center i.1 := by
            apply Subtype.ext
            rcases i with ⟨i,k⟩
            rcases j with ⟨j,l⟩
            dsimp only at hj hk
            subst j
            cases k <;> cases l
            · exact (hk rfl).elim
            · have ht : (param (i,false) t).val ≤ (center i).val := by
                change (center i).val + ((left i).val - (center i).val)*t.val ≤ (center i).val
                have hl : (left i).val < (center i).val := hleft i
                nlinarith [t.property.1]
              have hu : (center i).val ≤ (param (i,true) u).val := by
                change (center i).val ≤ (center i).val + ((right i).val - (center i).val)*u.val
                have hr : (center i).val < (right i).val := hright i
                nlinarith [u.property.1]
              exact le_antisymm ht ((congrArg Subtype.val hpar) ▸ hu)
            · have ht : (center i).val ≤ (param (i,true) t).val := by
                change (center i).val ≤ (center i).val + ((right i).val - (center i).val)*t.val
                have hr : (center i).val < (right i).val := hright i
                nlinarith [t.property.1]
              have hu : (param (i,false) u).val ≤ (center i).val := by
                change (center i).val + ((left i).val - (center i).val)*u.val ≤ (center i).val
                have hl : (left i).val < (center i).val := hleft i
                nlinarith [u.property.1]
              exact le_antisymm ((congrArg Subtype.val hpar) ▸ hu) ht
            · exact (hk rfl).elim
          change f i.1 (param i t) = p.val
          rw [hpt,hfc]
        · have haeq : a j.1.val (param j u) = a i.1.val (param i t) := Subtype.ext he
          have hyQ : β i t ∈ Q.source := hβU i t
          have hyN : (a i.1.val (param i t)).val ∈ N := (hQs ▸ hyQ).2
          have hy : a i.1.val (param i t) = p :=
            hOnly i.1.val j.1.val (fun hij => hj (Subtype.ext hij.symm))
              (a i.1.val (param i t)) ⟨mem_range_self _,⟨param j u,haeq⟩⟩ hyN
          exact congrArg Subtype.val hy
      exact Set.mem_singleton_iff.mpr hpval
    · rintro y rfl
      exact ⟨⟨0,hβ0 i⟩,⟨0,hβ0 j⟩⟩
  let Far₀ : Set S := ⋃ j : Inc, f j '' (Set.Ioo (left j) (right j))ᶜ
  let Far₁ : Set S := ⋃ j : Away, range (fun t : Interval => (a j.val t).val)
  let Far : Set S := Far₀ ∪ Far₁
  have hFar : IsClosed Far := by
    apply IsClosed.union
    · exact isClosed_iUnion_of_finite (fun j =>
        ((isCompact_univ.of_isClosed_subset isOpen_Ioo.isClosed_compl (Set.subset_univ _)).image
          (f j).continuous).isClosed)
    · exact isClosed_iUnion_of_finite (fun j =>
        (isCompact_range (continuous_subtype_val.comp (a j.val).continuous)).isClosed)
  have hpFar : p.val ∉ Far := by
    rintro (hh | hh)
    · obtain ⟨j,t,ht,he⟩ := Set.mem_iUnion.mp hh
      have heq : t = center j := (hf j).injective (he.trans (hfc j).symm)
      exact ht (heq.symm ▸ ⟨hleft j,hright j⟩)
    · obtain ⟨j,t,he⟩ := Set.mem_iUnion.mp hh
      exact j.property ⟨t,Subtype.ext he⟩
  let V := Q '' (Q.source \ Far)
  have hV : IsOpen V := Q.isOpen_image_of_subset_source
    (Q.open_source.sdiff hFar) Set.diff_subset
  have hzeroV : (0:Plane) ∈ V := ⟨p.val,⟨hpQ,hpFar⟩,hQp⟩
  let γ : Inc × Bool → Interval → Plane := fun j => Q ∘ β j
  have hγ (j : Inc × Bool) : IsClosedEmbedding (γ j) := by
    apply (Q.continuousOn.comp_continuous (β j).continuous
      (fun t => (hβU j t))).isClosedEmbedding
    intro t u he
    exact (hβ j).injective (Q.injOn (hβU j t) (hβU j u) he)
  have hγ0 (j : Inc × Bool) : γ j 0 = 0 := by
    change Q (β j 0) = 0
    rw [hβ0,hQp]
  have hγmeet (i j : Inc × Bool) (hij : i ≠ j) :
      Set.range (γ i) ∩ Set.range (γ j) = {0} := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨t,rfl⟩,⟨u,he⟩⟩
      have hβeq : β j u = β i t := Q.injOn (hβU j u) (hβU i t) he
      have hp : β i t = p.val := Set.mem_singleton_iff.mp
        (hβmeet i j hij ▸ (show β i t ∈ Set.range (β i) ∩ Set.range (β j) from
          ⟨Set.mem_range_self _,⟨u,hβeq⟩⟩))
      change Q (β i t) = 0
      rw [hp,hQp]
    · rintro z rfl
      exact ⟨⟨0,hγ0 i⟩,⟨0,hγ0 j⟩⟩
  obtain ⟨i₀,j₀,hij,hpi,hpj⟩ := hInc
  let seed : Inc := ⟨i₀,hpi⟩
  obtain ⟨R,hop⟩ := prescribed_pair_finite_actual_star_radialization_zero
    γ hγ hγ0 hγmeet (seed,false) (seed,true)
    (fun he => Bool.false_ne_true (congrArg Prod.snd he)) V hV hzeroV
  have hparamRange (j : Inc × Bool) : Set.range (param j) =
      Set.uIcc (center j.1) (tip j) := by
    rw [← Set.image_univ, unitInterval.univ_eq_Icc]
    rcases j with ⟨j,k⟩
    cases k
    · have hant : AntitoneOn (param (j,false)) (Set.Icc (0:Interval) 1) := by
        intro t ht u hu htu
        change (center j).val + ((left j).val - (center j).val)*u.val ≤
          (center j).val + ((left j).val - (center j).val)*t.val
        have hh : (left j).val < (center j).val := hleft j
        have htu : t.val ≤ u.val := htu
        nlinarith
      rw [ContinuousOn.image_Icc_of_antitoneOn (show (0:Interval) ≤ 1 by norm_num)
        (param (j,false)).continuous.continuousOn hant,hparam0,hparam1]
      exact (Set.uIcc_of_ge (hleft j).le).symm
    · have hmono : MonotoneOn (param (j,true)) (Set.Icc (0:Interval) 1) := by
        intro t ht u hu htu
        change (center j).val + ((right j).val - (center j).val)*t.val ≤
          (center j).val + ((right j).val - (center j).val)*u.val
        have hh : (center j).val < (right j).val := hright j
        have htu : t.val ≤ u.val := htu
        nlinarith
      rw [ContinuousOn.image_Icc_of_monotoneOn (show (0:Interval) ≤ 1 by norm_num)
        (param (j,true)).continuous.continuousOn hmono,hparam0,hparam1]
      exact (Set.uIcc_of_le (hright j).le).symm
  have hwholeCover (j : Inc) : Set.range (f j) ⊆
      Far ∪ (Set.range (β (j,false)) ∪ Set.range (β (j,true))) := by
    rintro y ⟨t,rfl⟩
    by_cases ht : t ∈ Set.Ioo (left j) (right j)
    · right
      by_cases htc : t ≤ center j
      · left
        have hh : t ∈ Set.range (param (j,false)) := by
          rw [hparamRange]
          change t ∈ Set.uIcc (center j) (left j)
          rw [Set.uIcc_of_ge (hleft j).le]
          exact ⟨ht.1.le,htc⟩
        obtain ⟨u,rfl⟩ := hh
        exact ⟨u,rfl⟩
      · right
        have hh : t ∈ Set.range (param (j,true)) := by
          rw [hparamRange]
          change t ∈ Set.uIcc (center j) (right j)
          rw [Set.uIcc_of_le (hright j).le]
          exact ⟨(lt_of_not_ge htc).le,ht.2.le⟩
        obtain ⟨u,rfl⟩ := hh
        exact ⟨u,rfl⟩
    · left
      exact Or.inl (Set.mem_iUnion.mpr ⟨j,t,ht,rfl⟩)
  let Q₀ := Q.transHomeomorph R.H
  have hQ₀s : Q₀.source = Q.source := rfl
  have hQ₀val (x : S) : Q₀ x = R.H (Q x) := rfl
  have hQ₀p : Q₀ p.val = 0 := by rw [hQ₀val,hQp,R.fixes_center]
  have hscale : ∃ σ : ℝ, ∃ E : OpenPartialHomeomorph S Plane,
      0 < σ ∧ E.source = Q₀.source ∧ E p.val = 0 ∧
      Metric.closedBall (0:Plane) 1 ⊆ E.target ∧
      (∀ x, E x = σ⁻¹ • Q₀ x) ∧
      ∀ x ∈ E.source, E x ∈ Metric.closedBall (0:Plane) 1 →
        ‖Q₀ x‖ < R.coreRadius := by
    have hzTarget : (0:Plane) ∈ Q₀.target := hQ₀p ▸ Q₀.map_source hpQ
    obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp Q₀.open_target 0 hzTarget
    let σ : ℝ := min δ R.coreRadius / 2
    have hσ : 0 < σ := half_pos (lt_min hδ R.core_pos)
    have hσδ : σ < δ := (half_lt_self (lt_min hδ R.core_pos)).trans_le (min_le_left _ _)
    have hσcore : σ < R.coreRadius := (half_lt_self (lt_min hδ R.core_pos)).trans_le (min_le_right _ _)
    let H : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero σ⁻¹ (inv_ne_zero (ne_of_gt hσ))
    let E := Q₀.transHomeomorph H
    have hvalue (x : S) : E x = σ⁻¹ • Q₀ x := rfl
    have hinv (z : Plane) : H.symm z = σ • z := by change (σ⁻¹)⁻¹ • z = σ • z;rw [inv_inv]
    have hsmall (z : Plane) (hz : z ∈ Metric.closedBall (0:Plane) 1) :
        ‖H.symm z‖ ≤ σ := by
      rw [hinv,norm_smul,Real.norm_eq_abs,abs_of_pos hσ]
      have hz' : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
      nlinarith
    refine ⟨σ,E,hσ,rfl,?_,?_,hvalue,?_⟩
    · change H (Q₀ p.val) = 0
      rw [hQ₀p]
      simp [H,Homeomorph.smulOfNeZero]
    · intro z hz
      change H.symm z ∈ Q₀.target
      apply hball
      rw [Metric.mem_ball,dist_zero_right]
      exact (hsmall z hz).trans_lt hσδ
    · intro x hx hz
      have he : H.symm (E x) = Q₀ x := H.symm_apply_apply _
      rw [← he]
      exact (hsmall (E x) hz).trans_lt hσcore
  obtain ⟨σ,E,hσ,hEs,hEp,hEBall,hEval,hEsmall⟩ := hscale
  have hEQ : E.source = Q.source := hEs
  have hCore (x : S) (hx : x ∈ E.source)
      (hxs : E x ∈ Metric.closedBall (0:Plane) 1) :
      R.H (Q x) ∈ Metric.closedBall (0:Plane) R.coreRadius := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (hEsmall x hx hxs).le
  have hFarClear (x : S) (hx : x ∈ E.source)
      (hxs : E x ∈ Metric.closedBall (0:Plane) 1) : x ∉ Far := by
    intro hfar
    have hxQ : x ∈ Q.source := hEQ ▸ hx
    have hxnotV : Q x ∉ V := by
      rintro ⟨y,hy,he⟩
      exact hy.2 ((Q.injOn hy.1 hxQ he).symm ▸ hfar)
    have hxout : Q x ∉ Metric.ball (0:Plane) R.supportRadius := by
      intro hin
      exact hxnotV (R.support_subset (Metric.ball_subset_closedBall hin))
    have hfix := R.fixes_exterior (Q x) hxout
    have hsmall := hCore x hx hxs
    rw [hfix] at hsmall
    exact hxnotV (R.support_subset
      (Metric.closedBall_subset_closedBall R.core_lt_support.le hsmall))
  let M : Inc × Bool → Interval → Plane := fun j t => E (β j t)
  let w : Inc × Bool → Plane := fun j => σ⁻¹ • R.vector j
  have hM (j : Inc × Bool) : Continuous (M j) := E.continuousOn.comp_continuous
    (β j).continuous (fun t => hEQ.symm ▸ (hβU j t))
  have hMi (j : Inc × Bool) : Function.Injective (M j) := by
    intro t u he
    exact (hβ j).injective (E.injOn (hEQ.symm ▸ (hβU j t))
      (hEQ.symm ▸ (hβU j u)) he)
  have hM0 (j : Inc × Bool) : M j 0 = 0 := by change E (β j 0) = 0;rw [hβ0,hEp]
  have hMval (j : Inc × Bool) (t : Interval) : M j t = σ⁻¹ • R.H (γ j t) :=
    hEval _
  have hwne (j : Inc × Bool) : w j ≠ 0 :=
    smul_ne_zero (inv_ne_zero (ne_of_gt hσ)) (R.vector_nonzero j)
  have hRay (j : Inc × Bool) (t : Interval) (ht : t ≤ R.cut j) :
      M j t ∈ segment ℝ (0:Plane) (w j) := by
    have hh : R.H (γ j t) ∈ segment ℝ (0:Plane) (R.vector j) := by
      simpa only [R.prefix_image,zero_add] using
        (show R.H (γ j t) ∈ R.H '' CurveComplex.FiniteStarGeometry.armPrefix γ j (R.cut j) from
          ⟨γ j t,⟨t,ht,rfl⟩,rfl⟩)
    rw [segment_eq_image'] at hh ⊢
    obtain ⟨q,hq,he⟩ := hh
    refine ⟨q,hq,?_⟩
    rw [hMval,← he]
    simp only [sub_zero,smul_zero,zero_add,map_smul]
    dsimp [w]
    rw [smul_smul,smul_smul,mul_comm]
  have hNormPos (j : Inc × Bool) : 0 < ‖w j‖ := norm_pos_iff.mpr (hwne j)
  let z : Inc × Bool → Interval → ℝ := fun j t => norm (M j t)
  have hz (j : Inc × Bool) : Continuous (z j) := continuous_norm.comp (hM j)
  have hzi (j : Inc × Bool) : Set.InjOn (z j) (Set.Icc (0:Interval) (R.cut j)) := by
    intro t ht u hu he
    have htRay := hRay j t ht.2
    have huRay := hRay j u hu.2
    rw [segment_eq_image'] at htRay huRay
    obtain ⟨q,hq,hqt⟩ := htRay
    obtain ⟨d,hd,hdu⟩ := huRay
    simp only [sub_zero,smul_zero,zero_add] at hqt hdu
    have hqd : q = d := by
      change norm (M j t) = norm (M j u) at he
      rw [← hqt,← hdu] at he
      have hsq : norm (q • w j) = q * norm (w j) := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hq.1]
      have hsd : norm (d • w j) = d * norm (w j) := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd.1]
      rw [hsq,hsd] at he
      exact mul_right_cancel₀ (ne_of_gt (hNormPos j)) he
    exact hMi j (hqt.symm.trans ((hqd ▸ hdu)))
  have hz0 (j : Inc × Bool) : z j 0 = 0 := by change norm (M j 0) = 0;rw [hM0];norm_num [norm]
  have hzcut (j : Inc × Bool) : 1 < z j (R.cut j) := by
    by_contra hn
    have hsq : M j (R.cut j) ∈ Metric.closedBall (0:Plane) 1 :=
      by simpa only [Metric.mem_closedBall,dist_zero_right] using (not_lt.mp hn)
    have hh := hCore (β j (R.cut j)) (hEQ.symm ▸ (hβU j _)) hsq
    have ht : R.H (γ j (R.cut j)) ∈ R.H '' CurveComplex.FiniteStarGeometry.tail γ j (R.cut j) :=
      ⟨γ j (R.cut j),⟨R.cut j,(show (R.cut j).val ≤ (R.cut j).val from le_rfl),rfl⟩,rfl⟩
    exact Set.disjoint_left.mp (R.excludes_tails j) ht hh
  have hzmono (j : Inc × Bool) : StrictMonoOn (z j) (Set.Icc (0:Interval) (R.cut j)) :=
    ContinuousOn.strictMonoOn_of_injOn_Icc (show (0:Interval) ≤ R.cut j from bot_le)
      (by rw [hz0];linarith [hzcut j]) (hz j).continuousOn (hzi j)
  have hcutExists (j : Inc × Bool) : ∃ t : Interval,
      0 < t ∧ t < R.cut j ∧ z j t = 1 := by
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc
      (show (0:Interval) ≤ R.cut j from bot_le) (hz j).continuousOn
      (show (1:ℝ) ∈ Set.Icc (z j 0) (z j (R.cut j)) from
        ⟨by rw [hz0];norm_num,(hzcut j).le⟩)
    have ht0 : 0 < t := by
      apply lt_of_le_of_ne ht.1
      intro heq
      rw [← heq,hz0] at he
      norm_num at he
    have htt : t < R.cut j := by
      apply lt_of_le_of_ne ht.2
      intro heq
      rw [heq] at he
      linarith [hzcut j]
    exact ⟨t,ht0,htt,he⟩
  choose cut hcut0 hcutR hcutz using hcutExists
  have hMsquare (j : Inc × Bool) (t : Interval) :
      M j t ∈ Metric.closedBall (0:Plane) 1 ↔ t ≤ cut j := by
    constructor
    · intro hsq
      have htR : t < R.cut j := by
        by_contra hn
        have htail : R.H (γ j t) ∈ R.H '' CurveComplex.FiniteStarGeometry.tail γ j (R.cut j) :=
          ⟨γ j t,⟨t,(show (R.cut j).val ≤ t.val from not_lt.mp hn),rfl⟩,rfl⟩
        exact Set.disjoint_left.mp (R.excludes_tails j) htail
          (hCore _ (hEQ.symm ▸ (hβU j t)) hsq)
      by_contra hn
      have hh := hzmono j ⟨bot_le,(hcutR j).le⟩ ⟨bot_le,htR.le⟩ (not_le.mp hn)
      rw [hcutz] at hh
      exact (not_lt_of_ge (show ‖M j t‖ ≤ 1 by simpa only [Metric.mem_closedBall,dist_zero_right] using hsq)) hh
    · intro ht
      rw [Metric.mem_closedBall,dist_zero_right]
      exact (hzmono j).monotoneOn ⟨bot_le,ht.trans (hcutR j).le⟩
        ⟨bot_le,(hcutR j).le⟩ ht |>.trans_eq (hcutz j)
  have hMopen (j : Inc × Bool) (t : Interval) (ht : t < cut j) :
      M j t ∈ Metric.ball (0:Plane) 1 := by
    rw [Metric.mem_ball,dist_zero_right]
    exact (hzmono j ⟨bot_le,ht.le.trans (hcutR j).le⟩
      ⟨bot_le,(hcutR j).le⟩ ht).trans_eq (hcutz j)
  have hEinterior : {x : S | x ∈ E.source ∧ E x ∈ Metric.closedBall (0:Plane) 1} ⊆ interior F := by
    intro x hx
    exact hNF ((hQs ▸ (hEQ ▸ hx.1)).2)
  have hBranchImage (j : Inc × Bool) : M j '' Set.Icc (0:Interval) (cut j) =
      segment ℝ (0:Plane) (M j (cut j)) := by
    have hformula (t : Interval) (ht : t ≤ cut j) :
        M j t = ((z j t) / norm (w j)) • w j := by
      have hh := hRay j t (ht.trans (hcutR j).le)
      rw [segment_eq_image'] at hh
      obtain ⟨q,hq,he⟩ := hh
      simp only [sub_zero,zero_add] at he
      have hzq : z j t = q * norm (w j) := by
        change norm (M j t) = _
        rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hq.1]
      rw [hzq,mul_div_cancel_right₀ _ (ne_of_gt (hNormPos j))]
      exact he.symm
    have hcutval : M j (cut j) = (norm (w j))⁻¹ • w j := by
      rw [hformula _ le_rfl,hcutz,one_div]
    apply Set.Subset.antisymm
    · rintro q ⟨t,ht,rfl⟩
      rw [segment_eq_image']
      refine ⟨z j t,⟨norm_nonneg _,?_⟩,?_⟩
      · exact (show ‖M j t‖ ≤ 1 by simpa only [Metric.mem_closedBall,dist_zero_right] using ((hMsquare j t).mpr ht.2))
      · simp only [sub_zero,zero_add]
        rw [hcutval,hformula t ht.2,smul_smul,div_eq_mul_inv]
    · intro q hq
      rw [segment_eq_image'] at hq
      obtain ⟨d,hd,he⟩ := hq
      simp only [sub_zero,zero_add] at he
      obtain ⟨t,ht,hzt⟩ := intermediate_value_Icc
        (show (0:Interval) ≤ cut j from bot_le) (hz j).continuousOn
        (show d ∈ Set.Icc (z j 0) (z j (cut j)) by rw [hz0,hcutz];exact hd)
      refine ⟨t,ht,?_⟩
      rw [hformula t ht.2,hzt,← he,hcutval,div_eq_mul_inv]
      exact (smul_smul d (norm (w j))⁻¹ (w j)).symm
  let edge : Inc × Bool → Interval := fun j => param j (cut j)
  have hedge (j : Inc) :
      0 < edge (j,false) ∧ edge (j,false) < center j ∧
      center j < edge (j,true) ∧ edge (j,true) < 1 := by
    have hc0f : 0 < (cut (j,false)).val := hcut0 _
    have hc1f : (cut (j,false)).val < 1 := by
      have hh : (cut (j,false)).val < (R.cut (j,false)).val := hcutR _
      exact hh.trans_le (R.cut _).property.2
    have hc0t : 0 < (cut (j,true)).val := hcut0 _
    have hc1t : (cut (j,true)).val < 1 := by
      have hh : (cut (j,true)).val < (R.cut (j,true)).val := hcutR _
      exact hh.trans_le (R.cut _).property.2
    have hl0 : 0 < (left j).val := hleft0 j
    have hl : (left j).val < (center j).val := hleft j
    have hr : (center j).val < (right j).val := hright j
    have hr1 : (right j).val < 1 := hright1 j
    change 0 < (center j).val + ((left j).val-(center j).val)*(cut (j,false)).val ∧
      (center j).val + ((left j).val-(center j).val)*(cut (j,false)).val < (center j).val ∧
      (center j).val < (center j).val + ((right j).val-(center j).val)*(cut (j,true)).val ∧
      (center j).val + ((right j).val-(center j).val)*(cut (j,true)).val < 1
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  have hparamSub (j : Inc × Bool) : param j '' Set.Icc (0:Interval) (cut j) =
      Set.uIcc (center j.1) (edge j) := by
    rcases j with ⟨j,k⟩
    cases k
    · have hant : AntitoneOn (param (j,false)) (Set.Icc (0:Interval) (cut (j,false))) := by
        intro t ht u hu htu
        change (center j).val + ((left j).val-(center j).val)*u.val ≤
          (center j).val + ((left j).val-(center j).val)*t.val
        have htu : t.val ≤ u.val := htu
        have hl : (left j).val < (center j).val := hleft j
        nlinarith
      rw [ContinuousOn.image_Icc_of_antitoneOn (show (0:Interval) ≤ cut (j,false) from bot_le)
        (param (j,false)).continuous.continuousOn hant,hparam0]
      exact (Set.uIcc_of_ge (hedge j).2.1.le).symm
    · have hmono : MonotoneOn (param (j,true)) (Set.Icc (0:Interval) (cut (j,true))) := by
        intro t ht u hu htu
        change (center j).val + ((right j).val-(center j).val)*t.val ≤
          (center j).val + ((right j).val-(center j).val)*u.val
        have htu : t.val ≤ u.val := htu
        have hr : (center j).val < (right j).val := hright j
        nlinarith
      rw [ContinuousOn.image_Icc_of_monotoneOn (show (0:Interval) ≤ cut (j,true) from bot_le)
        (param (j,true)).continuous.continuousOn hmono,hparam0]
      exact (Set.uIcc_of_le (hedge j).2.2.1.le).symm
  have htrace (j : Inc) : {x : S | x ∈ E.source ∧ E x ∈ Metric.closedBall (0:Plane) 1} ∩
      Set.range (f j) = f j '' Set.Icc (edge (j,false)) (edge (j,true)) := by
    have hsplit : Set.Icc (edge (j,false)) (edge (j,true)) =
        Set.uIcc (center j) (edge (j,false)) ∪ Set.uIcc (center j) (edge (j,true)) := by
      rw [Set.uIcc_of_ge (hedge j).2.1.le,Set.uIcc_of_le (hedge j).2.2.1.le]
      ext t
      simp only [Set.mem_Icc,Set.mem_union]
      constructor
      · intro ht
        rcases le_total t (center j) with hc | hc
        · exact Or.inl ⟨ht.1,hc⟩
        · exact Or.inr ⟨hc,ht.2⟩
      · rintro (ht | ht)
        · exact ⟨ht.1,ht.2.trans (hedge j).2.2.1.le⟩
        · exact ⟨(hedge j).2.1.le.trans ht.1,ht.2⟩
    rw [hsplit,Set.image_union,← hparamSub (j,false),← hparamSub (j,true),
      Set.image_image,Set.image_image]
    change _ = β (j,false) '' Set.Icc (0:Interval) (cut (j,false)) ∪
      β (j,true) '' Set.Icc (0:Interval) (cut (j,true))
    apply Set.Subset.antisymm
    · intro x hx
      have hg := (hwholeCover j hx.2).resolve_left (hFarClear x hx.1.1 hx.1.2)
      rcases hg with ⟨t,rfl⟩ | ⟨t,rfl⟩
      · left;exact ⟨t,⟨bot_le,(hMsquare (j,false) t).mp hx.1.2⟩,rfl⟩
      · right;exact ⟨t,⟨bot_le,(hMsquare (j,true) t).mp hx.1.2⟩,rfl⟩
    · intro x hx
      rcases hx with ⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩
      · exact ⟨⟨hEQ.symm ▸ (hβU (j,false) t),(hMsquare _ _).mpr ht.2⟩,
          ⟨param (j,false) t,rfl⟩⟩
      · exact ⟨⟨hEQ.symm ▸ (hβU (j,true) t),(hMsquare _ _).mpr ht.2⟩,
          ⟨param (j,true) t,rfl⟩⟩
  have htraceImage (j : Inc) : (fun t : Interval => E (f j t)) ''
      Set.Icc (edge (j,false)) (edge (j,true)) =
      segment ℝ (0:Plane) (M (j,false) (cut (j,false))) ∪
      segment ℝ (0:Plane) (M (j,true) (cut (j,true))) := by
    have hh := congrArg (fun X : Set S => E '' X) (htrace j)
    have hsplit : Set.Icc (edge (j,false)) (edge (j,true)) =
        Set.uIcc (center j) (edge (j,false)) ∪ Set.uIcc (center j) (edge (j,true)) := by
      rw [Set.uIcc_of_ge (hedge j).2.1.le,Set.uIcc_of_le (hedge j).2.2.1.le]
      ext t
      simp only [Set.mem_Icc,Set.mem_union]
      constructor
      · intro ht
        rcases le_total t (center j) with hc | hc
        · exact Or.inl ⟨ht.1,hc⟩
        · exact Or.inr ⟨hc,ht.2⟩
      · rintro (ht | ht)
        · exact ⟨ht.1,ht.2.trans (hedge j).2.2.1.le⟩
        · exact ⟨(hedge j).2.1.le.trans ht.1,ht.2⟩
    rw [hsplit,Set.image_union,← hparamSub (j,false),← hparamSub (j,true),
      Set.image_image,Set.image_image]
    change M (j,false) '' Set.Icc (0:Interval) (cut (j,false)) ∪
      M (j,true) '' Set.Icc (0:Interval) (cut (j,true)) = _
    rw [hBranchImage,hBranchImage]
  have hSubtypeTrace (j : Inc) :
      chartPull F E (Metric.closedBall (0:Plane) 1) ∩ range (a j.val) =
      a j.val '' Icc (edge (j,false)) (edge (j,true)) := by
    ext y
    constructor
    · intro hy
      have hval : y.val ∈ {x : S | x ∈ E.source ∧ E x ∈ Metric.closedBall (0:Plane) 1} ∩
          range (f j) := by
        refine ⟨hy.1,?_⟩
        obtain ⟨t,rfl⟩ := hy.2
        exact ⟨t,rfl⟩
      obtain ⟨t,ht,he⟩ := htrace j ▸ hval
      exact ⟨t,ht,Subtype.ext he⟩
    · rintro ⟨t,ht,rfl⟩
      have hh := (htrace j).symm ▸ (show f j t ∈ f j ''
        Icc (edge (j,false)) (edge (j,true)) from ⟨t,ht,rfl⟩)
      exact ⟨hh.1,mem_range_self _⟩
  have hSphere (j : Inc × Bool) : M j (cut j) ∈ Metric.sphere (0:Plane) 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using hcutz j
  have hInside (j : Inc) : ∀ t ∈ Ioo (edge (j,false)) (edge (j,true)),
      E (a j.val t).val ∈ Metric.ball (0:Plane) 1 := by
    intro t ht
    by_cases htc : t ≤ center j
    · have hh : t ∈ param (j,false) '' Icc (0:Interval) (cut (j,false)) := by
        rw [hparamSub,Set.uIcc_of_ge (hedge j).2.1.le]
        exact ⟨ht.1.le,htc⟩
      obtain ⟨u,hu,he⟩ := hh
      have huc : u < cut (j,false) := by
        apply lt_of_le_of_ne hu.2
        intro heq
        have htEq : t = edge (j,false) := he.symm.trans (congrArg (param (j,false)) heq)
        exact ht.1.ne htEq.symm
      have hh := hMopen (j,false) u huc
      change E (a j.val (param (j,false) u)).val ∈ _ at hh
      rwa [he] at hh
    · have hh : t ∈ param (j,true) '' Icc (0:Interval) (cut (j,true)) := by
        rw [hparamSub,Set.uIcc_of_le (hedge j).2.2.1.le]
        exact ⟨(lt_of_not_ge htc).le,ht.2.le⟩
      obtain ⟨u,hu,he⟩ := hh
      have huc : u < cut (j,true) := by
        apply lt_of_le_of_ne hu.2
        intro heq
        have htEq : t = edge (j,true) := he.symm.trans (congrArg (param (j,true)) heq)
        exact ht.2.ne htEq
      have hh := hMopen (j,true) u huc
      change E (a j.val (param (j,true) u)).val ∈ _ at hh
      rwa [he] at hh
  have hOpenTrace (j : Inc) :
      chartPull F E (Metric.ball (0:Plane) 1) ∩ range (a j.val) =
      a j.val '' Ioo (edge (j,false)) (edge (j,true)) := by
    apply Set.Subset.antisymm
    · intro y hy
      have hyD : y ∈ chartPull F E (Metric.closedBall (0:Plane) 1) ∩ range (a j.val) :=
        ⟨⟨hy.1.1,Metric.ball_subset_closedBall hy.1.2⟩,hy.2⟩
      obtain ⟨t,ht,rfl⟩ := (hSubtypeTrace j) ▸ hyD
      have hleftNe : t ≠ edge (j,false) := by
        intro he
        have hh := hy.1.2
        rw [he] at hh
        exact (Metric.sphere_disjoint_ball : Disjoint (Metric.sphere (0:Plane) 1)
          (Metric.ball (0:Plane) 1)) |>.le_bot ⟨hSphere (j,false),hh⟩
      have hrightNe : t ≠ edge (j,true) := by
        intro he
        have hh := hy.1.2
        rw [he] at hh
        exact (Metric.sphere_disjoint_ball : Disjoint (Metric.sphere (0:Plane) 1)
          (Metric.ball (0:Plane) 1)) |>.le_bot ⟨hSphere (j,true),hh⟩
      exact ⟨t,⟨lt_of_le_of_ne ht.1 (Ne.symm hleftNe),lt_of_le_of_ne ht.2 hrightNe⟩,rfl⟩
    · rintro y ⟨t,ht,rfl⟩
      have hh := (hSubtypeTrace j).symm ▸ (show a j.val t ∈ a j.val ''
        Icc (edge (j,false)) (edge (j,true)) from ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩)
      exact ⟨⟨hh.1.1,hInside j t ht⟩,mem_range_self _⟩
  have hAway (j : κ) (hj : p ∉ range (a j)) :
      Disjoint (chartPull F E (Metric.closedBall (0:Plane) 1)) (range (a j)) := by
    apply disjoint_left.mpr
    rintro y hy ⟨t,ht⟩
    apply hFarClear y.val hy.1 hy.2
    right
    exact mem_iUnion.mpr ⟨⟨j,hj⟩,t,congrArg Subtype.val ht⟩
  have hPortInjective : Function.Injective (fun j : Inc × Bool => M j (cut j)) := by
    intro i j he
    by_contra hij
    have hβeq : β i (cut i) = β j (cut j) := E.injOn
      (hEQ.symm ▸ (hβU i (cut i))) (hEQ.symm ▸ (hβU j (cut j))) he
    have hp : β i (cut i) = p.val := Set.mem_singleton_iff.mp
      (hβmeet i j hij ▸ (show β i (cut i) ∈ range (β i) ∩ range (β j) from
        ⟨mem_range_self _,⟨cut j,hβeq.symm⟩⟩))
    have hz : M i (cut i) = 0 := by change E (β i (cut i)) = 0;rw [hp,hEp]
    have hn := hcutz i
    change ‖M i (cut i)‖ = 1 at hn
    rw [hz,norm_zero] at hn
    norm_num at hn
  refine ⟨E,(fun j => edge (j,false)),(fun j => edge (j,true)),center,?_⟩
  dsimp only
  refine ⟨?_,⟨?_,hEp⟩,hEBall,hedge,hcenter,hSubtypeTrace,hOpenTrace,?_,hAway,?_,?_⟩
  · intro y hy
    exact (hQs ▸ (hEQ ▸ hy)).2
  · exact hEQ.symm ▸ hpQ
  · intro j
    change (fun t : Interval => E (f j t)) '' Icc (edge (j,false)) (edge (j,true)) =
      segment ℝ (M (j,false) (cut (j,false))) 0 ∪ segment ℝ 0 (M (j,true) (cut (j,true)))
    rw [segment_symm ℝ (M (j,false) (cut (j,false))) 0]
    exact htraceImage j
  · rintro ⟨j,b⟩
    cases b <;> exact hSphere _
  · convert hPortInjective using 1
    funext ⟨j,b⟩
    cases b <;> rfl

theorem finite_round_disk_chord_geometry
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
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
    ∀ (κ : Type) [Fintype κ] (port : κ × Bool → EuclideanSpace ℝ (Fin 2)),
      (∀ z, port z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) →
      Function.Injective port →
      let L := fun i => segment ℝ (port (i,false)) (port (i,true))
      let v := fun i => port (i,true)-port (i,false)
      (∀ i, Schoenflies.IsArcBetween (L i) (port (i,false)) (port (i,true))) ∧
      (∀ i, L i \ {port (i,false),port (i,true)} ⊆
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      (∀ i j, i ≠ j → (L i ∩ L j).Subsingleton) ∧
      (∀ i j, i ≠ j → ∀ z ∈ L i ∩ L j,
        z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
        z ∈ openSegment ℝ (port (i,false)) (port (i,true)) ∧
        z ∈ openSegment ℝ (port (j,false)) (port (j,true)) ∧
        ∃ T : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2)),
          T (v i) = Schoenflies.Plane.mk 1 0 ∧ T (v j) = Schoenflies.Plane.mk 0 1) := by
  dsimp only
  intro κ _ port hSphere hPort
  let L := fun i => segment ℝ (port (i,false)) (port (i,true))
  let v := fun i => port (i,true) - port (i,false)
  change (∀ i, IsArcBetween (L i) (port (i,false)) (port (i,true))) ∧
    (∀ i, L i \ {port (i,false),port (i,true)} ⊆ Metric.ball (0 : Plane) 1) ∧
    (∀ i j, i ≠ j → (L i ∩ L j).Subsingleton) ∧
    (∀ i j, i ≠ j → ∀ z ∈ L i ∩ L j,
      z ∈ Metric.ball (0 : Plane) 1 ∧
      z ∈ openSegment ℝ (port (i,false)) (port (i,true)) ∧
      z ∈ openSegment ℝ (port (j,false)) (port (j,true)) ∧
      ∃ T : Plane ≃L[ℝ] Plane, T (v i) = Plane.mk 1 0 ∧ T (v j) = Plane.mk 0 1)
  have hEnds (i : κ) : port (i,false) ≠ port (i,true) := by
    intro h
    have := congrArg Prod.snd (hPort h)
    cases this
  have hv (i : κ) : v i ≠ 0 := sub_ne_zero.mpr (hEnds i).symm
  have hBall (i : κ) : openSegment ℝ (port (i,false)) (port (i,true)) ⊆
      Metric.ball (0 : Plane) 1 :=
    openSegment_subset_ball_of_ne (Metric.sphere_subset_closedBall (hSphere _))
      (Metric.sphere_subset_closedBall (hSphere _)) (hEnds i)
  have hParam (i : κ) (z : Plane) (hz : z ∈ L i) :
      ∃ t ∈ Icc (0 : ℝ) 1, port (i,false) + t • v i = z := by
    change z ∈ segment ℝ (port (i,false)) (port (i,true)) at hz
    rw [segment_eq_image'] at hz
    exact hz
  -- A line through two distinct sphere points has only those two sphere points.
  have hLine (a b q : Plane) (ha : a ∈ Metric.sphere (0 : Plane) 1)
      (hb : b ∈ Metric.sphere (0 : Plane) 1) (hq : q ∈ Metric.sphere (0 : Plane) 1)
      (hab : a ≠ b) (t : ℝ) (he : q = a + t • (b-a)) : q = a ∨ q = b := by
    let sphere : EuclideanGeometry.Sphere Plane := ⟨0,1⟩
    have lineMem (u : ℝ) : a + u • (b-a) ∈ AffineSubspace.mk' a (ℝ ∙ (b-a)) := by
      rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
      exact ⟨u, by simp⟩
    have hbLine : b ∈ AffineSubspace.mk' a (ℝ ∙ (b-a)) := by
      simpa using lineMem 1
    have hbSecond := (sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem
      ha hbLine).2 hb
    have hbEq := hbSecond.resolve_left hab.symm
    have hqLine : q ∈ AffineSubspace.mk' a (ℝ ∙ (b-a)) := he ▸ lineMem t
    have hqSecond := (sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem
      ha hqLine).2 hq
    exact hqSecond.imp_right (fun h => h.trans hbEq.symm)
  have hBoundary (i : κ) (q : Plane) (hq : q ∈ Metric.sphere (0 : Plane) 1)
      (hqL : q ∈ L i) : q = port (i,false) ∨ q = port (i,true) := by
    obtain ⟨t,ht,he⟩ := hParam i q hqL
    exact hLine _ _ _ (hSphere _) (hSphere _) hq (hEnds i) t he.symm
  have hNoPort (i j : κ) (hij : i ≠ j) (b : Bool) : port (i,b) ∉ L j := by
    intro h
    rcases hBoundary j _ (hSphere _) h with h | h
    · exact hij (congrArg Prod.fst (hPort h))
    · exact hij (congrArg Prod.fst (hPort h))
  have hInterior (i j : κ) (hij : i ≠ j) (z : Plane) (hz : z ∈ L i ∩ L j) :
      z ∈ openSegment ℝ (port (i,false)) (port (i,true)) := by
    apply mem_openSegment_of_ne_left_right _ _ hz.1
    · intro h; exact hNoPort i j hij false (h ▸ hz.2)
    · intro h; exact hNoPort i j hij true (h ▸ hz.2)
  have hDet (i j : κ) (hij : i ≠ j) (z : Plane) (hz : z ∈ L i ∩ L j) :
      Plane.det (v i) (v j) ≠ 0 := by
    intro hd
    obtain ⟨r,hr⟩ := (Plane.det_eq_zero_iff_smul (v i) (v j) (hv i)).1 hd
    obtain ⟨t,ht,he⟩ := hParam i z hz.1
    obtain ⟨u,hu,hf⟩ := hParam j z hz.2
    have hp : port (j,false) = port (i,false) + (t-u*r) • v i := by
      have he' : port (i,false) + t • v i = z := he
      have hf' : port (j,false) + u • v j = z := hf
      rw [hr] at hf'
      ext k
      have he0 := congrArg (fun q : Plane => q k) he'
      have hf0 := congrArg (fun q : Plane => q k) hf'
      simp at he0 hf0 ⊢
      linear_combination hf0 - he0
    rcases hLine _ _ _ (hSphere _) (hSphere _) (hSphere _) (hEnds i) (t-u*r) hp with h | h
    · exact hij (congrArg Prod.fst (hPort h)).symm
    · exact hij (congrArg Prod.fst (hPort h)).symm
  refine ⟨fun i => isArcBetween_segment (hEnds i), ?_, ?_, ?_⟩
  · intro i z hz
    apply hBall i
    apply mem_openSegment_of_ne_left_right _ _ hz.1
    · intro h; exact hz.2 (by simp [h])
    · intro h; exact hz.2 (by simp [h])
  · intro i j hij z hz w hw
    have hd := hDet i j hij z hz
    obtain ⟨t,ht,he⟩ := hParam i z hz.1
    obtain ⟨u,hu,hf⟩ := hParam j z hz.2
    obtain ⟨t',ht',he'⟩ := hParam i w hw.1
    obtain ⟨u',hu',hf'⟩ := hParam j w hw.2
    have hvEq : (t-t') • v i = (u-u') • v j := by
      change port (i,false) + t • v i = z at he
      change port (j,false) + u • v j = z at hf
      change port (i,false) + t' • v i = w at he'
      change port (j,false) + u' • v j = w at hf'
      ext k
      have h0 := congrArg (fun q : Plane => q k) he
      have h1 := congrArg (fun q : Plane => q k) he'
      have h2 := congrArg (fun q : Plane => q k) hf
      have h3 := congrArg (fun q : Plane => q k) hf'
      simp at h0 h1 h2 h3 ⊢
      linear_combination h0 - h1 - h2 + h3
    have hscalar := congrArg (fun q => Plane.det q (v j)) hvEq
    simp only [Plane.det_smul_left, Plane.det_self, mul_zero] at hscalar
    have htt' : t = t' := sub_eq_zero.mp ((mul_eq_zero.mp hscalar).resolve_right hd)
    exact he.symm.trans (htt' ▸ he')
  · intro i j hij z hz
    have hi := hInterior i j hij z hz
    have hj := hInterior j i hij.symm z ⟨hz.2,hz.1⟩
    refine ⟨hBall i hi,hi,hj,?_⟩
    have hd := hDet i j hij z hz
    let A : Plane →ₗ[ℝ] Plane := {
      toFun := fun q => q 0 • v i + q 1 • v j
      map_add' := by intro q r; simp [add_smul]; abel
      map_smul' := by intro r q; simp [smul_add,smul_smul,mul_comm] }
    have hA : Function.Injective A := by
      intro q r h
      have hdiff : (q 0-r 0) • v i + (q 1-r 1) • v j = 0 := by
        change q 0 • v i + q 1 • v j = r 0 • v i + r 1 • v j at h
        ext k
        have h0 := congrArg (fun p : Plane => p k) h
        simp at h0 ⊢
        linear_combination h0
      have h0 := congrArg (fun p => Plane.det p (v j)) hdiff
      have h1 := congrArg (fun p => Plane.det (v i) p) hdiff
      simp only [Plane.det_add_left,Plane.det_smul_left,Plane.det_self,
        mul_zero,add_zero] at h0
      rw [show Plane.det 0 (v j) = 0 by simp [Plane.det]] at h0
      simp only [Plane.det_add_right,Plane.det_smul_right,Plane.det_self,
        mul_zero,zero_add] at h1
      rw [show Plane.det (v i) 0 = 0 by simp [Plane.det]] at h1
      have hq0 : q 0 = r 0 := sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hd)
      have hq1 : q 1 = r 1 := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hd)
      ext k; fin_cases k <;> assumption
    let E := LinearEquiv.ofBijective A ⟨hA, LinearMap.surjective_of_injective hA⟩
    refine ⟨E.symm.toContinuousLinearEquiv,?_,?_⟩
    · change E.symm (v i) = Plane.mk 1 0
      apply E.symm_apply_eq.mpr
      change v i = (Plane.mk 1 0) 0 • v i + (Plane.mk 1 0) 1 • v j
      simp
    · change E.symm (v j) = Plane.mk 0 1
      apply E.symm_apply_eq.mpr
      change v j = (Plane.mk 0 1) 0 • v i + (Plane.mk 0 1) 1 • v j
      simp

theorem regional_round_crosscut_supported_chord_movie
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
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
    ∀ (a : C(Interval,↥F)), IsEmbedding a →
      ∀ e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)),
      e.source ⊆ interior F → Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ e.target →
      ∀ l r : Interval, l < r →
      let D := chartPull F e (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
      let U := chartPull F e (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
      D ∩ range a = a '' Icc l r → U ∩ range a = a '' Ioo l r →
      let p₀ := e (a l).val
      let p₁ := e (a r).val
      p₀ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      p₁ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → p₀ ≠ p₁ →
      let A := (fun t => e (a t).val) '' Icc l r
      Schoenflies.IsArcBetween A p₀ p₁ →
      A \ {p₀,p₁} ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      let L := segment ℝ p₀ p₁
      ∃ K : AmbientIsotopy ↥F,
        let b := transport K a
        (∀ t y, y ∉ U → K.map (t,y) = y) ∧
        K.finalMap '' (a '' Icc l r) = chartPull F e L ∧
        D ∩ range b = chartPull F e L ∧
        range b \ U = range a \ U ∧
        range b = (range a \ U) ∪ chartPull F e L ∧
        (∀ t y, y.val ∈ frontier F → K.map (t,y) = y) := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  dsimp only
  intro a ha e heF heDisk l r hlr
  let D := chartPull F e (Metric.closedBall (0 : Plane) 1)
  let U := chartPull F e (Metric.ball (0 : Plane) 1)
  intro hD hU
  let p₀ := e (a l).val
  let p₁ := e (a r).val
  intro hp₀ hp₁ hpne
  let A := (fun t => e (a t).val) '' Icc l r
  intro hA hAi
  let L := segment ℝ p₀ p₁
  have hp₀c : p₀ ∈ Metric.closedBall (0 : Plane) 1 := by
    exact Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hp₀).le
  have hp₁c : p₁ ∈ Metric.closedBall (0 : Plane) 1 := by
    exact Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hp₁).le
  have hL : IsArcBetween L p₀ p₁ := isArcBetween_segment hpne
  have hLi : L \ {p₀,p₁} ⊆ Metric.ball (0 : Plane) 1 := by
    intro z hz
    apply openSegment_subset_ball_of_ne hp₀c hp₁c hpne
    apply mem_openSegment_of_ne_left_right _ _ hz.1
    · intro he; exact hz.2 (by simp [he])
    · intro he; exact hz.2 (by simp [he])
  obtain ⟨G,hGi,hGc,hGf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (Plane.convex_closedSquare 0 1)
    (by rw [Plane.interior_closedSquare]; exact ⟨0,by simp [Plane.openSquare,Plane.supNorm]⟩)
    (Plane.isBounded_closedSquare 0 1)
  have hGc' : G '' Plane.closedSquare 0 1 = Metric.closedBall (0 : Plane) 1 := by
    simpa only [(Plane.isClosed_closedSquare 0 1).closure_eq] using hGc
  have hGi' : G '' Plane.openSquare 0 1 = Metric.ball (0 : Plane) 1 := by
    simpa only [Plane.interior_closedSquare] using hGi
  have hGf' : G '' modelCurve = Metric.sphere (0 : Plane) 1 := by
    simpa only [modelCurve_eq_frontier] using hGf
  have hback (z : Plane) (T : Set Plane) : G.symm z ∈ T ↔ z ∈ G '' T := by
    constructor
    · intro hz; exact ⟨G.symm z,hz,G.apply_symm_apply z⟩
    · rintro ⟨w,hw,rfl⟩; simpa using hw
  have hAsq : IsArcBetween (G.symm '' A) (G.symm p₀) (G.symm p₁) :=
    hA.image_of_injOn subset_rfl G.symm.continuous.continuousOn G.symm.injective.injOn
  have hLsq : IsArcBetween (G.symm '' L) (G.symm p₀) (G.symm p₁) :=
    hL.image_of_injOn subset_rfl G.symm.continuous.continuousOn G.symm.injective.injOn
  have hportsq₀ : G.symm p₀ ∈ modelCurve := (hback p₀ modelCurve).mpr (hGf'.symm ▸ hp₀)
  have hportsq₁ : G.symm p₁ ∈ modelCurve := (hback p₁ modelCurve).mpr (hGf'.symm ▸ hp₁)
  have hinside (T : Set Plane) (hTi : T \ {p₀,p₁} ⊆ Metric.ball (0 : Plane) 1) :
      (G.symm '' T) \ {G.symm p₀,G.symm p₁} ⊆ Plane.openSquare 0 1 := by
    rintro z ⟨⟨w,hw,rfl⟩,hn⟩
    apply (hback w _).mpr
    rw [hGi']
    apply hTi ⟨hw,?_⟩
    intro he
    simp only [mem_insert_iff,mem_singleton_iff] at he
    rcases he with he | he
    · exact hn (by simp [he])
    · exact hn (by simp [he])
  let esq : e.source ≃ₜ (G.symm '' e.target) :=
    e.toHomeomorphSourceTarget.trans (G.symm.image e.target)
  have hesq (y : e.source) : (esq y : Plane) = G.symm (e y.val) := rfl
  have hSquare : Plane.closedSquare 0 1 ⊆ G.symm '' e.target := by
    intro z hz
    refine ⟨G z,heDisk ?_,G.symm_apply_apply z⟩
    rw [← hGc']
    exact ⟨z,hz,rfl⟩
  obtain ⟨H,hHA,hHfix⟩ := position_crosscut_surface_square_support S e.source
    (G.symm '' e.target) e.open_source esq hSquare
    (G.symm '' A) (G.symm '' L) (G.symm p₀) (G.symm p₁)
    hAsq hLsq hportsq₀ hportsq₁ (hinside A hAi) (hinside L hLi)
  have hcoordset (T : Set Plane) :
      {y : S | ∃ u : e.source, u.val = y ∧ (esq u : Plane) ∈ G.symm '' T} =
      {y : S | y ∈ e.source ∧ e y ∈ T} := by
    ext y
    constructor
    · rintro ⟨u,rfl,w,hw,he⟩
      refine ⟨u.property,?_⟩
      rw [hesq] at he
      exact G.symm.injective he ▸ hw
    · rintro ⟨hy,hT⟩
      exact ⟨⟨y,hy⟩,rfl,e y,hT,(hesq ⟨y,hy⟩).symm⟩
  have hopen :
      {y : S | ∃ u : e.source, u.val = y ∧ (esq u : Plane) ∈ Plane.openSquare 0 1} =
      {y : S | y ∈ e.source ∧ e y ∈ Metric.ball (0 : Plane) 1} := by
    ext y
    constructor
    · rintro ⟨u,rfl,hu⟩
      refine ⟨u.property,?_⟩
      rw [hesq] at hu
      exact hGi' ▸ (hback (e u.val) _).mp hu
    · rintro ⟨hy,hb⟩
      refine ⟨⟨y,hy⟩,rfl,?_⟩
      rw [hesq]
      exact (hback (e y) _).mpr (hGi'.symm ▸ hb)
  let US : Set S := {y | y ∈ e.source ∧ e y ∈ Metric.ball (0 : Plane) 1}
  have hUS : US ⊆ interior F := fun _ hy => heF hy.1
  have hHfix' : ∀ t y, y ∉ US → H.map (t,y) = y := by
    simpa only [hopen] using hHfix
  rw [hcoordset A,hcoordset L] at hHA
  obtain ⟨K,hKcoord,hKfix,hKfront⟩ :=
    regional_ambient_isotopy_restricts_with_support F US hUS H hHfix'
  have hfix : ∀ t y, y ∉ U → K.map (t,y) = y := hKfix
  have hsrc (t : Interval) (ht : t ∈ Icc l r) : (a t).val ∈ e.source := by
    have hm : a t ∈ D ∩ range a := hD.symm ▸ ⟨t,ht,rfl⟩
    exact hm.1.1
  have hPullA (y : ↥F) : y ∈ a '' Icc l r ↔ y.val ∈ e.source ∧ e y.val ∈ A := by
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨hsrc t ht,t,ht,rfl⟩
    · rintro ⟨hy,t,ht,he⟩
      refine ⟨t,ht,?_⟩
      apply Subtype.ext
      exact e.injOn (hsrc t ht) hy he
  have hfinalcoord (y : ↥F) : (K.finalMap y).val = H.finalMap y.val := hKcoord 1 y
  have hcut : K.finalMap '' (a '' Icc l r) = chartPull F e L := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      have him : H.finalMap z.val ∈ {y : S | y ∈ e.source ∧ e y ∈ L} := by
        rw [← hHA]
        exact ⟨z.val,(hPullA z).mp hz,rfl⟩
      change (K.finalMap z).val ∈ e.source ∧ e (K.finalMap z).val ∈ L
      rw [hfinalcoord]
      exact him
    · intro hy
      have him : y.val ∈ H.finalMap '' {z : S | z ∈ e.source ∧ e z ∈ A} := hHA.symm ▸ hy
      obtain ⟨z,hz,he⟩ := him
      let zF : ↥F := ⟨z,interior_subset (heF hz.1)⟩
      refine ⟨zF,(hPullA zF).mpr hz,?_⟩
      apply Subtype.ext
      exact (hfinalcoord zF).trans he
  have hinj : Function.Injective K.finalMap := by
    obtain ⟨k,hk⟩ := K.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    intro y z he
    exact k.injective (by simpa only [hk,AmbientIsotopy.finalMap] using he)
  have hUD : U ⊆ D := fun y hy => ⟨hy.1,Metric.ball_subset_closedBall hy.2⟩
  have hfixfinal (y : ↥F) (hy : y ∉ U) : K.finalMap y = y := hfix 1 y hy
  have hmem (T : Set ↥F) (hUT : U ⊆ T) (y : ↥F) : K.finalMap y ∈ T ↔ y ∈ T := by
    constructor
    · intro hy
      by_contra hn
      rw [hfixfinal y (fun hu => hn (hUT hu))] at hy
      exact hn hy
    · intro hy
      by_contra hn
      have he : K.finalMap (K.finalMap y) = K.finalMap y :=
        hfixfinal _ (fun hu => hn (hUT hu))
      exact hn ((hinj he).symm ▸ hy)
  have hrange : range (transport K a) = K.finalMap '' range a := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨a t,⟨t,rfl⟩,rfl⟩
    · rintro ⟨z,⟨t,rfl⟩,rfl⟩; exact ⟨t,rfl⟩
  have hDfinal : D ∩ range (transport K a) = chartPull F e L := by
    rw [hrange,← hcut,← hD]
    ext y
    constructor
    · rintro ⟨hyD,z,hza,rfl⟩
      exact ⟨z,⟨(hmem D hUD z).mp hyD,hza⟩,rfl⟩
    · rintro ⟨z,⟨hzD,hza⟩,rfl⟩
      exact ⟨(hmem D hUD z).mpr hzD,z,hza,rfl⟩
  have hout : range (transport K a) \ U = range a \ U := by
    rw [hrange]
    ext y
    constructor
    · rintro ⟨⟨z,hza,rfl⟩,hn⟩
      have hz : z ∉ U := fun hu => hn ((hmem U subset_rfl z).mpr hu)
      rw [hfixfinal z hz]
      exact ⟨hza,hz⟩
    · rintro ⟨hya,hn⟩
      exact ⟨⟨y,hya,hfixfinal y hn⟩,hn⟩
  refine ⟨K,hfix,hcut,?_,?_,?_,hKfront⟩
  · exact hDfinal
  · exact hout
  · rw [← hout,← hDfinal]
    ext y
    constructor
    · intro hy
      by_cases hu : y ∈ U
      · exact Or.inr ⟨hUD hu,hy⟩
      · exact Or.inl ⟨hy,hu⟩
    · rintro (hy | hy)
      · exact hy.1
      · exact hy.2

theorem regional_local_coordinate_axes_cross
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
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
    ∀ (a b : C(Interval,↥F)), IsEmbedding a → IsEmbedding b →
      ∀ r s : Interval, r ∈ Ioo (0 : Interval) 1 → s ∈ Ioo (0 : Interval) 1 →
      a r = b s → ∀ e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)),
      e.source ⊆ interior F → (a r).val ∈ e.source → e (a r).val = 0 →
      (∀ y : ↥F, y.val ∈ e.source → (y ∈ range a ↔ e y.val 1 = 0)) →
      (∀ y : ↥F, y.val ∈ e.source → (y ∈ range b ↔ e y.val 0 = 0)) →
      RegionalEmbeddedFamily.RegionalTopologicalCrossing F a b r s := by
  classical
  dsimp only
  intro a b ha hb r s hr hs hrs e heInterior hp hezero haxisA haxisB
  let : ClosedSurface S := Classical.choice hS.2.1
  let Ends : Set S := {(a 0).val, (a 1).val, (b 0).val, (b 1).val}
  have hEnds : IsClosed Ends := Set.toFinite Ends |>.isClosed
  have hpEnds : (a r).val ∉ Ends := by
    simp only [Ends, Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h | h | h)
    · exact hr.1.ne' (ha.injective (Subtype.ext h))
    · exact hr.2.ne (ha.injective (Subtype.ext h))
    · exact hs.1.ne' (hb.injective (hrs.symm.trans (Subtype.ext h)))
    · exact hs.2.ne (hb.injective (hrs.symm.trans (Subtype.ext h)))
  let E := e.restr Endsᶜ
  have hEs : E.source = e.source ∩ Endsᶜ := e.restr_source' _ hEnds.isOpen_compl
  have hpE : (a r).val ∈ E.source := by rw [hEs]; exact ⟨hp,hpEnds⟩
  have hEz : E (a r).val = 0 := hezero
  obtain ⟨σ,N,hσ,hNs,hNz,hSquare,hNformula,hsmall⟩ :=
    CurveComplex.HyperellipticModel.ArcSurgery.rescale_centered_chart_to_unit_square
      E (a r).val hpE hEz 1 (by norm_num)
  have hNsub : N.source ⊆ e.source := by rw [hNs,hEs]; exact inter_subset_left
  have hNInterior : N.source ⊆ interior F := hNsub.trans heInterior
  have hpN : (a r).val ∈ N.source := hNs.symm ▸ hpE
  have hNEnds : ∀ y ∈ N.source, y ∉ Ends := by
    intro y hy
    rw [hNs,hEs] at hy
    exact hy.2
  have haxisAN (y : ↥F) (hy : y.val ∈ N.source) :
      y ∈ range a ↔ N y.val 1 = 0 := by
    rw [hNformula]
    change y ∈ range a ↔ σ⁻¹ * e y.val 1 = 0
    rw [mul_eq_zero,or_iff_right (inv_ne_zero hσ.ne')]
    exact haxisA y (hNsub hy)
  have haxisBN (y : ↥F) (hy : y.val ∈ N.source) :
      y ∈ range b ↔ N y.val 0 = 0 := by
    rw [hNformula]
    change y ∈ range b ↔ σ⁻¹ * e y.val 0 = 0
    rw [mul_eq_zero,or_iff_right (inv_ne_zero hσ.ne')]
    exact haxisB y (hNsub hy)
  let W := Set.Icc (-1 : ℝ) 1
  let : Fact ((-1 : ℝ) ≤ 1) := ⟨by norm_num⟩
  let : PreconnectedSpace W := Subtype.preconnectedSpace isPreconnected_Icc
  let zm : W := ⟨-1,by simp [W]⟩
  let zp : W := ⟨1,by simp [W]⟩
  let z0 : W := ⟨0,by simp [W]⟩
  let f : Bool → C(Interval,↥F) := fun j => if j then b else a
  let center : Bool → Interval := fun j => if j then s else r
  let axis : Bool → ℝ → Plane := fun j u => if j then Plane.mk 0 u else Plane.mk u 0
  have haxisSquare (j : Bool) (u : W) : axis j u.val ∈ Plane.closedSquare 0 1 := by
    cases j <;> simp [axis, mem_closedSquare_zero_one,Plane.supNorm,
      abs_le.mpr u.property]
  have haxisZero (j : Bool) : axis j 0 = 0 := by
    cases j <;> apply PiLp.ext <;> intro i <;> fin_cases i <;> rfl
  have haxisInj (j : Bool) : Function.Injective (axis j) := by
    cases j <;> intro x y h
    · exact congrArg (fun z : Plane => z 0) h
    · exact congrArg (fun z : Plane => z 1) h
  have hf (j : Bool) : IsEmbedding (f j) := by cases j <;> assumption
  have hfc (j : Bool) : f j (center j) = a r := by cases j; rfl; exact hrs.symm
  have hAxis (j : Bool) (y : ↥F) (hy : y.val ∈ N.source) :
      y ∈ range (f j) ↔ N y.val (if j then 0 else 1) = 0 := by
    cases j
    · exact haxisAN y hy
    · exact haxisBN y hy
  let Y (j : Bool) (u : W) : ↥F :=
    ⟨N.symm (axis j u.val),interior_subset (hNInterior
      (N.map_target (hSquare (haxisSquare j u))))⟩
  have hYs (j : Bool) (u : W) : (Y j u).val ∈ N.source :=
    N.map_target (hSquare (haxisSquare j u))
  have hNY (j : Bool) (u : W) : N (Y j u).val = axis j u.val :=
    N.right_inv (hSquare (haxisSquare j u))
  have hYr (j : Bool) (u : W) : Y j u ∈ range (f j) := by
    apply (hAxis j _ (hYs j u)).mpr
    rw [hNY]
    cases j <;> rfl
  have hYc (j : Bool) : Continuous (Y j) := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun u : W => axis j u.val) := by
      cases j <;> dsimp [axis] <;> fun_prop
    exact N.continuousOn_symm.comp_continuous hc (fun u => hSquare (haxisSquare j u))
  let H (j : Bool) := (hf j).toHomeomorph
  let q (j : Bool) : C(W,Set.range (f j)) :=
    ⟨fun u => ⟨Y j u,hYr j u⟩,(hYc j).subtype_mk _⟩
  let clock (j : Bool) : C(W,Interval) :=
    ⟨fun u => (H j).symm (q j u),(H j).symm.continuous.comp (q j).continuous⟩
  have hclock (j : Bool) (u : W) : f j (clock j u) = Y j u := by
    exact congrArg Subtype.val ((H j).apply_symm_apply (q j u))
  have hclockN (j : Bool) (u : W) : N (f j (clock j u)).val = axis j u.val := by
    rw [hclock,hNY]
  have hclockI (j : Bool) : Function.Injective (clock j) := by
    intro u v h
    apply Subtype.ext
    apply haxisInj j
    have hu := hclockN j u
    rw [h] at hu
    exact hu.symm.trans (hclockN j v)
  have hclock0 (j : Bool) : clock j z0 = center j := by
    apply (hf j).injective
    apply Subtype.ext
    apply N.injOn
    · rw [hclock]; exact hYs j z0
    · rw [hfc]; exact hpN
    · rw [hclockN,hfc,hNz]
      exact haxisZero j
  have hclockInterior (j : Bool) (u : W) : 0 < clock j u ∧ clock j u < 1 := by
    have hc : (f j (clock j u)).val ∉ Ends := hNEnds _ (by rw [hclock];exact hYs j u)
    constructor
    · apply lt_of_le_of_ne (show (0 : Interval) ≤ clock j u from bot_le)
      intro h
      apply hc
      rw [← h]
      cases j <;> simp [f,Ends]
    · apply lt_of_le_of_ne (show clock j u ≤ (1 : Interval) from le_top)
      intro h
      apply hc
      rw [h]
      cases j <;> simp [f,Ends]
  have hclockMono (j : Bool) : StrictMono (clock j) ∨ StrictAnti (clock j) :=
    (clock j).continuous.strictMono_of_inj_boundedOrder' (hclockI j)
  let left (j : Bool) : Interval := min (clock j zm) (clock j zp)
  let right (j : Bool) : Interval := max (clock j zm) (clock j zp)
  have hcuts (j : Bool) : 0 < left j ∧ left j < center j ∧
      center j < right j ∧ right j < 1 := by
    have hm0 : zm < z0 := by change (-1:ℝ) < 0; norm_num
    have h0p : z0 < zp := by change (0:ℝ) < 1; norm_num
    rcases hclockMono j with hm | hm
    · have hmp := hm (hm0.trans h0p)
      simp only [left,right,min_eq_left hmp.le,max_eq_right hmp.le]
      exact ⟨(hclockInterior j zm).1,(hm hm0).trans_eq (hclock0 j),
        (hclock0 j).symm.trans_lt (hm h0p),(hclockInterior j zp).2⟩
    · have hpm := hm (hm0.trans h0p)
      simp only [left,right,min_eq_right hpm.le,max_eq_left hpm.le]
      exact ⟨(hclockInterior j zp).1,(hm h0p).trans_eq (hclock0 j),
        (hclock0 j).symm.trans_lt (hm hm0),(hclockInterior j zm).2⟩
  have hclockRange (j : Bool) : range (clock j) = Icc (left j) (right j) := by
    have hmp : zm ≤ zp := by change (-1:ℝ) ≤ 1; norm_num
    have hmu (u : W) : zm ≤ u := u.property.1
    have hup (u : W) : u ≤ zp := u.property.2
    rcases hclockMono j with hm | hm
    · have hmp' := hm.monotone hmp
      simp only [left,right,min_eq_left hmp',max_eq_right hmp']
      apply Set.Subset.antisymm
      · rintro t ⟨u,rfl⟩; exact ⟨hm.monotone (hmu u),hm.monotone (hup u)⟩
      · exact intermediate_value_univ zm zp (clock j).continuous
    · have hpm := hm.antitone hmp
      simp only [left,right,min_eq_right hpm,max_eq_left hpm]
      apply Set.Subset.antisymm
      · rintro t ⟨u,rfl⟩; exact ⟨hm.antitone (hup u),hm.antitone (hmu u)⟩
      · exact intermediate_value_univ zp zm (clock j).continuous
  have htrace (j : Bool) :
      ({y : ↥F | y.val ∈ N.source ∧ N y.val ∈ Plane.closedSquare 0 1} ∩
        range (f j)) = (f j) '' Icc (left j) (right j) := by
    apply Set.Subset.antisymm
    · rintro y ⟨hy,⟨t,ht⟩⟩
      have hz := (hAxis j y hy.1).mp ⟨t,ht⟩
      let u : W := ⟨N y.val (if j then 1 else 0),by
        have hsq := mem_closedSquare_zero_one.mp hy.2
        have habs : |N y.val (if j then 1 else 0)| ≤ 1 := by
          cases j
          · exact (Plane.abs_zero_le_supNorm _).trans hsq
          · exact (Plane.abs_one_le_supNorm _).trans hsq
        exact abs_le.mp habs⟩
      have hEq : N y.val = axis j u.val := by
        cases j <;> apply PiLp.ext <;> intro i <;> fin_cases i
        · rfl
        · exact hz
        · exact hz
        · rfl
      have hY : Y j u = y := by
        apply Subtype.ext
        change N.symm (axis j u.val) = y.val
        rw [← hEq,N.left_inv hy.1]
      refine ⟨clock j u,hclockRange j ▸ Set.mem_range_self u,?_⟩
      exact (hclock j u).trans hY
    · rintro y ⟨t,ht,rfl⟩
      obtain ⟨u,rfl⟩ := (hclockRange j).symm ▸ ht
      exact ⟨⟨by rw [hclock]; exact hYs j u,by rw [hclockN]; exact haxisSquare j u⟩,
        Set.mem_range_self _⟩
  have hparam (j : Bool) (t : Interval) (ht : t ∈ Icc (left j) (right j)) :
      ∃ u : W, clock j u = t := by
    have hh : t ∈ range (clock j) := (hclockRange j).symm ▸ ht
    exact hh
  have hends (j : Bool) :
      (clock j zm = left j ∧ clock j zp = right j) ∨
      (clock j zp = left j ∧ clock j zm = right j) := by
    rcases le_total (clock j zm) (clock j zp) with hh | hh
    · exact Or.inl ⟨(min_eq_left hh).symm,(max_eq_right hh).symm⟩
    · exact Or.inr ⟨(min_eq_right hh).symm,(max_eq_left hh).symm⟩
  have hparamOpen (j : Bool) (t : Interval) (ht : t ∈ Ioo (left j) (right j)) :
      ∃ u : W, clock j u = t ∧ -1 < u.val ∧ u.val < 1 := by
    obtain ⟨u,hu⟩ := hparam j t ⟨ht.1.le,ht.2.le⟩
    have hum : u ≠ zm := by
      intro hh
      rw [hh] at hu
      rcases hends j with hh | hh
      · exact ht.1.ne (hu.symm.trans hh.1).symm
      · exact ht.2.ne (hu.symm.trans hh.2)
    have hup : u ≠ zp := by
      intro hh
      rw [hh] at hu
      rcases hends j with hh | hh
      · exact ht.2.ne (hu.symm.trans hh.2)
      · exact ht.1.ne (hu.symm.trans hh.1).symm
    refine ⟨u,hu,lt_of_le_of_ne u.property.1 ?_,lt_of_le_of_ne u.property.2 ?_⟩
    · intro h; exact hum (Subtype.ext h.symm)
    · intro h; exact hup (Subtype.ext h)
  have hmodel (j : Bool) :
      (fun t : Interval => N (f j t).val) '' Icc (left j) (right j) =
        {z : Plane | z ∈ Plane.closedSquare 0 1 ∧ z (if j then 0 else 1) = 0} := by
    apply Set.Subset.antisymm
    · rintro z ⟨t,ht,rfl⟩
      obtain ⟨u,hu⟩ := hparam j t ht
      rw [← hu]
      change N (f j (clock j u)).val ∈
        {z : Plane | z ∈ Plane.closedSquare 0 1 ∧ z (if j then 0 else 1) = 0}
      rw [hclockN]
      refine ⟨haxisSquare j u,?_⟩
      cases j <;> rfl
    · rintro z ⟨hz,hz0⟩
      let u : W := ⟨z (if j then 1 else 0),by
        have hsq := mem_closedSquare_zero_one.mp hz
        have habs : |z (if j then 1 else 0)| ≤ 1 := by
          cases j
          · exact (Plane.abs_zero_le_supNorm _).trans hsq
          · exact (Plane.abs_one_le_supNorm _).trans hsq
        exact abs_le.mp habs⟩
      refine ⟨clock j u,hclockRange j ▸ Set.mem_range_self u,?_⟩
      change N (f j (clock j u)).val = z
      rw [hclockN]
      cases j <;> apply PiLp.ext <;> intro i <;> fin_cases i
      · rfl
      · exact hz0.symm
      · exact hz0.symm
      · rfl
  have hopen (j : Bool) (t : Interval) (ht : t ∈ Ioo (left j) (right j)) :
      N (f j t).val ∈ Plane.openSquare 0 1 := by
    obtain ⟨u,hu,hum,hup⟩ := hparamOpen j t ht
    rw [← hu,hclockN,mem_openSquare_zero_one]
    cases j <;> simpa [axis,Plane.supNorm] using (abs_lt.mpr ⟨hum,hup⟩)
  have hboundary (j : Bool) :
      N (f j (left j)).val ∈ modelCurve ∧ N (f j (right j)).val ∈ modelCurve := by
    have hm : N (f j (clock j zm)).val ∈ modelCurve := by
      rw [hclockN]; cases j <;> simp [axis,zm,modelCurve,Plane.supNorm]
    have hp : N (f j (clock j zp)).val ∈ modelCurve := by
      rw [hclockN]; cases j <;> simp [axis,zp,modelCurve,Plane.supNorm]
    rcases hends j with he | he
    · exact ⟨he.1 ▸ hm,he.2 ▸ hp⟩
    · exact ⟨he.1 ▸ hp,he.2 ▸ hm⟩
  have hOnly (t : Interval) (ht : t ∈ Icc (left true) (right true)) :
      b t ∈ range a ↔ t = s := by
    obtain ⟨u,hu⟩ := hparam true t ht
    have hbt : (b t).val ∈ N.source := by
      change (f true t).val ∈ N.source
      rw [← hu,hclock]
      exact hYs true u
    constructor
    · intro htA
      have hz := (haxisAN (b t) hbt).mp htA
      have hcoord : N (b t).val = axis true u.val := by
        change N (f true t).val = _
        rw [← hu,hclockN]
      rw [hcoord] at hz
      change u.val = 0 at hz
      have hu0 : u = z0 := Subtype.ext hz
      exact hu.symm.trans ((congrArg (clock true) hu0).trans (hclock0 true))
    · rintro rfl
      exact ⟨r,hrs⟩
  let C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F a b r s := {
    chart := N
    aLeft := left false
    aRight := right false
    bLeft := left true
    bRight := right true
    r_interior := hr
    s_interior := hs
    contact := hrs
    a_cuts := hcuts false
    b_cuts := hcuts true
    square_in_target := hSquare
    closed_support_interior := fun y hy => hNInterior hy.1
    whole_a_trace := htrace false
    whole_b_trace := htrace true
    anchor_diameter := hmodel false
    contact_at_origin := hNz
    b_open_inside := hopen true
    b_left_boundary := (hboundary true).1
    b_right_boundary := (hboundary true).2
    only_contact := hOnly }
  refine ⟨C,?_⟩
  change ((∀ t ∈ Ioo (left true) s, 0 < N (b t).val 1) ∧
    (∀ t ∈ Ioo s (right true), N (b t).val 1 < 0)) ∨
    ((∀ t ∈ Ioo (left true) s, N (b t).val 1 < 0) ∧
    (∀ t ∈ Ioo s (right true), 0 < N (b t).val 1))
  have hcoordinate (t : Interval) (u : W) (hu : clock true u = t) :
      N (b t).val 1 = u.val := by
    have hh := congrArg (fun z : Plane => z 1) (hclockN true u)
    change N (b (clock true u)).val 1 = u.val at hh
    rwa [hu] at hh
  rcases hclockMono true with hm | hm
  · right
    constructor
    · intro t ht
      obtain ⟨u,hu⟩ := hparam true t ⟨ht.1.le,(ht.2.trans (hcuts true).2.2.1).le⟩
      have hlt : clock true u < clock true z0 := by rw [hu,hclock0];exact ht.2
      have hu0 : u < z0 := hm.lt_iff_lt.mp hlt
      rw [hcoordinate t u hu]
      exact hu0
    · intro t ht
      obtain ⟨u,hu⟩ := hparam true t ⟨((hcuts true).2.1.trans ht.1).le,ht.2.le⟩
      have hlt : clock true z0 < clock true u := by rw [hu,hclock0];exact ht.1
      have hu0 : z0 < u := hm.lt_iff_lt.mp hlt
      rw [hcoordinate t u hu]
      exact hu0
  · left
    constructor
    · intro t ht
      obtain ⟨u,hu⟩ := hparam true t ⟨ht.1.le,(ht.2.trans (hcuts true).2.2.1).le⟩
      have hlt : clock true u < clock true z0 := by rw [hu,hclock0];exact ht.2
      have hu0 : z0 < u := hm.lt_iff_gt.mp hlt
      rw [hcoordinate t u hu]
      exact hu0
    · intro t ht
      obtain ⟨u,hu⟩ := hparam true t ⟨((hcuts true).2.1.trans ht.1).le,ht.2.le⟩
      have hlt : clock true z0 < clock true u := by rw [hu,hclock0];exact ht.1
      have hu0 : u < z0 := hm.lt_iff_gt.mp hlt
      rw [hcoordinate t u hu]
      exact hu0
