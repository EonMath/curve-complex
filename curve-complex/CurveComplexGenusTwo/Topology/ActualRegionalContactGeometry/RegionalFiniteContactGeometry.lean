import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalInterior
import CurveComplexGenusTwo.Topology.CrosscutIsotopy
import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.ActualNoTriplePosition.ScaleNormalizedChart

set_option maxHeartbeats 2200000

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-! Geometric meanings for the new branch contracts. No chart or side condition
is added to either original parent. Producing this chart from the literal pair
is a separate theorem obligation below and in the regional-context dichotomy. -/

/-- A local support controlling the WHOLE original traces of both arcs.
The anchor is straightened to the horizontal diameter. The other arc is a
single crosscut, with one contact at the origin. All four cut parameters are
strictly interior, and the entire closed support lies in `interior F`.
No differentiability, tangent-line or polynomial-normal-form condition occurs. -/
structure RegionalIsolatedContactChart
    {S : Type} [TopologicalSpace S] (F : Set S)
    (a b : C(Interval, ↥F)) (r s : Interval) where
  chart : OpenPartialHomeomorph S Plane
  aLeft : Interval
  aRight : Interval
  bLeft : Interval
  bRight : Interval
  r_interior : r ∈ Set.Ioo (0 : Interval) 1
  s_interior : s ∈ Set.Ioo (0 : Interval) 1
  contact : a r = b s
  a_cuts : 0 < aLeft ∧ aLeft < r ∧ r < aRight ∧ aRight < 1
  b_cuts : 0 < bLeft ∧ bLeft < s ∧ s < bRight ∧ bRight < 1
  square_in_target : Plane.closedSquare 0 1 ⊆ chart.target
  closed_support_interior :
    {z : S | z ∈ chart.source ∧ chart z ∈ Plane.closedSquare 0 1} ⊆ interior F
  whole_a_trace :
    ({y : ↥F | y.val ∈ chart.source ∧ chart y.val ∈ Plane.closedSquare 0 1} ∩
      Set.range a) = a '' Set.Icc aLeft aRight
  whole_b_trace :
    ({y : ↥F | y.val ∈ chart.source ∧ chart y.val ∈ Plane.closedSquare 0 1} ∩
      Set.range b) = b '' Set.Icc bLeft bRight
  anchor_diameter :
    (fun t : Interval => chart (a t).val) '' Set.Icc aLeft aRight =
      {z : Plane | z ∈ Plane.closedSquare 0 1 ∧ z 1 = 0}
  contact_at_origin : chart (a r).val = 0
  b_open_inside : ∀ t ∈ Set.Ioo bLeft bRight,
    chart (b t).val ∈ Plane.openSquare 0 1
  b_left_boundary : chart (b bLeft).val ∈ modelCurve
  b_right_boundary : chart (b bRight).val ∈ modelCurve
  only_contact : ∀ t ∈ Set.Icc bLeft bRight,
    (b t ∈ Set.range a ↔ t = s)

/-- The two punctured germs occupy the same local side of the straightened
anchor. The two half-squares are precisely the signs of coordinate `1`. -/
def RegionalIsolatedContactChart.SameSide
    {S : Type} [TopologicalSpace S] {F : Set S}
    {a b : C(Interval, ↥F)} {r s : Interval}
    (C : RegionalIsolatedContactChart F a b r s) : Prop :=
  ((∀ t ∈ Set.Ioo C.bLeft s, 0 < C.chart (b t).val 1) ∧
    (∀ t ∈ Set.Ioo s C.bRight, 0 < C.chart (b t).val 1)) ∨
  ((∀ t ∈ Set.Ioo C.bLeft s, C.chart (b t).val 1 < 0) ∧
    (∀ t ∈ Set.Ioo s C.bRight, C.chart (b t).val 1 < 0))

/-- Topological crossing in a particular actual support: the two punctured
germs occupy opposite sides of the horizontal anchor. -/
def RegionalIsolatedContactChart.OppositeSides
    {S : Type} [TopologicalSpace S] {F : Set S}
    {a b : C(Interval, ↥F)} {r s : Interval}
    (C : RegionalIsolatedContactChart F a b r s) : Prop :=
  ((∀ t ∈ Set.Ioo C.bLeft s, 0 < C.chart (b t).val 1) ∧
    (∀ t ∈ Set.Ioo s C.bRight, C.chart (b t).val 1 < 0)) ∨
  ((∀ t ∈ Set.Ioo C.bLeft s, C.chart (b t).val 1 < 0) ∧
    (∀ t ∈ Set.Ioo s C.bRight, 0 < C.chart (b t).val 1))

/-- A geometric crossing of these same original F-valued arcs, witnessed by an
actual chart controlling their whole traces; this is not smooth transversality. -/
def RegionalTopologicalCrossing
    {S : Type} [TopologicalSpace S] (F : Set S)
    (a b : C(Interval, ↥F)) (r s : Interval) : Prop :=
  ∃ C : RegionalIsolatedContactChart F a b r s, C.OppositeSides

/-- Every strict-interior contact of the same pair is a topological crossing.
Endpoint contacts are deliberately outside this predicate. -/
def RegionalAllInteriorContactsCross
    {S : Type} [TopologicalSpace S] (F : Set S)
    (a b : C(Interval, ↥F)) : Prop :=
  ∀ r s : Interval,
    r ∈ Set.Ioo (0 : Interval) 1 →
    s ∈ Set.Ioo (0 : Interval) 1 →
    a r = b s → RegionalTopologicalCrossing F a b r s

/-- Actual local geometry must be produced from the embedded finite-contact
pair. Isolated parameter gaps are not substituted for these whole-trace fields.
This is a topological local construction, with no smoothness assumption. -/
theorem regional_finite_contact_has_isolated_contact_chart
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (hfinite : (Set.range a ∩ Set.range b).Finite)
    (r s : Interval)
    (hr : r ∈ Set.Ioo (0 : Interval) 1)
    (hs : s ∈ Set.Ioo (0 : Interval) 1)
    (hrs : a r = b s) (hp : (a r).val ∈ interior F) :
    ∃ C : RegionalIsolatedContactChart F a b r s,
      C.SameSide ∨ C.OppositeSides := by
  classical
  let p := (a r).val
  let f : Bool → C(Interval,S) := fun j =>
    if j then ⟨fun t => (b t).val, continuous_subtype_val.comp b.continuous⟩
    else ⟨fun t => (a t).val, continuous_subtype_val.comp a.continuous⟩
  let center : Bool → Interval := fun j => if j then s else r
  have hf (j : Bool) : IsEmbedding (f j) := by
    cases j
    · exact IsEmbedding.subtypeVal.comp ha
    · exact IsEmbedding.subtypeVal.comp hb
  have hfc (j : Bool) : f j (center j) = p := by
    cases j
    · rfl
    · exact congrArg Subtype.val hrs.symm
  have hci (j : Bool) : center j ∈ Set.Ioo (0:Interval) 1 := by
    cases j <;> assumption
  let e := chartAt Plane p
  let Q := (e.restr (interior F)).trans (Homeomorph.subRight (e p)).toOpenPartialHomeomorph
  have hQs : Q.source = e.source ∩ interior F := by
    simp [Q,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.restr_source]
  have hpQ : p ∈ Q.source := by rw [hQs];exact ⟨mem_chart_source _ _,hp⟩
  have hQp : Q p = 0 := by change e p - e p = 0;exact sub_self _
  let Contacts : Set S := Subtype.val '' (Set.range a ∩ Set.range b)
  have hContacts : Contacts.Finite := hfinite.image _
  let U := Q.source \ (Contacts \ {p})
  have hU : IsOpen U := Q.open_source.sdiff hContacts.sdiff.isClosed
  have hpU : p ∈ U := ⟨hpQ,fun h => h.2 (Set.mem_singleton p)⟩
  have hwindow (j : Bool) : ∃ l d : Interval,
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
  let tip : Bool × Bool → Interval := fun j => if j.2 then right j.1 else left j.1
  let param : Bool × Bool → C(Interval,Interval) := fun j => {
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
  have hparam0 (j : Bool × Bool) : param j 0 = center j.1 := Subtype.ext (by
    change (center j.1).val + ((tip j).val - (center j.1).val)*0 = (center j.1).val
    ring)
  have hparam1 (j : Bool × Bool) : param j 1 = tip j := Subtype.ext (by
    change (center j.1).val + ((tip j).val - (center j.1).val)*1 = (tip j).val
    ring)
  have htipne (j : Bool × Bool) : tip j ≠ center j.1 := by
    rcases j with ⟨j,k⟩
    cases k
    · exact (hleft j).ne
    · exact (hright j).ne.symm
  have hparami (j : Bool × Bool) : Function.Injective (param j) := by
    intro t u he
    apply Subtype.ext
    have heq := congrArg Subtype.val he
    change (center j.1).val + ((tip j).val - (center j.1).val)*t.val =
      (center j.1).val + ((tip j).val - (center j.1).val)*u.val at heq
    have hne : (tip j).val - (center j.1).val ≠ 0 := sub_ne_zero.mpr (fun hh =>
      htipne j (Subtype.ext hh))
    exact mul_left_cancel₀ hne (add_left_cancel heq)
  have hparamK (j : Bool × Bool) (t : Interval) :
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
  let β : Bool × Bool → C(Interval,S) := fun j => (f j.1).comp (param j)
  have hβ (j : Bool × Bool) : IsEmbedding (β j) :=
    (hf j.1).comp (((param j).continuous.isClosedEmbedding (hparami j)).isEmbedding)
  have hβ0 (j : Bool × Bool) : β j 0 = p := by
    change f j.1 (param j 0) = p
    rw [hparam0,hfc]
  have hβU (j : Bool × Bool) (t : Interval) : β j t ∈ U :=
    hwindow j.1 _ (hparamK j t)
  have hβmeet (i j : Bool × Bool) (hij : i ≠ j) :
      Set.range (β i) ∩ Set.range (β j) = {p} := by
    apply Set.Subset.antisymm
    · rintro y ⟨⟨t,rfl⟩,⟨u,heu⟩⟩
      have he : f j.1 (param j u) = f i.1 (param i t) := heu
      have hpval : β i t = p := by
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
          change f i.1 (param i t) = p
          rw [hpt,hfc]
        · have hContact : β i t ∈ Contacts := by
            rcases i with ⟨i,k⟩
            rcases j with ⟨j,l⟩
            cases i <;> cases j
            · exact (hj rfl).elim
            · refine ⟨a (param (false,k) t),⟨Set.mem_range_self _,?_⟩,rfl⟩
              refine ⟨param (true,l) u,Subtype.ext he⟩
            · refine ⟨b (param (true,k) t),⟨?_,Set.mem_range_self _⟩,rfl⟩
              refine ⟨param (false,l) u,Subtype.ext he⟩
            · exact (hj rfl).elim
          by_contra hn
          exact (hβU i t).2 ⟨hContact,hn⟩
      exact Set.mem_singleton_iff.mpr hpval
    · rintro y rfl
      exact ⟨⟨0,hβ0 i⟩,⟨0,hβ0 j⟩⟩
  let Far : Set S := ⋃ j : Bool, f j '' (Set.Ioo (left j) (right j))ᶜ
  have hFar : IsClosed Far := isClosed_iUnion_of_finite (fun j =>
    ((isCompact_univ.of_isClosed_subset isOpen_Ioo.isClosed_compl (Set.subset_univ _)).image
      (f j).continuous).isClosed)
  have hpFar : p ∉ Far := by
    intro hh
    obtain ⟨j,t,ht,he⟩ := Set.mem_iUnion.mp hh
    have heq : t = center j := (hf j).injective (he.trans (hfc j).symm)
    exact ht (heq.symm ▸ ⟨hleft j,hright j⟩)
  let V := Q '' (Q.source \ Far)
  have hV : IsOpen V := Q.isOpen_image_of_subset_source
    (Q.open_source.sdiff hFar) Set.diff_subset
  have hzeroV : (0:Plane) ∈ V := ⟨p,⟨hpQ,hpFar⟩,hQp⟩
  let γ : Bool × Bool → Interval → Plane := fun j => Q ∘ β j
  have hγ (j : Bool × Bool) : IsClosedEmbedding (γ j) := by
    apply (Q.continuousOn.comp_continuous (β j).continuous
      (fun t => (hβU j t).1)).isClosedEmbedding
    intro t u he
    exact (hβ j).injective (Q.injOn (hβU j t).1 (hβU j u).1 he)
  have hγ0 (j : Bool × Bool) : γ j 0 = 0 := by
    change Q (β j 0) = 0
    rw [hβ0,hQp]
  have hγmeet (i j : Bool × Bool) (hij : i ≠ j) :
      Set.range (γ i) ∩ Set.range (γ j) = {0} := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨t,rfl⟩,⟨u,he⟩⟩
      have hβeq : β j u = β i t := Q.injOn (hβU j u).1 (hβU i t).1 he
      have hp : β i t = p := Set.mem_singleton_iff.mp
        (hβmeet i j hij ▸ (show β i t ∈ Set.range (β i) ∩ Set.range (β j) from
          ⟨Set.mem_range_self _,⟨u,hβeq⟩⟩))
      change Q (β i t) = 0
      rw [hp,hQp]
    · rintro z rfl
      exact ⟨⟨0,hγ0 i⟩,⟨0,hγ0 j⟩⟩
  obtain ⟨R,hop⟩ := prescribed_pair_finite_actual_star_radialization_zero
    γ hγ hγ0 hγmeet (false,false) (false,true) (by decide) V hV hzeroV
  have hparamRange (j : Bool × Bool) : Set.range (param j) =
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
  have hwholeCover (j : Bool) : Set.range (f j) ⊆
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
      exact Set.mem_iUnion.mpr ⟨j,t,ht,rfl⟩
  have hLinear (v : Plane) (hv : v ≠ 0) :
      ∃ T : Plane ≃L[ℝ] Plane, T v = Plane.mk 1 0 := by
    let L : ℂ ≃L[ℝ] Plane := Complex.equivRealProdCLM.trans
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
        (EuclideanSpace.equiv (Fin 2) ℝ).symm)
    let ζ : ℂ := L.symm v
    have hζ : ζ ≠ 0 := by
      intro hz
      apply hv
      have hh := congrArg L hz
      simpa [ζ] using hh
    let M : ℂ ≃L[ℂ] ℂ :=
      (LinearEquiv.smulOfNeZero ℂ ℂ ζ⁻¹ (inv_ne_zero hζ)).toContinuousLinearEquiv
    let T : Plane ≃L[ℝ] Plane := L.symm.trans ((M.restrictScalars ℝ).trans L)
    refine ⟨T,?_⟩
    change L (ζ⁻¹ * ζ) = Plane.mk 1 0
    rw [inv_mul_cancel₀ hζ]
    rfl
  obtain ⟨T,hTv⟩ := hLinear (R.vector (false,false)) (R.vector_nonzero _)
  let Q₀ := Q.transHomeomorph (R.H.trans T.toHomeomorph)
  have hQ₀s : Q₀.source = Q.source := rfl
  have hQ₀val (x : S) : Q₀ x = T (R.H (Q x)) := rfl
  have hQ₀p : Q₀ p = 0 := by rw [hQ₀val,hQp,R.fixes_center,map_zero]
  have hopen : IsOpen (T.symm ⁻¹' Metric.ball (0:Plane) R.coreRadius) :=
    Metric.isOpen_ball.preimage T.symm.continuous
  have h0open : (0:Plane) ∈ T.symm ⁻¹' Metric.ball (0:Plane) R.coreRadius := by
    rw [Set.mem_preimage,map_zero,Metric.mem_ball,dist_self]
    exact R.core_pos
  obtain ⟨ρ,hρ,hρcore⟩ := Metric.isOpen_iff.mp hopen 0 h0open
  obtain ⟨σ,N,hσ,hNs,hNp,hNSquare,hNval,hNsmall⟩ :=
    CurveComplex.HyperellipticModel.ArcSurgery.rescale_centered_chart_to_unit_square
      Q₀ p hpQ hQ₀p ρ hρ
  have hNQ : N.source = Q.source := hNs
  have hCore (x : S) (hx : x ∈ N.source)
      (hxs : N x ∈ Plane.closedSquare 0 1) :
      R.H (Q x) ∈ Metric.closedBall (0:Plane) R.coreRadius := by
    have hh := hρcore (show Q₀ x ∈ Metric.ball (0:Plane) ρ by
      rw [Metric.mem_ball,dist_zero_right];exact hNsmall x hx hxs)
    change T.symm (T (R.H (Q x))) ∈ Metric.ball (0:Plane) R.coreRadius at hh
    rw [T.symm_apply_apply] at hh
    exact Metric.ball_subset_closedBall hh
  have hFarClear (x : S) (hx : x ∈ N.source)
      (hxs : N x ∈ Plane.closedSquare 0 1) : x ∉ Far := by
    intro hfar
    have hxQ : x ∈ Q.source := hNQ ▸ hx
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
  let M : Bool × Bool → Interval → Plane := fun j t => N (β j t)
  let w : Bool × Bool → Plane := fun j => σ⁻¹ • T (R.vector j)
  have hM (j : Bool × Bool) : Continuous (M j) := N.continuousOn.comp_continuous
    (β j).continuous (fun t => hNQ.symm ▸ (hβU j t).1)
  have hMi (j : Bool × Bool) : Function.Injective (M j) := by
    intro t u he
    exact (hβ j).injective (N.injOn (hNQ.symm ▸ (hβU j t).1)
      (hNQ.symm ▸ (hβU j u).1) he)
  have hM0 (j : Bool × Bool) : M j 0 = 0 := by change N (β j 0) = 0;rw [hβ0,hNp]
  have hMval (j : Bool × Bool) (t : Interval) : M j t = σ⁻¹ • T (R.H (γ j t)) :=
    hNval _
  have hwne (j : Bool × Bool) : w j ≠ 0 := by
    intro he
    have hzero : T (R.vector j) = 0 := by
      have hh := congrArg (fun z : Plane => σ • z) he
      simpa [w,smul_smul,ne_of_gt hσ] using hh
    exact R.vector_nonzero j (T.injective (hzero.trans (map_zero T).symm))
  have hRay (j : Bool × Bool) (t : Interval) (ht : t ≤ R.cut j) :
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
  have hSupPos (j : Bool × Bool) : 0 < Plane.supNorm (w j) := by
    apply lt_of_le_of_ne (Plane.supNorm_nonneg _)
    intro he
    apply hwne j
    ext k
    fin_cases k
    · have hh := Plane.abs_zero_le_supNorm (w j)
      rw [← he] at hh
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    · have hh := Plane.abs_one_le_supNorm (w j)
      rw [← he] at hh
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  let z : Bool × Bool → Interval → ℝ := fun j t => Plane.supNorm (M j t)
  have hz (j : Bool × Bool) : Continuous (z j) := continuous_supNorm.comp (hM j)
  have hzi (j : Bool × Bool) : Set.InjOn (z j) (Set.Icc (0:Interval) (R.cut j)) := by
    intro t ht u hu he
    have htRay := hRay j t ht.2
    have huRay := hRay j u hu.2
    rw [segment_eq_image'] at htRay huRay
    obtain ⟨q,hq,hqt⟩ := htRay
    obtain ⟨d,hd,hdu⟩ := huRay
    simp only [sub_zero,smul_zero,zero_add] at hqt hdu
    have hqd : q = d := by
      change Plane.supNorm (M j t) = Plane.supNorm (M j u) at he
      rw [← hqt,← hdu] at he
      have hsq : Plane.supNorm (q • w j) = q * Plane.supNorm (w j) := by
        rw [Plane.supNorm_smul,abs_of_nonneg hq.1]
      have hsd : Plane.supNorm (d • w j) = d * Plane.supNorm (w j) := by
        rw [Plane.supNorm_smul,abs_of_nonneg hd.1]
      rw [hsq,hsd] at he
      exact mul_right_cancel₀ (ne_of_gt (hSupPos j)) he
    exact hMi j (hqt.symm.trans ((hqd ▸ hdu)))
  have hz0 (j : Bool × Bool) : z j 0 = 0 := by change Plane.supNorm (M j 0) = 0;rw [hM0];norm_num [Plane.supNorm]
  have hzcut (j : Bool × Bool) : 1 < z j (R.cut j) := by
    by_contra hn
    have hsq : M j (R.cut j) ∈ Plane.closedSquare 0 1 :=
      mem_closedSquare_zero_one.mpr (not_lt.mp hn)
    have hh := hCore (β j (R.cut j)) (hNQ.symm ▸ (hβU j _).1) hsq
    have ht : R.H (γ j (R.cut j)) ∈ R.H '' CurveComplex.FiniteStarGeometry.tail γ j (R.cut j) :=
      ⟨γ j (R.cut j),⟨R.cut j,(show (R.cut j).val ≤ (R.cut j).val from le_rfl),rfl⟩,rfl⟩
    exact Set.disjoint_left.mp (R.excludes_tails j) ht hh
  have hzmono (j : Bool × Bool) : StrictMonoOn (z j) (Set.Icc (0:Interval) (R.cut j)) :=
    ContinuousOn.strictMonoOn_of_injOn_Icc (show (0:Interval) ≤ R.cut j from bot_le)
      (by rw [hz0];linarith [hzcut j]) (hz j).continuousOn (hzi j)
  have hcutExists (j : Bool × Bool) : ∃ t : Interval,
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
  have hMsquare (j : Bool × Bool) (t : Interval) :
      M j t ∈ Plane.closedSquare 0 1 ↔ t ≤ cut j := by
    constructor
    · intro hsq
      have htR : t < R.cut j := by
        by_contra hn
        have htail : R.H (γ j t) ∈ R.H '' CurveComplex.FiniteStarGeometry.tail γ j (R.cut j) :=
          ⟨γ j t,⟨t,(show (R.cut j).val ≤ t.val from not_lt.mp hn),rfl⟩,rfl⟩
        exact Set.disjoint_left.mp (R.excludes_tails j) htail
          (hCore _ (hNQ.symm ▸ (hβU j t).1) hsq)
      by_contra hn
      have hh := hzmono j ⟨bot_le,(hcutR j).le⟩ ⟨bot_le,htR.le⟩ (not_le.mp hn)
      rw [hcutz] at hh
      exact (not_lt_of_ge (mem_closedSquare_zero_one.mp hsq)) hh
    · intro ht
      apply mem_closedSquare_zero_one.mpr
      exact (hzmono j).monotoneOn ⟨bot_le,ht.trans (hcutR j).le⟩
        ⟨bot_le,(hcutR j).le⟩ ht |>.trans_eq (hcutz j)
  have hMopen (j : Bool × Bool) (t : Interval) (ht : t < cut j) :
      M j t ∈ Plane.openSquare 0 1 := by
    apply mem_openSquare_zero_one.mpr
    exact (hzmono j ⟨bot_le,ht.le.trans (hcutR j).le⟩
      ⟨bot_le,(hcutR j).le⟩ ht).trans_eq (hcutz j)
  have hNinterior : {x : S | x ∈ N.source ∧ N x ∈ Plane.closedSquare 0 1} ⊆ interior F := by
    intro x hx
    exact (hQs ▸ (hNQ ▸ hx.1)).2
  have hBranchImage (j : Bool × Bool) : M j '' Set.Icc (0:Interval) (cut j) =
      segment ℝ (0:Plane) (M j (cut j)) := by
    have hformula (t : Interval) (ht : t ≤ cut j) :
        M j t = ((z j t) / Plane.supNorm (w j)) • w j := by
      have hh := hRay j t (ht.trans (hcutR j).le)
      rw [segment_eq_image'] at hh
      obtain ⟨q,hq,he⟩ := hh
      simp only [sub_zero,zero_add] at he
      have hzq : z j t = q * Plane.supNorm (w j) := by
        change Plane.supNorm (M j t) = _
        rw [← he,Plane.supNorm_smul,abs_of_nonneg hq.1]
      rw [hzq,mul_div_cancel_right₀ _ (ne_of_gt (hSupPos j))]
      exact he.symm
    have hcutval : M j (cut j) = (Plane.supNorm (w j))⁻¹ • w j := by
      rw [hformula _ le_rfl,hcutz,one_div]
    apply Set.Subset.antisymm
    · rintro q ⟨t,ht,rfl⟩
      rw [segment_eq_image']
      refine ⟨z j t,⟨Plane.supNorm_nonneg _,?_⟩,?_⟩
      · exact mem_closedSquare_zero_one.mp ((hMsquare j t).mpr ht.2)
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
      exact (smul_smul d (Plane.supNorm (w j))⁻¹ (w j)).symm
  let edge : Bool × Bool → Interval := fun j => param j (cut j)
  have hedge (j : Bool) :
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
  have hparamSub (j : Bool × Bool) : param j '' Set.Icc (0:Interval) (cut j) =
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
  have htrace (j : Bool) : {x : S | x ∈ N.source ∧ N x ∈ Plane.closedSquare 0 1} ∩
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
      · exact ⟨⟨hNQ.symm ▸ (hβU (j,false) t).1,(hMsquare _ _).mpr ht.2⟩,
          ⟨param (j,false) t,rfl⟩⟩
      · exact ⟨⟨hNQ.symm ▸ (hβU (j,true) t).1,(hMsquare _ _).mpr ht.2⟩,
          ⟨param (j,true) t,rfl⟩⟩
  have hWaxis : w (false,false) = σ⁻¹ • Plane.mk 1 0 := by
    change σ⁻¹ • T (R.vector (false,false)) = _
    rw [hTv]
  have hWopp : w (false,true) = -(w (false,false)) := by
    change σ⁻¹ • T (R.vector (false,true)) = _
    rw [hop,map_neg,smul_neg]
  have hAends : M (false,false) (cut (false,false)) = Plane.mk 1 0 ∧
      M (false,true) (cut (false,true)) = Plane.mk (-1) 0 := by
    have hformula (j : Bool × Bool) : M j (cut j) =
        (Plane.supNorm (w j))⁻¹ • w j := by
      have hh := hRay j (cut j) (hcutR j).le
      rw [segment_eq_image'] at hh
      obtain ⟨q,hq,he⟩ := hh
      simp only [sub_zero,zero_add] at he
      have hzq : 1 = q * Plane.supNorm (w j) := by
        rw [← hcutz j]
        change Plane.supNorm (M j (cut j)) = _
        rw [← he,Plane.supNorm_smul,abs_of_nonneg hq.1]
      have hqv : q = (Plane.supNorm (w j))⁻¹ := by
        have hh := (eq_div_iff (ne_of_gt (hSupPos j))).mpr hzq.symm
        simpa only [one_div] using hh
      rw [← he,hqv]
    constructor
    · rw [hformula,hWaxis]
      ext k
      fin_cases k <;> simp [Plane.supNorm,Plane.mk,PiLp.smul_apply,abs_of_pos (inv_pos.mpr hσ),max_eq_left (inv_pos.mpr hσ).le,ne_of_gt hσ]
    · rw [hformula,hWopp,hWaxis]
      ext k
      fin_cases k <;> simp [Plane.supNorm,Plane.mk,PiLp.smul_apply,abs_of_pos (inv_pos.mpr hσ),max_eq_left (inv_pos.mpr hσ).le,ne_of_gt hσ]
  have htraceImage (j : Bool) : (fun t : Interval => N (f j t)) ''
      Set.Icc (edge (j,false)) (edge (j,true)) =
      segment ℝ (0:Plane) (M (j,false) (cut (j,false))) ∪
      segment ℝ (0:Plane) (M (j,true) (cut (j,true))) := by
    have hh := congrArg (fun X : Set S => N '' X) (htrace j)
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
  have hdiameter : (fun t : Interval => N (a t).val) ''
      Set.Icc (edge (false,false)) (edge (false,true)) =
      {z : Plane | z ∈ Plane.closedSquare 0 1 ∧ z 1 = 0} := by
    change (fun t : Interval => N (f false t)) '' _ = _
    rw [htraceImage,hAends.1,hAends.2]
    ext z
    constructor
    · intro hz
      have hseg (v : Plane) (hv : v = Plane.mk 1 0 ∨ v = Plane.mk (-1) 0)
          (hz : z ∈ segment ℝ (0:Plane) v) : z ∈ Plane.closedSquare 0 1 ∧ z 1 = 0 := by
        rw [segment_eq_image'] at hz
        obtain ⟨t,ht,rfl⟩ := hz
        simp only [sub_zero,zero_add]
        rcases hv with rfl | rfl
        · constructor
          · apply mem_closedSquare_zero_one.mpr
            simpa [Plane.supNorm,Plane.mk,PiLp.smul_apply,abs_of_nonneg ht.1] using ht.2
          · simp [Plane.mk,PiLp.smul_apply]
        · constructor
          · apply mem_closedSquare_zero_one.mpr
            simpa [Plane.supNorm,Plane.mk,PiLp.smul_apply,abs_of_nonneg ht.1] using ht.2
          · simp [Plane.mk,PiLp.smul_apply]
      exact hz.elim (hseg _ (Or.inl rfl)) (hseg _ (Or.inr rfl))
    · rintro ⟨hz,hz1⟩
      have hz0 : |z 0| ≤ 1 := (Plane.abs_zero_le_supNorm z).trans
        (mem_closedSquare_zero_one.mp hz)
      by_cases hpos : 0 ≤ z 0
      · left
        rw [segment_eq_image']
        refine ⟨z 0,⟨hpos,(le_abs_self _).trans hz0⟩,?_⟩
        ext k
        fin_cases k <;> simp [Plane.mk,PiLp.smul_apply,hz1]
      · right
        rw [segment_eq_image']
        refine ⟨-z 0,⟨by linarith,(neg_le_abs _).trans hz0⟩,?_⟩
        ext k
        fin_cases k <;> simp [Plane.mk,PiLp.smul_apply,hz1]
  have hSubtypeTrace (j : Bool) :
      ({y : ↥F | y.val ∈ N.source ∧ N y.val ∈ Plane.closedSquare 0 1} ∩
        Set.range (if j then b else a)) =
      (if j then b else a) '' Set.Icc (edge (j,false)) (edge (j,true)) := by
    ext y
    constructor
    · intro hy
      have hval : y.val ∈ {x : S | x ∈ N.source ∧ N x ∈ Plane.closedSquare 0 1} ∩
          Set.range (f j) := by
        refine ⟨hy.1,?_⟩
        rcases j <;> obtain ⟨t,rfl⟩ := hy.2 <;> exact ⟨t,rfl⟩
      obtain ⟨t,ht,he⟩ := htrace j ▸ hval
      refine ⟨t,ht,?_⟩
      cases j <;> exact Subtype.ext he
    · rintro ⟨t,ht,rfl⟩
      have hh := (htrace j).symm ▸ (show f j t ∈ f j ''
        Set.Icc (edge (j,false)) (edge (j,true)) from ⟨t,ht,rfl⟩)
      cases j <;> exact ⟨hh.1,Set.mem_range_self _⟩
  have hbInside : ∀ t ∈ Set.Ioo (edge (true,false)) (edge (true,true)),
      N (b t).val ∈ Plane.openSquare 0 1 := by
    intro t ht
    by_cases htc : t ≤ s
    · have hh : t ∈ param (true,false) '' Set.Icc (0:Interval) (cut (true,false)) := by
        rw [hparamSub,Set.uIcc_of_ge (hedge true).2.1.le]
        exact ⟨ht.1.le,htc⟩
      obtain ⟨u,hu,he⟩ := hh
      have huc : u < cut (true,false) := by
        apply lt_of_le_of_ne hu.2
        intro heq
        have htEq : t = edge (true,false) := he.symm.trans (congrArg (param (true,false)) heq)
        exact ht.1.ne htEq.symm
      have hh := hMopen (true,false) u huc
      change N (b (param (true,false) u)).val ∈ _ at hh
      rwa [he] at hh
    · have hh : t ∈ param (true,true) '' Set.Icc (0:Interval) (cut (true,true)) := by
        rw [hparamSub,Set.uIcc_of_le (hedge true).2.2.1.le]
        exact ⟨(lt_of_not_ge htc).le,ht.2.le⟩
      obtain ⟨u,hu,he⟩ := hh
      have huc : u < cut (true,true) := by
        apply lt_of_le_of_ne hu.2
        intro heq
        have htEq : t = edge (true,true) := he.symm.trans (congrArg (param (true,true)) heq)
        exact ht.2.ne htEq
      have hh := hMopen (true,true) u huc
      change N (b (param (true,true) u)).val ∈ _ at hh
      rwa [he] at hh
  have hOnly : ∀ t ∈ Set.Icc (edge (true,false)) (edge (true,true)),
      (b t ∈ Set.range a ↔ t = s) := by
    intro t ht
    constructor
    · intro hta
      have hh := (hSubtypeTrace true).symm ▸ (show b t ∈ b ''
        Set.Icc (edge (true,false)) (edge (true,true)) from ⟨t,ht,rfl⟩)
      have hCover := (hwholeCover true ⟨t,rfl⟩).resolve_left (hFarClear _ hh.1.1 hh.1.2)
      have htU : (b t).val ∈ U := by
        rcases hCover with ⟨u,he⟩ | ⟨u,he⟩
        · have hh := hβU (true,false) u
          rw [he] at hh
          exact hh
        · have hh := hβU (true,true) u
          rw [he] at hh
          exact hh
      have hcontact : (b t).val ∈ Contacts := ⟨b t,⟨hta,Set.mem_range_self t⟩,rfl⟩
      have heq : (b t).val = p := by
        by_contra hn
        exact htU.2 ⟨hcontact,hn⟩
      exact hb.injective (Subtype.ext (heq.trans (congrArg Subtype.val hrs)))
    · rintro rfl
      exact ⟨r,hrs⟩
  let C : RegionalIsolatedContactChart F a b r s := {
    chart := N
    aLeft := edge (false,false)
    aRight := edge (false,true)
    bLeft := edge (true,false)
    bRight := edge (true,true)
    r_interior := hr
    s_interior := hs
    contact := hrs
    a_cuts := hedge false
    b_cuts := hedge true
    square_in_target := hNSquare
    closed_support_interior := hNinterior
    whole_a_trace := hSubtypeTrace false
    whole_b_trace := hSubtypeTrace true
    anchor_diameter := hdiameter
    contact_at_origin := hNp
    b_open_inside := hbInside
    b_left_boundary := hcutz (true,false)
    b_right_boundary := hcutz (true,true)
    only_contact := hOnly }
  let y : Interval → ℝ := fun t => C.chart (b t).val 1
  have hBsupport (t : Interval) (ht : t ∈ Set.Icc C.bLeft C.bRight) :
      (b t).val ∈ C.chart.source ∧ C.chart (b t).val ∈ Plane.closedSquare 0 1 := by
    have hh : b t ∈ b '' Set.Icc C.bLeft C.bRight := ⟨t,ht,rfl⟩
    rw [← C.whole_b_trace] at hh
    exact hh.1
  have hycont : ContinuousOn y (Set.Icc C.bLeft C.bRight) :=
    (Plane.continuous_coord 1).continuousOn.comp
      (C.chart.continuousOn.comp (continuous_subtype_val.comp b.continuous).continuousOn
        (fun t ht => (hBsupport t ht).1)) (Set.mapsTo_univ _ _)
  have hyne (t : Interval) (ht : t ∈ Set.Icc C.bLeft C.bRight) (hts : t ≠ s) : y t ≠ 0 := by
    intro hz
    have hAxis : C.chart (b t).val ∈ (fun t : Interval => C.chart (a t).val) ''
        Set.Icc C.aLeft C.aRight := C.anchor_diameter.symm ▸ ⟨(hBsupport t ht).2,hz⟩
    obtain ⟨u,hu,he⟩ := hAxis
    have huSupport : a u ∈ {y : ↥F | y.val ∈ C.chart.source ∧
        C.chart y.val ∈ Plane.closedSquare 0 1} ∩ Set.range a :=
      C.whole_a_trace.symm ▸ (show a u ∈ a '' Set.Icc C.aLeft C.aRight from ⟨u,hu,rfl⟩)
    have heq : a u = b t := Subtype.ext
      (C.chart.injOn huSupport.1.1 (hBsupport t ht).1 he)
    exact hts ((C.only_contact t ht).mp ⟨u,heq⟩)
  have hleftne : ∀ t ∈ Set.Ioo C.bLeft s, y t ≠ 0 := by
    intro t ht
    exact hyne t ⟨ht.1.le,ht.2.le.trans C.b_cuts.2.2.1.le⟩ ht.2.ne
  have hrightne : ∀ t ∈ Set.Ioo s C.bRight, y t ≠ 0 := by
    intro t ht
    exact hyne t ⟨C.b_cuts.2.1.le.trans ht.1.le,ht.2.le⟩ ht.1.ne.symm
  have hyl : ContinuousOn y (Set.Ioo C.bLeft s) := hycont.mono
    (fun t ht => ⟨ht.1.le,ht.2.le.trans C.b_cuts.2.2.1.le⟩)
  have hyr : ContinuousOn y (Set.Ioo s C.bRight) := hycont.mono
    (fun t ht => ⟨C.b_cuts.2.1.le.trans ht.1.le,ht.2.le⟩)
  obtain ⟨tl,htl⟩ := Set.nonempty_Ioo.mpr C.b_cuts.2.1
  obtain ⟨tr,htr⟩ := Set.nonempty_Ioo.mpr C.b_cuts.2.2.1
  have hlSign : (∀ t ∈ Set.Ioo C.bLeft s, 0 < y t) ∨
      (∀ t ∈ Set.Ioo C.bLeft s, y t < 0) := by
    rcases lt_or_gt_of_ne (hleftne tl htl) with hneg | hpos
    · exact Or.inr (fun t ht => isPreconnected_Ioo.gt_of_ne hyl hleftne ⟨tl,htl,hneg⟩ ht)
    · exact Or.inl (fun t ht => isPreconnected_Ioo.lt_of_ne hyl hleftne ⟨tl,htl,hpos⟩ ht)
  have hrSign : (∀ t ∈ Set.Ioo s C.bRight, 0 < y t) ∨
      (∀ t ∈ Set.Ioo s C.bRight, y t < 0) := by
    rcases lt_or_gt_of_ne (hrightne tr htr) with hneg | hpos
    · exact Or.inr (fun t ht => isPreconnected_Ioo.gt_of_ne hyr hrightne ⟨tr,htr,hneg⟩ ht)
    · exact Or.inl (fun t ht => isPreconnected_Ioo.lt_of_ne hyr hrightne ⟨tr,htr,hpos⟩ ht)
  refine ⟨C,?_⟩
  rcases hlSign with hl | hl <;> rcases hrSign with hh | hh
  · exact Or.inl (Or.inl ⟨hl,hh⟩)
  · exact Or.inr (Or.inl ⟨hl,hh⟩)
  · exact Or.inr (Or.inr ⟨hl,hh⟩)
  · exact Or.inl (Or.inr ⟨hl,hh⟩)

end RegionalEmbeddedFamily
