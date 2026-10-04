import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalFamilyComposition
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalInterior
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalCleanDiskFamily

open CurveComplex Set Topology

namespace RegionalEmbeddedFamily

/-- A fixed-endpoint proper embedded movie, allowing the final parametrization
    to differ by an endpoint-preserving homeomorphism. -/
def RegionalMovie {S : Type*} [TopologicalSpace S] (F : Set S)
    (a b : C(Interval, ↥F)) : Prop :=
  ∃ (V : C(Interval × Interval, ↥F)) (ρ : Interval ≃ₜ Interval),
    ρ 0 = 0 ∧ ρ 1 = 1 ∧
    (∀ s, V (0,s) = a s) ∧ (∀ s, V (1,s) = b (ρ s)) ∧
    (∀ t, Topology.IsEmbedding (fun s => V (t,s))) ∧
    (∀ t, V (t,0) = a 0 ∧ V (t,1) = a 1) ∧
    (∀ t s, s ∈ Set.Ioo (0 : Interval) 1 →
      (V (t,s)).val ∉ frontier F)

theorem regionalMovie_refl {S : Type*} [TopologicalSpace S]
    {F : Set S} (a : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a)
    (hclear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (a s).val ∉ frontier F) : RegionalMovie F a a := by
  let V : C(Interval × Interval, ↥F) :=
    ⟨fun p => a p.2, a.continuous.comp continuous_snd⟩
  refine ⟨V, Homeomorph.refl Interval, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro s; rfl
  · intro s; rfl
  · intro t; exact ha
  · intro t; exact ⟨rfl, rfl⟩
  · intro t s hs; exact hclear s hs

theorem regionalMovie_trans {S : Type*} [TopologicalSpace S]
    {F : Set S} {a b c : C(Interval, ↥F)}
    (hab : RegionalMovie F a b) (hbc : RegionalMovie F b c) :
    RegionalMovie F a c := by
  obtain ⟨U, ρ, hρ0, hρ1, hU0, hU1, hUemb, hUends, hUclear⟩ := hab
  obtain ⟨V, σ, hσ0, hσ1, hV0, hV1, hVemb, hVends, hVclear⟩ := hbc
  exact compose_regional_embedded_families a b c U V ρ σ
    hρ0 hρ1 hσ0 hσ1 hU0 hU1 hV0 hV1
    hUemb hVemb hUends hVends hUclear hVclear

private def reverseClock (t : Interval) : Interval :=
  ⟨1 - (t : ℝ), by
    constructor
    · linarith [t.property.2]
    · linarith [t.property.1]⟩

private theorem reverseClock_continuous : Continuous reverseClock := by
  apply Continuous.subtype_mk
  fun_prop

private theorem reverseClock_zero : reverseClock 0 = 1 :=
  Subtype.ext (by norm_num [reverseClock])

private theorem reverseClock_one : reverseClock 1 = 0 :=
  Subtype.ext (by norm_num [reverseClock])

theorem regionalMovie_symm {S : Type*} [TopologicalSpace S]
    {F : Set S} {a b : C(Interval, ↥F)}
    (hab : RegionalMovie F a b) : RegionalMovie F b a := by
  obtain ⟨V, ρ, hρ0, hρ1, hV0, hV1, hVemb, hVends, hVclear⟩ := hab
  have hσ0 : ρ.symm 0 = 0 := by
    apply ρ.injective
    simp only [ρ.apply_symm_apply, hρ0]
  have hσ1 : ρ.symm 1 = 1 := by
    apply ρ.injective
    simp only [ρ.apply_symm_apply, hρ1]
  have hσinterior (s : Interval) (hs : s ∈ Set.Ioo (0 : Interval) 1) :
      ρ.symm s ∈ Set.Ioo (0 : Interval) 1 := by
    have hn0 : ρ.symm s ≠ 0 := by
      intro he
      have : s = 0 := by calc
        s = ρ (ρ.symm s) := (ρ.apply_symm_apply s).symm
        _ = ρ 0 := by rw [he]
        _ = 0 := hρ0
      exact ne_of_gt hs.1 this
    have hn1 : ρ.symm s ≠ 1 := by
      intro he
      have : s = 1 := by calc
        s = ρ (ρ.symm s) := (ρ.apply_symm_apply s).symm
        _ = ρ 1 := by rw [he]
        _ = 1 := hρ1
      exact ne_of_lt hs.2 this
    exact ⟨lt_of_le_of_ne (ρ.symm s).property.1 (Ne.symm hn0),
      lt_of_le_of_ne (ρ.symm s).property.2 hn1⟩
  let W : C(Interval × Interval, ↥F) :=
    ⟨fun p => V (reverseClock p.1,ρ.symm p.2),
      V.continuous.comp
        ((reverseClock_continuous.comp continuous_fst).prodMk
          (ρ.symm.continuous.comp continuous_snd))⟩
  have hb0 : b 0 = a 0 := by
    calc
      b 0 = b (ρ 0) := by rw [hρ0]
      _ = V (1,0) := (hV1 0).symm
      _ = a 0 := (hVends 1).1
  have hb1 : b 1 = a 1 := by
    calc
      b 1 = b (ρ 1) := by rw [hρ1]
      _ = V (1,1) := (hV1 1).symm
      _ = a 1 := (hVends 1).2
  refine ⟨W, ρ.symm, hσ0, hσ1, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    change V (reverseClock 0,ρ.symm s) = b s
    rw [reverseClock_zero, hV1, ρ.apply_symm_apply]
  · intro s
    change V (reverseClock 1,ρ.symm s) = a (ρ.symm s)
    rw [reverseClock_one, hV0]
  · intro t
    have he := (hVemb (reverseClock t)).comp ρ.symm.isEmbedding
    change Topology.IsEmbedding (fun s => V (reverseClock t,ρ.symm s))
    exact he
  · intro t
    constructor
    · change V (reverseClock t,ρ.symm 0) = b 0
      rw [hσ0]
      exact (hVends (reverseClock t)).1.trans hb0.symm
    · change V (reverseClock t,ρ.symm 1) = b 1
      rw [hσ1]
      exact (hVends (reverseClock t)).2.trans hb1.symm
  · intro t s hs
    exact hVclear (reverseClock t) (ρ.symm s) (hσinterior s hs)

theorem regionalMovie_homotopic {S : Type*} [TopologicalSpace S]
    {F : Set S} {a b : C(Interval, ↥F)}
    (h : RegionalMovie F a b) :
    ∃ (h0 : b 0 = a 0) (h1 : b 1 = a 1),
      Path.Homotopic (⟨a, rfl, rfl⟩ : Path (a 0) (a 1))
        (⟨b, h0, h1⟩ : Path (a 0) (a 1)) := by
  obtain ⟨V, ρ, hρ0, hρ1, hV0, hV1, hVemb, hVends, hVclear⟩ := h
  have h0 : b 0 = a 0 := by
    calc
      b 0 = b (ρ 0) := by rw [hρ0]
      _ = V (1,0) := (hV1 0).symm
      _ = a 0 := (hVends 1).1
  have h1 : b 1 = a 1 := by
    calc
      b 1 = b (ρ 1) := by rw [hρ1]
      _ = V (1,1) := (hV1 1).symm
      _ = a 1 := (hVends 1).2
  let p : Path (a 0) (a 1) := ⟨a, rfl, rfl⟩
  let q : Path (a 0) (a 1) := ⟨b, h0, h1⟩
  let r : Path (a 0) (a 1) :=
    ⟨⟨fun s => b (ρ s), b.continuous.comp ρ.continuous⟩,
      by change b (ρ 0) = a 0; rw [hρ0, h0],
      by change b (ρ 1) = a 1; rw [hρ1, h1]⟩
  have hVhom : Path.Homotopy p r := {
    toFun := V
    map_zero_left := hV0
    map_one_left := hV1
    prop' := by
      intro t s hs
      rcases hs with hs | hs
      · subst s
        exact (hVends t).1
      · rw [Set.mem_singleton_iff] at hs
        subst s
        exact (hVends t).2
  }
  have hr : r = q.reparam ρ ρ.continuous hρ0 hρ1 := by
    ext s
    rfl
  refine ⟨h0, h1, ?_⟩
  change Path.Homotopic p q
  rw [hr] at hVhom
  exact (show Path.Homotopic p _ from ⟨hVhom⟩).trans
    (show Path.Homotopic q _ from
      ⟨Path.Homotopy.reparam q ρ ρ.continuous hρ0 hρ1⟩).symm

theorem regional_nonclean_has_interior_contact
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hnonclean : ¬ ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ s t : Interval,
      s ∈ Set.Ioo (0 : Interval) 1 ∧
      t ∈ Set.Ioo (0 : Interval) 1 ∧ a s = b t := by
  push Not at hnonclean
  obtain ⟨s,t,hst,hbad⟩ := hnonclean
  have hs0 : s ≠ 0 := by
    intro hs
    have ht : t = 0 := hb.injective (by calc
      b t = a s := hst.symm
      _ = a 0 := by rw [hs]
      _ = b 0 := h0.symm)
    exact hbad.1 hs ht
  have hs1 : s ≠ 1 := by
    intro hs
    have ht : t = 1 := hb.injective (by calc
      b t = a s := hst.symm
      _ = a 1 := by rw [hs]
      _ = b 1 := h1.symm)
    exact hbad.2 hs ht
  have ht0 : t ≠ 0 := by
    intro ht
    have hs : s = 0 := ha.injective (by calc
      a s = b t := hst
      _ = b 0 := by rw [ht]
      _ = a 0 := h0)
    exact hs0 hs
  have ht1 : t ≠ 1 := by
    intro ht
    have hs : s = 1 := ha.injective (by calc
      a s = b t := hst
      _ = b 1 := by rw [ht]
      _ = a 1 := h1)
    exact hs1 hs
  exact ⟨s,t,
    ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),
      lt_of_le_of_ne s.property.2 hs1⟩,
    ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
      lt_of_le_of_ne t.property.2 ht1⟩,
    hst⟩

/-- A finite sequence of independently certified local moves. -/
inductive RegionalMovieChain {S : Type*} [TopologicalSpace S]
    (F : Set S) : C(Interval, ↥F) → C(Interval, ↥F) → Prop where
  | singleton {a b} : RegionalMovie F a b → RegionalMovieChain F a b
  | append {a b c} : RegionalMovieChain F a b → RegionalMovie F b c →
      RegionalMovieChain F a c

theorem regionalMovieChain_to_movie {S : Type*} [TopologicalSpace S]
    {F : Set S} {a b : C(Interval, ↥F)}
    (h : RegionalMovieChain F a b) : RegionalMovie F a b := by
  induction h with
  | singleton h => exact h
  | append h hbc ih => exact regionalMovie_trans ih hbc

/-- A pointwise frontier-fixed ambient isotopy supplies the precise movie
    certificate needed to append a supported local cancellation. -/
theorem regionalMovie_of_ambient_isotopy
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (ha0Front : (a 0).val ∈ frontier F)
    (ha1Front : (a 1).val ∈ frontier F)
    (haClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (a s).val ∉ frontier F)
    (K : AmbientIsotopy ↥F)
    (hKfront : ∀ t y, y.val ∈ frontier F → K.map (t,y) = y)
    (hmove : K.finalMap '' Set.range a = Set.range b) :
    RegionalMovie F a b := by
  let c : C(Interval, ↥F) :=
    ⟨fun s => K.finalMap (a s),
      K.map.continuous.comp (continuous_const.prodMk a.continuous)⟩
  obtain ⟨e, he⟩ := K.homeomorphism_at 1
  have hcemb : Topology.IsEmbedding c := by
    have hemb : Topology.IsEmbedding (fun y => K.finalMap y) := by
      convert e.isEmbedding using 1
      funext y
      exact (he y).symm
    exact hemb.comp ha
  have hc0 : c 0 = a 0 := by
    change K.map (1,a 0) = a 0
    exact hKfront 1 (a 0) ha0Front
  have hc1 : c 1 = a 1 := by
    change K.map (1,a 1) = a 1
    exact hKfront 1 (a 1) ha1Front
  have hcClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (c s).val ∉ frontier F := by
    intro s hs hcs
    have hfix := hKfront 1 (c s) hcs
    have hinj : Function.Injective (fun y => K.finalMap y) := by
      intro y z hyz
      apply e.injective
      change K.map (1,y) = K.map (1,z) at hyz
      simpa only [he] using hyz
    have heq : c s = a s := hinj hfix
    exact haClear s hs (heq ▸ hcs)
  have hr : Set.range c = Set.range b := by
    calc
      Set.range c = K.finalMap '' Set.range a := by
        change Set.range (K.finalMap ∘ a) = K.finalMap '' Set.range a
        exact Set.range_comp K.finalMap a
      _ = Set.range b := hmove
  let V : C(Interval × Interval, ↥F) :=
    ⟨fun p => K.map (p.1,a p.2),
      K.map.continuous.comp (continuous_fst.prodMk
        (a.continuous.comp continuous_snd))⟩
  have hV : RegionalMovie F a c := by
    refine ⟨V, Homeomorph.refl Interval, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro s
      exact K.at_zero (a s)
    · intro s
      rfl
    · intro t
      obtain ⟨et, het⟩ := K.homeomorphism_at t
      have hemb : Topology.IsEmbedding (fun y => K.map (t,y)) := by
        convert et.isEmbedding using 1
        funext y
        exact (het y).symm
      exact hemb.comp ha
    · intro t
      exact ⟨hKfront t (a 0) ha0Front, hKfront t (a 1) ha1Front⟩
    · intro t s hs hvs
      have hfix := hKfront t (V (t,s)) hvs
      obtain ⟨et, het⟩ := K.homeomorphism_at t
      have heq : V (t,s) = a s := by
        apply et.injective
        change K.map (t,V (t,s)) = K.map (t,a s) at hfix
        simpa only [het] using hfix
      exact haClear s hs (heq ▸ hvs)
  have hcb : RegionalMovie F c b :=
    embedded_arcs_same_range_family c b hcemb hb
      (h0.trans hc0.symm) (h1.trans hc1.symm) hr hcClear
  exact regionalMovie_trans hV hcb

/-- The finite cancellation induction consumes one certified local move at a
    time. The local step is kept separate so its geometric construction can
    use an innermost F-bigon and a supported crosscut isotopy. -/
theorem regional_finite_contact_descent_to_clean
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval, ↥F))
    (hb : Topology.IsEmbedding b)
    (hb0 : b 0 = a 0) (hb1 : b 1 = a 1)
    (hbClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (b s).val ∉ frontier F)
    (hfinite : (Set.range a ∩ Set.range b).Finite)
    (step : ∀ q : C(Interval, ↥F),
      Topology.IsEmbedding q →
      q 0 = a 0 → q 1 = a 1 →
      (∀ s ∈ Set.Ioo (0 : Interval) 1,
        (q s).val ∉ frontier F) →
      (Set.range a ∩ Set.range q).Finite →
      (¬ ∀ s t, a s = q t →
        (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) →
      ∃ r : C(Interval, ↥F),
        Topology.IsEmbedding r ∧
        r 0 = a 0 ∧ r 1 = a 1 ∧
        (∀ s ∈ Set.Ioo (0 : Interval) 1,
          (r s).val ∉ frontier F) ∧
        (Set.range a ∩ Set.range r).Finite ∧
        RegionalMovie F q r ∧
        (Set.range a ∩ Set.range r).ncard <
          (Set.range a ∩ Set.range q).ncard) :
    ∃ q : C(Interval, ↥F),
      q 0 = a 0 ∧ q 1 = a 1 ∧
      (∀ s t, a s = q t →
        (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) ∧
      RegionalMovie F b q := by
  classical
  let μ : C(Interval, ↥F) → ℕ :=
    fun q => (Set.range a ∩ Set.range q).ncard
  have descend (q : C(Interval, ↥F))
      (hq : Topology.IsEmbedding q)
      (hq0 : q 0 = a 0) (hq1 : q 1 = a 1)
      (hqClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
        (q s).val ∉ frontier F)
      (hqFinite : (Set.range a ∩ Set.range q).Finite) :
      ∃ r : C(Interval, ↥F),
        r 0 = a 0 ∧ r 1 = a 1 ∧
        (∀ s t, a s = r t →
          (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) ∧
        RegionalMovie F q r := by
    induction q using (measure μ).wf.induction with
    | h q ih =>
      by_cases hclean : ∀ s t, a s = q t →
          (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)
      · exact ⟨q, hq0, hq1, hclean, regionalMovie_refl q hq hqClear⟩
      · obtain ⟨r, hr, hr0, hr1, hrClear, hrFinite, hqr, hdrop⟩ :=
          step q hq hq0 hq1 hqClear hqFinite hclean
        obtain ⟨z, hz0, hz1, hzClean, hrz⟩ :=
          ih r hdrop hr hr0 hr1 hrClear hrFinite
        exact ⟨z, hz0, hz1, hzClean, regionalMovie_trans hqr hrz⟩
  exact descend b hb hb0 hb1 hbClear hfinite

/-- Once positioning is realized by an embedded movie and each remaining
    contact admits a strict-drop embedded movie, the literal source pair has
    its full fixed-endpoint, frontier-clear embedded family. -/
theorem regional_family_of_positioning_and_contact_descent
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (a b q : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (_hb : Topology.IsEmbedding b)
    (hq : Topology.IsEmbedding q)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (haClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (a s).val ∉ frontier F)
    (hqClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (q s).val ∉ frontier F)
    (hhom : Path.Homotopic
      (⟨a, rfl, rfl⟩ : Path (a 0) (a 1))
      (⟨b, h0, h1⟩ : Path (a 0) (a 1)))
    (hposition : RegionalMovie F b q)
    (hfinite : (Set.range a ∩ Set.range q).Finite)
    (step : ∀ z : C(Interval, ↥F),
      Topology.IsEmbedding z →
      z 0 = a 0 → z 1 = a 1 →
      (∀ s ∈ Set.Ioo (0 : Interval) 1,
        (z s).val ∉ frontier F) →
      (Set.range a ∩ Set.range z).Finite →
      (¬ ∀ s t, a s = z t →
        (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) →
      ∃ r : C(Interval, ↥F),
        Topology.IsEmbedding r ∧
        r 0 = a 0 ∧ r 1 = a 1 ∧
        (∀ s ∈ Set.Ioo (0 : Interval) 1,
          (r s).val ∉ frontier F) ∧
        (Set.range a ∩ Set.range r).Finite ∧
        RegionalMovie F z r ∧
        (Set.range a ∩ Set.range r).ncard <
          (Set.range a ∩ Set.range z).ncard) :
    RegionalMovie F a b := by
  obtain ⟨hq0, hq1, hhomBq⟩ := regionalMovie_homotopic hposition
  obtain ⟨r, hr0, hr1, hrClean, hqr⟩ :=
    regional_finite_contact_descent_to_clean a q hq
      (hq0.trans h0) (hq1.trans h1) hqClear hfinite step
  obtain ⟨hr0', hr1', hhomQr⟩ := regionalMovie_homotopic hqr
  have hhomAr : Path.Homotopic
      (⟨a, rfl, rfl⟩ : Path (a 0) (a 1))
      (⟨r, hr0, hr1⟩ : Path (a 0) (a 1)) := by
    have hBq := Path.Homotopic.pathCast hhomBq h0.symm h1.symm
    have hQr := Path.Homotopic.pathCast hhomQr
      (hq0.trans h0).symm (hq1.trans h1).symm
    have hBq' : Path.Homotopic
        (⟨b,h0,h1⟩ : Path (a 0) (a 1))
        (⟨q,hq0.trans h0,hq1.trans h1⟩ : Path (a 0) (a 1)) := by
      convert hBq using 1 <;> ext s <;> rfl
    have hQr' : Path.Homotopic
        (⟨q,hq0.trans h0,hq1.trans h1⟩ : Path (a 0) (a 1))
        (⟨r,hr0,hr1⟩ : Path (a 0) (a 1)) := by
      convert hQr using 1 <;> ext s <;> rfl
    exact (hhom.trans hBq').trans hQr'
  have hrEmb : Topology.IsEmbedding r := by
    obtain ⟨W, ρ, hρ0, hρ1, hW0, hW1, hWemb, hWends, hWclear⟩ := hqr
    have he : Topology.IsEmbedding (fun s => r (ρ s)) := by
      convert hWemb 1 using 1
      funext s
      exact (hW1 s).symm
    have he' : Topology.IsEmbedding (fun s => r (ρ (ρ.symm s))) :=
      he.comp ρ.symm.isEmbedding
    simpa only [ρ.apply_symm_apply] using he'
  have hrClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (r s).val ∉ frontier F := by
    obtain ⟨W, ρ, hρ0, hρ1, hW0, hW1, hWemb, hWends, hWclear⟩ := hqr
    intro s hs
    have hs' : ρ.symm s ∈ Set.Ioo (0 : Interval) 1 := by
      have hn0 : ρ.symm s ≠ 0 := by
        intro he
        have : s = 0 := by calc
          s = ρ (ρ.symm s) := (ρ.apply_symm_apply s).symm
          _ = ρ 0 := by rw [he]
          _ = 0 := hρ0
        exact ne_of_gt hs.1 this
      have hn1 : ρ.symm s ≠ 1 := by
        intro he
        have : s = 1 := by calc
          s = ρ (ρ.symm s) := (ρ.apply_symm_apply s).symm
          _ = ρ 1 := by rw [he]
          _ = 1 := hρ1
        exact ne_of_lt hs.2 this
      exact ⟨lt_of_le_of_ne (ρ.symm s).property.1 (Ne.symm hn0),
        lt_of_le_of_ne (ρ.symm s).property.2 hn1⟩
    have hc := hWclear 1 (ρ.symm s) hs'
    rwa [hW1, ρ.apply_symm_apply] at hc
  have har : RegionalMovie F a r :=
    clean_homotopic_regional_arcs_embedded_family
      S g hg hS F a r ha hrEmb hr0 hr1 hrClean hhomAr haClear hrClear
  -- The remaining movie runs from `r` back to `b`.
  have hbr : RegionalMovie F b r := regionalMovie_trans hposition hqr
  exact regionalMovie_trans har (regionalMovie_symm hbr)

end RegionalEmbeddedFamily
