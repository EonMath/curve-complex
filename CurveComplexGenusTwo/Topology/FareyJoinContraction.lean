import CurveComplexGenusTwo.Topology.FareyJoinModel
import CurveComplexGenusTwo.Foundations.JoinFiniteSupport

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set unitInterval
open Filter

variable {V : Type*} [DecidableEq V]

private theorem continuousOn_finite_support_coordinates
    {V : Type*} [DecidableEq V]
    {A : Type*} [TopologicalSpace A]
    (K : AbstractSimplicialComplex V) (F : Finset V)
    (s : Set A) (f : A → RealizationPoint K)
    (hF : ∀ a ∈ s, f a ∈ finiteSupportLocus K F)
    (hcoord : ∀ w : F, ContinuousOn (fun a => (f a).weight w.1) s) :
    ContinuousOn f s := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_of_finite_support_and_coordinates K F
  · intro a
    exact hF a.1 a.2
  · intro w
    exact continuousOn_iff_continuous_domRestrict.mp (hcoord w)

private abbrev WeakFaceSimplex (K : AbstractSimplicialComplex V) :=
  Σ i : {tau : Finset V // tau ∈ K.faces}, FiniteSimplex i.1

private noncomputable def weakFaceSimplexMap
    (K : AbstractSimplicialComplex V) : WeakFaceSimplex K → RealizationPoint K :=
  fun p => faceInclusion K p.1.1 p.1.2 p.2

private theorem weakFaceSimplexMap_quotient
    (K : AbstractSimplicialComplex V) :
    Topology.IsQuotientMap (weakFaceSimplexMap K) := by
  refine ⟨⟨?_⟩, ?_⟩
  · apply TopologicalSpace.ext
    funext U
    apply propext
    change IsOpen U ↔ IsOpen ((weakFaceSimplexMap K) ⁻¹' U)
    constructor
    · intro hU
      exact isOpen_sigma_iff.mpr (fun i => hU i.1 i.2)
    · intro hU tau hτ
      exact isOpen_sigma_iff.mp hU ⟨tau, hτ⟩
  · intro x
    obtain ⟨face, hface, hzero, hsum⟩ := x.liesInFace
    let y : FiniteSimplex face := ⟨fun v => x.weight v, (fun v => x.nonneg v), by
      simpa only [Finset.sum_attach, Finset.univ_eq_attach] using hsum⟩
    refine ⟨⟨⟨face, hface⟩, y⟩, ?_⟩
    apply RealizationPoint.ext
    funext v
    by_cases hv : v ∈ face
    · simp [weakFaceSimplexMap, faceInclusion, y, hv]
    · simp [weakFaceSimplexMap, faceInclusion, y, hv, hzero v hv]

/-- Joint continuity into a weak realization is tested on finite simplex
charts crossed with the compact interval. This uses quotient×I, not an
assumption that products preserve arbitrary weak topologies. -/
theorem continuous_iff_continuous_on_face_time_charts
    {Y : Type*} [TopologicalSpace Y]
    (K : AbstractSimplicialComplex V)
    (f : I × RealizationPoint K → Y) :
    Continuous f ↔
      ∀ tau : Finset V, ∀ hτ : tau ∈ K.faces,
        Continuous (fun p : I × FiniteSimplex tau =>
          f (p.1, faceInclusion K tau hτ p.2)) := by
  constructor
  · intro hf tau hτ
    exact hf.comp (continuous_fst.prodMk
      (continuous_faceInclusion K tau hτ |>.comp continuous_snd))
  · intro hf
    apply (weakFaceSimplexMap_quotient K).continuous_lift_prod_right
    have hg : Continuous (fun p : I × WeakFaceSimplex K =>
        f (p.1, weakFaceSimplexMap K p.2)) := by
      let g : (Σ i : {tau : Finset V // tau ∈ K.faces},
          FiniteSimplex i.1 × I) → Y := fun p =>
        f (p.2.2, faceInclusion K p.1.1 p.1.2 p.2.1)
      have hgc : Continuous g := continuous_sigma_iff.mpr (by
        intro i
        exact (hf i.1 i.2).comp continuous_swap)
      exact hgc.comp (Homeomorph.sigmaProdDistrib (Y := I)).continuous
        |>.comp continuous_swap
    exact hg

private def fareyJoinWeight
    (t : I) (p q : RealizationPoint fareyFlagComplex) :
    Sum FareySlope FareySlope → ℝ
  | .inl a => (1 - (t : ℝ)) * p.weight a
  | .inr b => (t : ℝ) * q.weight b

/-- The pointwise barycentric join map. Its topology is addressed separately;
the definition itself only uses finite face supports and the exact join-face
criterion. -/
noncomputable def fareyJoinBlend
    (t : I) (p q : RealizationPoint fareyFlagComplex) :
    RealizationPoint fareyJoinComplex := by
  classical
  refine ⟨fareyJoinWeight t p q, ?_, ?_⟩
  · intro s
    cases s with
    | inl a =>
        exact mul_nonneg (sub_nonneg.mpr t.2.2) (p.nonneg a)
    | inr b =>
        exact mul_nonneg t.2.1 (q.nonneg b)
  · obtain ⟨faceA, hfaceA, hpzero, hpsum⟩ := p.liesInFace
    obtain ⟨faceB, hfaceB, hqzero, hqsum⟩ := q.liesInFace
    let faceJ := faceA.image Sum.inl ∪ faceB.image Sum.inr
    have hfaceJ : faceJ ∈ fareyJoinComplex.faces := by
      change faceJ.Nonempty ∧ FareyJoinFace faceJ
      constructor
      · exact Finset.Nonempty.inl (Finset.image_nonempty.mpr
          (fareyFlagComplex.isRelLowerSet_faces hfaceA).1)
      · exact (fareyJoinFace_image_union_iff faceA faceB).2 ⟨hfaceA.2, hfaceB.2⟩
    refine ⟨faceJ, hfaceJ, ?_, ?_⟩
    · intro s hs
      cases s with
      | inl a =>
          have ha : a ∉ faceA := by
            intro ha
            exact hs (Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
          exact by simp [fareyJoinWeight, hpzero a ha]
      | inr b =>
          have hb : b ∉ faceB := by
            intro hb
            exact hs (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
          exact by simp [fareyJoinWeight, hqzero b hb]
    · have hdis : Disjoint (faceA.image Sum.inl) (faceB.image Sum.inr) := by
        apply Finset.disjoint_left.mpr
        intro a ha hb
        rcases Finset.mem_image.mp ha with ⟨a', _, rfl⟩
        simp at hb
      calc
        ∑ s ∈ faceJ, fareyJoinWeight t p q s =
            (∑ s ∈ faceA.image Sum.inl, fareyJoinWeight t p q s) +
              (∑ s ∈ faceB.image Sum.inr, fareyJoinWeight t p q s) := by
              exact Finset.sum_union hdis
        _ = (1 - (t : ℝ)) * (∑ a ∈ faceA, p.weight a) +
              (t : ℝ) * (∑ b ∈ faceB, q.weight b) := by
              rw [Finset.sum_image (Sum.inl_injective.injOn),
                Finset.sum_image (Sum.inr_injective.injOn)]
              simp only [fareyJoinWeight]
              rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ = 1 := by rw [hpsum, hqsum]; ring

@[simp] theorem fareyJoinBlend_weight_inl
    (t : I) (p q : RealizationPoint fareyFlagComplex) (a : FareySlope) :
    (fareyJoinBlend t p q).weight (.inl a) =
      (1 - (t : ℝ)) * p.weight a := rfl

@[simp] theorem fareyJoinBlend_weight_inr
    (t : I) (p q : RealizationPoint fareyFlagComplex) (b : FareySlope) :
    (fareyJoinBlend t p q).weight (.inr b) =
      (t : ℝ) * q.weight b := rfl

/-- The join blend is continuous on any domain where both factor maps have
uniformly finite vertex support. In particular this applies to compact
finite-face-times-time domains after `compact_realization_has_finite_support`. -/
theorem fareyJoinBlend_continuous_of_finite_support
    {A : Type*} [TopologicalSpace A]
    (t : A → I)
    (p q : A → RealizationPoint fareyFlagComplex)
    (ht : Continuous t) (hp : Continuous p) (hq : Continuous q)
    (F G : Finset FareySlope)
    (hFp : ∀ a, supportFinset fareyFlagComplex (p a) ⊆ F)
    (hGq : ∀ a, supportFinset fareyFlagComplex (q a) ⊆ G) :
    Continuous (fun a => fareyJoinBlend (t a) (p a) (q a)) := by
  classical
  let J : Finset (Sum FareySlope FareySlope) :=
    F.image Sum.inl ∪ G.image Sum.inr
  apply continuous_of_finite_support_and_coordinates fareyJoinComplex J
  · intro a
    change supportFinset fareyJoinComplex
      (fareyJoinBlend (t a) (p a) (q a)) ⊆ J
    intro s hs
    cases s with
    | inl u =>
        have hu : u ∈ supportFinset fareyFlagComplex (p a) := by
          by_contra hnot
          have hz : (p a).weight u = 0 := by
            by_contra hn
            exact hnot ((mem_supportFinset_iff fareyFlagComplex (p a) u).2 hn)
          exact ((mem_supportFinset_iff fareyJoinComplex _ _).1 hs)
            (by simp [hz])
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨u, hFp a hu, rfl⟩)
    | inr u =>
        have hu : u ∈ supportFinset fareyFlagComplex (q a) := by
          by_contra hnot
          have hz : (q a).weight u = 0 := by
            by_contra hn
            exact hnot ((mem_supportFinset_iff fareyFlagComplex (q a) u).2 hn)
          exact ((mem_supportFinset_iff fareyJoinComplex _ _).1 hs)
            (by simp [hz])
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨u, hGq a hu, rfl⟩)
  · intro s
    cases s.1 with
    | inl u =>
        simp only [fareyJoinBlend_weight_inl]
        exact (continuous_const.sub (continuous_subtype_val.comp ht)).mul
          ((continuous_weight fareyFlagComplex u).comp hp)
    | inr u =>
        simp only [fareyJoinBlend_weight_inr]
        exact (continuous_subtype_val.comp ht).mul
          ((continuous_weight fareyFlagComplex u).comp hq)

/-- A compact parameter space supplies the two support bounds automatically.
This statement uses the actual weak realization on the target. -/
theorem fareyJoinBlend_continuous_of_compact_domain
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (t : A → I)
    (p q : A → RealizationPoint fareyFlagComplex)
    (ht : Continuous t) (hp : Continuous p) (hq : Continuous q) :
    Continuous (fun a => fareyJoinBlend (t a) (p a) (q a)) := by
  obtain ⟨F, hF⟩ := compact_realization_has_finite_support
    fareyFlagComplex (Set.range p) (isCompact_range hp)
  obtain ⟨G, hG⟩ := compact_realization_has_finite_support
    fareyFlagComplex (Set.range q) (isCompact_range hq)
  apply fareyJoinBlend_continuous_of_finite_support t p q ht hp hq F G
  · intro a
    exact hF (p a) ⟨a, rfl⟩
  · intro a
    exact hG (q a) ⟨a, rfl⟩

/-- Multiplying a normalized factor coordinate by its total mass removes the
apparent discontinuity at zero mass. This is the boundary-continuity step
needed when a join point has no vertices on one side. -/
theorem weighted_farey_coordinate_continuous
    {A : Type*} [TopologicalSpace A]
    (m : A → ℝ) (z : A → RealizationPoint fareyFlagComplex)
    (hm : Continuous m) (hm0 : ∀ a, 0 ≤ m a)
    (hz : ContinuousOn z {a | m a ≠ 0})
    (v : FareySlope) :
    Continuous (fun a => m a * (z a).weight v) := by
  rw [continuous_iff_continuousAt]
  intro a
  by_cases ha : m a = 0
  · have hlow : (fun _ : A => (0 : ℝ)) ≤
        (fun b => m b * (z b).weight v) := by
      intro b
      exact mul_nonneg (hm0 b) ((z b).nonneg v)
    have hhigh : (fun b => m b * (z b).weight v) ≤ m := by
      intro b
      have hle := realization_weight_le_one fareyFlagComplex (z b) v
      nlinarith [hm0 b]
    have hmAt : Tendsto m (nhds a) (nhds (0 : ℝ)) := by
      simpa [ContinuousAt, ha] using (hm.continuousAt (x := a))
    have hg : Tendsto (fun b => m b * (z b).weight v)
        (nhds a) (nhds (0 : ℝ)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hmAt hlow hhigh
    change Tendsto (fun b => m b * (z b).weight v)
      (nhds a) (nhds (m a * (z a).weight v))
    simpa [ha] using hg
  · have hopen : IsOpen {b : A | m b ≠ 0} :=
      by simpa [Set.compl_ofPred] using
        (isClosed_eq hm continuous_const).isOpen_compl
    have hzAt : ContinuousAt z a :=
      hz.continuousAt (hopen.mem_nhds ha)
    exact hm.continuousAt.mul
      ((continuous_weight fareyFlagComplex v).continuousAt.comp hzAt)

private theorem sum_supportFinset_eq_one
    {V : Type*} [DecidableEq V]
    (K : AbstractSimplicialComplex V) (x : RealizationPoint K) :
    ∑ v ∈ supportFinset K x, x.weight v = 1 := by
  classical
  obtain ⟨face, hface, hzero, hsum⟩ := x.liesInFace
  have hsub : supportFinset K x ⊆ face := by
    intro v hv
    by_contra hnot
    exact ((mem_supportFinset_iff K x v).1 hv) (hzero v hnot)
  have hsum' : (∑ v ∈ supportFinset K x, x.weight v) =
      ∑ v ∈ face, x.weight v := by
    apply Finset.sum_subset hsub
    intro v hv hnot
    by_contra hn
    exact hnot ((mem_supportFinset_iff K x v).2 hn)
  exact hsum'.trans hsum

noncomputable def fareyJoinLeftMass (x : RealizationPoint fareyJoinComplex) : ℝ :=
  ∑ a ∈ fareyJoinLeft (supportFinset fareyJoinComplex x),
    x.weight (.inl a)

noncomputable def fareyJoinRightMass (x : RealizationPoint fareyJoinComplex) : ℝ :=
  ∑ b ∈ fareyJoinRight (supportFinset fareyJoinComplex x),
    x.weight (.inr b)

theorem fareyJoinMass_sum_one (x : RealizationPoint fareyJoinComplex) :
    fareyJoinLeftMass x + fareyJoinRightMass x = 1 := by
  classical
  let support := supportFinset fareyJoinComplex x
  have hparts := fareyJoin_parts support
  have hdis : Disjoint
      ((fareyJoinLeft support).image Sum.inl)
      ((fareyJoinRight support).image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    rcases Finset.mem_image.mp hs with ⟨a, _, rfl⟩
    simp at ht
  have hsum := sum_supportFinset_eq_one fareyJoinComplex x
  change (∑ v ∈ support, x.weight v) = 1 at hsum
  rw [← hparts, Finset.sum_union hdis] at hsum
  rw [Finset.sum_image (Sum.inl_injective.injOn),
    Finset.sum_image (Sum.inr_injective.injOn)] at hsum
  exact hsum

private theorem fareyJoinLeftMass_of_support_subset
    (x : RealizationPoint fareyJoinComplex)
    (face : Finset (Sum FareySlope FareySlope))
    (hsub : supportFinset fareyJoinComplex x ⊆ face) :
    fareyJoinLeftMass x =
      ∑ a ∈ fareyJoinLeft face, x.weight (.inl a) := by
  classical
  apply Finset.sum_subset
  · intro a ha
    exact (mem_fareyJoinLeft_iff face a).2
      (hsub ((mem_fareyJoinLeft_iff _ a).1 ha))
  · intro a ha hnot
    have hz : x.weight (.inl a) = 0 := by
      by_contra hn
      exact hnot ((mem_fareyJoinLeft_iff _ a).2
        ((mem_supportFinset_iff fareyJoinComplex x (.inl a)).2 hn))
    exact hz

theorem fareyJoinLeftMass_continuous :
    Continuous fareyJoinLeftMass := by
  apply (continuous_iff_continuous_on_faces fareyJoinComplex
    fareyJoinLeftMass).2
  intro face hface
  have hchart (u : FiniteSimplex face) :
      supportFinset fareyJoinComplex
        (faceInclusion fareyJoinComplex face hface u) ⊆ face := by
    intro s hs
    by_contra hnot
    exact ((mem_supportFinset_iff fareyJoinComplex _ s).1 hs)
      (by simp [faceInclusion, hnot])
  have heq : fareyJoinLeftMass ∘
      faceInclusion fareyJoinComplex face hface =
      fun u => ∑ a ∈ fareyJoinLeft face,
        (faceInclusion fareyJoinComplex face hface u).weight (.inl a) := by
    funext u
    exact fareyJoinLeftMass_of_support_subset _ face (hchart u)
  rw [heq]
  apply continuous_finsetSum
  intro a ha
  exact (continuous_weight fareyJoinComplex (.inl a)).comp
    (continuous_faceInclusion fareyJoinComplex face hface)

private theorem fareyJoinRightMass_of_support_subset
    (x : RealizationPoint fareyJoinComplex)
    (face : Finset (Sum FareySlope FareySlope))
    (hsub : supportFinset fareyJoinComplex x ⊆ face) :
    fareyJoinRightMass x =
      ∑ b ∈ fareyJoinRight face, x.weight (.inr b) := by
  classical
  apply Finset.sum_subset
  · intro b hb
    exact (mem_fareyJoinRight_iff face b).2
      (hsub ((mem_fareyJoinRight_iff _ b).1 hb))
  · intro b hb hnot
    have hz : x.weight (.inr b) = 0 := by
      by_contra hn
      exact hnot ((mem_fareyJoinRight_iff _ b).2
        ((mem_supportFinset_iff fareyJoinComplex x (.inr b)).2 hn))
    exact hz

theorem fareyJoinRightMass_continuous :
    Continuous fareyJoinRightMass := by
  apply (continuous_iff_continuous_on_faces fareyJoinComplex
    fareyJoinRightMass).2
  intro face hface
  have hchart (u : FiniteSimplex face) :
      supportFinset fareyJoinComplex
        (faceInclusion fareyJoinComplex face hface u) ⊆ face := by
    intro s hs
    by_contra hnot
    exact ((mem_supportFinset_iff fareyJoinComplex _ s).1 hs)
      (by simp [faceInclusion, hnot])
  have heq : fareyJoinRightMass ∘
      faceInclusion fareyJoinComplex face hface =
      fun u => ∑ b ∈ fareyJoinRight face,
        (faceInclusion fareyJoinComplex face hface u).weight (.inr b) := by
    funext u
    exact fareyJoinRightMass_of_support_subset _ face (hchart u)
  rw [heq]
  apply continuous_finsetSum
  intro b hb
  exact (continuous_weight fareyJoinComplex (.inr b)).comp
    (continuous_faceInclusion fareyJoinComplex face hface)

theorem fareyJoinLeftMass_nonneg
    (x : RealizationPoint fareyJoinComplex) : 0 ≤ fareyJoinLeftMass x := by
  unfold fareyJoinLeftMass
  apply Finset.sum_nonneg
  intro a ha
  exact x.nonneg (.inl a)

theorem fareyJoinRightMass_nonneg
    (x : RealizationPoint fareyJoinComplex) : 0 ≤ fareyJoinRightMass x := by
  unfold fareyJoinRightMass
  apply Finset.sum_nonneg
  intro b hb
  exact x.nonneg (.inr b)

theorem fareyJoinLeftMass_le_one
    (x : RealizationPoint fareyJoinComplex) : fareyJoinLeftMass x ≤ 1 := by
  rw [← fareyJoinMass_sum_one x]
  linarith [fareyJoinRightMass_nonneg x]

theorem fareyJoinRightMass_le_one
    (x : RealizationPoint fareyJoinComplex) : fareyJoinRightMass x ≤ 1 := by
  rw [← fareyJoinMass_sum_one x]
  linarith [fareyJoinLeftMass_nonneg x]

theorem fareyJoinLeftMass_pos_iff
    (x : RealizationPoint fareyJoinComplex) :
    0 < fareyJoinLeftMass x ↔
      (fareyJoinLeft (supportFinset fareyJoinComplex x)).Nonempty := by
  classical
  constructor
  · intro h
    by_contra he
    have hempty := Finset.not_nonempty_iff_eq_empty.mp he
    simp [fareyJoinLeftMass, hempty] at h
  · intro h
    obtain ⟨a, ha⟩ := h
    have hpos : 0 < x.weight (.inl a) :=
      (mem_supportFinset_iff_pos fareyJoinComplex x (.inl a)).mp
        ((mem_fareyJoinLeft_iff _ a).mp ha)
    have hterm : x.weight (.inl a) ≤ fareyJoinLeftMass x := by
      unfold fareyJoinLeftMass
      exact Finset.single_le_sum (fun b hb => x.nonneg (.inl b)) ha
    exact lt_of_lt_of_le hpos hterm

theorem fareyJoinRightMass_pos_iff
    (x : RealizationPoint fareyJoinComplex) :
    0 < fareyJoinRightMass x ↔
      (fareyJoinRight (supportFinset fareyJoinComplex x)).Nonempty := by
  classical
  constructor
  · intro h
    by_contra he
    have hempty := Finset.not_nonempty_iff_eq_empty.mp he
    simp [fareyJoinRightMass, hempty] at h
  · intro h
    obtain ⟨b, hb⟩ := h
    have hpos : 0 < x.weight (.inr b) :=
      (mem_supportFinset_iff_pos fareyJoinComplex x (.inr b)).mp
        ((mem_fareyJoinRight_iff _ b).mp hb)
    have hterm : x.weight (.inr b) ≤ fareyJoinRightMass x := by
      unfold fareyJoinRightMass
      exact Finset.single_le_sum (fun a ha => x.nonneg (.inr a)) hb
    exact lt_of_lt_of_le hpos hterm

private theorem fareyFace_of_support
    (p : RealizationPoint fareyFlagComplex) :
    FareyFace (supportFinset fareyFlagComplex p) :=
  ((mem_fareyFlagComplex_iff (supportFinset fareyFlagComplex p)).mp
    (supportFinset_mem_faces fareyFlagComplex p)).2

private theorem fareyJoinFace_of_factors
    (p q : RealizationPoint fareyFlagComplex) :
    FareyJoinFace
      ((supportFinset fareyFlagComplex p).image Sum.inl ∪
        (supportFinset fareyFlagComplex q).image Sum.inr) :=
  (fareyJoinFace_image_union_iff _ _).2
    ⟨fareyFace_of_support p, fareyFace_of_support q⟩

private theorem fareyJoinFace_of_support
    (x : RealizationPoint fareyJoinComplex) :
    FareyJoinFace (supportFinset fareyJoinComplex x) :=
  ((mem_fareyJoinComplex_iff (supportFinset fareyJoinComplex x)).mp
    (supportFinset_mem_faces fareyJoinComplex x)).2

noncomputable def fareyJoinNormalizeLeft
    (x : RealizationPoint fareyJoinComplex)
    (hm : 0 < fareyJoinLeftMass x) : RealizationPoint fareyFlagComplex := by
  classical
  let face := fareyJoinLeft (supportFinset fareyJoinComplex x)
  have hface_ne : face.Nonempty :=
    fareyJoinLeftMass_pos_iff x |>.mp hm
  have hface : FareyFace face := by
    exact ((fareyJoinFace_iff_parts
      (supportFinset fareyJoinComplex x)).mp
        (fareyJoinFace_of_support x)).1
  refine ⟨fun a => x.weight (.inl a) / fareyJoinLeftMass x,
    ?_, ?_⟩
  · intro a
    exact div_nonneg (x.nonneg (.inl a)) (le_of_lt hm)
  · refine ⟨face, ?_, ?_, ?_⟩
    · exact ⟨hface_ne, hface⟩
    · intro a ha
      have hnot : .inl a ∉ supportFinset fareyJoinComplex x := by
        intro hin
        exact ha ((mem_fareyJoinLeft_iff _ a).2 hin)
      have hz : x.weight (.inl a) = 0 := by
        by_contra hn
        exact hnot ((mem_supportFinset_iff fareyJoinComplex x (.inl a)).2 hn)
      simp [hz]
    · have hsum : ∑ a ∈ face, x.weight (.inl a) =
          fareyJoinLeftMass x := rfl
      rw [← Finset.sum_div]
      rw [hsum, div_self (ne_of_gt hm)]

@[simp] theorem fareyJoinNormalizeLeft_weight
    (x : RealizationPoint fareyJoinComplex)
    (hm : 0 < fareyJoinLeftMass x) (a : FareySlope) :
    (fareyJoinNormalizeLeft x hm).weight a =
      x.weight (.inl a) / fareyJoinLeftMass x := rfl

theorem fareyJoinNormalizeLeft_support_subset
    (x : RealizationPoint fareyJoinComplex)
    (hm : 0 < fareyJoinLeftMass x) :
    supportFinset fareyFlagComplex (fareyJoinNormalizeLeft x hm) ⊆
      fareyJoinLeft (supportFinset fareyJoinComplex x) := by
  intro a ha
  by_contra hnot
  have hz : x.weight (.inl a) = 0 := by
    by_contra hn
    exact hnot ((mem_fareyJoinLeft_iff _ a).2
      ((mem_supportFinset_iff fareyJoinComplex x (.inl a)).2 hn))
  have hz' : (fareyJoinNormalizeLeft x hm).weight a = 0 := by
    simp [hz]
  exact ((mem_supportFinset_iff fareyFlagComplex
    (fareyJoinNormalizeLeft x hm) a).1 ha) hz'

theorem fareyJoinNormalizeLeft_continuous_of_faceBound
    {A : Type*} [TopologicalSpace A]
    (x : A → RealizationPoint fareyJoinComplex)
    (face : Finset (Sum FareySlope FareySlope))
    (hx : Continuous x)
    (hface : ∀ a, supportFinset fareyJoinComplex (x a) ⊆ face)
    (hm : ∀ a, 0 < fareyJoinLeftMass (x a)) :
    Continuous (fun a => fareyJoinNormalizeLeft (x a) (hm a)) := by
  classical
  let F := fareyJoinLeft face
  apply continuous_of_finite_support_and_coordinates fareyFlagComplex F
  · intro a
    change supportFinset fareyFlagComplex
      (fareyJoinNormalizeLeft (x a) (hm a)) ⊆ F
    exact (fareyJoinNormalizeLeft_support_subset (x a) (hm a)).trans
      (by intro u hu
          exact (mem_fareyJoinLeft_iff face u).2
            (hface a ((mem_fareyJoinLeft_iff _ u).1 hu)))
  · intro u
    have hnum : Continuous (fun a => (x a).weight (.inl u.1)) :=
      (continuous_weight fareyJoinComplex (.inl u.1)).comp hx
    have hden : Continuous (fun a => fareyJoinLeftMass (x a)) :=
      fareyJoinLeftMass_continuous.comp hx
    have heq : (fun a => (fareyJoinNormalizeLeft (x a) (hm a)).weight u.1) =
        fun a => (x a).weight (.inl u.1) / fareyJoinLeftMass (x a) := by
      funext a
      rfl
    rw [heq]
    exact hnum.div hden (fun a => ne_of_gt (hm a))

theorem fareyJoinLeftWeight_zero_of_mass_zero
    (x : RealizationPoint fareyJoinComplex)
    (hm : fareyJoinLeftMass x = 0) (a : FareySlope) :
    x.weight (.inl a) = 0 := by
  classical
  by_cases hmem : a ∈ fareyJoinLeft
      (supportFinset fareyJoinComplex x)
  · have hle : x.weight (.inl a) ≤ fareyJoinLeftMass x := by
      unfold fareyJoinLeftMass
      exact Finset.single_le_sum (fun b hb => x.nonneg (.inl b)) hmem
    exact le_antisymm (hm ▸ hle) (x.nonneg (.inl a))
  · by_contra hn
    exact hmem ((mem_fareyJoinLeft_iff _ a).2
      ((mem_supportFinset_iff fareyJoinComplex x (.inl a)).2 hn))

/-- Replace the normalized left factor of a join point along a supplied
factor homotopy, leaving the right factor and both total masses fixed. At a
zero left mass the point is already entirely on the right and is unchanged. -/
noncomputable def fareyJoinReplaceLeft
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base))
    (t : I) (x : RealizationPoint fareyJoinComplex) :
    RealizationPoint fareyJoinComplex := by
  classical
  by_cases hm : 0 < fareyJoinLeftMass x
  · let p := H (t, fareyJoinNormalizeLeft x hm)
    let qWeight (s : Sum FareySlope FareySlope) : ℝ :=
      match s with
      | .inl a => fareyJoinLeftMass x * p.weight a
      | .inr b => x.weight (.inr b)
    refine ⟨qWeight, ?_, ?_⟩
    · intro s
      cases s with
      | inl a => exact mul_nonneg (le_of_lt hm) (p.nonneg a)
      | inr b => exact x.nonneg (.inr b)
    · let left := supportFinset fareyFlagComplex p
      let right := fareyJoinRight (supportFinset fareyJoinComplex x)
      let face := left.image Sum.inl ∪ right.image Sum.inr
      have hface : face ∈ fareyJoinComplex.faces := by
        change face.Nonempty ∧ FareyJoinFace face
        constructor
        · exact Finset.Nonempty.inl (Finset.image_nonempty.mpr
            (supportFinset_nonempty fareyFlagComplex p))
        · exact (fareyJoinFace_image_union_iff left right).2
            ⟨fareyFace_of_support p,
              (fareyJoinFace_iff_parts
                (supportFinset fareyJoinComplex x)).mp
                  (fareyJoinFace_of_support x) |>.2⟩
      refine ⟨face, hface, ?_, ?_⟩
      · intro s hs
        cases s with
        | inl a =>
            have ha : a ∉ left := by
              intro ha
              exact hs (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
            have hz : p.weight a = 0 := by
              by_contra hn
              exact ha ((mem_supportFinset_iff fareyFlagComplex p a).2 hn)
            simp [qWeight, hz]
        | inr b =>
            have hb : b ∉ right := by
              intro hb
              exact hs (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
            have hb' : .inr b ∉ supportFinset fareyJoinComplex x := by
              intro hin
              exact hb ((mem_fareyJoinRight_iff _ b).2 hin)
            have hz : x.weight (.inr b) = 0 := by
              by_contra hn
              exact hb' ((mem_supportFinset_iff fareyJoinComplex x (.inr b)).2 hn)
            simp [qWeight, hz]
      · have hdis : Disjoint (left.image Sum.inl) (right.image Sum.inr) := by
          apply Finset.disjoint_left.mpr
          intro s hs ht
          rcases Finset.mem_image.mp hs with ⟨a, _, rfl⟩
          simp at ht
        have hleft : ∑ a ∈ left, qWeight (.inl a) =
            fareyJoinLeftMass x := by
          simp only [qWeight]
          rw [← Finset.mul_sum, sum_supportFinset_eq_one]
          ring
        have hright : ∑ b ∈ right, qWeight (.inr b) =
            fareyJoinRightMass x := by
          simp only [qWeight]
          unfold fareyJoinRightMass
          apply Finset.sum_subset
          · intro b hb
            exact (mem_fareyJoinRight_iff _ b).2
              ((mem_fareyJoinRight_iff _ b).1 hb)
          · intro b hb hnot
            have hz : x.weight (.inr b) = 0 := by
              by_contra hn
              exact hnot ((mem_fareyJoinRight_iff _ b).2
                ((mem_supportFinset_iff fareyJoinComplex x (.inr b)).2 hn))
            exact hz
        have hsum : ∑ s ∈ face, qWeight s =
            (∑ a ∈ left, qWeight (.inl a)) +
              (∑ b ∈ right, qWeight (.inr b)) := by
          rw [show face = left.image Sum.inl ∪ right.image Sum.inr from rfl]
          rw [Finset.sum_union hdis]
          rw [Finset.sum_image (Sum.inl_injective.injOn),
            Finset.sum_image (Sum.inr_injective.injOn)]
        rw [hsum, hleft, hright, fareyJoinMass_sum_one]
  · exact x

theorem fareyJoinReplaceLeft_weight_inl_of_pos
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base))
    (t : I) (x : RealizationPoint fareyJoinComplex)
    (hm : 0 < fareyJoinLeftMass x) (a : FareySlope) :
    (fareyJoinReplaceLeft base H t x).weight (.inl a) =
      fareyJoinLeftMass x *
        (H (t, fareyJoinNormalizeLeft x hm)).weight a := by
  simp [fareyJoinReplaceLeft, hm]

theorem fareyJoinReplaceLeft_weight_inr_of_pos
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base))
    (t : I) (x : RealizationPoint fareyJoinComplex)
    (hm : 0 < fareyJoinLeftMass x) (b : FareySlope) :
    (fareyJoinReplaceLeft base H t x).weight (.inr b) =
      x.weight (.inr b) := by
  simp [fareyJoinReplaceLeft, hm]


theorem fareyJoinReplaceLeft_zero
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base))
    (x : RealizationPoint fareyJoinComplex) :
    fareyJoinReplaceLeft base H ⟨0, by norm_num⟩ x = x := by
  classical
  by_cases hm : 0 < fareyJoinLeftMass x
  · apply RealizationPoint.ext
    funext s
    cases s with
    | inl a =>
        have hH := H.map_zero_left (fareyJoinNormalizeLeft x hm)
        simp only [fareyJoinReplaceLeft, dite_eq_left hm]
        have hH' : H (⟨0, by norm_num⟩,
            fareyJoinNormalizeLeft x hm) =
              fareyJoinNormalizeLeft x hm := by simp
        rw [hH']
        simp only [fareyJoinNormalizeLeft_weight]
        field_simp [ne_of_gt hm]
    | inr b =>
        simp [fareyJoinReplaceLeft, hm]
  · have hzero : fareyJoinLeftMass x = 0 := by
      apply le_antisymm
      · exact le_of_not_gt hm
      · exact fareyJoinLeftMass_nonneg x
    simp [fareyJoinReplaceLeft, hzero]

/-- A point with left factor already equal to `base` is contracted by
transferring all remaining right mass onto that basepoint. -/
noncomputable def fareyJoinCollapseRight
    (base : RealizationPoint fareyFlagComplex)
    (t : I) (x : RealizationPoint fareyJoinComplex) :
    RealizationPoint fareyJoinComplex := by
  classical
  let leftMass := fareyJoinLeftMass x
  let rightMass := fareyJoinRightMass x
  let w : Sum FareySlope FareySlope → ℝ := fun s =>
    match s with
    | .inl a => (leftMass + (t : ℝ) * rightMass) * base.weight a
    | .inr b => (1 - (t : ℝ)) * x.weight (.inr b)
  refine ⟨w, ?_, ?_⟩
  · intro s
    cases s with
    | inl a =>
        apply mul_nonneg
        · exact add_nonneg (fareyJoinLeftMass_nonneg x)
            (mul_nonneg t.2.1 (fareyJoinRightMass_nonneg x))
        · exact base.nonneg a
    | inr b =>
        exact mul_nonneg (sub_nonneg.mpr t.2.2) (x.nonneg (.inr b))
  · let left := supportFinset fareyFlagComplex base
    let right := fareyJoinRight (supportFinset fareyJoinComplex x)
    let face := left.image Sum.inl ∪ right.image Sum.inr
    have hface : face ∈ fareyJoinComplex.faces := by
      change face.Nonempty ∧ FareyJoinFace face
      constructor
      · exact Finset.Nonempty.inl (Finset.image_nonempty.mpr
          (supportFinset_nonempty fareyFlagComplex base))
      · exact (fareyJoinFace_image_union_iff left right).2
          ⟨fareyFace_of_support base,
            (fareyJoinFace_iff_parts
              (supportFinset fareyJoinComplex x)).mp
                (fareyJoinFace_of_support x) |>.2⟩
    refine ⟨face, hface, ?_, ?_⟩
    · intro s hs
      cases s with
      | inl a =>
          have ha : a ∉ left := by
            intro ha
            exact hs (Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
          have hz : base.weight a = 0 := by
            by_contra hn
            exact ha ((mem_supportFinset_iff fareyFlagComplex base a).2 hn)
          simp [w, hz]
      | inr b =>
          have hb : b ∉ right := by
            intro hb
            exact hs (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
          have hb' : .inr b ∉ supportFinset fareyJoinComplex x := by
            intro hin
            exact hb ((mem_fareyJoinRight_iff _ b).2 hin)
          have hz : x.weight (.inr b) = 0 := by
            by_contra hn
            exact hb' ((mem_supportFinset_iff fareyJoinComplex x (.inr b)).2 hn)
          simp [w, hz]
    · have hdis : Disjoint (left.image Sum.inl) (right.image Sum.inr) := by
        apply Finset.disjoint_left.mpr
        intro s hs ht
        rcases Finset.mem_image.mp hs with ⟨a, _, rfl⟩
        simp at ht
      have hleft : ∑ a ∈ left, w (.inl a) =
          (leftMass + (t : ℝ) * rightMass) := by
        simp only [w]
        rw [← Finset.mul_sum, sum_supportFinset_eq_one]
        ring
      have hright : ∑ b ∈ right, w (.inr b) =
          (1 - (t : ℝ)) * rightMass := by
        simp only [w]
        rw [← Finset.mul_sum]
        unfold rightMass fareyJoinRightMass
        apply congrArg
        apply Finset.sum_subset
        · intro b hb
          exact (mem_fareyJoinRight_iff _ b).2
            ((mem_fareyJoinRight_iff _ b).1 hb)
        · intro b hb hnot
          have hz : x.weight (.inr b) = 0 := by
            by_contra hn
            exact hnot ((mem_fareyJoinRight_iff _ b).2
              ((mem_supportFinset_iff fareyJoinComplex x (.inr b)).2 hn))
          exact hz
      have hsum : ∑ s ∈ face, w s =
          (∑ a ∈ left, w (.inl a)) + (∑ b ∈ right, w (.inr b)) := by
        rw [show face = left.image Sum.inl ∪ right.image Sum.inr from rfl]
        rw [Finset.sum_union hdis]
        rw [Finset.sum_image (Sum.inl_injective.injOn),
          Finset.sum_image (Sum.inr_injective.injOn)]
      rw [hsum, hleft, hright]
      dsimp [leftMass, rightMass]
      have hmass := fareyJoinMass_sum_one x
      nlinarith

@[simp] theorem fareyJoinCollapseRight_weight_inl
    (base : RealizationPoint fareyFlagComplex) (t : I)
    (x : RealizationPoint fareyJoinComplex) (a : FareySlope) :
    (fareyJoinCollapseRight base t x).weight (.inl a) =
      (fareyJoinLeftMass x + (t : ℝ) * fareyJoinRightMass x) *
        base.weight a := rfl

@[simp] theorem fareyJoinCollapseRight_weight_inr
    (base : RealizationPoint fareyFlagComplex) (t : I)
    (x : RealizationPoint fareyJoinComplex) (b : FareySlope) :
    (fareyJoinCollapseRight base t x).weight (.inr b) =
      (1 - (t : ℝ)) * x.weight (.inr b) := rfl

theorem fareyJoinCollapseRight_continuous
    (base : RealizationPoint fareyFlagComplex) :
    Continuous (fun z : I × RealizationPoint fareyJoinComplex =>
      fareyJoinCollapseRight base z.1 z.2) := by
  apply (continuous_iff_continuous_on_face_time_charts fareyJoinComplex _).2
  intro face hface
  let B : Finset (Sum FareySlope FareySlope) :=
    (supportFinset fareyFlagComplex base).image Sum.inl ∪ face
  apply continuous_of_finite_support_and_coordinates fareyJoinComplex B
  · intro z
    change supportFinset fareyJoinComplex
      (fareyJoinCollapseRight base z.1
        (faceInclusion fareyJoinComplex face hface z.2)) ⊆ B
    intro s hs
    cases s with
    | inl a =>
        by_cases ha : a ∈ supportFinset fareyFlagComplex base
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
        · have hz : base.weight a = 0 := by
            by_contra hn
            exact ha ((mem_supportFinset_iff fareyFlagComplex base a).2 hn)
          exact False.elim (((mem_supportFinset_iff fareyJoinComplex _ (.inl a)).1 hs)
            (by simp [hz]))
    | inr b =>
        by_cases hb : Sum.inr b ∈ face
        · exact Finset.mem_union_right _ hb
        · have hz : (faceInclusion fareyJoinComplex face hface z.2).weight
              (.inr b) = 0 :=
            faceInclusion_weight_of_not_mem fareyJoinComplex face hface z.2
              (.inr b) hb
          exact False.elim (((mem_supportFinset_iff fareyJoinComplex _ (.inr b)).1 hs)
            (by simp [hz]))
  · intro s
    cases s.1 with
    | inl a =>
        simp only [fareyJoinCollapseRight_weight_inl]
        exact ((fareyJoinLeftMass_continuous.comp
            (continuous_faceInclusion fareyJoinComplex face hface |>.comp
              continuous_snd)).add
          ((continuous_subtype_val.comp continuous_fst).mul
            (fareyJoinRightMass_continuous.comp
              (continuous_faceInclusion fareyJoinComplex face hface |>.comp
                continuous_snd)))).mul continuous_const
    | inr b =>
        simp only [fareyJoinCollapseRight_weight_inr]
        exact (continuous_const.sub
          (continuous_subtype_val.comp continuous_fst)).mul
            ((continuous_weight fareyJoinComplex (.inr b)).comp
              (continuous_faceInclusion fareyJoinComplex face hface |>.comp
                continuous_snd))

theorem fareyJoinCollapseRight_one
    (base : RealizationPoint fareyFlagComplex)
    (x : RealizationPoint fareyJoinComplex) :
    fareyJoinCollapseRight base ⟨1, by norm_num⟩ x =
      fareyJoinBlend ⟨0, by norm_num⟩ base base := by
  apply RealizationPoint.ext
  funext s
  cases s with
  | inl a =>
      simp only [fareyJoinCollapseRight_weight_inl,
        fareyJoinBlend_weight_inl, one_mul, sub_zero]
      have hmass := fareyJoinMass_sum_one x
      rw [hmass]
      ring
  | inr b =>
      simp

theorem fareyJoinCollapseRight_zero_of_leftBase
    (base : RealizationPoint fareyFlagComplex)
    (x : RealizationPoint fareyJoinComplex)
    (hleft : ∀ a : FareySlope,
      x.weight (.inl a) = fareyJoinLeftMass x * base.weight a) :
    fareyJoinCollapseRight base ⟨0, by norm_num⟩ x = x := by
  apply RealizationPoint.ext
  funext s
  cases s with
  | inl a =>
      simp only [fareyJoinCollapseRight_weight_inl]
      simpa using (hleft a).symm
  | inr b =>
      simp

theorem fareyJoinReplaceLeft_one_leftBase
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base))
    (x : RealizationPoint fareyJoinComplex)
    (a : FareySlope) :
    (fareyJoinReplaceLeft base H ⟨1, by norm_num⟩ x).weight (.inl a) =
      fareyJoinLeftMass x * base.weight a := by
  by_cases hm : 0 < fareyJoinLeftMass x
  · rw [fareyJoinReplaceLeft_weight_inl_of_pos base H _ x hm a]
    have hH := H.map_one_left (fareyJoinNormalizeLeft x hm)
    exact congrArg (fun p : RealizationPoint fareyFlagComplex =>
      fareyJoinLeftMass x * p.weight a) hH
  · have hzero : fareyJoinLeftMass x = 0 :=
      le_antisymm (le_of_not_gt hm) (fareyJoinLeftMass_nonneg x)
    have ha : x.weight (.inl a) = 0 := by
      by_cases hmem : a ∈ fareyJoinLeft
          (supportFinset fareyJoinComplex x)
      · have hle : x.weight (.inl a) ≤ fareyJoinLeftMass x := by
          unfold fareyJoinLeftMass
          exact Finset.single_le_sum
            (fun b hb => x.nonneg (.inl b)) hmem
        exact le_antisymm (hzero ▸ hle) (x.nonneg (.inl a))
      · by_contra hn
        exact hmem ((mem_fareyJoinLeft_iff _ a).2
          ((mem_supportFinset_iff fareyJoinComplex x (.inl a)).2 hn))
    simp [fareyJoinReplaceLeft, hzero, ha]



end CurveComplexGenusTwo.Topology
