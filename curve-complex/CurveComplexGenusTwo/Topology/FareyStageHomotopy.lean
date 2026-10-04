import CurveComplexGenusTwo.Topology.FareyStageAssembly

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex


theorem fareyParentTriangle_stage (p : ℚ) (hp : 1 < p.den) :
    ∀ w ∈ fareyParentTriangle p hp,
      fareyDenominator w ≤ p.den := by
  intro w hw
  rcases fareyParentData_spec p hp with ⟨hld, hrd, _, _, _⟩
  simp only [fareyParentTriangle, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · simp [fareyDenominator]
  · simp only [fareyDenominator]
    omega
  · simp only [fareyDenominator]
    omega

theorem fareyStageFace_subset_parentTriangle
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (p : ℚ) (hp : some p ∈ σ.1) (hpn : p.den = n) :
    σ.1 ⊆ fareyParentTriangle p (by omega) := by
  have hpgt : 1 < p.den := by omega
  intro w hw
  by_cases hwp : w = some p
  · simp [fareyParentTriangle, hwp]
  have hsmall : fareyDenominator w < n :=
    fareyFace_unique_top_vertex σ.1 σ.2.1 n hn σ.2.2 (some p) hp
      (by simpa [fareyDenominator] using hpn) w hw hwp
  have hadj : FareyAdjacent w (some p) := σ.2.1.2 hw hp hwp
  cases w with
  | none => exact False.elim (farey_infinity_not_lower_neighbor p hpgt hadj)
  | some q =>
    have hqsmall : q.den < p.den := by
      simpa [fareyDenominator, hpn] using hsmall
    rcases (fareyParentData_lower_link p hpgt (some q) hqsmall).mp hadj with h | h
    · simp [fareyParentTriangle, h]
    · simp [fareyParentTriangle, h]

theorem fareyParentTriangle_mem_top (p : ℚ) (hp : 1 < p.den) :
    some p ∈ fareyParentTriangle p hp := by
  simp [fareyParentTriangle]

theorem fareyParentTriangle_mem_left (p : ℚ) (hp : 1 < p.den) :
    some (fareyParentData p hp).1 ∈ fareyParentTriangle p hp := by
  simp [fareyParentTriangle]

theorem fareyParentTriangle_mem_right (p : ℚ) (hp : 1 < p.den) :
    some (fareyParentData p hp).2 ∈ fareyParentTriangle p hp := by
  simp [fareyParentTriangle]

theorem fareyParentTriangle_distinct (p : ℚ) (hp : 1 < p.den) :
    some p ≠ some (fareyParentData p hp).1 ∧
      some p ≠ some (fareyParentData p hp).2 ∧
      some (fareyParentData p hp).1 ≠ some (fareyParentData p hp).2 := by
  rcases fareyParentData_spec p hp with ⟨hld, hrd, _, _, hlr⟩
  constructor
  · intro h
    have : p = (fareyParentData p hp).1 := Option.some.inj h
    have hden := congrArg Rat.den this
    omega
  constructor
  · intro h
    have : p = (fareyParentData p hp).2 := Option.some.inj h
    have hden := congrArg Rat.den this
    omega
  · intro h
    have : (fareyParentData p hp).1 = (fareyParentData p hp).2 := Option.some.inj h
    rw [this] at hlr
    exact fareyAdjacent_irrefl _ hlr


noncomputable def fareyTopFaceAffine
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (p : ℚ) (hp : some p ∈ σ.1) (hpn : p.den = n)
    (t : ConeTime) (x : FiniteSimplex σ.1) :
    RealizationPoint fareyComplex := by
  classical
  let hpgt : 1 < p.den := by omega
  let τ := fareyParentTriangle p hpgt
  let hτ : τ ∈ fareyComplex.faces := fareyParentTriangle_face p hpgt
  let hστ : σ.1 ⊆ τ := fareyStageFace_subset_parentTriangle n hn σ p hp hpn
  let l := some (fareyParentData p hpgt).1
  let r := some (fareyParentData p hpgt).2
  let hpt : some p ∈ τ := fareyParentTriangle_mem_top p hpgt
  let hlt : l ∈ τ := fareyParentTriangle_mem_left p hpgt
  let hrt : r ∈ τ := fareyParentTriangle_mem_right p hpgt
  obtain ⟨hpl, hpr, hlr⟩ := fareyParentTriangle_distinct p hpgt
  exact faceInclusion fareyComplex τ hτ
    (fareyParentAffine τ (some p) l r hpt hlt hrt hpl hpr hlr t
      (fareyFiniteSimplexInclude σ.1 τ hστ x))

theorem fareyTopFaceAffine_continuous
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (p : ℚ) (hp : some p ∈ σ.1) (hpn : p.den = n) :
    Continuous (fun q : ConeTime × FiniteSimplex σ.1 =>
      fareyTopFaceAffine n hn σ p hp hpn q.1 q.2) := by
  classical
  let hpgt : 1 < p.den := by omega
  let τ := fareyParentTriangle p hpgt
  let hτ : τ ∈ fareyComplex.faces := fareyParentTriangle_face p hpgt
  let hστ : σ.1 ⊆ τ := fareyStageFace_subset_parentTriangle n hn σ p hp hpn
  let l := some (fareyParentData p hpgt).1
  let r := some (fareyParentData p hpgt).2
  let hpt : some p ∈ τ := fareyParentTriangle_mem_top p hpgt
  let hlt : l ∈ τ := fareyParentTriangle_mem_left p hpgt
  let hrt : r ∈ τ := fareyParentTriangle_mem_right p hpgt
  obtain ⟨hpl, hpr, hlr⟩ := fareyParentTriangle_distinct p hpgt
  have hincl : Continuous (fareyFiniteSimplexInclude σ.1 τ hστ) :=
    fareyFiniteSimplexInclude_continuous _ _ _
  have hprod : Continuous (fun q : ConeTime × FiniteSimplex σ.1 =>
      (q.1, fareyFiniteSimplexInclude σ.1 τ hστ q.2)) :=
    continuous_fst.prodMk (hincl.comp continuous_snd)
  have hcont := (continuous_fareyParentAffine_face τ hτ (some p) l r
    hpt hlt hrt hpl hpr hlr).comp hprod
  convert hcont using 1
  funext q
  rfl

theorem fareyTopFaceAffine_weight
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (p : ℚ) (hp : some p ∈ σ.1) (hpn : p.den = n)
    (t : ConeTime) (x : FiniteSimplex σ.1) (w : FareySlope) :
    (fareyTopFaceAffine n hn σ p hp hpn t x).weight w =
      (if w = some p then (1 - (t : ℝ)) *
          (faceInclusion fareyComplex σ.1 σ.2.1 x).weight w
        else (faceInclusion fareyComplex σ.1 σ.2.1 x).weight w) +
      (if w = some (fareyParentData p (by omega)).1 then
          (t : ℝ) * (faceInclusion fareyComplex σ.1 σ.2.1 x).weight (some p) / 2
        else 0) +
      (if w = some (fareyParentData p (by omega)).2 then
          (t : ℝ) * (faceInclusion fareyComplex σ.1 σ.2.1 x).weight (some p) / 2
        else 0) := by
  classical
  unfold fareyTopFaceAffine
  simp only
  rw [fareyParentAffine_weight]
  rw [fareyFiniteSimplexInclude_faceInclusion]

theorem fareyTopFaceAffine_zero
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (p : ℚ) (hp : some p ∈ σ.1) (hpn : p.den = n)
    (x : FiniteSimplex σ.1) :
    fareyTopFaceAffine n hn σ p hp hpn ⟨0, by norm_num⟩ x =
      faceInclusion fareyComplex σ.1 σ.2.1 x := by
  apply RealizationPoint.ext
  funext w
  rw [fareyTopFaceAffine_weight]
  simp

theorem fareyTopFaceAffine_one_top_weight_zero
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (p : ℚ) (hp : some p ∈ σ.1) (hpn : p.den = n)
    (x : FiniteSimplex σ.1) :
    (fareyTopFaceAffine n hn σ p hp hpn ⟨1, by norm_num⟩ x).weight (some p) = 0 := by
  rw [fareyTopFaceAffine_weight]
  have hpd := fareyParentTriangle_distinct p (by omega)
  have hpl : p ≠ (fareyParentData p (by omega)).1 := by
    intro h
    exact hpd.1 (congrArg some h)
  have hpr : p ≠ (fareyParentData p (by omega)).2 := by
    intro h
    exact hpd.2.1 (congrArg some h)
  simp [hpl, hpr]

noncomputable def fareyStageFaceAffine
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (t : ConeTime) (x : FiniteSimplex σ.1) :
    RealizationPoint fareyComplex := by
  classical
  by_cases htop : ∃ p : ℚ, some p ∈ σ.1 ∧ p.den = n
  · exact fareyTopFaceAffine n hn σ (Classical.choose htop)
      (Classical.choose_spec htop).1 (Classical.choose_spec htop).2 t x
  · exact faceInclusion fareyComplex σ.1 σ.2.1 x

theorem fareyStageFaceAffine_continuous
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n) :
    Continuous (fun q : ConeTime × FiniteSimplex σ.1 =>
      fareyStageFaceAffine n hn σ q.1 q.2) := by
  classical
  unfold fareyStageFaceAffine
  split_ifs with htop
  · exact fareyTopFaceAffine_continuous n hn σ (Classical.choose htop)
      (Classical.choose_spec htop).1 (Classical.choose_spec htop).2
  · exact (continuous_faceInclusion fareyComplex σ.1 σ.2.1).comp continuous_snd

theorem fareyStageFaceAffine_of_top
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (p : ℚ) (hp : some p ∈ σ.1) (hpn : p.den = n)
    (t : ConeTime) (x : FiniteSimplex σ.1) :
    fareyStageFaceAffine n hn σ t x =
      fareyTopFaceAffine n hn σ p hp hpn t x := by
  classical
  have htop : ∃ q : ℚ, some q ∈ σ.1 ∧ q.den = n := ⟨p, hp, hpn⟩
  have hq := Classical.choose_spec htop
  have hqp : some (Classical.choose htop) = some p :=
    fareyFace_atMostOne_of_denominator_gt_one σ.1 σ.2.1.2 n hn
      (some (Classical.choose htop)) (some p) hq.1 hp
      (by simpa [fareyDenominator] using hq.2)
      (by simpa [fareyDenominator] using hpn)
  have hqeq : Classical.choose htop = p := Option.some.inj hqp
  simp [fareyStageFaceAffine, htop, hqeq]

theorem fareyStageFaceAffine_fixed_of_no_top_mass
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (t : ConeTime) (x : FiniteSimplex σ.1)
    (hzero : ∀ p : ℚ, p.den = n →
      (faceInclusion fareyComplex σ.1 σ.2.1 x).weight (some p) = 0) :
    fareyStageFaceAffine n hn σ t x =
      faceInclusion fareyComplex σ.1 σ.2.1 x := by
  classical
  by_cases htop : ∃ p : ℚ, some p ∈ σ.1 ∧ p.den = n
  · let p := Classical.choose htop
    have hp : some p ∈ σ.1 := (Classical.choose_spec htop).1
    have hpn : p.den = n := (Classical.choose_spec htop).2
    rw [fareyStageFaceAffine_of_top n hn σ p hp hpn]
    apply RealizationPoint.ext
    funext w
    rw [fareyTopFaceAffine_weight]
    have hz := hzero p hpn
    by_cases hwp : w = some p
    · subst w
      simp [hz]
    · simp [hwp, hz]
  · simp [fareyStageFaceAffine, htop]

theorem fareyStageFaceAffine_compatible
    (n : ℕ) (hn : 1 < n)
    (σ τ : fareyStageFaceIndex n)
    (t : ConeTime) (x : FiniteSimplex σ.1) (y : FiniteSimplex τ.1)
    (hxy : faceInclusion fareyComplex σ.1 σ.2.1 x =
      faceInclusion fareyComplex τ.1 τ.2.1 y) :
    fareyStageFaceAffine n hn σ t x = fareyStageFaceAffine n hn τ t y := by
  classical
  by_cases hpositive : ∃ p : ℚ, p.den = n ∧
      (faceInclusion fareyComplex σ.1 σ.2.1 x).weight (some p) ≠ 0
  · obtain ⟨p, hpn, hpweight⟩ := hpositive
    have hpσ : some p ∈ σ.1 := by
      by_contra hnot
      exact hpweight (faceInclusion_weight_of_not_mem fareyComplex σ.1 σ.2.1 x (some p) hnot)
    have hpτ : some p ∈ τ.1 := by
      by_contra hnot
      exact hpweight (by rw [hxy]; exact faceInclusion_weight_of_not_mem fareyComplex τ.1 τ.2.1 y (some p) hnot)
    rw [fareyStageFaceAffine_of_top n hn σ p hpσ hpn,
      fareyStageFaceAffine_of_top n hn τ p hpτ hpn]
    apply RealizationPoint.ext
    funext w
    rw [fareyTopFaceAffine_weight, fareyTopFaceAffine_weight, hxy]
  · have hzσ : ∀ p : ℚ, p.den = n →
        (faceInclusion fareyComplex σ.1 σ.2.1 x).weight (some p) = 0 := by
      intro p hpden
      by_contra hne
      exact hpositive ⟨p, hpden, hne⟩
    have hzτ : ∀ p : ℚ, p.den = n →
        (faceInclusion fareyComplex τ.1 τ.2.1 y).weight (some p) = 0 := by
      intro p hpden
      rw [← hxy]
      exact hzσ p hpden
    rw [fareyStageFaceAffine_fixed_of_no_top_mass n hn σ t x hzσ,
      fareyStageFaceAffine_fixed_of_no_top_mass n hn τ t y hzτ]
    exact hxy

noncomputable def fareyStageAffineAmbient
    (n : ℕ) (hn : 1 < n) :
    fareyStage n × ConeTime → RealizationPoint fareyComplex := by
  classical
  intro z
  let a := Classical.choose ((fareyStageCoverMap_isQuotientMap n).surjective z.1)
  exact fareyStageFaceAffine n hn a.1 z.2 a.2

theorem fareyStageAffineAmbient_face
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (t : ConeTime) (x : FiniteSimplex σ.1) :
    fareyStageAffineAmbient n hn (fareyStageCoverMap n ⟨σ, x⟩, t) =
      fareyStageFaceAffine n hn σ t x := by
  classical
  unfold fareyStageAffineAmbient
  let a := Classical.choose
    ((fareyStageCoverMap_isQuotientMap n).surjective
      (fareyStageCoverMap n ⟨σ, x⟩))
  have ha := Classical.choose_spec
    ((fareyStageCoverMap_isQuotientMap n).surjective
      (fareyStageCoverMap n ⟨σ, x⟩))
  have heq : faceInclusion fareyComplex a.1.1 a.1.2.1 a.2 =
      faceInclusion fareyComplex σ.1 σ.2.1 x := by
    exact congrArg Subtype.val ha
  exact fareyStageFaceAffine_compatible n hn a.1 σ t a.2 x heq

theorem fareyStageAffineAmbient_continuous
    (n : ℕ) (hn : 1 < n) :
    Continuous (fareyStageAffineAmbient n hn) := by
  apply continuous_fareyStageHomotopy_of_faces n _
  let h : (Σ σ : fareyStageFaceIndex n, FiniteSimplex σ.1 × ConeTime) →
      RealizationPoint fareyComplex :=
    fun q => fareyStageFaceAffine n hn q.1 q.2.2 q.2.1
  have hh : Continuous h := by
    apply continuous_sigma_iff.mpr
    intro σ
    have hc := (fareyStageFaceAffine_continuous n hn σ).comp continuous_swap
    convert hc using 1
    funext q
    rfl
  have hd : Continuous (fun q :
      (Σ σ : fareyStageFaceIndex n, FiniteSimplex σ.1) × ConeTime =>
      h (Homeomorph.sigmaProdDistrib q)) :=
    hh.comp (Homeomorph.sigmaProdDistrib).continuous
  convert hd using 1
  funext q
  exact fareyStageAffineAmbient_face n hn q.1.1 q.2 q.1.2

theorem fareyStageAffineAmbient_zero
    (n : ℕ) (hn : 1 < n) (z : fareyStage n) :
    fareyStageAffineAmbient n hn (z, ⟨0, by norm_num⟩) = z := by
  classical
  let a := Classical.choose ((fareyStageCoverMap_isQuotientMap n).surjective z)
  have ha := Classical.choose_spec
    ((fareyStageCoverMap_isQuotientMap n).surjective z)
  have hchart : fareyStageCoverMap n a = z := ha
  rw [← hchart]
  rw [show fareyStageAffineAmbient n hn
      (fareyStageCoverMap n a, ⟨0, by norm_num⟩) =
      fareyStageFaceAffine n hn a.1 ⟨0, by norm_num⟩ a.2 by
    exact fareyStageAffineAmbient_face n hn a.1 ⟨0, by norm_num⟩ a.2]
  by_cases htop : ∃ p : ℚ, some p ∈ a.1.1 ∧ p.den = n
  · let p := Classical.choose htop
    have hp : some p ∈ a.1.1 := (Classical.choose_spec htop).1
    have hpn : p.den = n := (Classical.choose_spec htop).2
    rw [fareyStageFaceAffine_of_top n hn a.1 p hp hpn]
    exact fareyTopFaceAffine_zero n hn a.1 p hp hpn a.2
  · simp [fareyStageFaceAffine, htop]
    rfl

theorem fareyStageAffineAmbient_face_one_top_weight_zero
    (n : ℕ) (hn : 1 < n) (σ : fareyStageFaceIndex n)
    (p : ℚ) (hp : some p ∈ σ.1) (hpn : p.den = n)
    (x : FiniteSimplex σ.1) :
    (fareyStageAffineAmbient n hn
      (fareyStageCoverMap n ⟨σ, x⟩, ⟨1, by norm_num⟩)).weight (some p) = 0 := by
  rw [fareyStageAffineAmbient_face]
  rw [fareyStageFaceAffine_of_top n hn σ p hp hpn]
  exact fareyTopFaceAffine_one_top_weight_zero n hn σ p hp hpn x

theorem fareyStageAffineAmbient_one_top_weight_zero
    (n : ℕ) (hn : 1 < n) (z : fareyStage n)
    (p : ℚ) (hpz : z.1.weight (some p) ≠ 0) (hpn : p.den = n) :
    (fareyStageAffineAmbient n hn (z, ⟨1, by norm_num⟩)).weight (some p) = 0 := by
  classical
  let a := Classical.choose ((fareyStageCoverMap_isQuotientMap n).surjective z)
  have ha := Classical.choose_spec
    ((fareyStageCoverMap_isQuotientMap n).surjective z)
  have hp : some p ∈ a.1.1 := by
    by_contra hnot
    apply hpz
    rw [← ha]
    exact faceInclusion_weight_of_not_mem fareyComplex a.1.1 a.1.2.1 a.2
      (some p) hnot
  rw [show fareyStageAffineAmbient n hn
      (z, ⟨1, by norm_num⟩) =
      fareyStageFaceAffine n hn a.1 ⟨1, by norm_num⟩ a.2 by
    rw [← ha]
    exact fareyStageAffineAmbient_face n hn a.1 ⟨1, by norm_num⟩ a.2]
  rw [fareyStageFaceAffine_of_top n hn a.1 p hp hpn]
  exact fareyTopFaceAffine_one_top_weight_zero n hn a.1 p hp hpn a.2

end CurveComplexGenusTwo.Topology
