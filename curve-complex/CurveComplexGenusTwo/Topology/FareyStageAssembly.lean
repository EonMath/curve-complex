import CurveComplexGenusTwo.Topology.FareyGlobalFiltration
import CurveComplexGenusTwo.Topology.FareyAffineCollapse
import CurveComplexGenusTwo.Topology.FareyFanIdentification
import CurveComplexGenusTwo.Foundations.RealizationCW

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

noncomputable def finiteSimplexOfFaceLocal
    (x : RealizationPoint fareyComplex) (σ : Finset FareySlope)
    (_hzero : ∀ w ∉ σ, x.weight w = 0)
    (hsum : ∑ w ∈ σ, x.weight w = 1) : FiniteSimplex σ := by
  refine ⟨fun w => x.weight w, ?_, ?_⟩
  · intro w
    exact x.nonneg w
  · simpa only [Finset.sum_attach, Finset.univ_eq_attach] using hsum

noncomputable def fareyParentData (p : ℚ) (hp : 1 < p.den) : ℚ × ℚ := by
  classical
  let h := farey_parents_and_lower_link p hp
  exact (Classical.choose h, Classical.choose (Classical.choose_spec h))

theorem fareyParentData_spec (p : ℚ) (hp : 1 < p.den) :
    let l := (fareyParentData p hp).1
    let r := (fareyParentData p hp).2
    l.den < p.den ∧ r.den < p.den ∧
      FareyAdjacent (some l) (some p) ∧
      FareyAdjacent (some r) (some p) ∧
      FareyAdjacent (some l) (some r) := by
  classical
  let h := farey_parents_and_lower_link p hp
  have hs := Classical.choose_spec (Classical.choose_spec h)
  dsimp [fareyParentData]
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩

theorem fareyParentData_lower_link (p : ℚ) (hp : 1 < p.den)
    (s : FareySlope)
    (hs : match s with | none => False | some q => q.den < p.den) :
    (FareyAdjacent s (some p) ↔
      s = some (fareyParentData p hp).1 ∨
        s = some (fareyParentData p hp).2) := by
  classical
  let h := farey_parents_and_lower_link p hp
  have hspec := Classical.choose_spec (Classical.choose_spec h)
  rcases hspec with ⟨_, _, _, _, _, _, _, _, hlink⟩
  dsimp [fareyParentData]
  exact hlink s hs

theorem fareyStage_support_subset_parentTriangle
    (n : ℕ) (hn : 1 < n) (x : fareyStage n)
    (p : ℚ) (hp : some p ∈ supportFinset fareyComplex x.1)
    (hpn : p.den = n) :
    supportFinset fareyComplex x.1 ⊆
      ({some p, some (fareyParentData p (by omega)).1,
        some (fareyParentData p (by omega)).2} : Finset FareySlope) := by
  classical
  let S := supportFinset fareyComplex x.1
  have hSface : S ∈ fareyComplex.faces := supportFinset_mem_faces fareyComplex x.1
  have hstage : ∀ w ∈ S, fareyDenominator w ≤ n := by
    intro w hw
    by_contra hnot
    exact (mem_supportFinset_iff fareyComplex x.1 w).1 hw
      (x.property w hnot)
  have hpgt : 1 < p.den := by omega
  have hparents := fareyParentData_spec p hpgt
  have hparentLowerLink := fun s hs => fareyParentData_lower_link p hpgt s hs
  intro w hw
  have hwS : w ∈ S := hw
  by_cases hwp : w = some p
  · subst w
    simp [S]
  · have hsmall : fareyDenominator w < n :=
      fareyFace_unique_top_vertex S hSface n hn hstage (some p) hp hpn w hwS hwp
    have hadj : FareyAdjacent w (some p) := hSface.2 hwS hp hwp
    cases w with
    | none => exact False.elim (farey_infinity_not_lower_neighbor p hpgt hadj)
    | some q =>
      have hqsmall : q.den < p.den := by
        simpa [fareyDenominator, hpn] using hsmall
      have hqParent := (hparentLowerLink (some q) hqsmall).mp hadj
      rcases hqParent with hq | hq
      · simp [hq]
      · simp [hq]

private theorem farey_parent_triangle_face (p l r : ℚ)
    (hlp : FareyAdjacent (some l) (some p))
    (hrp : FareyAdjacent (some r) (some p))
    (hlr : FareyAdjacent (some l) (some r)) :
    ({some p, some l, some r} : Finset FareySlope) ∈ fareyComplex.faces := by
  refine ⟨by simp, ?_⟩
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with ha | ha
  · subst a
    rcases Finset.mem_insert.mp hb with hb | hb
    · subst b
      exact False.elim (hab rfl)
    · rcases Finset.mem_insert.mp hb with hb | hb
      · subst b
        exact fareyAdjacent_symm hlp
      · rcases Finset.mem_singleton.mp hb with rfl
        exact fareyAdjacent_symm hrp
  · rcases Finset.mem_insert.mp ha with ha | ha
    · subst a
      rcases Finset.mem_insert.mp hb with hb | hb
      · subst b
        exact hlp
      · rcases Finset.mem_insert.mp hb with hb | hb
        · subst b
          exact False.elim (hab rfl)
        · rcases Finset.mem_singleton.mp hb with rfl
          exact hlr
    · rcases Finset.mem_singleton.mp ha with rfl
      rcases Finset.mem_insert.mp hb with hb | hb
      · subst b
        exact hrp
      · rcases Finset.mem_insert.mp hb with hb | hb
        · subst b
          exact fareyAdjacent_symm hlr
        · rcases Finset.mem_singleton.mp hb with rfl
          exact False.elim (hab rfl)

private theorem sum_supportFinset_farey (x : RealizationPoint fareyComplex) :
    ∑ w ∈ supportFinset fareyComplex x, x.weight w = 1 := by
  classical
  let σ : Finset FareySlope := Classical.choose x.liesInFace
  have hs := Classical.choose_spec x.liesInFace
  have hsub : supportFinset fareyComplex x ⊆ σ := by
    intro w hw
    exact (Finset.mem_filter.mp hw).1
  have heq : (∑ w ∈ supportFinset fareyComplex x, x.weight w) =
      ∑ w ∈ σ, x.weight w := by
    apply Finset.sum_subset hsub
    intro w hwσ hws
    by_contra hn
    exact hws ((mem_supportFinset_iff fareyComplex x w).2 hn)
  rw [heq]
  exact hs.2.2

noncomputable def fareySimplexInFace
    (x : RealizationPoint fareyComplex)
    (τ : Finset FareySlope)
    (hS : supportFinset fareyComplex x ⊆ τ) : FiniteSimplex τ :=
  finiteSimplexOfFaceLocal x τ
    (by
      intro w hw
      by_contra hne
      exact hw (hS ((mem_supportFinset_iff fareyComplex x w).2 hne)))
    (by
      classical
      have hsumS := sum_supportFinset_farey x
      have hsum : (∑ w ∈ supportFinset fareyComplex x, x.weight w) =
          ∑ w ∈ τ, x.weight w := by
        apply Finset.sum_subset hS
        intro w _hwτ hws
        by_contra hn
        exact hws ((mem_supportFinset_iff fareyComplex x w).2 hn)
      rw [← hsum]
      exact hsumS)

theorem fareySimplexInFace_inclusion
    (x : RealizationPoint fareyComplex)
    (τ : Finset FareySlope)
    (hτ : τ ∈ fareyComplex.faces)
    (hS : supportFinset fareyComplex x ⊆ τ) :
    faceInclusion fareyComplex τ hτ
      (fareySimplexInFace x τ hS) = x := by
  apply RealizationPoint.ext
  funext w
  by_cases hw : w ∈ τ
  · simp [faceInclusion, fareySimplexInFace, finiteSimplexOfFaceLocal, hw]
  · have hzero : x.weight w = 0 := by
      by_contra hne
      exact hw (hS ((mem_supportFinset_iff fareyComplex x w).2 hne))
    simp [faceInclusion, fareySimplexInFace, finiteSimplexOfFaceLocal, hw, hzero]

noncomputable def fareyParentTriangle (p : ℚ) (hp : 1 < p.den) :
    Finset FareySlope :=
  {some p, some (fareyParentData p hp).1, some (fareyParentData p hp).2}

theorem fareyParentTriangle_face (p : ℚ) (hp : 1 < p.den) :
    fareyParentTriangle p hp ∈ fareyComplex.faces := by
  let l := (fareyParentData p hp).1
  let r := (fareyParentData p hp).2
  have hs := fareyParentData_spec p hp
  exact farey_parent_triangle_face p l r hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2

theorem fareyTopFace_subset_parentTriangle
    (n : ℕ) (hn : 1 < n)
    (σ : Finset FareySlope) (hσ : σ ∈ fareyComplex.faces)
    (hstage : ∀ w ∈ σ, fareyDenominator w ≤ n)
    (p : ℚ) (hp : some p ∈ σ) (hpn : p.den = n)
    (hpgt : 1 < p.den) :
    σ ⊆ fareyParentTriangle p hpgt := by
  intro w hw
  by_cases hwp : w = some p
  · subst w
    simp [fareyParentTriangle]
  · have hsmall : fareyDenominator w < n :=
      fareyFace_unique_top_vertex σ hσ n hn hstage (some p) hp
        (by simpa [fareyDenominator] using hpn) w hw hwp
    have hadj : FareyAdjacent w (some p) := hσ.2 hw hp hwp
    cases w with
    | none => exact False.elim (farey_infinity_not_lower_neighbor p hpgt hadj)
    | some q =>
      have hqsmall : q.den < p.den := by
        simpa [fareyDenominator, hpn] using hsmall
      have hqParent := (fareyParentData_lower_link p hpgt (some q) hqsmall).mp hadj
      rcases hqParent with hq | hq
      · simp [fareyParentTriangle, hq]
      · simp [fareyParentTriangle, hq]

noncomputable def fareyParentTriangleMove
    (p : ℚ) (hp : 1 < p.den)
    (x : RealizationPoint fareyComplex)
    (hx : supportFinset fareyComplex x ⊆ fareyParentTriangle p hp)
    (t : ConeTime) : RealizationPoint fareyComplex := by
  let τ := fareyParentTriangle p hp
  let hτ := fareyParentTriangle_face p hp
  let l := (fareyParentData p hp).1
  let r := (fareyParentData p hp).2
  have hs := fareyParentData_spec p hp
  have hpl : (some p : FareySlope) ≠ some l := by
    intro heq
    have heq' : p = l := Option.some.inj heq
    have hden : p.den = l.den := congrArg Rat.den heq'
    have hsmall : l.den < p.den := hs.1
    omega
  have hpr : (some p : FareySlope) ≠ some r := by
    intro heq
    have heq' : p = r := Option.some.inj heq
    have hden : p.den = r.den := congrArg Rat.den heq'
    have hsmall : r.den < p.den := hs.2.1
    omega
  have hlr : (some l : FareySlope) ≠ some r := by
    intro heq
    have hadj : FareyAdjacent (some l) (some r) := hs.2.2.2.2
    rw [heq] at hadj
    exact fareyAdjacent_irrefl (some r) hadj
  exact faceInclusion fareyComplex τ hτ
    (fareyParentAffine τ (some p) (some l) (some r)
      (by simp [τ, fareyParentTriangle])
      (by change some l ∈ τ; dsimp [τ, fareyParentTriangle, l]; simp)
      (by change some r ∈ τ; dsimp [τ, fareyParentTriangle, r]; simp)
      hpl hpr hlr t (fareySimplexInFace x τ hx))

theorem fareyParentTriangleMove_weight
    (p : ℚ) (hp : 1 < p.den)
    (x : RealizationPoint fareyComplex)
    (hx : supportFinset fareyComplex x ⊆ fareyParentTriangle p hp)
    (t : ConeTime) (w : FareySlope) :
    (fareyParentTriangleMove p hp x hx t).weight w =
      (if w = some p then (1 - (t : ℝ)) * x.weight w else x.weight w) +
      (if w = some (fareyParentData p hp).1 then
        (t : ℝ) * x.weight (some p) / 2 else 0) +
      (if w = some (fareyParentData p hp).2 then
        (t : ℝ) * x.weight (some p) / 2 else 0) := by
  unfold fareyParentTriangleMove
  rw [fareyParentAffine_weight]
  rw [fareySimplexInFace_inclusion]

theorem fareyParentTriangleMove_zero
    (p : ℚ) (hp : 1 < p.den)
    (x : RealizationPoint fareyComplex)
    (hx : supportFinset fareyComplex x ⊆ fareyParentTriangle p hp) :
    fareyParentTriangleMove p hp x hx ⟨0, by norm_num⟩ = x := by
  apply RealizationPoint.ext
  funext w
  rw [fareyParentTriangleMove_weight]
  simp

theorem fareyParentTriangleMove_top_zero
    (p : ℚ) (hp : 1 < p.den)
    (x : RealizationPoint fareyComplex)
    (hx : supportFinset fareyComplex x ⊆ fareyParentTriangle p hp) :
    (fareyParentTriangleMove p hp x hx ⟨1, by norm_num⟩).weight (some p) = 0 := by
  rw [fareyParentTriangleMove_weight]
  have hs := fareyParentData_spec p hp
  have hpl : p ≠ (fareyParentData p hp).1 := by
    intro heq
    have hden := congrArg Rat.den heq
    omega
  have hpr : p ≠ (fareyParentData p hp).2 := by
    intro heq
    have hden := congrArg Rat.den heq
    omega
  simp [hpl, hpr]

theorem fareyParentTriangleMove_fixed
    (p : ℚ) (hp : 1 < p.den)
    (x : RealizationPoint fareyComplex)
    (hx : supportFinset fareyComplex x ⊆ fareyParentTriangle p hp)
    (hzero : x.weight (some p) = 0) (t : ConeTime) :
    fareyParentTriangleMove p hp x hx t = x := by
  apply RealizationPoint.ext
  funext w
  rw [fareyParentTriangleMove_weight]
  by_cases hwp : w = some p
  · subst w
    simp [hzero]
  · simp [hwp, hzero]

noncomputable def fareyStageStep (n : ℕ) (hn : 1 < n)
    (x : fareyStage n) (t : ConeTime) : RealizationPoint fareyComplex := by
  classical
  by_cases htop : ∃ p : ℚ,
      some p ∈ supportFinset fareyComplex x.1 ∧ p.den = n
  · let p := Classical.choose htop
    have hp := Classical.choose_spec htop
    have hpgt : 1 < p.den := by rw [hp.2]; exact hn
    have hS : supportFinset fareyComplex x.1 ⊆ fareyParentTriangle p hpgt := by
      simpa only [fareyParentTriangle] using
        fareyStage_support_subset_parentTriangle n hn x p hp.1 hp.2
    exact fareyParentTriangleMove p hpgt x.1 hS t
  · exact x.1

theorem fareyStageStep_zero (n : ℕ) (hn : 1 < n)
    (x : fareyStage n) :
    fareyStageStep n hn x ⟨0, by norm_num⟩ = x.1 := by
  classical
  unfold fareyStageStep
  split
  · exact fareyParentTriangleMove_zero _ _ _ _
  · rfl

theorem fareyStageStep_eq_parentTriangleMove
    (n : ℕ) (hn : 1 < n) (x : fareyStage n)
    (p : ℚ) (hp : some p ∈ supportFinset fareyComplex x.1)
    (hpn : p.den = n)
    (hpgt : 1 < p.den)
    (hS : supportFinset fareyComplex x.1 ⊆ fareyParentTriangle p hpgt)
    (t : ConeTime) :
    fareyStageStep n hn x t = fareyParentTriangleMove p hpgt x.1 hS t := by
  classical
  unfold fareyStageStep
  split
  · rename_i htop
    let q := Classical.choose htop
    have hq := Classical.choose_spec htop
    have hpq : p = q := by
      have hface := supportFinset_mem_faces fareyComplex x.1
      have heq := fareyFace_atMostOne_of_denominator_gt_one
        (supportFinset fareyComplex x.1) hface.2 n hn
        (some p) (some q) hp hq.1 (by simpa [fareyDenominator] using hpn)
        (by simpa [fareyDenominator] using hq.2)
      exact Option.some.inj heq
    subst p
    rfl
  · exact False.elim (‹¬ ∃ p : ℚ, some p ∈ supportFinset fareyComplex x.1 ∧ p.den = n›
      ⟨p, hp, hpn⟩)

theorem fareyStageStep_fixed_of_lower (n : ℕ) (hn : 1 < n)
    (x : fareyStage n) (hx : x.1 ∈ fareyStage (n - 1)) (t : ConeTime) :
    fareyStageStep n hn x t = x.1 := by
  classical
  unfold fareyStageStep
  split
  · rename_i htop
    let p := Classical.choose htop
    have hp := Classical.choose_spec htop
    have hpzero : x.1.weight (some p) = 0 := by
      apply hx (some p)
      simp only [fareyDenominator]
      rw [hp.2]
      omega
    have hpgt : 1 < p.den := by rw [hp.2]; exact hn
    exact fareyParentTriangleMove_fixed p hpgt x.1 _ hpzero t
  · rfl

theorem fareyStageStep_eq_parentTriangleMove_of_face
    (n : ℕ) (hn : 1 < n) (x : fareyStage n)
    (σ : Finset FareySlope) (hσ : σ ∈ fareyComplex.faces)
    (hstage : ∀ w ∈ σ, fareyDenominator w ≤ n)
    (hSσ : supportFinset fareyComplex x.1 ⊆ σ)
    (p : ℚ) (hp : some p ∈ σ) (hpn : p.den = n)
    (hpgt : 1 < p.den)
    (t : ConeTime) :
    fareyStageStep n hn x t =
      fareyParentTriangleMove p hpgt x.1
        (hSσ.trans (fareyTopFace_subset_parentTriangle n hn σ hσ hstage
          p hp hpn hpgt)) t := by
  classical
  let hStri := hSσ.trans (fareyTopFace_subset_parentTriangle n hn σ hσ hstage
    p hp hpn hpgt)
  by_cases hpSupport : some p ∈ supportFinset fareyComplex x.1
  · exact fareyStageStep_eq_parentTriangleMove n hn x p hpSupport hpn hpgt hStri t
  · have hpzero : x.1.weight (some p) = 0 := by
      exact of_not_not (mt (mem_supportFinset_iff fareyComplex x.1 (some p)).2
        hpSupport)
    have hxlow : x.1 ∈ fareyStage (n - 1) := by
      intro w hw
      by_cases hz : x.1.weight w = 0
      · exact hz
      · have hmem : w ∈ supportFinset fareyComplex x.1 :=
          (mem_supportFinset_iff fareyComplex x.1 w).2 hz
        have hle : fareyDenominator w ≤ n := by
          exact hstage w (hSσ hmem)
        have hwt : fareyDenominator w = n := by omega
        have hwσ := hSσ hmem
        have heq := fareyFace_atMostOne_of_denominator_gt_one σ hσ.2 n hn
          w (some p) hwσ hp hwt (by simpa [fareyDenominator] using hpn)
        exact False.elim (hpSupport (heq ▸ hmem))
    calc
      fareyStageStep n hn x t = x.1 := fareyStageStep_fixed_of_lower n hn x hxlow t
      _ = fareyParentTriangleMove p hpgt x.1 hStri t :=
        (fareyParentTriangleMove_fixed p hpgt x.1 hStri hpzero t).symm

theorem fareyStageStep_top_zero (n : ℕ) (hn : 1 < n)
    (x : fareyStage n) (p : ℚ) (hpn : p.den = n) :
    (fareyStageStep n hn x ⟨1, by norm_num⟩).weight (some p) = 0 := by
  classical
  by_cases hp : some p ∈ supportFinset fareyComplex x.1
  · unfold fareyStageStep
    split
    · rename_i htop
      let q := Classical.choose htop
      have hq := Classical.choose_spec htop
      have hpq : p = q := by
        have hface := supportFinset_mem_faces fareyComplex x.1
        have heq := fareyFace_atMostOne_of_denominator_gt_one
          (supportFinset fareyComplex x.1) hface.2 n hn
          (some p) (some q) hp hq.1 (by simpa [fareyDenominator] using hpn)
          (by simpa [fareyDenominator] using hq.2)
        exact Option.some.inj heq
      subst p
      have hqgt : 1 < q.den := by rw [hq.2]; exact hn
      exact fareyParentTriangleMove_top_zero q hqgt x.1 _
    · exact False.elim (‹¬ ∃ p : ℚ, some p ∈ supportFinset fareyComplex x.1 ∧ p.den = n›
        ⟨p, hp, hpn⟩)
  · have hz : x.1.weight (some p) = 0 := by
      exact of_not_not (mt (mem_supportFinset_iff fareyComplex x.1 (some p)).2 hp)
    unfold fareyStageStep
    split
    · rename_i htop
      let q := Classical.choose htop
      have hq := Classical.choose_spec htop
      have hqgt : 1 < q.den := by rw [hq.2]; exact hn
      have hpq : p ≠ q := by
        intro heq
        apply hp
        rw [heq]
        exact hq.1
      rw [fareyParentTriangleMove_weight]
      have hpl : p ≠ (fareyParentData q hqgt).1 := by
        intro heq
        have hden := congrArg Rat.den heq
        have hs := fareyParentData_spec q hqgt
        have hlDen : (fareyParentData q hqgt).1.den < q.den := hs.1
        rw [hpn] at hden
        rw [hq.2] at hlDen
        omega
      have hpr : p ≠ (fareyParentData q hqgt).2 := by
        intro heq
        have hden := congrArg Rat.den heq
        have hs := fareyParentData_spec q hqgt
        have hrDen : (fareyParentData q hqgt).2.den < q.den := hs.2.1
        rw [hpn] at hden
        rw [hq.2] at hrDen
        omega
      simp only [Option.some.injEq]
      split_ifs with h1 h2 h3
      all_goals try exact False.elim (hpq h1)
      all_goals try exact False.elim (hpl h2)
      all_goals try exact False.elim (hpr h3)
      all_goals simp [hz]
    · exact hz

theorem fareyStageStep_maps_down (n : ℕ) (hn : 1 < n)
    (x : fareyStage n) :
    fareyStageStep n hn x ⟨1, by norm_num⟩ ∈ fareyStage (n - 1) := by
  classical
  intro w hw
  have hnle : n - 1 < n := by omega
  by_cases hwn : fareyDenominator w = n
  · cases w with
    | none =>
        simp [fareyDenominator] at hwn
        omega
    | some p =>
        have hpn : p.den = n := hwn
        exact fareyStageStep_top_zero n hn x p hpn
  · have hnlt : n < fareyDenominator w := by
      have hnot : ¬ fareyDenominator w ≤ n - 1 := hw
      omega
    have hxzero : x.1.weight w = 0 := x.property w (by omega)
    unfold fareyStageStep
    split
    · rename_i htop
      let p := Classical.choose htop
      have hp := Classical.choose_spec htop
      have hpgt : 1 < p.den := by rw [hp.2]; exact hn
      rw [fareyParentTriangleMove_weight]
      have hwp : w ≠ some p := by
        intro heq
        subst w
        change n < p.den at hnlt
        rw [hp.2] at hnlt
        omega
      have hwl : w ≠ some (fareyParentData p hpgt).1 := by
        intro heq
        subst w
        have hs := fareyParentData_spec p hpgt
        change n < (fareyParentData p hpgt).1.den at hnlt
        have hsmall : (fareyParentData p hpgt).1.den < p.den := hs.1
        rw [hp.2] at hsmall
        omega
      have hwr : w ≠ some (fareyParentData p hpgt).2 := by
        intro heq
        subst w
        have hs := fareyParentData_spec p hpgt
        change n < (fareyParentData p hpgt).2.den at hnlt
        have hsmall : (fareyParentData p hpgt).2.den < p.den := hs.2.1
        rw [hp.2] at hsmall
        omega
      split_ifs with h1 h2 h3
      all_goals try exact False.elim (hwp h1)
      all_goals try exact False.elim (hwl h2)
      all_goals try exact False.elim (hwr h3)
      all_goals simp [hxzero]
    · exact hxzero

theorem fareyParentTriangleMove_mem_stage
    (n : ℕ) (p : ℚ) (hp : 1 < p.den) (hpn : p.den = n)
    (x : RealizationPoint fareyComplex)
    (hx : supportFinset fareyComplex x ⊆ fareyParentTriangle p hp)
    (t : ConeTime) :
    fareyParentTriangleMove p hp x hx t ∈ fareyStage n := by
  classical
  intro w hw
  have hnot : w ∉ fareyParentTriangle p hp := by
    intro hmem
    simp only [fareyParentTriangle, Finset.mem_insert,
      Finset.mem_singleton] at hmem
    rcases hmem with hwp | hwl | hwr
    · subst w
      exact hw (by simp [fareyDenominator, hpn])
    · subst w
      have hs := fareyParentData_spec p hp
      have hsmall : (fareyParentData p hp).1.den < p.den := hs.1
      apply hw
      change (fareyParentData p hp).1.den ≤ n
      omega
    · subst w
      have hs := fareyParentData_spec p hp
      have hsmall : (fareyParentData p hp).2.den < p.den := hs.2.1
      apply hw
      change (fareyParentData p hp).2.den ≤ n
      omega
  unfold fareyParentTriangleMove
  exact faceInclusion_weight_of_not_mem fareyComplex
    (fareyParentTriangle p hp) (fareyParentTriangle_face p hp) _ w hnot

theorem fareyStageStep_mem_stage (n : ℕ) (hn : 1 < n)
    (x : fareyStage n) (t : ConeTime) :
    fareyStageStep n hn x t ∈ fareyStage n := by
  classical
  unfold fareyStageStep
  split
  · rename_i htop
    let p := Classical.choose htop
    have hp := Classical.choose_spec htop
    have hpgt : 1 < p.den := by rw [hp.2]; exact hn
    exact fareyParentTriangleMove_mem_stage n p hpgt hp.2 x.1 _ t
  · exact x.2

noncomputable def fareyStageStepHomotopy (n : ℕ) (hn : 1 < n) :
    fareyStage n × ConeTime → fareyStage n := fun q =>
  ⟨fareyStageStep n hn q.1 q.2, fareyStageStep_mem_stage n hn q.1 q.2⟩

theorem fareyStageStepHomotopy_zero (n : ℕ) (hn : 1 < n)
    (x : fareyStage n) :
    fareyStageStepHomotopy n hn (x, ⟨0, by norm_num⟩) = x := by
  apply Subtype.ext
  exact fareyStageStep_zero n hn x

theorem fareyStageStepHomotopy_one (n : ℕ) (hn : 1 < n)
    (x : fareyStage n) :
    (fareyStageStepHomotopy n hn (x, ⟨1, by norm_num⟩)).1 ∈
      fareyStage (n - 1) :=
  fareyStageStep_maps_down n hn x

theorem fareyStageStepHomotopy_fixed_of_lower
    (n : ℕ) (hn : 1 < n) (x : fareyStage n)
    (hx : x.1 ∈ fareyStage (n - 1)) (t : ConeTime) :
    fareyStageStepHomotopy n hn (x, t) = x := by
  apply Subtype.ext
  exact fareyStageStep_fixed_of_lower n hn x hx t

end CurveComplexGenusTwo.Topology
