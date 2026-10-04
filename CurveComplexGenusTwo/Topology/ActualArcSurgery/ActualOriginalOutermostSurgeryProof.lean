import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import CurveComplexGenusTwo.Topology.WeightedSurgery.RawSpliceHelperHeaders
import CurveComplexGenusTwo.Topology.Smoothing.FiniteSupportedPatchAssemblyProof
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingSlidePlane
import CurveComplexGenusTwo.Topology.IntersectionParity.CutTransition
import Mathlib.Topology.Order.IntermediateValue
import Schoenflies.Subarc
import CurveComplexGenusTwo.Topology.ChartLift
import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Topology.CompletedJordan
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import Schoenflies.ModelCurve
import Schoenflies.JordanSchoenflies
import Mathlib.Topology.MetricSpace.HausdorffDistance
open Set Topology Schoenflies Metric Filter
open CurveComplex
set_option maxHeartbeats 20000000
open Lean Elab Tactic in
elab "audit_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in anonymous probe: {ax}"
  logInfo m!"Anonymous proof base-3 audit: {found.toList}"

namespace CurveComplex.HyperellipticModel.ArcSurgery
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance originalAcyclicSurgeryDecidableEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
open CurveComplex.ActualCrossingSlide
set_option maxHeartbeats 100000000

private theorem actualSourceSurgery_tailChart_1 (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
(F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
(x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
(hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
(side : Bool) 
(v : S) (hv : v ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected))
(hvFirst : v ≠ anchor.val.map x.t) :
∃ (U : Set S) (hU : IsOpen U) (hp : v ∈ U),
  ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
    (e ⟨v,hp⟩).val=(0,0) ∧
    (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
    (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
  ∃ c : OpenPartialHomeomorph S (ℝ × ℝ), c.source ⊆ U ∧
    (∀ z : U, c z.val=(e z).val) ∧ v ∈ c.source ∧ c v=(0,0) ∧
  Disjoint c.source (M.cover.branch : Set S) ∧
  (∀ z ∈ c.source, z ∈ anchor.val.image ↔ (c z).2=0) ∧
  (∀ z ∈ c.source, z ∈ (P.rep x.selected).val.image ↔ (c z).1=0) ∧
  (∀ z ∈ c.source, z ∈ (raw side).image ↔ (c z).1=0) ∧ (∀ z ∈ c.source, z ∉ (raw (!side)).image) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have separation (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
  (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
  (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
  (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
  (side : Bool) :
  Disjoint (((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t})
    (raw (!side)).image := by
    have closed (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
    (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
    (side : Bool) :
    (raw side).image ∩ crossings M anchor (P.rep x.selected) =
      crossings M anchor (P.rep x.selected) ∩
        (P.rep x.selected).val.map '' {r : Interval |
          if side then x.s.val ≤ r.val else r.val ≤ x.s.val} := by
      ext z
      constructor
      · rintro ⟨hz,hc⟩
        refine ⟨hc,?_⟩
        rw [hraw] at hz
        rcases hz with ⟨r,hr,he⟩ | ht
        · have hzero : r.val ≠ 0 := by
            intro h
            have hr0 : r = (0 : Interval) := Subtype.ext h
            exact hc.1.2 (he ▸ hr0 ▸ anchor.val.start_marked)
          have hrpos : 0 < r.val := lt_of_le_of_ne r.property.1 hzero.symm
          have hrEq : r = x.t := by
            apply Subtype.ext
            apply le_antisymm hr
            by_contra hn
            have hlt : r.val < x.t.val := lt_of_not_ge hn
            exact x.first x.selected r hrpos hlt (he.symm ▸ hc.2)
          refine ⟨x.s,?_,?_⟩
          · cases side <;> simp
          · exact x.same_point.symm.trans ((congrArg anchor.val.map hrEq.symm).trans he)
        · exact ht
      · rintro ⟨hc,ht⟩
        refine ⟨?_,hc⟩
        rw [hraw]
        exact Or.inr ht
    apply disjoint_left.mpr
    rintro z ⟨⟨hz,hc⟩,hn⟩ hzOther
    have hzClosed : z ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected) := ⟨hz,hc⟩
    have hzOtherClosed : z ∈ (raw (!side)).image ∩ crossings M anchor (P.rep x.selected) := ⟨hzOther,hc⟩
    rw [closed M anchor F P x raw hraw side] at hzClosed
    rw [closed M anchor F P x raw hraw (!side)] at hzOtherClosed
    obtain ⟨_,r,hr,he⟩ := hzClosed
    obtain ⟨_,u,hu,he'⟩ := hzOtherClosed
    have hru : r=u := by
      rcases (P.rep x.selected).val.injective_except_loop_closure r u (he.trans he'.symm)
        with h | h | h
      · exact h
      · exact False.elim (hc.2.2 (he ▸ h.1 ▸ (P.rep x.selected).val.start_marked))
      · exact False.elim (hc.2.2 (he ▸ h.1 ▸ (P.rep x.selected).val.end_marked))
    have hrs : r=x.s := by
      apply Subtype.ext
      rw [←hru] at hu
      cases side <;> simp only [mem_setOf_eq,Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hr hu
      · exact le_antisymm hr hu
      · exact le_antisymm hu hr
    apply hn
    apply mem_singleton_iff.mpr
    exact he.symm.trans ((congrArg (P.rep x.selected).val.map hrs).trans x.same_point.symm)
  have hvOther : v ∉ (raw (!side)).image := by
    intro h
    exact disjoint_left.mp (separation M anchor F P x raw hraw side)
      ⟨hv,fun he => hvFirst (mem_singleton_iff.mp he)⟩ h
  obtain ⟨U,hU,hp,hmarks,e,he,ha,hb⟩ := P.transverse x.selected v hv.2
  let Q : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
  have hQ : IsOpen Q :=
    (isOpen_lt continuous_fst.abs continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)
  let coeU : OpenPartialHomeomorph U S :=
    (⟨U,hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe ⟨⟨v,hp⟩⟩
  let coeQ : OpenPartialHomeomorph Q (ℝ × ℝ) :=
    (⟨Q,hQ⟩ : TopologicalSpace.Opens (ℝ × ℝ)).openPartialHomeomorphSubtypeCoe
      ⟨⟨(0,0),by simp [Q]⟩⟩
  let d := coeU.symm.trans (e.toOpenPartialHomeomorph.trans coeQ)
  have dsource (z : S) : z ∈ d.source ↔ z ∈ U := by
    simp [d,OpenPartialHomeomorph.trans_source,coeU,coeQ]
  have dapply (z : U) : d z.val=(e z).val := by
    have cinv : coeU.symm z.val=z := coeU.left_inv (by simp [coeU])
    change (e (coeU.symm z.val)).val=(e z).val
    rw [cinv]
  let T := ((raw (!side)).image)ᶜ
  letI : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc
  have hT : IsOpen T := (isCompact_range (raw (!side)).continuous).isClosed.isOpen_compl
  let c := d.restrOpen T hT
  have csource (z : S) : z ∈ c.source ↔ z ∈ U ∧ z ∉ (raw (!side)).image := by
    change z ∈ d.source ∩ T ↔ _
    rw [mem_inter_iff,dsource]
    rfl
  have capply (z : U) : c z.val=(e z).val := dapply z
  have rawEq (z : S) (hz : z ∉ (raw (!side)).image) :
      z ∈ (raw side).image ↔ z ∈ (P.rep x.selected).val.image := by
    constructor
    · intro h
      rw [hraw] at h
      rcases h with ⟨t,ht,he⟩ | ⟨t,ht,he⟩
      · exact False.elim (hz (by rw [hraw]; exact Or.inl ⟨t,ht,he⟩))
      · exact ⟨t,he⟩
    · rintro ⟨t,he⟩
      cases side
      · by_cases ht : t.val ≤ x.s.val
        · rw [hraw]; exact Or.inr ⟨t,ht,he⟩
        · exact False.elim (hz (by rw [hraw]; exact Or.inr ⟨t,(le_of_not_ge ht),he⟩))
      · by_cases ht : x.s.val ≤ t.val
        · rw [hraw]; exact Or.inr ⟨t,ht,he⟩
        · exact False.elim (hz (by rw [hraw]; exact Or.inr ⟨t,(le_of_not_ge ht),he⟩))
  refine ⟨U,hU,hp,e,he,ha,hb,c,(fun z hz => ((csource z).mp hz).1),capply,(csource v).mpr ⟨hp,hvOther⟩,?_,?_,?_,?_,?_,(fun z hz => ((csource z).mp hz).2)⟩
  · exact (capply ⟨v,hp⟩).trans he
  · exact hmarks.mono_left (fun z hz => ((csource z).mp hz).1)
  · intro z hz
    have hu := ((csource z).mp hz).1
    rw [capply ⟨z,hu⟩]
    exact ha ⟨z,hu⟩
  · intro z hz
    have hu := ((csource z).mp hz).1
    rw [capply ⟨z,hu⟩]
    exact hb ⟨z,hu⟩
  · intro z hz
    have hu := ((csource z).mp hz).1
    rw [rawEq z ((csource z).mp hz).2,capply ⟨z,hu⟩]
    exact hb ⟨z,hu⟩

private theorem actualSourceSurgery_tailChart_2 (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
(F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
(x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
(hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
(side : Bool) 
(v : S) (hv : v ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected))
(hvFirst : v ≠ anchor.val.map x.t) :
∃ (U : Set S) (hU : IsOpen U) (hp : v ∈ U),
  ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
    (e ⟨v,hp⟩).val=(0,0) ∧
    (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
    (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
  ∃ c : OpenPartialHomeomorph S (ℝ × ℝ), c.source ⊆ U ∧
    (∀ z : U, c z.val=(e z).val) ∧ v ∈ c.source ∧ c v=(0,0) ∧
  Disjoint c.source (M.cover.branch : Set S) ∧
  (∀ z ∈ c.source, z ∈ anchor.val.image ↔ (c z).2=0) ∧
  (∀ z ∈ c.source, z ∈ (P.rep x.selected).val.image ↔ (c z).1=0) ∧
  (∀ z ∈ c.source, z ∈ (raw side).image ↔ (c z).1=0) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have separation (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
  (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
  (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
  (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
  (side : Bool) :
  Disjoint (((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t})
    (raw (!side)).image := by
    have closed (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
    (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
    (side : Bool) :
    (raw side).image ∩ crossings M anchor (P.rep x.selected) =
      crossings M anchor (P.rep x.selected) ∩
        (P.rep x.selected).val.map '' {r : Interval |
          if side then x.s.val ≤ r.val else r.val ≤ x.s.val} := by
      ext z
      constructor
      · rintro ⟨hz,hc⟩
        refine ⟨hc,?_⟩
        rw [hraw] at hz
        rcases hz with ⟨r,hr,he⟩ | ht
        · have hzero : r.val ≠ 0 := by
            intro h
            have hr0 : r = (0 : Interval) := Subtype.ext h
            exact hc.1.2 (he ▸ hr0 ▸ anchor.val.start_marked)
          have hrpos : 0 < r.val := lt_of_le_of_ne r.property.1 hzero.symm
          have hrEq : r = x.t := by
            apply Subtype.ext
            apply le_antisymm hr
            by_contra hn
            have hlt : r.val < x.t.val := lt_of_not_ge hn
            exact x.first x.selected r hrpos hlt (he.symm ▸ hc.2)
          refine ⟨x.s,?_,?_⟩
          · cases side <;> simp
          · exact x.same_point.symm.trans ((congrArg anchor.val.map hrEq.symm).trans he)
        · exact ht
      · rintro ⟨hc,ht⟩
        refine ⟨?_,hc⟩
        rw [hraw]
        exact Or.inr ht
    apply disjoint_left.mpr
    rintro z ⟨⟨hz,hc⟩,hn⟩ hzOther
    have hzClosed : z ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected) := ⟨hz,hc⟩
    have hzOtherClosed : z ∈ (raw (!side)).image ∩ crossings M anchor (P.rep x.selected) := ⟨hzOther,hc⟩
    rw [closed M anchor F P x raw hraw side] at hzClosed
    rw [closed M anchor F P x raw hraw (!side)] at hzOtherClosed
    obtain ⟨_,r,hr,he⟩ := hzClosed
    obtain ⟨_,u,hu,he'⟩ := hzOtherClosed
    have hru : r=u := by
      rcases (P.rep x.selected).val.injective_except_loop_closure r u (he.trans he'.symm)
        with h | h | h
      · exact h
      · exact False.elim (hc.2.2 (he ▸ h.1 ▸ (P.rep x.selected).val.start_marked))
      · exact False.elim (hc.2.2 (he ▸ h.1 ▸ (P.rep x.selected).val.end_marked))
    have hrs : r=x.s := by
      apply Subtype.ext
      rw [←hru] at hu
      cases side <;> simp only [mem_setOf_eq,Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hr hu
      · exact le_antisymm hr hu
      · exact le_antisymm hu hr
    apply hn
    apply mem_singleton_iff.mpr
    exact he.symm.trans ((congrArg (P.rep x.selected).val.map hrs).trans x.same_point.symm)
  have hvOther : v ∉ (raw (!side)).image := by
    intro h
    exact disjoint_left.mp (separation M anchor F P x raw hraw side)
      ⟨hv,fun he => hvFirst (mem_singleton_iff.mp he)⟩ h
  obtain ⟨U,hU,hp,hmarks,e,he,ha,hb⟩ := P.transverse x.selected v hv.2
  let Q : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
  have hQ : IsOpen Q :=
    (isOpen_lt continuous_fst.abs continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)
  let coeU : OpenPartialHomeomorph U S :=
    (⟨U,hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe ⟨⟨v,hp⟩⟩
  let coeQ : OpenPartialHomeomorph Q (ℝ × ℝ) :=
    (⟨Q,hQ⟩ : TopologicalSpace.Opens (ℝ × ℝ)).openPartialHomeomorphSubtypeCoe
      ⟨⟨(0,0),by simp [Q]⟩⟩
  let d := coeU.symm.trans (e.toOpenPartialHomeomorph.trans coeQ)
  have dsource (z : S) : z ∈ d.source ↔ z ∈ U := by
    simp [d,OpenPartialHomeomorph.trans_source,coeU,coeQ]
  have dapply (z : U) : d z.val=(e z).val := by
    have cinv : coeU.symm z.val=z := coeU.left_inv (by simp [coeU])
    change (e (coeU.symm z.val)).val=(e z).val
    rw [cinv]
  let T := ((raw (!side)).image)ᶜ
  letI : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc
  have hT : IsOpen T := (isCompact_range (raw (!side)).continuous).isClosed.isOpen_compl
  let c := d.restrOpen T hT
  have csource (z : S) : z ∈ c.source ↔ z ∈ U ∧ z ∉ (raw (!side)).image := by
    change z ∈ d.source ∩ T ↔ _
    rw [mem_inter_iff,dsource]
    rfl
  have capply (z : U) : c z.val=(e z).val := dapply z
  have rawEq (z : S) (hz : z ∉ (raw (!side)).image) :
      z ∈ (raw side).image ↔ z ∈ (P.rep x.selected).val.image := by
    constructor
    · intro h
      rw [hraw] at h
      rcases h with ⟨t,ht,he⟩ | ⟨t,ht,he⟩
      · exact False.elim (hz (by rw [hraw]; exact Or.inl ⟨t,ht,he⟩))
      · exact ⟨t,he⟩
    · rintro ⟨t,he⟩
      cases side
      · by_cases ht : t.val ≤ x.s.val
        · rw [hraw]; exact Or.inr ⟨t,ht,he⟩
        · exact False.elim (hz (by rw [hraw]; exact Or.inr ⟨t,(le_of_not_ge ht),he⟩))
      · by_cases ht : x.s.val ≤ t.val
        · rw [hraw]; exact Or.inr ⟨t,ht,he⟩
        · exact False.elim (hz (by rw [hraw]; exact Or.inr ⟨t,(le_of_not_ge ht),he⟩))
  refine ⟨U,hU,hp,e,he,ha,hb,c,(fun z hz => ((csource z).mp hz).1),capply,(csource v).mpr ⟨hp,hvOther⟩,?_,?_,?_,?_,?_⟩
  · exact (capply ⟨v,hp⟩).trans he
  · exact hmarks.mono_left (fun z hz => ((csource z).mp hz).1)
  · intro z hz
    have hu := ((csource z).mp hz).1
    rw [capply ⟨z,hu⟩]
    exact ha ⟨z,hu⟩
  · intro z hz
    have hu := ((csource z).mp hz).1
    rw [capply ⟨z,hu⟩]
    exact hb ⟨z,hu⟩
  · intro z hz
    have hu := ((csource z).mp hz).1
    rw [rawEq z ((csource z).mp hz).2,capply ⟨z,hu⟩]
    exact hb ⟨z,hu⟩

private theorem actualSourceSurgery_chart_3 (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
(F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
(x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
(hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
(side : Bool) :
∃ (U : Set S) (hU : IsOpen U) (hp : anchor.val.map x.t ∈ U),
  ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
  (e ⟨anchor.val.map x.t,hp⟩).val=(0,0) ∧
  (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
  (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
  ∃ k : OpenPartialHomeomorph S (ℝ × ℝ),
    anchor.val.map x.t ∈ k.source ∧ k.source ⊆ U ∧
    (∀ z ∈ k.source, z ∈ (raw side).image ↔ (k z).1=0) ∧
    ∀ z : U, z.val ∈ k.source →
      (0 < (k z.val).1 ↔ (e z).val.1 < 0 ∧
        (if side then 0 < (e z).val.2 else (e z).val.2 < 0)) := by
  have firstElbowTrace : ∀ (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
      (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
      (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
      (V : Set S) (hV : IsOpen V) (hpV : anchor.val.map x.t ∈ V)
      (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side),
      ∃ U : Set S, ∃ hU : IsOpen U, ∃ hp : anchor.val.map x.t ∈ U,
        Disjoint U (M.cover.branch : Set S) ∧
        ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
        (e ⟨anchor.val.map x.t,hp⟩).val = (0,0) ∧
        (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
        (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
        ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        (∀ z : U, |(e z).val.1| ≤ δ → |(e z).val.2| ≤ δ → z.val ∈ V) ∧
        ∀ side (z : U), |(e z).val.1| ≤ δ → |(e z).val.2| ≤ δ →
          (z.val ∈ (raw side).image ↔
            ((e z).val.2 = 0 ∧ (e z).val.1 ≤ 0) ∨
            ((e z).val.1 = 0 ∧ (if side then 0 ≤ (e z).val.2 else (e z).val.2 ≤ 0))) := by
    intro M anchor F P x raw V hV hpV hraw
    have prefixTrace : ∀ (M : HyperellipticModel E S) (a : MarkedArc M)
        (t : Interval) (ht0 : 0 < t.val) (ht1 : t.val < 1)
        (U : Set S) (hU : IsOpen U) (hp : a.map t ∈ U)
        (e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1})
        (he : (e ⟨a.map t,hp⟩).val = (0,0))
        (haxis : ∀ z : U, z.val ∈ a.image ↔ (e z).val.2 = 0),
        ∃ W : Set S, IsOpen W ∧ a.map t ∈ W ∧ W ⊆ U ∧
          Disjoint W (M.cover.branch : Set S) ∧ ∃ direction : Bool,
          ∀ z : U, z.val ∈ W →
            (z.val ∈ a.map '' {r : Interval | r.val ≤ t.val} ↔
              (e z).val.2 = 0 ∧
                (if direction then (e z).val.1 ≤ 0 else 0 ≤ (e z).val.1)) := by
      intro M a t ht0 ht1 U hU hp e he haxis
      have orient : ∀ (M : HyperellipticModel E S) (a : MarkedArc M)
          (t : Interval) (ht0 : 0 < t.val) (ht1 : t.val < 1)
          (U : Set S) (hU : IsOpen U) (hp : a.map t ∈ U)
          (e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1})
          (he : (e ⟨a.map t,hp⟩).val = (0,0))
          (haxis : ∀ z : U, z.val ∈ a.image ↔ (e z).val.2 = 0),
          ∃ δ : ℝ, 0 < δ ∧ δ < t.val ∧ δ < 1-t.val ∧
            ∃ hin : ∀ r : Interval, |r.val-t.val| ≤ δ → a.map r ∈ U,
            ((∀ r : Interval, ∀ hr : |r.val-t.val| ≤ δ,
              (e ⟨a.map r,hin r hr⟩).val.1 ≤ 0 ↔ r.val ≤ t.val) ∨
             (∀ r : Interval, ∀ hr : |r.val-t.val| ≤ δ,
              0 ≤ (e ⟨a.map r,hin r hr⟩).val.1 ↔ r.val ≤ t.val)) := by
        intro M a t ht0 ht1 U hU hp e he haxis
        have ho : IsOpen (a.map ⁻¹' U) := hU.preimage a.continuous
        obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp ho t hp
        let δ : ℝ := min R (min t.val (1-t.val))/4
        have hd : 0 < δ := by dsimp [δ]; positivity
        have hdR : δ < R := by dsimp [δ]; have := min_le_left R (min t.val (1-t.val)); linarith
        have hdt : δ < t.val := by dsimp [δ]; have := (min_le_right R (min t.val (1-t.val))).trans (min_le_left t.val (1-t.val)); linarith
        have hd1 : δ < 1-t.val := by dsimp [δ]; have := (min_le_right R (min t.val (1-t.val))).trans (min_le_right t.val (1-t.val)); linarith
        have hin (r : Interval) (hr : |r.val-t.val| ≤ δ) : a.map r ∈ U := by
          apply hball
          rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
          exact hr.trans_lt hdR
        let param : Interval → Interval := fun r => ⟨t.val+δ*(2*r.val-1),by
          constructor <;> nlinarith [r.property.1,r.property.2]⟩
        have bounds (r : Interval) : |(param r).val-t.val| ≤ δ := by
          rw [abs_le]
          dsimp [param]
          constructor <;> nlinarith [r.property.1,r.property.2]
        have pint (r : Interval) : 0 < (param r).val ∧ (param r).val < 1 := by
          have hh := abs_le.mp (bounds r)
          constructor <;> linarith
        have pc : Continuous param := by dsimp [param]; fun_prop
        let lift : Interval → U := fun r => ⟨a.map (param r),hin (param r) (bounds r)⟩
        have lc : Continuous lift := (a.continuous.comp pc).subtype_mk _
        let f : C(Interval,ℝ) := ⟨fun r => (e (lift r)).val.1,by fun_prop⟩
        have fi : Function.Injective f := by
          intro r s hh
          have hye (r : Interval) : (e (lift r)).val.2 = 0 := (haxis (lift r)).mp (mem_range_self (param r))
          have heq : e (lift r) = e (lift s) := Subtype.ext (Prod.ext hh ((hye r).trans (hye s).symm))
          have hval := congrArg Subtype.val (e.injective heq)
          rcases a.injective_except_loop_closure (param r) (param s) hval with hh | hh | hh
          · apply Subtype.ext
            have hpq := congrArg Subtype.val hh
            dsimp [param] at hpq
            nlinarith
          · have hz := congrArg Subtype.val hh.1
            have hpos := (pint r).1
            change (param r).val = 0 at hz
            linarith
          · have hz := congrArg Subtype.val hh.1
            have hpos := (pint r).2
            change (param r).val = 1 at hz
            linarith
        let mid : Interval := ⟨1/2,by norm_num⟩
        have pmid : param mid = t := by apply Subtype.ext; dsimp [param,mid]; ring
        have fmid : f mid = 0 := by
          have hle : lift mid = ⟨a.map t,hp⟩ := by apply Subtype.ext; dsimp [lift]; rw [pmid]
          change (e (lift mid)).val.1 = 0
          rw [hle,he]
        have back (r : Interval) (hr : |r.val-t.val| ≤ δ) :
            ∃ q : Interval, param q = r ∧ (q ≤ mid ↔ r.val ≤ t.val) := by
          have hh := abs_le.mp hr
          let q : Interval := ⟨(r.val-t.val+δ)/(2*δ),by
            constructor
            · exact div_nonneg (by linarith) (by positivity)
            · apply (div_le_iff₀ (by positivity : 0 < 2*δ)).mpr
              linarith⟩
          refine ⟨q,?_,?_⟩
          · apply Subtype.ext
            dsimp [param,q]
            field_simp
            ring
          · change (r.val-t.val+δ)/(2*δ) ≤ 1/2 ↔ r.val ≤ t.val
            rw [div_le_iff₀ (by positivity : 0 < 2*δ)]
            constructor <;> intro hh <;> linarith
        refine ⟨δ,hd,hdt,hd1,hin,?_⟩
        rcases f.continuous.strictMono_of_inj_boundedOrder' fi with hm | hm
        · left
          intro r hr
          obtain ⟨q,hq,hqm⟩ := back r hr
          have hf : f q = (e ⟨a.map r,hin r hr⟩).val.1 := by
            have hl : lift q = ⟨a.map r,hin r hr⟩ := Subtype.ext (congrArg a.map hq)
            exact congrArg (fun z : U => (e z).val.1) hl
          rw [←hf,←fmid,hm.le_iff_le,hqm]
        · right
          intro r hr
          obtain ⟨q,hq,hqm⟩ := back r hr
          have hf : f q = (e ⟨a.map r,hin r hr⟩).val.1 := by
            have hl : lift q = ⟨a.map r,hin r hr⟩ := Subtype.ext (congrArg a.map hq)
            exact congrArg (fun z : U => (e z).val.1) hl
          rw [←hf,←fmid,hm.le_iff_ge,hqm]
      have isolate : ∀ (M : HyperellipticModel E S) (a b : MarkedArc M)
          (t s : Interval) (ht0 : 0 < t.val) (ht1 : t.val < 1)
          (hs0 : 0 < s.val) (hs1 : s.val < 1)
          (he : a.map t = b.map s) (ε : ℝ) (hε : 0 < ε)
          (V : Set S) (hV : IsOpen V) (hpV : a.map t ∈ V),
          ∃ W : Set S, IsOpen W ∧ a.map t ∈ W ∧ W ⊆ V ∧
            Disjoint W (M.cover.branch : Set S) ∧
            (∀ r : Interval, a.map r ∈ W → |r.val-t.val| < ε) ∧
            (∀ r : Interval, b.map r ∈ W → |r.val-s.val| < ε) := by
        intro M a b t s ht0 ht1 hs0 hs1 he ε hε V hV hpV
        classical
        letI : T2Space S := M.sphere.symm.t2Space
        letI : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc
        have isolate (a : MarkedArc M) (t : Interval) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
            ∃ K : Set S, IsClosed K ∧ a.map t ∉ K ∧
              ∀ r : Interval, ε ≤ |r.val-t.val| → a.map r ∈ K := by
          let D : Set Interval := {r | ε ≤ |r.val-t.val|}
          have hD : IsClosed D := isClosed_le continuous_const (continuous_subtype_val.sub continuous_const).abs
          let K : Set S := a.map '' D
          have hK : IsClosed K := (hD.isCompact.image a.continuous).isClosed
          refine ⟨K,hK,?_,fun r hr => mem_image_of_mem a.map hr⟩
          rintro ⟨r,hr,he⟩
          rcases a.injective_except_loop_closure r t he with he | he | he
          · subst r
            have hh : ε ≤ |t.val-t.val| := hr
            simp only [sub_self,abs_zero] at hh
            linarith
          · have hh := congrArg Subtype.val he.2
            change t.val = 1 at hh
            linarith
          · have hh := congrArg Subtype.val he.2
            change t.val = 0 at hh
            linarith
        obtain ⟨A,hA,hpA,hcoverA⟩ := isolate a t ht0 ht1
        obtain ⟨B,hB,hpB,hcoverB⟩ := isolate b s hs0 hs1
        have hmarks : IsClosed (M.cover.branch : Set S) := M.cover.branch.finite_toSet.isClosed
        have hpm : a.map t ∉ (M.cover.branch : Set S) := by
          intro hm
          rcases a.marked_only_at_ends t hm with hh | hh
          · have := congrArg Subtype.val hh
            change t.val = 0 at this
            linarith
          · have := congrArg Subtype.val hh
            change t.val = 1 at this
            linarith
        let W := V ∩ Aᶜ ∩ Bᶜ ∩ (M.cover.branch : Set S)ᶜ
        have hW : IsOpen W := ((hV.inter hA.isOpen_compl).inter hB.isOpen_compl).inter hmarks.isOpen_compl
        have hpW : a.map t ∈ W := ⟨⟨⟨hpV,hpA⟩,he ▸ hpB⟩,hpm⟩
        refine ⟨W,hW,hpW,fun r hr => hr.1.1.1,?_,?_,?_⟩
        · exact Set.disjoint_left.mpr (fun r hr hm => hr.2 hm)
        · intro r hr
          by_contra hh
          exact hr.1.1.2 (hcoverA r (not_lt.mp hh))
        · intro r hr
          by_contra hh
          exact hr.1.2 (hcoverB r (not_lt.mp hh))
      obtain ⟨δ,hd,hdt,hd1,hin,hdir⟩ := orient M a t ht0 ht1 U hU hp e he haxis
      obtain ⟨W,hW,hpW,hWU,hm,hnear,_⟩ := isolate M a a t t ht0 ht1 ht0 ht1 rfl δ hd U hU hp
      refine ⟨W,hW,hpW,hWU,hm,?_⟩
      have build (direction : Bool)
          (ho : ∀ r : Interval, ∀ hr : |r.val-t.val| ≤ δ,
            (if direction then (e ⟨a.map r,hin r hr⟩).val.1 ≤ 0 else 0 ≤ (e ⟨a.map r,hin r hr⟩).val.1) ↔ r.val ≤ t.val) :
          ∀ z : U, z.val ∈ W →
            (z.val ∈ a.map '' {r : Interval | r.val ≤ t.val} ↔
              (e z).val.2 = 0 ∧ (if direction then (e z).val.1 ≤ 0 else 0 ≤ (e z).val.1)) := by
        intro z hz
        constructor
        · rintro ⟨r,hr,heq⟩
          have hrW : a.map r ∈ W := heq.symm ▸ hz
          have hrnear := (hnear r hrW).le
          have hl : (⟨a.map r,hin r hrnear⟩ : U) = z := Subtype.ext heq
          refine ⟨(haxis z).mp ⟨r,heq⟩,?_⟩
          have hh := (ho r hrnear).mpr hr
          simpa only [hl] using hh
        · rintro ⟨hzy,hzx⟩
          obtain ⟨r,heq⟩ := (haxis z).mpr hzy
          have hrW : a.map r ∈ W := heq.symm ▸ hz
          have hrnear := (hnear r hrW).le
          have hl : (⟨a.map r,hin r hrnear⟩ : U) = z := Subtype.ext heq
          refine ⟨r,(ho r hrnear).mp ?_,heq⟩
          simpa only [hl] using hzx
      rcases hdir with hdir | hdir
      · exact ⟨true,build true (by simpa only [ite_true] using hdir)⟩
      · exact ⟨false,build false (by simpa only [Bool.false_eq_true,ite_false] using hdir)⟩
    have suffixTrace : ∀ (M : HyperellipticModel E S) (a : MarkedArc M)
        (t : Interval) (ht0 : 0 < t.val) (ht1 : t.val < 1)
        (U : Set S) (hp : a.map t ∈ U)
        (e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1})
        (he : (e ⟨a.map t,hp⟩).val = (0,0))
        (haxis : ∀ z : U, z.val ∈ a.image ↔ (e z).val.2 = 0)
        (W : Set S) (hm : Disjoint W (M.cover.branch : Set S)) (direction : Bool)
        (hprefix : ∀ z : U, z.val ∈ W →
          (z.val ∈ a.map '' {r : Interval | r.val ≤ t.val} ↔
            (e z).val.2 = 0 ∧ (if direction then (e z).val.1 ≤ 0 else 0 ≤ (e z).val.1))),
        ∀ z : U, z.val ∈ W →
          (z.val ∈ a.map '' {r : Interval | t.val ≤ r.val} ↔
            (e z).val.2 = 0 ∧ (if direction then 0 ≤ (e z).val.1 else (e z).val.1 ≤ 0)) := by
      intro M a t ht0 ht1 U hp e he haxis W hm direction hprefix
      intro z hz
      have hzmark : z.val ∉ (M.cover.branch : Set S) := Set.disjoint_left.mp hm hz
      have zero (hzy : (e z).val.2 = 0) : (e z).val.1 = 0 ↔ z.val = a.map t := by
        constructor
        · intro hx
          have hze : e z = e ⟨a.map t,hp⟩ := Subtype.ext (by rw [he]; exact Prod.ext hx hzy)
          exact congrArg Subtype.val (e.injective hze)
        · intro hx
          have hze : z = ⟨a.map t,hp⟩ := Subtype.ext hx
          rw [hze,he]
      have unique (r s : Interval) (hr : a.map r = z.val) (hs : a.map s = z.val) : r = s := by
        rcases a.injective_except_loop_closure r s (hr.trans hs.symm) with he | he | he
        · exact he
        · apply False.elim
          apply hzmark
          rw [←hr,he.1]
          exact a.start_marked
        · apply False.elim
          apply hzmark
          rw [←hr,he.1]
          exact a.end_marked
      constructor
      · rintro ⟨r,hr,heq⟩
        have hzy := (haxis z).mp ⟨r,heq⟩
        refine ⟨hzy,?_⟩
        by_cases ht : r = t
        · have hx : (e z).val.1 = 0 := (zero hzy).mpr (heq.symm.trans (congrArg a.map ht))
          cases direction <;> simp [hx]
        · have hnot : z.val ∉ a.map '' {s : Interval | s.val ≤ t.val} := by
            rintro ⟨s,hs,hseq⟩
            have hh := unique r s heq hseq
            have hrt : r.val = t.val := le_antisymm (hh.symm ▸ hs) hr
            exact ht (Subtype.ext hrt)
          have hh : ¬ (if direction then (e z).val.1 ≤ 0 else 0 ≤ (e z).val.1) := by
            intro hh
            exact hnot ((hprefix z hz).mpr ⟨hzy,hh⟩)
          cases direction <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hh ⊢ <;> exact (lt_of_not_ge hh).le
      · rintro ⟨hzy,hzx⟩
        obtain ⟨r,heq⟩ := (haxis z).mpr hzy
        refine ⟨r,?_,heq⟩
        by_contra hh
        have hrt : r.val < t.val := lt_of_not_ge hh
        have hleft := (hprefix z hz).mp ⟨r,hrt.le,heq⟩
        have hxzero : (e z).val.1 = 0 := by
          cases direction <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hzx hleft <;> linarith [hleft.2]
        have hpz := (zero hzy).mp hxzero
        have hrr := unique r t heq hpz.symm
        have := congrArg Subtype.val hrr
        linarith
    have hpm : anchor.val.map x.t ∉ (M.cover.branch : Set S) := by
      intro hh
      rcases anchor.val.marked_only_at_ends x.t hh with hh | hh
      · have := congrArg Subtype.val hh
        have := x.t_interior.1
        simp only [show (0 : Interval).val = 0 from rfl] at *
        linarith
      · have := congrArg Subtype.val hh
        have := x.t_interior.2
        simp only [show (1 : Interval).val = 1 from rfl] at *
        linarith
    have hcross : anchor.val.map x.t ∈ crossings M anchor (P.rep x.selected) :=
      ⟨⟨mem_range_self x.t,hpm⟩,⟨⟨x.s,x.same_point.symm⟩,hpm⟩⟩
    obtain ⟨U,hU,hp,hm,e0,he0,ha,hb⟩ := P.transverse x.selected _ hcross
    let Q := {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}
    let swap : Q ≃ₜ Q := {
      toEquiv := {
        toFun := fun z => ⟨(z.val.2,z.val.1),z.property.2,z.property.1⟩
        invFun := fun z => ⟨(z.val.2,z.val.1),z.property.2,z.property.1⟩
        left_inv := by intro z; rfl
        right_inv := by intro z; rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let eb := e0.trans swap
    have hpOld : (P.rep x.selected).val.map x.s ∈ U := x.same_point ▸ hp
    have heOld : (eb ⟨(P.rep x.selected).val.map x.s,hpOld⟩).val = (0,0) := by
      have hz : (⟨(P.rep x.selected).val.map x.s,hpOld⟩ : U) = ⟨anchor.val.map x.t,hp⟩ := Subtype.ext x.same_point.symm
      change ((e0 ⟨_,hpOld⟩).val.2,(e0 ⟨_,hpOld⟩).val.1) = (0,0)
      rw [hz,he0]
    obtain ⟨Wa,hWa,hpWa,hWaU,hmWa,da,hpa⟩ := prefixTrace M anchor.val x.t x.t_interior.1 x.t_interior.2 U hU hp e0 he0 ha
    obtain ⟨Wb,hWb,hpWb,hWbU,hmWb,db,hpb⟩ := prefixTrace M (P.rep x.selected).val x.s x.s_interior.1 x.s_interior.2 U hU hpOld eb heOld (fun z => hb z)
    have hsb := suffixTrace M (P.rep x.selected).val x.s x.s_interior.1 x.s_interior.2 U hpOld eb heOld (fun z => hb z) Wb hmWb db hpb
    let reflect : Q ≃ₜ Q := {
      toEquiv := {
        toFun := fun z => ⟨(if da then z.val.1 else -z.val.1,if db then z.val.2 else -z.val.2),by cases da <;> cases db <;> simpa using z.property⟩
        invFun := fun z => ⟨(if da then z.val.1 else -z.val.1,if db then z.val.2 else -z.val.2),by cases da <;> cases db <;> simpa using z.property⟩
        left_inv := by intro z; cases da <;> cases db <;> apply Subtype.ext <;> simp
        right_inv := by intro z; cases da <;> cases db <;> apply Subtype.ext <;> simp }
      continuous_toFun := by cases da <;> cases db <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop
      continuous_invFun := by cases da <;> cases db <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop }
    let e := e0.trans reflect
    have he : (e ⟨anchor.val.map x.t,hp⟩).val = (0,0) := by
      change (if da then (e0 ⟨_,hp⟩).val.1 else -(e0 ⟨_,hp⟩).val.1,if db then (e0 ⟨_,hp⟩).val.2 else -(e0 ⟨_,hp⟩).val.2) = (0,0)
      rw [he0]
      cases da <;> cases db <;> simp
    let W := (Wa ∩ Wb) ∩ V
    have hpW : anchor.val.map x.t ∈ W := ⟨⟨hpWa,x.same_point.symm ▸ hpWb⟩,hpV⟩
    let o : Q := ⟨(0,0),by simp⟩
    have hpo : e.symm o = ⟨anchor.val.map x.t,hp⟩ := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact Subtype.ext he.symm
    have hOpen : IsOpen ((fun z : Q => (e.symm z).val) ⁻¹' W) :=
      ((hWa.inter hWb).inter hV).preimage (continuous_subtype_val.comp e.symm.continuous)
    have hoW : o ∈ ((fun z : Q => (e.symm z).val) ⁻¹' W) := by change (e.symm o).val ∈ W; rw [hpo]; exact hpW
    obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hOpen o hoW
    let δ := min r 1/2
    have hd : 0 < δ := by dsimp [δ]; positivity
    have hdr : δ < r := by dsimp [δ]; have := min_le_left r (1:ℝ); linarith
    have hd1 : δ < 1 := by dsimp [δ]; have := min_le_right r (1:ℝ); linarith
    have inside (z : U) (hz0 : |(e z).val.1| ≤ δ) (hz1 : |(e z).val.2| ≤ δ) : z.val ∈ W := by
      have hh : e z ∈ ball o r := by
        rw [Metric.mem_ball,Subtype.dist_eq]
        change dist (e z).val (0,0) < r
        rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero]
        exact (max_le hz0 hz1).trans_lt hdr
      have hh := hrW hh
      change (e.symm (e z)).val ∈ W at hh
      simpa only [e.symm_apply_apply] using hh
    refine ⟨U,hU,hp,hm,e,he,?_,?_,δ,hd,hd1,fun z hz0 hz1 => (inside z hz0 hz1).2,?_⟩
    · intro z
      cases da <;> cases db <;> simpa [e,reflect] using ha z
    · intro z
      cases da <;> cases db <;> simpa [e,reflect] using hb z
    · intro side z hz0 hz1
      have hzW := inside z hz0 hz1
      rw [hraw]
      change (z.val ∈ anchor.val.map '' {r : Interval | r.val ≤ x.t.val} ∪
        (P.rep x.selected).val.map '' {r : Interval | if side then x.s.val ≤ r.val else r.val ≤ x.s.val}) ↔ _
      simp only [Set.mem_union]
      rw [hpa z hzW.1.1]
      cases side
      · change _ ∨ z.val ∈ (P.rep x.selected).val.map '' {r : Interval | r.val ≤ x.s.val} ↔ _
        rw [hpb z hzW.1.2]
        cases da <;> cases db <;> simp [e,eb,reflect,swap]
      · change _ ∨ z.val ∈ (P.rep x.selected).val.map '' {r : Interval | x.s.val ≤ r.val} ↔ _
        rw [hsb z hzW.1.2]
        cases da <;> cases db <;> simp [e,eb,reflect,swap]
  have elbowChart : ∃ χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
  χ (0,0) = (0,0) ∧
  (∀ z, (χ z).2 = 0 ↔ (z.2 = 0 ∧ z.1 ≤ 0) ∨ (z.1 = 0 ∧ 0 ≤ z.2)) ∧
  (∀ z, 0 < (χ z).2 ↔ z.1 < 0 ∧ 0 < z.2) ∧
  (∀ z, (χ z).2 < 0 ↔ 0 < z.1 ∨ z.2 < 0) := by
    let χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
      toEquiv := {
        toFun := fun z => (z.1+z.2,z.2-z.1-|z.1+z.2|)
        invFun := fun z => ((z.1-z.2-|z.1|)/2,(z.1+z.2+|z.1|)/2)
        left_inv := by intro z; apply Prod.ext <;> dsimp <;> ring
        right_inv := by
          intro z
          have hx : (z.1-z.2-|z.1|)/2+(z.1+z.2+|z.1|)/2 = z.1 := by ring
          apply Prod.ext
          · exact hx
          · dsimp
            rw [hx]
            ring }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    refine ⟨χ,by simp [χ],?_,?_,?_⟩
    · intro z
      change z.2-z.1-|z.1+z.2| = 0 ↔ _
      by_cases h : 0 ≤ z.1+z.2
      · rw [abs_of_nonneg h]
        constructor
        · intro he
          right
          constructor <;> linarith
        · rintro (⟨hy,hx⟩ | ⟨hx,hy⟩) <;> linarith
      · rw [abs_of_nonpos (le_of_not_ge h)]
        constructor
        · intro he
          left
          constructor <;> linarith
        · rintro (⟨hy,hx⟩ | ⟨hx,hy⟩) <;> linarith
    · intro z
      change 0 < z.2-z.1-|z.1+z.2| ↔ _
      by_cases h : 0 ≤ z.1+z.2
      · rw [abs_of_nonneg h]
        constructor
        · intro he; constructor <;> linarith
        · rintro ⟨hx,hy⟩; linarith
      · rw [abs_of_nonpos (le_of_not_ge h)]
        constructor
        · intro he; constructor <;> linarith
        · rintro ⟨hx,hy⟩; linarith
    · intro z
      change z.2-z.1-|z.1+z.2| < 0 ↔ _
      by_cases h : 0 ≤ z.1+z.2
      · rw [abs_of_nonneg h]
        constructor
        · intro he; left; linarith
        · rintro (hx | hy) <;> linarith
      · rw [abs_of_nonpos (le_of_not_ge h)]
        constructor
        · intro he; right; linarith
        · rintro (hx | hy) <;> linarith
  obtain ⟨U,hU,hp,hm,e,he,ha,hb,δ,hd,hd1,hprot,htrace⟩ :=
    firstElbowTrace M anchor F P x raw univ isOpen_univ (mem_univ _) hraw
  obtain ⟨χ,hχ0,hχaxis,hχside,hχother⟩ := elbowChart
  let Q : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
  have hQ : IsOpen Q :=
    (isOpen_lt continuous_fst.abs continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)
  let coeU : OpenPartialHomeomorph U S :=
    (⟨U,hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe ⟨⟨_,hp⟩⟩
  let coeQ : OpenPartialHomeomorph Q (ℝ × ℝ) :=
    (⟨Q,hQ⟩ : TopologicalSpace.Opens (ℝ × ℝ)).openPartialHomeomorphSubtypeCoe
      ⟨⟨(0,0),by simp [Q]⟩⟩
  let reflect : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
    toEquiv := {
      toFun := fun z => (z.1,if side then z.2 else -z.2)
      invFun := fun z => (z.1,if side then z.2 else -z.2)
      left_inv := by intro z; cases side <;> simp
      right_inv := by intro z; cases side <;> simp }
    continuous_toFun := by cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop
    continuous_invFun := by cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop }
  let swap : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.prodComm ℝ ℝ
  let c := coeU.symm.trans (e.toOpenPartialHomeomorph.trans
    (coeQ.trans ((reflect.trans χ).trans swap).toOpenPartialHomeomorph))
  have csource (z : S) : z ∈ c.source ↔ z ∈ U := by
    simp [c,OpenPartialHomeomorph.trans_source,coeU,coeQ]
  have cinv (z : U) : coeU.symm z.val=z := by
    exact coeU.left_inv (by simp [coeU])
  have capply (z : U) : c z.val = swap (χ (reflect (e z).val)) := by
    change swap (χ (reflect ((e (coeU.symm z.val)).val)))=_
    rw [cinv]
  let T : Set S := Subtype.val '' {z : U | |(e z).val.1| < δ ∧ |(e z).val.2| < δ}
  have hT : IsOpen T := hU.isOpenMap_subtype_val _
    ((isOpen_lt (continuous_fst.comp (continuous_subtype_val.comp e.continuous)).abs continuous_const).inter
      (isOpen_lt (continuous_snd.comp (continuous_subtype_val.comp e.continuous)).abs continuous_const))
  have hpT : anchor.val.map x.t ∈ T := by
    refine ⟨⟨_,hp⟩,?_,rfl⟩
    change |(e ⟨_,hp⟩).val.1| < δ ∧ |(e ⟨_,hp⟩).val.2| < δ
    rw [he]
    exact ⟨by simpa using hd,by simpa using hd⟩
  let k := c.restrOpen T hT
  have ksource (z : S) : z ∈ k.source ↔ z ∈ U ∧ z ∈ T := by
    change z ∈ c.source ∩ T ↔ _
    rw [mem_inter_iff,csource]
  have kapply (z : U) : k z.val=swap (χ (reflect (e z).val)) := capply z
  refine ⟨U,hU,hp,e,he,ha,hb,k,(ksource _).mpr ⟨hp,hpT⟩,
    (fun z hz => ((ksource z).mp hz).1),?_,?_⟩
  · intro z hz
    obtain ⟨u,hu,rfl⟩ := ((ksource z).mp hz).2
    rw [kapply]
    change u.val ∈ (raw side).image ↔ (χ (reflect (e u).val)).2=0
    rw [hχaxis]
    have ht := htrace side u hu.1.le hu.2.le
    cases side <;> simpa [reflect] using ht
  · intro z hz
    rw [kapply]
    change 0 < (χ (reflect (e z).val)).2 ↔ _
    rw [hχside]
    cases side <;> simp [reflect]

private theorem actualSourceSurgery_loopRibbon_5 (M : HyperellipticModel E S) (a : MarkedArc M)
(hloop : a.map (0 : Interval) = a.map 1)
(F W : Set S) (hF : IsClosed F) (hmarks : (M.cover.branch : Set S) ⊆ F)
(hW : IsOpen W) (hAW : a.image \ F ⊆ W)
(r : S) (hrA : r ∈ a.image) (hrF : r ∈ F)
(hr0 : r ≠ a.map 0) (hr1 : r ≠ a.map 1)
(k : OpenPartialHomeomorph S (ℝ × ℝ)) (hrK : r ∈ k.source)
(hk : ∀ z ∈ k.source, z ∈ a.image ↔ (k z).1=0) :
∃ (H : AmbientIsotopy S) (N : Set S),
  (∀ t z, z ∈ F → H.map (t,z)=z) ∧
  (∀ t z, z ∉ W → H.map (t,z)=z) ∧
  Disjoint (H.finalMap '' (a.image \ F)) (a.image ∪ F) ∧
  IsOpen N ∧ r ∈ N ∧ N ⊆ k.source ∧
  (∀ z, z ∈ a.image \ F → z ∈ N →
    H.finalMap z ∈ k.source ∧ 0 < (k (H.finalMap z)).1) ∧
  ∀ v ∈ a.image ∩ F, v ≠ a.map 0 → v ≠ a.map 1 →
    ∀ c : OpenPartialHomeomorph S (ℝ × ℝ), v ∈ c.source →
      (∀ z ∈ c.source, z ∈ a.image ↔ (c z).1=0) →
      ∃ (σ : Bool) (V : Set S), IsOpen V ∧ v ∈ V ∧ V ⊆ c.source ∧
        ∀ z, z ∈ a.image \ F → z ∈ V → H.finalMap z ∈ c.source ∧
          (if σ then 0 < (c (H.finalMap z)).1 else (c (H.finalMap z)).1 < 0) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  have planar (A F W : Set Plane) (p q : Plane) (hA : IsJordanCurve A)
      (hF : IsClosed F) (hW : IsOpen W) (hp : p ∈ F) (hq : q ∈ F)
      (hAW : A \ F ⊆ W) (r : Plane) (hrA : r ∈ A) (hrF : r ∈ F)
      (_hrp : r ≠ p) (_hrq : r ≠ q)
      (h : OpenPartialHomeomorph Plane (ℝ × ℝ)) (hrH : r ∈ h.source)
      (hh : ∀ z ∈ h.source, z ∈ A ↔ (h z).1=0) :
      ∃ (H : AmbientIsotopy Plane) (C N : Set Plane),
        IsCompact C ∧ (∀ t z, z ∉ C → H.map (t,z)=z) ∧
        (∀ t z, z ∈ F → H.map (t,z)=z) ∧
        (∀ t z, z ∉ W → H.map (t,z)=z) ∧
        Disjoint (H.finalMap '' (A \ F)) (A ∪ F) ∧
        IsOpen N ∧ r ∈ N ∧ N ⊆ h.source ∧
        (∀ z, z ∈ A \ F → z ∈ N →
          H.finalMap z ∈ h.source ∧ 0 < (h (H.finalMap z)).1) ∧
        ∀ v ∈ A ∩ F, v ≠ p → v ≠ q →
          ∀ a : OpenPartialHomeomorph Plane (ℝ × ℝ), v ∈ a.source →
            (∀ z ∈ a.source, z ∈ A ↔ (a z).1=0) →
            ∃ (σ : Bool) (V : Set Plane), IsOpen V ∧ v ∈ V ∧ V ⊆ a.source ∧
              ∀ z, z ∈ A \ F → z ∈ V → H.finalMap z ∈ a.source ∧
                (if σ then 0 < (a (H.finalMap z)).1 else (a (H.finalMap z)).1 < 0) := by
    have jordan (A F : Set Plane) (hA : IsJordanCurve A)
  (hF : IsClosed F) (hne : F.Nonempty) (p : Plane) (hpA : p ∈ A) (hpF : p ∈ F)
  (h : OpenPartialHomeomorph Plane (ℝ × ℝ)) (hpH : p ∈ h.source)
  (hh : ∀ z ∈ h.source, z ∈ A ↔ (h z).1 = 0) :
  ∃ (H : AmbientIsotopy Plane) (C U : Set Plane),
    IsCompact C ∧ (∀ t z, z ∉ C → H.map (t,z) = z) ∧
    (∀ t z, z ∈ F → H.map (t,z) = z) ∧
    Disjoint (H.finalMap '' (A \ F)) (A ∪ F) ∧
    IsOpen U ∧ p ∈ U ∧ U ⊆ h.source ∧
    (∀ z, z ∈ A \ F → z ∈ U →
      H.finalMap z ∈ h.source ∧ 0 < (h (H.finalMap z)).1) ∧
    ∀ q ∈ A ∩ F, ∀ a : OpenPartialHomeomorph Plane (ℝ × ℝ), q ∈ a.source →
      (∀ z ∈ a.source, z ∈ A ↔ (a z).1=0) →
      ∃ (σ : Bool) (V : Set Plane), IsOpen V ∧ q ∈ V ∧ V ⊆ a.source ∧
        ∀ z, z ∈ A \ F → z ∈ V → H.finalMap z ∈ a.source ∧
          (if σ then 0 < (a (H.finalMap z)).1 else (a (H.finalMap z)).1 < 0) := by
      have bidirectional (A F : Set Plane) (hA : IsJordanCurve A)
        (hF : IsClosed F) (hne : F.Nonempty) :
        ∃ (L : Plane ≃ₜ (ℝ × ℝ)) (H I : AmbientIsotopy Plane) (C : Set Plane),
          IsCompact C ∧
          (∀ t z, z ∉ C → H.map (t,z) = z) ∧
          (∀ t z, z ∉ C → I.map (t,z) = z) ∧
          (∀ t z, z ∈ F → H.map (t,z) = z) ∧
          (∀ t z, z ∈ F → I.map (t,z) = z) ∧
          Disjoint (H.finalMap '' (A \ F)) (A ∪ F) ∧
          Disjoint (I.finalMap '' (A \ F)) (A ∪ F) ∧
          L '' A = {z : ℝ × ℝ | ‖z‖ = 1} ∧
          ∀ z, z ∈ A \ F →
            1 < ‖L (H.finalMap z)‖ ∧ ‖L (I.finalMap z)‖ < 1 := by
        have outward (A F : Set Plane) (hA : IsJordanCurve A)
            (hF : IsClosed F) (hne : F.Nonempty) :
            ∃ (L : Plane ≃ₜ (ℝ × ℝ)) (H : AmbientIsotopy Plane) (C : Set Plane),
              IsCompact C ∧ (∀ t z, z ∉ C → H.map (t,z) = z) ∧
              (∀ t z, z ∈ F → H.map (t,z) = z) ∧
              Disjoint (H.finalMap '' (A \ F)) (A ∪ F) ∧
              L '' A = {z : ℝ × ℝ | ‖z‖ = 1} ∧
              (∀ t z, z ∈ A \ F → 0 < t.val → 1 < ‖L (H.map (t,z))‖) ∧
              ∀ t z, ‖L z‖ ≤ ‖L (H.map (t,z))‖ := by

          have ribbon : ∀ (F : Set (ℝ × ℝ)) (hF : IsClosed F) (hne : F.Nonempty),
              ∃ H : AmbientIsotopy (ℝ × ℝ),
                (∀ t z, z ∈ F → H.map (t,z) = z) ∧
                (∀ t z, ‖z‖ ≤ 1/2 ∨ 3/2 ≤ ‖z‖ → H.map (t,z) = z) ∧
                Disjoint (H.finalMap '' ({z : ℝ × ℝ | ‖z‖ = 1} \ F))
                  ({z : ℝ × ℝ | ‖z‖ = 1} ∪ F) ∧
                (∀ t z, ‖z‖ = 1 → z ∉ F → 0 < t.val → 1 < ‖H.map (t,z)‖) ∧
                ∀ t z, ‖z‖ ≤ ‖H.map (t,z)‖ := by
            intro F hF hne
            have radial : ∀ (h : (ℝ × ℝ) → ℝ) (hc : Continuous h)
                (hp : ∀ z, 0 ≤ h z) (hb : ∀ z, h z ≤ 1/8),
                ∃ H : AmbientIsotopy (ℝ × ℝ),
                  (∀ t z, H.map (t,z) =
                    ((‖z‖ + max 0 (t.val*h (‖z‖⁻¹ • z)-|‖z‖-1|/2))/‖z‖) • z) ∧
                  (∀ t z, h (‖z‖⁻¹ • z) = 0 → H.map (t,z) = z) ∧
                  (∀ z, ‖z‖ = 1 → ‖H.finalMap z‖ = 1+h z) := by
              intro h hc hp hb
              have inverse : ∀ (h : (ℝ × ℝ) → ℝ) (hp : ∀ z, 0 ≤ h z) (hb : ∀ z, h z ≤ 1/8),
                  let d := fun z : ℝ × ℝ => ‖z‖⁻¹ • z
                  let R := fun z : ℝ × ℝ => ‖z‖ + max 0 (h (d z) - |‖z‖-1|/2)
                  let Q := fun z : ℝ × ℝ => ‖z‖ - max 0 (min ((‖z‖-1+2*h (d z))/3) (2*h (d z)-(‖z‖-1)))
                  let f := fun z : ℝ × ℝ => (R z / ‖z‖) • z
                  let g := fun z : ℝ × ℝ => (Q z / ‖z‖) • z
                  Function.LeftInverse g f ∧ Function.RightInverse g f := by
                intro h hp hb
                have scalar : ∀ (k r : ℝ) (hk : 0 ≤ k) (hkb : k ≤ 1/8) (hr : 0 ≤ r),
                    let f := fun y : ℝ => y + max 0 (k - |y|/2)
                    let g := fun y : ℝ => y - max 0 (min ((y+2*k)/3) (2*k-y))
                    0 ≤ 1 + f (r-1) ∧ 0 ≤ 1 + g (r-1) ∧
                    (1 + f (r-1) = 0 ↔ r = 0) ∧
                    (1 + g (r-1) = 0 ↔ r = 0) ∧
                    (r ≤ 1/2 → 1 + f (r-1) = r ∧ 1 + g (r-1) = r) ∧
                    1 + g (f (r-1)) = r ∧ 1 + f (g (r-1)) = r := by
                  intro k r hk hkb hr
                  let f : ℝ → ℝ → ℝ := fun k y => y + max 0 (k - |y|/2)
                  let g : ℝ → ℝ → ℝ := fun k z => z - max 0 (min ((z+2*k)/3) (2*k-z))
                  have left (k : ℝ) (hk : 0 ≤ k) (y : ℝ) : g k (f k y) = y := by
                    by_cases hy0 : y ≤ 0
                    ·
                      by_cases hy : y ≤ -2*k
                      · have hf : f k y = y := by
                          dsimp [f]
                          rw [abs_of_nonpos hy0, max_eq_left (by linarith)]
                          ring
                        rw [hf]
                        dsimp [g]
                        have h1 : (y+2*k)/3 ≤ 2*k-y := by linarith
                        rw [min_eq_left h1,max_eq_left (by linarith)]
                        ring
                      · have hf : f k y = 3/2*y+k := by
                          dsimp [f]
                          rw [abs_of_nonpos hy0,max_eq_right (by linarith)]
                          ring
                        rw [hf]
                        dsimp [g]
                        have h1 : ((3/2*y+k)+2*k)/3 ≤ 2*k-(3/2*y+k) := by linarith
                        rw [min_eq_left h1,max_eq_right (by linarith)]
                        ring
                    · have hy0' : 0 ≤ y := (not_le.mp hy0).le
                      by_cases hy : 2*k ≤ y
                      · have hf : f k y = y := by
                          dsimp [f]
                          rw [abs_of_nonneg hy0',max_eq_left (by linarith)]
                          ring
                        rw [hf]
                        dsimp [g]
                        have h1 : 2*k-y ≤ (y+2*k)/3 := by linarith
                        rw [min_eq_right h1,max_eq_left (by linarith)]
                        ring
                      · have hf : f k y = 1/2*y+k := by
                          dsimp [f]
                          rw [abs_of_nonneg hy0',max_eq_right (by linarith)]
                          ring
                        rw [hf]
                        dsimp [g]
                        have h1 : 2*k-(1/2*y+k) ≤ ((1/2*y+k)+2*k)/3 := by linarith
                        rw [min_eq_right h1,max_eq_right (by linarith)]
                        ring
                  have right (k : ℝ) (hk : 0 ≤ k) (z : ℝ) : f k (g k z) = z := by
                    by_cases hz : z ≤ -2*k
                    · have hg : g k z = z := by
                        dsimp [g]
                        rw [min_eq_left (by linarith),max_eq_left (by linarith)]
                        ring
                      rw [hg]
                      dsimp [f]
                      rw [abs_of_nonpos (by linarith),max_eq_left (by linarith)]
                      ring
                    · by_cases hz2 : 2*k ≤ z
                      · have hg : g k z = z := by
                          dsimp [g]
                          rw [min_eq_right (by linarith),max_eq_left (by linarith)]
                          ring
                        rw [hg]
                        dsimp [f]
                        rw [abs_of_nonneg (by linarith),max_eq_left (by linarith)]
                        ring
                      · by_cases hzk : z ≤ k
                        · have hg : g k z = 2/3*(z-k) := by
                            dsimp [g]
                            rw [min_eq_left (by linarith),max_eq_right (by linarith)]
                            ring
                          rw [hg]
                          dsimp [f]
                          rw [abs_of_nonpos (by linarith),max_eq_right (by linarith)]
                          ring
                        · have hg : g k z = 2*(z-k) := by
                            dsimp [g]
                            rw [min_eq_right (by linarith),max_eq_right (by linarith)]
                            ring
                          rw [hg]
                          dsimp [f]
                          rw [abs_of_nonneg (by linarith),max_eq_right (by linarith)]
                          ring
                  change 0 ≤ 1 + f k (r-1) ∧ 0 ≤ 1 + g k (r-1) ∧ _
                  have small (r : ℝ) (hr : r ≤ 1/2) :
                      1 + f k (r-1) = r ∧ 1 + g k (r-1) = r := by
                    constructor
                    · dsimp [f]
                      rw [abs_of_nonpos (by linarith),max_eq_left (by linarith)]
                      ring
                    · dsimp [g]
                      rw [min_eq_left (by linarith),max_eq_left (by linarith)]
                      ring
                  have fp : 0 ≤ 1 + f k (r-1) := by
                    dsimp [f]; have := le_max_left 0 (k-|r-1|/2); linarith
                  have gp : 0 ≤ 1 + g k (r-1) := by
                    by_cases hs : r ≤ 1/2
                    · rw [(small r hs).2]; exact hr
                    · have hm : max 0 (min ((r-1+2*k)/3) (2*k-(r-1))) ≤ r := by
                        apply max_le
                        · exact hr
                        · exact (min_le_left _ _).trans (by linarith)
                      dsimp [g]; linarith
                  refine ⟨fp,gp,?_,?_,small r,?_,?_⟩
                  · constructor
                    · intro he
                      dsimp [f] at he
                      have := le_max_left 0 (k-|r-1|/2)
                      linarith
                    · intro he; subst r; exact (small 0 (by norm_num)).1
                  · constructor
                    · intro he
                      by_cases hs : r ≤ 1/2
                      · rw [(small r hs).2] at he; exact he
                      · have hm : max 0 (min ((r-1+2*k)/3) (2*k-(r-1))) < r := by
                          apply max_lt
                          · linarith
                          · exact (min_le_left _ _).trans_lt (by linarith)
                        dsimp [g] at he
                        linarith
                    · intro he; subst r; exact (small 0 (by norm_num)).2
                  · change 1 + g k (f k (r-1)) = r
                    rw [left k hk]; ring
                  · change 1 + f k (g k (r-1)) = r
                    rw [right k hk]; ring
                dsimp only
                let d := fun z : ℝ × ℝ => ‖z‖⁻¹ • z
                let R := fun z : ℝ × ℝ => ‖z‖ + max 0 (h (d z) - |‖z‖-1|/2)
                let Q := fun z : ℝ × ℝ => ‖z‖ - max 0 (min ((‖z‖-1+2*h (d z))/3) (2*h (d z)-(‖z‖-1)))
                let f := fun z : ℝ × ℝ => (R z / ‖z‖) • z
                let g := fun z : ℝ × ℝ => (Q z / ‖z‖) • z
                change Function.LeftInverse g f ∧ Function.RightInverse g f
                have radial (A : (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) (hz : z ≠ 0) (hA : 0 < A z) :
                    ‖(A z / ‖z‖) • z‖ = A z ∧ d ((A z / ‖z‖) • z) = d z := by
                  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
                  have hr : 0 ≤ A z / ‖z‖ := (div_pos hA hn).le
                  have he : ‖(A z / ‖z‖) • z‖ = A z := by
                    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
                    field_simp
                  refine ⟨he,?_⟩
                  dsimp [d]
                  rw [he,smul_smul]
                  congr 1
                  field_simp
                have posR (z : ℝ × ℝ) (hz : z ≠ 0) : 0 < R z := by
                  have hs := scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)
                  have he : 1 + (‖z‖-1 + max 0 (h (d z)-|‖z‖-1|/2)) = R z := by dsimp [R]; ring
                  dsimp only at hs
                  rw [he] at hs
                  exact lt_of_le_of_ne hs.1 (Ne.symm (fun hh => hz (norm_eq_zero.mp (hs.2.2.1.mp hh))))
                have posQ (z : ℝ × ℝ) (hz : z ≠ 0) : 0 < Q z := by
                  have hs := scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)
                  have he : 1 + (‖z‖-1 - max 0 (min ((‖z‖-1+2*h (d z))/3) (2*h (d z)-(‖z‖-1)))) = Q z := by dsimp [Q]; ring
                  dsimp only at hs
                  rw [he] at hs
                  exact lt_of_le_of_ne hs.2.1 (Ne.symm (fun hh => hz (norm_eq_zero.mp (hs.2.2.2.1.mp hh))))
                constructor
                · intro z
                  by_cases hz : z = 0
                  · subst z; simp [f,g]
                  have hn := norm_pos_iff.mpr hz
                  obtain ⟨hfn,hfd⟩ := radial R z hz (posR z hz)
                  have hQ : Q (f z) = ‖z‖ := by
                    dsimp [Q]
                    rw [hfn]
                    change R z - max 0 (min ((R z-1+2*h (d (f z)))/3) (2*h (d (f z))-(R z-1))) = ‖z‖
                    rw [hfd]
                    have hs := (scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)).2.2.2.2.2.1
                    dsimp [R]
                    convert hs using 1 <;> ring_nf
                  change (Q (f z) / ‖f z‖) • ((R z / ‖z‖) • z) = z
                  rw [hQ,hfn,smul_smul]
                  have he : (‖z‖/R z)*(R z/‖z‖) = 1 := by field_simp [ne_of_gt hn,ne_of_gt (posR z hz),ne_of_gt (posQ z hz)]
                  rw [he,one_smul]
                · intro z
                  by_cases hz : z = 0
                  · subst z; simp [f,g]
                  have hn := norm_pos_iff.mpr hz
                  obtain ⟨hgn,hgd⟩ := radial Q z hz (posQ z hz)
                  have hR : R (g z) = ‖z‖ := by
                    dsimp [R]
                    rw [hgn]
                    change Q z + max 0 (h (d (g z))-|Q z-1|/2) = ‖z‖
                    rw [hgd]
                    have hs := (scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)).2.2.2.2.2.2
                    dsimp [Q]
                    convert hs using 1 <;> ring_nf
                  change (R (g z) / ‖g z‖) • ((Q z / ‖z‖) • z) = z
                  rw [hR,hgn,smul_smul]
                  have he : (‖z‖/Q z)*(Q z/‖z‖) = 1 := by field_simp [ne_of_gt hn,ne_of_gt (posR z hz),ne_of_gt (posQ z hz)]
                  rw [he,one_smul]
              let d := fun z : ℝ × ℝ => ‖z‖⁻¹ • z
              let R := fun z : Interval × (ℝ × ℝ) => ‖z.2‖ + max 0 (z.1.val*h (d z.2)-|‖z.2‖-1|/2)
              let Q := fun z : Interval × (ℝ × ℝ) => ‖z.2‖ - max 0 (min ((‖z.2‖-1+2*(z.1.val*h (d z.2)))/3) (2*(z.1.val*h (d z.2))-(‖z.2‖-1)))
              let f := fun z : Interval × (ℝ × ℝ) => (R z / ‖z.2‖) • z.2
              let g := fun z : Interval × (ℝ × ℝ) => (Q z / ‖z.2‖) • z.2
              have small (z : Interval × (ℝ × ℝ)) (hz : ‖z.2‖ < 1/2) : f z = z.2 ∧ g z = z.2 := by
                have hkp : 0 ≤ z.1.val * h (d z.2) := mul_nonneg z.1.property.1 (hp _)
                have hk : z.1.val * h (d z.2) ≤ 1/8 := (mul_le_of_le_one_left (hp _) z.1.property.2).trans (hb _)
                have hR : R z = ‖z.2‖ := by
                  dsimp [R]
                  rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
                  ring
                have hQ : Q z = ‖z.2‖ := by
                  dsimp [Q]
                  rw [min_eq_left (by linarith),max_eq_left (by linarith)]
                  ring
                by_cases he : z.2 = 0
                · simp [f,g,he]
                · have hn : ‖z.2‖ ≠ 0 := norm_ne_zero_iff.mpr he
                  simp [f,g,hR,hQ,hn]
              have cont : Continuous f ∧ Continuous g := by
                constructor <;> rw [continuous_iff_continuousAt] <;> intro z
                · by_cases hz : z.2 = 0
                  · have hh : ∀ᶠ w in 𝓝 z, ‖w.2‖ < 1/2 :=
                      (continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds (by simp [hz]))
                    apply continuous_snd.continuousAt.congr_of_eventuallyEq
                    filter_upwards [hh] with w hw
                    exact (small w hw).1
                  · dsimp [f,R,d]
                    fun_prop (disch := exact norm_ne_zero_iff.mpr hz)
                · by_cases hz : z.2 = 0
                  · have hh : ∀ᶠ w in 𝓝 z, ‖w.2‖ < 1/2 :=
                      (continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds (by simp [hz]))
                    apply continuous_snd.continuousAt.congr_of_eventuallyEq
                    filter_upwards [hh] with w hw
                    exact (small w hw).2
                  · dsimp [g,Q,d]
                    fun_prop (disch := exact norm_ne_zero_iff.mpr hz)
              let e : Interval → (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := fun t => {
                toEquiv := {
                  toFun := fun z => f (t,z)
                  invFun := fun z => g (t,z)
                  left_inv := (inverse (fun z => t.val*h z)
                    (fun z => mul_nonneg t.property.1 (hp z))
                    (fun z => (mul_le_of_le_one_left (hp z) t.property.2).trans (hb z))).1
                  right_inv := (inverse (fun z => t.val*h z)
                    (fun z => mul_nonneg t.property.1 (hp z))
                    (fun z => (mul_le_of_le_one_left (hp z) t.property.2).trans (hb z))).2 }
                continuous_toFun := cont.1.comp (continuous_const.prodMk continuous_id)
                continuous_invFun := cont.2.comp (continuous_const.prodMk continuous_id) }
              let H : AmbientIsotopy (ℝ × ℝ) := {
                map := ⟨f,cont.1⟩
                homeomorphism_at := fun t => ⟨e t,fun z => rfl⟩
                at_zero := by
                  intro z
                  by_cases hz : z = 0
                  · simp [f,hz]
                  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
                    change ((‖z‖+max 0 (0*h (d z)-|‖z‖-1|/2))/‖z‖) • z = z
                    rw [zero_mul,zero_sub,max_eq_left (neg_nonpos.mpr (div_nonneg (abs_nonneg _) (by norm_num))),add_zero,div_self hn,one_smul] }
              refine ⟨H,fun t z => rfl,?_,?_⟩
              · intro t z hz
                by_cases he : z = 0
                · simp [H,f,he]
                · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr he
                  change ((‖z‖+max 0 (t.val*h (d z)-|‖z‖-1|/2))/‖z‖) • z = z
                  rw [hz,mul_zero,zero_sub,max_eq_left (neg_nonpos.mpr (div_nonneg (abs_nonneg _) (by norm_num))),add_zero,div_self hn,one_smul]
              · intro z hz
                change ‖((‖z‖+max 0 (1*h (d z)-|‖z‖-1|/2))/‖z‖) • z‖ = _
                simp [d,hz,norm_smul,Real.norm_eq_abs,max_eq_right (hp z),abs_of_nonneg (by linarith [hp z] : 0 ≤ 1+h z)]
            let h : (ℝ × ℝ) → ℝ := fun z => min (1/8) (infDist z F/8)
            have hc : Continuous h := continuous_const.min ((Metric.continuous_infDist_pt F).div_const 8)
            have hp : ∀ z, 0 ≤ h z := fun z => le_min (by norm_num) (div_nonneg infDist_nonneg (by norm_num))
            have hb : ∀ z, h z ≤ 1/8 := fun z => min_le_left _ _
            obtain ⟨H,hmap,hzero,hnorm⟩ := radial h hc hp hb
            have distdir (z : ℝ × ℝ) (hz : z ≠ 0) : dist (‖z‖⁻¹ • z) z = |‖z‖-1| := by
              have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
              have hd : ‖‖z‖⁻¹ • z‖ = 1 := by
                rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
                exact inv_mul_cancel₀ hn
              have he : (‖z‖ : ℝ) • (‖z‖⁻¹ • z) = z := by rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
              calc
                dist (‖z‖⁻¹ • z) z = ‖(1-‖z‖) • (‖z‖⁻¹ • z)‖ := by rw [dist_eq_norm,sub_smul,one_smul,he]
                _ = |‖z‖-1| := by rw [norm_smul,Real.norm_eq_abs,hd,mul_one,abs_sub_comm]
            have fix : ∀ t z, z ∈ F → H.map (t,z) = z := by
              intro t z hz
              by_cases he : z = 0
              · subst z; rw [hmap]; simp
              have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr he
              have hi : infDist (‖z‖⁻¹ • z) F ≤ |‖z‖-1| := by
                rw [←distdir z he]
                exact infDist_le_dist_of_mem hz
              have hh : h (‖z‖⁻¹ • z) ≤ |‖z‖-1|/8 := (min_le_right _ _).trans (div_le_div_of_nonneg_right hi (by norm_num))
              have ht : t.val*h (‖z‖⁻¹ • z) ≤ h (‖z‖⁻¹ • z) := mul_le_of_le_one_left (hp _) t.property.2
              rw [hmap,max_eq_left (by have := abs_nonneg (‖z‖-1); linarith),add_zero,div_self hn,one_smul]
            refine ⟨H,fix,?_,?_,?_,?_⟩
            · intro t z hz
              by_cases he : z = 0
              · subst z; rw [hmap]; simp
              have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr he
              have ht : t.val*h (‖z‖⁻¹ • z) ≤ 1/8 := (mul_le_of_le_one_left (hp _) t.property.2).trans (hb _)
              have ha : 1/2 ≤ |‖z‖-1| := by
                rcases hz with hz | hz
                · rw [abs_of_nonpos (by linarith)]; linarith
                · rw [abs_of_nonneg (by linarith)]; linarith
              rw [hmap,max_eq_left (by linarith),add_zero,div_self hn,one_smul]
            · apply Set.disjoint_left.mpr
              rintro z ⟨w,⟨hw,hwF⟩,rfl⟩ hz
              rcases hz with hz | hz
              · have hpw : 0 < h w := by
                  apply lt_min (by norm_num)
                  exact div_pos ((hF.notMem_iff_infDist_pos hne).mp hwF) (by norm_num)
                have he := hnorm w hw
                change ‖H.finalMap w‖ = 1 at hz
                linarith
              · obtain ⟨e,he⟩ := H.homeomorphism_at (1 : Interval)
                have heq : H.finalMap w = w := e.injective (by
                  rw [he,he]
                  exact (fix 1 (H.finalMap w) hz).trans rfl)
                exact hwF (heq ▸ hz)
            · intro t z hz hzF ht
              have hpos : 0 < h z := lt_min (by norm_num)
                (div_pos ((hF.notMem_iff_infDist_pos hne).mp hzF) (by norm_num))
              have htz : 0 < t.val * h z := mul_pos ht hpos
              have norm_eq : ‖H.map (t,z)‖ = 1 + t.val * h z := by
                rw [hmap]
                simp only [hz,inv_one,one_smul,sub_self,abs_zero,zero_div,sub_zero,div_one]
                rw [max_eq_right htz.le,norm_smul,Real.norm_eq_abs,hz,mul_one,
                  abs_of_pos (by linarith : 0 < 1 + t.val * h z)]
              rw [norm_eq]
              linarith
            · intro t z
              rw [hmap,norm_smul,Real.norm_eq_abs]
              by_cases hz : z = 0
              · simp [hz]
              have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
              have hr : 0 ≤ ‖z‖ + max 0 (t.val*h (‖z‖⁻¹ • z)-|‖z‖-1|/2) :=
                add_nonneg (norm_nonneg _) (le_max_left _ _)
              rw [abs_of_nonneg (div_nonneg hr (norm_nonneg _)),div_mul_cancel₀ _ hn]
              exact le_add_of_nonneg_right (le_max_left _ _)
          obtain ⟨e⟩ := hA.homeomorph_modelCurve
          obtain ⟨G,hG⟩ := jordan_schoenflies_of_homeomorph hA isJordanCurve_modelCurve e
          have imageG : G '' A = modelCurve := by
            ext z
            constructor
            · rintro ⟨w,hw,rfl⟩
              rw [hG ⟨w,hw⟩]
              exact (e ⟨w,hw⟩).property
            · intro hz
              refine ⟨e.symm ⟨z,hz⟩,(e.symm ⟨z,hz⟩).property,?_⟩
              rw [hG]
              exact congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)
          let P : Plane ≃ₜ (ℝ × ℝ) := {
            toEquiv := {
              toFun := fun z => (z 0,z 1)
              invFun := fun z => Plane.mk z.1 z.2
              left_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk]
              right_inv := by intro z; exact Prod.ext (by simp [Plane.mk]) (by simp [Plane.mk]) }
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop }
          let L := G.trans P
          have imageL : L '' A = {z : ℝ × ℝ | ‖z‖ = 1} := by
            rw [show (L : Plane → ℝ × ℝ) = P ∘ G from rfl,Set.image_comp,imageG]
            ext z
            constructor
            · rintro ⟨w,hw,rfl⟩
              change max |w 0| |w 1| = 1 at hw
              simpa [P,Prod.norm_def,Real.norm_eq_abs] using hw
            · intro hz
              refine ⟨P.symm z,?_,P.apply_symm_apply z⟩
              change max |z.1| |z.2| = 1
              simpa [Prod.norm_def,Real.norm_eq_abs] using hz
          obtain ⟨K,hfix,hsupport,hdisj,hside,hmono⟩ := ribbon (L '' F) (L.isClosedMap F hF) (hne.image L)
          let H : AmbientIsotopy Plane := {
            map := ⟨fun z => L.symm (K.map (z.1,L z.2)), by fun_prop⟩
            homeomorphism_at := by
              intro t; obtain ⟨e,he⟩ := K.homeomorphism_at t
              exact ⟨(L.trans e).trans L.symm,fun z => congrArg L.symm (he (L z))⟩
            at_zero := by intro z; change L.symm (K.map (⟨0,by norm_num⟩,L z)) = z; rw [K.at_zero,L.symm_apply_apply] }
          let C : Set Plane := L.symm '' closedBall (0 : ℝ × ℝ) (3/2)
          have hcompact : IsCompact C := (isCompact_closedBall _ _).image L.symm.continuous
          have coord (t : Interval) (z : Plane) : L (H.map (t,z)) = K.map (t,L z) := L.apply_symm_apply _
          refine ⟨L,H,C,hcompact,?_,?_,?_,imageL,?_,?_⟩
          · intro t z hz
            apply L.injective
            rw [coord,hsupport]
            have hn : 3/2 < ‖L z‖ := by
              by_contra hh
              apply hz
              refine ⟨L z,?_,L.symm_apply_apply z⟩
              simpa [Metric.mem_closedBall,dist_zero_right] using (not_lt.mp hh)
            exact Or.inr hn.le
          · intro t z hz
            apply L.injective
            rw [coord,hfix t (L z) (mem_image_of_mem L hz)]
          · apply Set.disjoint_left.mpr
            rintro z ⟨w,⟨hw,hwF⟩,rfl⟩ hz
            apply Set.disjoint_left.mp hdisj
            · refine ⟨L w,⟨?_,?_⟩,?_⟩
              · rw [←imageL]; exact mem_image_of_mem L hw
              · rintro ⟨u,hu,he⟩; exact hwF (L.injective he ▸ hu)
              · exact (coord 1 w).symm
            · rcases hz with hz | hz
              · left; rw [←imageL]; exact mem_image_of_mem L hz
              · exact Or.inr (mem_image_of_mem L hz)
          · intro t z hz ht
            rw [coord]
            apply hside t (L z)
            · change L z ∈ {z : ℝ × ℝ | ‖z‖ = 1}
              rw [← imageL]
              exact mem_image_of_mem L hz.1
            · rintro ⟨q,hq,he⟩
              exact hz.2 (L.injective he ▸ hq)
            · exact ht
          · intro t z
            rw [coord]
            exact hmono t (L z)
        obtain ⟨L,H,C,hC,houtside,hfix,hdisj,hLA,hside,hmono⟩ := outward A F hA hF hne
        obtain ⟨e,he⟩ := H.homeomorphism_at 1
        let reverse : Interval → Interval := fun t =>
          ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩
        have reverseCont : Continuous reverse := by unfold reverse; fun_prop
        let I : AmbientIsotopy Plane := {
          map := ⟨fun z => H.map (reverse z.1,e.symm z.2),
            H.map.continuous.comp ((reverseCont.comp continuous_fst).prodMk
              (e.symm.continuous.comp continuous_snd))⟩
          homeomorphism_at := by
            intro t
            obtain ⟨et,het⟩ := H.homeomorphism_at (reverse t)
            exact ⟨e.symm.trans et,fun z => het _⟩
          at_zero := by
            intro z
            change H.map (reverse 0,e.symm z) = z
            rw [show reverse 0 = (1:Interval) by apply Subtype.ext; norm_num [reverse],
              ← he,e.apply_symm_apply] }
        have hifinal (z : Plane) : I.finalMap z = e.symm z := by
          change H.map (reverse 1,e.symm z) = e.symm z
          rw [show reverse 1 = (0:Interval) by apply Subtype.ext; norm_num [reverse]]
          exact H.at_zero _
        have inverseFixes (P : Set Plane) (hP : ∀ t z, z ∈ P → H.map (t,z) = z) :
            ∀ t z, z ∈ P → I.map (t,z) = z := by
          intro t z hz
          have hz' : e.symm z = z := by
            apply e.injective
            rw [e.apply_symm_apply,he,hP 1 z hz]
          change H.map (reverse t,e.symm z) = z
          rw [hz']
          exact hP _ z hz
        have hifix : ∀ t z, z ∈ F → I.map (t,z) = z := inverseFixes F hfix
        have hioutside : ∀ t z, z ∉ C → I.map (t,z) = z := inverseFixes Cᶜ houtside
        have radiusA (z : Plane) (hz : z ∈ A) : ‖L z‖ = 1 := by
          have hm : L z ∈ L '' A := mem_image_of_mem L hz
          rw [hLA] at hm
          exact hm
        have radiusConverse (z : Plane) (hz : ‖L z‖ = 1) : z ∈ A := by
          have hm : L z ∈ L '' A := by rw [hLA]; exact hz
          obtain ⟨w,hw,he⟩ := hm
          exact L.injective he ▸ hw
        have inward (z : Plane) (hz : z ∈ A \ F) : ‖L (I.finalMap z)‖ < 1 := by
          let y := e.symm z
          have hy : H.map (1,y) = z := by
            rw [← he]
            exact e.apply_symm_apply z
          have hyF : y ∉ F := by
            intro hm
            have hf := hfix 1 y hm
            rw [hy] at hf
            exact hz.2 (hf.symm ▸ hm)
          have hle : ‖L y‖ ≤ 1 := by
            have hm := hmono 1 y
            rw [hy,radiusA z hz.1] at hm
            exact hm
          have hne : ‖L y‖ ≠ 1 := by
            intro he
            have hs := hside 1 y ⟨radiusConverse y he,hyF⟩ (by norm_num)
            rw [hy,radiusA z hz.1] at hs
            exact lt_irrefl 1 hs
          have hi : I.finalMap z = y := hifinal z
          rw [hi]
          exact lt_of_le_of_ne hle hne
        have hidisj : Disjoint (I.finalMap '' (A \ F)) (A ∪ F) := by
          apply disjoint_left.mpr
          rintro z ⟨w,hw,rfl⟩ (hz | hz)
          · have hin := inward w hw
            rw [radiusA _ hz] at hin
            exact lt_irrefl 1 hin
          · obtain ⟨e,he⟩ := I.homeomorphism_at 1
            have hh : I.finalMap w = w := e.injective (by
              rw [he,he]
              exact hifix 1 (I.finalMap w) hz)
            exact hw.2 (hh ▸ hz)
        refine ⟨L,H,I,C,hC,houtside,hioutside,hfix,hifix,hdisj,hidisj,hLA,?_⟩
        intro z hz
        exact ⟨hside 1 z hz (by norm_num),inward z hz⟩
      have sideTransition {S : Type} [TopologicalSpace S] (G : S ≃ₜ (ℝ × ℝ)) (p : S)
        (hp : max |(G p).1| |(G p).2| = 1)
        (h : OpenPartialHomeomorph S (ℝ × ℝ)) (hpH : p ∈ h.source)
        (hh : ∀ z ∈ h.source, max |(G z).1| |(G z).2| = 1 ↔ (h z).1 = 0) :
        ∃ (ε : ZMod 2) (O : Set S), IsOpen O ∧ p ∈ O ∧ O ⊆ h.source ∧
          ∀ z ∈ O, max |(G z).1| |(G z).2| ≠ 1 →
            (if 0 < (h z).1 then (1 : ZMod 2) else 0) =
              (if 1 < max |(G z).1| |(G z).2| then (1 : ZMod 2) else 0) + ε := by
        have modelChart (q : ℝ × ℝ) (hq : max |q.1| |q.2| = 1) :
            ∃ (χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (U : Set (ℝ × ℝ)),
              IsOpen U ∧ q ∈ U ∧ χ q = (0,0) ∧
              ∀ z ∈ U, (max |z.1| |z.2| = 1 ↔ (χ z).1 = 0) ∧
                (1 < max |z.1| |z.2| ↔ 0 < (χ z).1) := by
          have corner : ∃ χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
              χ (1,1) = (0,0) ∧
              ∀ z, 0 < z.1 → 0 < z.2 →
                (χ z).1 = 2 * (max |z.1| |z.2| - 1) := by
            let χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
              toEquiv := {
                toFun := fun z => (z.1+z.2-2+|z.1-z.2|,z.1-z.2)
                invFun := fun z => (1+(z.1-|z.2|+z.2)/2,1+(z.1-|z.2|-z.2)/2)
                left_inv := by intro z; apply Prod.ext <;> dsimp <;> ring
                right_inv := by
                  intro z
                  have he : (1+(z.1-|z.2|+z.2)/2)-(1+(z.1-|z.2|-z.2)/2) = z.2 := by ring
                  apply Prod.ext
                  · dsimp; rw [he]; ring
                  · exact he }
              continuous_toFun := by fun_prop
              continuous_invFun := by fun_prop }
            refine ⟨χ,by norm_num [χ],?_⟩
            intro z hx hy
            change z.1+z.2-2+|z.1-z.2| = _
            rw [abs_of_pos hx,abs_of_pos hy]
            by_cases he : z.2 ≤ z.1
            · rw [max_eq_left he,abs_of_nonneg (sub_nonneg.mpr he)]; ring
            · rw [max_eq_right (le_of_not_ge he),abs_of_nonpos (by linarith)]; ring
          have facet (a : ℝ) (ha : |a| < 1) :
              ∃ (χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (U : Set (ℝ × ℝ)),
                IsOpen U ∧ (1,a) ∈ U ∧ χ (1,a) = (0,0) ∧
                ∀ z ∈ U, (max |z.1| |z.2| = 1 ↔ (χ z).1 = 0) ∧
                  (1 < max |z.1| |z.2| ↔ 0 < (χ z).1) := by
            let χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
              toEquiv := {
                toFun := fun z => (z.1-1,z.2-a)
                invFun := fun z => (z.1+1,z.2+a)
                left_inv := by intro z; apply Prod.ext <;> dsimp <;> ring
                right_inv := by intro z; apply Prod.ext <;> dsimp <;> ring }
              continuous_toFun := by fun_prop
              continuous_invFun := by fun_prop }
            let U : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ |z.2| < 1}
            have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
              (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
            refine ⟨χ,U,hU,⟨by norm_num,ha⟩,by simp [χ],?_⟩
            intro z hz
            have hx := hz.1
            have hy := hz.2
            constructor
            · change max |z.1| |z.2| = 1 ↔ z.1-1 = 0
              rw [abs_of_pos hx]
              constructor
              · intro hm
                by_cases hle : z.1 ≤ |z.2|
                · rw [max_eq_right hle] at hm
                  linarith
                · rw [max_eq_left (le_of_not_ge hle)] at hm
                  linarith
              · intro he
                have he' : z.1 = 1 := by linarith
                rw [he',max_eq_left hy.le]
            · change 1 < max |z.1| |z.2| ↔ 0 < z.1-1
              rw [abs_of_pos hx,lt_max_iff]
              constructor
              · rintro (h | h) <;> linarith
              · intro h; left; linarith
          have positive (q : ℝ × ℝ) (hx : 0 ≤ q.1) (hy : 0 ≤ q.2) (hq : max q.1 q.2 = 1) :
              ∃ (χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (U : Set (ℝ × ℝ)),
                IsOpen U ∧ q ∈ U ∧ χ q = (0,0) ∧
                ∀ z ∈ U, (max |z.1| |z.2| = 1 ↔ (χ z).1 = 0) ∧
                  (1 < max |z.1| |z.2| ↔ 0 < (χ z).1) := by
            have hxle : q.1 ≤ 1 := (le_max_left _ _).trans_eq hq
            have hyle : q.2 ≤ 1 := (le_max_right _ _).trans_eq hq
            by_cases hx1 : q.1 = 1
            · by_cases hy1 : q.2 = 1
              · obtain ⟨χ,hzero,hcoord⟩ := corner
                let U : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ 0 < z.2}
                have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)
                refine ⟨χ,U,hU,⟨by simpa [hx1],by simpa [hy1]⟩,?_,?_⟩
                · have he : q = (1,1) := Prod.ext hx1 hy1
                  simpa [he] using hzero
                · intro z hz
                  rw [hcoord z hz.1 hz.2]
                  constructor <;> constructor <;> intro h <;> linarith
              · have hylt : |q.2| < 1 := by rw [abs_of_nonneg hy]; exact lt_of_le_of_ne hyle hy1
                obtain ⟨χ,U,hU,hqu,hzero,hside⟩ := facet q.2 hylt
                have he : q = (1,q.2) := Prod.ext hx1 rfl
                exact ⟨χ,U,hU,he.symm ▸ hqu,he.symm ▸ hzero,hside⟩
            · have hxlt : |q.1| < 1 := by rw [abs_of_nonneg hx]; exact lt_of_le_of_ne hxle hx1
              have hy1 : q.2 = 1 := by
                by_contra hn
                have hylt : q.2 < 1 := lt_of_le_of_ne hyle hn
                have hxlt' : q.1 < 1 := lt_of_le_of_ne hxle hx1
                have hh := (max_lt_iff.mpr ⟨hxlt',hylt⟩)
                rw [hq] at hh
                exact lt_irrefl _ hh
              let R : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
                toEquiv := {
                  toFun := Prod.swap
                  invFun := Prod.swap
                  left_inv := by intro z; rfl
                  right_inv := by intro z; rfl }
                continuous_toFun := continuous_swap
                continuous_invFun := continuous_swap }
              obtain ⟨χ,V,hV,hqV,hzero,hside⟩ := facet q.1 hxlt
              let U : Set (ℝ × ℝ) := R ⁻¹' V
              refine ⟨R.trans χ,U,hV.preimage R.continuous,?_,?_,?_⟩
              · change (q.2,q.1) ∈ V
                simpa [hy1] using hqV
              · change χ (q.2,q.1) = (0,0)
                simpa [hy1] using hzero
              · intro z hz
                have hh := hside (R z) hz
                simpa [R,max_comm] using hh
          let R : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
            toEquiv := {
              toFun := fun z => (if q.1 < 0 then -z.1 else z.1,if q.2 < 0 then -z.2 else z.2)
              invFun := fun z => (if q.1 < 0 then -z.1 else z.1,if q.2 < 0 then -z.2 else z.2)
              left_inv := by intro z; split_ifs <;> simp
              right_inv := by intro z; split_ifs <;> simp }
            continuous_toFun := by split_ifs <;> fun_prop
            continuous_invFun := by split_ifs <;> fun_prop }
          have he : R q = (|q.1|,|q.2|) := by
            apply Prod.ext
            · dsimp [R]; split_ifs with h
              · exact (abs_of_neg h).symm
              · exact (abs_of_nonneg (le_of_not_gt h)).symm
            · dsimp [R]; split_ifs with h
              · exact (abs_of_neg h).symm
              · exact (abs_of_nonneg (le_of_not_gt h)).symm
          have hn (z : ℝ × ℝ) : max |(R z).1| |(R z).2| = max |z.1| |z.2| := by
            dsimp [R]; split_ifs <;> simp
          obtain ⟨χ,V,hV,hqV,hzero,hside⟩ := positive (R q)
            (by rw [he]; exact abs_nonneg _) (by rw [he]; exact abs_nonneg _) (by simpa [he] using hq)
          let U : Set (ℝ × ℝ) := R ⁻¹' V
          refine ⟨R.trans χ,U,hV.preimage R.continuous,hqV,hzero,?_⟩
          intro z hz
          have hh := hside (R z) hz
          rw [hn z] at hh
          exact hh
        obtain ⟨χ,U,hU,hpU,hzero,hside⟩ := modelChart (G p) hp
        let V : Set S := G ⁻¹' U
        have hV : IsOpen V := hU.preimage G.continuous
        let k : OpenPartialHomeomorph S (ℝ × ℝ) := (G.trans χ).toOpenPartialHomeomorph.restrOpen V hV
        have ks : k.source = V := by simp [k]
        have kp : p ∈ k.source := by rw [ks]; exact hpU
        have hk (z : S) (hz : z ∈ k.source) :
            max |(G z).1| |(G z).2| = 1 ↔ (k z).1 = 0 := by
          exact (hside (G z) (by change z ∈ V; exact ks ▸ hz)).1
        let A : Set S := {z | max |(G z).1| |(G z).2| = 1}
        obtain ⟨τ,hτ,hformula⟩ := CurveComplex.LocalSurgery.axis_chart_relative_side_extension A h k hh hk
        have hOpen : IsOpen (h.source ∩ k.source) := h.open_source.inter k.open_source
        have hpW : p ∈ h.source ∩ k.source := ⟨hpH,kp⟩
        have hc : ContinuousAt τ p := (hτ p hpW).continuousAt (hOpen.mem_nhds hpW)
        have hconstant : {z | τ z = τ p} ∈ 𝓝 p :=
          hc.preimage_mem_nhds ((isOpen_discrete {τ p}).mem_nhds (by simp))
        obtain ⟨O,hOW,hO,hpO⟩ := mem_nhds_iff.mp (inter_mem (hOpen.mem_nhds hpW) hconstant)
        refine ⟨τ p,O,hO,hpO,fun z hz => (hOW hz).1.1,?_⟩
        intro z hz hne
        have he := hformula z (hOW hz).1 hne
        have hs := (hside (G z) (by change z ∈ V; exact ks ▸ (hOW hz).1.2)).2
        have hlabel : (if 0 < (k z).1 then (1 : ZMod 2) else 0) =
            (if 1 < max |(G z).1| |(G z).2| then (1 : ZMod 2) else 0) := by
          simp only [show (k z).1 = (χ (G z)).1 from rfl,← hs]
        rw [hlabel,(hOW hz).2] at he
        rw [he,add_left_comm,CharTwo.add_self_eq_zero,add_zero]
      obtain ⟨L,H,I,C,hC,hout,hiout,hfix,hifix,hdisj,hidisj,hLA,hside⟩ :=
        bidirectional A F hA hF hne
      have normA (z : Plane) : ‖L z‖ = 1 ↔ z ∈ A := by
        constructor
        · intro hz
          have hm : L z ∈ L '' A := by rw [hLA]; exact hz
          obtain ⟨w,hw,he⟩ := hm
          exact L.injective he ▸ hw
        · intro hz
          have hm : L z ∈ L '' A := mem_image_of_mem L hz
          rw [hLA] at hm
          exact hm
      have normMax (z : Plane) : max |(L z).1| |(L z).2| = ‖L z‖ := by
        simp [Prod.norm_def,Real.norm_eq_abs]
      obtain ⟨ε,O,hO,hpO,hOH,hlabel⟩ := sideTransition L p
        (by rw [normMax]; exact (normA p).mpr hpA) h hpH
        (fun z hz => by rw [normMax,normA]; exact hh z hz)
      let U := O ∩ (H.finalMap ⁻¹' O) ∩ (I.finalMap ⁻¹' O)
      have hHcont : Continuous H.finalMap := H.map.continuous.comp
        (continuous_const.prodMk continuous_id)
      have hIcont : Continuous I.finalMap := I.map.continuous.comp
        (continuous_const.prodMk continuous_id)
      have hU : IsOpen U := (hO.inter (hO.preimage hHcont)).inter (hO.preimage hIcont)
      have hpU : p ∈ U := ⟨⟨hpO,by change H.finalMap p ∈ O; rw [show H.finalMap p = p from hfix 1 p hpF]; exact hpO⟩,
        by change I.finalMap p ∈ O; rw [show I.finalMap p = p from hifix 1 p hpF]; exact hpO⟩
      have hUH : U ⊆ h.source := fun z hz => hOH hz.1.1
      have allNode (T : AmbientIsotopy Plane)
          (hfixT : ∀ z ∈ F, T.finalMap z=z)
          (huniform : (∀ z, z ∈ A \ F → 1 < ‖L (T.finalMap z)‖) ∨
            (∀ z, z ∈ A \ F → ‖L (T.finalMap z)‖ < 1)) :
          ∀ q ∈ A ∩ F, ∀ a : OpenPartialHomeomorph Plane (ℝ × ℝ), q ∈ a.source →
            (∀ z ∈ a.source, z ∈ A ↔ (a z).1=0) →
            ∃ (σ : Bool) (V : Set Plane), IsOpen V ∧ q ∈ V ∧ V ⊆ a.source ∧
              ∀ z, z ∈ A \ F → z ∈ V → T.finalMap z ∈ a.source ∧
                (if σ then 0 < (a (T.finalMap z)).1 else (a (T.finalMap z)).1 < 0) := by
        intro q hq a hqa haa
        obtain ⟨ε',O',hO',hqO',hOa',hlabel'⟩ := sideTransition L q
          (by rw [normMax]; exact (normA q).mpr hq.1) a hqa
          (fun z hz => by rw [normMax,normA]; exact haa z hz)
        let V := O' ∩ (T.finalMap ⁻¹' O')
        have hTc : Continuous T.finalMap := T.map.continuous.comp
          (continuous_const.prodMk continuous_id)
        have hV : IsOpen V := hO'.inter (hO'.preimage hTc)
        have hqV : q ∈ V := ⟨hqO',by change T.finalMap q ∈ O'; rw [hfixT q hq.2]; exact hqO'⟩
        have hVa : V ⊆ a.source := fun z hz => hOa' hz.1
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        rcases huniform with hout | hin
        · fin_cases ε'
          · refine ⟨true,V,hV,hqV,hVa,?_⟩
            intro z hz hzV
            have hzO : T.finalMap z ∈ O' := hzV.2
            have hs := hout z hz
            have he := hlabel' (T.finalMap z) hzO (by rw [normMax]; exact ne_of_gt hs)
            rw [normMax] at he
            refine ⟨hOa' hzO,?_⟩
            simp only [Bool.false_eq_true,↓reduceIte]
            by_contra hn
            simp [hn,hs] at he
            exact h01 (by convert he using 1 <;> decide)
          · refine ⟨false,V,hV,hqV,hVa,?_⟩
            intro z hz hzV
            have hzO : T.finalMap z ∈ O' := hzV.2
            have hs := hout z hz
            have he := hlabel' (T.finalMap z) hzO (by rw [normMax]; exact ne_of_gt hs)
            rw [normMax] at he
            refine ⟨hOa' hzO,?_⟩
            simp only [Bool.false_eq_true,↓reduceIte]
            have hn : ¬ 0 < (a (T.finalMap z)).1 := by
              intro hp
              simp [hp,hs] at he
              exact h01 (by convert he.symm using 1 <;> decide)
            have hzero : (a (T.finalMap z)).1 ≠ 0 := by
              intro hh
              have hm := (normA (T.finalMap z)).mpr ((haa _ (hOa' hzO)).mpr hh)
              exact (ne_of_gt hs) hm
            exact lt_of_le_of_ne (le_of_not_gt hn) hzero
        · fin_cases ε'
          · refine ⟨false,V,hV,hqV,hVa,?_⟩
            intro z hz hzV
            have hzO : T.finalMap z ∈ O' := hzV.2
            have hs := hin z hz
            have he := hlabel' (T.finalMap z) hzO (by rw [normMax]; exact ne_of_lt hs)
            rw [normMax] at he
            refine ⟨hOa' hzO,?_⟩
            simp only [Bool.false_eq_true,↓reduceIte]
            have hn : ¬ 0 < (a (T.finalMap z)).1 := by
              intro hp
              simp [hp,not_lt_of_ge hs.le] at he
              exact h01 (by convert he.symm using 1 <;> decide)
            have hzero : (a (T.finalMap z)).1 ≠ 0 := by
              intro hh
              have hm := (normA (T.finalMap z)).mpr ((haa _ (hOa' hzO)).mpr hh)
              exact (ne_of_lt hs) hm
            exact lt_of_le_of_ne (le_of_not_gt hn) hzero
          · refine ⟨true,V,hV,hqV,hVa,?_⟩
            intro z hz hzV
            have hzO : T.finalMap z ∈ O' := hzV.2
            have hs := hin z hz
            have he := hlabel' (T.finalMap z) hzO (by rw [normMax]; exact ne_of_lt hs)
            rw [normMax] at he
            refine ⟨hOa' hzO,?_⟩
            simp only [Bool.false_eq_true,↓reduceIte]
            by_contra hn
            simp [hn,not_lt_of_ge hs.le] at he
            exact h01 (by convert he using 1 <;> decide)
      fin_cases ε
      · refine ⟨H,C,U,hC,hout,hfix,hdisj,hU,hpU,hUH,?_,?_⟩
        · intro z hz hzU
          have hzO : H.finalMap z ∈ O := hzU.1.2
          have houtside := (hside z hz).1
          have he := hlabel (H.finalMap z) hzO (by rw [normMax]; exact ne_of_gt houtside)
          rw [normMax] at he
          refine ⟨hOH hzO,?_⟩
          by_contra hn
          simp [hn,houtside] at he
          have h01 : (0 : ZMod 2) ≠ 1 := by decide
          exact h01 (by convert he using 1 <;> decide)
        · exact allNode H (fun z hz => hfix 1 z hz) (Or.inl (fun z hz => (hside z hz).1))
      · refine ⟨I,C,U,hC,hiout,hifix,hidisj,hU,hpU,hUH,?_,?_⟩
        · intro z hz hzU
          have hzO : I.finalMap z ∈ O := hzU.2
          have hinside := (hside z hz).2
          have he := hlabel (I.finalMap z) hzO (by rw [normMax]; exact ne_of_lt hinside)
          rw [normMax] at he
          refine ⟨hOH hzO,?_⟩
          by_contra hn
          simp [hn,not_lt_of_ge hinside.le] at he
          have h01 : (0 : ZMod 2) ≠ 1 := by decide
          exact h01 (by convert he using 1 <;> decide)
        · exact allNode I (fun z hz => hifix 1 z hz) (Or.inr (fun z hz => (hside z hz).2))
    let G : Set Plane := F ∪ Wᶜ
    have heq : A \ G=A \ F := by
      ext z
      constructor
      · exact fun hz => ⟨hz.1,fun h => hz.2 (Or.inl h)⟩
      · intro hz
        exact ⟨hz.1,fun h => h.elim hz.2 (fun h => h (hAW hz))⟩
    obtain ⟨H,C,N,hC,hout,hfix,hdisj,hN,hrN,hNh,hside,hAll⟩ := jordan A G hA
      (hF.union hW.isClosed_compl) ⟨p,Or.inl hp⟩ r hrA (Or.inl hrF) h hrH hh
    rw [heq] at hdisj hside hAll
    refine ⟨H,C,N,hC,hout,(fun t z hz => hfix t z (Or.inl hz)),
      (fun t z hz => hfix t z (Or.inr hz)),
      hdisj.mono_right (fun z hz => hz.elim Or.inl (fun hz => Or.inr (Or.inl hz))),
      hN,hrN,hNh,hside,?_⟩
    intro v hv _ _ a hva haa
    exact hAll v ⟨hv.1,Or.inl hv.2⟩ a hva haa
  have off : ∃ p : S, p ∉ a.image := by
    have hn : ¬ (M.cover.branch : Set S) ⊆ {a.map (0 : Interval),a.map 1} := by
      intro hh
      have hc := Finset.card_le_card (show M.cover.branch ⊆ {a.map (0 : Interval),a.map 1} from by
        intro z hz
        simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] using hh hz)
      have hb : ({a.map (0 : Interval),a.map 1} : Finset S).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
      rw [M.cover.branch_card] at hc
      omega
    obtain ⟨p,hp,he⟩ := Set.not_subset.mp hn
    refine ⟨p,?_⟩
    rintro ⟨t,rfl⟩
    rcases a.marked_only_at_ends t hp with rfl | rfl
    · exact he (Set.mem_insert _ _)
    · exact he (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨p,hp⟩ := off
  let U : Set S := {z | z ≠ p}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  let e : U ≃ₜ Plane := puncturedPlane M p
  let γ : C(Interval,Plane) := ⟨fun t => e ⟨a.map t,fun he => hp (he ▸ Set.mem_range_self t)⟩,
    e.continuous.comp (a.continuous.subtype_mk _)⟩
  let A : Set Plane := Set.range γ
  have hA : IsJordanCurve A := by
    let f : ℝ → Plane := γ ∘ Set.projIcc 0 1 zero_le_one
    refine ⟨f,⟨(γ.continuous.comp continuous_projIcc).continuousOn,?_,?_⟩,?_⟩
    · simp only [f,Function.comp_apply,Set.projIcc_of_mem zero_le_one (by norm_num : (0:ℝ) ∈ Icc 0 1),Set.projIcc_of_mem zero_le_one (by norm_num : (1:ℝ) ∈ Icc 0 1)]
      change e ⟨a.map 0,_⟩ = e ⟨a.map 1,_⟩
      congr 1
      exact Subtype.ext hloop
    · intro t ht u hu he
      let ti : Interval := ⟨t,ht.1,ht.2.le⟩
      let ui : Interval := ⟨u,hu.1,hu.2.le⟩
      have hg : γ ti = γ ui := by simpa [f,ti,ui,Set.projIcc_of_mem,ht.1,ht.2.le,hu.1,hu.2.le] using he
      have ha : a.map ti = a.map ui := congrArg Subtype.val (e.injective hg)
      rcases a.injective_except_loop_closure ti ui ha with he | he | he
      · exact congrArg Subtype.val he
      · exact (hu.2.ne (congrArg Subtype.val he.2)).elim
      · exact (ht.2.ne (congrArg Subtype.val he.1)).elim
    · ext z
      constructor
      · rintro ⟨t,ht,rfl⟩; exact ⟨Set.projIcc 0 1 zero_le_one t,rfl⟩
      · rintro ⟨t,rfl⟩
        refine ⟨t.val,t.property,?_⟩
        simp [f,Set.projIcc_of_mem]
  let B : Set Plane := e '' {z : U | z.val ∈ F}
  let V : Set Plane := e '' {z : U | z.val ∈ W}
  have hB : IsClosed B := e.isClosedMap _ (hF.preimage continuous_subtype_val)
  have hV : IsOpen V := e.isOpenMap _ (hW.preimage continuous_subtype_val)
  have hstart : γ 0 ∈ B := mem_image_of_mem e (hmarks a.start_marked)
  have hend : γ 1 ∈ B := mem_image_of_mem e (hmarks a.end_marked)
  have hAV : A \ B ⊆ V := by
    rintro z ⟨⟨t,rfl⟩,hz⟩
    apply mem_image_of_mem
    apply hAW
    refine ⟨Set.mem_range_self t,?_⟩
    intro hf
    exact hz (mem_image_of_mem e hf)
  have hrU : r ∈ U := fun he => hp (he ▸ hrA)
  let coeChart : OpenPartialHomeomorph U S :=
    (⟨U,hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe ⟨⟨r,hrU⟩⟩
  let h : OpenPartialHomeomorph Plane (ℝ × ℝ) :=
    e.symm.toOpenPartialHomeomorph.trans (coeChart.trans k)
  have hsource (z : Plane) : z ∈ h.source ↔ (e.symm z).val ∈ k.source := by
    simp [h,OpenPartialHomeomorph.trans_source,coeChart]
    rfl
  have happly (z : Plane) : h z = k (e.symm z).val := rfl
  have hAeq (z : Plane) : z ∈ A ↔ (e.symm z).val ∈ a.image := by
    constructor
    · rintro ⟨t,rfl⟩
      change (e.symm (e _)).val ∈ a.image
      rw [e.symm_apply_apply]
      exact mem_range_self _
    · rintro ⟨t,ht⟩
      refine ⟨t,?_⟩
      apply e.symm.injective
      change e.symm (e _) = e.symm z
      rw [e.symm_apply_apply]
      exact Subtype.ext ht
  have hrPlanar : e ⟨r,hrU⟩ ∈ A := by rw [hAeq,e.symm_apply_apply]; exact hrA
  have hrB : e ⟨r,hrU⟩ ∈ B := mem_image_of_mem e hrF
  have hrh : e ⟨r,hrU⟩ ∈ h.source := by rw [hsource,e.symm_apply_apply]; exact hrK
  have hchart : ∀ z ∈ h.source, z ∈ A ↔ (h z).1=0 := by
    intro z hz
    rw [hAeq,happly]
    exact hk _ ((hsource z).mp hz)
  have hrp : e ⟨r,hrU⟩ ≠ γ 0 := by
    intro he
    exact hr0 (congrArg Subtype.val (e.injective he))
  have hrq : e ⟨r,hrU⟩ ≠ γ 1 := by
    intro he
    exact hr1 (congrArg Subtype.val (e.injective he))
  obtain ⟨K,C,N,hC,hout,hfix,houtside,hdisj,hN,hrN,hNh,hside,hAll⟩ :=
    planar A B V (γ 0) (γ 1) hA hB hV hstart hend hAV
      (e ⟨r,hrU⟩) hrPlanar hrB hrp hrq h hrh hchart
  let ee : U ≃ₜ (Set.univ : Set Plane) := e.trans (Homeomorph.Set.univ Plane).symm
  obtain ⟨KU,H,hcoords,hlift,hexterior⟩ := position_surface_chart_lift S U univ hU ee C hC (Set.subset_univ C) K hout
  have coord (t : Interval) (z : U) : e ⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩ = K.map (t,e z) := by
    have hs : (⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩ : U) = KU.map (t,z) := Subtype.ext (hlift t z)
    rw [hs]
    exact hcoords t z
  have fix : ∀ t z, z ∈ F → H.map (t,z) = z := by
    intro t z hz
    by_cases hu : z ∈ U
    · have hh := coord t ⟨z,hu⟩
      rw [hfix t (e ⟨z,hu⟩) (mem_image_of_mem e hz)] at hh
      exact congrArg Subtype.val (e.injective hh)
    · exact hexterior t z hu
  have outside : ∀ t z, z ∉ W → H.map (t,z) = z := by
    intro t z hz
    by_cases hu : z ∈ U
    · have hn : e ⟨z,hu⟩ ∉ V := by
        rintro ⟨v,hv,he⟩
        have hev : v.val = z := congrArg Subtype.val (e.injective he)
        exact hz (hev ▸ hv)
      have hh := coord t ⟨z,hu⟩
      rw [houtside t _ hn] at hh
      exact congrArg Subtype.val (e.injective hh)
    · exact hexterior t z hu
  have disj : Disjoint (H.finalMap '' (a.image \ F)) (a.image ∪ F) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨w,⟨hw,hwF⟩,rfl⟩ hz
    have hwU : w ∈ U := fun he => hp (he ▸ hw)
    let wu : U := ⟨w,hwU⟩
    have hwB : e wu ∉ B := by
      rintro ⟨u,hu,he⟩
      have huval := congrArg Subtype.val (e.injective he)
      change u.val = w at huval
      exact hwF (huval ▸ hu)
    have hwA : e wu ∈ A := by
      obtain ⟨t,ht⟩ := hw
      exact ⟨t,congrArg e (Subtype.ext ht)⟩
    have htarget : H.finalMap w ∈ U := by
      change H.map (1,w) ∈ U
      rw [hlift 1 wu]
      exact (KU.map (1,wu)).property
    apply Set.disjoint_left.mp hdisj
    · refine ⟨e wu,⟨hwA,hwB⟩,(coord 1 wu).symm⟩
    · rcases hz with hz | hz
      · left
        obtain ⟨t,ht⟩ := hz
        exact ⟨t,congrArg e (Subtype.ext ht)⟩
      · exact Or.inr (mem_image_of_mem e hz)
  let Nsurf : Set S := Subtype.val '' (e ⁻¹' N)
  have hNs : IsOpen Nsurf := hU.isOpenMap_subtype_val _ (hN.preimage e.continuous)
  have hrNs : r ∈ Nsurf := ⟨⟨r,hrU⟩,hrN,rfl⟩
  have hNsK : Nsurf ⊆ k.source := by
    rintro z ⟨u,hu,rfl⟩
    have hh := (hsource (e u)).mp (hNh hu)
    simpa only [e.symm_apply_apply] using hh
  refine ⟨H,Nsurf,fix,outside,disj,hNs,hrNs,hNsK,?_,?_⟩
  · intro z hz hzN
    obtain ⟨u,hu,rfl⟩ := hzN
    have huA : e u ∈ A := (hAeq _).mpr (by simpa only [e.symm_apply_apply] using hz.1)
    have huB : e u ∉ B := by
      rintro ⟨v,hv,he⟩
      exact hz.2 (congrArg Subtype.val (e.injective he) ▸ hv)
    have hs := hside (e u) ⟨huA,huB⟩ hu
    have hstay : H.finalMap u.val ∈ U := by
      change H.map (1,u.val) ∈ U
      rw [hlift 1 u]
      exact (KU.map (1,u)).property
    have he := coord 1 u
    have hinv : (e.symm (K.finalMap (e u))).val=H.finalMap u.val := by
      change (e.symm (K.map (1,e u))).val=H.map (1,u.val)
      rw [←he,e.symm_apply_apply]
    refine ⟨?_,?_⟩
    · rw [←hinv]
      exact (hsource _).mp hs.1
    · rw [←hinv]
      exact (happly _).symm ▸ hs.2
  · intro v hv hv0 hv1 a hva haa
    have hvU : v ∈ U := fun he => hp (he ▸ hv.1)
    let c := e.symm.toOpenPartialHomeomorph.trans (coeChart.trans a)
    have csource (z : Plane) : z ∈ c.source ↔ (e.symm z).val ∈ a.source := by
      simp [c,OpenPartialHomeomorph.trans_source,coeChart]
      rfl
    have capply (z : Plane) : c z=a (e.symm z).val := rfl
    have hvA : e ⟨v,hvU⟩ ∈ A := by
      rw [hAeq,e.symm_apply_apply]
      exact hv.1
    have hvB : e ⟨v,hvU⟩ ∈ B := mem_image_of_mem e hv.2
    have hvp : e ⟨v,hvU⟩ ≠ γ 0 := by
      intro hh
      exact hv0 (congrArg Subtype.val (e.injective hh))
    have hvq : e ⟨v,hvU⟩ ≠ γ 1 := by
      intro hh
      exact hv1 (congrArg Subtype.val (e.injective hh))
    have hvc : e ⟨v,hvU⟩ ∈ c.source := by
      rw [csource,e.symm_apply_apply]
      exact hva
    have hcc : ∀ z ∈ c.source, z ∈ A ↔ (c z).1=0 := by
      intro z hz
      rw [hAeq,capply]
      exact haa _ ((csource _).mp hz)
    obtain ⟨σ,V0,hV0,hvV0,hV0c,hdir⟩ := hAll (e ⟨v,hvU⟩) ⟨hvA,hvB⟩ hvp hvq c hvc hcc
    let Vs : Set S := Subtype.val '' (e ⁻¹' V0)
    have hVs : IsOpen Vs := hU.isOpenMap_subtype_val _ (hV0.preimage e.continuous)
    have hvVs : v ∈ Vs := ⟨⟨v,hvU⟩,hvV0,rfl⟩
    have hVsa : Vs ⊆ a.source := by
      rintro z ⟨u,hu,rfl⟩
      have hm := (csource (e u)).mp (hV0c hu)
      simpa only [e.symm_apply_apply] using hm
    refine ⟨σ,Vs,hVs,hvVs,hVsa,?_⟩
    intro z hz hzV
    obtain ⟨u,hu,rfl⟩ := hzV
    have huA : e u ∈ A := (hAeq _).mpr (by simpa only [e.symm_apply_apply] using hz.1)
    have huB : e u ∉ B := by
      rintro ⟨v,hv,he⟩
      exact hz.2 (congrArg Subtype.val (e.injective he) ▸ hv)
    have hs := hdir (e u) ⟨huA,huB⟩ hu
    have hh := coord 1 u
    have hinv : (e.symm (K.finalMap (e u))).val=H.finalMap u.val := by
      change (e.symm (K.map (1,e u))).val=H.map (1,u.val)
      rw [←hh,e.symm_apply_apply]
    refine ⟨?_,?_⟩
    · rw [←hinv]
      exact (csource _).mp hs.1
    · rw [←hinv]
      exact (capply _).symm ▸ hs.2

private theorem actualSourceSurgery_nonloopRibbon_7 (M : HyperellipticModel E S) (a : MarkedArc M)
(hnonloop : a.map (0 : Interval) ≠ a.map 1)
(F W : Set S) (hF : IsClosed F) (hmarks : (M.cover.branch : Set S) ⊆ F)
(hW : IsOpen W) (hAW : a.image \ F ⊆ W)
(r : S) (hrA : r ∈ a.image) (hrF : r ∈ F)
(hr0 : r ≠ a.map 0) (hr1 : r ≠ a.map 1)
(k : OpenPartialHomeomorph S (ℝ × ℝ)) (hrK : r ∈ k.source)
(hk : ∀ z ∈ k.source, z ∈ a.image ↔ (k z).1=0) :
∃ (H : AmbientIsotopy S) (N : Set S),
  (∀ t z, z ∈ F → H.map (t,z)=z) ∧
  (∀ t z, z ∉ W → H.map (t,z)=z) ∧
  Disjoint (H.finalMap '' (a.image \ F)) (a.image ∪ F) ∧
  IsOpen N ∧ r ∈ N ∧ N ⊆ k.source ∧
  (∀ z, z ∈ a.image \ F → z ∈ N →
    H.finalMap z ∈ k.source ∧ 0 < (k (H.finalMap z)).1) ∧
  ∀ v ∈ a.image ∩ F, v ≠ a.map 0 → v ≠ a.map 1 →
    ∀ c : OpenPartialHomeomorph S (ℝ × ℝ), v ∈ c.source →
      (∀ z ∈ c.source, z ∈ a.image ↔ (c z).1=0) →
      ∃ (σ : Bool) (V : Set S), IsOpen V ∧ v ∈ V ∧ V ⊆ c.source ∧
        ∀ z, z ∈ a.image \ F → z ∈ V → H.finalMap z ∈ c.source ∧
          (if σ then 0 < (c (H.finalMap z)).1 else (c (H.finalMap z)).1 < 0) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  have planar (A F W : Set Plane) (p q : Plane) (hA : IsArcBetween A p q)
  (hF : IsClosed F) (hW : IsOpen W) (hpF : p ∈ F) (hqF : q ∈ F)
  (hAW : A \ F ⊆ W) (r : Plane) (hrA : r ∈ A) (hrF : r ∈ F)
  (hrp : r ≠ p) (hrq : r ≠ q)
  (h : OpenPartialHomeomorph Plane (ℝ × ℝ)) (hrH : r ∈ h.source)
  (hh : ∀ z ∈ h.source, z ∈ A ↔ (h z).1 = 0) :
  ∃ (H : AmbientIsotopy Plane) (C U : Set Plane),
    IsCompact C ∧ (∀ t z, z ∉ C → H.map (t,z) = z) ∧
    (∀ t z, z ∈ F → H.map (t,z) = z) ∧
    (∀ t z, z ∉ W → H.map (t,z) = z) ∧
    Disjoint (H.finalMap '' (A \ F)) (A ∪ F) ∧
    IsOpen U ∧ r ∈ U ∧ U ⊆ h.source ∧
    (∀ z, z ∈ A \ F → z ∈ U →
      H.finalMap z ∈ h.source ∧ 0 < (h (H.finalMap z)).1) ∧
    ∀ v ∈ A ∩ F, v ≠ p → v ≠ q →
      ∀ a : OpenPartialHomeomorph Plane (ℝ × ℝ), v ∈ a.source →
        (∀ z ∈ a.source, z ∈ A ↔ (a z).1=0) →
        ∃ (σ : Bool) (V : Set Plane), IsOpen V ∧ v ∈ V ∧ V ⊆ a.source ∧
          ∀ z, z ∈ A \ F → z ∈ V → H.finalMap z ∈ a.source ∧
            (if σ then 0 < (a (H.finalMap z)).1 else (a (H.finalMap z)).1 < 0) := by
    have sideJordan (A F : Set Plane) (hA : IsJordanCurve A)
    (hF : IsClosed F) (hne : F.Nonempty) (p : Plane) (hpA : p ∈ A) (hpF : p ∈ F)
    (h : OpenPartialHomeomorph Plane (ℝ × ℝ)) (hpH : p ∈ h.source)
    (hh : ∀ z ∈ h.source, z ∈ A ↔ (h z).1 = 0) :
    ∃ (H : AmbientIsotopy Plane) (C U : Set Plane),
      IsCompact C ∧ (∀ t z, z ∉ C → H.map (t,z) = z) ∧
      (∀ t z, z ∈ F → H.map (t,z) = z) ∧
      Disjoint (H.finalMap '' (A \ F)) (A ∪ F) ∧
      IsOpen U ∧ p ∈ U ∧ U ⊆ h.source ∧
      (∀ z, z ∈ A \ F → z ∈ U →
        H.finalMap z ∈ h.source ∧ 0 < (h (H.finalMap z)).1) ∧
      ∀ q ∈ A ∩ F, ∀ a : OpenPartialHomeomorph Plane (ℝ × ℝ), q ∈ a.source →
        (∀ z ∈ a.source, z ∈ A ↔ (a z).1=0) →
        ∃ (σ : Bool) (V : Set Plane), IsOpen V ∧ q ∈ V ∧ V ⊆ a.source ∧
          ∀ z, z ∈ A \ F → z ∈ V → H.finalMap z ∈ a.source ∧
            (if σ then 0 < (a (H.finalMap z)).1 else (a (H.finalMap z)).1 < 0) := by
      have bidirectional (A F : Set Plane) (hA : IsJordanCurve A)
        (hF : IsClosed F) (hne : F.Nonempty) :
        ∃ (L : Plane ≃ₜ (ℝ × ℝ)) (H I : AmbientIsotopy Plane) (C : Set Plane),
          IsCompact C ∧
          (∀ t z, z ∉ C → H.map (t,z) = z) ∧
          (∀ t z, z ∉ C → I.map (t,z) = z) ∧
          (∀ t z, z ∈ F → H.map (t,z) = z) ∧
          (∀ t z, z ∈ F → I.map (t,z) = z) ∧
          Disjoint (H.finalMap '' (A \ F)) (A ∪ F) ∧
          Disjoint (I.finalMap '' (A \ F)) (A ∪ F) ∧
          L '' A = {z : ℝ × ℝ | ‖z‖ = 1} ∧
          ∀ z, z ∈ A \ F →
            1 < ‖L (H.finalMap z)‖ ∧ ‖L (I.finalMap z)‖ < 1 := by
        have outward (A F : Set Plane) (hA : IsJordanCurve A)
            (hF : IsClosed F) (hne : F.Nonempty) :
            ∃ (L : Plane ≃ₜ (ℝ × ℝ)) (H : AmbientIsotopy Plane) (C : Set Plane),
              IsCompact C ∧ (∀ t z, z ∉ C → H.map (t,z) = z) ∧
              (∀ t z, z ∈ F → H.map (t,z) = z) ∧
              Disjoint (H.finalMap '' (A \ F)) (A ∪ F) ∧
              L '' A = {z : ℝ × ℝ | ‖z‖ = 1} ∧
              (∀ t z, z ∈ A \ F → 0 < t.val → 1 < ‖L (H.map (t,z))‖) ∧
              ∀ t z, ‖L z‖ ≤ ‖L (H.map (t,z))‖ := by

          have ribbon : ∀ (F : Set (ℝ × ℝ)) (hF : IsClosed F) (hne : F.Nonempty),
              ∃ H : AmbientIsotopy (ℝ × ℝ),
                (∀ t z, z ∈ F → H.map (t,z) = z) ∧
                (∀ t z, ‖z‖ ≤ 1/2 ∨ 3/2 ≤ ‖z‖ → H.map (t,z) = z) ∧
                Disjoint (H.finalMap '' ({z : ℝ × ℝ | ‖z‖ = 1} \ F))
                  ({z : ℝ × ℝ | ‖z‖ = 1} ∪ F) ∧
                (∀ t z, ‖z‖ = 1 → z ∉ F → 0 < t.val → 1 < ‖H.map (t,z)‖) ∧
                ∀ t z, ‖z‖ ≤ ‖H.map (t,z)‖ := by
            intro F hF hne
            have radial : ∀ (h : (ℝ × ℝ) → ℝ) (hc : Continuous h)
                (hp : ∀ z, 0 ≤ h z) (hb : ∀ z, h z ≤ 1/8),
                ∃ H : AmbientIsotopy (ℝ × ℝ),
                  (∀ t z, H.map (t,z) =
                    ((‖z‖ + max 0 (t.val*h (‖z‖⁻¹ • z)-|‖z‖-1|/2))/‖z‖) • z) ∧
                  (∀ t z, h (‖z‖⁻¹ • z) = 0 → H.map (t,z) = z) ∧
                  (∀ z, ‖z‖ = 1 → ‖H.finalMap z‖ = 1+h z) := by
              intro h hc hp hb
              have inverse : ∀ (h : (ℝ × ℝ) → ℝ) (hp : ∀ z, 0 ≤ h z) (hb : ∀ z, h z ≤ 1/8),
                  let d := fun z : ℝ × ℝ => ‖z‖⁻¹ • z
                  let R := fun z : ℝ × ℝ => ‖z‖ + max 0 (h (d z) - |‖z‖-1|/2)
                  let Q := fun z : ℝ × ℝ => ‖z‖ - max 0 (min ((‖z‖-1+2*h (d z))/3) (2*h (d z)-(‖z‖-1)))
                  let f := fun z : ℝ × ℝ => (R z / ‖z‖) • z
                  let g := fun z : ℝ × ℝ => (Q z / ‖z‖) • z
                  Function.LeftInverse g f ∧ Function.RightInverse g f := by
                intro h hp hb
                have scalar : ∀ (k r : ℝ) (hk : 0 ≤ k) (hkb : k ≤ 1/8) (hr : 0 ≤ r),
                    let f := fun y : ℝ => y + max 0 (k - |y|/2)
                    let g := fun y : ℝ => y - max 0 (min ((y+2*k)/3) (2*k-y))
                    0 ≤ 1 + f (r-1) ∧ 0 ≤ 1 + g (r-1) ∧
                    (1 + f (r-1) = 0 ↔ r = 0) ∧
                    (1 + g (r-1) = 0 ↔ r = 0) ∧
                    (r ≤ 1/2 → 1 + f (r-1) = r ∧ 1 + g (r-1) = r) ∧
                    1 + g (f (r-1)) = r ∧ 1 + f (g (r-1)) = r := by
                  intro k r hk hkb hr
                  let f : ℝ → ℝ → ℝ := fun k y => y + max 0 (k - |y|/2)
                  let g : ℝ → ℝ → ℝ := fun k z => z - max 0 (min ((z+2*k)/3) (2*k-z))
                  have left (k : ℝ) (hk : 0 ≤ k) (y : ℝ) : g k (f k y) = y := by
                    by_cases hy0 : y ≤ 0
                    ·
                      by_cases hy : y ≤ -2*k
                      · have hf : f k y = y := by
                          dsimp [f]
                          rw [abs_of_nonpos hy0, max_eq_left (by linarith)]
                          ring
                        rw [hf]
                        dsimp [g]
                        have h1 : (y+2*k)/3 ≤ 2*k-y := by linarith
                        rw [min_eq_left h1,max_eq_left (by linarith)]
                        ring
                      · have hf : f k y = 3/2*y+k := by
                          dsimp [f]
                          rw [abs_of_nonpos hy0,max_eq_right (by linarith)]
                          ring
                        rw [hf]
                        dsimp [g]
                        have h1 : ((3/2*y+k)+2*k)/3 ≤ 2*k-(3/2*y+k) := by linarith
                        rw [min_eq_left h1,max_eq_right (by linarith)]
                        ring
                    · have hy0' : 0 ≤ y := (not_le.mp hy0).le
                      by_cases hy : 2*k ≤ y
                      · have hf : f k y = y := by
                          dsimp [f]
                          rw [abs_of_nonneg hy0',max_eq_left (by linarith)]
                          ring
                        rw [hf]
                        dsimp [g]
                        have h1 : 2*k-y ≤ (y+2*k)/3 := by linarith
                        rw [min_eq_right h1,max_eq_left (by linarith)]
                        ring
                      · have hf : f k y = 1/2*y+k := by
                          dsimp [f]
                          rw [abs_of_nonneg hy0',max_eq_right (by linarith)]
                          ring
                        rw [hf]
                        dsimp [g]
                        have h1 : 2*k-(1/2*y+k) ≤ ((1/2*y+k)+2*k)/3 := by linarith
                        rw [min_eq_right h1,max_eq_right (by linarith)]
                        ring
                  have right (k : ℝ) (hk : 0 ≤ k) (z : ℝ) : f k (g k z) = z := by
                    by_cases hz : z ≤ -2*k
                    · have hg : g k z = z := by
                        dsimp [g]
                        rw [min_eq_left (by linarith),max_eq_left (by linarith)]
                        ring
                      rw [hg]
                      dsimp [f]
                      rw [abs_of_nonpos (by linarith),max_eq_left (by linarith)]
                      ring
                    · by_cases hz2 : 2*k ≤ z
                      · have hg : g k z = z := by
                          dsimp [g]
                          rw [min_eq_right (by linarith),max_eq_left (by linarith)]
                          ring
                        rw [hg]
                        dsimp [f]
                        rw [abs_of_nonneg (by linarith),max_eq_left (by linarith)]
                        ring
                      · by_cases hzk : z ≤ k
                        · have hg : g k z = 2/3*(z-k) := by
                            dsimp [g]
                            rw [min_eq_left (by linarith),max_eq_right (by linarith)]
                            ring
                          rw [hg]
                          dsimp [f]
                          rw [abs_of_nonpos (by linarith),max_eq_right (by linarith)]
                          ring
                        · have hg : g k z = 2*(z-k) := by
                            dsimp [g]
                            rw [min_eq_right (by linarith),max_eq_right (by linarith)]
                            ring
                          rw [hg]
                          dsimp [f]
                          rw [abs_of_nonneg (by linarith),max_eq_right (by linarith)]
                          ring
                  change 0 ≤ 1 + f k (r-1) ∧ 0 ≤ 1 + g k (r-1) ∧ _
                  have small (r : ℝ) (hr : r ≤ 1/2) :
                      1 + f k (r-1) = r ∧ 1 + g k (r-1) = r := by
                    constructor
                    · dsimp [f]
                      rw [abs_of_nonpos (by linarith),max_eq_left (by linarith)]
                      ring
                    · dsimp [g]
                      rw [min_eq_left (by linarith),max_eq_left (by linarith)]
                      ring
                  have fp : 0 ≤ 1 + f k (r-1) := by
                    dsimp [f]; have := le_max_left 0 (k-|r-1|/2); linarith
                  have gp : 0 ≤ 1 + g k (r-1) := by
                    by_cases hs : r ≤ 1/2
                    · rw [(small r hs).2]; exact hr
                    · have hm : max 0 (min ((r-1+2*k)/3) (2*k-(r-1))) ≤ r := by
                        apply max_le
                        · exact hr
                        · exact (min_le_left _ _).trans (by linarith)
                      dsimp [g]; linarith
                  refine ⟨fp,gp,?_,?_,small r,?_,?_⟩
                  · constructor
                    · intro he
                      dsimp [f] at he
                      have := le_max_left 0 (k-|r-1|/2)
                      linarith
                    · intro he; subst r; exact (small 0 (by norm_num)).1
                  · constructor
                    · intro he
                      by_cases hs : r ≤ 1/2
                      · rw [(small r hs).2] at he; exact he
                      · have hm : max 0 (min ((r-1+2*k)/3) (2*k-(r-1))) < r := by
                          apply max_lt
                          · linarith
                          · exact (min_le_left _ _).trans_lt (by linarith)
                        dsimp [g] at he
                        linarith
                    · intro he; subst r; exact (small 0 (by norm_num)).2
                  · change 1 + g k (f k (r-1)) = r
                    rw [left k hk]; ring
                  · change 1 + f k (g k (r-1)) = r
                    rw [right k hk]; ring
                dsimp only
                let d := fun z : ℝ × ℝ => ‖z‖⁻¹ • z
                let R := fun z : ℝ × ℝ => ‖z‖ + max 0 (h (d z) - |‖z‖-1|/2)
                let Q := fun z : ℝ × ℝ => ‖z‖ - max 0 (min ((‖z‖-1+2*h (d z))/3) (2*h (d z)-(‖z‖-1)))
                let f := fun z : ℝ × ℝ => (R z / ‖z‖) • z
                let g := fun z : ℝ × ℝ => (Q z / ‖z‖) • z
                change Function.LeftInverse g f ∧ Function.RightInverse g f
                have radial (A : (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) (hz : z ≠ 0) (hA : 0 < A z) :
                    ‖(A z / ‖z‖) • z‖ = A z ∧ d ((A z / ‖z‖) • z) = d z := by
                  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
                  have hr : 0 ≤ A z / ‖z‖ := (div_pos hA hn).le
                  have he : ‖(A z / ‖z‖) • z‖ = A z := by
                    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
                    field_simp
                  refine ⟨he,?_⟩
                  dsimp [d]
                  rw [he,smul_smul]
                  congr 1
                  field_simp
                have posR (z : ℝ × ℝ) (hz : z ≠ 0) : 0 < R z := by
                  have hs := scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)
                  have he : 1 + (‖z‖-1 + max 0 (h (d z)-|‖z‖-1|/2)) = R z := by dsimp [R]; ring
                  dsimp only at hs
                  rw [he] at hs
                  exact lt_of_le_of_ne hs.1 (Ne.symm (fun hh => hz (norm_eq_zero.mp (hs.2.2.1.mp hh))))
                have posQ (z : ℝ × ℝ) (hz : z ≠ 0) : 0 < Q z := by
                  have hs := scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)
                  have he : 1 + (‖z‖-1 - max 0 (min ((‖z‖-1+2*h (d z))/3) (2*h (d z)-(‖z‖-1)))) = Q z := by dsimp [Q]; ring
                  dsimp only at hs
                  rw [he] at hs
                  exact lt_of_le_of_ne hs.2.1 (Ne.symm (fun hh => hz (norm_eq_zero.mp (hs.2.2.2.1.mp hh))))
                constructor
                · intro z
                  by_cases hz : z = 0
                  · subst z; simp [f,g]
                  have hn := norm_pos_iff.mpr hz
                  obtain ⟨hfn,hfd⟩ := radial R z hz (posR z hz)
                  have hQ : Q (f z) = ‖z‖ := by
                    dsimp [Q]
                    rw [hfn]
                    change R z - max 0 (min ((R z-1+2*h (d (f z)))/3) (2*h (d (f z))-(R z-1))) = ‖z‖
                    rw [hfd]
                    have hs := (scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)).2.2.2.2.2.1
                    dsimp [R]
                    convert hs using 1 <;> ring_nf
                  change (Q (f z) / ‖f z‖) • ((R z / ‖z‖) • z) = z
                  rw [hQ,hfn,smul_smul]
                  have he : (‖z‖/R z)*(R z/‖z‖) = 1 := by field_simp [ne_of_gt hn,ne_of_gt (posR z hz),ne_of_gt (posQ z hz)]
                  rw [he,one_smul]
                · intro z
                  by_cases hz : z = 0
                  · subst z; simp [f,g]
                  have hn := norm_pos_iff.mpr hz
                  obtain ⟨hgn,hgd⟩ := radial Q z hz (posQ z hz)
                  have hR : R (g z) = ‖z‖ := by
                    dsimp [R]
                    rw [hgn]
                    change Q z + max 0 (h (d (g z))-|Q z-1|/2) = ‖z‖
                    rw [hgd]
                    have hs := (scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)).2.2.2.2.2.2
                    dsimp [Q]
                    convert hs using 1 <;> ring_nf
                  change (R (g z) / ‖g z‖) • ((Q z / ‖z‖) • z) = z
                  rw [hR,hgn,smul_smul]
                  have he : (‖z‖/Q z)*(Q z/‖z‖) = 1 := by field_simp [ne_of_gt hn,ne_of_gt (posR z hz),ne_of_gt (posQ z hz)]
                  rw [he,one_smul]
              let d := fun z : ℝ × ℝ => ‖z‖⁻¹ • z
              let R := fun z : Interval × (ℝ × ℝ) => ‖z.2‖ + max 0 (z.1.val*h (d z.2)-|‖z.2‖-1|/2)
              let Q := fun z : Interval × (ℝ × ℝ) => ‖z.2‖ - max 0 (min ((‖z.2‖-1+2*(z.1.val*h (d z.2)))/3) (2*(z.1.val*h (d z.2))-(‖z.2‖-1)))
              let f := fun z : Interval × (ℝ × ℝ) => (R z / ‖z.2‖) • z.2
              let g := fun z : Interval × (ℝ × ℝ) => (Q z / ‖z.2‖) • z.2
              have small (z : Interval × (ℝ × ℝ)) (hz : ‖z.2‖ < 1/2) : f z = z.2 ∧ g z = z.2 := by
                have hkp : 0 ≤ z.1.val * h (d z.2) := mul_nonneg z.1.property.1 (hp _)
                have hk : z.1.val * h (d z.2) ≤ 1/8 := (mul_le_of_le_one_left (hp _) z.1.property.2).trans (hb _)
                have hR : R z = ‖z.2‖ := by
                  dsimp [R]
                  rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
                  ring
                have hQ : Q z = ‖z.2‖ := by
                  dsimp [Q]
                  rw [min_eq_left (by linarith),max_eq_left (by linarith)]
                  ring
                by_cases he : z.2 = 0
                · simp [f,g,he]
                · have hn : ‖z.2‖ ≠ 0 := norm_ne_zero_iff.mpr he
                  simp [f,g,hR,hQ,hn]
              have cont : Continuous f ∧ Continuous g := by
                constructor <;> rw [continuous_iff_continuousAt] <;> intro z
                · by_cases hz : z.2 = 0
                  · have hh : ∀ᶠ w in 𝓝 z, ‖w.2‖ < 1/2 :=
                      (continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds (by simp [hz]))
                    apply continuous_snd.continuousAt.congr_of_eventuallyEq
                    filter_upwards [hh] with w hw
                    exact (small w hw).1
                  · dsimp [f,R,d]
                    fun_prop (disch := exact norm_ne_zero_iff.mpr hz)
                · by_cases hz : z.2 = 0
                  · have hh : ∀ᶠ w in 𝓝 z, ‖w.2‖ < 1/2 :=
                      (continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds (by simp [hz]))
                    apply continuous_snd.continuousAt.congr_of_eventuallyEq
                    filter_upwards [hh] with w hw
                    exact (small w hw).2
                  · dsimp [g,Q,d]
                    fun_prop (disch := exact norm_ne_zero_iff.mpr hz)
              let e : Interval → (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := fun t => {
                toEquiv := {
                  toFun := fun z => f (t,z)
                  invFun := fun z => g (t,z)
                  left_inv := (inverse (fun z => t.val*h z)
                    (fun z => mul_nonneg t.property.1 (hp z))
                    (fun z => (mul_le_of_le_one_left (hp z) t.property.2).trans (hb z))).1
                  right_inv := (inverse (fun z => t.val*h z)
                    (fun z => mul_nonneg t.property.1 (hp z))
                    (fun z => (mul_le_of_le_one_left (hp z) t.property.2).trans (hb z))).2 }
                continuous_toFun := cont.1.comp (continuous_const.prodMk continuous_id)
                continuous_invFun := cont.2.comp (continuous_const.prodMk continuous_id) }
              let H : AmbientIsotopy (ℝ × ℝ) := {
                map := ⟨f,cont.1⟩
                homeomorphism_at := fun t => ⟨e t,fun z => rfl⟩
                at_zero := by
                  intro z
                  by_cases hz : z = 0
                  · simp [f,hz]
                  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
                    change ((‖z‖+max 0 (0*h (d z)-|‖z‖-1|/2))/‖z‖) • z = z
                    rw [zero_mul,zero_sub,max_eq_left (neg_nonpos.mpr (div_nonneg (abs_nonneg _) (by norm_num))),add_zero,div_self hn,one_smul] }
              refine ⟨H,fun t z => rfl,?_,?_⟩
              · intro t z hz
                by_cases he : z = 0
                · simp [H,f,he]
                · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr he
                  change ((‖z‖+max 0 (t.val*h (d z)-|‖z‖-1|/2))/‖z‖) • z = z
                  rw [hz,mul_zero,zero_sub,max_eq_left (neg_nonpos.mpr (div_nonneg (abs_nonneg _) (by norm_num))),add_zero,div_self hn,one_smul]
              · intro z hz
                change ‖((‖z‖+max 0 (1*h (d z)-|‖z‖-1|/2))/‖z‖) • z‖ = _
                simp [d,hz,norm_smul,Real.norm_eq_abs,max_eq_right (hp z),abs_of_nonneg (by linarith [hp z] : 0 ≤ 1+h z)]
            let h : (ℝ × ℝ) → ℝ := fun z => min (1/8) (infDist z F/8)
            have hc : Continuous h := continuous_const.min ((Metric.continuous_infDist_pt F).div_const 8)
            have hp : ∀ z, 0 ≤ h z := fun z => le_min (by norm_num) (div_nonneg infDist_nonneg (by norm_num))
            have hb : ∀ z, h z ≤ 1/8 := fun z => min_le_left _ _
            obtain ⟨H,hmap,hzero,hnorm⟩ := radial h hc hp hb
            have distdir (z : ℝ × ℝ) (hz : z ≠ 0) : dist (‖z‖⁻¹ • z) z = |‖z‖-1| := by
              have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
              have hd : ‖‖z‖⁻¹ • z‖ = 1 := by
                rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
                exact inv_mul_cancel₀ hn
              have he : (‖z‖ : ℝ) • (‖z‖⁻¹ • z) = z := by rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
              calc
                dist (‖z‖⁻¹ • z) z = ‖(1-‖z‖) • (‖z‖⁻¹ • z)‖ := by rw [dist_eq_norm,sub_smul,one_smul,he]
                _ = |‖z‖-1| := by rw [norm_smul,Real.norm_eq_abs,hd,mul_one,abs_sub_comm]
            have fix : ∀ t z, z ∈ F → H.map (t,z) = z := by
              intro t z hz
              by_cases he : z = 0
              · subst z; rw [hmap]; simp
              have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr he
              have hi : infDist (‖z‖⁻¹ • z) F ≤ |‖z‖-1| := by
                rw [←distdir z he]
                exact infDist_le_dist_of_mem hz
              have hh : h (‖z‖⁻¹ • z) ≤ |‖z‖-1|/8 := (min_le_right _ _).trans (div_le_div_of_nonneg_right hi (by norm_num))
              have ht : t.val*h (‖z‖⁻¹ • z) ≤ h (‖z‖⁻¹ • z) := mul_le_of_le_one_left (hp _) t.property.2
              rw [hmap,max_eq_left (by have := abs_nonneg (‖z‖-1); linarith),add_zero,div_self hn,one_smul]
            refine ⟨H,fix,?_,?_,?_,?_⟩
            · intro t z hz
              by_cases he : z = 0
              · subst z; rw [hmap]; simp
              have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr he
              have ht : t.val*h (‖z‖⁻¹ • z) ≤ 1/8 := (mul_le_of_le_one_left (hp _) t.property.2).trans (hb _)
              have ha : 1/2 ≤ |‖z‖-1| := by
                rcases hz with hz | hz
                · rw [abs_of_nonpos (by linarith)]; linarith
                · rw [abs_of_nonneg (by linarith)]; linarith
              rw [hmap,max_eq_left (by linarith),add_zero,div_self hn,one_smul]
            · apply Set.disjoint_left.mpr
              rintro z ⟨w,⟨hw,hwF⟩,rfl⟩ hz
              rcases hz with hz | hz
              · have hpw : 0 < h w := by
                  apply lt_min (by norm_num)
                  exact div_pos ((hF.notMem_iff_infDist_pos hne).mp hwF) (by norm_num)
                have he := hnorm w hw
                change ‖H.finalMap w‖ = 1 at hz
                linarith
              · obtain ⟨e,he⟩ := H.homeomorphism_at (1 : Interval)
                have heq : H.finalMap w = w := e.injective (by
                  rw [he,he]
                  exact (fix 1 (H.finalMap w) hz).trans rfl)
                exact hwF (heq ▸ hz)
            · intro t z hz hzF ht
              have hpos : 0 < h z := lt_min (by norm_num)
                (div_pos ((hF.notMem_iff_infDist_pos hne).mp hzF) (by norm_num))
              have htz : 0 < t.val * h z := mul_pos ht hpos
              have norm_eq : ‖H.map (t,z)‖ = 1 + t.val * h z := by
                rw [hmap]
                simp only [hz,inv_one,one_smul,sub_self,abs_zero,zero_div,sub_zero,div_one]
                rw [max_eq_right htz.le,norm_smul,Real.norm_eq_abs,hz,mul_one,
                  abs_of_pos (by linarith : 0 < 1 + t.val * h z)]
              rw [norm_eq]
              linarith
            · intro t z
              rw [hmap,norm_smul,Real.norm_eq_abs]
              by_cases hz : z = 0
              · simp [hz]
              have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
              have hr : 0 ≤ ‖z‖ + max 0 (t.val*h (‖z‖⁻¹ • z)-|‖z‖-1|/2) :=
                add_nonneg (norm_nonneg _) (le_max_left _ _)
              rw [abs_of_nonneg (div_nonneg hr (norm_nonneg _)),div_mul_cancel₀ _ hn]
              exact le_add_of_nonneg_right (le_max_left _ _)
          obtain ⟨e⟩ := hA.homeomorph_modelCurve
          obtain ⟨G,hG⟩ := jordan_schoenflies_of_homeomorph hA isJordanCurve_modelCurve e
          have imageG : G '' A = modelCurve := by
            ext z
            constructor
            · rintro ⟨w,hw,rfl⟩
              rw [hG ⟨w,hw⟩]
              exact (e ⟨w,hw⟩).property
            · intro hz
              refine ⟨e.symm ⟨z,hz⟩,(e.symm ⟨z,hz⟩).property,?_⟩
              rw [hG]
              exact congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)
          let P : Plane ≃ₜ (ℝ × ℝ) := {
            toEquiv := {
              toFun := fun z => (z 0,z 1)
              invFun := fun z => Plane.mk z.1 z.2
              left_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk]
              right_inv := by intro z; exact Prod.ext (by simp [Plane.mk]) (by simp [Plane.mk]) }
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop }
          let L := G.trans P
          have imageL : L '' A = {z : ℝ × ℝ | ‖z‖ = 1} := by
            rw [show (L : Plane → ℝ × ℝ) = P ∘ G from rfl,Set.image_comp,imageG]
            ext z
            constructor
            · rintro ⟨w,hw,rfl⟩
              change max |w 0| |w 1| = 1 at hw
              simpa [P,Prod.norm_def,Real.norm_eq_abs] using hw
            · intro hz
              refine ⟨P.symm z,?_,P.apply_symm_apply z⟩
              change max |z.1| |z.2| = 1
              simpa [Prod.norm_def,Real.norm_eq_abs] using hz
          obtain ⟨K,hfix,hsupport,hdisj,hside,hmono⟩ := ribbon (L '' F) (L.isClosedMap F hF) (hne.image L)
          let H : AmbientIsotopy Plane := {
            map := ⟨fun z => L.symm (K.map (z.1,L z.2)), by fun_prop⟩
            homeomorphism_at := by
              intro t; obtain ⟨e,he⟩ := K.homeomorphism_at t
              exact ⟨(L.trans e).trans L.symm,fun z => congrArg L.symm (he (L z))⟩
            at_zero := by intro z; change L.symm (K.map (⟨0,by norm_num⟩,L z)) = z; rw [K.at_zero,L.symm_apply_apply] }
          let C : Set Plane := L.symm '' closedBall (0 : ℝ × ℝ) (3/2)
          have hcompact : IsCompact C := (isCompact_closedBall _ _).image L.symm.continuous
          have coord (t : Interval) (z : Plane) : L (H.map (t,z)) = K.map (t,L z) := L.apply_symm_apply _
          refine ⟨L,H,C,hcompact,?_,?_,?_,imageL,?_,?_⟩
          · intro t z hz
            apply L.injective
            rw [coord,hsupport]
            have hn : 3/2 < ‖L z‖ := by
              by_contra hh
              apply hz
              refine ⟨L z,?_,L.symm_apply_apply z⟩
              simpa [Metric.mem_closedBall,dist_zero_right] using (not_lt.mp hh)
            exact Or.inr hn.le
          · intro t z hz
            apply L.injective
            rw [coord,hfix t (L z) (mem_image_of_mem L hz)]
          · apply Set.disjoint_left.mpr
            rintro z ⟨w,⟨hw,hwF⟩,rfl⟩ hz
            apply Set.disjoint_left.mp hdisj
            · refine ⟨L w,⟨?_,?_⟩,?_⟩
              · rw [←imageL]; exact mem_image_of_mem L hw
              · rintro ⟨u,hu,he⟩; exact hwF (L.injective he ▸ hu)
              · exact (coord 1 w).symm
            · rcases hz with hz | hz
              · left; rw [←imageL]; exact mem_image_of_mem L hz
              · exact Or.inr (mem_image_of_mem L hz)
          · intro t z hz ht
            rw [coord]
            apply hside t (L z)
            · change L z ∈ {z : ℝ × ℝ | ‖z‖ = 1}
              rw [← imageL]
              exact mem_image_of_mem L hz.1
            · rintro ⟨q,hq,he⟩
              exact hz.2 (L.injective he ▸ hq)
            · exact ht
          · intro t z
            rw [coord]
            exact hmono t (L z)
        obtain ⟨L,H,C,hC,houtside,hfix,hdisj,hLA,hside,hmono⟩ := outward A F hA hF hne
        obtain ⟨e,he⟩ := H.homeomorphism_at 1
        let reverse : Interval → Interval := fun t =>
          ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩
        have reverseCont : Continuous reverse := by unfold reverse; fun_prop
        let I : AmbientIsotopy Plane := {
          map := ⟨fun z => H.map (reverse z.1,e.symm z.2),
            H.map.continuous.comp ((reverseCont.comp continuous_fst).prodMk
              (e.symm.continuous.comp continuous_snd))⟩
          homeomorphism_at := by
            intro t
            obtain ⟨et,het⟩ := H.homeomorphism_at (reverse t)
            exact ⟨e.symm.trans et,fun z => het _⟩
          at_zero := by
            intro z
            change H.map (reverse 0,e.symm z) = z
            rw [show reverse 0 = (1:Interval) by apply Subtype.ext; norm_num [reverse],
              ← he,e.apply_symm_apply] }
        have hifinal (z : Plane) : I.finalMap z = e.symm z := by
          change H.map (reverse 1,e.symm z) = e.symm z
          rw [show reverse 1 = (0:Interval) by apply Subtype.ext; norm_num [reverse]]
          exact H.at_zero _
        have inverseFixes (P : Set Plane) (hP : ∀ t z, z ∈ P → H.map (t,z) = z) :
            ∀ t z, z ∈ P → I.map (t,z) = z := by
          intro t z hz
          have hz' : e.symm z = z := by
            apply e.injective
            rw [e.apply_symm_apply,he,hP 1 z hz]
          change H.map (reverse t,e.symm z) = z
          rw [hz']
          exact hP _ z hz
        have hifix : ∀ t z, z ∈ F → I.map (t,z) = z := inverseFixes F hfix
        have hioutside : ∀ t z, z ∉ C → I.map (t,z) = z := inverseFixes Cᶜ houtside
        have radiusA (z : Plane) (hz : z ∈ A) : ‖L z‖ = 1 := by
          have hm : L z ∈ L '' A := mem_image_of_mem L hz
          rw [hLA] at hm
          exact hm
        have radiusConverse (z : Plane) (hz : ‖L z‖ = 1) : z ∈ A := by
          have hm : L z ∈ L '' A := by rw [hLA]; exact hz
          obtain ⟨w,hw,he⟩ := hm
          exact L.injective he ▸ hw
        have inward (z : Plane) (hz : z ∈ A \ F) : ‖L (I.finalMap z)‖ < 1 := by
          let y := e.symm z
          have hy : H.map (1,y) = z := by
            rw [← he]
            exact e.apply_symm_apply z
          have hyF : y ∉ F := by
            intro hm
            have hf := hfix 1 y hm
            rw [hy] at hf
            exact hz.2 (hf.symm ▸ hm)
          have hle : ‖L y‖ ≤ 1 := by
            have hm := hmono 1 y
            rw [hy,radiusA z hz.1] at hm
            exact hm
          have hne : ‖L y‖ ≠ 1 := by
            intro he
            have hs := hside 1 y ⟨radiusConverse y he,hyF⟩ (by norm_num)
            rw [hy,radiusA z hz.1] at hs
            exact lt_irrefl 1 hs
          have hi : I.finalMap z = y := hifinal z
          rw [hi]
          exact lt_of_le_of_ne hle hne
        have hidisj : Disjoint (I.finalMap '' (A \ F)) (A ∪ F) := by
          apply disjoint_left.mpr
          rintro z ⟨w,hw,rfl⟩ (hz | hz)
          · have hin := inward w hw
            rw [radiusA _ hz] at hin
            exact lt_irrefl 1 hin
          · obtain ⟨e,he⟩ := I.homeomorphism_at 1
            have hh : I.finalMap w = w := e.injective (by
              rw [he,he]
              exact hifix 1 (I.finalMap w) hz)
            exact hw.2 (hh ▸ hz)
        refine ⟨L,H,I,C,hC,houtside,hioutside,hfix,hifix,hdisj,hidisj,hLA,?_⟩
        intro z hz
        exact ⟨hside 1 z hz (by norm_num),inward z hz⟩
      have sideTransition {S : Type} [TopologicalSpace S] (G : S ≃ₜ (ℝ × ℝ)) (p : S)
        (hp : max |(G p).1| |(G p).2| = 1)
        (h : OpenPartialHomeomorph S (ℝ × ℝ)) (hpH : p ∈ h.source)
        (hh : ∀ z ∈ h.source, max |(G z).1| |(G z).2| = 1 ↔ (h z).1 = 0) :
        ∃ (ε : ZMod 2) (O : Set S), IsOpen O ∧ p ∈ O ∧ O ⊆ h.source ∧
          ∀ z ∈ O, max |(G z).1| |(G z).2| ≠ 1 →
            (if 0 < (h z).1 then (1 : ZMod 2) else 0) =
              (if 1 < max |(G z).1| |(G z).2| then (1 : ZMod 2) else 0) + ε := by
        have modelChart (q : ℝ × ℝ) (hq : max |q.1| |q.2| = 1) :
            ∃ (χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (U : Set (ℝ × ℝ)),
              IsOpen U ∧ q ∈ U ∧ χ q = (0,0) ∧
              ∀ z ∈ U, (max |z.1| |z.2| = 1 ↔ (χ z).1 = 0) ∧
                (1 < max |z.1| |z.2| ↔ 0 < (χ z).1) := by
          have corner : ∃ χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
              χ (1,1) = (0,0) ∧
              ∀ z, 0 < z.1 → 0 < z.2 →
                (χ z).1 = 2 * (max |z.1| |z.2| - 1) := by
            let χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
              toEquiv := {
                toFun := fun z => (z.1+z.2-2+|z.1-z.2|,z.1-z.2)
                invFun := fun z => (1+(z.1-|z.2|+z.2)/2,1+(z.1-|z.2|-z.2)/2)
                left_inv := by intro z; apply Prod.ext <;> dsimp <;> ring
                right_inv := by
                  intro z
                  have he : (1+(z.1-|z.2|+z.2)/2)-(1+(z.1-|z.2|-z.2)/2) = z.2 := by ring
                  apply Prod.ext
                  · dsimp; rw [he]; ring
                  · exact he }
              continuous_toFun := by fun_prop
              continuous_invFun := by fun_prop }
            refine ⟨χ,by norm_num [χ],?_⟩
            intro z hx hy
            change z.1+z.2-2+|z.1-z.2| = _
            rw [abs_of_pos hx,abs_of_pos hy]
            by_cases he : z.2 ≤ z.1
            · rw [max_eq_left he,abs_of_nonneg (sub_nonneg.mpr he)]; ring
            · rw [max_eq_right (le_of_not_ge he),abs_of_nonpos (by linarith)]; ring
          have facet (a : ℝ) (ha : |a| < 1) :
              ∃ (χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (U : Set (ℝ × ℝ)),
                IsOpen U ∧ (1,a) ∈ U ∧ χ (1,a) = (0,0) ∧
                ∀ z ∈ U, (max |z.1| |z.2| = 1 ↔ (χ z).1 = 0) ∧
                  (1 < max |z.1| |z.2| ↔ 0 < (χ z).1) := by
            let χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
              toEquiv := {
                toFun := fun z => (z.1-1,z.2-a)
                invFun := fun z => (z.1+1,z.2+a)
                left_inv := by intro z; apply Prod.ext <;> dsimp <;> ring
                right_inv := by intro z; apply Prod.ext <;> dsimp <;> ring }
              continuous_toFun := by fun_prop
              continuous_invFun := by fun_prop }
            let U : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ |z.2| < 1}
            have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
              (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
            refine ⟨χ,U,hU,⟨by norm_num,ha⟩,by simp [χ],?_⟩
            intro z hz
            have hx := hz.1
            have hy := hz.2
            constructor
            · change max |z.1| |z.2| = 1 ↔ z.1-1 = 0
              rw [abs_of_pos hx]
              constructor
              · intro hm
                by_cases hle : z.1 ≤ |z.2|
                · rw [max_eq_right hle] at hm
                  linarith
                · rw [max_eq_left (le_of_not_ge hle)] at hm
                  linarith
              · intro he
                have he' : z.1 = 1 := by linarith
                rw [he',max_eq_left hy.le]
            · change 1 < max |z.1| |z.2| ↔ 0 < z.1-1
              rw [abs_of_pos hx,lt_max_iff]
              constructor
              · rintro (h | h) <;> linarith
              · intro h; left; linarith
          have positive (q : ℝ × ℝ) (hx : 0 ≤ q.1) (hy : 0 ≤ q.2) (hq : max q.1 q.2 = 1) :
              ∃ (χ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (U : Set (ℝ × ℝ)),
                IsOpen U ∧ q ∈ U ∧ χ q = (0,0) ∧
                ∀ z ∈ U, (max |z.1| |z.2| = 1 ↔ (χ z).1 = 0) ∧
                  (1 < max |z.1| |z.2| ↔ 0 < (χ z).1) := by
            have hxle : q.1 ≤ 1 := (le_max_left _ _).trans_eq hq
            have hyle : q.2 ≤ 1 := (le_max_right _ _).trans_eq hq
            by_cases hx1 : q.1 = 1
            · by_cases hy1 : q.2 = 1
              · obtain ⟨χ,hzero,hcoord⟩ := corner
                let U : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ 0 < z.2}
                have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)
                refine ⟨χ,U,hU,⟨by simpa [hx1],by simpa [hy1]⟩,?_,?_⟩
                · have he : q = (1,1) := Prod.ext hx1 hy1
                  simpa [he] using hzero
                · intro z hz
                  rw [hcoord z hz.1 hz.2]
                  constructor <;> constructor <;> intro h <;> linarith
              · have hylt : |q.2| < 1 := by rw [abs_of_nonneg hy]; exact lt_of_le_of_ne hyle hy1
                obtain ⟨χ,U,hU,hqu,hzero,hside⟩ := facet q.2 hylt
                have he : q = (1,q.2) := Prod.ext hx1 rfl
                exact ⟨χ,U,hU,he.symm ▸ hqu,he.symm ▸ hzero,hside⟩
            · have hxlt : |q.1| < 1 := by rw [abs_of_nonneg hx]; exact lt_of_le_of_ne hxle hx1
              have hy1 : q.2 = 1 := by
                by_contra hn
                have hylt : q.2 < 1 := lt_of_le_of_ne hyle hn
                have hxlt' : q.1 < 1 := lt_of_le_of_ne hxle hx1
                have hh := (max_lt_iff.mpr ⟨hxlt',hylt⟩)
                rw [hq] at hh
                exact lt_irrefl _ hh
              let R : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
                toEquiv := {
                  toFun := Prod.swap
                  invFun := Prod.swap
                  left_inv := by intro z; rfl
                  right_inv := by intro z; rfl }
                continuous_toFun := continuous_swap
                continuous_invFun := continuous_swap }
              obtain ⟨χ,V,hV,hqV,hzero,hside⟩ := facet q.1 hxlt
              let U : Set (ℝ × ℝ) := R ⁻¹' V
              refine ⟨R.trans χ,U,hV.preimage R.continuous,?_,?_,?_⟩
              · change (q.2,q.1) ∈ V
                simpa [hy1] using hqV
              · change χ (q.2,q.1) = (0,0)
                simpa [hy1] using hzero
              · intro z hz
                have hh := hside (R z) hz
                simpa [R,max_comm] using hh
          let R : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
            toEquiv := {
              toFun := fun z => (if q.1 < 0 then -z.1 else z.1,if q.2 < 0 then -z.2 else z.2)
              invFun := fun z => (if q.1 < 0 then -z.1 else z.1,if q.2 < 0 then -z.2 else z.2)
              left_inv := by intro z; split_ifs <;> simp
              right_inv := by intro z; split_ifs <;> simp }
            continuous_toFun := by split_ifs <;> fun_prop
            continuous_invFun := by split_ifs <;> fun_prop }
          have he : R q = (|q.1|,|q.2|) := by
            apply Prod.ext
            · dsimp [R]; split_ifs with h
              · exact (abs_of_neg h).symm
              · exact (abs_of_nonneg (le_of_not_gt h)).symm
            · dsimp [R]; split_ifs with h
              · exact (abs_of_neg h).symm
              · exact (abs_of_nonneg (le_of_not_gt h)).symm
          have hn (z : ℝ × ℝ) : max |(R z).1| |(R z).2| = max |z.1| |z.2| := by
            dsimp [R]; split_ifs <;> simp
          obtain ⟨χ,V,hV,hqV,hzero,hside⟩ := positive (R q)
            (by rw [he]; exact abs_nonneg _) (by rw [he]; exact abs_nonneg _) (by simpa [he] using hq)
          let U : Set (ℝ × ℝ) := R ⁻¹' V
          refine ⟨R.trans χ,U,hV.preimage R.continuous,hqV,hzero,?_⟩
          intro z hz
          have hh := hside (R z) hz
          rw [hn z] at hh
          exact hh
        obtain ⟨χ,U,hU,hpU,hzero,hside⟩ := modelChart (G p) hp
        let V : Set S := G ⁻¹' U
        have hV : IsOpen V := hU.preimage G.continuous
        let k : OpenPartialHomeomorph S (ℝ × ℝ) := (G.trans χ).toOpenPartialHomeomorph.restrOpen V hV
        have ks : k.source = V := by simp [k]
        have kp : p ∈ k.source := by rw [ks]; exact hpU
        have hk (z : S) (hz : z ∈ k.source) :
            max |(G z).1| |(G z).2| = 1 ↔ (k z).1 = 0 := by
          exact (hside (G z) (by change z ∈ V; exact ks ▸ hz)).1
        let A : Set S := {z | max |(G z).1| |(G z).2| = 1}
        obtain ⟨τ,hτ,hformula⟩ := CurveComplex.LocalSurgery.axis_chart_relative_side_extension A h k hh hk
        have hOpen : IsOpen (h.source ∩ k.source) := h.open_source.inter k.open_source
        have hpW : p ∈ h.source ∩ k.source := ⟨hpH,kp⟩
        have hc : ContinuousAt τ p := (hτ p hpW).continuousAt (hOpen.mem_nhds hpW)
        have hconstant : {z | τ z = τ p} ∈ 𝓝 p :=
          hc.preimage_mem_nhds ((isOpen_discrete {τ p}).mem_nhds (by simp))
        obtain ⟨O,hOW,hO,hpO⟩ := mem_nhds_iff.mp (inter_mem (hOpen.mem_nhds hpW) hconstant)
        refine ⟨τ p,O,hO,hpO,fun z hz => (hOW hz).1.1,?_⟩
        intro z hz hne
        have he := hformula z (hOW hz).1 hne
        have hs := (hside (G z) (by change z ∈ V; exact ks ▸ (hOW hz).1.2)).2
        have hlabel : (if 0 < (k z).1 then (1 : ZMod 2) else 0) =
            (if 1 < max |(G z).1| |(G z).2| then (1 : ZMod 2) else 0) := by
          simp only [show (k z).1 = (χ (G z)).1 from rfl,← hs]
        rw [hlabel,(hOW hz).2] at he
        rw [he,add_left_comm,CharTwo.add_self_eq_zero,add_zero]
      obtain ⟨L,H,I,C,hC,hout,hiout,hfix,hifix,hdisj,hidisj,hLA,hside⟩ :=
        bidirectional A F hA hF hne
      have normA (z : Plane) : ‖L z‖ = 1 ↔ z ∈ A := by
        constructor
        · intro hz
          have hm : L z ∈ L '' A := by rw [hLA]; exact hz
          obtain ⟨w,hw,he⟩ := hm
          exact L.injective he ▸ hw
        · intro hz
          have hm : L z ∈ L '' A := mem_image_of_mem L hz
          rw [hLA] at hm
          exact hm
      have normMax (z : Plane) : max |(L z).1| |(L z).2| = ‖L z‖ := by
        simp [Prod.norm_def,Real.norm_eq_abs]
      obtain ⟨ε,O,hO,hpO,hOH,hlabel⟩ := sideTransition L p
        (by rw [normMax]; exact (normA p).mpr hpA) h hpH
        (fun z hz => by rw [normMax,normA]; exact hh z hz)
      let U := O ∩ (H.finalMap ⁻¹' O) ∩ (I.finalMap ⁻¹' O)
      have hHcont : Continuous H.finalMap := H.map.continuous.comp
        (continuous_const.prodMk continuous_id)
      have hIcont : Continuous I.finalMap := I.map.continuous.comp
        (continuous_const.prodMk continuous_id)
      have hU : IsOpen U := (hO.inter (hO.preimage hHcont)).inter (hO.preimage hIcont)
      have hpU : p ∈ U := ⟨⟨hpO,by change H.finalMap p ∈ O; rw [show H.finalMap p = p from hfix 1 p hpF]; exact hpO⟩,
        by change I.finalMap p ∈ O; rw [show I.finalMap p = p from hifix 1 p hpF]; exact hpO⟩
      have hUH : U ⊆ h.source := fun z hz => hOH hz.1.1
      have allNode (T : AmbientIsotopy Plane)
          (hfixT : ∀ z ∈ F, T.finalMap z=z)
          (huniform : (∀ z, z ∈ A \ F → 1 < ‖L (T.finalMap z)‖) ∨
            (∀ z, z ∈ A \ F → ‖L (T.finalMap z)‖ < 1)) :
          ∀ q ∈ A ∩ F, ∀ a : OpenPartialHomeomorph Plane (ℝ × ℝ), q ∈ a.source →
            (∀ z ∈ a.source, z ∈ A ↔ (a z).1=0) →
            ∃ (σ : Bool) (V : Set Plane), IsOpen V ∧ q ∈ V ∧ V ⊆ a.source ∧
              ∀ z, z ∈ A \ F → z ∈ V → T.finalMap z ∈ a.source ∧
                (if σ then 0 < (a (T.finalMap z)).1 else (a (T.finalMap z)).1 < 0) := by
        intro q hq a hqa haa
        obtain ⟨ε',O',hO',hqO',hOa',hlabel'⟩ := sideTransition L q
          (by rw [normMax]; exact (normA q).mpr hq.1) a hqa
          (fun z hz => by rw [normMax,normA]; exact haa z hz)
        let V := O' ∩ (T.finalMap ⁻¹' O')
        have hTc : Continuous T.finalMap := T.map.continuous.comp
          (continuous_const.prodMk continuous_id)
        have hV : IsOpen V := hO'.inter (hO'.preimage hTc)
        have hqV : q ∈ V := ⟨hqO',by change T.finalMap q ∈ O'; rw [hfixT q hq.2]; exact hqO'⟩
        have hVa : V ⊆ a.source := fun z hz => hOa' hz.1
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        rcases huniform with hout | hin
        · fin_cases ε'
          · refine ⟨true,V,hV,hqV,hVa,?_⟩
            intro z hz hzV
            have hzO : T.finalMap z ∈ O' := hzV.2
            have hs := hout z hz
            have he := hlabel' (T.finalMap z) hzO (by rw [normMax]; exact ne_of_gt hs)
            rw [normMax] at he
            refine ⟨hOa' hzO,?_⟩
            simp only [Bool.false_eq_true,↓reduceIte]
            by_contra hn
            simp [hn,hs] at he
            exact h01 (by convert he using 1 <;> decide)
          · refine ⟨false,V,hV,hqV,hVa,?_⟩
            intro z hz hzV
            have hzO : T.finalMap z ∈ O' := hzV.2
            have hs := hout z hz
            have he := hlabel' (T.finalMap z) hzO (by rw [normMax]; exact ne_of_gt hs)
            rw [normMax] at he
            refine ⟨hOa' hzO,?_⟩
            simp only [Bool.false_eq_true,↓reduceIte]
            have hn : ¬ 0 < (a (T.finalMap z)).1 := by
              intro hp
              simp [hp,hs] at he
              exact h01 (by convert he.symm using 1 <;> decide)
            have hzero : (a (T.finalMap z)).1 ≠ 0 := by
              intro hh
              have hm := (normA (T.finalMap z)).mpr ((haa _ (hOa' hzO)).mpr hh)
              exact (ne_of_gt hs) hm
            exact lt_of_le_of_ne (le_of_not_gt hn) hzero
        · fin_cases ε'
          · refine ⟨false,V,hV,hqV,hVa,?_⟩
            intro z hz hzV
            have hzO : T.finalMap z ∈ O' := hzV.2
            have hs := hin z hz
            have he := hlabel' (T.finalMap z) hzO (by rw [normMax]; exact ne_of_lt hs)
            rw [normMax] at he
            refine ⟨hOa' hzO,?_⟩
            simp only [Bool.false_eq_true,↓reduceIte]
            have hn : ¬ 0 < (a (T.finalMap z)).1 := by
              intro hp
              simp [hp,not_lt_of_ge hs.le] at he
              exact h01 (by convert he.symm using 1 <;> decide)
            have hzero : (a (T.finalMap z)).1 ≠ 0 := by
              intro hh
              have hm := (normA (T.finalMap z)).mpr ((haa _ (hOa' hzO)).mpr hh)
              exact (ne_of_lt hs) hm
            exact lt_of_le_of_ne (le_of_not_gt hn) hzero
          · refine ⟨true,V,hV,hqV,hVa,?_⟩
            intro z hz hzV
            have hzO : T.finalMap z ∈ O' := hzV.2
            have hs := hin z hz
            have he := hlabel' (T.finalMap z) hzO (by rw [normMax]; exact ne_of_lt hs)
            rw [normMax] at he
            refine ⟨hOa' hzO,?_⟩
            simp only [Bool.false_eq_true,↓reduceIte]
            by_contra hn
            simp [hn,not_lt_of_ge hs.le] at he
            exact h01 (by convert he using 1 <;> decide)
      fin_cases ε
      · refine ⟨H,C,U,hC,hout,hfix,hdisj,hU,hpU,hUH,?_,?_⟩
        · intro z hz hzU
          have hzO : H.finalMap z ∈ O := hzU.1.2
          have houtside := (hside z hz).1
          have he := hlabel (H.finalMap z) hzO (by rw [normMax]; exact ne_of_gt houtside)
          rw [normMax] at he
          refine ⟨hOH hzO,?_⟩
          by_contra hn
          simp [hn,houtside] at he
          have h01 : (0 : ZMod 2) ≠ 1 := by decide
          exact h01 (by convert he using 1 <;> decide)
        · exact allNode H (fun z hz => hfix 1 z hz) (Or.inl (fun z hz => (hside z hz).1))
      · refine ⟨I,C,U,hC,hiout,hifix,hidisj,hU,hpU,hUH,?_,?_⟩
        · intro z hz hzU
          have hzO : I.finalMap z ∈ O := hzU.2
          have hinside := (hside z hz).2
          have he := hlabel (I.finalMap z) hzO (by rw [normMax]; exact ne_of_lt hinside)
          rw [normMax] at he
          refine ⟨hOH hzO,?_⟩
          by_contra hn
          simp [hn,not_lt_of_ge hinside.le] at he
          have h01 : (0 : ZMod 2) ≠ 1 := by decide
          exact h01 (by convert he using 1 <;> decide)
        · exact allNode I (fun z hz => hifix 1 z hz) (Or.inr (fun z hz => (hside z hz).2))
    obtain ⟨D,hD,hmeet,hJ⟩ := exists_jordan_completion_of_isArcBetween hA
    let J := D ∪ A
    let G := F ∪ D ∪ Wᶜ
    have hG : IsClosed G := (hF.union hD.isArc.isClosed).union hW.isClosed_compl
    have hrD : r ∉ D := by
      intro hr
      have he : r ∈ ({p,q} : Set Plane) := hmeet ▸ ⟨hr,hrA⟩
      rcases mem_insert_iff.mp he with he | he
      · exact hrp he
      · exact hrq (mem_singleton_iff.mp he)
    let h' := h.restrOpen Dᶜ hD.isArc.isClosed.isOpen_compl
    have hrH' : r ∈ h'.source := by
      change r ∈ h.source ∩ Dᶜ
      exact ⟨hrH,hrD⟩
    have hchart : ∀ z ∈ h'.source, z ∈ J ↔ (h' z).1 = 0 := by
      intro z hz
      change z ∈ h.source ∩ Dᶜ at hz
      change z ∈ D ∪ A ↔ (h z).1 = 0
      have hzD : z ∉ D := hz.2
      simpa only [mem_union,hzD,false_or] using hh z hz.1
    have heq : J \ G = A \ F := by
      ext z
      constructor
      · rintro ⟨hz,hn⟩
        have hnD : z ∉ D := fun hd => hn (Or.inl (Or.inr hd))
        exact ⟨hz.resolve_left hnD,fun hf => hn (Or.inl (Or.inl hf))⟩
      · rintro ⟨hz,hf⟩
        refine ⟨Or.inr hz,?_⟩
        rintro ((h | h) | h)
        · exact hf h
        · have he : z ∈ ({p,q} : Set Plane) := hmeet ▸ ⟨h,hz⟩
          rcases mem_insert_iff.mp he with he | he
          · exact hf (he ▸ hpF)
          · exact hf ((mem_singleton_iff.mp he) ▸ hqF)
        · exact h (hAW ⟨hz,hf⟩)
    obtain ⟨H,C,U,hC,hout,hfix,hdisj,hU,hrU,hUH,hside,hAll⟩ := sideJordan J G hJ hG
      ⟨r,Or.inl (Or.inl hrF)⟩ r (Or.inr hrA) (Or.inl (Or.inl hrF)) h' hrH' hchart
    have hfixF : ∀ t z, z ∈ F → H.map (t,z) = z :=
      fun t z hz => hfix t z (Or.inl (Or.inl hz))
    have hfixW : ∀ t z, z ∉ W → H.map (t,z) = z :=
      fun t z hz => hfix t z (Or.inr hz)
    have hdisjA : Disjoint (H.finalMap '' (A \ F)) (A ∪ F) := by
      rw [heq] at hdisj
      apply hdisj.mono_right
      intro z hz
      rcases hz with hz | hz
      · exact Or.inl (Or.inr hz)
      · exact Or.inr (Or.inl (Or.inl hz))
    refine ⟨H,C,U,hC,hout,hfixF,hfixW,hdisjA,hU,hrU,?_,?_,?_⟩
    · intro z hz
      have hh := hUH hz
      exact hh.1
    · intro z hz hzU
      have hs := hside z (heq.symm ▸ hz) hzU
      exact ⟨hs.1.1,hs.2⟩
    · intro v hv hvp hvq a hva haa
      have hvD : v ∉ D := by
        intro hdv
        have he : v ∈ ({p,q} : Set Plane) := hmeet ▸ ⟨hdv,hv.1⟩
        rcases mem_insert_iff.mp he with h | h
        · exact hvp h
        · exact hvq (mem_singleton_iff.mp h)
      let a' := a.restrOpen Dᶜ hD.isArc.isClosed.isOpen_compl
      have hva' : v ∈ a'.source := ⟨hva,hvD⟩
      have hchart' : ∀ z ∈ a'.source, z ∈ J ↔ (a' z).1=0 := by
        intro z hz
        change z ∈ a.source ∩ Dᶜ at hz
        change z ∈ D ∪ A ↔ (a z).1=0
        have hzD : z ∉ D := hz.2
        simpa only [mem_union,hzD,false_or] using haa z hz.1
      obtain ⟨σ,V,hV,hvV,hVa,hdir⟩ := hAll v ⟨Or.inr hv.1,Or.inl (Or.inl hv.2)⟩ a' hva' hchart'
      refine ⟨σ,V,hV,hvV,(fun z hz => (hVa hz).1),?_⟩
      intro z hz hzV
      have hs := hdir z (heq.symm ▸ hz) hzV
      exact ⟨hs.1.1,hs.2⟩
  have off : ∃ p : S, p ∉ a.image := by
    have hn : ¬ (M.cover.branch : Set S) ⊆ {a.map (0 : Interval),a.map 1} := by
      intro hh
      have hc := Finset.card_le_card (show M.cover.branch ⊆ {a.map (0 : Interval),a.map 1} from by
        intro z hz
        simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] using hh hz)
      have hb : ({a.map (0 : Interval),a.map 1} : Finset S).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
      rw [M.cover.branch_card] at hc
      omega
    obtain ⟨p,hp,he⟩ := Set.not_subset.mp hn
    refine ⟨p,?_⟩
    rintro ⟨t,rfl⟩
    rcases a.marked_only_at_ends t hp with rfl | rfl
    · exact he (Set.mem_insert _ _)
    · exact he (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨p,hp⟩ := off
  let U : Set S := {z | z ≠ p}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  let e : U ≃ₜ Plane := puncturedPlane M p
  let γ : C(Interval,Plane) := ⟨fun t => e ⟨a.map t,fun he => hp (he ▸ Set.mem_range_self t)⟩,
    e.continuous.comp (a.continuous.subtype_mk _)⟩
  let A : Set Plane := Set.range γ
  have hA : IsArcBetween A (γ 0) (γ 1) := by
    let f : ℝ → Plane := γ ∘ Set.projIcc 0 1 zero_le_one
    refine ⟨f,(γ.continuous.comp continuous_projIcc).continuousOn,?_,?_,?_,?_⟩
    · intro t ht u hu he
      have hg : γ ⟨t,ht⟩ = γ ⟨u,hu⟩ := by simpa only [f,Function.comp_apply,Set.projIcc_of_mem zero_le_one ht,Set.projIcc_of_mem zero_le_one hu] using he
      have ha : a.map ⟨t,ht⟩ = a.map ⟨u,hu⟩ := congrArg Subtype.val (e.injective hg)
      rcases a.injective_except_loop_closure _ _ ha with he | he | he
      · exact congrArg Subtype.val he
      · have hc : a.map (0 : Interval) = a.map 1 := by
          have ht0 : (⟨t,ht⟩ : Interval) = 0 := by apply Subtype.ext; exact congrArg Subtype.val he.1
          have hu1 : (⟨u,hu⟩ : Interval) = 1 := by apply Subtype.ext; exact congrArg Subtype.val he.2
          simpa only [ht0,hu1] using ha
        exact (hnonloop hc).elim
      · have hc : a.map (0 : Interval) = a.map 1 := by
          have ht1 : (⟨t,ht⟩ : Interval) = 1 := by apply Subtype.ext; exact congrArg Subtype.val he.1
          have hu0 : (⟨u,hu⟩ : Interval) = 0 := by apply Subtype.ext; exact congrArg Subtype.val he.2
          simpa only [ht1,hu0] using ha.symm
        exact (hnonloop hc).elim
    · ext z
      constructor
      · rintro ⟨t,ht,rfl⟩; exact ⟨Set.projIcc 0 1 zero_le_one t,rfl⟩
      · rintro ⟨t,rfl⟩
        refine ⟨t.val,t.property,?_⟩
        simp [f,Set.projIcc_of_mem]
    · simp [f,Set.projIcc_of_mem]
    · simp [f,Set.projIcc_of_mem]
  let B : Set Plane := e '' {z : U | z.val ∈ F}
  let V : Set Plane := e '' {z : U | z.val ∈ W}
  have hB : IsClosed B := e.isClosedMap _ (hF.preimage continuous_subtype_val)
  have hV : IsOpen V := e.isOpenMap _ (hW.preimage continuous_subtype_val)
  have hstart : γ 0 ∈ B := mem_image_of_mem e (hmarks a.start_marked)
  have hend : γ 1 ∈ B := mem_image_of_mem e (hmarks a.end_marked)
  have hAV : A \ B ⊆ V := by
    rintro z ⟨⟨t,rfl⟩,hz⟩
    apply mem_image_of_mem
    apply hAW
    refine ⟨Set.mem_range_self t,?_⟩
    intro hf
    exact hz (mem_image_of_mem e hf)
  have hrU : r ∈ U := fun he => hp (he ▸ hrA)
  let coeChart : OpenPartialHomeomorph U S :=
    (⟨U,hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe ⟨⟨r,hrU⟩⟩
  let h : OpenPartialHomeomorph Plane (ℝ × ℝ) :=
    e.symm.toOpenPartialHomeomorph.trans (coeChart.trans k)
  have hsource (z : Plane) : z ∈ h.source ↔ (e.symm z).val ∈ k.source := by
    simp [h,OpenPartialHomeomorph.trans_source,coeChart]
    rfl
  have happly (z : Plane) : h z = k (e.symm z).val := rfl
  have hAeq (z : Plane) : z ∈ A ↔ (e.symm z).val ∈ a.image := by
    constructor
    · rintro ⟨t,rfl⟩
      change (e.symm (e _)).val ∈ a.image
      rw [e.symm_apply_apply]
      exact mem_range_self _
    · rintro ⟨t,ht⟩
      refine ⟨t,?_⟩
      apply e.symm.injective
      change e.symm (e _) = e.symm z
      rw [e.symm_apply_apply]
      exact Subtype.ext ht
  have hrPlanar : e ⟨r,hrU⟩ ∈ A := by rw [hAeq,e.symm_apply_apply]; exact hrA
  have hrB : e ⟨r,hrU⟩ ∈ B := mem_image_of_mem e hrF
  have hrh : e ⟨r,hrU⟩ ∈ h.source := by rw [hsource,e.symm_apply_apply]; exact hrK
  have hchart : ∀ z ∈ h.source, z ∈ A ↔ (h z).1=0 := by
    intro z hz
    rw [hAeq,happly]
    exact hk _ ((hsource z).mp hz)
  have hrp : e ⟨r,hrU⟩ ≠ γ 0 := by
    intro he
    exact hr0 (congrArg Subtype.val (e.injective he))
  have hrq : e ⟨r,hrU⟩ ≠ γ 1 := by
    intro he
    exact hr1 (congrArg Subtype.val (e.injective he))
  obtain ⟨K,C,N,hC,hout,hfix,houtside,hdisj,hN,hrN,hNh,hside,hAll⟩ :=
    planar A B V (γ 0) (γ 1) hA hB hV hstart hend hAV
      (e ⟨r,hrU⟩) hrPlanar hrB hrp hrq h hrh hchart
  let ee : U ≃ₜ (Set.univ : Set Plane) := e.trans (Homeomorph.Set.univ Plane).symm
  obtain ⟨KU,H,hcoords,hlift,hexterior⟩ := position_surface_chart_lift S U univ hU ee C hC (Set.subset_univ C) K hout
  have coord (t : Interval) (z : U) : e ⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩ = K.map (t,e z) := by
    have hs : (⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩ : U) = KU.map (t,z) := Subtype.ext (hlift t z)
    rw [hs]
    exact hcoords t z
  have fix : ∀ t z, z ∈ F → H.map (t,z) = z := by
    intro t z hz
    by_cases hu : z ∈ U
    · have hh := coord t ⟨z,hu⟩
      rw [hfix t (e ⟨z,hu⟩) (mem_image_of_mem e hz)] at hh
      exact congrArg Subtype.val (e.injective hh)
    · exact hexterior t z hu
  have outside : ∀ t z, z ∉ W → H.map (t,z) = z := by
    intro t z hz
    by_cases hu : z ∈ U
    · have hn : e ⟨z,hu⟩ ∉ V := by
        rintro ⟨v,hv,he⟩
        have hev : v.val = z := congrArg Subtype.val (e.injective he)
        exact hz (hev ▸ hv)
      have hh := coord t ⟨z,hu⟩
      rw [houtside t _ hn] at hh
      exact congrArg Subtype.val (e.injective hh)
    · exact hexterior t z hu
  have disj : Disjoint (H.finalMap '' (a.image \ F)) (a.image ∪ F) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨w,⟨hw,hwF⟩,rfl⟩ hz
    have hwU : w ∈ U := fun he => hp (he ▸ hw)
    let wu : U := ⟨w,hwU⟩
    have hwB : e wu ∉ B := by
      rintro ⟨u,hu,he⟩
      have huval := congrArg Subtype.val (e.injective he)
      change u.val = w at huval
      exact hwF (huval ▸ hu)
    have hwA : e wu ∈ A := by
      obtain ⟨t,ht⟩ := hw
      exact ⟨t,congrArg e (Subtype.ext ht)⟩
    have htarget : H.finalMap w ∈ U := by
      change H.map (1,w) ∈ U
      rw [hlift 1 wu]
      exact (KU.map (1,wu)).property
    apply Set.disjoint_left.mp hdisj
    · refine ⟨e wu,⟨hwA,hwB⟩,(coord 1 wu).symm⟩
    · rcases hz with hz | hz
      · left
        obtain ⟨t,ht⟩ := hz
        exact ⟨t,congrArg e (Subtype.ext ht)⟩
      · exact Or.inr (mem_image_of_mem e hz)
  let Nsurf : Set S := Subtype.val '' (e ⁻¹' N)
  have hNs : IsOpen Nsurf := hU.isOpenMap_subtype_val _ (hN.preimage e.continuous)
  have hrNs : r ∈ Nsurf := ⟨⟨r,hrU⟩,hrN,rfl⟩
  have hNsK : Nsurf ⊆ k.source := by
    rintro z ⟨u,hu,rfl⟩
    have hh := (hsource (e u)).mp (hNh hu)
    simpa only [e.symm_apply_apply] using hh
  refine ⟨H,Nsurf,fix,outside,disj,hNs,hrNs,hNsK,?_,?_⟩
  · intro z hz hzN
    obtain ⟨u,hu,rfl⟩ := hzN
    have huA : e u ∈ A := (hAeq _).mpr (by simpa only [e.symm_apply_apply] using hz.1)
    have huB : e u ∉ B := by
      rintro ⟨v,hv,he⟩
      exact hz.2 (congrArg Subtype.val (e.injective he) ▸ hv)
    have hs := hside (e u) ⟨huA,huB⟩ hu
    have hstay : H.finalMap u.val ∈ U := by
      change H.map (1,u.val) ∈ U
      rw [hlift 1 u]
      exact (KU.map (1,u)).property
    have he := coord 1 u
    have hinv : (e.symm (K.finalMap (e u))).val=H.finalMap u.val := by
      change (e.symm (K.map (1,e u))).val=H.map (1,u.val)
      rw [←he,e.symm_apply_apply]
    refine ⟨?_,?_⟩
    · rw [←hinv]
      exact (hsource _).mp hs.1
    · rw [←hinv]
      exact (happly _).symm ▸ hs.2
  · intro v hv hv0 hv1 a hva haa
    have hvU : v ∈ U := fun he => hp (he ▸ hv.1)
    let c := e.symm.toOpenPartialHomeomorph.trans (coeChart.trans a)
    have csource (z : Plane) : z ∈ c.source ↔ (e.symm z).val ∈ a.source := by
      simp [c,OpenPartialHomeomorph.trans_source,coeChart]
      rfl
    have capply (z : Plane) : c z=a (e.symm z).val := rfl
    have hvA : e ⟨v,hvU⟩ ∈ A := by
      rw [hAeq,e.symm_apply_apply]
      exact hv.1
    have hvB : e ⟨v,hvU⟩ ∈ B := mem_image_of_mem e hv.2
    have hvp : e ⟨v,hvU⟩ ≠ γ 0 := by
      intro hh
      exact hv0 (congrArg Subtype.val (e.injective hh))
    have hvq : e ⟨v,hvU⟩ ≠ γ 1 := by
      intro hh
      exact hv1 (congrArg Subtype.val (e.injective hh))
    have hvc : e ⟨v,hvU⟩ ∈ c.source := by
      rw [csource,e.symm_apply_apply]
      exact hva
    have hcc : ∀ z ∈ c.source, z ∈ A ↔ (c z).1=0 := by
      intro z hz
      rw [hAeq,capply]
      exact haa _ ((csource _).mp hz)
    obtain ⟨σ,V0,hV0,hvV0,hV0c,hdir⟩ := hAll (e ⟨v,hvU⟩) ⟨hvA,hvB⟩ hvp hvq c hvc hcc
    let Vs : Set S := Subtype.val '' (e ⁻¹' V0)
    have hVs : IsOpen Vs := hU.isOpenMap_subtype_val _ (hV0.preimage e.continuous)
    have hvVs : v ∈ Vs := ⟨⟨v,hvU⟩,hvV0,rfl⟩
    have hVsa : Vs ⊆ a.source := by
      rintro z ⟨u,hu,rfl⟩
      have hm := (csource (e u)).mp (hV0c hu)
      simpa only [e.symm_apply_apply] using hm
    refine ⟨σ,Vs,hVs,hvVs,hVsa,?_⟩
    intro z hz hzV
    obtain ⟨u,hu,rfl⟩ := hzV
    have huA : e u ∈ A := (hAeq _).mpr (by simpa only [e.symm_apply_apply] using hz.1)
    have huB : e u ∉ B := by
      rintro ⟨v,hv,he⟩
      exact hz.2 (congrArg Subtype.val (e.injective he) ▸ hv)
    have hs := hdir (e u) ⟨huA,huB⟩ hu
    have hh := coord 1 u
    have hinv : (e.symm (K.finalMap (e u))).val=H.finalMap u.val := by
      change (e.symm (K.map (1,e u))).val=H.map (1,u.val)
      rw [←hh,e.symm_apply_apply]
    refine ⟨?_,?_⟩
    · rw [←hinv]
      exact (csource _).mp hs.1
    · rw [←hinv]
      exact (capply _).symm ▸ hs.2

private theorem actualSourceSurgery_branch_9 (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
(F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
(x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
(hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
(side : Bool) :
∃ (H : AmbientIsotopy S) (U : Set S) (hU : IsOpen U) (hp : anchor.val.map x.t ∈ U),
  ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
  ∃ N : Set S,
    (∀ t z, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
      H.map (t,z)=z) ∧
    (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
      ∀ t z, z ∈ (P.rep v).val.image → H.map (t,z)=z) ∧
    H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) =
      (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ∩
        (anchor.val.image ∪ (P.rep x.selected).val.image) ∧
    (e ⟨anchor.val.map x.t,hp⟩).val=(0,0) ∧
    (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
    (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
    IsOpen N ∧ anchor.val.map x.t ∈ N ∧ N ⊆ U ∧
    (∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
      z=anchor.val.map x.t) ∧
    (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
      Disjoint N (P.rep v).val.image) ∧
    (∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
      z.val=anchor.val.map x.t ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) ∧
  ∀ v ∈ (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)),
    v ≠ (raw side).map 0 → v ≠ (raw side).map 1 →
    ∀ c : OpenPartialHomeomorph S (ℝ × ℝ), v ∈ c.source →
      (∀ z ∈ c.source, z ∈ (raw side).image ↔ (c z).1=0) →
      ∃ (σ : Bool) (V : Set S), IsOpen V ∧ v ∈ V ∧ V ⊆ c.source ∧
        ∀ z, z ∈ (raw side).image \ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) →
          z ∈ V → H.finalMap z ∈ c.source ∧
            (if σ then 0 < (c (H.finalMap z)).1 else (c (H.finalMap z)).1 < 0) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have loopRibbon := actualSourceSurgery_loopRibbon_5 (E := E) (S := S)
  have nonloopRibbon := actualSourceSurgery_nonloopRibbon_7 (E := E) (S := S)
  have chart := actualSourceSurgery_chart_3 (E := E) (S := S)
  have isolate (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
    (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
    (side : Bool) :
    ∃ W : Set S, IsOpen W ∧
      (raw side).image \ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ⊆ W ∧
      (anchor.val.image ∪ (P.rep x.selected).val.image) ∩ W ⊆ (raw side).image := by
  
    classical
    letI : T2Space S := M.sphere.isEmbedding.t2Space
    letI : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc
    let B := anchor.val.map '' {r : Interval | x.t.val ≤ r.val} ∪
      (P.rep x.selected).val.map '' {r : Interval |
        if side then r.val ≤ x.s.val else x.s.val ≤ r.val}
    have hB : IsClosed B := by
      apply IsClosed.union
      · exact ((isClosed_le continuous_const continuous_subtype_val).isCompact.image anchor.val.continuous).isClosed
      · have hc : IsClosed {r : Interval | if side then r.val ≤ x.s.val else x.s.val ≤ r.val} := by
          cases side
          · exact isClosed_le continuous_const continuous_subtype_val
          · exact isClosed_le continuous_subtype_val continuous_const
        exact (hc.isCompact.image (P.rep x.selected).val.continuous).isClosed
    refine ⟨Bᶜ,hB.isOpen_compl,?_,?_⟩
    · rintro z ⟨hz,hn⟩ hzB
      have hm : z ∉ (M.cover.branch : Set S) := fun h => hn (Or.inl h)
      have hcross : ¬ (z ∈ anchor.val.image ∧ z ∈ (P.rep x.selected).val.image) := by
        rintro ⟨ha,ho⟩
        exact hn (Or.inr ⟨⟨ha,hm⟩,⟨ho,hm⟩⟩)
      rw [hraw] at hz
      rcases hz with ⟨r,hr,he⟩ | ⟨r,hr,he⟩
      · rcases hzB with ⟨u,hu,huE⟩ | ⟨u,hu,huE⟩
        · have heq : anchor.val.map r = anchor.val.map u := he.trans huE.symm
          rcases anchor.val.injective_except_loop_closure r u heq with h | h | h
          · have hv := congrArg Subtype.val h
            have hrt : r = x.t := Subtype.ext (by dsimp at hr hu; linarith)
            apply hcross
            refine ⟨⟨r,he⟩,⟨x.s,?_⟩⟩
            rw [← x.same_point,← hrt]
            exact he
          · apply hm
            rw [← he,h.1]
            exact anchor.val.start_marked
          · apply hm
            rw [← he,h.1]
            exact anchor.val.end_marked
        · exact hcross ⟨⟨r,he⟩,⟨u,huE⟩⟩
      · rcases hzB with ⟨u,hu,huE⟩ | ⟨u,hu,huE⟩
        · exact hcross ⟨⟨u,huE⟩,⟨r,he⟩⟩
        · have heq : (P.rep x.selected).val.map r = (P.rep x.selected).val.map u := he.trans huE.symm
          rcases (P.rep x.selected).val.injective_except_loop_closure r u heq with h | h | h
          · have hv := congrArg Subtype.val h
            have hrs : r = x.s := by
              apply Subtype.ext
              change (if side then x.s.val ≤ r.val else r.val ≤ x.s.val) at hr
              change (if side then u.val ≤ x.s.val else x.s.val ≤ u.val) at hu
              cases side <;> simp only [Bool.false_eq_true,↓reduceIte] at hr hu <;> linarith
            apply hcross
            refine ⟨⟨x.t,?_⟩,⟨r,he⟩⟩
            rw [x.same_point,← hrs]
            exact he
          · apply hm
            rw [← he,h.1]
            exact (P.rep x.selected).val.start_marked
          · apply hm
            rw [← he,h.1]
            exact (P.rep x.selected).val.end_marked
    · rintro z ⟨hz,hzW⟩
      rw [hraw]
      rcases hz with ⟨r,hr⟩ | ⟨r,hr⟩
      · left
        refine ⟨r,?_,hr⟩
        have hn : ¬ x.t.val ≤ r.val := fun h => hzW (Or.inl ⟨r,h,hr⟩)
        exact (not_le.mp hn).le
      · right
        refine ⟨r,?_,hr⟩
        have hn : ¬ (if side then r.val ≤ x.s.val else x.s.val ≤ r.val) :=
          fun h => hzW (Or.inr ⟨r,h,hr⟩)
        cases side <;> simp only [Bool.false_eq_true,↓reduceIte] at hn ⊢ <;> exact (not_le.mp hn).le
  have incident : ∀ (side : Bool) (v : {v // v ∈ F}) (hne : v ≠ x.selected)
    (hsimplex : IsArcSimplex M {v.val, x.selected.val}),
    Disjoint ((raw side).image \ (M.cover.branch : Set S)) (arcInterior M (P.rep v)) := by
    intro side v hne hsimplex
    apply Set.disjoint_left.mpr
    rintro p ⟨hp, hpm⟩ hpv
    rw [hraw] at hp
    rcases hp with ⟨r, hr, he⟩ | ⟨r, hr, he⟩
    · by_cases hzero : r.val = 0
      · apply hpm
        rw [← he]
        have hz : r = (0 : Interval) := Subtype.ext hzero
        exact hz ▸ anchor.val.start_marked
      have hrpos : 0 < r.val := lt_of_le_of_ne r.property.1 (Ne.symm hzero)
      by_cases ht : r.val = x.t.val
      · have heq : r = x.t := Subtype.ext ht
        have hanchor : p ∈ arcInterior M anchor := ⟨⟨r, he⟩, hpm⟩
        have hold : p ∈ arcInterior M (P.rep x.selected) := by
          refine ⟨⟨x.s, ?_⟩, hpm⟩
          exact x.same_point.symm.trans (congrArg anchor.val.map heq.symm |>.trans he)
        exact Set.disjoint_left.mp (P.distinct_crossings x.selected v hne.symm)
          ⟨hanchor, hold⟩ ⟨hanchor, hpv⟩
      · have hrlt : r.val < x.t.val := lt_of_le_of_ne hr ht
        exact x.first v r hrpos hrlt (he.symm ▸ hpv)
    · have hold : p ∈ arcInterior M (P.rep x.selected) := ⟨⟨r, he⟩, hpm⟩
      exact Set.disjoint_left.mp (P.simplex_disjoint v x.selected hne hsimplex) hpv hold
  let K0 : Set S := (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)
  let J := {v : {v // v ∈ F} // v ≠ x.selected ∧ IsArcSimplex M {v.val,x.selected.val}}
  let D : Set S := ⋃ v : J, (P.rep v.val).val.image
  letI : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc
  have hD : IsClosed D := isClosed_iUnion_of_finite (fun v =>
    (isCompact_range (P.rep v.val).val.continuous).isClosed)
  have rawD : (raw side).image ∩ D ⊆ (M.cover.branch : Set S) := by
    rintro z ⟨hz,hd⟩
    by_contra hm
    obtain ⟨v,hv⟩ := mem_iUnion.mp hd
    exact disjoint_left.mp (incident side v.val v.property.1 v.property.2)
      ⟨hz,hm⟩ ⟨hv,hm⟩
  let K : Set S := K0 ∪ D
  have hK : IsClosed K := (M.cover.branch.finite_toSet.isClosed.union
    (P.finite x.selected).isClosed).union hD
  obtain ⟨W,hW,hAW0,htrace⟩ := isolate M anchor F P x raw hraw side
  have hAW : (raw side).image \ K ⊆ W := by
    intro z hz
    exact hAW0 ⟨hz.1,fun h => hz.2 (Or.inl h)⟩
  obtain ⟨U,hU,hp,e,he,ha,hb,k,hrk,hkU,hk,hchoice⟩ := chart M anchor F P x raw hraw side
  let r := anchor.val.map x.t
  have hrA : r ∈ (raw side).image := by
    rw [hraw]
    exact Or.inl ⟨x.t,(by change x.t.val ≤ x.t.val; exact le_rfl),rfl⟩
  have hrMark : r ∉ (M.cover.branch : Set S) := by
    intro h
    rcases anchor.val.marked_only_at_ends x.t h with h | h
    · exact (ne_of_gt x.t_interior.1) (congrArg Subtype.val h)
    · exact (ne_of_lt x.t_interior.2) (congrArg Subtype.val h)
  have hrC : r ∈ crossings M anchor (P.rep x.selected) :=
    ⟨⟨mem_range_self _,hrMark⟩,⟨⟨x.s,x.same_point.symm⟩,hrMark⟩⟩
  have hrK : r ∈ K := Or.inl (Or.inr hrC)
  have hr0 : r ≠ (raw side).map 0 := by
    intro h
    exact hrMark (h ▸ (raw side).start_marked)
  have hr1 : r ≠ (raw side).map 1 := by
    intro h
    exact hrMark (h ▸ (raw side).end_marked)
  have hrD : r ∉ D := fun h => hrMark (rawD ⟨hrA,h⟩)
  have ribbon : ∃ (H : AmbientIsotopy S) (Nr : Set S),
      (∀ t z, z ∈ K → H.map (t,z)=z) ∧
      (∀ t z, z ∉ W → H.map (t,z)=z) ∧
      Disjoint (H.finalMap '' ((raw side).image \ K)) ((raw side).image ∪ K) ∧
      IsOpen Nr ∧ r ∈ Nr ∧ Nr ⊆ k.source ∧
      (∀ z, z ∈ (raw side).image \ K → z ∈ Nr →
        H.finalMap z ∈ k.source ∧ 0 < (k (H.finalMap z)).1) ∧
    ∀ v ∈ (raw side).image ∩ K,
      v ≠ (raw side).map 0 → v ≠ (raw side).map 1 →
      ∀ c : OpenPartialHomeomorph S (ℝ × ℝ), v ∈ c.source →
        (∀ z ∈ c.source, z ∈ (raw side).image ↔ (c z).1=0) →
        ∃ (σ : Bool) (V : Set S), IsOpen V ∧ v ∈ V ∧ V ⊆ c.source ∧
          ∀ z, z ∈ (raw side).image \ K →
            z ∈ V → H.finalMap z ∈ c.source ∧
              (if σ then 0 < (c (H.finalMap z)).1 else (c (H.finalMap z)).1 < 0) := by
    by_cases hlo : (raw side).map (0 : Interval)=(raw side).map 1
    · exact loopRibbon M (raw side) hlo K W hK (fun z hz => Or.inl (Or.inl hz))
        hW hAW r hrA hrK hr0 hr1 k hrk hk
    · exact nonloopRibbon M (raw side) hlo K W hK (fun z hz => Or.inl (Or.inl hz))
        hW hAW r hrA hrK hr0 hr1 k hrk hk
  obtain ⟨H,Nr,hfix,houtside,hdisj,hNr,hrNr,hNrk,hside,hAll⟩ := ribbon
  have maps (t : Interval) (z : S) (hz : z ∈ W) : H.map (t,z) ∈ W := by
    by_contra hn
    obtain ⟨e,he⟩ := H.homeomorphism_at t
    have hh : H.map (t,H.map (t,z)) = H.map (t,z) := houtside t _ hn
    have hzEq : H.map (t,z) = z := e.injective (by simpa only [he] using hh)
    exact hn (hzEq.symm ▸ hz)
  have imageEq : H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) =
      (raw side).image ∩ K0 ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) := by
    ext z
    constructor
    · rintro ⟨⟨w,hw,he⟩,hzD⟩
      by_cases hwK : w ∈ K
      · have he0 : H.finalMap w=w := hfix 1 w hwK
        rw [he0] at he
        subst z
        have hwK0 : w ∈ K0 := by
          rcases hwK with h | h
          · exact h
          · exact Or.inl (rawD ⟨hw,h⟩)
        exact ⟨⟨hw,hwK0⟩,hzD⟩
      · have hzW : z ∈ W := he ▸ maps 1 w (hAW ⟨hw,hwK⟩)
        exact False.elim (disjoint_left.mp hdisj
          ⟨w,⟨hw,hwK⟩,he⟩ (Or.inl (htrace ⟨hzD,hzW⟩)))
    · rintro ⟨⟨hzA,hzK⟩,hzD⟩
      exact ⟨⟨z,hzA,hfix 1 z (Or.inl hzK)⟩,hzD⟩
  obtain ⟨f,hf⟩ := H.homeomorphism_at (1 : Interval)
  have hfFinal (z : S) : f z=H.finalMap z := hf z
  have hrFixed : f r=r := (hfFinal r).trans (hfix 1 r hrK)
  have hcOther : IsClosed (K0 \ {r}) :=
    ((M.cover.branch.finite_toSet.union (P.finite x.selected)).subset sdiff_subset).isClosed
  let N := ((k.source ∩ f '' Nr) ∩ (K0 \ {r})ᶜ) ∩ Dᶜ
  have hN : IsOpen N := ((k.open_source.inter (f.isOpenMap _ hNr)).inter
    hcOther.isOpen_compl).inter hD.isOpen_compl
  have hrN : r ∈ N := ⟨⟨⟨hrk,⟨r,hrNr,hrFixed⟩⟩,
    fun h => h.2 (mem_singleton r)⟩,hrD⟩
  have hNU : N ⊆ U := fun z hz => hkU hz.1.1.1
  let reflect : {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1} ≃ₜ
      {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1} := {
    toEquiv := {
      toFun := fun z => ⟨(z.val.1,if side then z.val.2 else -z.val.2),by
        cases side <;> simpa using z.property⟩
      invFun := fun z => ⟨(z.val.1,if side then z.val.2 else -z.val.2),by
        cases side <;> simpa using z.property⟩
      left_inv := by intro z; cases side <;> apply Subtype.ext <;> simp
      right_inv := by intro z; cases side <;> apply Subtype.ext <;> simp }
    continuous_toFun := by cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop
    continuous_invFun := by cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop }
  let ep := e.trans reflect
  refine ⟨H,U,hU,hp,ep,N,(fun t z hz => hfix t z (Or.inl hz)),?_,imageEq,?_,?_,?_,hN,hrN,hNU,?_,?_,?_,?_⟩
  · intro v hne hs t z hz
    exact hfix t z (Or.inr (mem_iUnion.mpr ⟨⟨v,hne,hs⟩,hz⟩))
  · change (reflect (e ⟨_,hp⟩)).val=(0,0)
    cases side <;> simp [reflect,he]
  · intro z
    cases side <;> simpa [ep,reflect] using ha z
  · intro z
    simpa [ep,reflect] using hb z
  · intro z hz hzK0
    by_contra hn
    exact hz.1.2 ⟨hzK0,fun h => hn (mem_singleton_iff.mp h)⟩
  · intro v hne hs
    exact disjoint_left.mpr (fun z hz hv => hz.2 (mem_iUnion.mpr ⟨⟨v,hne,hs⟩,hv⟩))
  · intro z hz hzN
    obtain ⟨w,hw,hwz⟩ := hz
    obtain ⟨u,hu,huz⟩ := hzN.1.1.2
    have hewu : w=u := f.injective ((hfFinal w).trans (hwz.trans huz.symm))
    have hwNr : w ∈ Nr := hewu ▸ hu
    by_cases hwK : w ∈ K
    · left
      have hzz : w=z.val := (hfix 1 w hwK).symm.trans hwz
      have hzK0 : z.val ∈ K0 := by
        rcases hwK with h | h
        · exact hzz ▸ h
        · exact Or.inl (hzz ▸ rawD ⟨hw,h⟩)
      by_contra hn
      exact hzN.1.2 ⟨hzK0,fun h => hn (mem_singleton_iff.mp h)⟩
    · right
      have hpSide := (hside w ⟨hw,hwK⟩ hwNr).2
      have hpSideZ : 0 < (k z.val).1 := hwz ▸ hpSide
      have hc := (hchoice z hzN.1.1.1).mp hpSideZ
      cases side <;> simpa [ep,reflect] using hc
  · intro v hv hv0 hv1 c hvc hc
    obtain ⟨σ,V,hV,hvV,hVc,hdirection⟩ := hAll v ⟨hv.1,Or.inl hv.2⟩ hv0 hv1 c hvc hc
    refine ⟨σ,V,hV,hvV,hVc,?_⟩
    intro z hz hzV
    have hzK : z ∉ K := by
      rintro (h | h)
      · exact hz.2 h
      · exact hz.2 (Or.inl (rawD ⟨hz.1,h⟩))
    exact hdirection z ⟨hz.1,hzK⟩ hzV

private theorem actualSourceSurgery_branch_10 (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
(F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
(x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
(hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
(side : Bool) (Obstacle : Set S) (hObstacle : IsClosed Obstacle)
(hrawObstacle : (raw side).image ∩ Obstacle ⊆ (M.cover.branch : Set S))
(hrObstacle : anchor.val.map x.t ∉ Obstacle) :
∃ (H : AmbientIsotopy S) (U : Set S) (hU : IsOpen U) (hp : anchor.val.map x.t ∈ U),
  ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
  ∃ N : Set S,
    (∀ t z, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
      H.map (t,z)=z) ∧
    (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
      ∀ t z, z ∈ (P.rep v).val.image → H.map (t,z)=z) ∧
    H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) =
      (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ∩
        (anchor.val.image ∪ (P.rep x.selected).val.image) ∧
    (e ⟨anchor.val.map x.t,hp⟩).val=(0,0) ∧
    (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
    (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
    IsOpen N ∧ anchor.val.map x.t ∈ N ∧ N ⊆ U ∧
    (∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
      z=anchor.val.map x.t) ∧
    (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
      Disjoint N (P.rep v).val.image) ∧
    (∀ t z, z ∈ Obstacle → H.map (t,z)=z) ∧ Disjoint N Obstacle ∧
    (∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
      z.val=anchor.val.map x.t ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) ∧
  ∀ v ∈ (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)),
    v ≠ (raw side).map 0 → v ≠ (raw side).map 1 →
    ∀ c : OpenPartialHomeomorph S (ℝ × ℝ), v ∈ c.source →
      (∀ z ∈ c.source, z ∈ (raw side).image ↔ (c z).1=0) →
      ∃ (σ : Bool) (V : Set S), IsOpen V ∧ v ∈ V ∧ V ⊆ c.source ∧
        ∀ z, z ∈ (raw side).image \ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) →
          z ∈ V → H.finalMap z ∈ c.source ∧
            (if σ then 0 < (c (H.finalMap z)).1 else (c (H.finalMap z)).1 < 0) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have loopRibbon := actualSourceSurgery_loopRibbon_5 (E := E) (S := S)
  have nonloopRibbon := actualSourceSurgery_nonloopRibbon_7 (E := E) (S := S)
  have chart := actualSourceSurgery_chart_3 (E := E) (S := S)
  have isolate (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
    (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
    (side : Bool) :
    ∃ W : Set S, IsOpen W ∧
      (raw side).image \ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ⊆ W ∧
      (anchor.val.image ∪ (P.rep x.selected).val.image) ∩ W ⊆ (raw side).image := by
  
    classical
    letI : T2Space S := M.sphere.isEmbedding.t2Space
    letI : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc
    let B := anchor.val.map '' {r : Interval | x.t.val ≤ r.val} ∪
      (P.rep x.selected).val.map '' {r : Interval |
        if side then r.val ≤ x.s.val else x.s.val ≤ r.val}
    have hB : IsClosed B := by
      apply IsClosed.union
      · exact ((isClosed_le continuous_const continuous_subtype_val).isCompact.image anchor.val.continuous).isClosed
      · have hc : IsClosed {r : Interval | if side then r.val ≤ x.s.val else x.s.val ≤ r.val} := by
          cases side
          · exact isClosed_le continuous_const continuous_subtype_val
          · exact isClosed_le continuous_subtype_val continuous_const
        exact (hc.isCompact.image (P.rep x.selected).val.continuous).isClosed
    refine ⟨Bᶜ,hB.isOpen_compl,?_,?_⟩
    · rintro z ⟨hz,hn⟩ hzB
      have hm : z ∉ (M.cover.branch : Set S) := fun h => hn (Or.inl h)
      have hcross : ¬ (z ∈ anchor.val.image ∧ z ∈ (P.rep x.selected).val.image) := by
        rintro ⟨ha,ho⟩
        exact hn (Or.inr ⟨⟨ha,hm⟩,⟨ho,hm⟩⟩)
      rw [hraw] at hz
      rcases hz with ⟨r,hr,he⟩ | ⟨r,hr,he⟩
      · rcases hzB with ⟨u,hu,huE⟩ | ⟨u,hu,huE⟩
        · have heq : anchor.val.map r = anchor.val.map u := he.trans huE.symm
          rcases anchor.val.injective_except_loop_closure r u heq with h | h | h
          · have hv := congrArg Subtype.val h
            have hrt : r = x.t := Subtype.ext (by dsimp at hr hu; linarith)
            apply hcross
            refine ⟨⟨r,he⟩,⟨x.s,?_⟩⟩
            rw [← x.same_point,← hrt]
            exact he
          · apply hm
            rw [← he,h.1]
            exact anchor.val.start_marked
          · apply hm
            rw [← he,h.1]
            exact anchor.val.end_marked
        · exact hcross ⟨⟨r,he⟩,⟨u,huE⟩⟩
      · rcases hzB with ⟨u,hu,huE⟩ | ⟨u,hu,huE⟩
        · exact hcross ⟨⟨u,huE⟩,⟨r,he⟩⟩
        · have heq : (P.rep x.selected).val.map r = (P.rep x.selected).val.map u := he.trans huE.symm
          rcases (P.rep x.selected).val.injective_except_loop_closure r u heq with h | h | h
          · have hv := congrArg Subtype.val h
            have hrs : r = x.s := by
              apply Subtype.ext
              change (if side then x.s.val ≤ r.val else r.val ≤ x.s.val) at hr
              change (if side then u.val ≤ x.s.val else x.s.val ≤ u.val) at hu
              cases side <;> simp only [Bool.false_eq_true,↓reduceIte] at hr hu <;> linarith
            apply hcross
            refine ⟨⟨x.t,?_⟩,⟨r,he⟩⟩
            rw [x.same_point,← hrs]
            exact he
          · apply hm
            rw [← he,h.1]
            exact (P.rep x.selected).val.start_marked
          · apply hm
            rw [← he,h.1]
            exact (P.rep x.selected).val.end_marked
    · rintro z ⟨hz,hzW⟩
      rw [hraw]
      rcases hz with ⟨r,hr⟩ | ⟨r,hr⟩
      · left
        refine ⟨r,?_,hr⟩
        have hn : ¬ x.t.val ≤ r.val := fun h => hzW (Or.inl ⟨r,h,hr⟩)
        exact (not_le.mp hn).le
      · right
        refine ⟨r,?_,hr⟩
        have hn : ¬ (if side then r.val ≤ x.s.val else x.s.val ≤ r.val) :=
          fun h => hzW (Or.inr ⟨r,h,hr⟩)
        cases side <;> simp only [Bool.false_eq_true,↓reduceIte] at hn ⊢ <;> exact (not_le.mp hn).le
  have incident : ∀ (side : Bool) (v : {v // v ∈ F}) (hne : v ≠ x.selected)
    (hsimplex : IsArcSimplex M {v.val, x.selected.val}),
    Disjoint ((raw side).image \ (M.cover.branch : Set S)) (arcInterior M (P.rep v)) := by
    intro side v hne hsimplex
    apply Set.disjoint_left.mpr
    rintro p ⟨hp, hpm⟩ hpv
    rw [hraw] at hp
    rcases hp with ⟨r, hr, he⟩ | ⟨r, hr, he⟩
    · by_cases hzero : r.val = 0
      · apply hpm
        rw [← he]
        have hz : r = (0 : Interval) := Subtype.ext hzero
        exact hz ▸ anchor.val.start_marked
      have hrpos : 0 < r.val := lt_of_le_of_ne r.property.1 (Ne.symm hzero)
      by_cases ht : r.val = x.t.val
      · have heq : r = x.t := Subtype.ext ht
        have hanchor : p ∈ arcInterior M anchor := ⟨⟨r, he⟩, hpm⟩
        have hold : p ∈ arcInterior M (P.rep x.selected) := by
          refine ⟨⟨x.s, ?_⟩, hpm⟩
          exact x.same_point.symm.trans (congrArg anchor.val.map heq.symm |>.trans he)
        exact Set.disjoint_left.mp (P.distinct_crossings x.selected v hne.symm)
          ⟨hanchor, hold⟩ ⟨hanchor, hpv⟩
      · have hrlt : r.val < x.t.val := lt_of_le_of_ne hr ht
        exact x.first v r hrpos hrlt (he.symm ▸ hpv)
    · have hold : p ∈ arcInterior M (P.rep x.selected) := ⟨⟨r, he⟩, hpm⟩
      exact Set.disjoint_left.mp (P.simplex_disjoint v x.selected hne hsimplex) hpv hold
  let K0 : Set S := (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)
  let J := {v : {v // v ∈ F} // v ≠ x.selected ∧ IsArcSimplex M {v.val,x.selected.val}}
  let D : Set S := (⋃ v : J, (P.rep v.val).val.image) ∪ Obstacle
  letI : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc
  have hD : IsClosed D := (isClosed_iUnion_of_finite (fun v : J =>
    (isCompact_range (P.rep v.val).val.continuous).isClosed)).union hObstacle
  have rawD : (raw side).image ∩ D ⊆ (M.cover.branch : Set S) := by
    rintro z ⟨hz,hd⟩
    by_contra hm
    rcases hd with hd | hd
    · obtain ⟨v,hv⟩ := mem_iUnion.mp hd
      exact disjoint_left.mp (incident side v.val v.property.1 v.property.2)
        ⟨hz,hm⟩ ⟨hv,hm⟩
    · exact hm (hrawObstacle ⟨hz,hd⟩)
  let K : Set S := K0 ∪ D
  have hK : IsClosed K := (M.cover.branch.finite_toSet.isClosed.union
    (P.finite x.selected).isClosed).union hD
  obtain ⟨W,hW,hAW0,htrace⟩ := isolate M anchor F P x raw hraw side
  have hAW : (raw side).image \ K ⊆ W := by
    intro z hz
    exact hAW0 ⟨hz.1,fun h => hz.2 (Or.inl h)⟩
  obtain ⟨U,hU,hp,e,he,ha,hb,k,hrk,hkU,hk,hchoice⟩ := chart M anchor F P x raw hraw side
  let r := anchor.val.map x.t
  have hrA : r ∈ (raw side).image := by
    rw [hraw]
    exact Or.inl ⟨x.t,(by change x.t.val ≤ x.t.val; exact le_rfl),rfl⟩
  have hrMark : r ∉ (M.cover.branch : Set S) := by
    intro h
    rcases anchor.val.marked_only_at_ends x.t h with h | h
    · exact (ne_of_gt x.t_interior.1) (congrArg Subtype.val h)
    · exact (ne_of_lt x.t_interior.2) (congrArg Subtype.val h)
  have hrC : r ∈ crossings M anchor (P.rep x.selected) :=
    ⟨⟨mem_range_self _,hrMark⟩,⟨⟨x.s,x.same_point.symm⟩,hrMark⟩⟩
  have hrK : r ∈ K := Or.inl (Or.inr hrC)
  have hr0 : r ≠ (raw side).map 0 := by
    intro h
    exact hrMark (h ▸ (raw side).start_marked)
  have hr1 : r ≠ (raw side).map 1 := by
    intro h
    exact hrMark (h ▸ (raw side).end_marked)
  have hrD : r ∉ D := fun h => hrMark (rawD ⟨hrA,h⟩)
  have ribbon : ∃ (H : AmbientIsotopy S) (Nr : Set S),
      (∀ t z, z ∈ K → H.map (t,z)=z) ∧
      (∀ t z, z ∉ W → H.map (t,z)=z) ∧
      Disjoint (H.finalMap '' ((raw side).image \ K)) ((raw side).image ∪ K) ∧
      IsOpen Nr ∧ r ∈ Nr ∧ Nr ⊆ k.source ∧
      (∀ z, z ∈ (raw side).image \ K → z ∈ Nr →
        H.finalMap z ∈ k.source ∧ 0 < (k (H.finalMap z)).1) ∧
    ∀ v ∈ (raw side).image ∩ K,
      v ≠ (raw side).map 0 → v ≠ (raw side).map 1 →
      ∀ c : OpenPartialHomeomorph S (ℝ × ℝ), v ∈ c.source →
        (∀ z ∈ c.source, z ∈ (raw side).image ↔ (c z).1=0) →
        ∃ (σ : Bool) (V : Set S), IsOpen V ∧ v ∈ V ∧ V ⊆ c.source ∧
          ∀ z, z ∈ (raw side).image \ K →
            z ∈ V → H.finalMap z ∈ c.source ∧
              (if σ then 0 < (c (H.finalMap z)).1 else (c (H.finalMap z)).1 < 0) := by
    by_cases hlo : (raw side).map (0 : Interval)=(raw side).map 1
    · exact loopRibbon M (raw side) hlo K W hK (fun z hz => Or.inl (Or.inl hz))
        hW hAW r hrA hrK hr0 hr1 k hrk hk
    · exact nonloopRibbon M (raw side) hlo K W hK (fun z hz => Or.inl (Or.inl hz))
        hW hAW r hrA hrK hr0 hr1 k hrk hk
  obtain ⟨H,Nr,hfix,houtside,hdisj,hNr,hrNr,hNrk,hside,hAll⟩ := ribbon
  have maps (t : Interval) (z : S) (hz : z ∈ W) : H.map (t,z) ∈ W := by
    by_contra hn
    obtain ⟨e,he⟩ := H.homeomorphism_at t
    have hh : H.map (t,H.map (t,z)) = H.map (t,z) := houtside t _ hn
    have hzEq : H.map (t,z) = z := e.injective (by simpa only [he] using hh)
    exact hn (hzEq.symm ▸ hz)
  have imageEq : H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) =
      (raw side).image ∩ K0 ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) := by
    ext z
    constructor
    · rintro ⟨⟨w,hw,he⟩,hzD⟩
      by_cases hwK : w ∈ K
      · have he0 : H.finalMap w=w := hfix 1 w hwK
        rw [he0] at he
        subst z
        have hwK0 : w ∈ K0 := by
          rcases hwK with h | h
          · exact h
          · exact Or.inl (rawD ⟨hw,h⟩)
        exact ⟨⟨hw,hwK0⟩,hzD⟩
      · have hzW : z ∈ W := he ▸ maps 1 w (hAW ⟨hw,hwK⟩)
        exact False.elim (disjoint_left.mp hdisj
          ⟨w,⟨hw,hwK⟩,he⟩ (Or.inl (htrace ⟨hzD,hzW⟩)))
    · rintro ⟨⟨hzA,hzK⟩,hzD⟩
      exact ⟨⟨z,hzA,hfix 1 z (Or.inl hzK)⟩,hzD⟩
  obtain ⟨f,hf⟩ := H.homeomorphism_at (1 : Interval)
  have hfFinal (z : S) : f z=H.finalMap z := hf z
  have hrFixed : f r=r := (hfFinal r).trans (hfix 1 r hrK)
  have hcOther : IsClosed (K0 \ {r}) :=
    ((M.cover.branch.finite_toSet.union (P.finite x.selected)).subset sdiff_subset).isClosed
  let N := ((k.source ∩ f '' Nr) ∩ (K0 \ {r})ᶜ) ∩ Dᶜ
  have hN : IsOpen N := ((k.open_source.inter (f.isOpenMap _ hNr)).inter
    hcOther.isOpen_compl).inter hD.isOpen_compl
  have hrN : r ∈ N := ⟨⟨⟨hrk,⟨r,hrNr,hrFixed⟩⟩,
    fun h => h.2 (mem_singleton r)⟩,hrD⟩
  have hNU : N ⊆ U := fun z hz => hkU hz.1.1.1
  let reflect : {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1} ≃ₜ
      {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1} := {
    toEquiv := {
      toFun := fun z => ⟨(z.val.1,if side then z.val.2 else -z.val.2),by
        cases side <;> simpa using z.property⟩
      invFun := fun z => ⟨(z.val.1,if side then z.val.2 else -z.val.2),by
        cases side <;> simpa using z.property⟩
      left_inv := by intro z; cases side <;> apply Subtype.ext <;> simp
      right_inv := by intro z; cases side <;> apply Subtype.ext <;> simp }
    continuous_toFun := by cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop
    continuous_invFun := by cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop }
  let ep := e.trans reflect
  refine ⟨H,U,hU,hp,ep,N,(fun t z hz => hfix t z (Or.inl hz)),?_,imageEq,?_,?_,?_,hN,hrN,hNU,?_,?_,?_,?_,?_,?_⟩
  · intro v hne hs t z hz
    exact hfix t z (Or.inr (Or.inl (mem_iUnion.mpr ⟨⟨v,hne,hs⟩,hz⟩)))
  · change (reflect (e ⟨_,hp⟩)).val=(0,0)
    cases side <;> simp [reflect,he]
  · intro z
    cases side <;> simpa [ep,reflect] using ha z
  · intro z
    simpa [ep,reflect] using hb z
  · intro z hz hzK0
    by_contra hn
    exact hz.1.2 ⟨hzK0,fun h => hn (mem_singleton_iff.mp h)⟩
  · intro v hne hs
    exact disjoint_left.mpr (fun z hz hv => hz.2 (Or.inl (mem_iUnion.mpr ⟨⟨v,hne,hs⟩,hv⟩)))
  · intro t z hz
    exact hfix t z (Or.inr (Or.inr hz))
  · exact disjoint_left.mpr (fun z hz hb => hz.2 (Or.inr hb))
  · intro z hz hzN
    obtain ⟨w,hw,hwz⟩ := hz
    obtain ⟨u,hu,huz⟩ := hzN.1.1.2
    have hewu : w=u := f.injective ((hfFinal w).trans (hwz.trans huz.symm))
    have hwNr : w ∈ Nr := hewu ▸ hu
    by_cases hwK : w ∈ K
    · left
      have hzz : w=z.val := (hfix 1 w hwK).symm.trans hwz
      have hzK0 : z.val ∈ K0 := by
        rcases hwK with h | h
        · exact hzz ▸ h
        · exact Or.inl (hzz ▸ rawD ⟨hw,h⟩)
      by_contra hn
      exact hzN.1.2 ⟨hzK0,fun h => hn (mem_singleton_iff.mp h)⟩
    · right
      have hpSide := (hside w ⟨hw,hwK⟩ hwNr).2
      have hpSideZ : 0 < (k z.val).1 := hwz ▸ hpSide
      have hc := (hchoice z hzN.1.1.1).mp hpSideZ
      cases side <;> simpa [ep,reflect] using hc
  · intro v hv hv0 hv1 c hvc hc
    obtain ⟨σ,V,hV,hvV,hVc,hdirection⟩ := hAll v ⟨hv.1,Or.inl hv.2⟩ hv0 hv1 c hvc hc
    refine ⟨σ,V,hV,hvV,hVc,?_⟩
    intro z hz hzV
    have hzK : z ∉ K := by
      rintro (h | h)
      · exact hz.2 h
      · exact hz.2 (Or.inl (rawD ⟨hz.1,h⟩))
    exact hdirection z ⟨hz.1,hzK⟩ hzV

private theorem actualSourceSurgery_germ_11 (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
    (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
    (side : Bool) :
    ∃ (H : AmbientIsotopy S) (U : Set S) (hU : IsOpen U) (hp : anchor.val.map x.t ∈ U),
      ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
      ∃ N : Set S,
        (∀ t z, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
          H.map (t,z)=z) ∧
        (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
          ∀ t z, z ∈ (P.rep v).val.image → H.map (t,z)=z) ∧
        H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) =
          (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ∩
            (anchor.val.image ∪ (P.rep x.selected).val.image) ∧
        (e ⟨anchor.val.map x.t,hp⟩).val=(0,0) ∧
        (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
        (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
        IsOpen N ∧ anchor.val.map x.t ∈ N ∧ N ⊆ U ∧
        (∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
          z=anchor.val.map x.t) ∧
        (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
          Disjoint N (P.rep v).val.image) ∧
        (∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
          z.val=anchor.val.map x.t ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) ∧
      ∀ v ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected), v ≠ anchor.val.map x.t →
        ∃ (U : Set S) (hU : IsOpen U) (hp : v ∈ U),
          ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}, ∃ N : Set S,
            (e ⟨v,hp⟩).val=(0,0) ∧
            (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
            (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
            IsOpen N ∧ v ∈ N ∧ N ⊆ U ∧
            (∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) → z=v) ∧
            (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
              Disjoint N (P.rep w).val.image) ∧ Disjoint N (raw (!side)).image ∧
            ∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
              z.val=v ∨ 0 < (e z).val.1 := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have branch := actualSourceSurgery_branch_9 (E := E) (S := S)
  have tailChart := actualSourceSurgery_tailChart_1 (E := E) (S := S)
  obtain ⟨H,Uf,hUf,hpf,ef,Nf,hfix,hneighbors,himage,hef,haf,hbf,hNf,hrNf,hNfUf,hnodef,hneighborNf,hgermf,hAll⟩ :=
    branch M anchor F P x raw hraw side
  let K0 : Set S := (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)
  let J := {w : {w // w ∈ F} // w ≠ x.selected ∧ IsArcSimplex M {w.val,x.selected.val}}
  let D : Set S := ⋃ w : J, (P.rep w.val).val.image
  letI : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc
  have hD : IsClosed D := isClosed_iUnion_of_finite (fun w =>
    (isCompact_range (P.rep w.val).val.continuous).isClosed)
  obtain ⟨f,hf⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
  have hfFinal (z : S) : f z=H.finalMap z := hf z
  refine ⟨H,Uf,hUf,hpf,ef,Nf,hfix,hneighbors,himage,hef,haf,hbf,hNf,hrNf,hNfUf,hnodef,hneighborNf,hgermf,?_⟩
  intro v hv hvFirst
  obtain ⟨U,hU,hp,e,he,ha,hb,c,hcU,hcapply,hvc,hcv,hcm,hca,hcb,hcr,hcOther⟩ :=
    tailChart M anchor F P x raw hraw side v hv hvFirst
  have hvm : v ∉ (M.cover.branch : Set S) := hv.2.1.2
  have hv0 : v ≠ (raw side).map 0 := fun h => hvm (h ▸ (raw side).start_marked)
  have hv1 : v ≠ (raw side).map 1 := fun h => hvm (h ▸ (raw side).end_marked)
  obtain ⟨σ,V,hV,hvV,hVc,hdir⟩ := hAll v ⟨hv.1,Or.inr hv.2⟩ hv0 hv1 c hvc hcr
  have hvMark : v ∉ (M.cover.branch : Set S) := hv.2.1.2
  have hvD : v ∉ D := by
    intro h
    obtain ⟨w,hw⟩ := mem_iUnion.mp h
    exact disjoint_left.mp (P.distinct_crossings x.selected w.val w.property.1.symm)
      hv.2 ⟨hv.2.1,⟨hw,hvMark⟩⟩
  have hvFixed : f v=v := (hfFinal v).trans (hfix 1 v (Or.inr hv.2))
  have hOther : IsClosed (K0 \ {v}) :=
    ((M.cover.branch.finite_toSet.union (P.finite x.selected)).subset sdiff_subset).isClosed
  let N := ((c.source ∩ f '' V) ∩ (K0 \ {v})ᶜ) ∩ Dᶜ
  have hN : IsOpen N := ((c.open_source.inter (f.isOpenMap _ hV)).inter
    hOther.isOpen_compl).inter hD.isOpen_compl
  have hvN : v ∈ N := ⟨⟨⟨hvc,⟨v,hvV,hvFixed⟩⟩,fun h => h.2 (mem_singleton v)⟩,hvD⟩
  have hNU : N ⊆ U := fun z hz => hcU hz.1.1.1
  let reflect : {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1} ≃ₜ
      {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1} := {
    toEquiv := {
      toFun := fun z => ⟨(if σ then z.val.1 else -z.val.1,z.val.2),by
        cases σ <;> simpa using z.property⟩
      invFun := fun z => ⟨(if σ then z.val.1 else -z.val.1,z.val.2),by
        cases σ <;> simpa using z.property⟩
      left_inv := by intro z; cases σ <;> apply Subtype.ext <;> simp
      right_inv := by intro z; cases σ <;> apply Subtype.ext <;> simp }
    continuous_toFun := by cases σ <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop
    continuous_invFun := by cases σ <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop }
  let ep := e.trans reflect
  have onlyNode : ∀ z ∈ N, z ∈ K0 → z=v := by
    intro z hz hzK
    by_contra hn
    exact hz.1.2 ⟨hzK,fun h => hn (mem_singleton_iff.mp h)⟩
  refine ⟨U,hU,hp,ep,N,?_,?_,?_,hN,hvN,hNU,onlyNode,?_,?_,?_⟩
  · change (reflect (e ⟨v,hp⟩)).val=(0,0)
    cases σ <;> simp [reflect,he]
  · intro z
    simpa [ep,reflect] using ha z
  · intro z
    cases σ <;> simpa [ep,reflect] using hb z
  · intro w hn hs
    exact disjoint_left.mpr (fun z hz hw => hz.2 (mem_iUnion.mpr ⟨⟨w,hn,hs⟩,hw⟩))
  · exact disjoint_left.mpr (fun z hz ho => hcOther z hz.1.1.1 ho)
  · intro z hz hzN
    obtain ⟨w,hw,hwz⟩ := hz
    obtain ⟨u,hu,huz⟩ := hzN.1.1.2
    have hwu : w=u := f.injective ((hfFinal w).trans (hwz.trans huz.symm))
    have hwV : w ∈ V := hwu ▸ hu
    by_cases hwK : w ∈ K0
    · left
      have hzz : w=z.val := (hfix 1 w hwK).symm.trans hwz
      exact onlyNode z.val hzN (hzz ▸ hwK)
    · right
      have hh := (hdir w ⟨hw,hwK⟩ hwV).2
      have hs : if σ then 0 < (c z.val).1 else (c z.val).1 < 0 := hwz ▸ hh
      rw [hcapply z] at hs
      cases σ <;> simpa [ep,reflect] using hs

private theorem actualSourceSurgery_germ_12 (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
    (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
    (side : Bool) (Obstacle : Set S) (hObstacle : IsClosed Obstacle)
    (hrawObstacle : (raw side).image ∩ Obstacle ⊆ (M.cover.branch : Set S))
    (hrObstacle : anchor.val.map x.t ∉ Obstacle) :
    ∃ (H : AmbientIsotopy S) (U : Set S) (hU : IsOpen U) (hp : anchor.val.map x.t ∈ U),
      ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
      ∃ N : Set S,
        (∀ t z, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
          H.map (t,z)=z) ∧
        (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
          ∀ t z, z ∈ (P.rep v).val.image → H.map (t,z)=z) ∧
        H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) =
          (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ∩
            (anchor.val.image ∪ (P.rep x.selected).val.image) ∧
        (e ⟨anchor.val.map x.t,hp⟩).val=(0,0) ∧
        (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
        (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
        IsOpen N ∧ anchor.val.map x.t ∈ N ∧ N ⊆ U ∧
        (∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
          z=anchor.val.map x.t) ∧
        (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
          Disjoint N (P.rep v).val.image) ∧
        (∀ t z, z ∈ Obstacle → H.map (t,z)=z) ∧ Disjoint N Obstacle ∧
        (∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
          z.val=anchor.val.map x.t ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) ∧
      ∀ v ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected), v ≠ anchor.val.map x.t →
        ∃ (U : Set S) (hU : IsOpen U) (hp : v ∈ U),
          ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}, ∃ N : Set S,
            (e ⟨v,hp⟩).val=(0,0) ∧
            (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
            (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
            IsOpen N ∧ v ∈ N ∧ N ⊆ U ∧
            (∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) → z=v) ∧
            (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
              Disjoint N (P.rep w).val.image) ∧ Disjoint N Obstacle ∧
            ∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
              z.val=v ∨ 0 < (e z).val.1 := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have branch := actualSourceSurgery_branch_10 (E := E) (S := S)
  have tailChart := actualSourceSurgery_tailChart_2 (E := E) (S := S)
  obtain ⟨H,Uf,hUf,hpf,ef,Nf,hfix,hneighbors,himage,hef,haf,hbf,hNf,hrNf,hNfUf,hnodef,hneighborNf,hfixObstacle,hNfObstacle,hgermf,hAll⟩ :=
    branch M anchor F P x raw hraw side Obstacle hObstacle hrawObstacle hrObstacle
  let K0 : Set S := (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)
  let J := {w : {w // w ∈ F} // w ≠ x.selected ∧ IsArcSimplex M {w.val,x.selected.val}}
  let D : Set S := (⋃ w : J, (P.rep w.val).val.image) ∪ Obstacle
  letI : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc
  have hD : IsClosed D := (isClosed_iUnion_of_finite (fun w : J =>
    (isCompact_range (P.rep w.val).val.continuous).isClosed)).union hObstacle
  obtain ⟨f,hf⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
  have hfFinal (z : S) : f z=H.finalMap z := hf z
  refine ⟨H,Uf,hUf,hpf,ef,Nf,hfix,hneighbors,himage,hef,haf,hbf,hNf,hrNf,hNfUf,hnodef,hneighborNf,hfixObstacle,hNfObstacle,hgermf,?_⟩
  intro v hv hvFirst
  obtain ⟨U,hU,hp,e,he,ha,hb,c,hcU,hcapply,hvc,hcv,hcm,hca,hcb,hcr⟩ :=
    tailChart M anchor F P x raw hraw side v hv hvFirst
  have hvm : v ∉ (M.cover.branch : Set S) := hv.2.1.2
  have hv0 : v ≠ (raw side).map 0 := fun h => hvm (h ▸ (raw side).start_marked)
  have hv1 : v ≠ (raw side).map 1 := fun h => hvm (h ▸ (raw side).end_marked)
  obtain ⟨σ,V,hV,hvV,hVc,hdir⟩ := hAll v ⟨hv.1,Or.inr hv.2⟩ hv0 hv1 c hvc hcr
  have hvMark : v ∉ (M.cover.branch : Set S) := hv.2.1.2
  have hvD : v ∉ D := by
    intro h
    rcases h with h | h
    · obtain ⟨w,hw⟩ := mem_iUnion.mp h
      exact disjoint_left.mp (P.distinct_crossings x.selected w.val w.property.1.symm)
        hv.2 ⟨hv.2.1,⟨hw,hvMark⟩⟩
    · exact hvMark (hrawObstacle ⟨hv.1,h⟩)
  have hvFixed : f v=v := (hfFinal v).trans (hfix 1 v (Or.inr hv.2))
  have hOther : IsClosed (K0 \ {v}) :=
    ((M.cover.branch.finite_toSet.union (P.finite x.selected)).subset sdiff_subset).isClosed
  let N := ((c.source ∩ f '' V) ∩ (K0 \ {v})ᶜ) ∩ Dᶜ
  have hN : IsOpen N := ((c.open_source.inter (f.isOpenMap _ hV)).inter
    hOther.isOpen_compl).inter hD.isOpen_compl
  have hvN : v ∈ N := ⟨⟨⟨hvc,⟨v,hvV,hvFixed⟩⟩,fun h => h.2 (mem_singleton v)⟩,hvD⟩
  have hNU : N ⊆ U := fun z hz => hcU hz.1.1.1
  let reflect : {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1} ≃ₜ
      {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1} := {
    toEquiv := {
      toFun := fun z => ⟨(if σ then z.val.1 else -z.val.1,z.val.2),by
        cases σ <;> simpa using z.property⟩
      invFun := fun z => ⟨(if σ then z.val.1 else -z.val.1,z.val.2),by
        cases σ <;> simpa using z.property⟩
      left_inv := by intro z; cases σ <;> apply Subtype.ext <;> simp
      right_inv := by intro z; cases σ <;> apply Subtype.ext <;> simp }
    continuous_toFun := by cases σ <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop
    continuous_invFun := by cases σ <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop }
  let ep := e.trans reflect
  have onlyNode : ∀ z ∈ N, z ∈ K0 → z=v := by
    intro z hz hzK
    by_contra hn
    exact hz.1.2 ⟨hzK,fun h => hn (mem_singleton_iff.mp h)⟩
  refine ⟨U,hU,hp,ep,N,?_,?_,?_,hN,hvN,hNU,onlyNode,?_,?_,?_⟩
  · change (reflect (e ⟨v,hp⟩)).val=(0,0)
    cases σ <;> simp [reflect,he]
  · intro z
    simpa [ep,reflect] using ha z
  · intro z
    cases σ <;> simpa [ep,reflect] using hb z
  · intro w hn hs
    exact disjoint_left.mpr (fun z hz hw => hz.2 (Or.inl (mem_iUnion.mpr ⟨⟨w,hn,hs⟩,hw⟩)))
  · exact disjoint_left.mpr (fun z hz hb => hz.2 (Or.inr hb))
  · intro z hz hzN
    obtain ⟨w,hw,hwz⟩ := hz
    obtain ⟨u,hu,huz⟩ := hzN.1.1.2
    have hwu : w=u := f.injective ((hfFinal w).trans (hwz.trans huz.symm))
    have hwV : w ∈ V := hwu ▸ hu
    by_cases hwK : w ∈ K0
    · left
      have hzz : w=z.val := (hfix 1 w hwK).symm.trans hwz
      exact onlyNode z.val hzN (hzz ▸ hwK)
    · right
      have hh := (hdir w ⟨hw,hwK⟩ hwV).2
      have hs : if σ then 0 < (c z.val).1 else (c z.val).1 < 0 := hwz ▸ hh
      rw [hcapply z] at hs
      cases σ <;> simpa [ep,reflect] using hs

private theorem actualSourceSurgery_secondBranch_13 (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
    (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
    (side : Bool) (Obstacle : Set S) (hObstacle : IsClosed Obstacle)
    (hrawObstacle : (raw side).image ∩ Obstacle ⊆ (M.cover.branch : Set S))
    (hrObstacle : anchor.val.map x.t ∉ Obstacle) :
    ∃ (H J Q : AmbientIsotopy S),
      (∀ t z, z ∈ (M.cover.branch : Set S) → H.map (t,z)=z ∧ J.map (t,z)=z ∧ Q.map (t,z)=z) ∧
      (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
        ∀ t z, z ∈ (P.rep w).val.image → H.map (t,z)=z ∧ J.map (t,z)=z ∧ Q.map (t,z)=z) ∧
      (∀ t z, z ∈ Obstacle → H.map (t,z)=z ∧ J.map (t,z)=z ∧ Q.map (t,z)=z) ∧
      (Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ (P.rep x.selected).val.image =
        ((H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) \ 
          ((raw side).image ∩ crossings M anchor (P.rep x.selected)) ∧
      (∀ t z, J.map (t,z) ∈ anchor.val.image ↔ z ∈ anchor.val.image) ∧
      (Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ anchor.val.image =
        ((J.finalMap '' (H.finalMap '' (raw side).image)) ∩ anchor.val.image) \ {anchor.val.map x.t} ∧
      ((((Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ anchor.val.image) \ (M.cover.branch : Set S)).ncard =
        (((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}).ncard ∧
        (((Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ anchor.val.image) \ (M.cover.branch : Set S)).Finite) ∧
      Disjoint ((Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) \ (M.cover.branch : Set S))
        (arcInterior M (P.rep x.selected)) ∧
      (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
        Disjoint ((Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) \ (M.cover.branch : Set S))
          (arcInterior M (P.rep w))) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  have family (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
      (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
      (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
      (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
      (side : Bool) (Obstacle : Set S) (hObstacle : IsClosed Obstacle)
      (hrawObstacle : (raw side).image ∩ Obstacle ⊆ (M.cover.branch : Set S))
      (hrObstacle : anchor.val.map x.t ∉ Obstacle) :
      let R := ((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}
      ∃ (H : AmbientIsotopy S) (U : Set S) (hU : IsOpen U) (hp : anchor.val.map x.t ∈ U),
        ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
        ∃ N : Set S, ∃ (J : AmbientIsotopy S),
          (∀ t z, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
            H.map (t,z)=z) ∧
          (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
            ∀ t z, z ∈ (P.rep v).val.image → H.map (t,z)=z) ∧
          H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) =
            (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ∩
              (anchor.val.image ∪ (P.rep x.selected).val.image) ∧
          (e ⟨anchor.val.map x.t,hp⟩).val=(0,0) ∧
          (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
          (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
          IsOpen N ∧ anchor.val.map x.t ∈ N ∧ N ⊆ U ∧
          (∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
            z=anchor.val.map x.t) ∧
          (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
            Disjoint N (P.rep v).val.image) ∧
          (∀ t z, z ∈ Obstacle → H.map (t,z)=z) ∧ Disjoint N Obstacle ∧
          (∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
            z.val=anchor.val.map x.t ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) ∧
        (∀ t z, z ∈ N → J.map (t,z)=z) ∧
        (∀ t z, z ∈ (M.cover.branch : Set S) → J.map (t,z)=z) ∧
        (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
          ∀ t z, z ∈ (P.rep w).val.image → J.map (t,z)=z) ∧
        (∀ t z, J.map (t,z) ∈ anchor.val.image ↔ z ∈ anchor.val.image) ∧
        (∀ z : U, z.val ∈ J.finalMap '' (H.finalMap '' (raw side).image) → z.val ∈ N →
          z.val=anchor.val.map x.t ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) ∧
        (J.finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image =
          ((H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) \ R ∧ (∀ t z, z ∈ Obstacle → J.map (t,z)=z) := by
    classical
    have family (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
        (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
        (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
        (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
        (side : Bool) (Obstacle : Set S) (hObstacle : IsClosed Obstacle)
        (hrawObstacle : (raw side).image ∩ Obstacle ⊆ (M.cover.branch : Set S))
        (hrObstacle : anchor.val.map x.t ∉ Obstacle) :
        let R := ((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}
        ∃ (H : AmbientIsotopy S) (U : Set S) (hU : IsOpen U) (hp : anchor.val.map x.t ∈ U),
          ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
          ∃ N : Set S, ∃ (Q : R → AmbientIsotopy S) (W : R → Set S),
            (∀ t z, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
              H.map (t,z)=z) ∧
            (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
              ∀ t z, z ∈ (P.rep v).val.image → H.map (t,z)=z) ∧
            H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) =
              (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ∩
                (anchor.val.image ∪ (P.rep x.selected).val.image) ∧
            (e ⟨anchor.val.map x.t,hp⟩).val=(0,0) ∧
            (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
            (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
            IsOpen N ∧ anchor.val.map x.t ∈ N ∧ N ⊆ U ∧
            (∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
              z=anchor.val.map x.t) ∧
            (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
              Disjoint N (P.rep v).val.image) ∧
            (∀ t z, z ∈ Obstacle → H.map (t,z)=z) ∧ Disjoint N Obstacle ∧
            (∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
              z.val=anchor.val.map x.t ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) ∧
          (∀ p : R, IsOpen (W p) ∧ p.val ∈ W p ∧
              (∀ t z, z ∉ W p → (Q p).map (t,z)=z) ∧
              (∀ t z, z ∈ (M.cover.branch : Set S) → (Q p).map (t,z)=z) ∧
              (∀ t z, z ∈ crossings M anchor (P.rep x.selected) → z ≠ p.val → (Q p).map (t,z)=z) ∧
              (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
                ∀ t z, z ∈ (P.rep w).val.image → (Q p).map (t,z)=z) ∧
              (∀ t z, (Q p).map (t,z) ∈ anchor.val.image ↔ z ∈ anchor.val.image) ∧
              ((Q p).finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image =
                ((H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) \ {p.val}) ∧
          (∀ p q : R, p ≠ q → Disjoint (W p) (W q)) ∧ (∀ p : R, Disjoint N (W p)) ∧ ∀ p : R, Disjoint (W p) Obstacle := by
      classical
      letI : T2Space S := M.sphere.symm.t2Space
      letI : CompactSpace S := M.sphere.symm.compactSpace
      have germ := actualSourceSurgery_germ_12 (E := E) (S := S)
      have clearFamily {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
      (U : Set S) (hU : IsOpen U) (p : S) (hp : p ∈ U)
      (e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1})
      (he : (e ⟨p,hp⟩).val=(0,0))
      (δ : ℝ) (hd : 0 < δ) (hd1 : δ < 1) :
      ∃ H : AmbientIsotopy S,
        (∀ t z, z ∉ U → H.map (t,z)=z) ∧
        (∀ t (z : U), δ ≤ |(e z).val.1| ∨ δ ≤ |(e z).val.2| → H.map (t,z.val)=z.val) ∧
        (∀ t (z : U), ∃ hz : H.map (t,z.val) ∈ U,
          (e ⟨H.map (t,z.val),hz⟩).val.2=(e z).val.2) ∧
        ∀ A : Set S,
          (∀ z : U, z.val ∈ A → |(e z).val.1| < δ → |(e z).val.2| < δ →
            z.val=p ∨ 0 < (e z).val.1) →
          ∀ z : U, z.val ∈ H.finalMap '' A → |(e z).val.1| < δ → |(e z).val.2| < δ →
            0 < (e z).val.1 := by
        classical
        let a : Amount := ⟨(1/4:ℝ),by norm_num⟩
        let R := productIsotopy a
        have rfix (t : Interval) (z : ℝ × ℝ) (hz : 1 ≤ |z.1| ∨ 1 ≤ |z.2|) :
            R.map (t,z)=z := productIsotopy_fixed a t z hz
        have r0x : 0 < (R.finalMap (0,0)).1 := by
          change 0 < scalar (rowAmount (timeAmount a 1) 0).val 0
          norm_num [scalar,rowAmount,timeAmount,a,tent]
        have rpositive (t : Interval) (z : ℝ × ℝ) (hx : 0 < z.1) :
            0 < (R.map (t,z)).1 := by
          change 0 < z.1 + (t.val * (1/4:ℝ) * tent z.2) * tent z.1
          have ht := t.property.1
          have h1 := tent_nonneg z.1
          have h2 := tent_nonneg z.2
          exact hx.trans_le (le_add_of_nonneg_right (by positivity))
        let Q := {q : ℝ × ℝ | |q.1| < 1 ∧ |q.2| < 1}
        let g : (ℝ × ℝ) ≃ₜ Plane := {
          toEquiv := {
            toFun := fun z => Plane.mk (z.1/δ) (z.2/δ)
            invFun := fun z => (δ*z 0,δ*z 1)
            left_inv := by intro z; apply Prod.ext <;> simp [Plane.mk] <;> field_simp [ne_of_gt hd]
            right_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk,ne_of_gt hd] }
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
        let V : Set Plane := g '' Q
        let ee : U ≃ₜ V := e.trans (g.image Q)
        have hCV : Plane.closedSquare 0 1 ⊆ V := by
          intro z hz
          have hcoords := max_le_iff.mp (mem_closedSquare_zero_one.mp hz)
          refine ⟨g.symm z,?_,g.apply_symm_apply z⟩
          change |δ*z 0| < 1 ∧ |δ*z 1| < 1
          rw [abs_mul,abs_mul,abs_of_pos hd]
          constructor
          · exact (mul_le_of_le_one_right hd.le hcoords.1).trans_lt hd1
          · exact (mul_le_of_le_one_right hd.le hcoords.2).trans_lt hd1
        let pc := planeCoordinates
        let K : AmbientIsotopy Plane := {
          map := ⟨fun z => pc.symm (R.map (z.1,pc z.2)),by
            exact pc.symm.continuous.comp (R.map.continuous.comp
              (continuous_fst.prodMk (pc.continuous.comp continuous_snd)))⟩
          homeomorphism_at := by
            intro t
            obtain ⟨r,hr⟩ := R.homeomorphism_at t
            exact ⟨(pc.trans r).trans pc.symm,fun z => congrArg pc.symm (hr (pc z))⟩
          at_zero := by
            intro z
            change pc.symm (R.map (⟨0,by norm_num⟩,pc z))=z
            rw [R.at_zero,pc.symm_apply_apply] }
        have kcoord (t : Interval) (z : Plane) : pc (K.map (t,z))=R.map (t,pc z) :=
          pc.apply_symm_apply _
        have kfix (t : Interval) (z : Plane) (hz : z ∉ Plane.openSquare 0 1) :
            K.map (t,z)=z := by
          apply pc.injective
          rw [kcoord]
          apply rfix
          change 1 ≤ |z 0| ∨ 1 ≤ |z 1|
          have hn : ¬ (|z 0| < 1 ∧ |z 1| < 1) := by
            intro hh
            exact hz (mem_openSquare_zero_one.mpr (max_lt hh.1 hh.2))
          rcases not_and_or.mp hn with h | h
          · exact Or.inl (le_of_not_gt h)
          · exact Or.inr (le_of_not_gt h)
        obtain ⟨KU,H,hcoords,hlift,houtside⟩ := position_surface_chart_lift S U V hU ee
          (Plane.closedSquare 0 1) (isCompact_closedSquare 0 1) hCV K
          (fun t z hz => kfix t z (fun hh => hz
            (mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hh).le)))
        have coord (t : Interval) (z : U) :
            g (e ⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩).val =
              K.map (t,g (e z).val) := by
          have hs : (⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩ : U) =
              KU.map (t,z) := Subtype.ext (hlift t z)
          rw [hs]
          exact hcoords t z
        have localFix : ∀ t (z : U), δ ≤ |(e z).val.1| ∨ δ ≤ |(e z).val.2| →
            H.map (t,z.val)=z.val := by
          intro t z hz
          have hne : g (e z).val ∉ Plane.openSquare 0 1 := by
            intro hh
            have hcc := max_lt_iff.mp (mem_openSquare_zero_one.mp hh)
            have hx : |(e z).val.1| / δ < 1 := by
              simpa [g,Plane.mk,abs_div,abs_of_pos hd] using hcc.1
            have hy : |(e z).val.2| / δ < 1 := by
              simpa [g,Plane.mk,abs_div,abs_of_pos hd] using hcc.2
            have hx := (div_lt_iff₀ hd).mp hx
            have hy := (div_lt_iff₀ hd).mp hy
            rcases hz with hz | hz <;> linarith
          have hh := coord t z
          rw [kfix t _ hne] at hh
          exact congrArg Subtype.val (e.injective (Subtype.ext (g.injective hh)))
        refine ⟨H,houtside,localFix,?_,?_⟩
        · intro t z
          have hz : H.map (t,z.val) ∈ U := by
            rw [hlift t z]
            exact (KU.map (t,z)).property
          refine ⟨hz,?_⟩
          have hh := congrArg (fun v : Plane => v 1) (coord t z)
          change (e ⟨H.map (t,z.val),hz⟩).val.2 / δ =
            (R.map (t,pc (g (e z).val))).2 at hh
          change (e ⟨H.map (t,z.val),hz⟩).val.2 / δ = (e z).val.2 / δ at hh
          exact (div_left_inj' (ne_of_gt hd)).mp hh
        · intro A hA z hz hx hy
          obtain ⟨w,hw,hwz⟩ := hz
          have hwU : w ∈ U := by
            by_contra hn
            have hf := houtside 1 w hn
            change H.finalMap w=w at hf
            exact hn ((hf.symm.trans hwz).symm ▸ z.property)
          let wu : U := ⟨w,hwU⟩
          have hwx : |(e wu).val.1| < δ := by
            by_contra hn
            have hf := localFix 1 wu (Or.inl (le_of_not_gt hn))
            change H.finalMap w=w at hf
            have huw : wu=z := Subtype.ext (hf.symm.trans hwz)
            exact hn (huw.symm ▸ hx)
          have hwy : |(e wu).val.2| < δ := by
            by_contra hn
            have hf := localFix 1 wu (Or.inr (le_of_not_gt hn))
            change H.finalMap w=w at hf
            have huw : wu=z := Subtype.ext (hf.symm.trans hwz)
            exact hn (huw.symm ▸ hy)
          have hc := congrArg pc (coord 1 wu)
          have hez : (⟨H.map (1,wu.val),by rw [hlift]; exact (KU.map (1,wu)).property⟩ : U)=z :=
            Subtype.ext hwz
          rw [hez,kcoord] at hc
          have coords (v : U) : pc (g (e v).val) = ((e v).val.1/δ,(e v).val.2/δ) := rfl
          rw [coords,coords] at hc
          have hx : 0 < (R.finalMap ((e wu).val.1/δ,(e wu).val.2/δ)).1 := by
            rcases hA wu hw hwx hwy with hpw | hpw
            · have hwp : wu=⟨p,hp⟩ := Subtype.ext hpw
              rw [hwp,he]
              simpa using r0x
            · exact rpositive 1 _ (div_pos hpw hd)
          change ((e z).val.1/δ,(e z).val.2/δ)=R.finalMap _ at hc
          rw [←hc] at hx
          simpa using (lt_div_iff₀ hd).mp hx
      obtain ⟨H,Uf,hUf,hpf,ef,Nf,hfix,hneighbors,hgraph,hef,haf,hbf,hNf,hrNf,hNfUf,hnodef,hneighborNf,hHObstacle,hNfObstacle,hgermf,hAll⟩ := germ M anchor F P x raw hraw side Obstacle hObstacle hrawObstacle hrObstacle
      have clearNode (v : S) (hv : v ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected))
          (hvFirst : v ≠ anchor.val.map x.t) (O : Set S) (hO : IsOpen O) (hvO : v ∈ O) :
          ∃ (Q : AmbientIsotopy S) (W : Set S), Disjoint W Obstacle ∧ IsOpen W ∧ v ∈ W ∧ W ⊆ O ∧
            (∀ t z, z ∉ W → Q.map (t,z)=z) ∧
            (∀ t z, z ∈ (M.cover.branch : Set S) → Q.map (t,z)=z) ∧
            (∀ t z, z ∈ crossings M anchor (P.rep x.selected) → z ≠ v → Q.map (t,z)=z) ∧
            (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
              ∀ t z, z ∈ (P.rep w).val.image → Q.map (t,z)=z) ∧
            (∀ t z, Q.map (t,z) ∈ anchor.val.image ↔ z ∈ anchor.val.image) ∧
            (Q.finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image =
              ((H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) \ {v} := by
          obtain ⟨U,hU,hp,e,N₀,he,ha,hb,hN₀,hrN₀,hN₀U,hnode₀,hneighborN₀,hN₀Obstacle,hgerm₀⟩ := hAll v hv hvFirst
          let N := N₀ ∩ O
          have hN : IsOpen N := hN₀.inter hO
          have hrN : v ∈ N := ⟨hrN₀,hvO⟩
          have hNU : N ⊆ U := fun z hz => hN₀U hz.1
          have hnode : ∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) → z=v :=
            fun z hz hk => hnode₀ z hz.1 hk
          have hneighborN : ∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
              Disjoint N (P.rep w).val.image := fun w hn hs =>
            (hneighborN₀ w hn hs).mono_left inter_subset_left
          have hgerm : ∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
              z.val=v ∨ 0 < (e z).val.1 := fun z hz hn => hgerm₀ z hz hn.1
          let r := v
          have hrMark : r ∉ (M.cover.branch : Set S) := hv.2.1.2
          let B := {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}
          let o : B := ⟨(0,0),by simp⟩
          have hpo : e.symm o=⟨r,hp⟩ := by
            apply e.injective
            rw [e.apply_symm_apply]
            exact Subtype.ext he.symm
          have hOpen : IsOpen ((fun z : B => (e.symm z).val) ⁻¹' N) :=
            hN.preimage (continuous_subtype_val.comp e.symm.continuous)
          have hoN : o ∈ ((fun z : B => (e.symm z).val) ⁻¹' N) := by
            change (e.symm o).val ∈ N
            rw [hpo]
            exact hrN
          obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hOpen o hoN
          let δ := min ρ 1 / 2
          have hd : 0 < δ := by dsimp [δ]; positivity
          have hdρ : δ < ρ := by dsimp [δ]; have := min_le_left ρ (1:ℝ); linarith
          have hd1 : δ < 1 := by dsimp [δ]; have := min_le_right ρ (1:ℝ); linarith
          have smallN (z : U) (hx : |(e z).val.1| ≤ δ) (hy : |(e z).val.2| ≤ δ) : z.val ∈ N := by
            have hh : e z ∈ ball o ρ := by
              rw [Metric.mem_ball,Subtype.dist_eq]
              change dist (e z).val (0,0) < ρ
              rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero]
              exact (max_le hx hy).trans_lt hdρ
            have h := hball hh
            change (e.symm (e z)).val ∈ N at h
            simpa only [e.symm_apply_apply] using h
          obtain ⟨Q,qout,qlocal,qcoord,qclear⟩ := clearFamily U hU r hp e he δ hd hd1
          let Small : Set S := Subtype.val '' {z : U | |(e z).val.1| < δ ∧ |(e z).val.2| < δ}
          have hSmallN : Small ⊆ N := by
            rintro z ⟨u,hu,rfl⟩
            exact smallN u hu.1.le hu.2.le
          have hrSmall : r ∈ Small := by
            refine ⟨⟨r,hp⟩,?_,rfl⟩
            change |(e ⟨r,hp⟩).val.1| < δ ∧ |(e ⟨r,hp⟩).val.2| < δ
            rw [he]
            exact ⟨by simpa using hd,by simpa using hd⟩
          have qfix : ∀ t z, z ∉ Small → Q.map (t,z)=z := by
            intro t z hz
            by_cases hu : z ∈ U
            · apply qlocal t ⟨z,hu⟩
              have hn : ¬ (|(e ⟨z,hu⟩).val.1| < δ ∧ |(e ⟨z,hu⟩).val.2| < δ) :=
                fun h => hz ⟨⟨z,hu⟩,h,rfl⟩
              rcases not_and_or.mp hn with h | h
              · exact Or.inl (le_of_not_gt h)
              · exact Or.inr (le_of_not_gt h)
            · exact qout t z hu
          have hlocal : ∀ z : U, z.val ∈ H.finalMap '' (raw side).image →
              |(e z).val.1| < δ → |(e z).val.2| < δ → z.val=r ∨ 0 < (e z).val.1 :=
            fun z hz hx hy => hgerm z hz (smallN z hx.le hy.le)
          have qavoid : Disjoint ((Q.finalMap '' (H.finalMap '' (raw side).image)) ∩ Small)
              (P.rep x.selected).val.image := by
            apply disjoint_left.mpr
            rintro z ⟨hz,⟨u,hu,rfl⟩⟩ hzOld
            have hpos := qclear (H.finalMap '' (raw side).image) hlocal u hz hu.1 hu.2
            exact (ne_of_gt hpos) ((hb u).mp hzOld)
          have hSmall : IsOpen Small := hU.isOpenMap_subtype_val _
            ((isOpen_lt (continuous_fst.comp (continuous_subtype_val.comp e.continuous)).abs continuous_const).inter
              (isOpen_lt (continuous_snd.comp (continuous_subtype_val.comp e.continuous)).abs continuous_const))
          refine ⟨Q,Small,hN₀Obstacle.mono_left (fun z hz => (hSmallN hz).1),hSmall,hrSmall,(fun z hz => (hSmallN hz).2),qfix,?_,?_,?_,?_,?_⟩
          · intro t z hz
            exact qfix t z (fun h => hrMark (by
              have heq : z=r := hnode z (hSmallN h) (Or.inl hz)
              rw [←heq]
              exact hz))
          · intro t z hz hn
            exact qfix t z (fun h => hn (hnode z (hSmallN h) (Or.inr hz)))
          · intro w hn hs t z hz
            exact qfix t z (fun h => disjoint_left.mp (hneighborN w hn hs) (hSmallN h) hz)
          · intro t z
            by_cases hu : z ∈ U
            · obtain ⟨hqU,hsecond⟩ := qcoord t ⟨z,hu⟩
              rw [ha ⟨_,hqU⟩,ha ⟨z,hu⟩,hsecond]
            · rw [qout t z hu]
          · ext z
            constructor
            · rintro ⟨hz,hzOld⟩
              have hzSmall : z ∉ Small := fun h => disjoint_left.mp qavoid ⟨hz,h⟩ hzOld
              obtain ⟨w,hw,hwz⟩ := hz
              have hqz : Q.finalMap z=z := qfix 1 z hzSmall
              obtain ⟨q,hq⟩ := Q.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
              have hqFinal (u : S) : q u=Q.finalMap u := hq u
              have hwEq : w=z := q.injective (by rw [hqFinal,hqFinal]; exact hwz.trans hqz.symm)
              subst w
              refine ⟨⟨hw,hzOld⟩,?_⟩
              intro hzR
              exact hzSmall ((mem_singleton_iff.mp hzR).symm ▸ hrSmall)
            · rintro ⟨⟨hzImage,hzOld⟩,hn⟩
              have hzSmall : z ∉ Small := by
                intro h
                have hzGraph : z ∈ (H.finalMap '' (raw side).image) ∩
                    (anchor.val.image ∪ (P.rep x.selected).val.image) := ⟨hzImage,Or.inr hzOld⟩
                rw [hgraph] at hzGraph
                exact hn (mem_singleton_iff.mpr (hnode z (hSmallN h) hzGraph.1.2))
              exact ⟨⟨z,hzImage,qfix 1 z hzSmall⟩,hzOld⟩
      let R := ((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}
      have hR : R.Finite := (P.finite x.selected).subset (fun z hz => hz.1.2)
      obtain ⟨O,hO,hOdis⟩ := (P.finite x.selected).t2_separation
      choose Q W hWObstacle hW hpW hWO hqout hqmarks hqnodes hqneighbors hqanchor hqimage using
        fun p : R => clearNode p.val p.property.1
          (fun h => p.property.2 (mem_singleton_iff.mpr h)) (O p.val) (hO p.val).2 (hO p.val).1
      let r := anchor.val.map x.t
      have hrMark : r ∉ (M.cover.branch : Set S) := by
        intro h
        rcases anchor.val.marked_only_at_ends x.t h with h | h
        · exact (ne_of_gt x.t_interior.1) (congrArg Subtype.val h)
        · exact (ne_of_lt x.t_interior.2) (congrArg Subtype.val h)
      have hrC : r ∈ crossings M anchor (P.rep x.selected) :=
        ⟨⟨mem_range_self _,hrMark⟩,⟨⟨x.s,x.same_point.symm⟩,hrMark⟩⟩
      let N := Nf ∩ O r
      refine ⟨H,Uf,hUf,hpf,ef,N,Q,W,hfix,hneighbors,hgraph,hef,haf,hbf,
        hNf.inter (hO r).2,⟨hrNf,(hO r).1⟩,(fun z hz => hNfUf hz.1),
        (fun z hz hk => hnodef z hz.1 hk),
        (fun w hn hs => (hneighborNf w hn hs).mono_left inter_subset_left),
        hHObstacle,hNfObstacle.mono_left inter_subset_left,
        (fun z hz hn => hgermf z hz hn.1),?_,?_,?_,hWObstacle⟩
      · intro p
        exact ⟨hW p,hpW p,hqout p,hqmarks p,hqnodes p,hqneighbors p,hqanchor p,hqimage p⟩
      · intro p q hn
        exact (hOdis p.property.1.2 q.property.1.2 (fun h => hn (Subtype.ext h))).mono (hWO p) (hWO q)
      · intro p
        have hne : r ≠ p.val := fun h => p.property.2 (mem_singleton_iff.mpr h.symm)
        exact (hOdis hrC p.property.1.2 hne).mono (fun z hz => hz.2) (hWO p)
    let R := ((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}
    obtain ⟨H,U,hU,hp,e,N,Q,W,hfix,hneighbors,hgraph,he,ha,hb,hN,hpN,hNU,hnode,hneighborN,hHObstacle,hNObstacle,hgerm,hQ,hdis,hNW,hWObstacle⟩ := family M anchor F P x raw hraw side Obstacle hObstacle hrawObstacle hrObstacle
    have hR : R.Finite := (P.finite x.selected).subset (fun z hz => hz.1.2)
    letI : Fintype R := hR.fintype
    obtain ⟨J,houtside,hinside⟩ := finite_supported_patch_assembly W hdis Q (fun p => (hQ p).2.2.1)
    have qpres (p : R) (t : Interval) (z : S) (hz : z ∈ W p) : (Q p).map (t,z) ∈ W p := by
      obtain ⟨f,hf⟩ := (Q p).homeomorphism_at t
      by_contra hn
      have he : f ((Q p).map (t,z))=f z := by
        rw [hf,(hQ p).2.2.1 t _ hn,hf]
      exact hn ((f.injective he).symm ▸ hz)
    have jfix (t : Interval) (z : S) (h : ∀ p : R, (Q p).map (t,z)=z) : J.map (t,z)=z := by
      by_cases hz : z ∈ ⋃ p, W p
      · obtain ⟨p,hp⟩ := mem_iUnion.mp hz
        exact (hinside p t z hp).trans (h p)
      · exact houtside t z hz
    have jN (t : Interval) (z : S) (hz : z ∈ N) : J.map (t,z)=z := by
      apply jfix t z
      intro p
      exact (hQ p).2.2.1 t z (fun h => disjoint_left.mp (hNW p) hz h)
    refine ⟨H,U,hU,hp,e,N,J,hfix,hneighbors,hgraph,he,ha,hb,hN,hpN,hNU,hnode,
      hneighborN,hHObstacle,hNObstacle,hgerm,jN,?_,?_,?_,?_,?_,?_⟩
    · intro t z hz
      exact jfix t z (fun p => (hQ p).2.2.2.1 t z hz)
    · intro w hn hs t z hz
      exact jfix t z (fun p => (hQ p).2.2.2.2.2.1 w hn hs t z hz)
    · intro t z
      by_cases hz : z ∈ ⋃ p, W p
      · obtain ⟨p,hp⟩ := mem_iUnion.mp hz
        rw [hinside p t z hp]
        exact (hQ p).2.2.2.2.2.2.1 t z
      · rw [houtside t z hz]
    · intro z hz hn
      obtain ⟨v,hv,hvz⟩ := hz
      obtain ⟨f,hf⟩ := J.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
      have hvEq : v=z.val := f.injective (by rw [hf,hf]; exact hvz.trans (jN 1 z.val hn).symm)
      exact hgerm z (hvEq ▸ hv) hn
    · ext z
      constructor
      · rintro ⟨⟨w,hw,hwz⟩,hzOld⟩
        by_cases hwW : w ∈ ⋃ p, W p
        · obtain ⟨p,hp⟩ := mem_iUnion.mp hwW
          have hQw : (Q p).finalMap w=z := (hinside p 1 w hp).symm.trans hwz
          have hzQ : z ∈ (Q p).finalMap '' (H.finalMap '' (raw side).image) ∩
              (P.rep x.selected).val.image := ⟨⟨w,hw,hQw⟩,hzOld⟩
          rw [(hQ p).2.2.2.2.2.2.2] at hzQ
          refine ⟨hzQ.1,?_⟩
          intro hzR
          let q : R := ⟨z,hzR⟩
          have hzP : z ∈ W p := hQw ▸ qpres p 1 w hp
          have hpq : p=q := by
            by_contra hn
            exact disjoint_left.mp (hdis p q hn) hzP (hQ q).2.1
          exact hzQ.2 (mem_singleton_iff.mpr (congrArg Subtype.val hpq).symm)
        · have hwEq : w=z := (houtside 1 w hwW).symm.trans hwz
          refine ⟨⟨hwEq ▸ hw,hzOld⟩,?_⟩
          intro hzR
          let p : R := ⟨z,hzR⟩
          exact hwW (hwEq.symm ▸ mem_iUnion.mpr ⟨p,(hQ p).2.1⟩)
      · rintro ⟨⟨hzImage,hzOld⟩,hzNotR⟩
        have hzGraph : z ∈ H.finalMap '' (raw side).image ∩
            (anchor.val.image ∪ (P.rep x.selected).val.image) := ⟨hzImage,Or.inr hzOld⟩
        rw [hgraph] at hzGraph
        have hzFix : J.finalMap z=z := by
          apply jfix 1 z
          intro p
          rcases hzGraph.1.2 with hm | hc
          · exact (hQ p).2.2.2.1 1 z hm
          · exact (hQ p).2.2.2.2.1 1 z hc (fun h => hzNotR (h.symm ▸ p.property))
        exact ⟨⟨z,hzImage,hzFix⟩,hzOld⟩
    · intro t z hz
      apply jfix t z
      intro p
      exact (hQ p).2.2.1 t z (fun h => disjoint_left.mp (hWObstacle p) h hz)
  have clearFamily {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
  (U : Set S) (hU : IsOpen U) (p : S) (hp : p ∈ U)
  (e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1})
  (he : (e ⟨p,hp⟩).val=(0,0))
  (δ : ℝ) (hd : 0 < δ) (hd1 : δ < 1) :
  ∃ H : AmbientIsotopy S,
    (∀ t z, z ∉ U → H.map (t,z)=z) ∧
    (∀ t (z : U), δ ≤ |(e z).val.1| ∨ δ ≤ |(e z).val.2| → H.map (t,z.val)=z.val) ∧
    ∀ A : Set S,
      (∀ z : U, z.val ∈ A → |(e z).val.1| < δ → |(e z).val.2| < δ →
        z.val=p ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) →
      ∀ z : U, z.val ∈ H.finalMap '' A → |(e z).val.1| < δ → |(e z).val.2| < δ →
        (e z).val.1 < 0 ∧ 0 < (e z).val.2 := by
    classical
    have quadrant : ∃ H : AmbientIsotopy (ℝ × ℝ),
    (∀ t z, 1 ≤ |z.1| ∨ 1 ≤ |z.2| → H.map (t,z)=z) ∧
    (H.finalMap (0,0)).1 < 0 ∧ 0 < (H.finalMap (0,0)).2 ∧
    ∀ t z, z.1 < 0 → 0 < z.2 →
      (H.map (t,z)).1 < 0 ∧ 0 < (H.map (t,z)).2 := by
      let a : Amount := ⟨-(1/4:ℝ),by norm_num⟩
      let b : Amount := ⟨(1/4:ℝ),by norm_num⟩
      let swap : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.prodComm ℝ ℝ
      let V : AmbientIsotopy (ℝ × ℝ) := {
        map := ⟨fun z => swap ((productIsotopy b).map (z.1,swap z.2)),by
          exact swap.continuous.comp ((productIsotopy b).map.continuous.comp
            (continuous_fst.prodMk (swap.continuous.comp continuous_snd)))⟩
        homeomorphism_at := by
          intro t
          exact ⟨(swap.trans (productSlide (timeAmount b t))).trans swap,fun _ => rfl⟩
        at_zero := by intro z; change swap ((productIsotopy b).map (0,swap z))=z
                      simp [productIsotopy,productSlide,timeAmount,rowAmount,scalar,swap] }
      let H : AmbientIsotopy (ℝ × ℝ) := {
        map := ⟨fun z => V.map (z.1,(productIsotopy a).map z),by
          exact V.map.continuous.comp (continuous_fst.prodMk (productIsotopy a).map.continuous)⟩
        homeomorphism_at := by
          intro t
          obtain ⟨v,hv⟩ := V.homeomorphism_at t
          exact ⟨(productSlide (timeAmount a t)).trans v,fun z => hv _⟩
        at_zero := by intro z; change V.map (0,(productIsotopy a).map (0,z))=z
                      simp [V,productIsotopy,productSlide,timeAmount,rowAmount,scalar,swap] }
      have hleft (t : Interval) (z : ℝ × ℝ) :
          ((productIsotopy a).map (t,z)).1 ≤ z.1 := by
        change z.1 + (t.val * (-(1/4:ℝ)) * tent z.2) * tent z.1 ≤ z.1
        have ht := t.property.1
        have h1 := tent_nonneg z.1
        have h2 := tent_nonneg z.2
        nlinarith [mul_nonneg ht h2,mul_nonneg (mul_nonneg ht h2) h1]
      have hup (t : Interval) (z : ℝ × ℝ) : z.2 ≤ (V.map (t,z)).2 := by
        change z.2 ≤ z.2 + (t.val * (1/4:ℝ) * tent z.1) * tent z.2
        have ht := t.property.1
        have h1 := tent_nonneg z.1
        have h2 := tent_nonneg z.2
        exact le_add_of_nonneg_right (by positivity)
      refine ⟨H,?_,?_,?_,?_⟩
      · intro t z hz
        change V.map (t,(productIsotopy a).map (t,z))=z
        rw [productIsotopy_fixed a t z hz]
        change swap ((productIsotopy b).map (t,swap z))=z
        rw [productIsotopy_fixed b t (swap z) (by exact hz.symm)]
        rfl
      · change scalar (rowAmount (timeAmount a 1) 0).val 0 < 0
        norm_num [scalar,rowAmount,timeAmount,a,tent]
      · change 0 < scalar (rowAmount (timeAmount b 1)
            (scalar (rowAmount (timeAmount a 1) 0).val 0)).val 0
        norm_num [scalar,rowAmount,timeAmount,a,b,tent]
      · intro t z hx hy
        constructor
        · exact (hleft t z).trans_lt hx
        · exact hy.trans_le (hup t ((productIsotopy a).map (t,z)))
    let Q := {q : ℝ × ℝ | |q.1| < 1 ∧ |q.2| < 1}
    let g : (ℝ × ℝ) ≃ₜ Plane := {
      toEquiv := {
        toFun := fun z => Plane.mk (z.1/δ) (z.2/δ)
        invFun := fun z => (δ*z 0,δ*z 1)
        left_inv := by intro z; apply Prod.ext <;> simp [Plane.mk] <;> field_simp [ne_of_gt hd]
        right_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk,ne_of_gt hd] }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let V : Set Plane := g '' Q
    let ee : U ≃ₜ V := e.trans (g.image Q)
    have hCV : Plane.closedSquare 0 1 ⊆ V := by
      intro z hz
      have hcoords := max_le_iff.mp (mem_closedSquare_zero_one.mp hz)
      refine ⟨g.symm z,?_,g.apply_symm_apply z⟩
      change |δ*z 0| < 1 ∧ |δ*z 1| < 1
      rw [abs_mul,abs_mul,abs_of_pos hd]
      constructor
      · exact (mul_le_of_le_one_right hd.le hcoords.1).trans_lt hd1
      · exact (mul_le_of_le_one_right hd.le hcoords.2).trans_lt hd1
    obtain ⟨R,rfix,r0x,r0y,rquad⟩ := quadrant
    let pc := planeCoordinates
    let K : AmbientIsotopy Plane := {
      map := ⟨fun z => pc.symm (R.map (z.1,pc z.2)),by
        exact pc.symm.continuous.comp (R.map.continuous.comp
          (continuous_fst.prodMk (pc.continuous.comp continuous_snd)))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨r,hr⟩ := R.homeomorphism_at t
        exact ⟨(pc.trans r).trans pc.symm,fun z => congrArg pc.symm (hr (pc z))⟩
      at_zero := by
        intro z
        change pc.symm (R.map (⟨0,by norm_num⟩,pc z))=z
        rw [R.at_zero,pc.symm_apply_apply] }
    have kcoord (t : Interval) (z : Plane) : pc (K.map (t,z))=R.map (t,pc z) :=
      pc.apply_symm_apply _
    have kfix (t : Interval) (z : Plane) (hz : z ∉ Plane.openSquare 0 1) :
        K.map (t,z)=z := by
      apply pc.injective
      rw [kcoord]
      apply rfix
      change 1 ≤ |z 0| ∨ 1 ≤ |z 1|
      have hn : ¬ (|z 0| < 1 ∧ |z 1| < 1) := by
        intro hh
        exact hz (mem_openSquare_zero_one.mpr (max_lt hh.1 hh.2))
      rcases not_and_or.mp hn with h | h
      · exact Or.inl (le_of_not_gt h)
      · exact Or.inr (le_of_not_gt h)
    obtain ⟨KU,H,hcoords,hlift,houtside⟩ := position_surface_chart_lift S U V hU ee
      (Plane.closedSquare 0 1) (isCompact_closedSquare 0 1) hCV K
      (fun t z hz => kfix t z (fun hh => hz
        (mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hh).le)))
    have coord (t : Interval) (z : U) :
        g (e ⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩).val =
          K.map (t,g (e z).val) := by
      have hs : (⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩ : U) =
          KU.map (t,z) := Subtype.ext (hlift t z)
      rw [hs]
      exact hcoords t z
    have localFix : ∀ t (z : U), δ ≤ |(e z).val.1| ∨ δ ≤ |(e z).val.2| →
        H.map (t,z.val)=z.val := by
      intro t z hz
      have hne : g (e z).val ∉ Plane.openSquare 0 1 := by
        intro hh
        have hcc := max_lt_iff.mp (mem_openSquare_zero_one.mp hh)
        have hx : |(e z).val.1| / δ < 1 := by
          simpa [g,Plane.mk,abs_div,abs_of_pos hd] using hcc.1
        have hy : |(e z).val.2| / δ < 1 := by
          simpa [g,Plane.mk,abs_div,abs_of_pos hd] using hcc.2
        have hx := (div_lt_iff₀ hd).mp hx
        have hy := (div_lt_iff₀ hd).mp hy
        rcases hz with hz | hz <;> linarith
      have hh := coord t z
      rw [kfix t _ hne] at hh
      exact congrArg Subtype.val (e.injective (Subtype.ext (g.injective hh)))
    refine ⟨H,houtside,localFix,?_⟩
    intro A hA z hz hx hy
    obtain ⟨w,hw,hwz⟩ := hz
    have hwU : w ∈ U := by
      by_contra hn
      have hf := houtside 1 w hn
      change H.finalMap w=w at hf
      exact hn ((hf.symm.trans hwz).symm ▸ z.property)
    let wu : U := ⟨w,hwU⟩
    have hwx : |(e wu).val.1| < δ := by
      by_contra hn
      have hf := localFix 1 wu (Or.inl (le_of_not_gt hn))
      change H.finalMap w=w at hf
      have huw : wu=z := Subtype.ext (hf.symm.trans hwz)
      exact hn (huw.symm ▸ hx)
    have hwy : |(e wu).val.2| < δ := by
      by_contra hn
      have hf := localFix 1 wu (Or.inr (le_of_not_gt hn))
      change H.finalMap w=w at hf
      have huw : wu=z := Subtype.ext (hf.symm.trans hwz)
      exact hn (huw.symm ▸ hy)
    have hc := congrArg pc (coord 1 wu)
    have hez : (⟨H.map (1,wu.val),by rw [hlift]; exact (KU.map (1,wu)).property⟩ : U)=z :=
      Subtype.ext hwz
    rw [hez,kcoord] at hc
    have coords (v : U) : pc (g (e v).val) = ((e v).val.1/δ,(e v).val.2/δ) := rfl
    rw [coords,coords] at hc
    have hnw : (R.finalMap ((e wu).val.1/δ,(e wu).val.2/δ)).1 < 0 ∧
        0 < (R.finalMap ((e wu).val.1/δ,(e wu).val.2/δ)).2 := by
      rcases hA wu hw hwx hwy with hpw | ⟨hxl,hyp⟩
      · have hwp : wu=⟨p,hp⟩ := Subtype.ext hpw
        rw [hwp,he]
        simpa using And.intro r0x r0y
      · exact rquad 1 _ (div_neg_of_neg_of_pos hxl hd) (div_pos hyp hd)
    change ((e z).val.1/δ,(e z).val.2/δ)=R.finalMap _ at hc
    rw [←hc] at hnw
    constructor
    · simpa using (div_lt_iff₀ hd).mp hnw.1
    · simpa using (lt_div_iff₀ hd).mp hnw.2
  let R := ((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}
  obtain ⟨H,U,hU,hp,e,N,J,hfix,hneighbors,hgraph,he,ha,hb,hN,hrN,hNU,hnode,hneighborN,hHObstacle,hNObstacle,hgerm,jN,jmarks,jneighbors,janchor,jgerm,jimage,jObstacle⟩ :=
    family M anchor F P x raw hraw side Obstacle hObstacle hrawObstacle hrObstacle
  let r := anchor.val.map x.t
  have hrMark : r ∉ (M.cover.branch : Set S) := by
    intro h
    rcases anchor.val.marked_only_at_ends x.t h with h | h
    · exact (ne_of_gt x.t_interior.1) (congrArg Subtype.val h)
    · exact (ne_of_lt x.t_interior.2) (congrArg Subtype.val h)
  let B := {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}
  let o : B := ⟨(0,0),by simp⟩
  have hpo : e.symm o=⟨r,hp⟩ := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext he.symm
  have hOpen : IsOpen ((fun z : B => (e.symm z).val) ⁻¹' N) :=
    hN.preimage (continuous_subtype_val.comp e.symm.continuous)
  have hoN : o ∈ ((fun z : B => (e.symm z).val) ⁻¹' N) := by
    change (e.symm o).val ∈ N
    rw [hpo]
    exact hrN
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hOpen o hoN
  let δ := min ρ 1 / 2
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hdρ : δ < ρ := by dsimp [δ]; have := min_le_left ρ (1:ℝ); linarith
  have hd1 : δ < 1 := by dsimp [δ]; have := min_le_right ρ (1:ℝ); linarith
  have smallN (z : U) (hx : |(e z).val.1| ≤ δ) (hy : |(e z).val.2| ≤ δ) : z.val ∈ N := by
    have hh : e z ∈ ball o ρ := by
      rw [Metric.mem_ball,Subtype.dist_eq]
      change dist (e z).val (0,0) < ρ
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero]
      exact (max_le hx hy).trans_lt hdρ
    have h := hball hh
    change (e.symm (e z)).val ∈ N at h
    simpa only [e.symm_apply_apply] using h
  obtain ⟨Q,qout,qlocal,qclear⟩ := clearFamily U hU r hp e he δ hd hd1
  let Small : Set S := Subtype.val '' {z : U | |(e z).val.1| < δ ∧ |(e z).val.2| < δ}
  have hSmallN : Small ⊆ N := by
    rintro z ⟨u,hu,rfl⟩
    exact smallN u hu.1.le hu.2.le
  have hrSmall : r ∈ Small := by
    refine ⟨⟨r,hp⟩,?_,rfl⟩
    change |(e ⟨r,hp⟩).val.1| < δ ∧ |(e ⟨r,hp⟩).val.2| < δ
    rw [he]
    exact ⟨by simpa using hd,by simpa using hd⟩
  have qfix : ∀ t z, z ∉ Small → Q.map (t,z)=z := by
    intro t z hz
    by_cases hu : z ∈ U
    · apply qlocal t ⟨z,hu⟩
      have hn : ¬ (|(e ⟨z,hu⟩).val.1| < δ ∧ |(e ⟨z,hu⟩).val.2| < δ) :=
        fun h => hz ⟨⟨z,hu⟩,h,rfl⟩
      rcases not_and_or.mp hn with h | h
      · exact Or.inl (le_of_not_gt h)
      · exact Or.inr (le_of_not_gt h)
    · exact qout t z hu
  have hlocal : ∀ z : U, z.val ∈ J.finalMap '' (H.finalMap '' (raw side).image) →
      |(e z).val.1| < δ → |(e z).val.2| < δ →
      z.val=r ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2) :=
    fun z hz hx hy => jgerm z hz (smallN z hx.le hy.le)
  have qavoid : Disjoint ((Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ Small)
      (anchor.val.image ∪ (P.rep x.selected).val.image) := by
    apply disjoint_left.mpr
    rintro z ⟨hz,⟨u,hu,rfl⟩⟩ hzgraph
    have hnw := qclear (J.finalMap '' (H.finalMap '' (raw side).image)) hlocal u hz hu.1 hu.2
    rcases hzgraph with hzA | hzO
    · exact (ne_of_gt hnw.2) ((ha u).mp hzA)
    · exact (ne_of_lt hnw.1) ((hb u).mp hzO)
  have qAnchor :
      (Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ anchor.val.image =
        ((J.finalMap '' (H.finalMap '' (raw side).image)) ∩ anchor.val.image) \ {r} := by
    ext z
    constructor
    · rintro ⟨⟨w,hw,hwz⟩,hzAnchor⟩
      have hzSmall : z ∉ Small := fun h => disjoint_left.mp qavoid ⟨⟨w,hw,hwz⟩,h⟩ (Or.inl hzAnchor)
      obtain ⟨q,hq⟩ := Q.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
      have hwEq : w=z := q.injective (by rw [hq,hq]; exact hwz.trans (qfix 1 z hzSmall).symm)
      subst w
      exact ⟨⟨hw,hzAnchor⟩,fun h => hzSmall ((mem_singleton_iff.mp h).symm ▸ hrSmall)⟩
    · rintro ⟨⟨hzImage,hzAnchor⟩,hn⟩
      have hzSmall : z ∉ Small := by
        intro h
        obtain ⟨w,hw,hwz⟩ := hzImage
        obtain ⟨j,hj⟩ := J.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
        have hwEq : w=z := j.injective (by rw [hj,hj]; exact hwz.trans (jN 1 z (hSmallN h)).symm)
        have hzH : z ∈ H.finalMap '' (raw side).image := hwEq ▸ hw
        have hzGraph : z ∈ H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) :=
          ⟨hzH,Or.inl hzAnchor⟩
        rw [hgraph] at hzGraph
        exact hn (mem_singleton_iff.mpr (hnode z (hSmallN h) hzGraph.1.2))
      exact ⟨⟨z,hzImage,qfix 1 z hzSmall⟩,hzAnchor⟩
  refine ⟨H,J,Q,?_,?_,?_,?_,janchor,qAnchor,?_,?_,?_⟩
  · intro t z hz
    refine ⟨hfix t z (Or.inl hz),jmarks t z hz,qfix t z ?_⟩
    intro h
    have heq : z=r := hnode z (hSmallN h) (Or.inl hz)
    exact hrMark (heq ▸ hz)
  · intro w hn hs t z hz
    exact ⟨hneighbors w hn hs t z hz,jneighbors w hn hs t z hz,
      qfix t z (fun h => disjoint_left.mp (hneighborN w hn hs) (hSmallN h) hz)⟩
  · intro t z hz
    exact ⟨hHObstacle t z hz,jObstacle t z hz,
      qfix t z (fun h => disjoint_left.mp hNObstacle (hSmallN h) hz)⟩
  · have hqdelete :
        (Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ (P.rep x.selected).val.image =
        ((J.finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image) \ {r} := by
      ext z
      constructor
      · rintro ⟨⟨w,hw,hwz⟩,hzOld⟩
        have hzSmall : z ∉ Small := fun h => disjoint_left.mp qavoid ⟨⟨w,hw,hwz⟩,h⟩ (Or.inr hzOld)
        obtain ⟨q,hq⟩ := Q.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
        have hwEq : w=z := q.injective (by rw [hq,hq]; exact hwz.trans (qfix 1 z hzSmall).symm)
        subst w
        exact ⟨⟨hw,hzOld⟩,fun h => hzSmall ((mem_singleton_iff.mp h).symm ▸ hrSmall)⟩
      · rintro ⟨⟨hzImage,hzOld⟩,hn⟩
        have hzOriginal : z ∈ H.finalMap '' (raw side).image := by
          have hh : z ∈ (J.finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image := ⟨hzImage,hzOld⟩
          rw [jimage] at hh
          exact hh.1.1
        have hzGraph : z ∈ H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) :=
          ⟨hzOriginal,Or.inr hzOld⟩
        rw [hgraph] at hzGraph
        have hzSmall : z ∉ Small := fun h => hn (mem_singleton_iff.mpr (hnode z (hSmallN h) hzGraph.1.2))
        exact ⟨⟨z,hzImage,qfix 1 z hzSmall⟩,hzOld⟩
    rw [hqdelete,jimage]
    have hrRaw : r ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected) := by
      have ht : (x.t : Interval) ∈ Set.Icc (0 : Interval) x.t := ⟨by exact x.t.property.1,le_rfl⟩
      have hrImage : r ∈ (raw side).image := by
        rw [hraw side]
        exact Or.inl ⟨x.t,show x.t.val ≤ x.t.val from le_rfl,rfl⟩
      exact ⟨hrImage,⟨⟨mem_range_self _,hrMark⟩,⟨⟨x.s,x.same_point.symm⟩,hrMark⟩⟩⟩
    ext z
    change (((z ∈ (H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) ∧
      ¬ (z ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected) ∧ z ≠ r)) ∧ z ≠ r) ↔
      ((z ∈ (H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) ∧
        ¬ z ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected))
    by_cases hz : z=r
    · subst z; tauto
    · tauto
  · obtain ⟨j,hj⟩ := J.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have jinj : Function.Injective J.finalMap := by
      intro u v h
      exact j.injective (by rw [hj,hj]; exact h)
    have jMarked (z : S) : J.finalMap z ∈ (M.cover.branch : Set S) ↔ z ∈ (M.cover.branch : Set S) := by
      constructor
      · intro h
        have hfixz := jmarks 1 (J.finalMap z) h
        have he : z=J.finalMap z := (jinj hfixz).symm
        exact he.symm ▸ h
      · intro h
        have he : J.finalMap z=z := jmarks 1 z h
        exact he.symm ▸ h
    have hJcontacts :
        ((J.finalMap '' (H.finalMap '' (raw side).image)) ∩ anchor.val.image) \ (M.cover.branch : Set S) =
        J.finalMap '' (((H.finalMap '' (raw side).image) ∩ anchor.val.image) \ (M.cover.branch : Set S)) := by
      ext z
      constructor
      · rintro ⟨⟨⟨w,hw,hwz⟩,hzA⟩,hzM⟩
        refine ⟨w,⟨⟨hw,?_⟩,?_⟩,hwz⟩
        · have hwA : J.finalMap w ∈ anchor.val.image := hwz.symm ▸ hzA
          exact (janchor 1 w).mp hwA
        · intro hm
          exact hzM (hwz ▸ (jMarked w).mpr hm)
      · rintro ⟨w,⟨⟨hw,hwA⟩,hwM⟩,rfl⟩
        exact ⟨⟨⟨w,hw,rfl⟩,(janchor 1 w).mpr hwA⟩,fun hm => hwM ((jMarked w).mp hm)⟩
    have hHcontacts :
        ((H.finalMap '' (raw side).image) ∩ anchor.val.image) \ (M.cover.branch : Set S) =
        (raw side).image ∩ crossings M anchor (P.rep x.selected) := by
      ext z
      constructor
      · rintro ⟨⟨hzH,hzA⟩,hzM⟩
        have h : z ∈ H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) := ⟨hzH,Or.inl hzA⟩
        rw [hgraph] at h
        exact ⟨h.1.1,h.1.2.resolve_left hzM⟩
      · rintro ⟨hzRaw,hzC⟩
        have h : z ∈ (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ∩
            (anchor.val.image ∪ (P.rep x.selected).val.image) := ⟨⟨hzRaw,Or.inr hzC⟩,Or.inl hzC.1.1⟩
        rw [←hgraph] at h
        exact ⟨⟨h.1,hzC.1.1⟩,hzC.1.2⟩
    rw [qAnchor]
    have hcomm (A : Set S) : (A \ {r}) \ (M.cover.branch : Set S) = (A \ (M.cover.branch : Set S)) \ {r} := by
      ext z; simp only [mem_diff]; tauto
    rw [hcomm,hJcontacts,hHcontacts]
    have jr : J.finalMap r=r := jN 1 r hrN
    have hd (A : Set S) : J.finalMap '' (A \ {r}) = (J.finalMap '' A) \ {r} := by
      rw [Set.image_sdiff jinj,Set.image_singleton,jr]
    rw [←hd]
    refine ⟨Set.ncard_image_of_injective _ jinj,?_⟩
    exact ((P.finite x.selected).subset (fun z hz => hz.1.2)).image J.finalMap
  · apply disjoint_left.mpr
    rintro z ⟨hzCandidate,hzUnmarked⟩ hzOld
    have hzSmall : z ∉ Small := fun h => disjoint_left.mp qavoid ⟨hzCandidate,h⟩ (Or.inr hzOld.1)
    obtain ⟨v,hv,hvz⟩ := hzCandidate
    obtain ⟨q,hq⟩ := Q.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have hvEq : v=z := q.injective (by rw [hq,hq]; exact hvz.trans (qfix 1 z hzSmall).symm)
    have hzBefore : z ∈ (J.finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image :=
      ⟨hvEq ▸ hv,hzOld.1⟩
    rw [jimage] at hzBefore
    have hzGraph : z ∈ H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) :=
      ⟨hzBefore.1.1,Or.inr hzOld.1⟩
    rw [hgraph] at hzGraph
    have hzC := hzGraph.1.2.resolve_left hzUnmarked
    apply hzBefore.2
    refine ⟨⟨hzGraph.1.1,hzC⟩,?_⟩
    intro h
    exact hzSmall ((mem_singleton_iff.mp h).symm ▸ hrSmall)
  ·
    have incident : ∀ (side : Bool) (v : {v // v ∈ F}) (hne : v ≠ x.selected)
      (hsimplex : IsArcSimplex M {v.val, x.selected.val}),
      Disjoint ((raw side).image \ (M.cover.branch : Set S)) (arcInterior M (P.rep v)) := by
      intro side v hne hsimplex
      apply Set.disjoint_left.mpr
      rintro p ⟨hp, hpm⟩ hpv
      rw [hraw] at hp
      rcases hp with ⟨r, hr, he⟩ | ⟨r, hr, he⟩
      · by_cases hzero : r.val = 0
        · apply hpm
          rw [← he]
          have hz : r = (0 : Interval) := Subtype.ext hzero
          exact hz ▸ anchor.val.start_marked
        have hrpos : 0 < r.val := lt_of_le_of_ne r.property.1 (Ne.symm hzero)
        by_cases ht : r.val = x.t.val
        · have heq : r = x.t := Subtype.ext ht
          have hanchor : p ∈ arcInterior M anchor := ⟨⟨r, he⟩, hpm⟩
          have hold : p ∈ arcInterior M (P.rep x.selected) := by
            refine ⟨⟨x.s, ?_⟩, hpm⟩
            exact x.same_point.symm.trans (congrArg anchor.val.map heq.symm |>.trans he)
          exact Set.disjoint_left.mp (P.distinct_crossings x.selected v hne.symm)
            ⟨hanchor, hold⟩ ⟨hanchor, hpv⟩
        · have hrlt : r.val < x.t.val := lt_of_le_of_ne hr ht
          exact x.first v r hrpos hrlt (he.symm ▸ hpv)
      · have hold : p ∈ arcInterior M (P.rep x.selected) := ⟨⟨r, he⟩, hpm⟩
        exact Set.disjoint_left.mp (P.simplex_disjoint v x.selected hne hsimplex) hpv hold
    intro w hn hs
    apply disjoint_left.mpr
    rintro z ⟨hzCandidate,hzUnmarked⟩ hzNeighbor
    have hzSmall : z ∉ Small := fun h => disjoint_left.mp (hneighborN w hn hs) (hSmallN h) hzNeighbor.1
    obtain ⟨v,hv,hvz⟩ := hzCandidate
    obtain ⟨q,hq⟩ := Q.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have hvEq : v=z := q.injective (by rw [hq,hq]; exact hvz.trans (qfix 1 z hzSmall).symm)
    obtain ⟨u,hu,huz⟩ := (hvEq ▸ hv : z ∈ J.finalMap '' (H.finalMap '' (raw side).image))
    obtain ⟨j,hj⟩ := J.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have huEq : u=z := j.injective (by rw [hj,hj]; exact huz.trans (jneighbors w hn hs 1 z hzNeighbor.1).symm)
    obtain ⟨v,hv,hvz⟩ := (huEq ▸ hu : z ∈ H.finalMap '' (raw side).image)
    obtain ⟨h,hh⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have hvEq : v=z := h.injective (by rw [hh,hh]; exact hvz.trans (hneighbors w hn hs 1 z hzNeighbor.1).symm)
    exact disjoint_left.mp (incident side w hn hs) ⟨hvEq ▸ hv,hzUnmarked⟩ hzNeighbor

private theorem actualSourceSurgery_firstBranch_14 (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
    (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
    (side : Bool) :
    ∃ (H J Q : AmbientIsotopy S),
      (∀ t z, z ∈ (M.cover.branch : Set S) → H.map (t,z)=z ∧ J.map (t,z)=z ∧ Q.map (t,z)=z) ∧
      (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
        ∀ t z, z ∈ (P.rep w).val.image → H.map (t,z)=z ∧ J.map (t,z)=z ∧ Q.map (t,z)=z) ∧
      (Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ (P.rep x.selected).val.image =
        ((H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) \ 
          ((raw side).image ∩ crossings M anchor (P.rep x.selected)) ∧
      (∀ t z, J.map (t,z) ∈ anchor.val.image ↔ z ∈ anchor.val.image) ∧
      (Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ anchor.val.image =
        ((J.finalMap '' (H.finalMap '' (raw side).image)) ∩ anchor.val.image) \ {anchor.val.map x.t} ∧
      ((((Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ anchor.val.image) \ (M.cover.branch : Set S)).ncard =
        (((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}).ncard ∧
        (((Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ anchor.val.image) \ (M.cover.branch : Set S)).Finite) ∧
      (∀ t z, z ∈ (raw (!side)).image → J.map (t,z)=z) ∧
      Disjoint ((Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) \ (M.cover.branch : Set S))
        ((raw (!side)).image \ (M.cover.branch : Set S)) ∧
      Disjoint ((Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) \ (M.cover.branch : Set S))
        (arcInterior M (P.rep x.selected)) ∧
      (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
        Disjoint ((Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) \ (M.cover.branch : Set S))
          (arcInterior M (P.rep w))) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  have family (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
      (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
      (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
      (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
      (side : Bool) :
      let R := ((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}
      ∃ (H : AmbientIsotopy S) (U : Set S) (hU : IsOpen U) (hp : anchor.val.map x.t ∈ U),
        ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
        ∃ N : Set S, ∃ (J : AmbientIsotopy S),
          (∀ t z, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
            H.map (t,z)=z) ∧
          (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
            ∀ t z, z ∈ (P.rep v).val.image → H.map (t,z)=z) ∧
          H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) =
            (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ∩
              (anchor.val.image ∪ (P.rep x.selected).val.image) ∧
          (e ⟨anchor.val.map x.t,hp⟩).val=(0,0) ∧
          (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
          (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
          IsOpen N ∧ anchor.val.map x.t ∈ N ∧ N ⊆ U ∧
          (∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
            z=anchor.val.map x.t) ∧
          (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
            Disjoint N (P.rep v).val.image) ∧
          (∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
            z.val=anchor.val.map x.t ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) ∧
        (∀ t z, z ∈ N → J.map (t,z)=z) ∧
        (∀ t z, z ∈ (M.cover.branch : Set S) → J.map (t,z)=z) ∧
        (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
          ∀ t z, z ∈ (P.rep w).val.image → J.map (t,z)=z) ∧
        (∀ t z, J.map (t,z) ∈ anchor.val.image ↔ z ∈ anchor.val.image) ∧
        (∀ z : U, z.val ∈ J.finalMap '' (H.finalMap '' (raw side).image) → z.val ∈ N →
          z.val=anchor.val.map x.t ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) ∧
        (J.finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image =
          ((H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) \ R ∧ (∀ t z, z ∈ (raw (!side)).image → J.map (t,z)=z) := by
    classical
    have family (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
        (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
        (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
        (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
        (side : Bool) :
        let R := ((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}
        ∃ (H : AmbientIsotopy S) (U : Set S) (hU : IsOpen U) (hp : anchor.val.map x.t ∈ U),
          ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
          ∃ N : Set S, ∃ (Q : R → AmbientIsotopy S) (W : R → Set S),
            (∀ t z, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
              H.map (t,z)=z) ∧
            (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
              ∀ t z, z ∈ (P.rep v).val.image → H.map (t,z)=z) ∧
            H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) =
              (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ∩
                (anchor.val.image ∪ (P.rep x.selected).val.image) ∧
            (e ⟨anchor.val.map x.t,hp⟩).val=(0,0) ∧
            (∀ z : U, z.val ∈ anchor.val.image ↔ (e z).val.2=0) ∧
            (∀ z : U, z.val ∈ (P.rep x.selected).val.image ↔ (e z).val.1=0) ∧
            IsOpen N ∧ anchor.val.map x.t ∈ N ∧ N ⊆ U ∧
            (∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) →
              z=anchor.val.map x.t) ∧
            (∀ v : {v // v ∈ F}, v ≠ x.selected → IsArcSimplex M {v.val,x.selected.val} →
              Disjoint N (P.rep v).val.image) ∧
            (∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
              z.val=anchor.val.map x.t ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) ∧
          (∀ p : R, IsOpen (W p) ∧ p.val ∈ W p ∧
              (∀ t z, z ∉ W p → (Q p).map (t,z)=z) ∧
              (∀ t z, z ∈ (M.cover.branch : Set S) → (Q p).map (t,z)=z) ∧
              (∀ t z, z ∈ crossings M anchor (P.rep x.selected) → z ≠ p.val → (Q p).map (t,z)=z) ∧
              (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
                ∀ t z, z ∈ (P.rep w).val.image → (Q p).map (t,z)=z) ∧
              (∀ t z, (Q p).map (t,z) ∈ anchor.val.image ↔ z ∈ anchor.val.image) ∧
              ((Q p).finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image =
                ((H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) \ {p.val}) ∧
          (∀ p q : R, p ≠ q → Disjoint (W p) (W q)) ∧ (∀ p : R, Disjoint N (W p)) ∧ ∀ p : R, Disjoint (W p) (raw (!side)).image := by
      classical
      letI : T2Space S := M.sphere.symm.t2Space
      letI : CompactSpace S := M.sphere.symm.compactSpace
      have germ := actualSourceSurgery_germ_11 (E := E) (S := S)
      have clearFamily {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
      (U : Set S) (hU : IsOpen U) (p : S) (hp : p ∈ U)
      (e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1})
      (he : (e ⟨p,hp⟩).val=(0,0))
      (δ : ℝ) (hd : 0 < δ) (hd1 : δ < 1) :
      ∃ H : AmbientIsotopy S,
        (∀ t z, z ∉ U → H.map (t,z)=z) ∧
        (∀ t (z : U), δ ≤ |(e z).val.1| ∨ δ ≤ |(e z).val.2| → H.map (t,z.val)=z.val) ∧
        (∀ t (z : U), ∃ hz : H.map (t,z.val) ∈ U,
          (e ⟨H.map (t,z.val),hz⟩).val.2=(e z).val.2) ∧
        ∀ A : Set S,
          (∀ z : U, z.val ∈ A → |(e z).val.1| < δ → |(e z).val.2| < δ →
            z.val=p ∨ 0 < (e z).val.1) →
          ∀ z : U, z.val ∈ H.finalMap '' A → |(e z).val.1| < δ → |(e z).val.2| < δ →
            0 < (e z).val.1 := by
        classical
        let a : Amount := ⟨(1/4:ℝ),by norm_num⟩
        let R := productIsotopy a
        have rfix (t : Interval) (z : ℝ × ℝ) (hz : 1 ≤ |z.1| ∨ 1 ≤ |z.2|) :
            R.map (t,z)=z := productIsotopy_fixed a t z hz
        have r0x : 0 < (R.finalMap (0,0)).1 := by
          change 0 < scalar (rowAmount (timeAmount a 1) 0).val 0
          norm_num [scalar,rowAmount,timeAmount,a,tent]
        have rpositive (t : Interval) (z : ℝ × ℝ) (hx : 0 < z.1) :
            0 < (R.map (t,z)).1 := by
          change 0 < z.1 + (t.val * (1/4:ℝ) * tent z.2) * tent z.1
          have ht := t.property.1
          have h1 := tent_nonneg z.1
          have h2 := tent_nonneg z.2
          exact hx.trans_le (le_add_of_nonneg_right (by positivity))
        let Q := {q : ℝ × ℝ | |q.1| < 1 ∧ |q.2| < 1}
        let g : (ℝ × ℝ) ≃ₜ Plane := {
          toEquiv := {
            toFun := fun z => Plane.mk (z.1/δ) (z.2/δ)
            invFun := fun z => (δ*z 0,δ*z 1)
            left_inv := by intro z; apply Prod.ext <;> simp [Plane.mk] <;> field_simp [ne_of_gt hd]
            right_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk,ne_of_gt hd] }
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
        let V : Set Plane := g '' Q
        let ee : U ≃ₜ V := e.trans (g.image Q)
        have hCV : Plane.closedSquare 0 1 ⊆ V := by
          intro z hz
          have hcoords := max_le_iff.mp (mem_closedSquare_zero_one.mp hz)
          refine ⟨g.symm z,?_,g.apply_symm_apply z⟩
          change |δ*z 0| < 1 ∧ |δ*z 1| < 1
          rw [abs_mul,abs_mul,abs_of_pos hd]
          constructor
          · exact (mul_le_of_le_one_right hd.le hcoords.1).trans_lt hd1
          · exact (mul_le_of_le_one_right hd.le hcoords.2).trans_lt hd1
        let pc := planeCoordinates
        let K : AmbientIsotopy Plane := {
          map := ⟨fun z => pc.symm (R.map (z.1,pc z.2)),by
            exact pc.symm.continuous.comp (R.map.continuous.comp
              (continuous_fst.prodMk (pc.continuous.comp continuous_snd)))⟩
          homeomorphism_at := by
            intro t
            obtain ⟨r,hr⟩ := R.homeomorphism_at t
            exact ⟨(pc.trans r).trans pc.symm,fun z => congrArg pc.symm (hr (pc z))⟩
          at_zero := by
            intro z
            change pc.symm (R.map (⟨0,by norm_num⟩,pc z))=z
            rw [R.at_zero,pc.symm_apply_apply] }
        have kcoord (t : Interval) (z : Plane) : pc (K.map (t,z))=R.map (t,pc z) :=
          pc.apply_symm_apply _
        have kfix (t : Interval) (z : Plane) (hz : z ∉ Plane.openSquare 0 1) :
            K.map (t,z)=z := by
          apply pc.injective
          rw [kcoord]
          apply rfix
          change 1 ≤ |z 0| ∨ 1 ≤ |z 1|
          have hn : ¬ (|z 0| < 1 ∧ |z 1| < 1) := by
            intro hh
            exact hz (mem_openSquare_zero_one.mpr (max_lt hh.1 hh.2))
          rcases not_and_or.mp hn with h | h
          · exact Or.inl (le_of_not_gt h)
          · exact Or.inr (le_of_not_gt h)
        obtain ⟨KU,H,hcoords,hlift,houtside⟩ := position_surface_chart_lift S U V hU ee
          (Plane.closedSquare 0 1) (isCompact_closedSquare 0 1) hCV K
          (fun t z hz => kfix t z (fun hh => hz
            (mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hh).le)))
        have coord (t : Interval) (z : U) :
            g (e ⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩).val =
              K.map (t,g (e z).val) := by
          have hs : (⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩ : U) =
              KU.map (t,z) := Subtype.ext (hlift t z)
          rw [hs]
          exact hcoords t z
        have localFix : ∀ t (z : U), δ ≤ |(e z).val.1| ∨ δ ≤ |(e z).val.2| →
            H.map (t,z.val)=z.val := by
          intro t z hz
          have hne : g (e z).val ∉ Plane.openSquare 0 1 := by
            intro hh
            have hcc := max_lt_iff.mp (mem_openSquare_zero_one.mp hh)
            have hx : |(e z).val.1| / δ < 1 := by
              simpa [g,Plane.mk,abs_div,abs_of_pos hd] using hcc.1
            have hy : |(e z).val.2| / δ < 1 := by
              simpa [g,Plane.mk,abs_div,abs_of_pos hd] using hcc.2
            have hx := (div_lt_iff₀ hd).mp hx
            have hy := (div_lt_iff₀ hd).mp hy
            rcases hz with hz | hz <;> linarith
          have hh := coord t z
          rw [kfix t _ hne] at hh
          exact congrArg Subtype.val (e.injective (Subtype.ext (g.injective hh)))
        refine ⟨H,houtside,localFix,?_,?_⟩
        · intro t z
          have hz : H.map (t,z.val) ∈ U := by
            rw [hlift t z]
            exact (KU.map (t,z)).property
          refine ⟨hz,?_⟩
          have hh := congrArg (fun v : Plane => v 1) (coord t z)
          change (e ⟨H.map (t,z.val),hz⟩).val.2 / δ =
            (R.map (t,pc (g (e z).val))).2 at hh
          change (e ⟨H.map (t,z.val),hz⟩).val.2 / δ = (e z).val.2 / δ at hh
          exact (div_left_inj' (ne_of_gt hd)).mp hh
        · intro A hA z hz hx hy
          obtain ⟨w,hw,hwz⟩ := hz
          have hwU : w ∈ U := by
            by_contra hn
            have hf := houtside 1 w hn
            change H.finalMap w=w at hf
            exact hn ((hf.symm.trans hwz).symm ▸ z.property)
          let wu : U := ⟨w,hwU⟩
          have hwx : |(e wu).val.1| < δ := by
            by_contra hn
            have hf := localFix 1 wu (Or.inl (le_of_not_gt hn))
            change H.finalMap w=w at hf
            have huw : wu=z := Subtype.ext (hf.symm.trans hwz)
            exact hn (huw.symm ▸ hx)
          have hwy : |(e wu).val.2| < δ := by
            by_contra hn
            have hf := localFix 1 wu (Or.inr (le_of_not_gt hn))
            change H.finalMap w=w at hf
            have huw : wu=z := Subtype.ext (hf.symm.trans hwz)
            exact hn (huw.symm ▸ hy)
          have hc := congrArg pc (coord 1 wu)
          have hez : (⟨H.map (1,wu.val),by rw [hlift]; exact (KU.map (1,wu)).property⟩ : U)=z :=
            Subtype.ext hwz
          rw [hez,kcoord] at hc
          have coords (v : U) : pc (g (e v).val) = ((e v).val.1/δ,(e v).val.2/δ) := rfl
          rw [coords,coords] at hc
          have hx : 0 < (R.finalMap ((e wu).val.1/δ,(e wu).val.2/δ)).1 := by
            rcases hA wu hw hwx hwy with hpw | hpw
            · have hwp : wu=⟨p,hp⟩ := Subtype.ext hpw
              rw [hwp,he]
              simpa using r0x
            · exact rpositive 1 _ (div_pos hpw hd)
          change ((e z).val.1/δ,(e z).val.2/δ)=R.finalMap _ at hc
          rw [←hc] at hx
          simpa using (lt_div_iff₀ hd).mp hx
      obtain ⟨H,Uf,hUf,hpf,ef,Nf,hfix,hneighbors,hgraph,hef,haf,hbf,hNf,hrNf,hNfUf,hnodef,hneighborNf,hgermf,hAll⟩ := germ M anchor F P x raw hraw side
      have clearNode (v : S) (hv : v ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected))
          (hvFirst : v ≠ anchor.val.map x.t) (O : Set S) (hO : IsOpen O) (hvO : v ∈ O) :
          ∃ (Q : AmbientIsotopy S) (W : Set S), Disjoint W (raw (!side)).image ∧ IsOpen W ∧ v ∈ W ∧ W ⊆ O ∧
            (∀ t z, z ∉ W → Q.map (t,z)=z) ∧
            (∀ t z, z ∈ (M.cover.branch : Set S) → Q.map (t,z)=z) ∧
            (∀ t z, z ∈ crossings M anchor (P.rep x.selected) → z ≠ v → Q.map (t,z)=z) ∧
            (∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
              ∀ t z, z ∈ (P.rep w).val.image → Q.map (t,z)=z) ∧
            (∀ t z, Q.map (t,z) ∈ anchor.val.image ↔ z ∈ anchor.val.image) ∧
            (Q.finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image =
              ((H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) \ {v} := by
          obtain ⟨U,hU,hp,e,N₀,he,ha,hb,hN₀,hrN₀,hN₀U,hnode₀,hneighborN₀,hN₀Other,hgerm₀⟩ := hAll v hv hvFirst
          let N := N₀ ∩ O
          have hN : IsOpen N := hN₀.inter hO
          have hrN : v ∈ N := ⟨hrN₀,hvO⟩
          have hNU : N ⊆ U := fun z hz => hN₀U hz.1
          have hnode : ∀ z ∈ N, z ∈ (M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected) → z=v :=
            fun z hz hk => hnode₀ z hz.1 hk
          have hneighborN : ∀ w : {w // w ∈ F}, w ≠ x.selected → IsArcSimplex M {w.val,x.selected.val} →
              Disjoint N (P.rep w).val.image := fun w hn hs =>
            (hneighborN₀ w hn hs).mono_left inter_subset_left
          have hgerm : ∀ z : U, z.val ∈ H.finalMap '' (raw side).image → z.val ∈ N →
              z.val=v ∨ 0 < (e z).val.1 := fun z hz hn => hgerm₀ z hz hn.1
          let r := v
          have hrMark : r ∉ (M.cover.branch : Set S) := hv.2.1.2
          let B := {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}
          let o : B := ⟨(0,0),by simp⟩
          have hpo : e.symm o=⟨r,hp⟩ := by
            apply e.injective
            rw [e.apply_symm_apply]
            exact Subtype.ext he.symm
          have hOpen : IsOpen ((fun z : B => (e.symm z).val) ⁻¹' N) :=
            hN.preimage (continuous_subtype_val.comp e.symm.continuous)
          have hoN : o ∈ ((fun z : B => (e.symm z).val) ⁻¹' N) := by
            change (e.symm o).val ∈ N
            rw [hpo]
            exact hrN
          obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hOpen o hoN
          let δ := min ρ 1 / 2
          have hd : 0 < δ := by dsimp [δ]; positivity
          have hdρ : δ < ρ := by dsimp [δ]; have := min_le_left ρ (1:ℝ); linarith
          have hd1 : δ < 1 := by dsimp [δ]; have := min_le_right ρ (1:ℝ); linarith
          have smallN (z : U) (hx : |(e z).val.1| ≤ δ) (hy : |(e z).val.2| ≤ δ) : z.val ∈ N := by
            have hh : e z ∈ ball o ρ := by
              rw [Metric.mem_ball,Subtype.dist_eq]
              change dist (e z).val (0,0) < ρ
              rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero]
              exact (max_le hx hy).trans_lt hdρ
            have h := hball hh
            change (e.symm (e z)).val ∈ N at h
            simpa only [e.symm_apply_apply] using h
          obtain ⟨Q,qout,qlocal,qcoord,qclear⟩ := clearFamily U hU r hp e he δ hd hd1
          let Small : Set S := Subtype.val '' {z : U | |(e z).val.1| < δ ∧ |(e z).val.2| < δ}
          have hSmallN : Small ⊆ N := by
            rintro z ⟨u,hu,rfl⟩
            exact smallN u hu.1.le hu.2.le
          have hrSmall : r ∈ Small := by
            refine ⟨⟨r,hp⟩,?_,rfl⟩
            change |(e ⟨r,hp⟩).val.1| < δ ∧ |(e ⟨r,hp⟩).val.2| < δ
            rw [he]
            exact ⟨by simpa using hd,by simpa using hd⟩
          have qfix : ∀ t z, z ∉ Small → Q.map (t,z)=z := by
            intro t z hz
            by_cases hu : z ∈ U
            · apply qlocal t ⟨z,hu⟩
              have hn : ¬ (|(e ⟨z,hu⟩).val.1| < δ ∧ |(e ⟨z,hu⟩).val.2| < δ) :=
                fun h => hz ⟨⟨z,hu⟩,h,rfl⟩
              rcases not_and_or.mp hn with h | h
              · exact Or.inl (le_of_not_gt h)
              · exact Or.inr (le_of_not_gt h)
            · exact qout t z hu
          have hlocal : ∀ z : U, z.val ∈ H.finalMap '' (raw side).image →
              |(e z).val.1| < δ → |(e z).val.2| < δ → z.val=r ∨ 0 < (e z).val.1 :=
            fun z hz hx hy => hgerm z hz (smallN z hx.le hy.le)
          have qavoid : Disjoint ((Q.finalMap '' (H.finalMap '' (raw side).image)) ∩ Small)
              (P.rep x.selected).val.image := by
            apply disjoint_left.mpr
            rintro z ⟨hz,⟨u,hu,rfl⟩⟩ hzOld
            have hpos := qclear (H.finalMap '' (raw side).image) hlocal u hz hu.1 hu.2
            exact (ne_of_gt hpos) ((hb u).mp hzOld)
          have hSmall : IsOpen Small := hU.isOpenMap_subtype_val _
            ((isOpen_lt (continuous_fst.comp (continuous_subtype_val.comp e.continuous)).abs continuous_const).inter
              (isOpen_lt (continuous_snd.comp (continuous_subtype_val.comp e.continuous)).abs continuous_const))
          refine ⟨Q,Small,hN₀Other.mono_left (fun z hz => (hSmallN hz).1),hSmall,hrSmall,(fun z hz => (hSmallN hz).2),qfix,?_,?_,?_,?_,?_⟩
          · intro t z hz
            exact qfix t z (fun h => hrMark (by
              have heq : z=r := hnode z (hSmallN h) (Or.inl hz)
              rw [←heq]
              exact hz))
          · intro t z hz hn
            exact qfix t z (fun h => hn (hnode z (hSmallN h) (Or.inr hz)))
          · intro w hn hs t z hz
            exact qfix t z (fun h => disjoint_left.mp (hneighborN w hn hs) (hSmallN h) hz)
          · intro t z
            by_cases hu : z ∈ U
            · obtain ⟨hqU,hsecond⟩ := qcoord t ⟨z,hu⟩
              rw [ha ⟨_,hqU⟩,ha ⟨z,hu⟩,hsecond]
            · rw [qout t z hu]
          · ext z
            constructor
            · rintro ⟨hz,hzOld⟩
              have hzSmall : z ∉ Small := fun h => disjoint_left.mp qavoid ⟨hz,h⟩ hzOld
              obtain ⟨w,hw,hwz⟩ := hz
              have hqz : Q.finalMap z=z := qfix 1 z hzSmall
              obtain ⟨q,hq⟩ := Q.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
              have hqFinal (u : S) : q u=Q.finalMap u := hq u
              have hwEq : w=z := q.injective (by rw [hqFinal,hqFinal]; exact hwz.trans hqz.symm)
              subst w
              refine ⟨⟨hw,hzOld⟩,?_⟩
              intro hzR
              exact hzSmall ((mem_singleton_iff.mp hzR).symm ▸ hrSmall)
            · rintro ⟨⟨hzImage,hzOld⟩,hn⟩
              have hzSmall : z ∉ Small := by
                intro h
                have hzGraph : z ∈ (H.finalMap '' (raw side).image) ∩
                    (anchor.val.image ∪ (P.rep x.selected).val.image) := ⟨hzImage,Or.inr hzOld⟩
                rw [hgraph] at hzGraph
                exact hn (mem_singleton_iff.mpr (hnode z (hSmallN h) hzGraph.1.2))
              exact ⟨⟨z,hzImage,qfix 1 z hzSmall⟩,hzOld⟩
      let R := ((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}
      have hR : R.Finite := (P.finite x.selected).subset (fun z hz => hz.1.2)
      obtain ⟨O,hO,hOdis⟩ := (P.finite x.selected).t2_separation
      choose Q W hWOther hW hpW hWO hqout hqmarks hqnodes hqneighbors hqanchor hqimage using
        fun p : R => clearNode p.val p.property.1
          (fun h => p.property.2 (mem_singleton_iff.mpr h)) (O p.val) (hO p.val).2 (hO p.val).1
      let r := anchor.val.map x.t
      have hrMark : r ∉ (M.cover.branch : Set S) := by
        intro h
        rcases anchor.val.marked_only_at_ends x.t h with h | h
        · exact (ne_of_gt x.t_interior.1) (congrArg Subtype.val h)
        · exact (ne_of_lt x.t_interior.2) (congrArg Subtype.val h)
      have hrC : r ∈ crossings M anchor (P.rep x.selected) :=
        ⟨⟨mem_range_self _,hrMark⟩,⟨⟨x.s,x.same_point.symm⟩,hrMark⟩⟩
      let N := Nf ∩ O r
      refine ⟨H,Uf,hUf,hpf,ef,N,Q,W,hfix,hneighbors,hgraph,hef,haf,hbf,
        hNf.inter (hO r).2,⟨hrNf,(hO r).1⟩,(fun z hz => hNfUf hz.1),
        (fun z hz hk => hnodef z hz.1 hk),
        (fun w hn hs => (hneighborNf w hn hs).mono_left inter_subset_left),
        (fun z hz hn => hgermf z hz hn.1),?_,?_,?_,hWOther⟩
      · intro p
        exact ⟨hW p,hpW p,hqout p,hqmarks p,hqnodes p,hqneighbors p,hqanchor p,hqimage p⟩
      · intro p q hn
        exact (hOdis p.property.1.2 q.property.1.2 (fun h => hn (Subtype.ext h))).mono (hWO p) (hWO q)
      · intro p
        have hne : r ≠ p.val := fun h => p.property.2 (mem_singleton_iff.mpr h.symm)
        exact (hOdis hrC p.property.1.2 hne).mono (fun z hz => hz.2) (hWO p)
    let R := ((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}
    obtain ⟨H,U,hU,hp,e,N,Q,W,hfix,hneighbors,hgraph,he,ha,hb,hN,hpN,hNU,hnode,hneighborN,hgerm,hQ,hdis,hNW,hWOther⟩ := family M anchor F P x raw hraw side
    have hR : R.Finite := (P.finite x.selected).subset (fun z hz => hz.1.2)
    letI : Fintype R := hR.fintype
    obtain ⟨J,houtside,hinside⟩ := finite_supported_patch_assembly W hdis Q (fun p => (hQ p).2.2.1)
    have qpres (p : R) (t : Interval) (z : S) (hz : z ∈ W p) : (Q p).map (t,z) ∈ W p := by
      obtain ⟨f,hf⟩ := (Q p).homeomorphism_at t
      by_contra hn
      have he : f ((Q p).map (t,z))=f z := by
        rw [hf,(hQ p).2.2.1 t _ hn,hf]
      exact hn ((f.injective he).symm ▸ hz)
    have jfix (t : Interval) (z : S) (h : ∀ p : R, (Q p).map (t,z)=z) : J.map (t,z)=z := by
      by_cases hz : z ∈ ⋃ p, W p
      · obtain ⟨p,hp⟩ := mem_iUnion.mp hz
        exact (hinside p t z hp).trans (h p)
      · exact houtside t z hz
    have jN (t : Interval) (z : S) (hz : z ∈ N) : J.map (t,z)=z := by
      apply jfix t z
      intro p
      exact (hQ p).2.2.1 t z (fun h => disjoint_left.mp (hNW p) hz h)
    refine ⟨H,U,hU,hp,e,N,J,hfix,hneighbors,hgraph,he,ha,hb,hN,hpN,hNU,hnode,
      hneighborN,hgerm,jN,?_,?_,?_,?_,?_,?_⟩
    · intro t z hz
      exact jfix t z (fun p => (hQ p).2.2.2.1 t z hz)
    · intro w hn hs t z hz
      exact jfix t z (fun p => (hQ p).2.2.2.2.2.1 w hn hs t z hz)
    · intro t z
      by_cases hz : z ∈ ⋃ p, W p
      · obtain ⟨p,hp⟩ := mem_iUnion.mp hz
        rw [hinside p t z hp]
        exact (hQ p).2.2.2.2.2.2.1 t z
      · rw [houtside t z hz]
    · intro z hz hn
      obtain ⟨v,hv,hvz⟩ := hz
      obtain ⟨f,hf⟩ := J.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
      have hvEq : v=z.val := f.injective (by rw [hf,hf]; exact hvz.trans (jN 1 z.val hn).symm)
      exact hgerm z (hvEq ▸ hv) hn
    · ext z
      constructor
      · rintro ⟨⟨w,hw,hwz⟩,hzOld⟩
        by_cases hwW : w ∈ ⋃ p, W p
        · obtain ⟨p,hp⟩ := mem_iUnion.mp hwW
          have hQw : (Q p).finalMap w=z := (hinside p 1 w hp).symm.trans hwz
          have hzQ : z ∈ (Q p).finalMap '' (H.finalMap '' (raw side).image) ∩
              (P.rep x.selected).val.image := ⟨⟨w,hw,hQw⟩,hzOld⟩
          rw [(hQ p).2.2.2.2.2.2.2] at hzQ
          refine ⟨hzQ.1,?_⟩
          intro hzR
          let q : R := ⟨z,hzR⟩
          have hzP : z ∈ W p := hQw ▸ qpres p 1 w hp
          have hpq : p=q := by
            by_contra hn
            exact disjoint_left.mp (hdis p q hn) hzP (hQ q).2.1
          exact hzQ.2 (mem_singleton_iff.mpr (congrArg Subtype.val hpq).symm)
        · have hwEq : w=z := (houtside 1 w hwW).symm.trans hwz
          refine ⟨⟨hwEq ▸ hw,hzOld⟩,?_⟩
          intro hzR
          let p : R := ⟨z,hzR⟩
          exact hwW (hwEq.symm ▸ mem_iUnion.mpr ⟨p,(hQ p).2.1⟩)
      · rintro ⟨⟨hzImage,hzOld⟩,hzNotR⟩
        have hzGraph : z ∈ H.finalMap '' (raw side).image ∩
            (anchor.val.image ∪ (P.rep x.selected).val.image) := ⟨hzImage,Or.inr hzOld⟩
        rw [hgraph] at hzGraph
        have hzFix : J.finalMap z=z := by
          apply jfix 1 z
          intro p
          rcases hzGraph.1.2 with hm | hc
          · exact (hQ p).2.2.2.1 1 z hm
          · exact (hQ p).2.2.2.2.1 1 z hc (fun h => hzNotR (h.symm ▸ p.property))
        exact ⟨⟨z,hzImage,hzFix⟩,hzOld⟩
    · intro t z hz
      apply jfix t z
      intro p
      exact (hQ p).2.2.1 t z (fun h => disjoint_left.mp (hWOther p) h hz)
  have clearFamily {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
  (U : Set S) (hU : IsOpen U) (p : S) (hp : p ∈ U)
  (e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1})
  (he : (e ⟨p,hp⟩).val=(0,0))
  (δ : ℝ) (hd : 0 < δ) (hd1 : δ < 1) :
  ∃ H : AmbientIsotopy S,
    (∀ t z, z ∉ U → H.map (t,z)=z) ∧
    (∀ t (z : U), δ ≤ |(e z).val.1| ∨ δ ≤ |(e z).val.2| → H.map (t,z.val)=z.val) ∧
    ∀ A : Set S,
      (∀ z : U, z.val ∈ A → |(e z).val.1| < δ → |(e z).val.2| < δ →
        z.val=p ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2)) →
      ∀ z : U, z.val ∈ H.finalMap '' A → |(e z).val.1| < δ → |(e z).val.2| < δ →
        (e z).val.1 < 0 ∧ 0 < (e z).val.2 := by
    classical
    have quadrant : ∃ H : AmbientIsotopy (ℝ × ℝ),
    (∀ t z, 1 ≤ |z.1| ∨ 1 ≤ |z.2| → H.map (t,z)=z) ∧
    (H.finalMap (0,0)).1 < 0 ∧ 0 < (H.finalMap (0,0)).2 ∧
    ∀ t z, z.1 < 0 → 0 < z.2 →
      (H.map (t,z)).1 < 0 ∧ 0 < (H.map (t,z)).2 := by
      let a : Amount := ⟨-(1/4:ℝ),by norm_num⟩
      let b : Amount := ⟨(1/4:ℝ),by norm_num⟩
      let swap : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.prodComm ℝ ℝ
      let V : AmbientIsotopy (ℝ × ℝ) := {
        map := ⟨fun z => swap ((productIsotopy b).map (z.1,swap z.2)),by
          exact swap.continuous.comp ((productIsotopy b).map.continuous.comp
            (continuous_fst.prodMk (swap.continuous.comp continuous_snd)))⟩
        homeomorphism_at := by
          intro t
          exact ⟨(swap.trans (productSlide (timeAmount b t))).trans swap,fun _ => rfl⟩
        at_zero := by intro z; change swap ((productIsotopy b).map (0,swap z))=z
                      simp [productIsotopy,productSlide,timeAmount,rowAmount,scalar,swap] }
      let H : AmbientIsotopy (ℝ × ℝ) := {
        map := ⟨fun z => V.map (z.1,(productIsotopy a).map z),by
          exact V.map.continuous.comp (continuous_fst.prodMk (productIsotopy a).map.continuous)⟩
        homeomorphism_at := by
          intro t
          obtain ⟨v,hv⟩ := V.homeomorphism_at t
          exact ⟨(productSlide (timeAmount a t)).trans v,fun z => hv _⟩
        at_zero := by intro z; change V.map (0,(productIsotopy a).map (0,z))=z
                      simp [V,productIsotopy,productSlide,timeAmount,rowAmount,scalar,swap] }
      have hleft (t : Interval) (z : ℝ × ℝ) :
          ((productIsotopy a).map (t,z)).1 ≤ z.1 := by
        change z.1 + (t.val * (-(1/4:ℝ)) * tent z.2) * tent z.1 ≤ z.1
        have ht := t.property.1
        have h1 := tent_nonneg z.1
        have h2 := tent_nonneg z.2
        nlinarith [mul_nonneg ht h2,mul_nonneg (mul_nonneg ht h2) h1]
      have hup (t : Interval) (z : ℝ × ℝ) : z.2 ≤ (V.map (t,z)).2 := by
        change z.2 ≤ z.2 + (t.val * (1/4:ℝ) * tent z.1) * tent z.2
        have ht := t.property.1
        have h1 := tent_nonneg z.1
        have h2 := tent_nonneg z.2
        exact le_add_of_nonneg_right (by positivity)
      refine ⟨H,?_,?_,?_,?_⟩
      · intro t z hz
        change V.map (t,(productIsotopy a).map (t,z))=z
        rw [productIsotopy_fixed a t z hz]
        change swap ((productIsotopy b).map (t,swap z))=z
        rw [productIsotopy_fixed b t (swap z) (by exact hz.symm)]
        rfl
      · change scalar (rowAmount (timeAmount a 1) 0).val 0 < 0
        norm_num [scalar,rowAmount,timeAmount,a,tent]
      · change 0 < scalar (rowAmount (timeAmount b 1)
            (scalar (rowAmount (timeAmount a 1) 0).val 0)).val 0
        norm_num [scalar,rowAmount,timeAmount,a,b,tent]
      · intro t z hx hy
        constructor
        · exact (hleft t z).trans_lt hx
        · exact hy.trans_le (hup t ((productIsotopy a).map (t,z)))
    let Q := {q : ℝ × ℝ | |q.1| < 1 ∧ |q.2| < 1}
    let g : (ℝ × ℝ) ≃ₜ Plane := {
      toEquiv := {
        toFun := fun z => Plane.mk (z.1/δ) (z.2/δ)
        invFun := fun z => (δ*z 0,δ*z 1)
        left_inv := by intro z; apply Prod.ext <;> simp [Plane.mk] <;> field_simp [ne_of_gt hd]
        right_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk,ne_of_gt hd] }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let V : Set Plane := g '' Q
    let ee : U ≃ₜ V := e.trans (g.image Q)
    have hCV : Plane.closedSquare 0 1 ⊆ V := by
      intro z hz
      have hcoords := max_le_iff.mp (mem_closedSquare_zero_one.mp hz)
      refine ⟨g.symm z,?_,g.apply_symm_apply z⟩
      change |δ*z 0| < 1 ∧ |δ*z 1| < 1
      rw [abs_mul,abs_mul,abs_of_pos hd]
      constructor
      · exact (mul_le_of_le_one_right hd.le hcoords.1).trans_lt hd1
      · exact (mul_le_of_le_one_right hd.le hcoords.2).trans_lt hd1
    obtain ⟨R,rfix,r0x,r0y,rquad⟩ := quadrant
    let pc := planeCoordinates
    let K : AmbientIsotopy Plane := {
      map := ⟨fun z => pc.symm (R.map (z.1,pc z.2)),by
        exact pc.symm.continuous.comp (R.map.continuous.comp
          (continuous_fst.prodMk (pc.continuous.comp continuous_snd)))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨r,hr⟩ := R.homeomorphism_at t
        exact ⟨(pc.trans r).trans pc.symm,fun z => congrArg pc.symm (hr (pc z))⟩
      at_zero := by
        intro z
        change pc.symm (R.map (⟨0,by norm_num⟩,pc z))=z
        rw [R.at_zero,pc.symm_apply_apply] }
    have kcoord (t : Interval) (z : Plane) : pc (K.map (t,z))=R.map (t,pc z) :=
      pc.apply_symm_apply _
    have kfix (t : Interval) (z : Plane) (hz : z ∉ Plane.openSquare 0 1) :
        K.map (t,z)=z := by
      apply pc.injective
      rw [kcoord]
      apply rfix
      change 1 ≤ |z 0| ∨ 1 ≤ |z 1|
      have hn : ¬ (|z 0| < 1 ∧ |z 1| < 1) := by
        intro hh
        exact hz (mem_openSquare_zero_one.mpr (max_lt hh.1 hh.2))
      rcases not_and_or.mp hn with h | h
      · exact Or.inl (le_of_not_gt h)
      · exact Or.inr (le_of_not_gt h)
    obtain ⟨KU,H,hcoords,hlift,houtside⟩ := position_surface_chart_lift S U V hU ee
      (Plane.closedSquare 0 1) (isCompact_closedSquare 0 1) hCV K
      (fun t z hz => kfix t z (fun hh => hz
        (mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hh).le)))
    have coord (t : Interval) (z : U) :
        g (e ⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩).val =
          K.map (t,g (e z).val) := by
      have hs : (⟨H.map (t,z.val),by rw [hlift]; exact (KU.map (t,z)).property⟩ : U) =
          KU.map (t,z) := Subtype.ext (hlift t z)
      rw [hs]
      exact hcoords t z
    have localFix : ∀ t (z : U), δ ≤ |(e z).val.1| ∨ δ ≤ |(e z).val.2| →
        H.map (t,z.val)=z.val := by
      intro t z hz
      have hne : g (e z).val ∉ Plane.openSquare 0 1 := by
        intro hh
        have hcc := max_lt_iff.mp (mem_openSquare_zero_one.mp hh)
        have hx : |(e z).val.1| / δ < 1 := by
          simpa [g,Plane.mk,abs_div,abs_of_pos hd] using hcc.1
        have hy : |(e z).val.2| / δ < 1 := by
          simpa [g,Plane.mk,abs_div,abs_of_pos hd] using hcc.2
        have hx := (div_lt_iff₀ hd).mp hx
        have hy := (div_lt_iff₀ hd).mp hy
        rcases hz with hz | hz <;> linarith
      have hh := coord t z
      rw [kfix t _ hne] at hh
      exact congrArg Subtype.val (e.injective (Subtype.ext (g.injective hh)))
    refine ⟨H,houtside,localFix,?_⟩
    intro A hA z hz hx hy
    obtain ⟨w,hw,hwz⟩ := hz
    have hwU : w ∈ U := by
      by_contra hn
      have hf := houtside 1 w hn
      change H.finalMap w=w at hf
      exact hn ((hf.symm.trans hwz).symm ▸ z.property)
    let wu : U := ⟨w,hwU⟩
    have hwx : |(e wu).val.1| < δ := by
      by_contra hn
      have hf := localFix 1 wu (Or.inl (le_of_not_gt hn))
      change H.finalMap w=w at hf
      have huw : wu=z := Subtype.ext (hf.symm.trans hwz)
      exact hn (huw.symm ▸ hx)
    have hwy : |(e wu).val.2| < δ := by
      by_contra hn
      have hf := localFix 1 wu (Or.inr (le_of_not_gt hn))
      change H.finalMap w=w at hf
      have huw : wu=z := Subtype.ext (hf.symm.trans hwz)
      exact hn (huw.symm ▸ hy)
    have hc := congrArg pc (coord 1 wu)
    have hez : (⟨H.map (1,wu.val),by rw [hlift]; exact (KU.map (1,wu)).property⟩ : U)=z :=
      Subtype.ext hwz
    rw [hez,kcoord] at hc
    have coords (v : U) : pc (g (e v).val) = ((e v).val.1/δ,(e v).val.2/δ) := rfl
    rw [coords,coords] at hc
    have hnw : (R.finalMap ((e wu).val.1/δ,(e wu).val.2/δ)).1 < 0 ∧
        0 < (R.finalMap ((e wu).val.1/δ,(e wu).val.2/δ)).2 := by
      rcases hA wu hw hwx hwy with hpw | ⟨hxl,hyp⟩
      · have hwp : wu=⟨p,hp⟩ := Subtype.ext hpw
        rw [hwp,he]
        simpa using And.intro r0x r0y
      · exact rquad 1 _ (div_neg_of_neg_of_pos hxl hd) (div_pos hyp hd)
    change ((e z).val.1/δ,(e z).val.2/δ)=R.finalMap _ at hc
    rw [←hc] at hnw
    constructor
    · simpa using (div_lt_iff₀ hd).mp hnw.1
    · simpa using (lt_div_iff₀ hd).mp hnw.2
  let R := ((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t}
  obtain ⟨H,U,hU,hp,e,N,J,hfix,hneighbors,hgraph,he,ha,hb,hN,hrN,hNU,hnode,hneighborN,hgerm,jN,jmarks,jneighbors,janchor,jgerm,jimage,jOther⟩ :=
    family M anchor F P x raw hraw side
  let r := anchor.val.map x.t
  have hrMark : r ∉ (M.cover.branch : Set S) := by
    intro h
    rcases anchor.val.marked_only_at_ends x.t h with h | h
    · exact (ne_of_gt x.t_interior.1) (congrArg Subtype.val h)
    · exact (ne_of_lt x.t_interior.2) (congrArg Subtype.val h)
  let B := {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}
  let o : B := ⟨(0,0),by simp⟩
  have hpo : e.symm o=⟨r,hp⟩ := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext he.symm
  have hOpen : IsOpen ((fun z : B => (e.symm z).val) ⁻¹' N) :=
    hN.preimage (continuous_subtype_val.comp e.symm.continuous)
  have hoN : o ∈ ((fun z : B => (e.symm z).val) ⁻¹' N) := by
    change (e.symm o).val ∈ N
    rw [hpo]
    exact hrN
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hOpen o hoN
  let δ := min ρ 1 / 2
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hdρ : δ < ρ := by dsimp [δ]; have := min_le_left ρ (1:ℝ); linarith
  have hd1 : δ < 1 := by dsimp [δ]; have := min_le_right ρ (1:ℝ); linarith
  have smallN (z : U) (hx : |(e z).val.1| ≤ δ) (hy : |(e z).val.2| ≤ δ) : z.val ∈ N := by
    have hh : e z ∈ ball o ρ := by
      rw [Metric.mem_ball,Subtype.dist_eq]
      change dist (e z).val (0,0) < ρ
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero]
      exact (max_le hx hy).trans_lt hdρ
    have h := hball hh
    change (e.symm (e z)).val ∈ N at h
    simpa only [e.symm_apply_apply] using h
  obtain ⟨Q,qout,qlocal,qclear⟩ := clearFamily U hU r hp e he δ hd hd1
  let Small : Set S := Subtype.val '' {z : U | |(e z).val.1| < δ ∧ |(e z).val.2| < δ}
  have hSmallN : Small ⊆ N := by
    rintro z ⟨u,hu,rfl⟩
    exact smallN u hu.1.le hu.2.le
  have hrSmall : r ∈ Small := by
    refine ⟨⟨r,hp⟩,?_,rfl⟩
    change |(e ⟨r,hp⟩).val.1| < δ ∧ |(e ⟨r,hp⟩).val.2| < δ
    rw [he]
    exact ⟨by simpa using hd,by simpa using hd⟩
  have qfix : ∀ t z, z ∉ Small → Q.map (t,z)=z := by
    intro t z hz
    by_cases hu : z ∈ U
    · apply qlocal t ⟨z,hu⟩
      have hn : ¬ (|(e ⟨z,hu⟩).val.1| < δ ∧ |(e ⟨z,hu⟩).val.2| < δ) :=
        fun h => hz ⟨⟨z,hu⟩,h,rfl⟩
      rcases not_and_or.mp hn with h | h
      · exact Or.inl (le_of_not_gt h)
      · exact Or.inr (le_of_not_gt h)
    · exact qout t z hu
  have hlocal : ∀ z : U, z.val ∈ J.finalMap '' (H.finalMap '' (raw side).image) →
      |(e z).val.1| < δ → |(e z).val.2| < δ →
      z.val=r ∨ ((e z).val.1 < 0 ∧ 0 < (e z).val.2) :=
    fun z hz hx hy => jgerm z hz (smallN z hx.le hy.le)
  have qavoid : Disjoint ((Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ Small)
      (anchor.val.image ∪ (P.rep x.selected).val.image) := by
    apply disjoint_left.mpr
    rintro z ⟨hz,⟨u,hu,rfl⟩⟩ hzgraph
    have hnw := qclear (J.finalMap '' (H.finalMap '' (raw side).image)) hlocal u hz hu.1 hu.2
    rcases hzgraph with hzA | hzO
    · exact (ne_of_gt hnw.2) ((ha u).mp hzA)
    · exact (ne_of_lt hnw.1) ((hb u).mp hzO)
  have qAnchor :
      (Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ anchor.val.image =
        ((J.finalMap '' (H.finalMap '' (raw side).image)) ∩ anchor.val.image) \ {r} := by
    ext z
    constructor
    · rintro ⟨⟨w,hw,hwz⟩,hzAnchor⟩
      have hzSmall : z ∉ Small := fun h => disjoint_left.mp qavoid ⟨⟨w,hw,hwz⟩,h⟩ (Or.inl hzAnchor)
      obtain ⟨q,hq⟩ := Q.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
      have hwEq : w=z := q.injective (by rw [hq,hq]; exact hwz.trans (qfix 1 z hzSmall).symm)
      subst w
      exact ⟨⟨hw,hzAnchor⟩,fun h => hzSmall ((mem_singleton_iff.mp h).symm ▸ hrSmall)⟩
    · rintro ⟨⟨hzImage,hzAnchor⟩,hn⟩
      have hzSmall : z ∉ Small := by
        intro h
        obtain ⟨w,hw,hwz⟩ := hzImage
        obtain ⟨j,hj⟩ := J.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
        have hwEq : w=z := j.injective (by rw [hj,hj]; exact hwz.trans (jN 1 z (hSmallN h)).symm)
        have hzH : z ∈ H.finalMap '' (raw side).image := hwEq ▸ hw
        have hzGraph : z ∈ H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) :=
          ⟨hzH,Or.inl hzAnchor⟩
        rw [hgraph] at hzGraph
        exact hn (mem_singleton_iff.mpr (hnode z (hSmallN h) hzGraph.1.2))
      exact ⟨⟨z,hzImage,qfix 1 z hzSmall⟩,hzAnchor⟩
  refine ⟨H,J,Q,?_,?_,?_,janchor,qAnchor,?_,jOther,?_,?_,?_⟩
  · intro t z hz
    refine ⟨hfix t z (Or.inl hz),jmarks t z hz,qfix t z ?_⟩
    intro h
    have heq : z=r := hnode z (hSmallN h) (Or.inl hz)
    exact hrMark (heq ▸ hz)
  · intro w hn hs t z hz
    exact ⟨hneighbors w hn hs t z hz,jneighbors w hn hs t z hz,
      qfix t z (fun h => disjoint_left.mp (hneighborN w hn hs) (hSmallN h) hz)⟩
  · have hqdelete :
        (Q.finalMap '' (J.finalMap '' (H.finalMap '' (raw side).image))) ∩ (P.rep x.selected).val.image =
        ((J.finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image) \ {r} := by
      ext z
      constructor
      · rintro ⟨⟨w,hw,hwz⟩,hzOld⟩
        have hzSmall : z ∉ Small := fun h => disjoint_left.mp qavoid ⟨⟨w,hw,hwz⟩,h⟩ (Or.inr hzOld)
        obtain ⟨q,hq⟩ := Q.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
        have hwEq : w=z := q.injective (by rw [hq,hq]; exact hwz.trans (qfix 1 z hzSmall).symm)
        subst w
        exact ⟨⟨hw,hzOld⟩,fun h => hzSmall ((mem_singleton_iff.mp h).symm ▸ hrSmall)⟩
      · rintro ⟨⟨hzImage,hzOld⟩,hn⟩
        have hzOriginal : z ∈ H.finalMap '' (raw side).image := by
          have hh : z ∈ (J.finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image := ⟨hzImage,hzOld⟩
          rw [jimage] at hh
          exact hh.1.1
        have hzGraph : z ∈ H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) :=
          ⟨hzOriginal,Or.inr hzOld⟩
        rw [hgraph] at hzGraph
        have hzSmall : z ∉ Small := fun h => hn (mem_singleton_iff.mpr (hnode z (hSmallN h) hzGraph.1.2))
        exact ⟨⟨z,hzImage,qfix 1 z hzSmall⟩,hzOld⟩
    rw [hqdelete,jimage]
    have hrRaw : r ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected) := by
      have ht : (x.t : Interval) ∈ Set.Icc (0 : Interval) x.t := ⟨by exact x.t.property.1,le_rfl⟩
      have hrImage : r ∈ (raw side).image := by
        rw [hraw side]
        exact Or.inl ⟨x.t,show x.t.val ≤ x.t.val from le_rfl,rfl⟩
      exact ⟨hrImage,⟨⟨mem_range_self _,hrMark⟩,⟨⟨x.s,x.same_point.symm⟩,hrMark⟩⟩⟩
    ext z
    change (((z ∈ (H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) ∧
      ¬ (z ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected) ∧ z ≠ r)) ∧ z ≠ r) ↔
      ((z ∈ (H.finalMap '' (raw side).image) ∩ (P.rep x.selected).val.image) ∧
        ¬ z ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected))
    by_cases hz : z=r
    · subst z; tauto
    · tauto
  · obtain ⟨j,hj⟩ := J.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have jinj : Function.Injective J.finalMap := by
      intro u v h
      exact j.injective (by rw [hj,hj]; exact h)
    have jMarked (z : S) : J.finalMap z ∈ (M.cover.branch : Set S) ↔ z ∈ (M.cover.branch : Set S) := by
      constructor
      · intro h
        have hfixz := jmarks 1 (J.finalMap z) h
        have he : z=J.finalMap z := (jinj hfixz).symm
        exact he.symm ▸ h
      · intro h
        have he : J.finalMap z=z := jmarks 1 z h
        exact he.symm ▸ h
    have hJcontacts :
        ((J.finalMap '' (H.finalMap '' (raw side).image)) ∩ anchor.val.image) \ (M.cover.branch : Set S) =
        J.finalMap '' (((H.finalMap '' (raw side).image) ∩ anchor.val.image) \ (M.cover.branch : Set S)) := by
      ext z
      constructor
      · rintro ⟨⟨⟨w,hw,hwz⟩,hzA⟩,hzM⟩
        refine ⟨w,⟨⟨hw,?_⟩,?_⟩,hwz⟩
        · have hwA : J.finalMap w ∈ anchor.val.image := hwz.symm ▸ hzA
          exact (janchor 1 w).mp hwA
        · intro hm
          exact hzM (hwz ▸ (jMarked w).mpr hm)
      · rintro ⟨w,⟨⟨hw,hwA⟩,hwM⟩,rfl⟩
        exact ⟨⟨⟨w,hw,rfl⟩,(janchor 1 w).mpr hwA⟩,fun hm => hwM ((jMarked w).mp hm)⟩
    have hHcontacts :
        ((H.finalMap '' (raw side).image) ∩ anchor.val.image) \ (M.cover.branch : Set S) =
        (raw side).image ∩ crossings M anchor (P.rep x.selected) := by
      ext z
      constructor
      · rintro ⟨⟨hzH,hzA⟩,hzM⟩
        have h : z ∈ H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) := ⟨hzH,Or.inl hzA⟩
        rw [hgraph] at h
        exact ⟨h.1.1,h.1.2.resolve_left hzM⟩
      · rintro ⟨hzRaw,hzC⟩
        have h : z ∈ (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ∩
            (anchor.val.image ∪ (P.rep x.selected).val.image) := ⟨⟨hzRaw,Or.inr hzC⟩,Or.inl hzC.1.1⟩
        rw [←hgraph] at h
        exact ⟨⟨h.1,hzC.1.1⟩,hzC.1.2⟩
    rw [qAnchor]
    have hcomm (A : Set S) : (A \ {r}) \ (M.cover.branch : Set S) = (A \ (M.cover.branch : Set S)) \ {r} := by
      ext z; simp only [mem_diff]; tauto
    rw [hcomm,hJcontacts,hHcontacts]
    have jr : J.finalMap r=r := jN 1 r hrN
    have hd (A : Set S) : J.finalMap '' (A \ {r}) = (J.finalMap '' A) \ {r} := by
      rw [Set.image_sdiff jinj,Set.image_singleton,jr]
    rw [←hd]
    refine ⟨Set.ncard_image_of_injective _ jinj,?_⟩
    exact ((P.finite x.selected).subset (fun z hz => hz.1.2)).image J.finalMap
  ·
    have separation (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
        (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
        (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
        (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
        (side : Bool) :
        Disjoint (((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t})
          (raw (!side)).image := by
      have closed (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
      (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
      (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
      (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
      (side : Bool) :
      (raw side).image ∩ crossings M anchor (P.rep x.selected) =
        crossings M anchor (P.rep x.selected) ∩
          (P.rep x.selected).val.map '' {r : Interval |
            if side then x.s.val ≤ r.val else r.val ≤ x.s.val} := by
        ext z
        constructor
        · rintro ⟨hz,hc⟩
          refine ⟨hc,?_⟩
          rw [hraw] at hz
          rcases hz with ⟨r,hr,he⟩ | ht
          · have hzero : r.val ≠ 0 := by
              intro h
              have hr0 : r = (0 : Interval) := Subtype.ext h
              exact hc.1.2 (he ▸ hr0 ▸ anchor.val.start_marked)
            have hrpos : 0 < r.val := lt_of_le_of_ne r.property.1 hzero.symm
            have hrEq : r = x.t := by
              apply Subtype.ext
              apply le_antisymm hr
              by_contra hn
              have hlt : r.val < x.t.val := lt_of_not_ge hn
              exact x.first x.selected r hrpos hlt (he.symm ▸ hc.2)
            refine ⟨x.s,?_,?_⟩
            · cases side <;> simp
            · exact x.same_point.symm.trans ((congrArg anchor.val.map hrEq.symm).trans he)
          · exact ht
        · rintro ⟨hc,ht⟩
          refine ⟨?_,hc⟩
          rw [hraw]
          exact Or.inr ht
      apply disjoint_left.mpr
      rintro z ⟨⟨hz,hc⟩,hn⟩ hzOther
      have hzClosed : z ∈ (raw side).image ∩ crossings M anchor (P.rep x.selected) := ⟨hz,hc⟩
      have hzOtherClosed : z ∈ (raw (!side)).image ∩ crossings M anchor (P.rep x.selected) := ⟨hzOther,hc⟩
      rw [closed M anchor F P x raw hraw side] at hzClosed
      rw [closed M anchor F P x raw hraw (!side)] at hzOtherClosed
      obtain ⟨_,r,hr,he⟩ := hzClosed
      obtain ⟨_,u,hu,he'⟩ := hzOtherClosed
      have hru : r=u := by
        rcases (P.rep x.selected).val.injective_except_loop_closure r u (he.trans he'.symm)
          with h | h | h
        · exact h
        · exact False.elim (hc.2.2 (he ▸ h.1 ▸ (P.rep x.selected).val.start_marked))
        · exact False.elim (hc.2.2 (he ▸ h.1 ▸ (P.rep x.selected).val.end_marked))
      have hrs : r=x.s := by
        apply Subtype.ext
        rw [←hru] at hu
        cases side <;> simp only [mem_setOf_eq,Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hr hu
        · exact le_antisymm hr hu
        · exact le_antisymm hu hr
      apply hn
      apply mem_singleton_iff.mpr
      exact he.symm.trans ((congrArg (P.rep x.selected).val.map hrs).trans x.same_point.symm)
    apply disjoint_left.mpr
    rintro z ⟨hzCandidate,hzUnmarked⟩ ⟨hzOther,_⟩
    have hzGraph : z ∈ anchor.val.image ∪ (P.rep x.selected).val.image := by
      have h := hzOther
      rw [hraw (!side)] at h
      rcases h with ⟨t,ht,htz⟩ | ⟨t,ht,htz⟩
      · exact Or.inl ⟨t,htz⟩
      · exact Or.inr ⟨t,htz⟩
    have hzSmall : z ∉ Small := fun h => disjoint_left.mp qavoid ⟨hzCandidate,h⟩ hzGraph
    obtain ⟨v,hv,hvz⟩ := hzCandidate
    obtain ⟨q,hq⟩ := Q.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have hvEq : v=z := q.injective (by rw [hq,hq]; exact hvz.trans (qfix 1 z hzSmall).symm)
    have hzJH : z ∈ J.finalMap '' (H.finalMap '' (raw side).image) := hvEq ▸ hv
    obtain ⟨u,hu,huz⟩ := hzJH
    obtain ⟨j,hj⟩ := J.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have huEq : u=z := j.injective (by rw [hj,hj]; exact huz.trans (jOther 1 z hzOther).symm)
    have hzH : z ∈ H.finalMap '' (raw side).image := huEq ▸ hu
    have hzOriginal : z ∈ (raw side).image ∩ ((M.cover.branch : Set S) ∪ crossings M anchor (P.rep x.selected)) ∩
        (anchor.val.image ∪ (P.rep x.selected).val.image) := hgraph ▸ ⟨hzH,hzGraph⟩
    have hzC := hzOriginal.1.2.resolve_left hzUnmarked
    have hzNotFirst : z ∉ {anchor.val.map x.t} := fun h => hzSmall ((mem_singleton_iff.mp h).symm ▸ hrSmall)
    exact disjoint_left.mp (separation M anchor F P x raw hraw side) ⟨⟨hzOriginal.1.1,hzC⟩,hzNotFirst⟩ hzOther
  · apply disjoint_left.mpr
    rintro z ⟨hzCandidate,hzUnmarked⟩ hzOld
    have hzSmall : z ∉ Small := fun h => disjoint_left.mp qavoid ⟨hzCandidate,h⟩ (Or.inr hzOld.1)
    obtain ⟨v,hv,hvz⟩ := hzCandidate
    obtain ⟨q,hq⟩ := Q.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have hvEq : v=z := q.injective (by rw [hq,hq]; exact hvz.trans (qfix 1 z hzSmall).symm)
    have hzBefore : z ∈ (J.finalMap '' (H.finalMap '' (raw side).image)) ∩ (P.rep x.selected).val.image :=
      ⟨hvEq ▸ hv,hzOld.1⟩
    rw [jimage] at hzBefore
    have hzGraph : z ∈ H.finalMap '' (raw side).image ∩ (anchor.val.image ∪ (P.rep x.selected).val.image) :=
      ⟨hzBefore.1.1,Or.inr hzOld.1⟩
    rw [hgraph] at hzGraph
    have hzC := hzGraph.1.2.resolve_left hzUnmarked
    apply hzBefore.2
    refine ⟨⟨hzGraph.1.1,hzC⟩,?_⟩
    intro h
    exact hzSmall ((mem_singleton_iff.mp h).symm ▸ hrSmall)
  ·
    have incident : ∀ (side : Bool) (v : {v // v ∈ F}) (hne : v ≠ x.selected)
      (hsimplex : IsArcSimplex M {v.val, x.selected.val}),
      Disjoint ((raw side).image \ (M.cover.branch : Set S)) (arcInterior M (P.rep v)) := by
      intro side v hne hsimplex
      apply Set.disjoint_left.mpr
      rintro p ⟨hp, hpm⟩ hpv
      rw [hraw] at hp
      rcases hp with ⟨r, hr, he⟩ | ⟨r, hr, he⟩
      · by_cases hzero : r.val = 0
        · apply hpm
          rw [← he]
          have hz : r = (0 : Interval) := Subtype.ext hzero
          exact hz ▸ anchor.val.start_marked
        have hrpos : 0 < r.val := lt_of_le_of_ne r.property.1 (Ne.symm hzero)
        by_cases ht : r.val = x.t.val
        · have heq : r = x.t := Subtype.ext ht
          have hanchor : p ∈ arcInterior M anchor := ⟨⟨r, he⟩, hpm⟩
          have hold : p ∈ arcInterior M (P.rep x.selected) := by
            refine ⟨⟨x.s, ?_⟩, hpm⟩
            exact x.same_point.symm.trans (congrArg anchor.val.map heq.symm |>.trans he)
          exact Set.disjoint_left.mp (P.distinct_crossings x.selected v hne.symm)
            ⟨hanchor, hold⟩ ⟨hanchor, hpv⟩
        · have hrlt : r.val < x.t.val := lt_of_le_of_ne hr ht
          exact x.first v r hrpos hrlt (he.symm ▸ hpv)
      · have hold : p ∈ arcInterior M (P.rep x.selected) := ⟨⟨r, he⟩, hpm⟩
        exact Set.disjoint_left.mp (P.simplex_disjoint v x.selected hne hsimplex) hpv hold
    intro w hn hs
    apply disjoint_left.mpr
    rintro z ⟨hzCandidate,hzUnmarked⟩ hzNeighbor
    have hzSmall : z ∉ Small := fun h => disjoint_left.mp (hneighborN w hn hs) (hSmallN h) hzNeighbor.1
    obtain ⟨v,hv,hvz⟩ := hzCandidate
    obtain ⟨q,hq⟩ := Q.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have hvEq : v=z := q.injective (by rw [hq,hq]; exact hvz.trans (qfix 1 z hzSmall).symm)
    obtain ⟨u,hu,huz⟩ := (hvEq ▸ hv : z ∈ J.finalMap '' (H.finalMap '' (raw side).image))
    obtain ⟨j,hj⟩ := J.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have huEq : u=z := j.injective (by rw [hj,hj]; exact huz.trans (jneighbors w hn hs 1 z hzNeighbor.1).symm)
    obtain ⟨v,hv,hvz⟩ := (huEq ▸ hu : z ∈ H.finalMap '' (raw side).image)
    obtain ⟨h,hh⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have hvEq : v=z := h.injective (by rw [hh,hh]; exact hvz.trans (hneighbors w hn hs 1 z hzNeighbor.1).symm)
    exact disjoint_left.mp (incident side w hn hs) ⟨hvEq ▸ hv,hzUnmarked⟩ hzNeighbor

theorem outermostSurgery_exists (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P) :
    Nonempty (SurgeryPair M anchor F P x) := by
  audit_base3
    classical
    have firstBranch := actualSourceSurgery_firstBranch_14 (E := E) (S := S)
    have secondBranch := actualSourceSurgery_secondBranch_13 (E := E) (S := S)
    have rawBudget (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
        (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
        (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
        (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
        (retained : Finset Bool) :
        let stem := anchor.val.map '' {r : Interval | r.val ≤ x.t.val}
        (∑ side ∈ retained, (arcInterior M anchor ∩ ((raw side).image \ stem)).ncard) <
          (crossings M anchor (P.rep x.selected)).ncard := by
      classical
      have raw_companions_overlap_only_on_prefix
          (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
          (F : Finset (EssentialArcClass M))
          (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
          (raw : Bool → MarkedArc M)
          (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side) :
          ((raw false).image ∩ (raw true).image) \ (M.cover.branch : Set S) ⊆
            anchor.val.map '' {r : Interval | r.val ≤ x.t.val} := by
        rintro p ⟨⟨hl, hr⟩, hn⟩
        rw [hraw false] at hl
        rw [hraw true] at hr
        rcases hl with hl | ⟨u, hu, hup⟩
        · exact hl
        rcases hr with hr | ⟨v, hv, hvp⟩
        · exact hr
        simp only [Bool.false_eq_true, ↓reduceIte] at hu
        simp only [↓reduceIte] at hv
        have heq : (P.rep x.selected).val.map u = (P.rep x.selected).val.map v :=
          hup.trans hvp.symm
        rcases (P.rep x.selected).val.injective_except_loop_closure u v heq with h | h | h
        · subst v
          have hus : u = x.s := Subtype.ext (le_antisymm hu hv)
          subst u
          exact ⟨x.t, show x.t.val ≤ x.t.val from le_rfl, x.same_point.trans hup⟩
        · rcases h with ⟨rfl, rfl⟩
          exact False.elim (hn (hup ▸ (P.rep x.selected).val.start_marked))
        · rcases h with ⟨rfl, rfl⟩
          exact False.elim (hn (hup ▸ (P.rep x.selected).val.end_marked))

      have raw_companions_union_eq_old_union_prefix
          (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
          (F : Finset (EssentialArcClass M))
          (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
          (raw : Bool → MarkedArc M)
          (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side) :
          (raw false).image ∪ (raw true).image =
            (P.rep x.selected).val.image ∪
              (anchor.val.map '' {r : Interval | r.val ≤ x.t.val}) := by
        rw [hraw false, hraw true]
        apply Set.Subset.antisymm
        · intro p hp
          rcases hp with (hp | ⟨u, _, hu⟩) | (hp | ⟨u, _, hu⟩)
          · exact Or.inr hp
          · exact Or.inl ⟨u, hu⟩
          · exact Or.inr hp
          · exact Or.inl ⟨u, hu⟩
        · rintro p (⟨u, rfl⟩ | hp)
          · by_cases hu : u.val ≤ x.s.val
            · exact Or.inl (Or.inr ⟨u, hu, rfl⟩)
            · exact Or.inr (Or.inr ⟨u, le_of_not_ge hu, rfl⟩)
          · exact Or.inl (Or.inl hp)

      have first_crossing_not_marked
          (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
          (F : Finset (EssentialArcClass M))
          (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P) :
          anchor.val.map x.t ∉ M.cover.branch := by
        intro h
        rcases anchor.val.marked_only_at_ends x.t h with h | h
        · have hz : x.t.val = 0 := congrArg Subtype.val h
          linarith [x.t_interior.1]
        · have hz : x.t.val = 1 := congrArg Subtype.val h
          linarith [x.t_interior.2]

      have old_crossings_on_prefix_eq_first
          (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
          (F : Finset (EssentialArcClass M))
          (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P) :
          crossings M anchor (P.rep x.selected) ∩
            (anchor.val.map '' {r : Interval | r.val ≤ x.t.val}) =
              {anchor.val.map x.t} := by
        ext p
        constructor
        · rintro ⟨hc, r, hr, rfl⟩
          have hr0 : 0 < r.val := by
            have hne : r.val ≠ 0 := by
              intro hz
              have he : r = ⟨0, by norm_num⟩ := Subtype.ext hz
              exact hc.1.2 (he ▸ anchor.val.start_marked)
            exact lt_of_le_of_ne r.property.1 (Ne.symm hne)
          have ht : r.val = x.t.val := by
            apply le_antisymm hr
            by_contra hn
            exact x.first x.selected r hr0 (lt_of_not_ge hn) hc.2
          exact congrArg anchor.val.map (Subtype.ext ht)
        · intro hp
          have he : p = anchor.val.map x.t := hp
          subst p
          have hn := first_crossing_not_marked M anchor F P x
          exact ⟨⟨⟨⟨x.t, rfl⟩, hn⟩,
            ⟨⟨x.s, x.same_point.symm⟩, hn⟩⟩,
            ⟨x.t, show x.t.val ≤ x.t.val from le_rfl, rfl⟩⟩

      have raw_residual_crossings_partition
          (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
          (F : Finset (EssentialArcClass M))
          (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
          (raw : Bool → MarkedArc M)
          (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side) :
          let stem := anchor.val.map '' {r : Interval | r.val ≤ x.t.val}
          let L := arcInterior M anchor ∩ ((raw false).image \ stem)
          let T := arcInterior M anchor ∩ ((raw true).image \ stem)
          L.Finite ∧ T.Finite ∧ Disjoint L T ∧
            L ∪ T = crossings M anchor (P.rep x.selected) \ {anchor.val.map x.t} := by
        dsimp only
        let stem := anchor.val.map '' {r : Interval | r.val ≤ x.t.val}
        have hu := raw_companions_union_eq_old_union_prefix M anchor F P x raw hraw
        have hsub (i : Bool) :
            arcInterior M anchor ∩ ((raw i).image \ stem) ⊆
              crossings M anchor (P.rep x.selected) := by
          rintro p ⟨ha, hi, hn⟩
          have hp : p ∈ (raw false).image ∪ (raw true).image := by
            cases i
            · exact Or.inl hi
            · exact Or.inr hi
          rw [hu] at hp
          exact ⟨ha, hp.resolve_right hn, ha.2⟩
        refine ⟨(P.finite x.selected).subset (hsub false),
          (P.finite x.selected).subset (hsub true), ?_, ?_⟩
        · apply Set.disjoint_left.mpr
          rintro p ⟨ha, hl, hn⟩ ⟨_, ht, _⟩
          exact hn (raw_companions_overlap_only_on_prefix M anchor F P x raw hraw
            ⟨⟨hl, ht⟩, ha.2⟩)
        · ext p
          constructor
          · intro hp
            have hc : p ∈ crossings M anchor (P.rep x.selected) := by
              rcases hp with hp | hp
              · exact hsub false hp
              · exact hsub true hp
            refine ⟨hc, ?_⟩
            intro he
            have hpre : p ∈ stem := by
              have heq : p = anchor.val.map x.t := he
              exact heq ▸ ⟨x.t, show x.t.val ≤ x.t.val from le_rfl, rfl⟩
            rcases hp with hp | hp <;> exact hp.2.2 hpre
          · rintro ⟨hc, hn⟩
            have hpre : p ∉ stem := by
              intro hp
              have he := old_crossings_on_prefix_eq_first M anchor F P x
              exact hn (he ▸ ⟨hc, hp⟩)
            have hp : p ∈ (raw false).image ∪ (raw true).image := by
              rw [hu]
              exact Or.inl hc.2.1
            rcases hp with hp | hp
            · exact Or.inl ⟨hc.1, hp, hpre⟩
            · exact Or.inr ⟨hc.1, hp, hpre⟩

      have raw_residual_crossings_exact_budget
          (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
          (F : Finset (EssentialArcClass M))
          (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
          (raw : Bool → MarkedArc M)
          (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side) :
          let stem := anchor.val.map '' {r : Interval | r.val ≤ x.t.val}
          (arcInterior M anchor ∩ ((raw false).image \ stem)).ncard +
            (arcInterior M anchor ∩ ((raw true).image \ stem)).ncard + 1 =
              (crossings M anchor (P.rep x.selected)).ncard := by
        dsimp only
        obtain ⟨hL, hT, hd, hu⟩ := raw_residual_crossings_partition M anchor F P x raw hraw
        have hm : anchor.val.map x.t ∈ crossings M anchor (P.rep x.selected) := by
          have hn := first_crossing_not_marked M anchor F P x
          exact ⟨⟨⟨x.t, rfl⟩, hn⟩, ⟨⟨x.s, x.same_point.symm⟩, hn⟩⟩
        rw [← Set.ncard_union_eq hd hL hT, hu]
        exact Set.ncard_sdiff_singleton_add_one hm (P.finite x.selected)

      let stem := anchor.val.map '' {r : Interval | r.val ≤ x.t.val}
      have budget := raw_residual_crossings_exact_budget M anchor F P x raw hraw
      change (arcInterior M anchor ∩ ((raw false).image \ stem)).ncard +
        (arcInterior M anchor ∩ ((raw true).image \ stem)).ncard + 1 = _ at budget
      have hle : (∑ side ∈ retained, (arcInterior M anchor ∩ ((raw side).image \ stem)).ncard) ≤
          ∑ side : Bool, (arcInterior M anchor ∩ ((raw side).image \ stem)).ncard :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ retained) (fun _ _ _ => Nat.zero_le _)
      rw [Fintype.sum_bool] at hle
      change (∑ side ∈ retained, (arcInterior M anchor ∩ ((raw side).image \ stem)).ncard) < (crossings M anchor (P.rep x.selected)).ncard
      omega
    have residualContact (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
        (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
        (x : FirstCrossing M anchor F P) (raw : Bool → MarkedArc M)
        (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side)
        (side : Bool) :
        ((raw side).image ∩ crossings M anchor (P.rep x.selected)) \ {anchor.val.map x.t} =
          arcInterior M anchor ∩ ((raw side).image \ (anchor.val.map '' {r : Interval | r.val ≤ x.t.val})) := by
      classical
      have raw_companions_overlap_only_on_prefix
          (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
          (F : Finset (EssentialArcClass M))
          (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
          (raw : Bool → MarkedArc M)
          (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side) :
          ((raw false).image ∩ (raw true).image) \ (M.cover.branch : Set S) ⊆
            anchor.val.map '' {r : Interval | r.val ≤ x.t.val} := by
        rintro p ⟨⟨hl, hr⟩, hn⟩
        rw [hraw false] at hl
        rw [hraw true] at hr
        rcases hl with hl | ⟨u, hu, hup⟩
        · exact hl
        rcases hr with hr | ⟨v, hv, hvp⟩
        · exact hr
        simp only [Bool.false_eq_true, ↓reduceIte] at hu
        simp only [↓reduceIte] at hv
        have heq : (P.rep x.selected).val.map u = (P.rep x.selected).val.map v :=
          hup.trans hvp.symm
        rcases (P.rep x.selected).val.injective_except_loop_closure u v heq with h | h | h
        · subst v
          have hus : u = x.s := Subtype.ext (le_antisymm hu hv)
          subst u
          exact ⟨x.t, show x.t.val ≤ x.t.val from le_rfl, x.same_point.trans hup⟩
        · rcases h with ⟨rfl, rfl⟩
          exact False.elim (hn (hup ▸ (P.rep x.selected).val.start_marked))
        · rcases h with ⟨rfl, rfl⟩
          exact False.elim (hn (hup ▸ (P.rep x.selected).val.end_marked))

      have raw_companions_union_eq_old_union_prefix
          (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
          (F : Finset (EssentialArcClass M))
          (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
          (raw : Bool → MarkedArc M)
          (hraw : ∀ side, (raw side).image = spliceTrace M anchor (P.rep x.selected) x.t x.s side) :
          (raw false).image ∪ (raw true).image =
            (P.rep x.selected).val.image ∪
              (anchor.val.map '' {r : Interval | r.val ≤ x.t.val}) := by
        rw [hraw false, hraw true]
        apply Set.Subset.antisymm
        · intro p hp
          rcases hp with (hp | ⟨u, _, hu⟩) | (hp | ⟨u, _, hu⟩)
          · exact Or.inr hp
          · exact Or.inl ⟨u, hu⟩
          · exact Or.inr hp
          · exact Or.inl ⟨u, hu⟩
        · rintro p (⟨u, rfl⟩ | hp)
          · by_cases hu : u.val ≤ x.s.val
            · exact Or.inl (Or.inr ⟨u, hu, rfl⟩)
            · exact Or.inr (Or.inr ⟨u, le_of_not_ge hu, rfl⟩)
          · exact Or.inl (Or.inl hp)

      have first_crossing_not_marked
          (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
          (F : Finset (EssentialArcClass M))
          (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P) :
          anchor.val.map x.t ∉ M.cover.branch := by
        intro h
        rcases anchor.val.marked_only_at_ends x.t h with h | h
        · have hz : x.t.val = 0 := congrArg Subtype.val h
          linarith [x.t_interior.1]
        · have hz : x.t.val = 1 := congrArg Subtype.val h
          linarith [x.t_interior.2]

      have old_crossings_on_prefix_eq_first
          (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
          (F : Finset (EssentialArcClass M))
          (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P) :
          crossings M anchor (P.rep x.selected) ∩
            (anchor.val.map '' {r : Interval | r.val ≤ x.t.val}) =
              {anchor.val.map x.t} := by
        ext p
        constructor
        · rintro ⟨hc, r, hr, rfl⟩
          have hr0 : 0 < r.val := by
            have hne : r.val ≠ 0 := by
              intro hz
              have he : r = ⟨0, by norm_num⟩ := Subtype.ext hz
              exact hc.1.2 (he ▸ anchor.val.start_marked)
            exact lt_of_le_of_ne r.property.1 (Ne.symm hne)
          have ht : r.val = x.t.val := by
            apply le_antisymm hr
            by_contra hn
            exact x.first x.selected r hr0 (lt_of_not_ge hn) hc.2
          exact congrArg anchor.val.map (Subtype.ext ht)
        · intro hp
          have he : p = anchor.val.map x.t := hp
          subst p
          have hn := first_crossing_not_marked M anchor F P x
          exact ⟨⟨⟨⟨x.t, rfl⟩, hn⟩,
            ⟨⟨x.s, x.same_point.symm⟩, hn⟩⟩,
            ⟨x.t, show x.t.val ≤ x.t.val from le_rfl, rfl⟩⟩

      ext z
      constructor
      · rintro ⟨⟨hzRaw,hzC⟩,hn⟩
        refine ⟨hzC.1,hzRaw,?_⟩
        intro hzStem
        have h := old_crossings_on_prefix_eq_first M anchor F P x
        exact hn (h ▸ ⟨hzC,hzStem⟩)
      · rintro ⟨hzAnchor,hzRaw,hzNotStem⟩
        have hzOld : z ∈ (P.rep x.selected).val.image := by
          rw [hraw side] at hzRaw
          obtain ⟨t,ht,htz⟩ := hzRaw.resolve_left hzNotStem
          exact ⟨t,htz⟩
        refine ⟨⟨hzRaw,⟨hzAnchor,hzOld,hzAnchor.2⟩⟩,?_⟩
        intro hzFirst
        have he : z=anchor.val.map x.t := mem_singleton_iff.mp hzFirst
        exact hzNotStem (he.symm ▸ ⟨x.t,show x.t.val ≤ x.t.val from le_rfl,rfl⟩)
    obtain ⟨raw,hraw,hstart,hend⟩ := rawSplices_exists M anchor F P x
    obtain ⟨H₀,J₀,Q₀,hm₀,hn₀,ho₀,ja₀,qa₀,hc₀,jother₀,hsep₀,hdold₀,hdneigh₀⟩ :=
      firstBranch M anchor F P x raw hraw false
    let K₀ := (H₀.compose J₀).compose Q₀
    have tripleImage (H J Q : AmbientIsotopy S) (A : Set S) :
        ((H.compose J).compose Q).finalMap '' A = Q.finalMap '' (J.finalMap '' (H.finalMap '' A)) := by
      change (Q.finalMap ∘ J.finalMap ∘ H.finalMap) '' A = _
      rw [Set.image_comp,Set.image_comp]
    have kp₀ (A : Set S) : K₀.finalMap '' A=Q₀.finalMap '' (J₀.finalMap '' (H₀.finalMap '' A)) := tripleImage _ _ _ _
    have km₀ : ∀ t z, z ∈ (M.cover.branch : Set S) → K₀.map (t,z)=z := by
      intro t z hz
      change Q₀.map (t,J₀.map (t,H₀.map (t,z)))=z
      rw [(hm₀ t z hz).1,(hm₀ t z hz).2.1,(hm₀ t z hz).2.2]
    let Obstacle := K₀.finalMap '' (raw false).image
    have hi₀ : Obstacle=Q₀.finalMap '' (J₀.finalMap '' (H₀.finalMap '' (raw false).image)) :=
      tripleImage H₀ J₀ Q₀ _
    have hs₀ : Disjoint (Obstacle \ (M.cover.branch : Set S))
        ((raw true).image \ (M.cover.branch : Set S)) := by simpa only [hi₀,Bool.not_false] using hsep₀
    letI : T2Space S := M.sphere.symm.t2Space
    letI : CompactSpace S := M.sphere.symm.compactSpace
    letI : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc
    have hObstacle : IsClosed Obstacle :=
      ((isCompact_range (raw false).continuous).image
        (K₀.map.continuous.comp (continuous_const.prodMk continuous_id))).isClosed
    have hrawObstacle : (raw true).image ∩ Obstacle ⊆ (M.cover.branch : Set S) := by
      rintro z ⟨hz,hb⟩
      by_contra hm
      exact disjoint_left.mp hs₀ ⟨hb,hm⟩ ⟨hz,hm⟩
    let r := anchor.val.map x.t
    have hrMark : r ∉ (M.cover.branch : Set S) := by
      intro h
      rcases anchor.val.marked_only_at_ends x.t h with h | h
      · exact (ne_of_gt x.t_interior.1) (congrArg Subtype.val h)
      · exact (ne_of_lt x.t_interior.2) (congrArg Subtype.val h)
    have hrRaw : r ∈ (raw true).image := by
      rw [hraw true]
      exact Or.inl ⟨x.t,show x.t.val ≤ x.t.val from le_rfl,rfl⟩
    have hrObstacle : r ∉ Obstacle := fun h => disjoint_left.mp hs₀ ⟨h,hrMark⟩ ⟨hrRaw,hrMark⟩
    obtain ⟨H₁,J₁,Q₁,hm₁,hn₁,hfix₁,ho₁,ja₁,qa₁,hc₁,hdold₁,hdneigh₁⟩ :=
      secondBranch M anchor F P x raw hraw true Obstacle hObstacle hrawObstacle hrObstacle
    let K₁ := (H₁.compose J₁).compose Q₁
    have kp₁ (A : Set S) : K₁.finalMap '' A=Q₁.finalMap '' (J₁.finalMap '' (H₁.finalMap '' A)) := tripleImage _ _ _ _
    have km₁ : ∀ t z, z ∈ (M.cover.branch : Set S) → K₁.map (t,z)=z := by
      intro t z hz
      change Q₁.map (t,J₁.map (t,H₁.map (t,z)))=z
      rw [(hm₁ t z hz).1,(hm₁ t z hz).2.1,(hm₁ t z hz).2.2]
    have ko₁ : ∀ t z, z ∈ Obstacle → K₁.map (t,z)=z := by
      intro t z hz
      change Q₁.map (t,J₁.map (t,H₁.map (t,z)))=z
      rw [(hfix₁ t z hz).1,(hfix₁ t z hz).2.1,(hfix₁ t z hz).2.2]
    let K : Bool → AmbientIsotopy S := fun i => if i then K₁ else K₀
    have km (i : Bool) : ∀ t z, z ∈ (M.cover.branch : Set S) → (K i).map (t,z)=z := by
      cases i
      · exact km₀
      · exact km₁
    choose f hf using fun i : Bool => (K i).homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have ff (i : Bool) (z : S) : f i z=(K i).finalMap z := hf i z
    have fm (i : Bool) : ∀ z, z ∈ (M.cover.branch : Set S) → f i z=z :=
      fun z hz => (ff i z).trans (km i 1 z hz)
    let retained := Finset.univ.filter (fun i : Bool => IsEssentialMarkedArc M (raw i))
    have retained_iff (i : Bool) : i ∈ retained ↔ IsEssentialMarkedArc M (raw i) := by simp [retained]
    have hret : retained.Nonempty := by
      obtain ⟨i,hi⟩ := rawSplices_essential_nonempty M anchor F P x raw hraw hstart hend
      exact ⟨i,(retained_iff i).mpr hi⟩
    let pushed (i : {i // i ∈ retained}) : EssentialMarkedArc M :=
      EssentialMarkedArc.transport (⟨raw i.val,(retained_iff i.val).mp i.property⟩ : EssentialMarkedArc M) (f i.val) (fm i.val)
    have imageP (i : {i // i ∈ retained}) : (pushed i).val.image=(K i.val).finalMap '' (raw i.val).image := by
      change ((raw i.val).transport (f i.val) (fm i.val)).image = _
      rw [MarkedArc.transport_image]
      exact congrArg (fun g : S → S => g '' (raw i.val).image) (funext (ff i.val))
    have isotopy (i : {i // i ∈ retained}) : MarkedIsotopyRel M (raw i.val).image (pushed i).val.image :=
      ⟨K i.val,km i.val,(imageP i).symm⟩
    have interiorP (i : {i // i ∈ retained}) : arcInterior M (pushed i)=
        ((K i.val).finalMap '' (raw i.val).image) \ (M.cover.branch : Set S) := by
      change (pushed i).val.image \ (M.cover.branch : Set S)=_
      rw [imageP]
    have pair : Disjoint (Obstacle \ (M.cover.branch : Set S))
        ((K₁.finalMap '' (raw true).image) \ (M.cover.branch : Set S)) := by
      apply disjoint_left.mpr
      rintro z ⟨hz,hzm⟩ ⟨⟨w,hw,hwz⟩,_⟩
      obtain ⟨k,hk⟩ := K₁.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
      have hwEq : w=z := k.injective (by rw [hk,hk]; exact hwz.trans (ko₁ 1 z hz).symm)
      exact disjoint_left.mp hs₀ ⟨hz,hzm⟩ ⟨hwEq ▸ hw,hzm⟩
    have pairwise (i j : {i // i ∈ retained}) (hne : i ≠ j) :
        Disjoint (arcInterior M (pushed i)) (arcInterior M (pushed j)) := by
      have hv : i.val ≠ j.val := fun h => hne (Subtype.ext h)
      rw [interiorP i,interiorP j]
      cases hi : i.val <;> cases hj : j.val
      · exact False.elim (hv (hi.trans hj.symm))
      · simpa only [K,hi,hj,Bool.false_eq_true,ite_false,ite_true] using pair
      · simpa only [K,hi,hj,Bool.false_eq_true,ite_false,ite_true] using pair.symm
      · exact False.elim (hv (hi.trans hj.symm))
    have old (i : {i // i ∈ retained}) : Disjoint (arcInterior M (pushed i)) (arcInterior M (P.rep x.selected)) := by
      rw [interiorP]
      cases hi : i.val
      · simpa only [K,hi,Bool.false_eq_true,ite_false,kp₀,kp₁] using hdold₀
      · simpa only [K,hi,ite_true,kp₀,kp₁] using hdold₁
    have neighbors (i : {i // i ∈ retained}) (v : {v // v ∈ F}) (hn : v ≠ x.selected)
        (hs : IsArcSimplex M {v.val,x.selected.val}) :
        Disjoint (arcInterior M (pushed i)) (arcInterior M (P.rep v)) := by
      rw [interiorP]
      cases hi : i.val
      · simpa only [K,hi,Bool.false_eq_true,ite_false,kp₀,kp₁] using hdneigh₀ v hn hs
      · simpa only [K,hi,ite_true,kp₀,kp₁] using hdneigh₁ v hn hs
    let stem := anchor.val.map '' {t : Interval | t.val ≤ x.t.val}
    let residual (i : Bool) := arcInterior M anchor ∩ ((raw i).image \ stem)
    have contactP (i : {i // i ∈ retained}) : crossings M anchor (pushed i)=
        (((K i.val).finalMap '' (raw i.val).image) ∩ anchor.val.image) \ (M.cover.branch : Set S) := by
      rw [crossings,interiorP]
      change (anchor.val.image \ (M.cover.branch : Set S)) ∩ _ = _
      ext z; simp only [mem_inter_iff,mem_diff]; tauto
    have finite (i : {i // i ∈ retained}) : (crossings M anchor (pushed i)).Finite := by
      rw [contactP]
      cases hi : i.val
      · simpa only [K,hi,Bool.false_eq_true,ite_false,kp₀,kp₁] using hc₀.2
      · simpa only [K,hi,ite_true,kp₀,kp₁] using hc₁.2
    have count (i : {i // i ∈ retained}) : (crossings M anchor (pushed i)).ncard=(residual i.val).ncard := by
      rw [contactP]
      have rawId := residualContact M anchor F P x raw hraw i.val
      cases hi : i.val
      · have h := hc₀.1.trans (congrArg Set.ncard (hi ▸ rawId))
        simpa only [K,hi,Bool.false_eq_true,ite_false,kp₀,kp₁,residual,stem] using h
      · have h := hc₁.1.trans (congrArg Set.ncard (hi ▸ rawId))
        simpa only [K,hi,ite_true,kp₀,kp₁,residual,stem] using h
    have decreases (i : {i // i ∈ retained}) : (crossings M anchor (pushed i)).ncard <
        (crossings M anchor (P.rep x.selected)).ncard := by
      rw [count]
      simpa only [residual,stem,Finset.sum_singleton] using rawBudget M anchor F P x raw hraw {i.val}
    have total : (∑ i ∈ retained.attach, (crossings M anchor (pushed i)).ncard) <
        (crossings M anchor (P.rep x.selected)).ncard := by
      have h := rawBudget M anchor F P x raw hraw retained
      have he : (∑ i ∈ retained.attach, (crossings M anchor (pushed i)).ncard)=
          ∑ i ∈ retained, (residual i).ncard := by
        simp only [count]
        exact Finset.sum_attach retained (fun i => (residual i).ncard)
      rw [he]
      exact h
    exact ⟨{
      raw := raw
      raw_trace := hraw
      raw_start := hstart
      raw_end := hend
      retained := retained
      retained_iff := retained_iff
      nonempty := hret
      pushed := pushed
      push_isotopy := isotopy
      pushed_disjoint := pairwise
      disjoint_old := old
      disjoint_neighbors := neighbors
      finite := finite
      decreases := decreases
      total_decreases := total }⟩
end CurveComplex.HyperellipticModel.ArcSurgery
