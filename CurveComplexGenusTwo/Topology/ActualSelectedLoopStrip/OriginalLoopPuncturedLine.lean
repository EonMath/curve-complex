import CurveComplexGenusTwo.Intersection.SphereChart
import Mathlib

namespace CurveComplex.HyperellipticModel

open Set Topology

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private abbrev OpenInterval := Set.Ioo (0 : Interval) 1

/- The original parameter is retained; only the two copies of its common
   endpoint are deleted from the domain and from the sphere. -/
noncomputable def originalLoopPuncturedLine
    (M : HyperellipticModel E S) (a : MarkedArc M)
    (_ha : a.map 0 = a.map 1) :
    OpenInterval → {x : S // x ≠ a.map 0} := fun t =>
  ⟨a.map t, by
    intro h
    rcases a.injective_except_loop_closure t 0 h with he | he | he
    · exact (ne_of_gt t.property.1) he
    · exact (ne_of_gt t.property.1) he.1
    · exact (ne_of_lt t.property.2) he.1⟩

theorem originalLoopPuncturedLine_closedEmbedding
    (M : HyperellipticModel E S) (a : MarkedArc M)
    (ha : a.map 0 = a.map 1) :
    IsClosedEmbedding (originalLoopPuncturedLine M a ha) := by
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  letI : LocallyCompactSpace S := M.sphere.isOpenEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace {x : S // x ≠ a.map 0} :=
    (show IsOpen ({a.map 0}ᶜ : Set S) from isClosed_singleton.isOpen_compl).isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hcont : Continuous (originalLoopPuncturedLine M a ha) := by
    exact (a.continuous.comp continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective (originalLoopPuncturedLine M a ha) := by
    intro t u h
    apply Subtype.ext
    have hmap : a.map t = a.map u := congrArg Subtype.val h
    rcases a.injective_except_loop_closure t u hmap with he | he | he
    · exact he
    · exact False.elim ((ne_of_gt t.property.1) he.1)
    · exact False.elim ((ne_of_lt t.property.2) he.1)
  have hproper : IsProperMap (originalLoopPuncturedLine M a ha) := by
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨hcont, ?_⟩
    intro K hK
    let Kimg : Set S := (fun x : {x : S // x ≠ a.map 0} => (x : S)) '' K
    let C : Set Interval := a.map ⁻¹' Kimg
    have hKC : IsCompact Kimg :=
      hK.image continuous_subtype_val
    have hC : IsCompact C := (hKC.isClosed.preimage a.continuous).isCompact
    have hpnot : a.map 0 ∉ Kimg := by
      rintro ⟨x, hxK, hx⟩
      exact x.property hx
    have hCopen : C ⊆ OpenInterval := by
      intro t ht
      have h0 : t ≠ 0 := by
        intro he
        subst t
        exact hpnot ht
      have h1 : t ≠ 1 := by
        intro he
        subst t
        exact hpnot (ha ▸ ht)
      exact ⟨lt_of_le_of_ne t.property.1 h0.symm, lt_of_le_of_ne t.property.2 h1⟩
    have himage : Subtype.val '' ((originalLoopPuncturedLine M a ha) ⁻¹' K) = C := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨originalLoopPuncturedLine M a ha u, hu, rfl⟩
      · intro ht
        let u : OpenInterval := ⟨t, hCopen ht⟩
        obtain ⟨x, hxK, hx⟩ : a.map t ∈ Kimg := ht
        have he : originalLoopPuncturedLine M a ha u = x := Subtype.ext hx.symm
        exact ⟨u, by simpa [he] using hxK, rfl⟩
    exact Subtype.isCompact_iff.mpr (himage ▸ hC)
  exact IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
    ⟨hcont, hinj, hproper.isClosedMap⟩

theorem originalLoopPuncturedLine_range
    (M : HyperellipticModel E S) (a : MarkedArc M)
    (ha : a.map 0 = a.map 1) :
    Set.range (fun t : OpenInterval =>
      ((originalLoopPuncturedLine M a ha t : {x : S // x ≠ a.map 0}) : S)) =
      a.image \ {a.map 0} := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨t, rfl⟩, (originalLoopPuncturedLine M a ha t).property⟩
  · rintro ⟨⟨t, ht⟩, hx⟩
    have ht0 : t ≠ 0 := by
      intro he
      exact hx (he ▸ ht.symm)
    have ht1 : t ≠ 1 := by
      intro he
      exact hx (ha.symm ▸ (he ▸ ht.symm))
    have hti : t ∈ OpenInterval :=
      ⟨lt_of_le_of_ne t.property.1 ht0.symm,
        lt_of_le_of_ne t.property.2 ht1⟩
    refine ⟨⟨t, hti⟩, ?_⟩
    exact ht

theorem originalLoopPuncturedLines_disjoint
    (M : HyperellipticModel E S) (a b : MarkedArc M)
    (ha : a.map 0 = a.map 1) (hb : b.map 0 = b.map 1)
    (_hbase : a.map 0 = b.map 0)
    (hmeet : a.image ∩ b.image = {a.map 0}) :
    Disjoint (Set.range (fun t : OpenInterval =>
      ((originalLoopPuncturedLine M a ha t : {x : S // x ≠ a.map 0}) : S)))
      (Set.range (fun t : OpenInterval =>
        ((originalLoopPuncturedLine M b hb t : {x : S // x ≠ b.map 0}) : S))) := by
  rw [originalLoopPuncturedLine_range M a ha,
    originalLoopPuncturedLine_range M b hb]
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  have hxbase : x ∈ ({a.map 0} : Set S) := hmeet ▸ ⟨hxa.1, hxb.1⟩
  exact hxa.2 hxbase

noncomputable def originalLoopRealParameter : ℝ ≃ₜ OpenInterval := by
  let affine : Set.Ioo (-1 : ℝ) 1 ≃ₜ OpenInterval := {
    toFun x := ⟨⟨(x.val + 1) / 2, by
      constructor <;> linarith [x.property.1, x.property.2]⟩,
      by
        constructor
        · change (0 : ℝ) < (x.val + 1) / 2
          linarith [x.property.1]
        · change (x.val + 1) / 2 < (1 : ℝ)
          linarith [x.property.2]⟩
    invFun y := ⟨2 * (y.val : ℝ) - 1, by
      constructor
      · change (-1 : ℝ) < 2 * (y.val : ℝ) - 1
        have hy : (0 : ℝ) < (y.val : ℝ) := y.property.1
        linarith
      · change 2 * (y.val : ℝ) - 1 < (1 : ℝ)
        have hy : (y.val : ℝ) < 1 := y.property.2
        linarith⟩
    left_inv x := by
      apply Subtype.ext
      dsimp
      ring
    right_inv y := by
      apply Subtype.ext
      apply Subtype.ext
      dsimp
      ring
    continuous_toFun := by
      fun_prop
    continuous_invFun := by
      fun_prop }
  exact (orderIsoIooNegOneOne ℝ).toHomeomorph.trans affine

theorem originalLoopRealLine_closedEmbedding
    (M : HyperellipticModel E S) (a : MarkedArc M)
    (ha : a.map 0 = a.map 1) :
    IsClosedEmbedding
      (fun t : ℝ => originalLoopPuncturedLine M a ha (originalLoopRealParameter t)) := by
  exact (originalLoopPuncturedLine_closedEmbedding M a ha).comp
    originalLoopRealParameter.isClosedEmbedding

noncomputable def originalLoopPlanarLine
    (M : HyperellipticModel E S) (a : MarkedArc M)
    (ha : a.map 0 = a.map 1) : C(ℝ, Schoenflies.Plane) :=
  ⟨fun t => M.puncturedPlane (a.map 0)
      (originalLoopPuncturedLine M a ha (originalLoopRealParameter t)),
    (M.puncturedPlane (a.map 0)).continuous.comp
      (originalLoopRealLine_closedEmbedding M a ha).continuous⟩

theorem originalLoopPlanarLine_closedEmbedding
    (M : HyperellipticModel E S) (a : MarkedArc M)
    (ha : a.map 0 = a.map 1) :
    IsClosedEmbedding (originalLoopPlanarLine M a ha) := by
  exact (M.puncturedPlane (a.map 0)).isClosedEmbedding.comp
    (originalLoopRealLine_closedEmbedding M a ha)

noncomputable def originalLoopPlanarLineAt
    (M : HyperellipticModel E S) (p : S) (a : MarkedArc M)
    (ha : a.map 0 = a.map 1) (hp : a.map 0 = p) :
    C(ℝ, Schoenflies.Plane) :=
  ⟨fun t => M.puncturedPlane p
      ⟨a.map (originalLoopRealParameter t), by
        intro he
        exact (originalLoopPuncturedLine M a ha (originalLoopRealParameter t)).property
          (he.trans hp.symm)⟩,
    by
      apply (M.puncturedPlane p).continuous.comp
      exact ((a.continuous.comp continuous_subtype_val).comp
        originalLoopRealParameter.continuous).subtype_mk _⟩

theorem originalLoopPlanarLineAt_closedEmbedding
    (M : HyperellipticModel E S) (p : S) (a : MarkedArc M)
    (ha : a.map 0 = a.map 1) (hp : a.map 0 = p) :
    IsClosedEmbedding (originalLoopPlanarLineAt M p a ha hp) := by
  subst p
  have he : (originalLoopPlanarLineAt M (a.map 0) a ha rfl :
      ℝ → Schoenflies.Plane) = originalLoopPlanarLine M a ha := by
    funext t
    rfl
  rw [he]
  exact originalLoopPlanarLine_closedEmbedding M a ha

theorem originalLoopPlanarLinesAt_disjoint
    (M : HyperellipticModel E S) (p : S) (a b : MarkedArc M)
    (ha : a.map 0 = a.map 1) (hb : b.map 0 = b.map 1)
    (hap : a.map 0 = p) (hbp : b.map 0 = p)
    (hmeet : a.image ∩ b.image = {p}) :
    Disjoint (Set.range (originalLoopPlanarLineAt M p a ha hap))
      (Set.range (originalLoopPlanarLineAt M p b hb hbp)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, he⟩ := hy
  let A : {x : S // x ≠ p} :=
    ⟨a.map (originalLoopRealParameter s), by
      intro heq
      exact (originalLoopPuncturedLine M a ha (originalLoopRealParameter s)).property
        (heq.trans hap.symm)⟩
  let B : {x : S // x ≠ p} :=
    ⟨b.map (originalLoopRealParameter t), by
      intro heq
      exact (originalLoopPuncturedLine M b hb (originalLoopRealParameter t)).property
        (heq.trans hbp.symm)⟩
  have hpoint : a.map (originalLoopRealParameter s) =
      b.map (originalLoopRealParameter t) := by
    have he' : M.puncturedPlane p A = M.puncturedPlane p B := by
      simpa only [originalLoopPlanarLineAt, ContinuousMap.coe_mk, A, B] using he.symm
    exact congrArg Subtype.val ((M.puncturedPlane p).injective he')
  have hbaseMem : a.map (originalLoopRealParameter s) ∈ ({p} : Set S) :=
    hmeet ▸ ⟨⟨_, rfl⟩, ⟨_, hpoint.symm⟩⟩
  exact (originalLoopPuncturedLine M a ha (originalLoopRealParameter s)).property
    ((Set.mem_singleton_iff.mp hbaseMem).trans hap.symm)

end CurveComplex.HyperellipticModel
