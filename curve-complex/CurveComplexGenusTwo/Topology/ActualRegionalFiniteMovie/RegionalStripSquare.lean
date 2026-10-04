import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalSquareCrosscutMovie
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualStripSurfaceChart

open CurveComplex Set Topology Schoenflies

namespace RegionalFinitePosition

noncomputable def squareToStrip (z : Square) : Interval × Set.Icc (-1:ℝ) 1 :=
  (⟨(z.val 0+1)/2,by
    have h := mem_closedSquare_zero_one.mp z.property
    have h0 : |z.val 0| ≤ 1 := (le_max_left _ _).trans h
    have h0 := abs_le.mp h0
    constructor <;> linarith [h0.1,h0.2]⟩,
   ⟨z.val 1,by
    have h := mem_closedSquare_zero_one.mp z.property
    exact abs_le.mp ((le_max_right _ _).trans h)⟩)

theorem squareToStrip_continuous : Continuous squareToStrip := by
  apply Continuous.prodMk <;> apply Continuous.subtype_mk <;> fun_prop

theorem squareToStrip_injective : Function.Injective squareToStrip := by
  intro z w h
  have h0 := congrArg (fun q : Interval × Set.Icc (-1:ℝ) 1 => (q.1:ℝ)) h
  have h1 := congrArg (fun q : Interval × Set.Icc (-1:ℝ) 1 => (q.2:ℝ)) h
  apply Subtype.ext
  ext i
  fin_cases i
  · change z.val 0 = w.val 0
    dsimp [squareToStrip] at h0
    linarith
  · exact h1

theorem squareToStrip_surjective : Function.Surjective squareToStrip := by
  intro z
  refine ⟨⟨Plane.mk (2*(z.1:ℝ)-1) z.2,?_⟩,?_⟩
  · apply mem_closedSquare_zero_one.mpr
    change max |2*(z.1:ℝ)-1| |(z.2:ℝ)| ≤ 1
    rw [max_le_iff,abs_le,abs_le]
    constructor
    · constructor <;> linarith [z.1.property.1,z.1.property.2]
    · exact z.2.property
  · apply Prod.ext
    · apply Subtype.ext
      change (2*(z.1:ℝ)-1+1)/2 = z.1
      ring
    · rfl

theorem squareToStrip_horizontal (s : Interval) :
    squareToStrip (horizontalPoint s) = (s,⟨0,by norm_num⟩) := by
  apply Prod.ext
  · apply Subtype.ext
    change (2*(s:ℝ)-1+1)/2 = s
    ring
  · rfl

noncomputable def normalizePlane : Plane ≃ₜ Plane where
  toFun z := Plane.mk ((z 0+1)/2) (z 1)
  invFun z := Plane.mk (2*z 0-1) (z 1)
  left_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk] <;> ring
  right_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk] <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem strip_square_package
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (F : Set S) (b : C(Interval, ↥F))
    (E : C(Interval × Set.Icc (-1:ℝ) 1, ↥F)) (hE : IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = b t)
    (hend : ∀ w, (E (0,w)).val ∈ frontier F ∧ (E (1,w)).val ∈ frontier F)
    (hint : ∀ t ∈ Ioo (0:Interval) 1, ∀ w, (E (t,w)).val ∉ frontier F)
    (hopen : IsOpen (E '' {z | (-1:ℝ) < z.2.val ∧ z.2.val < 1})) :
    ∃ D : C(Square, ↥F), IsEmbedding D ∧
      (∀ s, D (horizontalPoint s) = b s) ∧
      (∀ z : Square, z.val ∈ Plane.openSquare 0 1 → (D z).val ∉ frontier F) ∧
      (∀ z : Square, |z.val 1| < 1 → (D z).val ∉ frontier F →
        z.val ∈ Plane.openSquare 0 1) ∧
      IsOpen (D '' {z : Square | |z.val 1| < 1}) ∧
      ∃ P : OpenPartialHomeomorph Plane S,
        P.source = Plane.openSquare 0 1 ∧
        ∀ z : Square, z.val ∈ Plane.openSquare 0 1 → P z.val = (D z).val := by
  letI : CompactSpace Square := isCompact_iff_compactSpace.mp (Schoenflies.isCompact_closedSquare (0 : Plane) (1 : ℝ))
  let D : C(Square, ↥F) := ⟨E ∘ squareToStrip,E.continuous.comp squareToStrip_continuous⟩
  have hD : IsEmbedding D := hE.comp
    (squareToStrip_continuous.isClosedEmbedding squareToStrip_injective).isEmbedding
  have hDcenter (s : Interval) : D (horizontalPoint s) = b s := by
    change E (squareToStrip (horizontalPoint s)) = b s
    rw [squareToStrip_horizontal,hcenter]
  have hi (z : Square) (hz : z.val ∈ Plane.openSquare 0 1) :
      (squareToStrip z).1 ∈ Ioo (0:Interval) 1 := by
    have hz0 : |z.val 0| < 1 := lt_of_le_of_lt (le_max_left _ _) (mem_openSquare_zero_one.mp hz)
    have hz0 := abs_lt.mp hz0
    constructor
    · change (0:ℝ) < (z.val 0+1)/2
      linarith [hz0.1]
    · change (z.val 0+1)/2 < (1:ℝ)
      linarith [hz0.2]
  have hDclear (z : Square) (hz : z.val ∈ Plane.openSquare 0 1) :
      (D z).val ∉ frontier F := hint _ (hi z hz) _
  have hback (z : Square) (hz1 : |z.val 1| < 1) (hz : (D z).val ∉ frontier F) :
      z.val ∈ Plane.openSquare 0 1 := by
    have hn0 : (squareToStrip z).1 ≠ 0 := by
      intro h
      apply hz
      change (E (squareToStrip z)).val ∈ frontier F
      have he : squareToStrip z = (0,(squareToStrip z).2) := Prod.ext h rfl
      rw [he]
      exact (hend _).1
    have hn1 : (squareToStrip z).1 ≠ 1 := by
      intro h
      apply hz
      change (E (squareToStrip z)).val ∈ frontier F
      have he : squareToStrip z = (1,(squareToStrip z).2) := Prod.ext h rfl
      rw [he]
      exact (hend _).2
    have h0 : (0:ℝ) < (squareToStrip z).1 := bot_lt_iff_ne_bot.mpr hn0
    have h1 : ((squareToStrip z).1:ℝ) < 1 := lt_top_iff_ne_top.mpr hn1
    apply mem_openSquare_zero_one.mpr
    change max |z.val 0| |z.val 1| < 1
    rw [max_lt_iff,abs_lt]
    exact ⟨⟨by dsimp [squareToStrip] at h0; linarith,
      by dsimp [squareToStrip] at h1; linarith⟩,hz1⟩
  have himage : D '' {z : Square | |z.val 1| < 1} =
      E '' {z | (-1:ℝ) < z.2.val ∧ z.2.val < 1} := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨squareToStrip z,abs_lt.mp hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨w,rfl⟩ := squareToStrip_surjective z
      exact ⟨w,abs_lt.mpr hz,rfl⟩
  let eS : Interval × Set.Icc (-1:ℝ) 1 → S := fun z => (E z).val
  let bS : C(Interval,S) := ⟨fun t => (b t).val,continuous_subtype_val.comp b.continuous⟩
  obtain ⟨Q,hQs,hQt,hQco,hQaxis⟩ := source_embedded_strip_interior_chart eS
    (IsEmbedding.subtypeVal.comp hE) bS (fun t => congrArg Subtype.val (hcenter t))
  let P := normalizePlane.toOpenPartialHomeomorph.trans Q.symm
  refine ⟨D,hD,hDcenter,hDclear,hback,by rw [himage]; exact hopen,P,?_,?_⟩
  · ext z
    simp only [P,OpenPartialHomeomorph.trans_source,Homeomorph.toOpenPartialHomeomorph_source,
      mem_inter_iff,mem_univ,true_and,mem_preimage,OpenPartialHomeomorph.symm_source]
    rw [hQt]
    change (0 < (z 0+1)/2 ∧ (z 0+1)/2 < 1 ∧ -1 < z 1 ∧ z 1 < 1) ↔ _
    rw [mem_openSquare_zero_one]
    change _ ↔ max |z 0| |z 1| < 1
    rw [max_lt_iff,abs_lt,abs_lt]
    constructor
    · rintro ⟨h0,h1,hw0,hw1⟩
      exact ⟨⟨by linarith,by linarith⟩,hw0,hw1⟩
    · rintro ⟨⟨h0,h1⟩,hw0,hw1⟩
      exact ⟨by linarith,by linarith,hw0,hw1⟩
  · intro z hz
    have hz0 := hi z hz
    have hz1 : -1 < z.val 1 ∧ z.val 1 < 1 := abs_lt.mp
      (lt_of_le_of_lt (le_max_right _ _) (mem_openSquare_zero_one.mp hz))
    have hcoord := hQco (squareToStrip z) hz0.1 hz0.2 hz1.1 hz1.2
    have hsource : eS (squareToStrip z) ∈ Q.source := by
      rw [hQs]
      exact ⟨squareToStrip z,⟨hz0.1,hz0.2,hz1.1,hz1.2⟩,rfl⟩
    change Q.symm (normalizePlane z.val) = eS (squareToStrip z)
    change Q.symm (Plane.mk (squareToStrip z).1 (squareToStrip z).2) = _
    rw [← hcoord]
    exact Q.left_inv hsource

#print axioms strip_square_package

end RegionalFinitePosition
