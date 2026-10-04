import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerCornerGeometryDefinitions
import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisTransition
import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchSquares

open Set Topology Metric Schoenflies CurveComplex CurveComplex.FiniteStarGeometry

namespace ActualHarerCornerGeometry
set_option maxHeartbeats 2000000

theorem interval_four_arm_radial_core
    {S : Type} [TopologicalSpace S] [T2Space S]
    {J : Type} [Fintype J] (f : J → C(Interval,S))
    (hf : ∀ j, IsEmbedding (f j)) (c : J → Interval)
    (hc : ∀ j, c j ∈ Ioo (0:Interval) 1) (p : S)
    (hp : ∀ j, f j (c j) = p)
    (E : OpenPartialHomeomorph S Plane) (hEp : E p = 0)
    (U : Set S) (hU : IsOpen U) (hpU : p ∈ U) (hUE : U ⊆ E.source)
    (hmeet : ∀ i j, i ≠ j → U ∩ (range (f i) ∩ range (f j)) ⊆ {p})
    (j₀ : J) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ j, 0 < (c j:ℝ)-δ ∧ (c j:ℝ)+δ < 1) ∧
      ∃ θ : (J × Bool) → Interval → Interval,
        (∀ j t, (θ j t:ℝ) = (c j.1:ℝ) + if j.2 then δ*t.val else -(δ*t.val)) ∧
        (∀ j t, f j.1 (θ j t) ∈ U) ∧
        ∃ R : RadializedStar (fun j t => E (f j.1 (θ j t))) 0 (E '' U),
          R.vector (j₀,true) = -R.vector (j₀,false) ∧
          (∀ j x, x ∈ E.source → ‖R.H (E x)‖ ≤ R.coreRadius →
            (x ∈ range (f j) ↔ R.H (E x) ∈
              segment ℝ (0:Plane) (R.vector (j,false)) ∪
              segment ℝ (0:Plane) (R.vector (j,true)))) ∧
          (∀ j u, f j u ∈ E.source → ‖R.H (E (f j u))‖ ≤ R.coreRadius →
            (c j:ℝ)-δ < u.val ∧ u.val < (c j:ℝ)+δ) := by
  classical
  let ψ : J → ℝ → S := fun j r => f j ⟨max 0 (min 1 r), by constructor <;> simp⟩
  have hψ : ∀ j, Continuous (ψ j) := fun j =>
    (f j).continuous.comp (by
      apply Continuous.subtype_mk
      exact continuous_const.max (continuous_const.min continuous_id))
  have hψc (j : J) : ψ j (c j) = p := by
    have he : (⟨max 0 (min 1 (c j:ℝ)), by constructor <;> simp⟩ : Interval) = c j := by
      apply Subtype.ext
      simp [min_eq_right (c j).property.2, max_eq_right (c j).property.1]
    exact (congrArg (f j) he).trans (hp j)
  let V : Set ℝ := ⋂ j, {r | ψ j ((c j:ℝ)+r) ∈ U ∧ 0 < (c j:ℝ)+r ∧ (c j:ℝ)+r < 1}
  have hV : IsOpen V := by
    apply isOpen_iInter_of_finite
    intro j
    exact (hU.preimage ((hψ j).comp (by fun_prop))).inter
      ((isOpen_lt continuous_const (continuous_const.add continuous_id)).inter
        (isOpen_lt (continuous_const.add continuous_id) continuous_const))
  have h0V : (0:ℝ) ∈ V := by
    apply mem_iInter.mpr
    intro j
    simpa [hψc] using And.intro hpU (hc j)
  obtain ⟨r,hr,hrr⟩ := Metric.isOpen_iff.mp hV 0 h0V
  let δ := r/2
  have hδ : 0 < δ := half_pos hr
  have hδr : δ < r := by dsimp [δ]; linarith
  have hsmall (j : J) (a : ℝ) (ha : a ∈ Icc (-δ) δ) :
      ψ j ((c j:ℝ)+a) ∈ U ∧ 0 < (c j:ℝ)+a ∧ (c j:ℝ)+a < 1 := by
    have hab : a ∈ Metric.ball (0:ℝ) r := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [ha.1,ha.2]
    exact mem_iInter.mp (hrr hab) j
  have hδc (j : J) : 0 < (c j:ℝ)-δ ∧ (c j:ℝ)+δ < 1 := by
    exact ⟨by simpa [sub_eq_add_neg] using (hsmall j (-δ) ⟨le_rfl,by linarith⟩).2.1,
      (hsmall j δ ⟨by linarith,le_rfl⟩).2.2⟩
  let a : (J × Bool) → Interval → ℝ := fun j t => if j.2 then δ*t.val else -(δ*t.val)
  have ha (j : J × Bool) (t : Interval) : a j t ∈ Icc (-δ) δ := by
    dsimp [a]
    split_ifs <;> constructor <;> nlinarith [t.property.1,t.property.2]
  let θ : (J × Bool) → Interval → Interval := fun j t =>
    ⟨(c j.1:ℝ)+a j t, (hsmall j.1 (a j t) (ha j t)).2.1.le,
      (hsmall j.1 (a j t) (ha j t)).2.2.le⟩
  have hθcont (j : J × Bool) : Continuous (θ j) := by
    apply Continuous.subtype_mk
    dsimp [a]
    split_ifs <;> fun_prop
  have hθ0 (j : J × Bool) : θ j 0 = c j.1 := by
    apply Subtype.ext
    simp [θ,a]
  have hθU (j : J × Bool) (t : Interval) : f j.1 (θ j t) ∈ U := by
    have hh := (hsmall j.1 (a j t) (ha j t)).1
    have he : ψ j.1 ((c j.1:ℝ)+a j t) = f j.1 (θ j t) := by
      dsimp only [ψ]
      apply congrArg (f j.1)
      apply Subtype.ext
      change max 0 (min 1 ((θ j t).val)) = (θ j t).val
      rw [min_eq_right (θ j t).property.2, max_eq_right (θ j t).property.1]
    rwa [he] at hh
  let γ : (J × Bool) → Interval → Plane := fun j t => E (f j.1 (θ j t))
  have hγcont (j : J × Bool) : Continuous (γ j) :=
    E.continuousOn.comp_continuous ((f j.1).continuous.comp (hθcont j))
      (fun t => hUE (hθU j t))
  have hγ0 (j : J × Bool) : γ j zeroI = 0 := by
    change E (f j.1 (θ j 0)) = 0
    rw [hθ0,hp,hEp]
  have hγinj (j : J × Bool) : Function.Injective (γ j) := by
    intro t u he
    have hs := (hf j.1).injective (E.injOn (hUE (hθU j t)) (hUE (hθU j u)) he)
    have hh := congrArg Subtype.val hs
    apply Subtype.ext
    dsimp [θ,a] at hh
    split_ifs at hh <;> nlinarith
  have hγclosed (j : J × Bool) : IsClosedEmbedding (γ j) :=
    (hγcont j).isClosedEmbedding (hγinj j)
  have hγmeet (i j : J × Bool) (hij : i ≠ j) : range (γ i) ∩ range (γ j) = {0} := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨t,rfl⟩,⟨u,he⟩⟩
      have hs := E.injOn (hUE (hθU j u)) (hUE (hθU i t)) he
      by_cases hlabels : i.1 = j.1
      · have hh := congrArg Subtype.val ((hf i.1).injective (by simpa [hlabels] using hs))
        have hsign : i.2 ≠ j.2 := fun heq => hij (Prod.ext hlabels heq)
        have ht0 : t.val = 0 := by
          dsimp [θ,a] at hh
          rw [hlabels] at hh
          cases hi : i.2 <;> cases hj : j.2
          · exact False.elim (hsign (hi.trans hj.symm))
          · simp [hi,hj] at hh; nlinarith [t.property.1,u.property.1]
          · simp [hi,hj] at hh; nlinarith [t.property.1,u.property.1]
          · exact False.elim (hsign (hi.trans hj.symm))
        have htZ : t = zeroI := Subtype.ext ht0
        rw [htZ,hγ0]
        exact mem_singleton 0
      · have hpt : f i.1 (θ i t) = p :=
          hmeet i.1 j.1 hlabels ⟨hθU i t,mem_range_self _,hs ▸ mem_range_self _⟩
        change E (f i.1 (θ i t)) = 0
        rw [hpt,hEp]
    · rintro x rfl
      exact ⟨⟨zeroI,hγ0 i⟩,⟨zeroI,hγ0 j⟩⟩
  let C : J → Set Interval := fun j => {u | (c j:ℝ)-δ < u.val ∧ u.val < (c j:ℝ)+δ}
  have hCopen (j : J) : IsOpen (C j) :=
    (isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const)
  let K : J → Set S := fun j => f j '' (C j)ᶜ
  have hKcompact (j : J) : IsCompact (K j) :=
    (hCopen j).isClosed_compl.isCompact.image (f j).continuous
  let bad : Set S := ⋃ j, K j
  have hBadClosed : IsClosed bad := isClosed_iUnion_of_finite (fun j => (hKcompact j).isClosed)
  have hpBad : p ∉ bad := by
    intro hpB
    obtain ⟨j,u,hu,hup⟩ := mem_iUnion.mp hpB
    have huc : u = c j := (hf j).injective (hup.trans (hp j).symm)
    apply hu
    rw [huc]
    exact ⟨by linarith,by linarith⟩
  let W := U \ bad
  have hW : IsOpen W := hU.sdiff hBadClosed
  have hpW : p ∈ W := ⟨hpU,hpBad⟩
  have hWE : W ⊆ E.source := fun x hx => hUE hx.1
  have hPlaneW : IsOpen (E '' W) := E.isOpen_image_of_subset_source hW hWE
  have h0PlaneW : (0:Plane) ∈ E '' W := ⟨p,hpW,hEp⟩
  obtain ⟨R₀,hRop⟩ := prescribed_pair_finite_actual_star_radialization_zero γ hγclosed hγ0 hγmeet
    (j₀,false) (j₀,true) (by simp) (E '' W) hPlaneW h0PlaneW
  let R : RadializedStar γ 0 (E '' U) := {R₀ with
    support_subset := R₀.support_subset.trans (image_mono sdiff_subset)}
  have hNotK (j : J) (x : S) (hxE : x ∈ E.source)
      (hxN : ‖R.H (E x)‖ ≤ R.coreRadius) : x ∉ K j := by
    intro hxK
    have hxPlane : E x ∉ E '' W := by
      rintro ⟨y,hy,he⟩
      have hyx : y = x := E.injOn (hWE hy) hxE he
      exact hy.2 (hyx.symm ▸ mem_iUnion.mpr ⟨j,hxK⟩)
    have hxOut : E x ∉ Metric.ball (0:Plane) R₀.supportRadius := by
      intro hx
      exact hxPlane (R₀.support_subset (Metric.ball_subset_closedBall hx))
    have hxFix : R.H (E x) = E x := R₀.fixes_exterior _ hxOut
    rw [hxFix] at hxN
    have hxBall : E x ∈ Metric.closedBall (0:Plane) R₀.supportRadius := by
      rw [Metric.mem_closedBall,dist_zero_right]
      exact hxN.trans R₀.core_lt_support.le
    exact hxPlane (R₀.support_subset hxBall)
  have hGammaCover (j : J) (x : S) (hx : x ∈ range (f j)) (hxK : x ∉ K j) :
      ∃ sign : Bool, ∃ t : Interval, γ (j,sign) t = E x := by
    obtain ⟨u,hux⟩ := hx
    have huC : u ∈ C j := by
      by_contra hn
      exact hxK ⟨u,hn,hux⟩
    by_cases hupos : (c j:ℝ) ≤ u.val
    · let t : Interval := ⟨(u.val-(c j:ℝ))/δ,⟨div_nonneg (sub_nonneg.mpr hupos) hδ.le,
        (div_le_one hδ).mpr (by linarith [huC.2])⟩⟩
      refine ⟨true,t,?_⟩
      have hθt : θ (j,true) t = u := by
        apply Subtype.ext
        change (c j:ℝ)+δ*((u.val-(c j:ℝ))/δ) = u.val
        field_simp
        <;> ring
      change E (f j (θ (j,true) t)) = E x
      rw [hθt,hux]
    · let t : Interval := ⟨((c j:ℝ)-u.val)/δ,⟨div_nonneg (by linarith) hδ.le,
        (div_le_one hδ).mpr (by linarith [huC.1])⟩⟩
      refine ⟨false,t,?_⟩
      have hθt : θ (j,false) t = u := by
        apply Subtype.ext
        change (c j:ℝ) + -(δ*(((c j:ℝ)-u.val)/δ)) = u.val
        field_simp
        <;> ring
      change E (f j (θ (j,false) t)) = E x
      rw [hθt,hux]
  refine ⟨δ,hδ,hδc,θ,(fun j t => rfl),hθU,R,hRop,?_,?_⟩
  · intro j x hxE hxN
    constructor
    · intro hx
      obtain ⟨sign,t,htx⟩ := hGammaCover j x hx (hNotK j x hxE hxN)
      have hcut : t.val ≤ (R.cut (j,sign)).val := by
        by_contra hn
        have htail : R.H (γ (j,sign) t) ∈ R.H '' tail γ (j,sign) (R.cut (j,sign)) :=
          ⟨γ (j,sign) t,⟨t,(lt_of_not_ge hn).le,rfl⟩,rfl⟩
        have hball : R.H (γ (j,sign) t) ∈ Metric.closedBall (0:Plane) R.coreRadius := by
          rw [htx,Metric.mem_closedBall,dist_zero_right]
          exact hxN
        exact disjoint_left.mp (R.excludes_tails (j,sign)) htail hball
      have hray : R.H (E x) ∈ segment ℝ (0:Plane) (R.vector (j,sign)) := by
        have hh : R.H (γ (j,sign) t) ∈ R.H '' armPrefix γ (j,sign) (R.cut (j,sign)) :=
          ⟨γ (j,sign) t,⟨t,hcut,rfl⟩,rfl⟩
        simpa only [R.prefix_image,zero_add,htx] using hh
      cases sign
      · exact Or.inl hray
      · exact Or.inr hray
    · intro hx
      have hRecover (sign : Bool) (hray : R.H (E x) ∈ segment ℝ (0:Plane) (R.vector (j,sign))) :
          x ∈ range (f j) := by
        have hh : R.H (E x) ∈ R.H '' armPrefix γ (j,sign) (R.cut (j,sign)) := by
          rw [R.prefix_image,zero_add]
          exact hray
        obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := hh
        have hEx : γ (j,sign) t = E x := R.H.injective he
        exact ⟨θ (j,sign) t,E.injOn (hUE (hθU (j,sign) t)) hxE hEx⟩
      exact hx.elim (hRecover false) (hRecover true)
  · intro j u huE huN
    by_contra hn
    exact hNotK j (f j u) huE huN ⟨u,hn,rfl⟩

end ActualHarerCornerGeometry
