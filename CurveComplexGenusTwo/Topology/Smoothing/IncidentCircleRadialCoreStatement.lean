import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
open Set Topology Metric Schoenflies CurveComplex.FiniteStarGeometry
namespace CurveComplex
set_option maxHeartbeats 2000000
theorem finite_incident_circle_radial_core {S : Type} [TopologicalSpace S] [T2Space S]
    {J : Type} [Fintype J] (c : J → Curve S) (p : S)
    (hp : ∀ j, p ∈ (c j).image)
    (E : OpenPartialHomeomorph S Plane) (hEp : E p = 0)
    (U : Set S) (hU : IsOpen U) (hpU : p ∈ U) (hUE : U ⊆ E.source)
    (hmeet : ∀ i j, i ≠ j → U ∩ ((c i).image ∩ (c j).image) ⊆ {p})
    (j₀ : J) :
    ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi ∧
      ∃ q : J → Circle, (∀ j, (c j).map (q j) = p) ∧
      let γ : (J × Bool) → CurveComplex.Interval → Plane := fun j t =>
        E ((c j.1).map (q j.1 * Circle.exp (if j.2 then ε*t.val else -(ε*t.val))))
      ∃ R : RadializedStar γ 0 (E '' U),
        R.vector (j₀,true) = -R.vector (j₀,false) ∧
        ∀ j x, x ∈ E.source → ‖R.H (E x)‖ ≤ R.coreRadius →
          (x ∈ (c j).image ↔ R.H (E x) ∈
            segment ℝ (0 : Plane) (R.vector (j,false)) ∪
            segment ℝ (0 : Plane) (R.vector (j,true))) := by
  classical
  have hex : ∀ j, ∃ q : Circle, (c j).map q = p := hp
  choose q hq using hex
  let ψ : J → ℝ → S := fun j t => (c j).map (q j * Circle.exp t)
  have hψ : ∀ j, Continuous (ψ j) := fun j =>
    (c j).embedded.continuous.comp (continuous_const.mul Circle.exp.continuous)
  have hψ0 (j : J) : ψ j 0 = p := by simp [ψ,hq]
  have hPre : IsOpen (⋂ j, ψ j ⁻¹' U) := isOpen_iInter_of_finite
    (fun j => hU.preimage (hψ j))
  have h0Pre : (0 : ℝ) ∈ ⋂ j, ψ j ⁻¹' U := by
    apply Set.mem_iInter.mpr
    intro j
    simpa [hψ0] using hpU
  obtain ⟨r,hr,hrr⟩ := Metric.isOpen_iff.mp hPre 0 h0Pre
  let ε := min r Real.pi / 2
  have hε : 0 < ε := half_pos (lt_min hr Real.pi_pos)
  have hεr : ε < r := by dsimp [ε]; linarith [min_le_left r Real.pi]
  have hεπ : ε < Real.pi := by dsimp [ε]; linarith [min_le_right r Real.pi,Real.pi_pos]
  have hSmall (j : J) (t : ℝ) (ht : t ∈ Icc (-ε) ε) : ψ j t ∈ U := by
    have htball : t ∈ Metric.ball (0 : ℝ) r := by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
      constructor <;> linarith [ht.1,ht.2]
    exact Set.mem_iInter.mp (hrr htball) j
  let θ : (J × Bool) → CurveComplex.Interval → ℝ := fun j t =>
    if j.2 then ε*t.val else -(ε*t.val)
  have hθ (j : J × Bool) (t : CurveComplex.Interval) : θ j t ∈ Icc (-ε) ε := by
    dsimp [θ]
    split_ifs <;> constructor <;> nlinarith [t.property.1,t.property.2]
  let γ : (J × Bool) → CurveComplex.Interval → Plane := fun j t => E (ψ j.1 (θ j t))
  have hγU (j : J × Bool) (t : CurveComplex.Interval) : ψ j.1 (θ j t) ∈ U :=
    hSmall j.1 _ (hθ j t)
  have hγcont (j : J × Bool) : Continuous (γ j) := by
    have hc : Continuous (fun t : CurveComplex.Interval => ψ j.1 (θ j t)) :=
      (hψ j.1).comp (by dsimp [θ]; split_ifs <;> fun_prop)
    exact E.continuousOn.comp_continuous hc (fun t => hUE (hγU j t))
  have hγ0 (j : J × Bool) : γ j zeroI = 0 := by
    have hh : θ j zeroI = 0 := by simp [θ,zeroI]
    simp only [γ,hh,hψ0,hEp]
  have hγinj (j : J × Bool) : Function.Injective (γ j) := by
    intro t s he
    have hs := E.injOn (hUE (hγU j t)) (hUE (hγU j s)) he
    have hang := Circle.exp_injOn_Icc (by linarith : ε - -ε < 2*Real.pi)
      (hθ j t) (hθ j s) (mul_left_cancel ((c j.1).embedded.injective hs))
    apply Subtype.ext
    dsimp [θ] at hang
    split_ifs at hang <;> nlinarith
  have hγclosed (j : J × Bool) : Topology.IsClosedEmbedding (γ j) :=
    (hγcont j).isClosedEmbedding (hγinj j)
  have hγmeet (i j : J × Bool) (hij : i ≠ j) : Set.range (γ i) ∩ Set.range (γ j) = {0} := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨t,rfl⟩,⟨s,he⟩⟩
      have heS := E.injOn (hUE (hγU j s)) (hUE (hγU i t)) he
      by_cases hlabels : i.1 = j.1
      · have hang := Circle.exp_injOn_Icc (by linarith : ε - -ε < 2*Real.pi)
          (hθ j s) (hθ i t) (mul_left_cancel ((c i.1).embedded.injective (by simpa [hlabels] using heS)))
        have hsign : i.2 ≠ j.2 := by
          intro heq
          exact hij (Prod.ext hlabels heq)
        have ht0 : t.val = 0 := by
          dsimp [θ] at hang
          cases hi : i.2 <;> cases hj : j.2
          · exact False.elim (hsign (hi.trans hj.symm))
          · simp [hi,hj] at hang
            nlinarith [s.property.1,t.property.1]
          · simp [hi,hj] at hang
            nlinarith [s.property.1,t.property.1]
          · exact False.elim (hsign (hi.trans hj.symm))
        have htZ : t = zeroI := Subtype.ext ht0
        rw [htZ,hγ0]
        exact Set.mem_singleton 0
      · have hc : ψ i.1 (θ i t) ∈ ({p} : Set S) :=
          hmeet i.1 j.1 hlabels ⟨hγU i t,⟨⟨q i.1 * Circle.exp (θ i t),rfl⟩,
            heS ▸ ⟨q j.1 * Circle.exp (θ j s),rfl⟩⟩⟩
        change ψ i.1 (θ i t) = p at hc
        change E (ψ i.1 (θ i t)) ∈ ({0} : Set Plane)
        rw [hc,hEp]
        exact Set.mem_singleton 0
    · rintro x rfl
      exact ⟨⟨zeroI,hγ0 i⟩,⟨zeroI,hγ0 j⟩⟩
  let C : J → Set Circle := fun j => (fun t : ℝ => q j * Circle.exp t) '' Ioo (-ε) ε
  have hCopen (j : J) : IsOpen (C j) :=
    ((isOpenMap_mul_left (q j)).comp Circle.isCoveringMap_exp.isOpenMap) _ isOpen_Ioo
  let K : J → Set S := fun j => (c j).map '' (C j)ᶜ
  have hKcompact (j : J) : IsCompact (K j) :=
    (hCopen j).isClosed_compl.isCompact.image (c j).embedded.continuous
  let bad : Set S := ⋃ j, K j
  have hBadClosed : IsClosed bad := isClosed_iUnion_of_finite (fun j => (hKcompact j).isClosed)
  have hpBad : p ∉ bad := by
    intro hpB
    obtain ⟨j,z,hz,hzp⟩ := Set.mem_iUnion.mp hpB
    have hzq : z = q j := (c j).embedded.injective (hzp.trans (hq j).symm)
    apply hz
    exact ⟨0,⟨by linarith, hε⟩,by simpa using hzq.symm⟩
  let W := U \ bad
  have hW : IsOpen W := hU.sdiff hBadClosed
  have hpW : p ∈ W := ⟨hpU,hpBad⟩
  have hWE : W ⊆ E.source := fun x hx => hUE hx.1
  have hPlaneW : IsOpen (E '' W) := E.isOpen_image_of_subset_source hW hWE
  have h0PlaneW : (0 : Plane) ∈ E '' W := ⟨p,hpW,hEp⟩
  obtain ⟨R₀,hRop⟩ := prescribed_pair_finite_actual_star_radialization_zero γ hγclosed hγ0 hγmeet
    (j₀,false) (j₀,true) (by simp) (E '' W) hPlaneW h0PlaneW
  let R : RadializedStar γ 0 (E '' U) := {R₀ with
    support_subset := R₀.support_subset.trans (Set.image_mono Set.sdiff_subset)}
  have hNotK (j : J) (x : S) (hxE : x ∈ E.source)
      (hxN : ‖R.H (E x)‖ ≤ R.coreRadius) : x ∉ K j := by
    intro hxK
    have hxPlane : E x ∉ E '' W := by
      rintro ⟨y,hy,he⟩
      have hyx : y = x := E.injOn (hWE hy) hxE he
      exact hy.2 (hyx.symm ▸ Set.mem_iUnion.mpr ⟨j,hxK⟩)
    have hxOut : E x ∉ Metric.ball (0 : Plane) R₀.supportRadius := by
      intro hx
      exact hxPlane (R₀.support_subset (Metric.ball_subset_closedBall hx))
    have hxFix : R.H (E x) = E x := R₀.fixes_exterior _ hxOut
    rw [hxFix] at hxN
    have hxBall : E x ∈ Metric.closedBall (0 : Plane) R₀.supportRadius := by
      rw [Metric.mem_closedBall,dist_zero_right]
      exact hxN.trans R₀.core_lt_support.le
    exact hxPlane (R₀.support_subset hxBall)
  have hGammaCover (j : J) (x : S) (hx : x ∈ (c j).image) (hxK : x ∉ K j) :
      ∃ sign : Bool, ∃ t : CurveComplex.Interval, γ (j,sign) t = E x := by
    obtain ⟨z,hzx⟩ := hx
    have hzC : z ∈ C j := by
      by_contra hn
      exact hxK ⟨z,hn,hzx⟩
    obtain ⟨a,ha,haz⟩ := hzC
    change q j * Circle.exp a = z at haz
    by_cases hapos : 0 ≤ a
    · let t : CurveComplex.Interval := ⟨a/ε,⟨div_nonneg hapos hε.le,
        (div_le_one hε).mpr ha.2.le⟩⟩
      refine ⟨true,t,?_⟩
      have hmul : ε*t.val = a := by dsimp [t]; field_simp
      change E ((c j).map (q j * Circle.exp (ε*t.val))) = E x
      rw [hmul,haz,hzx]
    · let t : CurveComplex.Interval := ⟨(-a)/ε,⟨div_nonneg (by linarith) hε.le,
        (div_le_one hε).mpr (by linarith [ha.1])⟩⟩
      refine ⟨false,t,?_⟩
      have hmul : -(ε*t.val) = a := by dsimp [t]; field_simp
      change E ((c j).map (q j * Circle.exp (-(ε*t.val)))) = E x
      rw [hmul,haz,hzx]
  refine ⟨ε,hε,hεπ,q,hq,R,hRop,?_⟩
  intro j x hxE hxN
  constructor
  · intro hx
    obtain ⟨sign,t,htx⟩ := hGammaCover j x hx (hNotK j x hxE hxN)
    have hcut : t.val ≤ (R.cut (j,sign)).val := by
      by_contra hn
      have htail : R.H (γ (j,sign) t) ∈ R.H '' tail γ (j,sign) (R.cut (j,sign)) :=
        ⟨γ (j,sign) t,⟨t,(lt_of_not_ge hn).le,rfl⟩,rfl⟩
      have hball : R.H (γ (j,sign) t) ∈ Metric.closedBall (0 : Plane) R.coreRadius := by
        rw [htx,Metric.mem_closedBall,dist_zero_right]
        exact hxN
      exact Set.disjoint_left.mp (R.excludes_tails (j,sign)) htail hball
    have hray : R.H (E x) ∈ segment ℝ (0 : Plane) (R.vector (j,sign)) := by
      have hh : R.H (γ (j,sign) t) ∈ R.H '' armPrefix γ (j,sign) (R.cut (j,sign)) :=
        ⟨γ (j,sign) t,⟨t,hcut,rfl⟩,rfl⟩
      simpa only [R.prefix_image,zero_add,htx] using hh
    cases sign
    · exact Or.inl hray
    · exact Or.inr hray
  · intro hx
    have hRecover (sign : Bool) (hray : R.H (E x) ∈ segment ℝ (0 : Plane) (R.vector (j,sign))) :
        x ∈ (c j).image := by
      have hh : R.H (E x) ∈ R.H '' armPrefix γ (j,sign) (R.cut (j,sign)) := by
        rw [R.prefix_image,zero_add]
        exact hray
      obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := hh
      have hEx : γ (j,sign) t = E x := R.H.injective he
      have hsx : ψ j (θ (j,sign) t) = x := E.injOn (hUE (hγU (j,sign) t)) hxE hEx
      exact ⟨q j * Circle.exp (θ (j,sign) t),hsx⟩
    exact hx.elim (hRecover false) (hRecover true)
end CurveComplex
