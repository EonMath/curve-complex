import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
import CurveComplexGenusTwo.Topology.Smoothing.PointedPlaneIsotopyProof
import CurveComplexGenusTwo.Topology.ChartLift
open Set Metric Schoenflies CurveComplex CurveComplex.FiniteStarGeometry
theorem actual_surface_interior_interval_point_star_normalization {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (e : OpenPartialHomeomorph S Plane) (η : I → S)
    (hη : Topology.IsClosedEmbedding η) (hsource : ∀ t, η t ∈ e.source)
    (τ : I) (hτ0 : 0 < τ.val) (hτ1 : τ.val < 1)
    (W : Set S) (hW : IsOpen W) (hpW : η τ ∈ W) :
    ∃ (γ : Bool → I → Plane),
      (∀ t, γ false t=e (η ⟨τ.val*(1-t.val),by
        constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩)) ∧
      (∀ t, γ true t=e (η ⟨τ.val+(1-τ.val)*t.val,by
        constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩)) ∧
      ∃ R : RadializedStar γ (e (η τ)) (e '' (e.source ∩ W)),
        ∃ q : ℝ, 0 < q ∧ R.vector true = -q • R.vector false ∧
        ∃ (P : AmbientIsotopy Plane) (H : AmbientIsotopy S), P.finalMap=R.H ∧
          (∀ t, H.map (t,η τ)=η τ) ∧ (∀ t x, x ∉ W → H.map (t,x)=x) ∧
          (∀ t s, e (H.map (t,η s))=P.map (t,e (η s))) := by
  have planeStar (η : I → Plane) (hη : Topology.IsClosedEmbedding η)
      (τ : I) (hτ0 : 0 < τ.val) (hτ1 : τ.val < 1)
      (V : Set Plane) (hV : IsOpen V) (hpV : η τ ∈ V) :
      ∃ (γ : Bool → I → Plane),
        (∀ t, γ false t=η ⟨τ.val*(1-t.val),by
          constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩) ∧
        (∀ t, γ true t=η ⟨τ.val+(1-τ.val)*t.val,by
          constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩) ∧
        ∃ R : RadializedStar γ (η τ) V, ∃ q : ℝ, 0 < q ∧
          R.vector true = -q • R.vector false ∧
          ∃ H : AmbientIsotopy Plane, H.finalMap=R.H ∧
            (∀ t, H.map (t,η τ)=η τ) ∧ (∀ t x, x ∉ V → H.map (t,x)=x) := by
    classical
    let left : I → I := fun t => ⟨τ.val*(1-t.val),by
      constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩
    let right : I → I := fun t => ⟨τ.val+(1-τ.val)*t.val,by
      constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩
    let γ : Bool → I → Plane := fun b => if b then η ∘ right else η ∘ left
    have hc : ∀ b, Continuous (γ b) := by
      intro b
      cases b
      · exact hη.continuous.comp ((continuous_const.mul (continuous_const.sub continuous_subtype_val)).subtype_mk _)
      · exact hη.continuous.comp ((continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _)
    have hi : ∀ b, Function.Injective (γ b) := by
      intro b s t he
      apply Subtype.ext
      cases b
      · have hh := congrArg Subtype.val (hη.injective he)
        change τ.val*(1-s.val)=τ.val*(1-t.val) at hh
        nlinarith
      · have hh := congrArg Subtype.val (hη.injective he)
        change τ.val+(1-τ.val)*s.val=τ.val+(1-τ.val)*t.val at hh
        nlinarith
    have hclosed : ∀ b, Topology.IsClosedEmbedding (γ b) := fun b => (hc b).isClosedEmbedding (hi b)
    have hstart : ∀ b, γ b zeroI=η τ := by
      intro b
      cases b <;> apply congrArg η <;> apply Subtype.ext <;> simp [γ,left,right,zeroI]
    have hmeet : ∀ i j, i ≠ j → range (γ i) ∩ range (γ j)={η τ} := by
      have lr : range (γ false) ∩ range (γ true)={η τ} := by
        ext x
        constructor
        · rintro ⟨⟨s,hs⟩,⟨t,ht⟩⟩
          have he : η (left s)=η (right t) := hs.trans ht.symm
          have hh := congrArg Subtype.val (hη.injective he)
          change τ.val*(1-s.val)=τ.val+(1-τ.val)*t.val at hh
          have hs0 : s.val=0 := by nlinarith [s.property.1,t.property.1]
          have hsz : s=zeroI := Subtype.ext hs0
          rw [hsz,hstart] at hs
          exact hs.symm
        · intro hx
          have hx' : x=η τ := hx
          subst x
          exact ⟨⟨zeroI,hstart false⟩,⟨zeroI,hstart true⟩⟩
      intro i j hij
      cases i <;> cases j
      · exact False.elim (hij rfl)
      · exact lr
      · simpa only [inter_comm] using lr
      · exact False.elim (hij rfl)
    obtain ⟨R,hopp⟩ := pointed_one_or_two_arm_relative_seed γ (η τ)
      hclosed hstart hmeet (Or.inr (by decide)) V hV hpV
    obtain ⟨q,hq,hvectors⟩ := hopp false true (by decide)
    obtain ⟨H,hfinal,hcenter,houtside⟩ := supported_pointed_plane_isotopy (η τ)
      R.supportRadius R.support_pos R.H R.fixes_center R.fixes_exterior
    refine ⟨γ,(fun _ => rfl),(fun _ => rfl),R,q,hq,hvectors,H,hfinal,hcenter,?_⟩
    intro t x hx
    apply houtside t x
    intro hh
    exact hx (R.support_subset (ball_subset_closedBall hh))
  let ξ : I → Plane := e ∘ η
  have hξcont : Continuous ξ := by
    apply continuousOn_univ.mp
    exact e.continuousOn.comp hη.continuous.continuousOn (fun t _ => hsource t)
  have hξ : Topology.IsClosedEmbedding ξ := hξcont.isClosedEmbedding (by
    intro s t he
    apply hη.injective
    exact e.injOn (hsource s) (hsource t) he)
  let V : Set Plane := e '' (e.source ∩ W)
  have hV : IsOpen V := e.isOpen_image_source_inter hW
  have hpV : ξ τ ∈ V := ⟨η τ,⟨hsource τ,hpW⟩,rfl⟩
  obtain ⟨γ,hleft,hright,R,q,hq,hvectors,Pold,hPold,hPoldcenter,hPoldoutside⟩ :=
    planeStar ξ hξ τ hτ0 hτ1 V hV hpV
  obtain ⟨P,hPfinal,hPcenter,hPoutside⟩ := supported_pointed_plane_isotopy (ξ τ)
    R.supportRadius R.support_pos R.H R.fixes_center R.fixes_exterior
  have hCtarget : closedBall (ξ τ) R.supportRadius ⊆ e.target := by
    intro z hz
    obtain ⟨x,hx,hxz⟩ := R.support_subset hz
    rw [← hxz]
    exact e.mapsTo hx.1
  have hPclosed : ∀ t z, z ∉ closedBall (ξ τ) R.supportRadius → P.map (t,z)=z := by
    intro t z hz
    exact hPoutside t z (fun hh => hz (ball_subset_closedBall hh))
  obtain ⟨K,H,hcoord,hHU,hHoutside⟩ := position_surface_chart_lift S e.source e.target
    e.open_source e.toHomeomorphSourceTarget (closedBall (ξ τ) R.supportRadius)
    (isCompact_closedBall _ _) hCtarget P hPclosed
  have hcoord' (t : Interval) (x : e.source) : e (K.map (t,x))=P.map (t,e x) := by
    simpa only [OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe] using hcoord t x
  have hHpoint (t : Interval) (x : S) (hx : x ∈ e.source) :
      H.map (t,x)=e.symm (P.map (t,e x)) := by
    rw [hHU t ⟨x,hx⟩,← hcoord' t ⟨x,hx⟩]
    exact (e.left_inv (K.map (t,⟨x,hx⟩)).property).symm
  refine ⟨γ,hleft,hright,R,q,hq,hvectors,P,H,hPfinal,?_,?_,?_⟩
  · intro t
    rw [hHpoint t (η τ) (hsource τ)]
    change e.symm (P.map (t,ξ τ))=η τ
    rw [hPcenter]
    exact e.left_inv (hsource τ)
  · intro t x hxW
    by_cases hx : x ∈ e.source
    · have heout : e x ∉ closedBall (ξ τ) R.supportRadius := by
        intro hz
        obtain ⟨y,hy,hyx⟩ := R.support_subset hz
        have hxy : y=x := e.injOn hy.1 hx hyx
        exact hxW (hxy ▸ hy.2)
      rw [hHpoint t x hx,hPclosed t (e x) heout,e.left_inv hx]
    · exact hHoutside t x hx
  · intro t s
    rw [hHU t ⟨η s,hsource s⟩]
    exact hcoord' t ⟨η s,hsource s⟩

#print axioms actual_surface_interior_interval_point_star_normalization
