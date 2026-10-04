import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14PairedSupportedCrossingCount
import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchCharts
import CurveComplexGenusTwo.Topology.IntersectionParity.HomeomorphTransport
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14CrossesAtImageAgreement

namespace CurveComplex
open Set Topology Schoenflies
set_option maxHeartbeats 4000000

/-- The paired supported operation preserves actual whole-curve crossings as
well as strictly reducing their finite count. Local chart transport is proved
on the two open complements of the disjoint closed supports. -/
theorem paired_supported_homeomorph_transverse_drop
    {E : Type} [TopologicalSpace E] [ChartedSpace Plane E] [ClosedSurface E]
    (τ H : E ≃ₜ E) (hτ : ∀ x, τ (τ x) = x)
    (V : Set E) (hsep : Disjoint (closure V) (τ '' closure V))
    (hfix : ∀ x, x ∉ V → H x = x)
    (a b : Curve E) (hA : τ '' a.image = a.image) (hB : τ '' b.image = b.image)
    (ht : Transverse a b) (htH : Transverse (LocalSurgery.homeomorphCurve H a) b)
    (hdrop : ((LocalSurgery.homeomorphCurve H a).image ∩ b.image).ncard <
      (a.image ∩ b.image).ncard) :
    let J := (τ.trans H).trans τ
    let K := H.trans J
    Transverse (LocalSurgery.homeomorphCurve K a) b ∧
      ((LocalSurgery.homeomorphCurve K a).image ∩ b.image).ncard < (a.image ∩ b.image).ncard := by
  classical
  let W := τ '' V
  let J := (τ.trans H).trans τ
  let K := H.trans J
  have hsepVW : Disjoint V W := hsep.mono subset_closure (Set.image_mono subset_closure)
  have hτmem (C : Set E) (x : E) : x ∈ τ '' C ↔ τ x ∈ C := by
    constructor
    · rintro ⟨y,hy,rfl⟩; simpa only [hτ] using hy
    · intro hx; exact ⟨τ x,hx,hτ x⟩
  have hJfix (x : E) (hx : x ∉ W) : J x = x := by
    change τ (H (τ x)) = x
    rw [hfix _ (fun h => hx ((hτmem V x).mpr h)),hτ]
  have outsideImage (F : E ≃ₜ E) (U : Set E)
      (hF : ∀ x, x ∉ U → F x = x) (C : Set E) (x : E) (hx : x ∉ U) :
      x ∈ F '' C ↔ x ∈ C := by
    constructor
    · rintro ⟨y,hy,he⟩
      exact (F.injective (he.trans (hF x hx).symm)) ▸ hy
    · intro hc; exact ⟨x,hc,hF x hx⟩
  have hImage (F : E ≃ₜ E) (c : Curve E) :
      (LocalSurgery.homeomorphCurve F c).image = F '' c.image := by
    change Set.range (F ∘ c.map) = F '' Set.range c.map
    exact Set.range_comp _ _
  have hKimage : K '' a.image = J '' (H '' a.image) := by rw [Set.image_image]; rfl
  have hJimage : J '' a.image = τ '' (H '' a.image) := by
    calc
      J '' a.image = τ '' (H '' (τ '' a.image)) := by
        rw [Set.image_image,Set.image_image]; rfl
      _ = τ '' (H '' a.image) := by rw [hA]
  have hLocalH (x : E) (hx : x ∉ W) :
      x ∈ (LocalSurgery.homeomorphCurve K a).image ↔ x ∈ (LocalSurgery.homeomorphCurve H a).image := by
    rw [hImage,hImage,hKimage,outsideImage J W hJfix (H '' a.image) x hx]
  have hJVfix (x : E) (hx : x ∈ V) : J x = x :=
    hJfix x (fun h => Set.disjoint_left.mp hsepVW hx h)
  have hJV (x : E) : J x ∈ V ↔ x ∈ V := by
    constructor
    · intro hx
      have he : J (J x) = J x := hJVfix _ hx
      have he' : J x = x := J.injective he
      exact he' ▸ hx
    · intro hx; rw [hJVfix x hx]; exact hx
  have hLocalτH (x : E) (hx : x ∉ V) :
      x ∈ (LocalSurgery.homeomorphCurve K a).image ↔
        x ∈ (LocalSurgery.homeomorphCurve τ (LocalSurgery.homeomorphCurve H a)).image := by
    rw [hImage,hImage,hImage,hKimage]
    rw [← hJimage]
    constructor
    · rintro ⟨u,hu,he⟩
      have huNV : u ∉ V := fun h => hx (he ▸ (hJV u).mpr h)
      exact ⟨u,(outsideImage H V hfix a.image u huNV).mp hu,he⟩
    · rintro ⟨u,hu,he⟩
      have huNV : u ∉ V := fun h => hx (he ▸ (hJV u).mpr h)
      exact ⟨u,(outsideImage H V hfix a.image u huNV).mpr hu,he⟩
  have hLocalB (x : E) : x ∈ b.image ↔ x ∈ (LocalSurgery.homeomorphCurve τ b).image := by
    rw [hImage,hB]
  obtain ⟨htτ,hcardτ⟩ := LocalSurgery.transverse_homeomorph_count τ
    (LocalSurgery.homeomorphCurve H a) b htH
  have hfin : ((LocalSurgery.homeomorphCurve K a).image ∩ b.image).Finite := by
    rw [hImage]
    exact (paired_supported_homeomorph_crossing_drop τ H hτ V hsepVW hfix a.image b.image
      hA hB ht.1 (by simpa only [hImage] using htH.1) (by simpa only [hImage] using hdrop)).1
  have hCross : ∀ p ∈ (LocalSurgery.homeomorphCurve K a).image ∩ b.image,
      CrossesAt (LocalSurgery.homeomorphCurve K a) b p := by
    intro p hp
    by_cases hpW : p ∈ τ '' closure V
    · have hpNV : p ∉ closure V := fun h => Set.disjoint_left.mp hsep h hpW
      let U := (closure V)ᶜ
      have hpU : p ∈ U := hpNV
      have haU : ∀ x ∈ U, x ∈ (LocalSurgery.homeomorphCurve K a).image ↔
          x ∈ (LocalSurgery.homeomorphCurve τ (LocalSurgery.homeomorphCurve H a)).image :=
        fun x hx => hLocalτH x (fun h => hx (subset_closure h))
      have hpτ : p ∈ (LocalSurgery.homeomorphCurve τ (LocalSurgery.homeomorphCurve H a)).image ∩
          (LocalSurgery.homeomorphCurve τ b).image := ⟨(haU p hpU).mp hp.1,(hLocalB p).mp hp.2⟩
      exact crossesAt_of_curve_images_agree_on_open _ _ _ _ p U isClosed_closure.isOpen_compl hpU
        haU (fun x _ => hLocalB x) (htτ.2 p hpτ)
    · let U := (τ '' closure V)ᶜ
      have hU : IsOpen U := (τ.isClosedMap _ isClosed_closure).isOpen_compl
      have haU : ∀ x ∈ U, x ∈ (LocalSurgery.homeomorphCurve K a).image ↔
          x ∈ (LocalSurgery.homeomorphCurve H a).image :=
        fun x hx => hLocalH x (fun h => hx (Set.image_mono subset_closure h))
      have hpH : p ∈ (LocalSurgery.homeomorphCurve H a).image ∩ b.image :=
        ⟨(haU p hpW).mp hp.1,hp.2⟩
      exact crossesAt_of_curve_images_agree_on_open _ _ _ _ p U hU hpW haU
        (fun _ _ => Iff.rfl) (htH.2 p hpH)
  refine ⟨⟨hfin,hCross⟩,?_⟩
  rw [hImage]
  exact (paired_supported_homeomorph_crossing_drop τ H hτ V hsepVW hfix a.image b.image
    hA hB ht.1 (by simpa only [hImage] using htH.1) (by simpa only [hImage] using hdrop)).2
end CurveComplex
