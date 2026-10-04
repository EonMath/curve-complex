import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopOriginalEndpointOrientationPrivate
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers

open Lean Elab Term in
elab "checkedRLNonloopEndpointOrientation" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopOriginalEndpointOrientationPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_rl_same_class_nonloop_endpoint_orientation_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRLNonloopOriginalImageReverse" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopOriginalEndpointOrientationPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_rl_nonloop_reverse_parametrization_preserves_original_image_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRLNonloopSameClassAvoidingSweep" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualSameClassNonloopTargetAvoidingSweepCanonicalImportsPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_rl_same_class_target_avoiding_nonloop_sweep_private
  discard <| getConstInfo n
  return mkConst n

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 1500000
private theorem actual_original_same_class_nonloop_subpaths_of_aligned_actual_sweep_selector_private
    (hAlignedSelector :
    ∀ (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0≠a.val.map 1)
    (hSweep : ∃ K : C(Interval × Interval,S),
      (∀ t,K (0,t)=b.val.map t) ∧
      (∀ τ s t,K (τ,s)=K (τ,t) → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
      (∀ τ,K (τ,0)=b.val.map 0 ∧ K (τ,1)=b.val.map 1) ∧
      (∀ τ t,t≠0 → t≠1 → K (τ,t)∉(M.cover.branch:Set S)) ∧
      (∀ t,t≠0 → t≠1 → K (1,t)∉arcInterior M a))
    (hb0 : b.val.map 0=a.val.map 0) (hb1 : b.val.map 1=a.val.map 1)
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (htransverse : ∀ q ∈ ArcSurgery.crossings M a b,
      ArcSurgery.CrossesInDisk M a b q)
    (p : S) (hp : p ∈ ArcSurgery.crossings M a b) ,
    ∃ (f g : C(Interval,S)) (u v : S),
      IsEmbedding f ∧ IsEmbedding g ∧
      range f ⊆ a.val.image ∧ range g ⊆ b.val.image ∧
      f 0 = u ∧ g 0 = u ∧ f 1 = v ∧ g 1 = v ∧ u ≠ v ∧
      range f ∩ range g = {u,v} ∧
      v ∈ ArcSurgery.crossings M a b ∧
      (u ∈ ArcSurgery.crossings M a b ∨
        (u ∈ a.val.image ∩ b.val.image ∧ u ∈ (M.cover.branch : Set S))) ∧
      ∃ (hu : u ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (hv : v ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (α β : Path (⟨u,hu⟩ : ↑((M.cover.branch : Set S) \ {u})ᶜ) ⟨v,hv⟩),
        (∀ t : Interval, (α t : S) = f t) ∧
        (∀ t : Interval, (β t : S) = g t) ∧ α.Homotopic β
    )
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0≠a.val.map 1)
    (hab : Quotient.mk (essentialArcSetoid M) a=Quotient.mk (essentialArcSetoid M) b)
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (htransverse : ∀ q ∈ ArcSurgery.crossings M a b,
      ArcSurgery.CrossesInDisk M a b q)
    (p : S) (hp : p ∈ ArcSurgery.crossings M a b) :
    ∃ (f g : C(Interval,S)) (u v : S),
      IsEmbedding f ∧ IsEmbedding g ∧
      range f ⊆ a.val.image ∧ range g ⊆ b.val.image ∧
      f 0 = u ∧ g 0 = u ∧ f 1 = v ∧ g 1 = v ∧ u ≠ v ∧
      range f ∩ range g = {u,v} ∧
      v ∈ ArcSurgery.crossings M a b ∧
      (u ∈ ArcSurgery.crossings M a b ∨
        (u ∈ a.val.image ∩ b.val.image ∧ u ∈ (M.cover.branch : Set S))) ∧
      ∃ (hu : u ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (hv : v ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (α β : Path (⟨u,hu⟩ : ↑((M.cover.branch : Set S) \ {u})ᶜ) ⟨v,hv⟩),
        (∀ t : Interval, (α t : S) = f t) ∧
        (∀ t : Interval, (β t : S) = g t) ∧ α.Homotopic β := by
  classical
  rcases checkedRLNonloopEndpointOrientation M a b hab ha with ⟨h00,h11⟩ | ⟨h01,h10⟩
  · have hb : b.val.map 0≠b.val.map 1 := by
      simpa only [←h00,←h11] using ha
    obtain ⟨K,hzero,hinj,hends,hmarks,htop⟩ :=
      checkedRLNonloopSameClassAvoidingSweep M a b ha hb hab
    apply hAlignedSelector M a b ha
      ⟨K,hzero,(fun τ s t he => Or.inl (hinj τ he)),hends,hmarks,
        (fun t ht0 ht1 ht => htop t ht0 ht1 ht.1)⟩
      h00.symm h11.symm hfinite htransverse p hp
  · have hb : b.val.map 0≠b.val.map 1 := by
      intro he
      exact ha (h01.trans (he.symm.trans h10.symm))
    obtain ⟨c,hcmap,hc0,hc1,hcimage,hcclass⟩ := checkedRLNonloopOriginalImageReverse M b hb
    have hca0 : c.val.map 0=a.val.map 0 := hc0.trans h01.symm
    have hca1 : c.val.map 1=a.val.map 1 := hc1.trans h10.symm
    have hc : c.val.map 0≠c.val.map 1 := by
      simpa only [hca0,hca1] using ha
    have hac : Quotient.mk (essentialArcSetoid M) a=Quotient.mk (essentialArcSetoid M) c :=
      hab.trans hcclass.symm
    obtain ⟨K,hzero,hinj,hends,hmarks,htop⟩ :=
      checkedRLNonloopSameClassAvoidingSweep M a c ha hc hac
    have hCrossings : ArcSurgery.crossings M a c=ArcSurgery.crossings M a b := by
      unfold ArcSurgery.crossings arcInterior
      rw [hcimage]
    have hfiniteC : (ArcSurgery.crossings M a c).Finite := hCrossings.symm ▸ hfinite
    have hcrossC : ∀ q∈ArcSurgery.crossings M a c,ArcSurgery.CrossesInDisk M a c q := by
      intro q hq
      have hh := htransverse q (hCrossings ▸ hq)
      simpa only [ArcSurgery.CrossesInDisk,hcimage] using hh
    have hsubpaths := hAlignedSelector M a c ha
      ⟨K,hzero,(fun τ s t he => Or.inl (hinj τ he)),hends,hmarks,
        (fun t ht0 ht1 ht => htop t ht0 ht1 ht.1)⟩
      hca0 hca1 hfiniteC hcrossC p (hCrossings.symm ▸ hp)
    simpa only [hcimage,hCrossings] using hsubpaths

#print axioms actual_original_same_class_nonloop_subpaths_of_aligned_actual_sweep_selector_private
end CurveComplex.HyperellipticModel
