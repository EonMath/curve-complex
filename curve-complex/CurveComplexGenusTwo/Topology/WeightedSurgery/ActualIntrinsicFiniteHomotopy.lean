import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualIntrinsicPotentialDescent
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualIntrinsicClockCompatibility
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualClockRescaling

namespace CurveComplex.HyperellipticModel.ArcSurgery.ActualFiniteEventTrace
open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
variable {M : HyperellipticModel E S} [LinearOrder (EssentialArcClass M)]
  {anchor : EssentialMarkedArc M}
local notation "K" => geometricComplex (actualA M)
local notation "Stage" σ => CurveComplex.RealizationPoint (CurveComplex.fullSubcomplex K (· ∈ σ))
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Genuine actual finite surgery homotopy at the SOURCE intrinsic depth tθ.
The endpoint budget is proved from actual minimum cardinalities and actual
branch descent, rather than supplied as a matching-time assumption. -/
noncomputable def intrinsicHomotopy {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) :
    ContinuousMap.Homotopy
      ⟨CurveComplex.fullToAmbient K (· ∈ σ), CurveComplex.fullToAmbient_continuous K _⟩ T.endpoint where
  toFun := T.intrinsicDepthMap
  continuous_toFun := T.intrinsicDepthMap.continuous
  map_zero_left := T.intrinsicDepthMap_starts
  map_one_left p := by
    change T.atDepth (1 * intrinsicThickness (anchor := anchor) σ p,p) = T.endpoint p
    rw [one_mul]
    exact T.atDepth_after p _ (T.totalWidth_le_intrinsicThickness p)

theorem intrinsicHomotopy_face_independent
    {σ τ : Finset (ActiveVertex (actualA M))}
    {T : ActualFiniteEventTrace M anchor σ} {U : ActualFiniteEventTrace M anchor τ}
    (h : SameGeometry T U) (p : Stage σ) (q : Stage τ)
    (hpq : CurveComplex.fullToAmbient K (· ∈ σ) p = CurveComplex.fullToAmbient K (· ∈ τ) q)
    (t : CurveComplex.EdgeTime) : T.intrinsicHomotopy (t,p) = U.intrinsicHomotopy (t,q) :=
  intrinsicDepthMap_face_independent h p q hpq t

theorem intrinsicHomotopy_finishes_by_budget {σ : Finset (ActiveVertex (actualA M))}
    (T : ActualFiniteEventTrace M anchor σ) (p : Stage σ) (t : CurveComplex.EdgeTime)
    (ht : T.totalWidth p ≤ t.val * intrinsicThickness (anchor := anchor) σ p) :
    T.intrinsicHomotopy (t,p) = T.endpoint p := T.atDepth_after p _ ht

/-- A zero-mass geometric cut preserves the actual intrinsic clock of the
point transferred into the next full weak realization. -/
theorem zeroMass_intrinsicThickness {σ : Finset (ActiveVertex (actualA M))}
    (c : ActualEventCertificate M anchor σ) (p : Stage σ) (hz : c.selectedMass p = 0) :
    intrinsicThickness (anchor := anchor) c.nextFace (c.endpointToNext p) =
      intrinsicThickness (anchor := anchor) σ p := by
  have hb := c.intrinsic_coefficient_balance p
  simpa [ActualEventCertificate.endpointScale, hz] using hb

/-- Zero-width deletion agrees at the SAME original source time, without
inserting a pause or changing the intrinsic tθ parametrization. -/
theorem intrinsicHomotopy_cut_zeroMass {σ : Finset (ActiveVertex (actualA M))}
    (c : ActualEventCertificate M anchor σ) (T : ActualFiniteEventTrace M anchor c.nextFace)
    (p : Stage σ) (hz : c.selectedMass p = 0) (t : CurveComplex.EdgeTime) :
    (ActualFiniteEventTrace.cut c T).intrinsicHomotopy (t,p) =
      T.intrinsicHomotopy (t,c.endpointToNext p) := by
  change (ActualFiniteEventTrace.cut c T).atDepth
    (t.val * intrinsicThickness (anchor := anchor) σ p,p) =
    T.atDepth (t.val * intrinsicThickness (anchor := anchor) c.nextFace (c.endpointToNext p),
      c.endpointToNext p)
  rw [zeroMass_intrinsicThickness c p hz]
  exact atDepth_cut_zeroMass c T p hz _
    (mul_nonneg t.property.1 (intrinsicThickness_nonneg σ p))

end CurveComplex.HyperellipticModel.ArcSurgery.ActualFiniteEventTrace
