import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14Circle33StrictIterationStep

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
set_option maxHeartbeats 8000000
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]

/-- Actual finite elimination of every empty upstairs full-preimage bigon.
The endpoint is bigon-free, retains the original marked circle isotopies and
upstairs vertex classes, and remains a transverse literal full-preimage pair.
No existence/decrease/elimination certificate is supplied. The separate source
bigon criterion is needed to turn this bigon-free endpoint into disjointness. -/
theorem circle33_actual_finite_empty_bigon_elimination
    (M : HyperellipticModel E S) (a b : EssentialCurve E) (c d : Circle33 M)
    (ht : Transverse a.val b.val)
    (ha : a.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.val.image)
    (htbase : Transverse c.val.curve d.val.curve) :
    ∃ a' b' : EssentialCurve E, ∃ c' d' : Circle33 M,
      a'.val.image = M.cover.projection ⁻¹' c'.val.image ∧
      b'.val.image = M.cover.projection ⁻¹' d'.val.image ∧
      Quotient.mk (essentialCurveSetoid E) a' = Quotient.mk (essentialCurveSetoid E) a ∧
      Quotient.mk (essentialCurveSetoid E) b' = Quotient.mk (essentialCurveSetoid E) b ∧
      MarkedIsotopyRel M c.val.image c'.val.image ∧
      MarkedIsotopyRel M d.val.image d'.val.image ∧
      Transverse a'.val b'.val ∧ Transverse c'.val.curve d'.val.curve ∧
      (a'.val.image ∩ b'.val.image).ncard ≤ (a.val.image ∩ b.val.image).ncard ∧
      ¬ ∃ B : LocalSurgery.TwoCurveDisk a'.val b'.val,
        Disjoint B.openInterior (a'.val.image ∪ b'.val.image) := by
  classical
  have aux : ∀ n : ℕ, ∀ (a b : EssentialCurve E) (c d : Circle33 M),
      Transverse a.val b.val →
      a.val.image = M.cover.projection ⁻¹' c.val.image →
      b.val.image = M.cover.projection ⁻¹' d.val.image →
      Transverse c.val.curve d.val.curve →
      (a.val.image ∩ b.val.image).ncard = n →
      ∃ a' b' : EssentialCurve E, ∃ c' d' : Circle33 M,
        a'.val.image = M.cover.projection ⁻¹' c'.val.image ∧
        b'.val.image = M.cover.projection ⁻¹' d'.val.image ∧
        Quotient.mk (essentialCurveSetoid E) a' = Quotient.mk (essentialCurveSetoid E) a ∧
        Quotient.mk (essentialCurveSetoid E) b' = Quotient.mk (essentialCurveSetoid E) b ∧
        MarkedIsotopyRel M c.val.image c'.val.image ∧
        MarkedIsotopyRel M d.val.image d'.val.image ∧
        Transverse a'.val b'.val ∧ Transverse c'.val.curve d'.val.curve ∧
        (a'.val.image ∩ b'.val.image).ncard ≤ n ∧
        ¬ ∃ B : LocalSurgery.TwoCurveDisk a'.val b'.val,
          Disjoint B.openInterior (a'.val.image ∪ b'.val.image) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b c d ht ha hb htbase hcard
      by_cases hbigon : ∃ B : LocalSurgery.TwoCurveDisk a.val b.val,
        Disjoint B.openInterior (a.val.image ∪ b.val.image)
      · obtain ⟨B,hempty⟩ := hbigon
        obtain ⟨a₁,b₁,c₁,d₁,ha₁,hb₁,hac₁,hbc₁,hci₁,hdi₁,ht₁,htbase₁,hdrop⟩ :=
          M.circle33_actual_strict_bigon_iteration_step a b ht B c d ha hb htbase hempty
        have hlt : (a₁.val.image ∩ b₁.val.image).ncard < n := by rw [← hcard]; exact hdrop
        obtain ⟨a₂,b₂,c₂,d₂,ha₂,hb₂,hac₂,hbc₂,hci₂,hdi₂,ht₂,htbase₂,hcount₂,hfree₂⟩ :=
          ih (a₁.val.image ∩ b₁.val.image).ncard hlt a₁ b₁ c₁ d₁ ht₁ ha₁ hb₁ htbase₁ rfl
        refine ⟨a₂,b₂,c₂,d₂,ha₂,hb₂,hac₂.trans hac₁,hbc₂.trans hbc₁,
          (markedIsotopy_equivalence M).trans hci₁ hci₂,
          (markedIsotopy_equivalence M).trans hdi₁ hdi₂,ht₂,htbase₂,?_,hfree₂⟩
        exact hcount₂.trans (Nat.le_of_lt hlt)
      · exact ⟨a,b,c,d,ha,hb,rfl,rfl,(markedIsotopy_equivalence M).refl _,
          (markedIsotopy_equivalence M).refl _,ht,htbase,by omega,hbigon⟩
  exact aux _ a b c d ht ha hb htbase rfl

/-- In particular, arbitrary original upstairs ambient isotopy remains an
actual ambient isotopy between the bigon-free endpoint full preimages. No
isotopy of that endpoint or minimum-position certificate is an input. -/
theorem circle33_isotopic_actual_finite_empty_bigon_elimination
    (M : HyperellipticModel E S) (a b : EssentialCurve E) (c d : Circle33 M)
    (ht : Transverse a.val b.val)
    (ha : a.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.val.image)
    (htbase : Transverse c.val.curve d.val.curve)
    (hiso : AmbientIsotopy.Rel a.val.image b.val.image) :
    ∃ a' b' : EssentialCurve E, ∃ c' d' : Circle33 M,
      a'.val.image = M.cover.projection ⁻¹' c'.val.image ∧
      b'.val.image = M.cover.projection ⁻¹' d'.val.image ∧
      MarkedIsotopyRel M c.val.image c'.val.image ∧
      MarkedIsotopyRel M d.val.image d'.val.image ∧
      AmbientIsotopy.Rel a'.val.image b'.val.image ∧
      Transverse a'.val b'.val ∧ Transverse c'.val.curve d'.val.curve ∧
      ¬ ∃ B : LocalSurgery.TwoCurveDisk a'.val b'.val,
        Disjoint B.openInterior (a'.val.image ∪ b'.val.image) := by
  obtain ⟨a',b',c',d',ha',hb',hca,hcb,hci,hdi,ht',htbase',hcount,hfree⟩ :=
    M.circle33_actual_finite_empty_bigon_elimination a b c d ht ha hb htbase
  have hia : AmbientIsotopy.Rel a'.val.image a.val.image := Quotient.exact hca
  have hib : AmbientIsotopy.Rel b'.val.image b.val.image := Quotient.exact hcb
  have hiab : AmbientIsotopy.Rel a'.val.image b'.val.image :=
    ambientIsotopy_equivalence.trans (ambientIsotopy_equivalence.trans hia hiso)
      (ambientIsotopy_equivalence.symm hib)
  exact ⟨a',b',c',d',ha',hb',hci,hdi,hiab,ht',htbase',hfree⟩
end CurveComplex.HyperellipticModel
