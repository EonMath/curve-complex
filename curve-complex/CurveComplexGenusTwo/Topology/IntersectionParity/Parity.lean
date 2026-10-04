import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import Mathlib
import CurveComplexGenusTwo.Topology.IntersectionParity.HomeomorphTransport
import CurveComplexGenusTwo.Topology.IntersectionParity.IsotopyParity
namespace CurveComplex.LocalSurgery

/- Candidate local auxiliary statement for F-Reviewer approval. This is an
   OPEN proof obligation, not an axiom or a dependency of the verified files.
   It records mod-two invariance of transverse intersection under the ambient
   isotopy classes used to define geometricIntersection. -/
theorem geometric_intersection_mod_two_actual
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a b : EssentialCurve S) (ht : Transverse a.val b.val) :
    Nat.ModEq 2
      (geometricIntersection (Quotient.mk (essentialCurveSetoid S) a)
        (Quotient.mk (essentialCurveSetoid S) b))
      ht.1.toFinset.card := by
  classical
  let α := Quotient.mk (essentialCurveSetoid S) a
  let β := Quotient.mk (essentialCurveSetoid S) b
  have hnonempty : (intersectionCounts α β).Nonempty := by
    exact ⟨ht.1.toFinset.card, a, b, rfl, rfl, ht, rfl⟩
  have hminimum : geometricIntersection α β ∈ intersectionCounts α β :=
    Nat.sInf_mem hnonempty
  obtain ⟨c, d, hc, hd, hcd, hcount⟩ := hminimum
  have hac : (essentialCurveSetoid S).r a c :=
    Quotient.exact hc.symm
  have hbd : (essentialCurveSetoid S).r b d :=
    Quotient.exact hd.symm
  obtain ⟨H, hH⟩ := hac
  obtain ⟨K, hK⟩ := hbd
  change Nat.ModEq 2 (geometricIntersection α β) ht.1.toFinset.card
  rw [hcount]
  obtain ⟨e, he⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
  have hfinal : H.finalMap = e := (funext he).symm
  have himage (q : Curve S) : (homeomorphCurve e q).image = e '' q.image :=
    Set.range_comp e q.map
  have haimage : (homeomorphCurve e a.val).image = c.val.image := by
    rw [himage, ← hfinal]
    exact hH
  let b' := homeomorphCurve e b.val
  obtain ⟨hetrans, hecount⟩ := transverse_homeomorph_count e a.val b.val ht
  have hcb' : Transverse c.val b' := by
    simpa only [Transverse, CrossesAt, haimage] using hetrans
  have hcb'count : hcb'.1.toFinset.card = ht.1.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hcb'.1]
    change (c.val.image ∩ (homeomorphCurve e b.val).image).ncard = ht.1.toFinset.card
    rw [← haimage, Set.ncard_eq_toFinset_card _ hetrans.1]
    exact hecount
  have hbb' : AmbientIsotopy.Rel b.val.image b'.image := by
    refine ⟨H, ?_⟩
    change H.finalMap '' b.val.image = (homeomorphCurve e b.val).image
    rw [himage, hfinal]
  have hb'd : AmbientIsotopy.Rel b'.image d.val.image :=
    (ambientIsotopy_equivalence (S := S)).trans
      ((ambientIsotopy_equivalence (S := S)).symm hbb') ⟨K, hK⟩
  obtain ⟨L, hL⟩ := hb'd
  have hparity : Nat.ModEq 2 hcb'.1.toFinset.card hcd.1.toFinset.card := by
    exact transverse_intersection_mod_two_ambient_isotopy c.val b' d.val hcb' hcd L hL
  rw [hcb'count] at hparity
  exact hparity.symm

end CurveComplex.LocalSurgery
