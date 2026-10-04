import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualMarkedCircleParallel
import CurveComplexGenusTwo.Dictionary.ActualDictionaryEssential
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalFirstDiskActualCoverAssemblyProved
import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc

open Lean Elab Tactic in
elab "audit_main14_paired_reference_returning_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in actual paired reference returning disk: {ax}"
  logInfo m!"Actual paired reference returning disk proof axiom audit: {found.toList}"
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000
theorem actual_given_paired_component_reference_returning_disk (M : HyperellipticModel E S) (a b r : EssentialCurve E) (c : PuncturedCircle M)
    (hb : b.val.image ⊆ M.cover.projection ⁻¹' c.image)
    (hr : r.val.image ⊆ M.cover.projection ⁻¹' c.image)
    (ht : Transverse a.val r.val) (hiso : AmbientIsotopy.Rel a.val.image b.val.image)
    (hne : (a.val.image ∩ r.val.image).Nonempty) :
    Nonempty (LocalSurgery.TwoCurveDisk a.val r.val) := by
  audit_main14_paired_reference_returning_base3
    have hCompare (M : HyperellipticModel E S) (a b : EssentialCurve E) (c : PuncturedCircle M)
        (hb : b.val.image ⊆ M.cover.projection ⁻¹' c.image)
        (hiso : AmbientIsotopy.Rel a.val.image b.val.image) :
        ∃ a' : EssentialCurve E, AmbientIsotopy.Rel a.val.image a'.val.image ∧
          Disjoint a'.val.image (M.cover.projection ⁻¹' c.image) := by
      classical
      obtain ⟨D,hmarks,hdisjoint⟩ := M.actual_marked_punctured_circle_parallel_isotopy c
      have hdown : MarkedIsotopyRel M c.image (D.finalMap '' c.image) := ⟨D,hmarks,rfl⟩
      obtain ⟨H,hH⟩ := M.marked_isotopy_preimage hdown
      obtain ⟨g,hg⟩ := H.homeomorphism_at 1
      have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
      let d : Curve E := ⟨g ∘ b.val.map,g.isEmbedding.comp b.val.embedded⟩
      have hd : d.image=H.finalMap '' b.val.image := by
        change Set.range (g ∘ b.val.map)=H.finalMap '' Set.range b.val.map
        rw [Set.range_comp,hfinal]
      have hbd : AmbientIsotopy.Rel b.val.image d.image := ⟨H,hd.symm⟩
      have hess : Essential d := (essential_isotopy_invariant hbd).mp b.property
      let a' : EssentialCurve E := ⟨d,hess⟩
      have hnew : a'.val.image ⊆ M.cover.projection ⁻¹' (D.finalMap '' c.image) := by
        rw [hd]
        rw [←hH]
        exact Set.image_mono hb
      exact ⟨a',ambientIsotopy_equivalence.trans hiso hbd,
        (hdisjoint.preimage M.cover.projection).mono hnew Set.Subset.rfl⟩
    classical
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    obtain ⟨a',hi,hdisjoint⟩ := hCompare M a b c hb hiso
    have hdisc : Disjoint a'.val.image r.val.image := hdisjoint.mono Set.Subset.rfl hr
    have he : a'.val.image ∩ r.val.image=∅ := Set.disjoint_iff_inter_eq_empty.mp hdisc
    have ht' : Transverse a'.val r.val := by
      refine ⟨?_,?_⟩
      · rw [he]; exact Set.finite_empty
      · intro p hp; rw [he] at hp; exact False.elim hp
    have hzero : ht'.1.toFinset.card=0 := by rw [←Set.ncard_eq_toFinset_card _ ht'.1,he,Set.ncard_empty]
    have hpos : 0 < ht.1.toFinset.card := by
      apply Finset.card_pos.mpr
      obtain ⟨x,hx⟩ := hne
      exact ⟨x,(Set.Finite.mem_toFinset ht.1).mpr hx⟩
    obtain ⟨u,v,huv,hu,hv,f,g,hf,hfa,hgb,hclean,hhom⟩ :=
      LocalSurgery.count_decreasing_isotopy_has_returning_subarc a r a' ht hi ht'
        (by rw [hzero]; exact hpos)
    exact LocalSurgery.actual_original_returning_subarc_produces_two_curve_disk
      E 2 (by omega) M.genusTwo a r ht u v huv f g hf hfa hgb hclean hhom

end CurveComplex.HyperellipticModel
