import CurveComplexGenusTwo.Dictionary.ActualCircle24Components
import Mathlib.Topology.Homeomorph.Lemmas
open Lean Elab Tactic in
elab "audit_main14_pairing_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in actual component pairing: {ax}"
  logInfo m!"Actual component pairing proof axiom audit: {found.toList}"
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 1000000
theorem actual_circle24_given_union_component_pairing (M : HyperellipticModel E S) (c d : Circle24 M)
    (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c.val.image)
      (M.cover.projection ⁻¹' d.val.image)) :
    ∃ a0 a1 b0 b1 : Curve E, ∃ H : AmbientIsotopy E,
      a0.image ∪ a1.image = M.cover.projection ⁻¹' c.val.image ∧
      b0.image ∪ b1.image = M.cover.projection ⁻¹' d.val.image ∧
      Disjoint a0.image a1.image ∧ Disjoint b0.image b1.image ∧
      M.cover.deck '' a0.image = a1.image ∧ M.cover.deck '' b0.image = b1.image ∧
      H.finalMap '' a0.image = b0.image ∧ H.finalMap '' a1.image = b1.image ∧
      Set.BijOn M.cover.projection a0.image c.val.image ∧
      Set.BijOn M.cover.projection a1.image c.val.image ∧
      Set.BijOn M.cover.projection b0.image d.val.image ∧
      Set.BijOn M.cover.projection b1.image d.val.image := by
  audit_main14_pairing_base3
    classical
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    obtain ⟨a0,a1,ha,had,hadeck,hap0,hap1,hac0,hac1⟩ := M.actual_circle24_components_project_bijectively c
    obtain ⟨b0,b1,hb,hbd,hbdeck,hbp0,hbp1,hbc0,hbc1⟩ := M.actual_circle24_components_project_bijectively d
    let z0 : Circle := Classical.choice inferInstance
    obtain ⟨H,hH⟩ := hup
    obtain ⟨e,he⟩ := H.homeomorphism_at 1
    have hef : H.finalMap = e := funext (fun x => (he x).symm)
    have hunion : e '' (a0.image ∪ a1.image) = b0.image ∪ b1.image := by
      rw [ha,hb,← hef]; exact hH
    have hpair (a0 a1 b0 b1 : Curve E)
        (had : Disjoint a0.image a1.image) (hbd : Disjoint b0.image b1.image)
        (hunion : e '' (a0.image ∪ a1.image) = b0.image ∪ b1.image)
        (hfirst : e '' a0.image = b0.image) : e '' a1.image = b1.image := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        have hx : e y ∈ b0.image ∪ b1.image := hunion ▸ ⟨y,Or.inr hy,rfl⟩
        rcases hx with hx | hx
        · obtain ⟨z,hz,hzy⟩ := hfirst.symm ▸ hx
          exact False.elim (Set.disjoint_left.mp had hz ((e.injective hzy).symm ▸ hy))
        · exact hx
      · intro hx
        have hxpre : x ∈ e '' (a0.image ∪ a1.image) := by
          rw [hunion]; exact Or.inr hx
        obtain ⟨y,hy,hyx⟩ := hxpre
        rcases hy with hy | hy
        · have hxb : x ∈ b0.image := hfirst ▸ ⟨y,hy,hyx⟩
          exact False.elim (Set.disjoint_left.mp hbd hxb hx)
        · exact ⟨y,hy,hyx⟩
    have hImageComp (b0 b1 : Curve E) (hbd : Disjoint b0.image b1.image)
        (hunion : e '' (a0.image ∪ a1.image) = b0.image ∪ b1.image)
        (hx : e (a0.map z0) ∈ b0.image) : e '' a0.image = b0.image := by
      have hsource : a0.map z0 ∈ a0.image := Set.mem_range_self _
      have hs := disjoint_curve_connectedComponentIn a0 a1 had (a0.map z0) hsource
      have ht := disjoint_curve_connectedComponentIn b0 b1 hbd (e (a0.map z0)) hx
      have hh := e.image_connectedComponentIn (s := a0.image ∪ a1.image)
        (x := a0.map z0) (by exact Or.inl hsource)
      rw [hs,hunion,ht] at hh
      exact hh
    have hx : e (a0.map z0) ∈ b0.image ∪ b1.image :=
      hunion ▸ ⟨a0.map z0,Or.inl (Set.mem_range_self _),rfl⟩
    rcases hx with hx | hx
    · have h0 := hImageComp b0 b1 hbd hunion hx
      have h1 := hpair a0 a1 b0 b1 had hbd hunion h0
      exact ⟨a0,a1,b0,b1,H,ha,hb,had,hbd,hadeck,hbdeck,by rw [hef];exact h0,by rw [hef];exact h1,hap0,hap1,hbp0,hbp1⟩
    · have hunion' : e '' (a0.image ∪ a1.image) = b1.image ∪ b0.image :=
        hunion.trans (Set.union_comm _ _)
      have h0 := hImageComp b1 b0 hbd.symm hunion' hx
      have h1 := hpair a0 a1 b1 b0 had hbd.symm hunion' h0
      have hbdeck' : M.cover.deck '' b1.image = b0.image := by
        rw [← hbdeck,Set.image_image]
        have hi : (fun x : E => M.cover.deck (M.cover.deck x)) = id := funext M.cover.deck_involution
        rw [hi,Set.image_id]
      exact ⟨a0,a1,b1,b0,H,ha,(Set.union_comm _ _).trans hb,had,hbd.symm,hadeck,hbdeck',
        by rw [hef];exact h0,by rw [hef];exact h1,hap0,hap1,hbp1,hbp0⟩
end CurveComplex.HyperellipticModel
