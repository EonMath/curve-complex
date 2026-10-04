import SquareRootContracts

namespace AlternatingSphereCover
abbrev PatchRaw := {x : Raw // x.val.1 ∈ positivePatch}

def patchSetoid : Setoid PatchRaw := Setoid.comap Subtype.val setoid

abbrev PatchTotal := Quotient patchSetoid

def patchProjection : PatchTotal → Total := Quotient.map Subtype.val (by intro x y h; exact h)

theorem patchProjection_mem (x : PatchTotal) : projection (patchProjection x) ∈ positivePatch := by
  induction x using Quotient.inductionOn with
  | h x => exact x.property

def patchToOpen (x : PatchTotal) : {q : Total // projection q ∈ positivePatch} :=
  ⟨patchProjection x, patchProjection_mem x⟩

theorem patchToOpen_isHomeomorph : IsHomeomorph patchToOpen := by
  have hc : Continuous patchToOpen := by
    apply Continuous.subtype_mk
    exact (continuous_quotient_mk'.comp continuous_subtype_val).quotient_lift _
  have hi : Function.Injective patchToOpen := by
    intro x y h
    have he := congrArg Subtype.val h
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        change Quotient.mk setoid x.val = Quotient.mk setoid y.val at he
        apply Quotient.sound
        exact (Quotient.exact he : setoid x.val y.val)
  apply isHomeomorph_iff_isQuotientMap_injective.mpr
  refine ⟨?_, hi⟩
  apply Topology.IsQuotientMap.of_comp (f := Quotient.mk patchSetoid)
    continuous_quotient_mk' hc
  exact isQuotientMap_quotient_mk'.restrictPreimage_isOpen
    (positivePatch_isOpen.preimage projection_continuous)

noncomputable def patchRoot : PatchTotal → ℂ :=
  Quotient.lift (fun x : PatchRaw => rawRoot x.val) (by intro x y h; exact rawRoot_respects x.val y.val x.property h)

theorem patchRoot_continuous : Continuous patchRoot := by
  exact (rawRoot_continuous.comp continuous_subtype_val).quotient_lift _

theorem patchRoot_injective : Function.Injective patchRoot := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      apply Quotient.sound
      exact (rawRoot_eq_iff_rel x.val y.val x.property y.property).mp h

theorem patchRoot_sq (x : PatchTotal) :
    (patchRoot x)^2 = localPlane (projection (patchProjection x)) := by
  induction x using Quotient.inductionOn with
  | h x => exact rawRoot_sq x.val

end AlternatingSphereCover
