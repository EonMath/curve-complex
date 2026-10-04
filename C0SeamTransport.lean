import C0RelativeCarrierScaffold
import CurveComplexGenusTwo.Foundations.FullSubcomplex
import CurveComplexGenusTwo.Foundations.EdgeHomotopy
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Product

open CurveComplex Set Topology
attribute [local instance] instDecidable_c0RelativeCarrierScaffold instDecidableEq_c0RelativeCarrierScaffold
set_option autoImplicit false

namespace C0RelativeCarrier

/-- A closed-loop free contraction has an actual seam at every time. Its moving
basepoint is transported back to the original x in the based conclusion. -/
theorem based_loop_nullhomotopic_of_seam_preserving_free_contraction
    {X : Type*} [TopologicalSpace X] {x : X} (p : Path x x) (c : X)
    (H : ContinuousMap.HomotopyWith p.toContinuousMap (ContinuousMap.const unitInterval c)
      (fun q : C(unitInterval,X) => q 0 = q 1)) :
    Path.Homotopic p (Path.refl x) := by
  let i : Path (0 : unitInterval) 1 :=
    { toFun := id
      continuous_toFun := continuous_id
      source' := rfl
      target' := rfl }
  let a := (Path.refl (0 : unitInterval)).prod i
  let b := i.prod (Path.refl (1 : unitInterval))
  let d := i.prod (Path.refl (0 : unitInterval))
  let e := (Path.refl (1 : unitInterval)).prod i
  have hi : Path.Homotopic ((Path.refl 0).trans i) (i.trans (Path.refl 1)) :=
    (Path.Homotopic.refl_trans i).trans (Path.Homotopic.trans_refl i).symm
  have hsquare : Path.Homotopic (a.trans b) (d.trans e) := by
    obtain ⟨F⟩ := hi
    exact ⟨(Path.Homotopic.prodHomotopy F F.symm).cast
      (Path.trans_prod_eq_prod_trans _ _ _ _).symm
      (Path.trans_prod_eq_prod_trans _ _ _ _).symm⟩
  have h00 : x = H (0, 0) := by simp
  have h01 : x = H (0, 1) := by simp
  have h10 : c = H (1, 0) := by simp
  have h11 : c = H (1, 1) := by simp
  let r : Path x c := ((H.toHomotopy.evalAt 0).cast (by simp) rfl)
  have ha : (a.map H.continuous).cast h00 h01 = p := by
    ext t
    change H (0, t) = p t
    simp
  have hb : (b.map H.continuous).cast h01 h11 = r := by
    ext t
    change H (t, 1) = H (t, 0)
    exact (H.prop t).symm
  have hd : (d.map H.continuous).cast h00 h10 = r := by
    ext t
    rfl
  have he : (e.map H.continuous).cast h10 h11 = Path.refl c := by
    ext t
    change H (1, t) = c
    simp
  have hroute := (hsquare.map H.toContinuousMap).pathCast h00 h11
  rw [Path.map_trans, Path.cast_trans _ _ h00 h01 h11, ha, hb,
    Path.map_trans, Path.cast_trans _ _ h00 h10 h11, hd, he] at hroute
  have h : Path.Homotopic (p.trans r) r := hroute.trans (Path.Homotopic.trans_refl r)
  calc
    Path.Homotopic p (p.trans (Path.refl x)) := (Path.Homotopic.trans_refl p).symm
    Path.Homotopic (p.trans (Path.refl x)) (p.trans (r.trans r.symm)) :=
      (Path.Homotopic.refl p).hcomp (Path.Homotopic.trans_symm r).symm
    Path.Homotopic (p.trans (r.trans r.symm)) ((p.trans r).trans r.symm) :=
      (Path.Homotopic.trans_assoc p r r.symm).symm
    Path.Homotopic ((p.trans r).trans r.symm) (r.trans r.symm) :=
      h.hcomp (Path.Homotopic.refl r.symm)
    Path.Homotopic (r.trans r.symm) (Path.refl x) := Path.Homotopic.trans_symm r

end C0RelativeCarrier
