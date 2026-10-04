import CurveComplexGenusTwo.Cover.ActualWholeBankSectorSide
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import Mathlib
open Set Metric Topology
namespace AlternatingSphereCover
set_option maxHeartbeats 1000000
/-- Transfer the proved boundary-fixed local contraction to the actual source
five-edge tree, including exact fibers and an actual quotient homeomorphism. -/
theorem actual_source_primal_tree_collapse_transfer :
    let D := Set.Icc (-2:ℝ) 2 × Set.Icc (-2:ℝ) 2
    let K : Set D := {v | v.1.val=0 ∧ |v.2.val|≤1}
    let A : Set Total := northDiskFace true ''
      {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
        (∃ i : Fin 6, i≠0 ∧ closedArcSector i p) ∧ v=diskBoundaryPoint p hp}
    ∀ E : C(D,Total), IsEmbedding E → E '' K=A →
      (∀ v, (|v.1.val|<2 ∧ |v.2.val|<2) → E v∈interior (Set.range E)) →
    ∀ F : C(D,D), Function.Surjective F →
      (∀ v w, F v=F w ↔ v=w ∨ (v∈K ∧ w∈K)) →
      (∀ v, (|v.1.val|=2 ∨ |v.2.val|=2) → F v=v) →
    ∃ G : C(Total,Total),
      (∀ v, G (E v)=E (F v)) ∧
      (∀ z, z∉interior (Set.range E) → G z=z) ∧
      Function.Surjective G ∧
      (∀ z w, G z=G w ↔ z=w ∨ (z∈A ∧ w∈A)) ∧
      ∃ h : Quotient (Relation.EqvGen.setoid (fun z w : Total => z∈A ∧ w∈A)) ≃ₜ Total,
        ∀ z, h (Quotient.mk _ z)=G z := by
  dsimp only
  intro E hE hEK hEint F hFs hFker hFboundary
  classical
  letI : T2Space Total := actual_t2Space
  letI : CompactSpace Total := total_compact
  let D := Set.Icc (-2:ℝ) 2 × Set.Icc (-2:ℝ) 2
  let K : Set D := {v | v.1.val=0 ∧ |v.2.val|≤1}
  let A : Set Total := northDiskFace true ''
    {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
      (∃ i : Fin 6, i≠0 ∧ closedArcSector i p) ∧ v=diskBoundaryPoint p hp}
  have hEKexact : E '' K=A := hEK
  let R := Set.range E
  have hRc : IsClosed R := (isCompact_range E.continuous).isClosed
  let inv : R → D := hE.toHomeomorph.symm
  have hinv (v : D) : inv ⟨E v,⟨v,rfl⟩⟩=v := hE.toHomeomorph.symm_apply_apply v
  have hEinv (z : Total) (hz : z∈R) : E (inv ⟨z,hz⟩)=z :=
    congrArg Subtype.val (hE.toHomeomorph.apply_symm_apply ⟨z,hz⟩)
  let inner : C(R,Total) := ⟨fun z => E (F (inv z)),
    E.continuous.comp (F.continuous.comp hE.toHomeomorph.symm.continuous)⟩
  let g : Total → Total := Function.extend Subtype.val inner id
  have hgin (z : Total) (hz : z∈R) : g z=E (F (inv ⟨z,hz⟩)) :=
    Subtype.val_injective.extend_apply _ _ ⟨z,hz⟩
  have hgc : ContinuousOn g R := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : R.domRestrict g=inner := funext (fun z => hgin z.val z.property)
    rw [heq];exact inner.continuous
  have hboundary (z : Total) (hz : z∈frontier R) : g z=z := by
    rw [hRc.frontier_eq] at hz
    let v := inv ⟨z,hz.1⟩
    have hev : E v=z := hEinv z hz.1
    have hb : |v.1.val|=2 ∨ |v.2.val|=2 := by
      have hx : |v.1.val|≤2 := abs_le.mpr v.1.property
      have hy : |v.2.val|≤2 := abs_le.mpr v.2.property
      by_contra hn
      push_neg at hn
      have hi := hEint v ⟨lt_of_le_of_ne hx hn.1,lt_of_le_of_ne hy hn.2⟩
      rw [hev] at hi
      exact hz.2 hi
    rw [hgin z hz.1]
    change E (F v)=z
    rw [hFboundary v hb,hev]
  let G : C(Total,Total) := ⟨R.piecewise g id,
    continuous_piecewise hboundary (by rw [hRc.closure_eq];exact hgc) continuous_id.continuousOn⟩
  have hGpin (v : D) : G (E v)=E (F v) := by
    change R.piecewise g id (E v)=_
    rw [Set.piecewise_eq_of_mem R g id (show E v∈R from ⟨v,rfl⟩)]
    rw [hgin (E v) ⟨v,rfl⟩,hinv]
  have hGout (z : Total) (hz : z∉R) : G z=z :=
    Set.piecewise_eq_of_notMem R g id hz
  have hGsupport (z : Total) (hz : z∉interior R) : G z=z := by
    by_cases hr : z∈R
    · have hfr : z∈frontier R := by rw [hRc.frontier_eq];exact ⟨hr,hz⟩
      change R.piecewise g id z=z
      rw [Set.piecewise_eq_of_mem R g id hr,hboundary z hfr]
    · exact hGout z hr
  have hAsub : A⊆R := by
    rw [←hEKexact]
    rintro z ⟨v,hv,rfl⟩;exact ⟨v,rfl⟩
  have hEA (v : D) : E v∈A ↔ v∈K := by
    rw [←hEKexact]
    constructor
    · rintro ⟨w,hw,he⟩
      exact hE.injective he ▸ hw
    · intro hv;exact ⟨v,hv,rfl⟩
  have hGsurj : Function.Surjective G := by
    intro z
    by_cases hz : z∈R
    · obtain ⟨v,rfl⟩ := hz
      obtain ⟨u,hu⟩ := hFs v
      exact ⟨E u,(hGpin u).trans (congrArg E hu)⟩
    · exact ⟨z,hGout z hz⟩
  have hGker (z w : Total) : G z=G w ↔ z=w ∨ (z∈A ∧ w∈A) := by
    by_cases hz : z∈R
    · obtain ⟨v,rfl⟩ := hz
      by_cases hw : w∈R
      · obtain ⟨u,rfl⟩ := hw
        rw [hGpin,hGpin]
        constructor
        · intro he
          rcases (hFker v u).mp (hE.injective he) with he|he
          · exact Or.inl (congrArg E he)
          · exact Or.inr ⟨(hEA v).mpr he.1,(hEA u).mpr he.2⟩
        · rintro (he|he)
          · exact congrArg (fun x => E (F x)) (hE.injective he)
          · exact congrArg E ((hFker v u).mpr (Or.inr ⟨(hEA v).mp he.1,(hEA u).mp he.2⟩))
      · rw [hGpin,hGout w hw]
        constructor
        · intro he
          exact False.elim (hw (he ▸ Set.mem_range_self (F v)))
        · rintro (he|he)
          · exact False.elim (hw (he ▸ Set.mem_range_self v))
          · exact False.elim (hw (hAsub he.2))
    · by_cases hw : w∈R
      · obtain ⟨u,rfl⟩ := hw
        rw [hGout z hz,hGpin]
        constructor
        · intro he
          exact False.elim (hz (he.symm ▸ Set.mem_range_self (F u)))
        · rintro (he|he)
          · exact False.elim (hz (he.symm ▸ Set.mem_range_self u))
          · exact False.elim (hz (hAsub he.1))
      · rw [hGout z hz,hGout w hw]
        constructor
        · exact Or.inl
        · rintro (he|he)
          · exact he
          · exact False.elim (hz (hAsub he.1))
  let Q := Quotient (Relation.EqvGen.setoid (fun z w : Total => z∈A ∧ w∈A))
  have hrespect (z w : Total) (h : Relation.EqvGen (fun z w : Total => z∈A ∧ w∈A) z w) : G z=G w := by
    induction h with
    | rel z w h => exact (hGker z w).mpr (Or.inr h)
    | refl z => rfl
    | symm z w h ih => exact ih.symm
    | trans z w u h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  let q : Q → Total := Quotient.lift G hrespect
  have hqc : Continuous q := G.continuous.quotient_lift _
  have hqi : Function.Injective q := by
    intro x y he
    induction x using Quotient.inductionOn with
    | _ z =>
      induction y using Quotient.inductionOn with
      | _ w =>
        change G z=G w at he
        rcases (hGker z w).mp he with he|he
        · exact congrArg (Quotient.mk _) he
        · exact Quotient.sound (Relation.EqvGen.rel z w he)
  have hqs : Function.Surjective q := by
    intro z
    obtain ⟨w,hw⟩ := hGsurj z
    exact ⟨Quotient.mk _ w,hw⟩
  let e := Equiv.ofBijective q ⟨hqi,hqs⟩
  let Hq : Q ≃ₜ Total := (show Continuous (e : Q → Total) from hqc).homeoOfEquivCompactToT2
  exact ⟨G,hGpin,hGsupport,hGsurj,hGker,Hq,fun _ => rfl⟩
end AlternatingSphereCover
