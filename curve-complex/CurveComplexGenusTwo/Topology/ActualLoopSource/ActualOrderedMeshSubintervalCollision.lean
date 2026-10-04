import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMaxNormSquareBoundaryCover
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Distinct actual mesh intervals can meet only at parameter endpoints. -/
theorem actual_ordered_mesh_subinterval_collision
    {m : ℕ} (mesh : Fin (m+2) → Interval) (hmono : StrictMono mesh)
    (i j : Fin (m+1)) (t u : Interval)
    (he : Icc.convexComb (mesh i.castSucc) (mesh i.succ) t=
      Icc.convexComb (mesh j.castSucc) (mesh j.succ) u) :
    (i=j ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1)) := by
  have hs (k : Fin (m+1)) : (mesh k.castSucc).val<(mesh k.succ).val :=
    hmono (by change k.val< k.val+1; omega)
  have heR := congrArg Subtype.val he
  change (1-t.val)*(mesh i.castSucc).val+t.val*(mesh i.succ).val=
    (1-u.val)*(mesh j.castSucc).val+u.val*(mesh j.succ).val at heR
  by_cases hij : i=j
  · left
    refine ⟨hij,?_⟩
    subst j
    apply Subtype.ext
    have hp : (t.val-u.val)*((mesh i.succ).val-(mesh i.castSucc).val)=0 := by
      nlinarith only [heR]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (ne_of_gt (sub_pos.mpr (hs i))))
  · right
    rcases lt_or_gt_of_ne hij with hij | hji
    · have horder : (mesh i.succ).val≤(mesh j.castSucc).val :=
        hmono.monotone (by change i.val+1≤ j.val; exact hij)
      have hi := Icc.convexComb_le (hs i).le t
      have hj := Icc.le_convexComb (hs j).le u
      change (1-t.val)*(mesh i.castSucc).val+t.val*(mesh i.succ).val≤(mesh i.succ).val at hi
      change (mesh j.castSucc).val≤(1-u.val)*(mesh j.castSucc).val+u.val*(mesh j.succ).val at hj
      have ht : t=1 := by
        apply Subtype.ext
        change t.val=1
        nlinarith only [hi,hj,horder,heR,hs i,t.property.2]
      have hu : u=0 := by
        apply Subtype.ext
        change u.val=0
        nlinarith only [hi,hj,horder,heR,hs j,u.property.1]
      exact ⟨Or.inr ht,Or.inl hu⟩
    · have horder : (mesh j.succ).val≤(mesh i.castSucc).val :=
        hmono.monotone (by change j.val+1≤ i.val; exact hji)
      have hi := Icc.le_convexComb (hs i).le t
      have hj := Icc.convexComb_le (hs j).le u
      change (mesh i.castSucc).val≤(1-t.val)*(mesh i.castSucc).val+t.val*(mesh i.succ).val at hi
      change (1-u.val)*(mesh j.castSucc).val+u.val*(mesh j.succ).val≤(mesh j.succ).val at hj
      have ht : t=0 := by
        apply Subtype.ext
        change t.val=0
        nlinarith only [hi,hj,horder,heR,hs i,t.property.1]
      have hu : u=1 := by
        apply Subtype.ext
        change u.val=1
        nlinarith only [hi,hj,horder,heR,hs j,u.property.2]
      exact ⟨Or.inl ht,Or.inr hu⟩
end CurveComplex.HyperellipticModel
