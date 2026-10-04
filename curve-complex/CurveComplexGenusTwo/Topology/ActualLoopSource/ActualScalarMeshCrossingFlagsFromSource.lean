import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteScalarSourceIncidenceMesh
namespace CurveComplex.HyperellipticModel
open Set Topology CurveComplex.LocalSurgery
/-- The actual local crossing normal-sign theorem selects opposite adjacent
source mesh flags, and therefore one literal endpoint incidence. -/
theorem actual_scalar_mesh_crossing_flags_from_source
    (m : ℕ) (mesh : Fin (m+2) → Interval) (hmono : StrictMono mesh)
    (g : C(Interval,ℝ)) (negative : Fin (m+1) → Prop)
    (hflag : ∀ j,negative j ↔ g (actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ)) < 0)
    (hno : ∀ (j : Fin (m+1)) t,mesh j.castSucc < t → t < mesh j.succ → g t≠0)
    (l r : Fin (m+1)) (u : Interval) (hl : mesh l.succ=u) (hr : mesh r.castSucc=u)
    (δ : ℝ) (hδ : 0<δ)
    (hflip : ∀ v w : Interval,u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
      g v≠0 ∧ g w≠0 ∧ ((0<g v) ↔ ¬(0<g w))) :
    (negative l ↔ ¬negative r) ∧
    {q : {j : Fin (m+1) // negative j} × Fin 2 |
      mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=u}.ncard=1 := by
  classical
  have hs (j : Fin (m+1)) : (mesh j.castSucc).val < (mesh j.succ).val :=
    hmono (by change j.val < j.val+1; omega)
  have hlower : max (mesh l.castSucc).val (u.val-δ) < u.val :=
    max_lt (by simpa only [hl] using hs l) (by linarith only [hδ])
  obtain ⟨v0,hvlow,hvu⟩ := exists_between hlower
  have hupper : u.val < min (mesh r.succ).val (u.val+δ) :=
    lt_min (by simpa only [hr] using hs r) (by linarith only [hδ])
  obtain ⟨w0,huw,hwupper⟩ := exists_between hupper
  let v : Interval := ⟨v0,⟨(mesh l.castSucc).property.1.trans
    ((le_max_left _ _).trans hvlow.le),hvu.le.trans u.property.2⟩⟩
  let w : Interval := ⟨w0,⟨u.property.1.trans huw.le,
    (hwupper.le.trans (min_le_left _ _)).trans (mesh r.succ).property.2⟩⟩
  have hvopen : v∈Ioo (mesh l.castSucc) (mesh l.succ) :=
    ⟨show (mesh l.castSucc).val < v.val from (le_max_left _ _).trans_lt hvlow,
      by change v.val < (mesh l.succ).val; rw [hl]; exact hvu⟩
  have hwopen : w∈Ioo (mesh r.castSucc) (mesh r.succ) :=
    ⟨by change (mesh r.castSucc).val < w.val; rw [hr]; exact huw,
      show w.val < (mesh r.succ).val from hwupper.trans_le (min_le_left _ _)⟩
  have hmid (j : Fin (m+1)) : actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ)∈
      Ioo (mesh j.castSucc) (mesh j.succ) := by
    constructor
    · change (mesh j.castSucc).val < ((mesh j.castSucc).val+(mesh j.succ).val)/2
      linarith only [hs j]
    · change ((mesh j.castSucc).val+(mesh j.succ).val)/2 < (mesh j.succ).val
      linarith only [hs j]
  have hsame (j : Fin (m+1)) (t : Interval)
      (ht : t∈Ioo (mesh j.castSucc) (mesh j.succ)) : negative j ↔ g t < 0 := by
    rw [hflag]
    constructor
    · intro hm
      exact actualNegativeEndpointForcesInteriorSign g _ _ t _ ht
        ⟨(hmid j).1.le,(hmid j).2.le⟩ hm (hno j)
    · intro hm
      exact actualNegativeEndpointForcesInteriorSign g _ _ _ t (hmid j)
        ⟨ht.1.le,ht.2.le⟩ hm (hno j)
  have hf := hflip v w ((le_max_right _ _).trans_lt hvlow) hvu huw
    (hwupper.trans_le (min_le_right _ _))
  have hsign : g v < 0 ↔ ¬(g w < 0) := by
    rcases lt_or_gt_of_ne hf.1 with hvn | hvp
    · have hwp : 0<g w := by
        by_contra hw
        have hgv := hf.2.2.mpr hw
        exact (not_lt.mpr hvn.le) hgv
      simp only [hvn,not_lt.mpr hwp.le,not_false_eq_true]
    · have hwn : g w < 0 := lt_of_le_of_ne (le_of_not_gt (hf.2.2.mp hvp)) hf.2.1
      simp only [hwn,not_lt.mpr hvp.le,not_true_eq_false]
  have hflags : negative l ↔ ¬negative r := by rw [hsame l v hvopen,hsame r w hwopen]; exact hsign
  exact ⟨hflags,actual_scalar_mesh_crossing_root_incidence m mesh hmono negative l r u hl hr hflags⟩
end CurveComplex.HyperellipticModel
