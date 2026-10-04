import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualNegativeInternalMeshNodeIncidenceKernelRecovery
open scoped unitInterval
open Set
namespace CurveComplex.LocalSurgery
noncomputable section
attribute [local instance] Classical.propDecidable

theorem actualNegativeFirstMeshNodeIncidenceOne (m : ℕ) (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (g : C(Interval,ℝ))
    (hmid : ∀ j : Fin (m+1),actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ)∈Set.Ioo (mesh j.castSucc) (mesh j.succ))
    (hnozero : ∀ j : Fin (m+1),∀ t,mesh j.castSucc < t → t < mesh j.succ → g t≠0)
    (hneg : g (mesh 0)<0) :
    (Finset.univ.filter (fun j : Fin (m+1) =>
      g (actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ))<0 ∧
      (mesh j.castSucc=mesh 0 ∨ mesh j.succ=mesh 0))).card=1 := by
  have hm := hmid 0
  have hgl : g (actualIntervalMidpoint (mesh (0 : Fin (m+1)).castSucc)
      (mesh (0 : Fin (m+1)).succ))<0 :=
    actualNegativeEndpointForcesInteriorSign g _ _ _ (mesh 0) hm
      ⟨le_rfl,hm.1.le.trans hm.2.le⟩ hneg (hnozero 0)
  have hs : (Finset.univ.filter (fun j : Fin (m+1) =>
      g (actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ))<0 ∧
      (mesh j.castSucc=mesh 0 ∨ mesh j.succ=mesh 0)))={0} := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · rintro ⟨_,h | h⟩
      · exact Fin.ext (congrArg (fun z : Fin (m+2) => z.val) (hmono.injective h))
      · have he := congrArg Fin.val (hmono.injective h)
        change j.val+1=0 at he
        omega
    · rintro rfl
      exact ⟨hgl,Or.inl rfl⟩
  rw [hs,Finset.card_singleton]

theorem actualNegativeLastMeshNodeIncidenceOne (m : ℕ) (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (g : C(Interval,ℝ))
    (hmid : ∀ j : Fin (m+1),actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ)∈Set.Ioo (mesh j.castSucc) (mesh j.succ))
    (hnozero : ∀ j : Fin (m+1),∀ t,mesh j.castSucc < t → t < mesh j.succ → g t≠0)
    (hneg : g (mesh (Fin.last (m+1)))<0) :
    (Finset.univ.filter (fun j : Fin (m+1) =>
      g (actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ))<0 ∧
      (mesh j.castSucc=mesh (Fin.last (m+1)) ∨ mesh j.succ=mesh (Fin.last (m+1))))).card=1 := by
  have hm := hmid (Fin.last m)
  have hgl : g (actualIntervalMidpoint (mesh (Fin.last m).castSucc)
      (mesh (Fin.last m).succ))<0 :=
    actualNegativeEndpointForcesInteriorSign g _ _ _ (mesh (Fin.last (m+1))) hm
      ⟨hm.1.le.trans hm.2.le,le_rfl⟩ hneg (hnozero (Fin.last m))
  have hs : (Finset.univ.filter (fun j : Fin (m+1) =>
      g (actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ))<0 ∧
      (mesh j.castSucc=mesh (Fin.last (m+1)) ∨ mesh j.succ=mesh (Fin.last (m+1)))))={Fin.last m} := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · rintro ⟨_,h | h⟩
      · have he := congrArg Fin.val (hmono.injective h)
        change j.val=m+1 at he
        omega
      · have he := congrArg Fin.val (hmono.injective h)
        apply Fin.ext
        change j.val=m
        change j.val+1=m+1 at he
        omega
    · rintro rfl
      exact ⟨hgl,Or.inr rfl⟩
  rw [hs,Finset.card_singleton]

#print axioms actualNegativeFirstMeshNodeIncidenceOne
#print axioms actualNegativeLastMeshNodeIncidenceOne
end
end CurveComplex.LocalSurgery
