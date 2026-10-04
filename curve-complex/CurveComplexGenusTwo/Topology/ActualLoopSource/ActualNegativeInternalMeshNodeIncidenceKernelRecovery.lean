import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc
open scoped unitInterval
open Set
namespace CurveComplex.LocalSurgery
noncomputable section
attribute [local instance] Classical.propDecidable
theorem actualMeshIncidentIntervalUnique (m : ℕ) (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (l r : Fin (m+1)) (u : Interval)
    (hlu : mesh l.succ=u) (hru : mesh r.castSucc=u) (j : Fin (m+1))
    (hj : mesh j.castSucc=u ∨ mesh j.succ=u) : j=l ∨ j=r := by
  rcases hj with hj | hj
  · right
    have he := hmono.injective (hj.trans hru.symm)
    apply Fin.ext
    exact congrArg (fun z : Fin (m+2) => z.val) he
  · left
    have he := congrArg Fin.val (hmono.injective (hj.trans hlu.symm))
    apply Fin.ext
    change j.val+1=l.val+1 at he
    omega
theorem actualMeshNegativeIncidenceUnique (m : ℕ) (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (negative : Fin (m+1) → Prop) (l r : Fin (m+1))
    (u : Interval) (hlu : mesh l.succ=u) (hru : mesh r.castSucc=u)
    (hflip : negative l ↔ ¬negative r) :
    ∃! j : Fin (m+1),negative j ∧ (mesh j.castSucc=u ∨ mesh j.succ=u) := by
  by_cases hl : negative l
  · refine ⟨l,⟨hl,Or.inr hlu⟩,?_⟩
    intro j hj
    rcases actualMeshIncidentIntervalUnique m mesh hmono l r u hlu hru j hj.2 with he | he
    · exact he
    · have hr : ¬negative r := hflip.mp hl
      exact False.elim (hr (he ▸ hj.1))
  · have hr : negative r := by
      by_contra hn
      exact hl (hflip.mpr hn)
    refine ⟨r,⟨hr,Or.inl hru⟩,?_⟩
    intro j hj
    rcases actualMeshIncidentIntervalUnique m mesh hmono l r u hlu hru j hj.2 with he | he
    · exact False.elim (hl (he ▸ hj.1))
    · exact he
theorem actualMeshNegativeEndpointCard (m : ℕ) (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (negative : Fin (m+1) → Prop) (l r : Fin (m+1))
    (u : Interval) (hlu : mesh l.succ=u) (hru : mesh r.castSucc=u) :
    (Finset.univ.filter (fun j => negative j ∧
      (mesh j.castSucc=u ∨ mesh j.succ=u))).card =
      (if negative l then 1 else 0)+(if negative r then 1 else 0) := by
  have hlr : l≠r := by
    intro he
    have hnodes := hmono.injective (hlu.trans hru.symm)
    have hn := congrArg (fun z : Fin (m+2) => z.val) hnodes
    change l.val+1=r.val at hn
    have hv := congrArg (fun z : Fin (m+1) => z.val) he
    omega
  have hfilter : Finset.univ.filter (fun j => negative j ∧
      (mesh j.castSucc=u ∨ mesh j.succ=u)) = ({l,r} : Finset (Fin (m+1))).filter negative := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · intro hj
      exact ⟨actualMeshIncidentIntervalUnique m mesh hmono l r u hlu hru j hj.2,hj.1⟩
    · rintro ⟨hj,hn⟩
      refine ⟨hn,?_⟩
      rcases hj with rfl | rfl
      · exact Or.inr hlu
      · exact Or.inl hru
  rw [hfilter]
  by_cases hl : negative l <;> by_cases hr : negative r <;> simp [Finset.filter_insert,Finset.filter_singleton,hl,hr,hlr,Ne.symm hlr]
theorem actualMeshSourceTargetCardAdd (m : ℕ) (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (negative : Fin (m+1) → Prop) (u : Interval) :
    (Finset.univ.filter (fun j => negative j ∧ mesh j.castSucc=u)).card+
    (Finset.univ.filter (fun j => negative j ∧ mesh j.succ=u)).card=
    (Finset.univ.filter (fun j => negative j ∧ (mesh j.castSucc=u ∨ mesh j.succ=u))).card := by
  have hd : Disjoint (Finset.univ.filter (fun j => negative j ∧ mesh j.castSucc=u))
      (Finset.univ.filter (fun j => negative j ∧ mesh j.succ=u)) := by
    apply Finset.disjoint_left.mpr
    intro j hj₀ hj₁
    have hzero := (Finset.mem_filter.mp hj₀).2.2
    have hone := (Finset.mem_filter.mp hj₁).2.2
    have he := hmono.injective (hzero.trans hone.symm)
    have hv := congrArg (fun z : Fin (m+2) => z.val) he
    change j.val=j.val+1 at hv
    omega
  rw [←Finset.card_union_of_disjoint hd]
  congr 1
  ext j
  simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
  tauto
theorem actualNoZeroIntervalSign (g : C(Interval,ℝ)) (x y s : Interval)
    (hxs : x < s) (hsy : s < y) (hs : g s < 0)
    (hn : ∀ t, x < t → t < y → g t ≠ 0) :
    ∀ t ∈ Set.Icc x y, g t ≤ 0 := by
  intro t ht
  by_contra hgt
  have htpos : 0 < g t := lt_of_not_ge hgt
  rcases le_total s t with hst | hts
  · obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc hst g.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (g s) (g t) from ⟨hs.le,htpos.le⟩)
    have hzt : z < t := lt_of_le_of_ne hz.2 (by
      intro he; rw [he] at hgz; linarith)
    exact hn z (hxs.trans_le hz.1) (hzt.trans_le ht.2) hgz
  · obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc' hts g.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (g s) (g t) from ⟨hs.le,htpos.le⟩)
    have htz : t < z := lt_of_le_of_ne hz.1 (by
      intro he; rw [← he] at hgz; linarith)
    exact hn z (ht.1.trans_lt htz) (hz.2.trans_lt hsy) hgz
theorem actualNegativeEndpointForcesInteriorSign (g : C(Interval,ℝ)) (x y s t : Interval)
    (hs : s∈Set.Ioo x y) (ht : t∈Set.Icc x y) (hneg : g t<0)
    (hn : ∀ z,x<z → z<y → g z≠0) : g s<0 := by
  by_contra hbad
  have hpos : 0<g s := lt_of_le_of_ne (le_of_not_gt hbad) (Ne.symm (hn s hs.1 hs.2))
  have hn' : ∀ z,x<z → z<y → (-g) z≠0 := by
    intro z hz₀ hz₁
    change -g z≠0
    exact neg_ne_zero.mpr (hn z hz₀ hz₁)
  have hnonpos := actualNoZeroIntervalSign (-g) x y s hs.1 hs.2
    (show (-g) s<0 by change -g s<0;linarith only [hpos]) hn' t ht
  change -g t≤0 at hnonpos
  linarith only [hneg,hnonpos]

def actualIntervalMidpoint (x y : Interval) : Interval := ⟨(x.val+y.val)/2,by
  constructor <;> linarith only [x.property.1,x.property.2,y.property.1,y.property.2]⟩

theorem actualNegativeInternalMeshNodeIncidenceTwo (m : ℕ) (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (g : C(Interval,ℝ))
    (hmid : ∀ j : Fin (m+1),actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ)∈Set.Ioo (mesh j.castSucc) (mesh j.succ))
    (hnozero : ∀ j : Fin (m+1),∀ t,mesh j.castSucc<t → t < mesh j.succ → g t≠0)
    (q : Fin (m+2)) (hq₀ : q≠0)
    (hq₁ : q≠Fin.last (m+1))
    (hneg : g (mesh q)<0) :
    (Finset.univ.filter (fun j : Fin (m+1) => g (actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ))<0 ∧ (mesh j.castSucc=mesh q ∨ mesh j.succ=mesh q))).card=2 := by
  obtain ⟨l,hl⟩ := Fin.exists_succ_eq.mpr hq₀
  obtain ⟨r,hr⟩ := Fin.exists_castSucc_eq.mpr hq₁
  have hml := hmid l
  have hmr := hmid r
  have hgl : g (actualIntervalMidpoint
      (mesh l.castSucc) (mesh l.succ))<0 :=
    actualNegativeEndpointForcesInteriorSign (g) _ _ _
      (mesh l.succ) hml ⟨hml.1.le.trans hml.2.le,le_rfl⟩
      (by simpa only [hl] using hneg) (hnozero l)
  have hgr : g (actualIntervalMidpoint
      (mesh r.castSucc) (mesh r.succ))<0 :=
    actualNegativeEndpointForcesInteriorSign (g) _ _ _
      (mesh r.castSucc) hmr ⟨le_rfl,hmr.1.le.trans hmr.2.le⟩
      (by simpa only [hr] using hneg) (hnozero r)
  have hc := actualMeshNegativeEndpointCard (m) (mesh)
    (hmono) (fun j => g (actualIntervalMidpoint
      (mesh j.castSucc) (mesh j.succ))<0) l r
    (mesh q) (congrArg (mesh) hl)
    (congrArg (mesh) hr)
  simpa only [if_pos hgl,if_pos hgr] using hc

#print axioms actualNegativeInternalMeshNodeIncidenceTwo
end
end CurveComplex.LocalSurgery
