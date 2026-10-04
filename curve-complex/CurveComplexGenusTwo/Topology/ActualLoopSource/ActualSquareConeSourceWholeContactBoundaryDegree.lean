import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConeSourceIncidenceFaceArcs
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareNegativeCornerEndpointIncidence
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualScalarMeshCrossingFlagsFromSource
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualScalarMeshRootAdjacentIntervals
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMeshIntervalParameterCover
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourFaceMeshDirectionCollision
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConeCompatibleWholeContactFamily
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual four-side boundary with finite scalar contacts produces a finite
embedded-arc family covering EVERY contact of the constructed square filling.
Finite vertices and arcs are outputs, not a presumed contact certificate. -/
theorem actual_square_cone_source_whole_contact_boundary_degree
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (f : C({z : ℝ × ℝ // ‖z‖=1},V)) (center : V) (hc : center.val.2≠0)
    (hfinite : ∀ i : Fin 4,
      {t : Interval | (f (actualMaxNormSquareBoundaryFace i t)).val.2=0}.Finite) :
    ∃ G : C({z : ℝ × ℝ // ‖z‖≤1},V),
      (∀ z : {z : ℝ × ℝ // ‖z‖=1},G ⟨z.val,z.property.le⟩=f z) ∧
    ∃ vertices : Finset {z : ℝ × ℝ // ‖z‖≤1},
    ∃ A : Type,∃ _hA : Finite A,∃ arc : A → C(Interval,{z : ℝ × ℝ // ‖z‖≤1}),
      (∀ e,arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices) ∧
      (∀ e f t u,arc e t=arc f u →
        (e=f ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1))) ∧
      (∀ e t,t≠0 → t≠1 → arc e t ∉ vertices) ∧
      (∀ e,IsEmbedding (arc e)) ∧
      (∀ e t,0<t.val → t.val<1 → ‖(arc e t).val‖<1) ∧
      (∀ u,(G u).val.2=0 ↔ u ∈ vertices ∨ ∃ e t,arc e t=u) ∧
      (∀ v : ↑vertices,‖v.val.val‖ < 1 →
        {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=v.val}.ncard=2) ∧
      (∀ (i : Fin 4) (u : Interval),0<u.val → u.val < 1 →
        (f (actualMaxNormSquareBoundaryFace i u)).val.2=0 →
        ∀ δ : ℝ,0<δ →
        (∀ v w : Interval,u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
          (f (actualMaxNormSquareBoundaryFace i v)).val.2/center.val.2≠0 ∧
          (f (actualMaxNormSquareBoundaryFace i w)).val.2/center.val.2≠0 ∧
          ((0<(f (actualMaxNormSquareBoundaryFace i v)).val.2/center.val.2) ↔
            ¬(0<(f (actualMaxNormSquareBoundaryFace i w)).val.2/center.val.2))) →
        {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=
          ⟨(actualMaxNormSquareBoundaryFace i u).val,
            (actualMaxNormSquareBoundaryFace i u).property.le⟩}.ncard=1) := by
  classical
  obtain ⟨G,hboundary,q,hinj,hq,hzero,hcomplete,hfaces⟩ :=
    actual_square_cone_source_incidence_face_arcs V hV f center hc actualMaxNormSquareBoundaryFace
      actual_max_norm_square_boundary_face_embedding hfinite
  choose m mesh negative hmono h0 h1 hnodes hno hflag hfirstSign hlastSign hnegative hcover arcs hformula hembed harczero harcinterior hendpoint hcount hnodeCount hcrossCount hfirstCount hlastCount using hfaces
  let N := {z : {z : ℝ × ℝ // ‖z‖=1} | (f z).val.2/center.val.2≤0}
  let Z : Set {z : ℝ × ℝ // ‖z‖=1} := {z | (f z).val.2=0}
  have hfZ : Z.Finite := by
    have hsub : Z ⊆ ⋃ i : Fin 4,actualMaxNormSquareBoundaryFace i ''
        {t : Interval | (f (actualMaxNormSquareBoundaryFace i t)).val.2=0} := by
      intro z hz
      obtain ⟨i,t,he⟩ := actual_max_norm_square_boundary_cover z
      have ht : (f (actualMaxNormSquareBoundaryFace i t)).val.2=0 := by
        rw [he]
        exact hz
      exact mem_iUnion.mpr ⟨i,t,ht,he⟩
    exact (Set.finite_iUnion (fun i => (hfinite i).image _)).subset hsub
  let ZN : Set N := Subtype.val ⁻¹' Z
  have hfZN : ZN.Finite := hfZ.preimage Subtype.val_injective.injOn
  let A := Σ i : Fin 4,{j : Fin (m i+1) // negative i j}
  let arc : A → C(Interval,{z : ℝ × ℝ // ‖z‖≤1}) := fun e => arcs e.1 e.2
  have hbounds (e : A) (t : Interval) :
      Icc.convexComb (mesh e.1 e.2.val.castSucc) (mesh e.1 e.2.val.succ) t ∈
        Icc (mesh e.1 e.2.val.castSucc) (mesh e.1 e.2.val.succ) :=
    ⟨Icc.le_convexComb ((hmono e.1).monotone (by change e.2.val.val≤e.2.val.val+1; omega)) t,
      Icc.convexComb_le ((hmono e.1).monotone (by change e.2.val.val≤e.2.val.val+1; omega)) t⟩
  let direction (e : A) (t : Interval) : N :=
    ⟨actualMaxNormSquareBoundaryFace e.1
      (Icc.convexComb (mesh e.1 e.2.val.castSucc) (mesh e.1 e.2.val.succ) t),
        hnegative e.1 e.2.val e.2.property _ (hbounds e t)⟩
  have hArcQ (e : A) (t : Interval) : arc e t=q (direction e t) := by
    apply Subtype.ext
    rw [hformula e.1 e.2 t,hq]
  have hforget : Function.Injective (fun e : A =>
      (⟨e.1,e.2.val⟩ : Σ i : Fin 4,Fin (m i+1))) := by
    rintro ⟨i,⟨j,hj⟩⟩ ⟨k,⟨l,hl⟩⟩ he
    cases he
    rfl
  have hcollision (e d : A) (t u : Interval) (he : arc e t=arc d u) :
      (e=d ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1)) := by
    have hd := congrArg Subtype.val (hinj ((hArcQ e t).symm.trans (he.trans (hArcQ d u))))
    rcases actual_four_face_mesh_direction_collision m mesh hmono
      ⟨e.1,e.2.val⟩ ⟨d.1,d.2.val⟩ t u hd with ⟨hed,htu⟩ | hend
    · exact Or.inl ⟨hforget hed,htu⟩
    · exact Or.inr hend
  let endpoints : Set {z : ℝ × ℝ // ‖z‖≤1} :=
    range (fun e : A => arc e 0) ∪ range (fun e : A => arc e 1)
  have hfend : endpoints.Finite := (Set.finite_range _).union (Set.finite_range _)
  let vertexSet := q '' ZN ∪ endpoints
  have hfvertices : vertexSet.Finite := (hfZN.image q).union hfend
  let vertices := hfvertices.toFinset
  have hends (e : A) : arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices := by
    constructor
    · exact hfvertices.mem_toFinset.mpr (Or.inr (Or.inl (mem_range_self e)))
    · exact hfvertices.mem_toFinset.mpr (Or.inr (Or.inr (mem_range_self e)))
  have hclear (e : A) (t : Interval) (ht0 : t≠0) (ht1 : t≠1) : arc e t ∉ vertices := by
    intro hv
    have ht0R : 0<t.val := lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm))
    have ht1R : t.val<1 := lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))
    rcases hfvertices.mem_toFinset.mp hv with hv | hv
    · obtain ⟨z,hz,he⟩ := hv
      have hz0 : (f z.val).val.2=0 := hz
      have hnorm : ‖(q z).val‖=1 := by
        rw [hq,hz0,zero_div,sub_zero,div_one,one_smul,z.val.property]
      have hp := harcinterior e.1 e.2 t ht0R ht1R
      change ‖(arc e t).val‖<1 at hp
      rw [← he,hnorm] at hp
      exact (lt_irrefl 1) hp
    · rcases hv with hv | hv
      · obtain ⟨d,he⟩ := hv
        rcases hcollision e d t 0 he.symm with ⟨hed,hte⟩ | ⟨hte,hde⟩
        · exact ht0 hte
        · exact hte.elim ht0 ht1
      · obtain ⟨d,he⟩ := hv
        rcases hcollision e d t 1 he.symm with ⟨hed,hte⟩ | ⟨hte,hde⟩
        · exact ht1 hte
        · exact hte.elim ht0 ht1
  have hdegree (v : ↑vertices) (hv : ‖v.val.val‖ < 1) :
      {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=v.val}.ncard=2 := by
    have hve : ∃ (e : A) (bit : Fin 2),arc e (if bit=0 then 0 else 1)=v.val := by
      rcases hfvertices.mem_toFinset.mp v.property with hvz | hve
      · obtain ⟨z,hz,he⟩ := hvz
        have hz0 : (f z.val).val.2=0 := hz
        have hnorm : ‖(q z).val‖=1 := by
          rw [hq,hz0,zero_div,sub_zero,div_one,one_smul,z.val.property]
        rw [← he,hnorm] at hv
        exact False.elim ((lt_irrefl 1) hv)
      · rcases hve with ⟨e,he⟩ | ⟨e,he⟩
        · exact ⟨e,0,by simpa using he⟩
        · exact ⟨e,1,by simpa using he⟩
    obtain ⟨e,bit,he⟩ := hve
    let node : Fin (m e.1+2) := if bit=0 then e.2.val.castSucc else e.2.val.succ
    have hp : Icc.convexComb (mesh e.1 e.2.val.castSucc)
        (mesh e.1 e.2.val.succ) (if bit=0 then 0 else 1)=mesh e.1 node := by
      by_cases hb : bit=0 <;> simp [node,hb]
    have hd : (direction e (if bit=0 then 0 else 1)).val=
        actualMaxNormSquareBoundaryFace e.1 (mesh e.1 node) := congrArg (actualMaxNormSquareBoundaryFace e.1) hp
    have hnle : (f (actualMaxNormSquareBoundaryFace e.1 (mesh e.1 node))).val.2/center.val.2≤0 := by
      rw [← hd]
      exact (direction e (if bit=0 then 0 else 1)).property
    have hnne : (f (actualMaxNormSquareBoundaryFace e.1 (mesh e.1 node))).val.2/center.val.2≠0 := by
      intro hz
      have hfz : (f (actualMaxNormSquareBoundaryFace e.1 (mesh e.1 node))).val.2=0 :=
        (div_eq_zero_iff.mp hz).resolve_right hc
      have hnorm : ‖(arc e (if bit=0 then 0 else 1)).val‖=1 := by
        rw [hArcQ,hq,hd,hfz,zero_div,sub_zero,div_one,one_smul]
        exact (actualMaxNormSquareBoundaryFace e.1 (mesh e.1 node)).property
      rw [he] at hnorm
      rw [hnorm] at hv
      exact (lt_irrefl 1) hv
    have hn := lt_of_le_of_ne hnle hnne
    have hbound : mesh e.1 node=0 ∨ mesh e.1 node=1 := by
      rcases hnodes e.1 node with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hnne h)
    let cb : Fin 2 := if mesh e.1 node=0 then 0 else 1
    have hcorner : mesh e.1 node=(if cb=0 then 0 else 1) := by
      rcases hbound with h | h
      · simp [cb,h]
      · simp [cb,h]
    have hset : {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=v.val}=
        {r : A × Fin 2 | actualMaxNormSquareBoundaryFace r.1.1
          (mesh r.1.1 (if r.2=0 then r.1.2.val.castSucc else r.1.2.val.succ))=
            actualMaxNormSquareBoundaryFace e.1 (if cb=0 then 0 else 1)} := by
      ext r
      change (_=_) ↔ (_=_)
      rw [← he,hArcQ,hArcQ,hinj.eq_iff,Subtype.ext_iff,hd,hcorner]
      by_cases hb : r.2=0 <;> simp [direction,hb]
    rw [hset]
    apply actual_square_negative_corner_endpoint_incidence V f center m mesh hmono h0 h1 negative hfirstSign hlastSign e.1 cb
    rw [← hcorner]
    exact hn
  have hboundaryCount (i : Fin 4) (u : Interval) (hu0 : 0<u.val) (hu1 : u.val < 1)
      (hroot : (f (actualMaxNormSquareBoundaryFace i u)).val.2=0)
      (δ : ℝ) (hδ : 0<δ)
      (hflip : ∀ v w : Interval,u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
        (f (actualMaxNormSquareBoundaryFace i v)).val.2/center.val.2≠0 ∧
        (f (actualMaxNormSquareBoundaryFace i w)).val.2/center.val.2≠0 ∧
        ((0<(f (actualMaxNormSquareBoundaryFace i v)).val.2/center.val.2) ↔
          ¬(0<(f (actualMaxNormSquareBoundaryFace i w)).val.2/center.val.2))) :
      {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=
        ⟨(actualMaxNormSquareBoundaryFace i u).val,
          (actualMaxNormSquareBoundaryFace i u).property.le⟩}.ncard=1 := by
    let g : C(Interval,ℝ) := ⟨fun t => (f (actualMaxNormSquareBoundaryFace i t)).val.2/center.val.2,by fun_prop⟩
    have hg : g u=0 := by change _/center.val.2=0; rw [hroot]; simp
    obtain ⟨l,r,hl,hr⟩ := actual_scalar_mesh_root_adjacent_intervals (m i) (mesh i)
      (hmono i) (h0 i) (h1 i) g (hno i) u ⟨hu0,hu1⟩ hg
    have hflags := (actual_scalar_mesh_crossing_flags_from_source (m i) (mesh i) (hmono i)
      g (negative i) (hflag i) (hno i) l r u hl hr δ hδ hflip).1
    let z : N := ⟨actualMaxNormSquareBoundaryFace i u,by change _/center.val.2≤0; rw [hroot]; simp⟩
    have hqz : q z=⟨(actualMaxNormSquareBoundaryFace i u).val,
        (actualMaxNormSquareBoundaryFace i u).property.le⟩ := by
      apply Subtype.ext
      rw [hq]
      change (1/(1-(f (actualMaxNormSquareBoundaryFace i u)).val.2/center.val.2)) • _=_
      rw [hroot,zero_div,sub_zero,div_one,one_smul]
    rw [← hqz]
    have heq : {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=q z}.ncard=
        {r : {j : Fin (m i+1) // negative i j} × Fin 2 |
          arcs i r.1 (if r.2=0 then 0 else 1)=q z}.ncard := by
      symm
      apply Set.ncard_congr (fun r _ => (⟨i,r.1⟩,r.2))
      · intro r hr
        exact hr
      · intro r s hr hs he
        have ha : r.1=s.1 := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst he)).2
        have hb : r.2=s.2 := congrArg (fun e : A × Fin 2 => e.2) he
        exact Prod.ext ha hb
      · rintro ⟨⟨j,e⟩,bit⟩ he
        have hd := congrArg Subtype.val (hinj ((hArcQ ⟨j,e⟩ (if bit=0 then 0 else 1)).symm.trans he))
        change actualMaxNormSquareBoundaryFace j
          (Icc.convexComb (mesh j e.val.castSucc) (mesh j e.val.succ) (if bit=0 then 0 else 1))=
            actualMaxNormSquareBoundaryFace i u at hd
        have hji : j=i := by
          rcases actual_max_norm_square_boundary_face_collision j i _ u hd with h | ⟨_,hb⟩
          · exact h.1
          · rcases hb with h | h
            · simp [h] at hu0
            · simp [h] at hu1
        cases hji
        exact ⟨(e,bit),he,rfl⟩
    rw [heq]
    exact hcrossCount i l r u hl hr hflags z.property
  refine ⟨G,hboundary,vertices,A,inferInstance,arc,hends,hcollision,hclear,(fun e => hembed e.1 e.2),
    (fun e t ht0 ht1 => harcinterior e.1 e.2 t ht0 ht1),?_,hdegree,hboundaryCount⟩
  intro u
  constructor
  · intro hu
    obtain ⟨z,hzu⟩ := (hcomplete u).mp hu
    obtain ⟨i,t,hface⟩ := actual_max_norm_square_boundary_cover z.val
    have ht : (f (actualMaxNormSquareBoundaryFace i t)).val.2/center.val.2≤0 :=
      hface ▸ z.property
    rcases (hcover i t).mp ht with hzt | ⟨j,hj,hjt⟩
    · left
      apply hfvertices.mem_toFinset.mpr
      left
      refine ⟨z,?_,hzu⟩
      change (f z.val).val.2=0
      have hh : (f (actualMaxNormSquareBoundaryFace i t)).val.2=0 := by
        simpa only [div_eq_zero_iff,hc,or_false] using hzt
      exact hface ▸ hh
    · right
      obtain ⟨s,hs⟩ := actual_mesh_interval_parameter_cover _ _ _ hjt
      refine ⟨⟨i,⟨j,hj⟩⟩,s,?_⟩
      apply Subtype.ext
      change (arcs i ⟨j,hj⟩ s).val=u.val
      rw [hformula i ⟨j,hj⟩ s,hs,hface,← hzu,hq]
  · rintro (hv | ⟨e,t,rfl⟩)
    · rcases hfvertices.mem_toFinset.mp hv with hv | hv
      · obtain ⟨z,hz,he⟩ := hv
        rw [← he]
        exact hzero z
      · rcases hv with hv | hv
        · obtain ⟨e,rfl⟩ := hv
          exact harczero e.1 e.2 0
        · obtain ⟨e,rfl⟩ := hv
          exact harczero e.1 e.2 1
    · exact harczero e.1 e.2 t
end CurveComplex.HyperellipticModel
