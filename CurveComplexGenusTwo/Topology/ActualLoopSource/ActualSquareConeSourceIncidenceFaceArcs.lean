import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConeFiniteFaceContactArcs
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteScalarSourceIncidenceMesh
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualScalarMeshEndpointBits
namespace CurveComplex.HyperellipticModel
open Set Topology
attribute [local instance] Classical.propDecidable
/-- Finite actual scalar contacts on an embedded face select the finite
negative intervals and construct embedded contact arcs in the conical filling.
Neither negative intervals nor contact arcs are input certificates. -/
theorem actual_square_cone_source_incidence_face_arcs
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (f : C({z : ℝ × ℝ // ‖z‖=1},V)) (center : V) (hc : center.val.2≠0)
    {ι : Type} [Finite ι]
    (faces : ι → C(Interval,{z : ℝ × ℝ // ‖z‖=1})) (hface : ∀ i,IsEmbedding (faces i))
    (hfinite : ∀ i,{t : Interval | (f (faces i t)).val.2=0}.Finite) :
    ∃ G : C({z : ℝ × ℝ // ‖z‖≤1},V),
      (∀ z : {z : ℝ × ℝ // ‖z‖=1},G ⟨z.val,z.property.le⟩=f z) ∧
    ∃ q : C({z : {z : ℝ × ℝ // ‖z‖=1} | (f z).val.2/center.val.2≤0},
      {z : ℝ × ℝ // ‖z‖≤1}),Function.Injective q ∧
      (∀ z,(q z).val=(1/(1-(f z.val).val.2/center.val.2)) • z.val.val) ∧
      (∀ z,(G (q z)).val.2=0) ∧
      (∀ u,(G u).val.2=0 ↔ ∃ z,q z=u) ∧
    ∀ i : ι,∃ m : ℕ, ∃ mesh : Fin (m+2) → Interval,∃ negative : Fin (m+1) → Prop,
      StrictMono mesh ∧ mesh 0=0 ∧ mesh (Fin.last (m+1))=1 ∧
      (∀ j,mesh j=0 ∨ mesh j=1 ∨ (f (faces i (mesh j))).val.2/center.val.2=0) ∧
      (∀ (j : Fin (m+1)) t,mesh j.castSucc < t → t < mesh j.succ →
        (f (faces i t)).val.2/center.val.2≠0) ∧
      (∀ j,negative j ↔
        (f (faces i (CurveComplex.LocalSurgery.actualIntervalMidpoint
          (mesh j.castSucc) (mesh j.succ)))).val.2/center.val.2 < 0) ∧
      ((f (faces i 0)).val.2/center.val.2≠0 →
        (negative 0 ↔ (f (faces i 0)).val.2/center.val.2 < 0)) ∧
      ((f (faces i 1)).val.2/center.val.2≠0 →
        (negative (Fin.last m) ↔ (f (faces i 1)).val.2/center.val.2 < 0)) ∧
      (∀ j,negative j → ∀ t ∈ Icc (mesh j.castSucc) (mesh j.succ),
        (f (faces i t)).val.2/center.val.2≤0) ∧
      (∀ t,(f (faces i t)).val.2/center.val.2≤0 ↔
        (f (faces i t)).val.2/center.val.2=0 ∨
          ∃ j,negative j ∧ t ∈ Icc (mesh j.castSucc) (mesh j.succ)) ∧
    ∃ arc : {j : Fin (m+1) // negative j} → C(Interval,{z : ℝ × ℝ // ‖z‖≤1}),
      (∀ j t,(arc j t).val=
        (1/(1-(f (faces i (Icc.convexComb (mesh j.val.castSucc) (mesh j.val.succ) t))).val.2/center.val.2)) •
          (faces i (Icc.convexComb (mesh j.val.castSucc) (mesh j.val.succ) t)).val) ∧
      (∀ j,IsEmbedding (arc j)) ∧
      (∀ j t,(G (arc j t)).val.2=0) ∧
      (∀ j t,0<t.val → t.val<1 → ‖(arc j t).val‖<1) ∧
      (∀ (j : {j : Fin (m+1) // negative j}) (bit : Fin 2)
        (u : Interval) (hu : (f (faces i u)).val.2/center.val.2≤0),
        arc j (if bit=0 then 0 else 1)=q ⟨faces i u,hu⟩ ↔
          mesh (if bit=0 then j.val.castSucc else j.val.succ)=u) ∧
      (∀ (u : Interval) (hu : (f (faces i u)).val.2/center.val.2≤0),
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=q ⟨faces i u,hu⟩}.ncard=
        (Finset.univ.filter (fun j : Fin (m+1) => negative j ∧
          (mesh j.castSucc=u ∨ mesh j.succ=u))).card) ∧
      (∀ (node : Fin (m+2)) (hn0 : node≠0) (hn1 : node≠Fin.last (m+1))
        (hn : (f (faces i (mesh node))).val.2/center.val.2 < 0),
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=
            q ⟨faces i (mesh node),hn.le⟩}.ncard=2) ∧
      (∀ (l r : Fin (m+1)) (u : Interval) (hl : mesh l.succ=u)
        (hr : mesh r.castSucc=u) (hflip : negative l ↔ ¬negative r)
        (hu : (f (faces i u)).val.2/center.val.2≤0),
        {e : {j : Fin (m+1) // negative j} × Fin 2 |
          arc e.1 (if e.2=0 then 0 else 1)=q ⟨faces i u,hu⟩}.ncard=1) ∧
      ((f (faces i 0)).val.2=0 →
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=
            ⟨(faces i 0).val,(faces i 0).property.le⟩}.ncard=
              if negative 0 then 1 else 0) ∧
      ((f (faces i 1)).val.2=0 →
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=
            ⟨(faces i 1).val,(faces i 1).property.le⟩}.ncard=
              if negative (Fin.last m) then 1 else 0) := by
  classical
  obtain ⟨G,hboundary,q,hinj,hq,hzero,hcomplete⟩ :=
    actual_square_cone_complete_zero_radials V hV f center hc
  have perface (i : ι) :
    ∃ m : ℕ, ∃ mesh : Fin (m+2) → Interval,∃ negative : Fin (m+1) → Prop,
      StrictMono mesh ∧ mesh 0=0 ∧ mesh (Fin.last (m+1))=1 ∧
      (∀ j,mesh j=0 ∨ mesh j=1 ∨ (f (faces i (mesh j))).val.2/center.val.2=0) ∧
      (∀ (j : Fin (m+1)) t,mesh j.castSucc < t → t < mesh j.succ →
        (f (faces i t)).val.2/center.val.2≠0) ∧
      (∀ j,negative j ↔
        (f (faces i (CurveComplex.LocalSurgery.actualIntervalMidpoint
          (mesh j.castSucc) (mesh j.succ)))).val.2/center.val.2 < 0) ∧
      ((f (faces i 0)).val.2/center.val.2≠0 →
        (negative 0 ↔ (f (faces i 0)).val.2/center.val.2 < 0)) ∧
      ((f (faces i 1)).val.2/center.val.2≠0 →
        (negative (Fin.last m) ↔ (f (faces i 1)).val.2/center.val.2 < 0)) ∧
      (∀ j,negative j → ∀ t ∈ Icc (mesh j.castSucc) (mesh j.succ),
        (f (faces i t)).val.2/center.val.2≤0) ∧
      (∀ t,(f (faces i t)).val.2/center.val.2≤0 ↔
        (f (faces i t)).val.2/center.val.2=0 ∨
          ∃ j,negative j ∧ t ∈ Icc (mesh j.castSucc) (mesh j.succ)) ∧
    ∃ arc : {j : Fin (m+1) // negative j} → C(Interval,{z : ℝ × ℝ // ‖z‖≤1}),
      (∀ j t,(arc j t).val=
        (1/(1-(f (faces i (Icc.convexComb (mesh j.val.castSucc) (mesh j.val.succ) t))).val.2/center.val.2)) •
          (faces i (Icc.convexComb (mesh j.val.castSucc) (mesh j.val.succ) t)).val) ∧
      (∀ j,IsEmbedding (arc j)) ∧
      (∀ j t,(G (arc j t)).val.2=0) ∧
      (∀ j t,0<t.val → t.val<1 → ‖(arc j t).val‖<1) ∧
      (∀ (j : {j : Fin (m+1) // negative j}) (bit : Fin 2)
        (u : Interval) (hu : (f (faces i u)).val.2/center.val.2≤0),
        arc j (if bit=0 then 0 else 1)=q ⟨faces i u,hu⟩ ↔
          mesh (if bit=0 then j.val.castSucc else j.val.succ)=u) ∧
      (∀ (u : Interval) (hu : (f (faces i u)).val.2/center.val.2≤0),
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=q ⟨faces i u,hu⟩}.ncard=
        (Finset.univ.filter (fun j : Fin (m+1) => negative j ∧
          (mesh j.castSucc=u ∨ mesh j.succ=u))).card) ∧
      (∀ (node : Fin (m+2)) (hn0 : node≠0) (hn1 : node≠Fin.last (m+1))
        (hn : (f (faces i (mesh node))).val.2/center.val.2 < 0),
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=
            q ⟨faces i (mesh node),hn.le⟩}.ncard=2) ∧
      (∀ (l r : Fin (m+1)) (u : Interval) (hl : mesh l.succ=u)
        (hr : mesh r.castSucc=u) (hflip : negative l ↔ ¬negative r)
        (hu : (f (faces i u)).val.2/center.val.2≤0),
        {e : {j : Fin (m+1) // negative j} × Fin 2 |
          arc e.1 (if e.2=0 then 0 else 1)=q ⟨faces i u,hu⟩}.ncard=1) ∧
      ((f (faces i 0)).val.2=0 →
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=
            ⟨(faces i 0).val,(faces i 0).property.le⟩}.ncard=
              if negative 0 then 1 else 0) ∧
      ((f (faces i 1)).val.2=0 →
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=
            ⟨(faces i 1).val,(faces i 1).property.le⟩}.ncard=
              if negative (Fin.last m) then 1 else 0) := by
    let face := faces i
    let scalar : C(Interval,ℝ) := ⟨fun t => (f (face t)).val.2/center.val.2,by fun_prop⟩
    have hfiniteScalar : (scalar ⁻¹' {0}).Finite := by
      have he : scalar ⁻¹' {0}={t : Interval | (f (face t)).val.2=0} := by
        ext t
        change (f (face t)).val.2/center.val.2=0 ↔ (f (face t)).val.2=0
        simp only [div_eq_zero_iff,hc,or_false]
      rw [he]
      exact hfinite i
    obtain ⟨m,mesh,negative,hmono,h0,h1,hnodes,hno,hflag,hnegative,hcover,hfirst,hlast,hfirstSign,hlastSign⟩ :=
      actual_finite_scalar_source_incidence_mesh scalar hfiniteScalar
    let parameter (j : Fin (m+1)) : C(Interval,Interval) :=
      ⟨Icc.convexComb (mesh j.castSucc) (mesh j.succ),by fun_prop⟩
    have hbounds (j : Fin (m+1)) (t : Interval) :
        parameter j t ∈ Icc (mesh j.castSucc) (mesh j.succ) :=
      ⟨Icc.le_convexComb (hmono.monotone (by change j.val≤j.val+1; omega)) t,
        Icc.convexComb_le (hmono.monotone (by change j.val≤j.val+1; omega)) t⟩
    have hstrict (j : Fin (m+1)) : (mesh j.castSucc).val<(mesh j.succ).val :=
      hmono (by change j.val<j.val+1; omega)
    have hparameter (j : Fin (m+1)) : Function.Injective (parameter j) := by
      intro t u he
      apply Subtype.ext
      have hh := congrArg Subtype.val he
      change (1-t.val)*(mesh j.castSucc).val+t.val*(mesh j.succ).val=
        (1-u.val)*(mesh j.castSucc).val+u.val*(mesh j.succ).val at hh
      have hp : (t.val-u.val)*((mesh j.succ).val-(mesh j.castSucc).val)=0 := by
        nlinarith only [hh]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right
        (ne_of_gt (sub_pos.mpr (hstrict j))))
    let direction (j : {j : Fin (m+1) // negative j}) :
        C(Interval,{z : {z : ℝ × ℝ // ‖z‖=1} | (f z).val.2/center.val.2≤0}) :=
      ⟨fun t => ⟨face (parameter j.val t),hnegative j.val j.property _ (hbounds j.val t)⟩,
        (face.continuous.comp (parameter j.val).continuous).subtype_mk _⟩
    let arc (j : {j : Fin (m+1) // negative j}) := q.comp (direction j)
    have harc (j) : IsEmbedding (arc j) := by
      refine ((arc j).continuous.isClosedEmbedding ?_).isEmbedding
      intro t u he
      have hh := congrArg Subtype.val (hinj he)
      exact hparameter j.val ((hface i).injective hh)
    have hendpoint (j : {j : Fin (m+1) // negative j}) (bit : Fin 2)
        (u : Interval) (hu : (f (faces i u)).val.2/center.val.2≤0) :
        arc j (if bit=0 then 0 else 1)=q ⟨faces i u,hu⟩ ↔
          mesh (if bit=0 then j.val.castSucc else j.val.succ)=u := by
      have hparam : parameter j.val (if bit=0 then 0 else 1)=
          mesh (if bit=0 then j.val.castSucc else j.val.succ) := by
        by_cases hb : bit=0 <;> simp [parameter,hb]
      constructor
      · intro he
        have hd := congrArg Subtype.val (hinj he)
        have hp := (hface i).injective hd
        exact hparam.symm.trans hp
      · intro he
        apply congrArg q
        apply Subtype.ext
        change face (parameter j.val (if bit=0 then 0 else 1))=faces i u
        rw [hparam,he]
    have hcount (u : Interval) (hu : (f (faces i u)).val.2/center.val.2≤0) :
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=q ⟨faces i u,hu⟩}.ncard=
        (Finset.univ.filter (fun j : Fin (m+1) => negative j ∧
          (mesh j.castSucc=u ∨ mesh j.succ=u))).card := by
      have he : {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=q ⟨faces i u,hu⟩}=
          {r : {j : Fin (m+1) // negative j} × Fin 2 |
            mesh (if r.2=0 then r.1.val.castSucc else r.1.val.succ)=u} := by
        ext r
        exact hendpoint r.1 r.2 u hu
      rw [he]
      exact actual_scalar_mesh_endpoint_bits_as_interval_count m mesh hmono negative u
    have hnodeCount (node : Fin (m+2)) (hn0 : node≠0) (hn1 : node≠Fin.last (m+1))
        (hn : (f (faces i (mesh node))).val.2/center.val.2 < 0) :
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=q ⟨faces i (mesh node),hn.le⟩}.ncard=2 := by
      rw [hcount,← actual_scalar_mesh_endpoint_bits_as_interval_count m mesh hmono negative (mesh node)]
      exact actual_scalar_mesh_internal_negative_endpoint_incidence m mesh hmono scalar negative hflag hno node hn0 hn1 hn
    have hcrossCount (l r : Fin (m+1)) (u : Interval) (hl : mesh l.succ=u)
        (hr : mesh r.castSucc=u) (hflip : negative l ↔ ¬negative r)
        (hu : (f (faces i u)).val.2/center.val.2≤0) :
        {e : {j : Fin (m+1) // negative j} × Fin 2 |
          arc e.1 (if e.2=0 then 0 else 1)=q ⟨faces i u,hu⟩}.ncard=1 := by
      rw [hcount,← actual_scalar_mesh_endpoint_bits_as_interval_count m mesh hmono negative u]
      exact actual_scalar_mesh_crossing_root_incidence m mesh hmono negative l r u hl hr hflip
    have hboundaryq (u : Interval) (hu : (f (faces i u)).val.2=0) :
        q ⟨faces i u,by change (f (faces i u)).val.2/center.val.2≤0; rw [hu]; simp⟩=
          ⟨(faces i u).val,(faces i u).property.le⟩ := by
      apply Subtype.ext
      rw [hq]
      simp only [hu,zero_div,sub_zero,div_one,one_smul]
    have hfirstActual (hu : (f (faces i 0)).val.2=0) :
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=
            ⟨(faces i 0).val,(faces i 0).property.le⟩}.ncard=
              if negative 0 then 1 else 0 := by
      have he : {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=
            ⟨(faces i 0).val,(faces i 0).property.le⟩}=
          {r : {j : Fin (m+1) // negative j} × Fin 2 |
            mesh (if r.2=0 then r.1.val.castSucc else r.1.val.succ)=0} := by
        ext r
        change (_=_) ↔ (_=_)
        rw [← hboundaryq 0 hu]
        exact hendpoint r.1 r.2 0 (by rw [hu]; simp)
      rw [he]
      exact hfirst
    have hlastActual (hu : (f (faces i 1)).val.2=0) :
        {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=
            ⟨(faces i 1).val,(faces i 1).property.le⟩}.ncard=
              if negative (Fin.last m) then 1 else 0 := by
      have he : {r : {j : Fin (m+1) // negative j} × Fin 2 |
          arc r.1 (if r.2=0 then 0 else 1)=
            ⟨(faces i 1).val,(faces i 1).property.le⟩}=
          {r : {j : Fin (m+1) // negative j} × Fin 2 |
            mesh (if r.2=0 then r.1.val.castSucc else r.1.val.succ)=1} := by
        ext r
        change (_=_) ↔ (_=_)
        rw [← hboundaryq 1 hu]
        exact hendpoint r.1 r.2 1 (by rw [hu]; simp)
      rw [he]
      exact hlast
    refine ⟨m,mesh,negative,hmono,h0,h1,hnodes,hno,hflag,hfirstSign,hlastSign,hnegative,hcover,
      arc,(fun j t => hq (direction j t)),harc,?_,?_,hendpoint,hcount,hnodeCount,hcrossCount,hfirstActual,hlastActual⟩
    · intro j t
      exact hzero (direction j t)
    · intro j t ht0 ht1
      have hs := hstrict j.val
      have hp0 : mesh j.val.castSucc<parameter j.val t := by
        change (mesh j.val.castSucc).val<(1-t.val)*(mesh j.val.castSucc).val+t.val*(mesh j.val.succ).val
        nlinarith only [hs,ht0]
      have hp1 : parameter j.val t< mesh j.val.succ := by
        change (1-t.val)*(mesh j.val.castSucc).val+t.val*(mesh j.val.succ).val<(mesh j.val.succ).val
        nlinarith only [hs,ht1]
      have hs0 := hnegative j.val j.property _ (hbounds j.val t)
      have hsn := hno j.val _ hp0 hp1
      have hsneg : scalar (parameter j.val t)<0 := lt_of_le_of_ne hs0 hsn
      have hden : 1-scalar (parameter j.val t)>1 := by linarith only [hsneg]
      change ‖(q (direction j t)).val‖<1
      rw [hq,norm_smul,Real.norm_eq_abs,(direction j t).val.property,mul_one]
      change |1/(1-scalar (parameter j.val t))|<1
      rw [abs_of_pos (one_div_pos.mpr (lt_trans zero_lt_one hden))]
      exact (div_lt_one (lt_trans zero_lt_one hden)).mpr hden
  exact ⟨G,hboundary,q,hinj,hq,hzero,hcomplete,perface⟩
end CurveComplex.HyperellipticModel
