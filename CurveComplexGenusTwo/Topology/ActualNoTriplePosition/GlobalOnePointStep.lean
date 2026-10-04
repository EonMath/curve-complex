import CurveComplexGenusTwo.Topology.ActualNoTriplePosition.GlobalTripleMeasure

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem option_other_label_injective
    {A : Type} (a0 : A) (P : A → Prop) :
    Function.Injective (fun x : Option {a : A // a ≠ a0 ∧ P a} =>
      Option.elim x a0 (fun j => j.val)) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some j =>
      have he : a0 = j.val := h
      exact ((j.property.1 he.symm).elim)
  | some i =>
    cases y with
    | none =>
      have he : i.val = a0 := h
      exact ((i.property.1 he).elim)
    | some j =>
      have he : i.val = j.val := h
      exact congrArg Option.some (Subtype.ext he)

theorem actual_one_point_global_descent
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (anchor : EssentialMarkedArc M) (r : I → EssentialMarkedArc M)
    (hfinite : ∀ a b : Option I, a ≠ b →
      (crossings M (fullArc M anchor r a) (fullArc M anchor r b)).Finite)
    (htrans : ∀ a b : Option I, a ≠ b →
      ∀ x ∈ crossings M (fullArc M anchor r a) (fullArc M anchor r b),
        CrossesInDisk M (fullArc M anchor r a) (fullArc M anchor r b) x)
    (i0 : I) (b0 c0 : Option I) (p : S)
    (hpold : ((some i0,b0,c0),p) ∈ tripleContactWitnesses M anchor r)
    (hWfinite : (tripleContactWitnesses M anchor r).Finite) :
    ∃ q : I → EssentialMarkedArc M,
      vertex M (q i0) = vertex M (r i0) ∧
      (∀ i, i ≠ i0 → q i = r i) ∧
      (∀ a b : Option I, a ≠ b →
        (crossings M (fullArc M anchor q a) (fullArc M anchor q b)).Finite ∧
        (∀ x ∈ crossings M (fullArc M anchor q a) (fullArc M anchor q b),
          CrossesInDisk M (fullArc M anchor q a) (fullArc M anchor q b) x) ∧
        (crossings M (fullArc M anchor q a) (fullArc M anchor q b)).ncard =
          (crossings M (fullArc M anchor r a) (fullArc M anchor r b)).ncard) ∧
      (tripleContactWitnesses M anchor q).ncard <
        (tripleContactWitnesses M anchor r).ncard := by
  classical
  let t : Option I → EssentialMarkedArc M := fullArc M anchor r
  let selected : Option I := some i0
  let J := {a : Option I // a ≠ selected ∧ p ∈ (t a).val.image}
  let K := {a : Option I // a ≠ selected ∧ p ∉ (t a).val.image}
  let b : J → EssentialMarkedArc M := fun a => t a.val
  let u : K → EssentialMarkedArc M := fun a => t a.val
  have hb0 : b0 ≠ selected := by
    intro he
    exact hpold.1 he.symm
  have hpb0 : p ∈ (t b0).val.image := hpold.2.2.2.1.2.1
  let j0 : J := ⟨b0,hb0,hpb0⟩
  have : Nonempty J := ⟨j0⟩
  have hpmark : p ∉ (M.cover.branch : Set S) :=
    hpold.2.2.2.1.1.2
  have hpc : p ∈ (r i0).val.image := hpold.2.2.2.1.1.1
  have hpB (j : J) : p ∈ (b j).val.image := j.property.2
  have hpU (k : K) : p ∉ (u k).val.image := k.property.2
  let lab : Option J → Option I := fun a => Option.elim a selected Subtype.val
  have hlab : Function.Injective lab :=
    option_other_label_injective selected (fun a => p ∈ (t a).val.image)
  have htype (a : Option J) : Option.elim a (r i0) b = t (lab a) := by
    cases a <;> rfl
  have hJfinite : ∀ a z : Option J, a ≠ z →
      (crossings M (Option.elim a (r i0) b)
        (Option.elim z (r i0) b)).Finite := by
    intro a z haz
    rw [htype a,htype z]
    exact hfinite (lab a) (lab z) (fun he => haz (hlab he))
  have hJcross (j : J) (x : S)
      (hx : x ∈ crossings M (r i0) (b j)) :
      CrossesInDisk M (r i0) (b j) x := by
    exact htrans selected j.val (Ne.symm j.property.1) x hx
  have hKcross (k : K) (x : S)
      (hx : x ∈ crossings M (r i0) (u k)) :
      CrossesInDisk M (r i0) (u k) x := by
    exact htrans selected k.val (Ne.symm k.property.1) x hx
  obtain ⟨F,v,δ,d,hδ,hδ1,hclass,himage,hremove,hJ,havoidJ,hK⟩ :=
    actual_incident_family_one_point_redraw M (r i0) b u p hpmark hpc hpB
      hpU hJfinite hJcross hKcross
  let q : I → EssentialMarkedArc M := fun i => if i = i0 then d else r i
  have hqi : q i0 = d := by simp [q]
  have hkeep (i : I) (hi : i ≠ i0) : q i = r i := by simp [q,hi]
  have hkeepLab (a : Option I) (ha : a ≠ selected) :
      fullArc M anchor q a = t a := by
    cases a with
    | none => rfl
    | some i =>
      change q i = r i
      exact hkeep i (fun he => ha (congrArg Option.some he))
  have hnoNewTriple : ∀ a z : Option I,
      a ≠ selected → z ≠ selected → a ≠ z →
      ∀ x, x ∈ crossings M d (t a) → x ∈ (t z).val.image →
        x ∈ crossings M (r i0) (t a) := by
    intro a z ha hz haz x hx hxz
    by_cases hpa : p ∈ (t a).val.image
    · let ja : J := ⟨a,ha,hpa⟩
      have hxa : x ∈ crossings M d (b ja) := hx
      have hset := (hJ ja).2.2.2.1
      rw [hset] at hxa
      rcases hxa with hxa | hxa
      · exact hxa.1
      · have he : x = F.symm (Schoenflies.Plane.mk (δ * (v ja) 0 / (v ja) 1) δ) :=
          Set.mem_singleton_iff.mp hxa
        by_cases hpz : p ∈ (t z).val.image
        · let jz : J := ⟨z,hz,hpz⟩
          have hne : ja ≠ jz := fun h => haz (congrArg Subtype.val h)
          exact ((havoidJ ja jz hne) (he ▸ hxz)).elim
        · let kz : K := ⟨z,hz,hpz⟩
          exact (((hJ ja).2.2.2.2 kz) (he ▸ hxz)).elim
    · let ka : K := ⟨a,ha,hpa⟩
      have hset := (hK ka).1
      exact hset ▸ hx
  have hsubset : tripleContactWitnesses M anchor q ⊆
      tripleContactWitnesses M anchor r := by
    apply triple_witnesses_subset_of_local_move M anchor r q i0 hkeepLab
    intro a z ha hz haz x hx hxz
    exact hnoNewTriple a z ha hz haz x (hqi ▸ hx) hxz
  have hdrop : (tripleContactWitnesses M anchor q).ncard <
      (tripleContactWitnesses M anchor r).ncard :=
    triple_witnesses_strict_after_center_removal M anchor r q i0 b0 c0 p
      hpold (hqi ▸ hremove) hsubset hWfinite
  have hselected (a : Option I) (ha : a ≠ selected) :
      (crossings M d (t a)).Finite ∧
      (∀ x ∈ crossings M d (t a), CrossesInDisk M d (t a) x) ∧
      (crossings M d (t a)).ncard =
        (crossings M (r i0) (t a)).ncard := by
    by_cases hp : p ∈ (t a).val.image
    · let j : J := ⟨a,ha,hp⟩
      exact ⟨(hJ j).1, (hJ j).2.2.1, (hJ j).2.1⟩
    · let k : K := ⟨a,ha,hp⟩
      have hk := hK k
      refine ⟨?_,hk.2,?_⟩
      · rw [hk.1]
        exact hfinite selected a (Ne.symm ha)
      · rw [hk.1]
  have hqselected : fullArc M anchor q selected = d := by
    simpa [fullArc,selected] using hqi
  have hrselected : t selected = r i0 := rfl
  refine ⟨q,hqi ▸ hclass,hkeep,?_,hdrop⟩
  intro a z haz
  by_cases ha : a = selected
  · have hz : z ≠ selected := fun he => haz (ha.trans he.symm)
    obtain ⟨hf,ht,hcount⟩ := hselected z hz
    rw [ha,hqselected,hkeepLab z hz]
    change (crossings M d (t z)).Finite ∧
      (∀ x ∈ crossings M d (t z), CrossesInDisk M d (t z) x) ∧
      (crossings M d (t z)).ncard =
        (crossings M (r i0) (t z)).ncard
    exact ⟨hf,ht,hcount⟩
  · by_cases hz : z = selected
    · obtain ⟨hf,ht,hcount⟩ := hselected a ha
      rw [hz,hqselected,hkeepLab a ha]
      rw [crossings_comm M (t a) d]
      change (crossings M d (t a)).Finite ∧
        (∀ x ∈ crossings M d (t a), CrossesInDisk M (t a) d x) ∧
        (crossings M d (t a)).ncard =
          (crossings M (t a) (r i0)).ncard
      rw [crossings_comm M (t a) (r i0)]
      refine ⟨hf,?_,hcount⟩
      intro x hx
      exact crossesSymm M d (t a) x (ht x hx)
    · rw [hkeepLab a ha,hkeepLab z hz]
      exact ⟨hfinite a z haz,htrans a z haz,rfl⟩

end CurveComplex.HyperellipticModel.ArcSurgery
