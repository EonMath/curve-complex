import C0FiniteTriangulatedDisk
import CyclicLayeredDiskSupports
import CurveComplexGenusTwo.Foundations.VertexEquiv

set_option maxHeartbeats 5000000

open Set
open scoped BigOperators

namespace CurveComplex.FiniteArcDisk

/-- The finite polygon/prism/cone layout underlying the approved N1 label
assembler. This generic existence obligation retains the literal disk and
boundary objects, seam fibres, and all ordered affine boundary blocks.
No target complex, labels, successful descent, or supplied disk is a premise. -/
theorem finite_cyclic_layered_disk_layout {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : AbstractSimplicialComplex ι) (m : ℕ)
    (vertices : Fin (m + 1) → ι)
    (vertex_closed : vertices (Fin.last m) = vertices 0)
    (edge_face : ∀ k : Fin m,
      ({vertices k.castSucc, vertices k.succ} : Finset ι) ∈ A.faces)
    (steps : ℕ) (times : Fin (m + 2) → EdgeTime)
    (times_strict : StrictMono (fun k => (times k : ℝ)))
    (times_zero : times 0 = 0)
    (times_one : times (Fin.last (m + 1)) = 1) :
    let phase : Fin (steps + 1) → ι → Option (Fin (steps + 1) × ι) :=
      fun t i => some (t, i)
    let phaseZero := phase 0;
      ∃ (D : FiniteDiskModel)
        (address : Fin D.vertexCount → Option (Fin (steps + 1) × ι))
        (param : C(EdgeTime, RealizationPoint D.boundary))
        (blocks : Fin (m + 1) → Finset (Finset ↥D.boundaryVertices)),
        (∀ σ, σ ∈ D.complex.faces → ∃ τ : Finset ι, τ ∈ A.faces ∧
          ((∃ t : Fin (steps + 1), σ.image address ⊆ τ.image (phase t)) ∨
           (∃ t : Fin steps, σ.image address ⊆
             τ.image (phase t.castSucc) ∪ τ.image (phase t.succ)) ∨
           σ.image address ⊆ insert none (τ.image (phase (Fin.last steps))))) ∧
        Function.Surjective param ∧
        (∀ t u : EdgeTime, param t = param u ↔
          t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0)) ∧
        (∀ (f : Option (Fin (steps + 1) × ι) → ℝ) (u : EdgeTime),
          (∑ v : Fin D.vertexCount, f (address v) *
            (D.boundaryInclusion (param
              (Icc.convexComb (times 0) (times 1) u))).weight v) =
            f (phaseZero (vertices 0))) ∧
        (∀ (f : Option (Fin (steps + 1) × ι) → ℝ)
            (k : Fin m) (u : EdgeTime),
          (∑ v : Fin D.vertexCount, f (address v) *
            (D.boundaryInclusion (param
              (Icc.convexComb (times k.succ.castSucc) (times k.succ.succ) u))).weight v) =
            (1 - (u : ℝ)) * f (phaseZero (vertices k.castSucc)) +
            (u : ℝ) * f (phaseZero (vertices k.succ))) ∧
        (∀ k σ, σ ∈ blocks k → σ ∈ D.boundary.faces) ∧
        (∀ σ, σ ∈ blocks 0 →
          σ.image (fun b => address b.val) ⊆ {phaseZero (vertices 0)}) ∧
        (∀ (k : Fin m) σ, σ ∈ blocks k.succ →
          σ.image (fun b => address b.val) ⊆
            {phaseZero (vertices k.castSucc), phaseZero (vertices k.succ)}) ∧
        (∀ k : Fin (m + 1),
          (⋃ σ ∈ blocks k, faceCarrier D.boundary σ) =
            Set.range (fun u : EdgeTime =>
              param (Icc.convexComb (times k.castSucc) (times k.succ) u))) ∧
        (∀ σ, σ ∈ D.boundary.faces →
          (σ.image (fun b => address b.val)) ⊆ {phaseZero (vertices 0)} ∨
          ∃ k : Fin m,
            (σ.image (fun b => address b.val)) ⊆
              {phaseZero (vertices k.castSucc), phaseZero (vertices k.succ)}) := by
  classical
  have hpad :
      ∃ q : Fin (m + 3) → ι,
        (∀ j, j.val ≤ 3 → q j = vertices 0) ∧
        (∀ k : Fin m, q ⟨k.val + 3, by omega⟩ = vertices k.castSucc) ∧
        (∀ j : Fin (m + 3),
          ({q j, q ⟨(j.val + 1) % (m + 3), Nat.mod_lt _ (by omega)⟩} : Finset ι) ∈ A.faces) := by
    let q : Fin (m + 3) → ι := fun j => vertices ⟨j.val - 3, by omega⟩
    have hq0 (j : Fin (m + 3)) (hj : j.val ≤ 3) : q j = vertices 0 := by
      apply congrArg vertices
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    refine ⟨q, hq0, ?_, ?_⟩
    · intro k
      apply congrArg vertices
      apply Fin.ext
      simp
    · intro j
      let j' : Fin (m + 3) := ⟨(j.val + 1) % (m + 3), Nat.mod_lt _ (by omega)⟩
      change ({q j, q j'} : Finset ι) ∈ A.faces
      by_cases hj : j.val < 3
      · have hfirst : q j = vertices 0 := hq0 j (by omega)
        have hsecond : q j' = vertices 0 := hq0 j' (by
          dsimp [j']
          exact (Nat.mod_le _ _).trans (by omega))
        simpa only [hfirst, hsecond, Finset.pair_eq_singleton] using A.singleton_mem (vertices 0)
      · let k : Fin m := ⟨j.val - 3, by omega⟩
        have hfirst : q j = vertices k.castSucc := by rfl
        have hsecond : q j' = vertices k.succ := by
          by_cases hlast : j.val + 1 = m + 3
          · have hj' : j' = 0 := by
              apply Fin.ext
              simp [j', hlast]
            have hk : k.succ = Fin.last m := by
              apply Fin.ext
              dsimp [k]
              omega
            rw [hj', hq0 0 (by simp), hk, vertex_closed]
          · have hlt : j.val + 1 < m + 3 := by omega
            apply congrArg vertices
            apply Fin.ext
            dsimp [q, j', k]
            rw [Nat.mod_eq_of_lt hlt]
            omega
        simpa only [hfirst, hsecond] using edge_face k
  obtain ⟨q,hqzero,hqindex,hqedge⟩ := hpad
  have rawConstruction (n : ℕ) (hn : 0 < n)
      (q : Fin n → ι)
      (q_edge : ∀ j : Fin n,
        ({q j, q ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩} : Finset ι) ∈ A.faces)
      (steps : ℕ) :
      let V := Option (Fin (steps + 1) × Fin n)
      let addr : V → Option (Fin (steps + 1) × ι) := Option.map (fun p => (p.1, q p.2))
      let next : Fin n → Fin n := fun j => ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩
      let cap : Fin n → Finset V := fun j =>
        {none, some (Fin.last steps, j), some (Fin.last steps, next j)}
      let lower : Fin steps → Fin n → Finset V := fun t j =>
        {some (t.castSucc, j), some (t.castSucc, next j), some (t.succ, next j)}
      let upper : Fin steps → Fin n → Finset V := fun t j =>
        {some (t.castSucc, j), some (t.succ, j), some (t.succ, next j)}
      ∃ K : AbstractSimplicialComplex V,
        (∀ σ, σ ∈ K.faces ↔ σ.Nonempty ∧
          ((∃ j, σ ⊆ cap j) ∨ (∃ t j, σ ⊆ lower t j) ∨ (∃ t j, σ ⊆ upper t j))) ∧
        (∀ σ, σ ∈ K.faces → σ.card ≤ 3) ∧
        (∀ σ, σ ∈ K.faces → ∃ τ : Finset ι, τ ∈ A.faces ∧
          ((∃ t : Fin (steps + 1), σ.image addr ⊆ τ.image (fun i => some (t, i))) ∨
           (∃ t : Fin steps, σ.image addr ⊆
             τ.image (fun i => some (t.castSucc, i)) ∪
             τ.image (fun i => some (t.succ, i))) ∨
           σ.image addr ⊆ insert none (τ.image (fun i => some (Fin.last steps, i))))) := by
    classical
    dsimp only
    let V := Option (Fin (steps + 1) × Fin n)
    let addr : V → Option (Fin (steps + 1) × ι) := Option.map (fun p => (p.1, q p.2))
    let next : Fin n → Fin n := fun j => ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩
    let cap : Fin n → Finset V := fun j =>
      {none, some (Fin.last steps, j), some (Fin.last steps, next j)}
    let lower : Fin steps → Fin n → Finset V := fun t j =>
      {some (t.castSucc, j), some (t.castSucc, next j), some (t.succ, next j)}
    let upper : Fin steps → Fin n → Finset V := fun t j =>
      {some (t.castSucc, j), some (t.succ, j), some (t.succ, next j)}
    let P : Finset V → Prop := fun σ => σ.Nonempty ∧
      ((∃ j, σ ⊆ cap j) ∨ (∃ t j, σ ⊆ lower t j) ∨ (∃ t j, σ ⊆ upper t j))
    have hsing (v : V) : P {v} := by
      refine ⟨Finset.singleton_nonempty _, ?_⟩
      cases v with
      | none => exact Or.inl ⟨⟨0, hn⟩, by simp [cap]⟩
      | some p =>
        rcases p with ⟨t,j⟩
        by_cases hlast : t = Fin.last steps
        · subst t
          exact Or.inl ⟨j, by simp [cap]⟩
        · have ht : t.val < steps := by
            have hne : t.val ≠ steps := by
              intro he
              apply hlast
              apply Fin.ext
              exact he
            omega
          refine Or.inr (Or.inl ⟨⟨t.val, ht⟩, j, ?_⟩)
          have he : (⟨t.val, ht⟩ : Fin steps).castSucc = t := Fin.ext rfl
          simp [lower, he]
    let K : AbstractSimplicialComplex V := {
      faces := {σ | P σ}
      isRelLowerSet_faces := by
        intro σ hσ
        refine ⟨hσ.1, ?_⟩
        intro τ hτσ hτ
        refine ⟨hτ, ?_⟩
        rcases hσ.2 with ⟨j,hj⟩ | ⟨t,j,hj⟩ | ⟨t,j,hj⟩
        · exact Or.inl ⟨j, hτσ.trans hj⟩
        · exact Or.inr (Or.inl ⟨t,j,hτσ.trans hj⟩)
        · exact Or.inr (Or.inr ⟨t,j,hτσ.trans hj⟩)
      singleton_mem := hsing }
    have hcard3 (a b c : V) : ({a,b,c} : Finset V).card ≤ 3 := by
      calc
        _ ≤ ({b,c} : Finset V).card + 1 := Finset.card_insert_le _ _
        _ ≤ ({c} : Finset V).card + 1 + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le b {c}) 1
        _ = 3 := by simp
    refine ⟨K, (fun σ => Iff.rfl), ?_, ?_⟩
    · intro σ hσ
      rcases hσ.2 with ⟨j,hj⟩ | ⟨t,j,hj⟩ | ⟨t,j,hj⟩
      all_goals apply (Finset.card_le_card hj).trans
      all_goals simp only [cap, lower, upper]
      all_goals exact hcard3 _ _ _
    · intro σ hσ
      rcases hσ.2 with ⟨j,hj⟩ | ⟨t,j,hj⟩ | ⟨t,j,hj⟩
      · refine ⟨{q j, q (next j)}, q_edge j, Or.inr (Or.inr ?_)⟩
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨v,hv,rfl⟩
        have hv' := hj hv
        simp only [cap, Finset.mem_insert, Finset.mem_singleton] at hv'
        rcases hv' with rfl | rfl | rfl <;> simp
      · refine ⟨{q j, q (next j)}, q_edge j, Or.inr (Or.inl ⟨t, ?_⟩)⟩
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨v,hv,rfl⟩
        have hv' := hj hv
        simp only [lower, Finset.mem_insert, Finset.mem_singleton] at hv'
        rcases hv' with rfl | rfl | rfl <;> simp
      · refine ⟨{q j, q (next j)}, q_edge j, Or.inr (Or.inl ⟨t, ?_⟩)⟩
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨v,hv,rfl⟩
        have hv' := hj hv
        simp only [upper, Finset.mem_insert, Finset.mem_singleton] at hv'
        rcases hv' with rfl | rfl | rfl <;> simp
  obtain ⟨K,hK,hKcard,hKaddress⟩ := rawConstruction (m+3) (by omega) q hqedge steps
  have boundaryConstruction (n : ℕ) (hn : 0 < n) (steps : ℕ)
      (K : AbstractSimplicialComplex (Option (Fin (steps + 1) × Fin n)))
      (hK : ∀ σ, σ ∈ K.faces ↔ σ.Nonempty ∧
        ((∃ j : Fin n, σ ⊆ {none, some (Fin.last steps, j),
          some (Fin.last steps, ⟨(j.val+1)%n, Nat.mod_lt _ hn⟩)}) ∨
         (∃ (t : Fin steps) (j : Fin n), σ ⊆
          {some (t.castSucc,j), some (t.castSucc,⟨(j.val+1)%n, Nat.mod_lt _ hn⟩),
           some (t.succ,⟨(j.val+1)%n, Nat.mod_lt _ hn⟩)}) ∨
         (∃ (t : Fin steps) (j : Fin n), σ ⊆
          {some (t.castSucc,j), some (t.succ,j),
           some (t.succ,⟨(j.val+1)%n, Nat.mod_lt _ hn⟩)}))) :
      ∃ B : AbstractSimplicialComplex (Fin n),
        (∀ σ, σ ∈ B.faces ↔ σ.Nonempty ∧
          ∃ j : Fin n, σ ⊆ {j, ⟨(j.val+1)%n, Nat.mod_lt _ hn⟩}) ∧
        (∀ σ, σ ∈ B.faces → σ.card ≤ 2) ∧
        (∀ σ, σ ∈ B.faces → σ.image (fun j => some ((0 : Fin (steps+1)),j)) ∈ K.faces) ∧
        ∃ inc : C(RealizationPoint B, RealizationPoint K),
          (∀ x v, (inc x).weight v = ∑ j : Fin n,
            if some ((0 : Fin (steps+1)),j) = v then x.weight j else 0) ∧
          Topology.IsClosedEmbedding inc := by
    classical
    let next : Fin n → Fin n := fun j => ⟨(j.val+1)%n, Nat.mod_lt _ hn⟩
    let B : AbstractSimplicialComplex (Fin n) := {
      faces := {σ | σ.Nonempty ∧ ∃ j, σ ⊆ {j,next j}}
      isRelLowerSet_faces := by
        intro σ hσ
        refine ⟨hσ.1, ?_⟩
        intro τ hτσ hτ
        obtain ⟨j,hj⟩ := hσ.2
        exact ⟨hτ,j,hτσ.trans hj⟩
      singleton_mem := fun j => ⟨Finset.singleton_nonempty _,j,by simp⟩ }
    have hcard (σ) (hσ : σ ∈ B.faces) : σ.card ≤ 2 := by
      obtain ⟨j,hj⟩ := hσ.2
      apply (Finset.card_le_card hj).trans
      exact (Finset.card_insert_le _ _).trans (by simp)
    have hface (σ) (hσ : σ ∈ B.faces) :
        σ.image (fun j => some ((0 : Fin (steps+1)),j)) ∈ K.faces := by
      rw [hK]
      refine ⟨hσ.1.image _, ?_⟩
      obtain ⟨j,hj⟩ := hσ.2
      cases steps with
      | zero =>
        refine Or.inl ⟨j, ?_⟩
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨v,hv,rfl⟩
        have hv' := hj hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
        rcases hv' with rfl | rfl <;> simp [next]
      | succ s =>
        refine Or.inr (Or.inl ⟨0,j,?_⟩)
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨v,hv,rfl⟩
        have hv' := hj hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
        rcases hv' with rfl | rfl <;> simp [next]
    obtain ⟨inc,hinc⟩ := regional_finite_label_realization_map B K
      (fun j => some ((0 : Fin (steps+1)),j)) hface
    have hinj : Function.Injective inc := by
      intro x y hxy
      apply RealizationPoint.ext
      funext j
      have he := congrArg (fun z : RealizationPoint K => z.weight (some (0,j))) hxy
      simpa only [hinc,Option.some.injEq,Prod.mk.injEq,true_and,Finset.sum_ite_eq',
        Finset.mem_univ,ite_true] using he
    have hcompact : CompactSpace (RealizationPoint B) := by
      have he : finiteSupportLocus B Finset.univ = Set.univ := by
        ext x
        simp [finiteSupportLocus]
      exact isCompact_univ_iff.mp (he ▸ isCompact_finiteSupportLocus B Finset.univ)
    let := hcompact
    refine ⟨B,(fun _ => Iff.rfl),hcard,hface,inc,hinc,?_⟩
    exact inc.continuous.isClosedEmbedding hinj
  obtain ⟨B,hB,hBcard,hBfaces,inc,hinc,hincClosed⟩ :=
    boundaryConstruction (m+3) (by omega) steps K hK
  obtain ⟨diskHome,boundaryHome,hhomeCompat,hboundaryExact⟩ :=
    cyclic_layered_realization_disk_pair (m+3) (by omega) steps K hK B hB inc hinc
  have timing :
      ∃ s : Fin (m+4) → EdgeTime,
        StrictMono (fun k => (s k : ℝ)) ∧ s 0 = 0 ∧ s (Fin.last (m+3)) = 1 ∧
        (∀ j : Fin 4, (s ⟨j.val, by omega⟩ : ℝ) = (times 1 : ℝ) * j.val / 3) ∧
        (∀ k : Fin (m+1), s ⟨k.val+3,by omega⟩ = times k.succ) := by
    have ht : 0 < (times 1 : ℝ) := by
      have h := times_strict (show (0 : Fin (m+2)) < 1 by simp)
      simpa [times_zero] using h
    let s : Fin (m+4) → EdgeTime := fun j =>
      if hj : j.val < 3 then ⟨(times 1 : ℝ) * j.val / 3, by
        have hj0 : (0:ℝ) ≤ j.val := Nat.cast_nonneg _
        have hj3 : (j.val:ℝ) ≤ 3 := by exact_mod_cast (show j.val ≤ 3 by omega)
        constructor
        · positivity
        · nlinarith [(times 1).property.2]⟩
      else times ⟨j.val-2,by omega⟩
    have hsmall (j : Fin 4) : (s ⟨j.val,by omega⟩ : ℝ) = (times 1 : ℝ)*j.val/3 := by
      dsimp [s]
      split_ifs with hj
      · rfl
      · have he : j.val = 3 := by omega
        simp [he]
    have htail (k : Fin (m+1)) : s ⟨k.val+3,by omega⟩ = times k.succ := by
      dsimp [s]
      congr 1
    have hs : StrictMono (fun k => (s k : ℝ)) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro k
      by_cases hk : k.val < 3
      · have h₀ := hsmall ⟨k.val,by omega⟩
        have h₁ := hsmall ⟨k.val+1,by omega⟩
        change (s ⟨k.val,by omega⟩ : ℝ) < (s ⟨k.val+1,by omega⟩ : ℝ)
        rw [h₀,h₁]
        push_cast
        nlinarith
      · let j : Fin m := ⟨k.val-3,by omega⟩
        have h₀ := htail j.castSucc
        have h₁ := htail j.succ
        have hval : j.val+3 = k.val := by dsimp [j]; omega
        have he₀ : (⟨j.castSucc.val+3,by omega⟩ : Fin (m+4)) = k.castSucc := by apply Fin.ext; exact hval
        have he₁ : (⟨j.succ.val+3,by omega⟩ : Fin (m+4)) = k.succ := by apply Fin.ext; simp only [Fin.val_succ]; omega
        rw [he₀] at h₀
        rw [he₁] at h₁
        rw [h₀,h₁]
        exact times_strict (by simp)
    refine ⟨s,hs,?_,?_,hsmall,htail⟩
    · apply Subtype.ext
      simpa using hsmall 0
    · have h := htail (Fin.last m)
      exact h.trans times_one
  obtain ⟨s,hs,hzero,hone,hsmall,htail⟩ := timing
  obtain ⟨p,hponto,hpfib,hpweight,hpcarrier⟩ :=
    cyclic_realization_affine_boundary_parameter (m+3) (by omega) B hB s hs hzero hone
  let next (j : Fin (m+3)) : Fin (m+3) := ⟨(j.val+1)%(m+3),Nat.mod_lt _ (by omega)⟩
  let addr : Option (Fin (steps+1) × Fin (m+3)) → Option (Fin (steps+1) × ι) :=
    Option.map (fun z => (z.1,q z.2))
  let edge (j : Fin (m+3)) : Finset (Fin (m+3)) := {j,next j}
  have hedge (j) : edge j ∈ B.faces := (hB _).mpr ⟨by simp [edge],j,Finset.Subset.refl _⟩
  have sumEval (f : Option (Fin (steps+1) × ι) → ℝ) (x : RealizationPoint B) :
      (∑ v, f (addr v) * (inc x).weight v) = ∑ j, f (some (0,q j)) * x.weight j := by
    simp_rw [hinc,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp [mul_ite,addr]
  have sumEdge (f : Option (Fin (steps+1) × ι) → ℝ) (j : Fin (m+3)) (u : EdgeTime) :
      (∑ v, f (addr v) * (inc (p (Icc.convexComb (s j.castSucc) (s j.succ) u))).weight v) =
      (1-(u:ℝ))*f (some (0,q j)) + (u:ℝ)*f (some (0,q (next j))) := by
    rw [sumEval]
    simp_rw [hpweight,mul_add]
    rw [Finset.sum_add_distrib]
    simp [mul_ite,next]
    ring
  have nextSource (k : Fin m) : q (next ⟨k.val+3,by omega⟩) = vertices k.succ := by
    by_cases hk : k.val+1 = m
    · have he : next ⟨k.val+3,by omega⟩ = 0 := by
        apply Fin.ext
        dsimp [next]
        have hh : k.val+3+1 = m+3 := by omega
        simp [hh]
      rw [he,hqzero 0 (by simp)]
      have he' : k.succ = Fin.last m := by apply Fin.ext; exact hk
      rw [he',vertex_closed]
    · have hlt : k.val+3+1 < m+3 := by omega
      have he : next ⟨k.val+3,by omega⟩ = ⟨(k.val+1)+3,by omega⟩ := by
        apply Fin.ext
        dsimp [next]
        rw [Nat.mod_eq_of_lt hlt]
      rw [he]
      let l : Fin m := ⟨k.val+1,by omega⟩
      exact hqindex l
  have rawEdge (f : Option (Fin (steps+1) × ι) → ℝ) (k : Fin m) (u : EdgeTime) :
      (∑ v, f (addr v) * (inc (p (Icc.convexComb
        (times k.succ.castSucc) (times k.succ.succ) u))).weight v) =
      (1-(u:ℝ))*f (some (0,vertices k.castSucc)) + (u:ℝ)*f (some (0,vertices k.succ)) := by
    have h₀ := htail k.castSucc
    have h₁ := htail k.succ
    have he₀ : (⟨k.castSucc.val+3,by omega⟩ : Fin (m+4)) = (⟨k.val+3,by omega⟩ : Fin (m+3)).castSucc := rfl
    have he₁ : (⟨k.succ.val+3,by omega⟩ : Fin (m+4)) = (⟨k.val+3,by omega⟩ : Fin (m+3)).succ := by apply Fin.ext; simp
    rw [he₀] at h₀
    rw [he₁] at h₁
    have hi : k.castSucc.succ = k.succ.castSucc := by apply Fin.ext; rfl
    rw [hi] at h₀
    rw [← h₀,← h₁,sumEdge,hqindex,nextSource]
  have intervalRange (a b : EdgeTime) (hab : (a:ℝ) < (b:ℝ)) :
      Set.range (Icc.convexComb a b) = {t : EdgeTime | (a:ℝ) ≤ (t:ℝ) ∧ (t:ℝ) ≤ (b:ℝ)} := by
    ext t
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨Icc.le_convexComb hab.le u,Icc.convexComb_le hab.le u⟩
    · intro ht
      let u : EdgeTime := ⟨((t:ℝ)-(a:ℝ))/((b:ℝ)-(a:ℝ)), by
        constructor
        · exact div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hab.le)
        · exact (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right ht.2 _)⟩
      refine ⟨u,?_⟩
      apply Subtype.ext
      dsimp [Icc.convexComb,u]
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring
  have initialCover (t : EdgeTime) (ht : (t:ℝ) ≤ (times 1 : ℝ)) :
      ∃ j : Fin 3, ∃ u : EdgeTime,
        Icc.convexComb (s (⟨j.val,by omega⟩ : Fin (m+3)).castSucc)
          (s (⟨j.val,by omega⟩ : Fin (m+3)).succ) u = t := by
    have ht0 := t.property.1
    have ht3 := hsmall 3
    have hs0 := hsmall 0
    have hs1 := hsmall 1
    have hs2 := hsmall 2
    by_cases h₁ : (t:ℝ) ≤ (s ⟨1,by omega⟩ : ℝ)
    · refine ⟨0,?_⟩
      apply Set.mem_range.mp
      rw [intervalRange _ _ (hs (by exact Fin.castSucc_lt_succ))]
      exact ⟨by simpa [hzero] using ht0,h₁⟩
    · by_cases h₂ : (t:ℝ) ≤ (s ⟨2,by omega⟩ : ℝ)
      · refine ⟨1,?_⟩
        apply Set.mem_range.mp
        rw [intervalRange _ _ (hs (by exact Fin.castSucc_lt_succ))]
        exact ⟨le_of_not_ge h₁,h₂⟩
      · refine ⟨2,?_⟩
        apply Set.mem_range.mp
        rw [intervalRange _ _ (hs (by exact Fin.castSucc_lt_succ))]
        exact ⟨le_of_not_ge h₂,by
          change (t:ℝ) ≤ (s ⟨3,by omega⟩ : ℝ)
          have h := htail 0
          change s ⟨3,by omega⟩ = times 1 at h
          rw [h]
          exact ht⟩
  have rawConstant (f : Option (Fin (steps+1) × ι) → ℝ) (u : EdgeTime) :
      (∑ v, f (addr v) * (inc (p (Icc.convexComb (times 0) (times 1) u))).weight v) =
        f (some (0,vertices 0)) := by
    have horder : (times 0 : ℝ) ≤ (times 1 : ℝ) := (times_strict (by simp)).le
    obtain ⟨j,w,hw⟩ := initialCover (Icc.convexComb (times 0) (times 1) u)
      (Icc.convexComb_le horder u)
    rw [← hw,sumEdge]
    rw [hqzero _ (by exact Nat.le_trans (Nat.le_of_lt j.isLt) (by decide))]
    rw [hqzero _ (by dsimp [next]; exact (Nat.mod_le _ _).trans (by omega))]
    ring
  let smallIndex (j : Fin 3) : Fin (m+3) := ⟨j.val,by omega⟩
  let blocks0 : Finset (Finset (Fin (m+3))) := Finset.univ.image (fun j => edge (smallIndex j))
  let rawBlocks (k : Fin (m+1)) : Finset (Finset (Fin (m+3))) :=
    if hk : k = 0 then blocks0 else {edge ⟨k.val+2,by omega⟩}
  have rawBlocks_zero : rawBlocks 0 = blocks0 := by simp [rawBlocks]
  have rawBlocks_succ (k : Fin m) : rawBlocks k.succ = {edge ⟨k.val+3,by omega⟩} := by
    simp [rawBlocks,Fin.succ_ne_zero,Nat.add_assoc]
  have rawBlockFaces (k σ) (hσ : σ ∈ rawBlocks k) : σ ∈ B.faces := by
    by_cases hk : k = 0
    · subst k
      rw [rawBlocks_zero] at hσ
      rcases Finset.mem_image.mp hσ with ⟨j,_,rfl⟩
      exact hedge _
    · have he : rawBlocks k = {edge ⟨k.val+2,by omega⟩} := dite_eq_right hk
      rw [he] at hσ
      simp only [Finset.mem_singleton] at hσ
      subst σ
      exact hedge _
  have rawBlockConst (σ) (hσ : σ ∈ rawBlocks 0) :
      σ.image (fun j => some ((0 : Fin (steps+1)),q j)) ⊆ {some (0,vertices 0)} := by
    rw [rawBlocks_zero] at hσ
    rcases Finset.mem_image.mp hσ with ⟨j,_,rfl⟩
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨v,hv,rfl⟩
    simp only [edge,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · rw [hqzero (smallIndex j) (by dsimp [smallIndex]; omega)]
      simp
    · rw [hqzero (next (smallIndex j)) (by dsimp [next,smallIndex]; exact (Nat.mod_le _ _).trans (by omega))]
      simp
  have rawBlockEdge (k : Fin m) (σ) (hσ : σ ∈ rawBlocks k.succ) :
      σ.image (fun j => some ((0 : Fin (steps+1)),q j)) ⊆
        {some (0,vertices k.castSucc),some (0,vertices k.succ)} := by
    rw [rawBlocks_succ] at hσ
    have he := Finset.mem_singleton.mp hσ
    subst σ
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨v,hv,rfl⟩
    simp only [edge,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [hqindex]
    · simp [nextSource]
  have rawFaceWord (σ) (hσ : σ ∈ B.faces) :
      σ.image (fun j => some ((0 : Fin (steps+1)),q j)) ⊆ {some (0,vertices 0)} ∨
      ∃ k : Fin m, σ.image (fun j => some ((0 : Fin (steps+1)),q j)) ⊆
        {some (0,vertices k.castSucc),some (0,vertices k.succ)} := by
    obtain ⟨_,j,hj⟩ := (hB σ).mp hσ
    by_cases hjs : j.val < 3
    · apply Or.inl
      have h := rawBlockConst (edge j) (by
        rw [rawBlocks_zero]
        exact Finset.mem_image.mpr ⟨⟨j.val,hjs⟩,Finset.mem_univ _,rfl⟩)
      exact (Finset.image_subset_image hj).trans h
    · let k : Fin m := ⟨j.val-3,by omega⟩
      have he : (⟨k.val+3,by omega⟩ : Fin (m+3)) = j := by apply Fin.ext; dsimp [k]; omega
      refine Or.inr ⟨k,?_⟩
      have h := rawBlockEdge k (edge j) (by rw [rawBlocks_succ,he]; simp)
      exact (Finset.image_subset_image hj).trans h
  have rawBlockExact (k : Fin (m+1)) :
      (⋃ σ ∈ rawBlocks k, faceCarrier B σ) =
        Set.range (fun u : EdgeTime => p (Icc.convexComb (times k.castSucc) (times k.succ) u)) := by
    by_cases hk : k = 0
    · subst k
      rw [rawBlocks_zero]
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨σ,hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hσ,hx⟩
        rcases Finset.mem_image.mp hσ with ⟨j,_,rfl⟩
        rw [show faceCarrier B (edge (smallIndex j)) = _ from hpcarrier (smallIndex j)] at hx
        obtain ⟨u,rfl⟩ := hx
        have ht : Icc.convexComb (s (smallIndex j).castSucc) (s (smallIndex j).succ) u ∈
            Set.range (Icc.convexComb (times 0) (times 1)) := by
          rw [intervalRange _ _ (times_strict (by simp))]
          refine ⟨?_,?_⟩
          · simpa [times_zero] using (Icc.convexComb (s (smallIndex j).castSucc) (s (smallIndex j).succ) u).property.1
          · apply (Icc.convexComb_le (hs (by simp)).le u).trans
            have hh := hsmall ⟨j.val+1,by omega⟩
            change (s ⟨j.val+1,by omega⟩ : ℝ) ≤ (times 1 : ℝ)
            rw [hh]
            have hj : (j.val : ℝ) ≤ 2 := by exact_mod_cast (show j.val ≤ 2 by omega)
            push_cast
            nlinarith [(times 1).property.1]
        obtain ⟨w,hw⟩ := ht
        exact ⟨w,congrArg p hw⟩
      · rintro ⟨u,rfl⟩
        obtain ⟨j,w,hw⟩ := initialCover (Icc.convexComb (times 0) (times 1) u)
          (Icc.convexComb_le (times_strict (by simp)).le u)
        apply Set.mem_iUnion.mpr
        refine ⟨edge (smallIndex j),Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
        · exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
        · rw [show faceCarrier B (edge (smallIndex j)) = _ from hpcarrier (smallIndex j)]
          exact ⟨w,congrArg p hw⟩
    · obtain ⟨l,rfl⟩ : ∃ l : Fin m, l.succ = k := ⟨k.pred hk, Fin.succ_pred k hk⟩
      rw [rawBlocks_succ]
      simp only [Finset.mem_singleton,Set.iUnion_iUnion_eq_left]
      rw [show faceCarrier B (edge ⟨l.val+3,by omega⟩) = _ from hpcarrier ⟨l.val+3,by omega⟩]
      have h₀ := htail l.castSucc
      have h₁ := htail l.succ
      have hi : l.castSucc.succ = l.succ.castSucc := by apply Fin.ext; rfl
      rw [hi] at h₀
      have he₁ : (⟨l.succ.val+3,by omega⟩ : Fin (m+4)) = (⟨l.val+3,by omega⟩ : Fin (m+3)).succ := by apply Fin.ext; simp
      rw [he₁] at h₁
      change s (⟨l.val+3,by omega⟩ : Fin (m+3)).castSucc = times l.succ.castSucc at h₀
      rw [h₀,h₁]
  have relabel {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      (J : AbstractSimplicialComplex X) (e : X ≃ Y) :
      ∃ (L : AbstractSimplicialComplex Y) (H : RealizationPoint J ≃ₜ RealizationPoint L),
        (∀ σ, σ ∈ L.faces ↔ σ.image e.symm ∈ J.faces) ∧
        (∀ x y, (H x).weight y = x.weight (e.symm y)) ∧
        (∀ x y, (H.symm x).weight y = x.weight (e y)) ∧
        (∀ σ x, H x ∈ faceCarrier L (σ.image e) ↔ x ∈ faceCarrier J σ) := by
    classical
    let L : AbstractSimplicialComplex Y := {
      faces := {σ | σ.image e.symm ∈ J.faces}
      isRelLowerSet_faces := by
        intro σ hσ
        refine ⟨?_,?_⟩
        · exact Finset.image_nonempty.mp (J.isRelLowerSet_faces hσ).1
        · intro τ hτσ hτ
          exact (J.isRelLowerSet_faces hσ).2 (Finset.image_subset_image hτσ) (hτ.image _)
      singleton_mem := by intro y; simpa using J.singleton_mem (e.symm y) }
    have hface (σ : Finset X) : σ ∈ J.faces ↔ σ.image e ∈ L.faces := by
      change _ ↔ (σ.image e).image e.symm ∈ J.faces
      simp [Finset.image_image]
    let H := realizationHomeomorphOfVertexEquiv J L e hface
    have hw (x y) : (H x).weight y = x.weight (e.symm y) := rfl
    have hiw (x y) : (H.symm x).weight y = x.weight (e y) := rfl
    refine ⟨L,H,(fun _ => Iff.rfl),hw,hiw,?_⟩
    intro σ x
    change (∀ v, v ∉ σ.image e → (H x).weight v = 0) ↔ ∀ v, v ∉ σ → x.weight v = 0
    constructor
    · intro h v hv
      have hh := h (e v) (by simpa using hv)
      simpa only [hw,e.symm_apply_apply] using hh
    · intro h v hv
      rw [hw]
      exact h _ (fun hh => hv (Finset.mem_image.mpr ⟨e.symm v,hh,e.apply_symm_apply v⟩))
  let V := Option (Fin (steps+1) × Fin (m+3))
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  obtain ⟨L,H,hL,hH,hHinv,hHcarrier⟩ := relabel K e
  let bottom (j : Fin (m+3)) : V := some (0,j)
  let bv : Finset (Fin (Fintype.card V)) := Finset.univ.image (fun j => e (bottom j))
  let bf (j : Fin (m+3)) : ↥bv := ⟨e (bottom j),Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  have hbf : Function.Bijective bf := by
    constructor
    · intro i j he
      have h : bottom i = bottom j := e.injective (congrArg Subtype.val he)
      exact (Prod.mk.inj (Option.some.inj h)).2
    · intro v
      rcases Finset.mem_image.mp v.property with ⟨j,_,hj⟩
      exact ⟨j,Subtype.ext hj⟩
  let b : Fin (m+3) ≃ ↥bv := Equiv.ofBijective bf hbf
  have hbval (j) : (b j).val = e (bottom j) := rfl
  obtain ⟨LB,HB,hLB,hHB,hHBinv,hHBcarrier⟩ := relabel B b
  let incl : C(RealizationPoint LB,RealizationPoint L) :=
    ⟨fun x => H (inc (HB.symm x)),H.continuous.comp (inc.continuous.comp HB.symm.continuous)⟩
  have hIncl (x : RealizationPoint LB) (v) :
      (incl x).weight v = ∑ z : ↥bv, if z.val = v then x.weight z else 0 := by
    change (H (inc (HB.symm x))).weight v = _
    rw [hH,hinc]
    simp_rw [hHBinv]
    rw [← b.sum_comp (fun z => if z.val = v then x.weight z else 0)]
    apply Finset.sum_congr rfl
    intro j _
    rw [hbval]
    have hi : some ((0 : Fin (steps+1)),j) = e.symm v ↔ e (bottom j) = v := by
      exact e.eq_symm_apply
    exact if_ctx_congr hi (fun _ => rfl) (fun _ => rfl)
  have hInclClosed : Topology.IsClosedEmbedding incl :=
    H.isClosedEmbedding.comp (hincClosed.comp HB.symm.isClosedEmbedding)
  have hBfaces' (σ) (hσ : σ ∈ LB.faces) : σ.image Subtype.val ∈ L.faces := by
    rw [hL]
    have h := hBfaces (σ.image b.symm) ((hLB σ).mp hσ)
    convert h using 1
    simp only [Finset.image_image]
    congr 1
    funext z
    have hh := hbval (b.symm z)
    rw [b.apply_symm_apply] at hh
    exact (e.symm_apply_eq).mpr hh
  have hcardL (σ) (hσ : σ ∈ L.faces) : σ.card ≤ 3 := by
    have h := hKcard (σ.image e.symm) ((hL σ).mp hσ)
    simpa only [Finset.card_image_of_injective _ e.symm.injective] using h
  have hcardLB (σ) (hσ : σ ∈ LB.faces) : σ.card ≤ 2 := by
    have h := hBcard (σ.image b.symm) ((hLB σ).mp hσ)
    simpa only [Finset.card_image_of_injective _ b.symm.injective] using h
  let D : FiniteDiskModel := {
    vertexCount := Fintype.card V
    complex := L
    boundaryVertices := bv
    boundary := LB
    boundary_faces := hBfaces'
    face_card := hcardL
    boundary_face_card := hcardLB
    boundaryInclusion := incl
    boundaryInclusion_weight := hIncl
    boundaryInclusion_closedEmbedding := hInclClosed
    diskHome := H.symm.trans diskHome
    boundaryHome := HB.symm.trans boundaryHome
    boundaryHome_compat := by
      intro x
      change (boundaryHome (HB.symm x)).val = (diskHome (H.symm (H (inc (HB.symm x))))).val
      rw [H.symm_apply_apply]
      exact hhomeCompat (HB.symm x)
    boundary_exact := by
      intro x
      change x ∈ Set.range incl ↔ ‖(diskHome (H.symm x)).val‖ = 1
      rw [← hboundaryExact]
      constructor
      · rintro ⟨y,rfl⟩
        exact ⟨HB.symm y,(H.symm_apply_apply _).symm⟩
      · rintro ⟨y,hy⟩
        refine ⟨HB y,?_⟩
        change H (inc (HB.symm (HB y))) = x
        rw [HB.symm_apply_apply,hy,H.apply_symm_apply]
    closed_faces := fun σ _ => isClosed_faceCarrier L σ
    faces_cover := fun x => by
      obtain ⟨σ,hσ,p,rfl⟩ := exists_faceInclusion_eq L x
      exact ⟨σ,hσ,faceInclusion_mem_faceCarrier L σ hσ p⟩ }
  let address : Fin D.vertexCount → Option (Fin (steps+1) × ι) := fun v => addr (e.symm v)
  let param : C(EdgeTime,RealizationPoint D.boundary) := ⟨fun t => HB (p t),HB.continuous.comp p.continuous⟩
  let blocks (k : Fin (m+1)) : Finset (Finset ↥D.boundaryVertices) :=
    (rawBlocks k).image (fun σ => σ.image b)
  have hAddress (j) : address (b j).val = some ((0 : Fin (steps+1)),q j) := by
    change addr (e.symm (b j).val) = _
    rw [hbval,e.symm_apply_apply]
    rfl
  have totalWeight (f : Option (Fin (steps+1) × ι) → ℝ) (t : EdgeTime) :
      (∑ v : Fin D.vertexCount, f (address v) * (D.boundaryInclusion (param t)).weight v) =
        ∑ v : V, f (addr v) * (inc (p t)).weight v := by
    change (∑ v, f (addr (e.symm v)) * (H (inc (HB.symm (HB (p t))))).weight v) = _
    rw [HB.symm_apply_apply]
    simp_rw [hH]
    exact e.symm.sum_comp (fun v => f (addr v) * (inc (p t)).weight v)
  have blockImage (σ : Finset (Fin (m+3))) :
      (σ.image b).image (fun z => address z.val) =
        σ.image (fun j => some ((0 : Fin (steps+1)),q j)) := by
    simp only [Finset.image_image,Function.comp_def,hAddress]
  have faceImage (σ : Finset ↥bv) :
      σ.image (fun z => address z.val) =
        (σ.image b.symm).image (fun j => some ((0 : Fin (steps+1)),q j)) := by
    simp only [Finset.image_image]
    congr 1
    funext z
    have h := hAddress (b.symm z)
    simpa only [Function.comp_def,b.apply_symm_apply] using h
  refine ⟨D,address,param,blocks,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro σ hσ
    have h := hKaddress (σ.image e.symm) ((hL σ).mp hσ)
    simpa only [Finset.image_image,Function.comp_def,address,addr] using h
  · exact HB.surjective.comp hponto
  · intro t u
    change HB (p t) = HB (p u) ↔ _
    rw [HB.injective.eq_iff]
    exact hpfib t u
  · intro f u
    rw [totalWeight]
    exact rawConstant f u
  · intro f k u
    rw [totalWeight]
    exact rawEdge f k u
  · intro k σ hσ
    obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
    change τ.image b ∈ LB.faces
    rw [hLB]
    simpa only [Finset.image_image,Function.comp_def,b.symm_apply_apply,Finset.image_id'] using rawBlockFaces k τ hτ
  · intro σ hσ
    obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
    rw [blockImage]
    exact rawBlockConst τ hτ
  · intro k σ hσ
    obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
    rw [blockImage]
    exact rawBlockEdge k τ hτ
  · intro k
    ext x
    constructor
    · intro hx
      obtain ⟨σ,hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hσ,hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
      have hh : HB.symm x ∈ faceCarrier B τ := by
        apply (hHBcarrier τ (HB.symm x)).mp
        simpa only [HB.apply_symm_apply] using hx
      have hr : HB.symm x ∈ ⋃ σ ∈ rawBlocks k, faceCarrier B σ :=
        Set.mem_iUnion.mpr ⟨τ,Set.mem_iUnion.mpr ⟨hτ,hh⟩⟩
      rw [rawBlockExact] at hr
      obtain ⟨u,hu⟩ := hr
      refine ⟨u,?_⟩
      change HB (p _) = x
      exact (congrArg HB hu).trans (HB.apply_symm_apply x)
    · rintro ⟨u,rfl⟩
      have hr : p (Icc.convexComb (times k.castSucc) (times k.succ) u) ∈
          ⋃ σ ∈ rawBlocks k, faceCarrier B σ := by
        rw [rawBlockExact]
        exact ⟨u,rfl⟩
      obtain ⟨τ,hr⟩ := Set.mem_iUnion.mp hr
      obtain ⟨hτ,hr⟩ := Set.mem_iUnion.mp hr
      refine Set.mem_iUnion.mpr ⟨τ.image b,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
      · exact Finset.mem_image.mpr ⟨τ,hτ,rfl⟩
      · exact (hHBcarrier τ _).mpr hr
  · intro σ hσ
    rw [faceImage]
    exact rawFaceWord (σ.image b.symm) ((hLB σ).mp hσ)

end CurveComplex.FiniteArcDisk
