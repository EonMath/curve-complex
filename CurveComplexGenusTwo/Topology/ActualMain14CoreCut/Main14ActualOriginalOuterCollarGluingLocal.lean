import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualOriginalOuterCollarSideLocal

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]
set_option maxHeartbeats 5000000

-- The gluing consumer takes actual selected exterior collar halves, not a new original hypothesis.
example (M : HyperellipticModel E S) (U : Set E)
    (T : Circle × Interval ≃ₜ U)
    (L R : C(Circle × Interval,E)) (hL : Topology.IsEmbedding L) (hR : Topology.IsEmbedding R)
    (hLzero : ∀ z, L (z,0) = (T (z,0)).val)
    (hRzero : ∀ z, R (z,0) = (T (z,1)).val)
    (hLoutside : ∀ (z : Circle) (t : Interval), 0 < (t:ℝ) → L (z,t) ∉ U)
    (hRoutside : ∀ (z : Circle) (t : Interval), 0 < (t:ℝ) → R (z,t) ∉ U)
    (hLR : Disjoint (Set.range L) (Set.range R)) :
    ∃ g : C(Circle × Set.Icc (-1:ℝ) 2,E), Topology.IsEmbedding g ∧
      (∀ z, g (z,⟨0,by norm_num⟩) = (T (z,0)).val) ∧
      (∀ z, g (z,⟨1,by norm_num⟩) = (T (z,1)).val) ∧
      ∀ p : Circle × Set.Icc (-1:ℝ) 2,
        ∀ hp0 : 0 ≤ (p.2:ℝ), ∀ hp1 : (p.2:ℝ) ≤ 1,
          g p = (T (p.1,⟨p.2.val,hp0,hp1⟩)).val := by
  audit_main14_base3
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    let q : C(Circle × Interval,E) := ⟨fun p => (T p).val,continuous_subtype_val.comp T.continuous⟩
    have hq : Topology.IsEmbedding q := Topology.IsEmbedding.subtypeVal.comp T.isEmbedding
    have hLq (z : Circle) (t : Interval) (w : Circle) (v : Interval)
        (he : L (z,t) = q (w,v)) : t = 0 ∧ v = 0 ∧ z = w := by
      by_cases ht : t = 0
      · rw [ht,hLzero] at he
        have hh := T.injective (Subtype.ext he)
        have hv := congrArg (fun p : Circle × Interval => p.2) hh
        have hz := congrArg (fun p : Circle × Interval => p.1) hh
        exact ⟨ht,hv.symm,hz⟩
      · have htp : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun hn => ht (Subtype.ext hn.symm))
        exact False.elim (hLoutside z t htp (he.symm ▸ (T (w,v)).property))
    have hRq (z : Circle) (t : Interval) (w : Circle) (v : Interval)
        (he : R (z,t) = q (w,v)) : t = 0 ∧ v = 1 ∧ z = w := by
      by_cases ht : t = 0
      · rw [ht,hRzero] at he
        have hh := T.injective (Subtype.ext he)
        have hv := congrArg (fun p : Circle × Interval => p.2) hh
        have hz := congrArg (fun p : Circle × Interval => p.1) hh
        exact ⟨ht,hv.symm,hz⟩
      · have htp : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun hn => ht (Subtype.ext hn.symm))
        exact False.elim (hRoutside z t htp (he.symm ▸ (T (w,v)).property))
    let X := Set.Icc (-1 : ℝ) 2
    let τL : X → Interval := fun r => projIcc 0 1 zero_le_one (-(r:ℝ))
    let τQ : X → Interval := fun r => projIcc 0 1 zero_le_one (r:ℝ)
    let τR : X → Interval := fun r => projIcc 0 1 zero_le_one (((r:ℝ)-1))
    have hτL (r : X) (hr : (r:ℝ) ≤ 0) : (τL r:ℝ) = -(r:ℝ) := by
      dsimp only [τL]
      rw [projIcc_of_mem zero_le_one (show -(r:ℝ) ∈ Icc (0:ℝ) 1 by
        constructor <;> linarith [r.property.1])]
    have hτQ (r : X) (hr0 : 0 ≤ (r:ℝ)) (hr1 : (r:ℝ) ≤ 1) : (τQ r:ℝ) = r := by
      dsimp only [τQ]; rw [projIcc_of_mem zero_le_one ⟨hr0,hr1⟩]
    have hτR (r : X) (hr : 1 ≤ (r:ℝ)) : (τR r:ℝ) = ((r:ℝ)-1) := by
      dsimp only [τR]
      rw [projIcc_of_mem zero_le_one (show ((r:ℝ)-1) ∈ Icc (0:ℝ) 1 by
        constructor <;> linarith [r.property.2])]
    let ℓ : Circle × X → E := fun p => L (p.1,τL p.2)
    let m : Circle × X → E := fun p => q (p.1,τQ p.2)
    let r : Circle × X → E := fun p => R (p.1,τR p.2)
    have hℓcont : Continuous ℓ := L.continuous.comp
      (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
    have hmcont : Continuous m := q.continuous.comp
      (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
    have hrcont : Continuous r := R.continuous.comp
      (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
    let k : Circle × X → E := fun p => if (p.2:ℝ) ≤ 1 then m p else r p
    have hkcont : Continuous k := by
      apply continuous_if_le (by fun_prop) continuous_const hmcont.continuousOn hrcont.continuousOn
      intro p hp
      have hq1 : τQ p.2 = 1 := Subtype.ext (by rw [hτQ p.2 (by linarith) hp.le]; exact hp)
      have hr0 : τR p.2 = 0 := Subtype.ext (by rw [hτR p.2 hp.ge]; simp [hp])
      dsimp only [m,r]
      rw [hq1,hr0,hRzero]
      rfl
    let G : Circle × X → E := fun p => if (p.2:ℝ) ≤ 0 then ℓ p else k p
    have hGcont : Continuous G := by
      apply continuous_if_le (by fun_prop) continuous_const hℓcont.continuousOn hkcont.continuousOn
      intro p hp
      have hL0 : τL p.2 = 0 := Subtype.ext (by rw [hτL p.2 hp.le]; simp [hp])
      have hq0 : τQ p.2 = 0 := Subtype.ext (by rw [hτQ p.2 hp.ge (by linarith)]; exact hp)
      dsimp only [ℓ,k]
      rw [ite_eq_left (show (p.2:ℝ) ≤ 1 by linarith)]
      dsimp only [m]
      rw [hL0,hq0,hLzero]
      rfl
    have hℓinj (p s : Circle × X) (hp : (p.2:ℝ) ≤ 0) (hs : (s.2:ℝ) ≤ 0)
        (he : ℓ p = ℓ s) : p = s := by
      have hh := hL.injective he
      have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
      apply Prod.ext hz
      apply Subtype.ext
      have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
      change (τL p.2:ℝ) = (τL s.2:ℝ) at hval
      rw [hτL p.2 hp,hτL s.2 hs] at hval
      linarith
    have hminj (p s : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1)
        (hs0 : 0 ≤ (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) (he : m p = m s) : p = s := by
      have hh := hq.injective he
      have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
      apply Prod.ext hz
      apply Subtype.ext
      have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
      change (τQ p.2:ℝ) = (τQ s.2:ℝ) at hval
      rwa [hτQ p.2 hp0 hp1,hτQ s.2 hs0 hs1] at hval
    have hrinj (p s : Circle × X) (hp : 1 ≤ (p.2:ℝ)) (hs : 1 ≤ (s.2:ℝ))
        (he : r p = r s) : p = s := by
      have hh := hR.injective he
      have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
      apply Prod.ext hz
      apply Subtype.ext
      have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
      change (τR p.2:ℝ) = (τR s.2:ℝ) at hval
      rw [hτR p.2 hp,hτR s.2 hs] at hval
      linarith
    have hℓm (p s : Circle × X) (hs0 : 0 < (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) : ℓ p ≠ m s := by
      intro he
      have hh := (hLq p.1 (τL p.2) s.1 (τQ s.2) he).2.1
      have hv := congrArg Subtype.val hh
      change (τQ s.2:ℝ) = 0 at hv
      rw [hτQ s.2 hs0.le hs1] at hv
      linarith
    have hmr (p s : Circle × X) (hs : 1 < (s.2:ℝ)) : m p ≠ r s := by
      intro he
      have hh := (hRq s.1 (τR s.2) p.1 (τQ p.2) he.symm).1
      have hv := congrArg Subtype.val hh
      change (τR s.2:ℝ) = 0 at hv
      rw [hτR s.2 hs.le] at hv
      linarith
    have hℓr (p s : Circle × X) : ℓ p ≠ r s := by
      intro he
      exact Set.disjoint_left.mp hLR (Set.mem_range_self (p.1,τL p.2))
        ⟨(s.1,τR s.2),he.symm⟩
    have hGinj : Function.Injective G := by
      intro p s he
      dsimp only [G,k] at he
      by_cases hp0 : (p.2:ℝ) ≤ 0
      · rw [ite_eq_left hp0] at he
        by_cases hs0 : (s.2:ℝ) ≤ 0
        · rw [ite_eq_left hs0] at he; exact hℓinj p s hp0 hs0 he
        · rw [ite_eq_right hs0] at he
          by_cases hs1 : (s.2:ℝ) ≤ 1
          · rw [ite_eq_left hs1] at he; exact False.elim (hℓm p s (by linarith) hs1 he)
          · rw [ite_eq_right hs1] at he; exact False.elim (hℓr p s he)
      · rw [ite_eq_right hp0] at he
        by_cases hp1 : (p.2:ℝ) ≤ 1
        · rw [ite_eq_left hp1] at he
          by_cases hs0 : (s.2:ℝ) ≤ 0
          · rw [ite_eq_left hs0] at he; exact False.elim (hℓm s p (by linarith) hp1 he.symm)
          · rw [ite_eq_right hs0] at he
            by_cases hs1 : (s.2:ℝ) ≤ 1
            · rw [ite_eq_left hs1] at he; exact hminj p s (by linarith) hp1 (by linarith) hs1 he
            · rw [ite_eq_right hs1] at he; exact False.elim (hmr p s (by linarith) he)
        · rw [ite_eq_right hp1] at he
          by_cases hs0 : (s.2:ℝ) ≤ 0
          · rw [ite_eq_left hs0] at he; exact False.elim (hℓr s p he.symm)
          · rw [ite_eq_right hs0] at he
            by_cases hs1 : (s.2:ℝ) ≤ 1
            · rw [ite_eq_left hs1] at he; exact False.elim (hmr s p (by linarith) he.symm)
            · rw [ite_eq_right hs1] at he; exact hrinj p s (by linarith) (by linarith) he
    let g : C(Circle × X,E) := ⟨G,hGcont⟩
    have hg : Topology.IsEmbedding g := (hGcont.isClosedEmbedding hGinj).isEmbedding
    have hg0 (z : Circle) : g (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0) := by
      change G (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0)
      simp only [G,le_refl,if_true,ℓ,τL,neg_zero,
        projIcc_of_mem zero_le_one (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)]
      exact hLzero z
    have hg1 (z : Circle) : g (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1) := by
      change G (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1)
      simp only [G,show ¬(1:ℝ)≤0 by norm_num,if_false,k,le_refl,if_true,m,τQ,
        projIcc_of_mem zero_le_one (show (1:ℝ)∈Icc (0:ℝ) 1 by simp)]
      congr 1
    have hgmid (p : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1) :
        g p = q (p.1,⟨p.2.val,hp0,hp1⟩) := by
      by_cases hp : (p.2:ℝ) = 0
      · have he : p.2 = ⟨0,by dsimp [X]; norm_num⟩ := Subtype.ext hp
        calc
          g p = g (p.1,⟨0,by dsimp [X]; norm_num⟩) := congrArg g (Prod.ext rfl he)
          _ = q (p.1,0) := hg0 p.1
          _ = q (p.1,⟨p.2.val,hp0,hp1⟩) := congrArg q (Prod.ext rfl (Subtype.ext hp.symm))
      · change G p = _
        have hpp : 0 < (p.2:ℝ) := lt_of_le_of_ne hp0 (Ne.symm hp)
        dsimp only [G,k]
        rw [ite_eq_right (not_le_of_gt hpp),ite_eq_left hp1]
        change q (p.1,τQ p.2) = _
        congr 1
        apply Prod.ext
        · rfl
        · apply Subtype.ext; exact hτQ p.2 hp0 hp1
    exact ⟨g,hg,hg0,hg1,hgmid⟩

end CurveComplex.HyperellipticModel
