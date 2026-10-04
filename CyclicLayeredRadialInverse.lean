import C0FiniteTriangulatedDisk

open Set
open scoped BigOperators
namespace CurveComplex.FiniteArcDisk

/-- Recognition of the prescribed cyclic layered triangle complex and its
literal bottom boundary as the original weak-realization disk/sphere pair. -/
theorem cyclic_layered_radial_coordinates_unique_recovery (n : ℕ) (hn : 3 ≤ n) (steps : ℕ)
    (K : AbstractSimplicialComplex (Option (Fin (steps + 1) × Fin n)))
    (hK : ∀ σ, σ ∈ K.faces ↔ σ.Nonempty ∧
      ((∃ j : Fin n, σ ⊆ {none, some (Fin.last steps, j),
        some (Fin.last steps, ⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩)}) ∨
       (∃ (t : Fin steps) (j : Fin n), σ ⊆
        {some (t.castSucc,j), some (t.castSucc,⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩),
         some (t.succ,⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩)}) ∨
       (∃ (t : Fin steps) (j : Fin n), σ ⊆
        {some (t.castSucc,j), some (t.succ,j),
         some (t.succ,⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩)}))) 
    : ∀ (q : Fin n → ℝ), (∀ j, 0 ≤ q j) → (∑ j,q j) ≤ 1 →
      (∃ j : Fin n, ∀ k, k ∉ ({j,⟨(j.val+1)%n,Nat.mod_lt _ (by omega)⟩} : Finset (Fin n)) → q k = 0) →
      ∃! x : RealizationPoint K, ∀ j : Fin n,
        (∑ t : Fin (steps+1), (1 - (t.val : ℝ) / ((steps : ℝ)+1)) *
          x.weight (some (t,j))) = q j := by
  set_option maxHeartbeats 2000000 in
  set_option maxRecDepth 100000 in
    classical
    let V := Option (Fin (steps + 1) × Fin n)
    let next : Fin n → Fin n := fun j => ⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩
    let r : Fin (steps+1) → ℝ := fun t => 1 - (t.val : ℝ) / ((steps : ℝ)+1)
    let coord (x : RealizationPoint K) (j : Fin n) :=
      ∑ t : Fin (steps+1), r t * x.weight (some (t,j))
    have hd : 0 < (steps : ℝ) + 1 := by positivity
    have hr (t : Fin (steps+1)) : 0 < r t := by
      dsimp [r]
      have ht : (t.val : ℝ) < (steps : ℝ) + 1 := by exact_mod_cast t.isLt
      exact sub_pos.mpr ((div_lt_one hd).mpr ht)
    have hnxt (j : Fin n) : next j ≠ j := by
      intro h
      have hh := congrArg Fin.val h
      dsimp [next] at hh
      have hj := j.isLt
      by_cases hlt : j.val + 1 < n
      · rw [Nat.mod_eq_of_lt hlt] at hh
        omega
      · have he : j.val + 1 = n := by omega
        rw [he, Nat.mod_self] at hh
        omega
    have sum_weights (x : RealizationPoint K) : ∑ v, x.weight v = 1 := by
      obtain ⟨σ, _, hz, hs⟩ := x.liesInFace
      rw [← hs]
      exact (Finset.sum_subset (Finset.subset_univ σ) (by
        intro v _ hv
        exact hz v hv)).symm
    have make_point (a b c : V) (A B C : ℝ)
        (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hs : A+B+C=1)
        (hf : ({a,b,c} : Finset V) ∈ K.faces) :
        ∃ x : RealizationPoint K, ∀ v,
          x.weight v = (if v=a then A else 0) + (if v=b then B else 0) +
            (if v=c then C else 0) := by
      let w : V → ℝ := fun v =>
        (if v=a then A else 0) + (if v=b then B else 0) + (if v=c then C else 0)
      have hw (v) : 0 ≤ w v := by
        dsimp [w]
        positivity
      have hz (v) (hv : v ∉ ({a,b,c} : Finset V)) : w v = 0 := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
        simp [w, hv.1, hv.2.1, hv.2.2]
      have ht : ∑ v, w v = 1 := by
        change (∑ v : V, w v) = 1
        dsimp only [w]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq',Finset.sum_ite_eq',Finset.sum_ite_eq']
        simpa using hs
      exact ⟨⟨w,hw,⟨{a,b,c},hf,hz,by
        rw [← ht]
        exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hz v hv)⟩⟩,
        fun _ => rfl⟩
    have coord_formula (x : RealizationPoint K) (a b c : V) (A B C : ℝ)
        (hw : ∀ v, x.weight v = (if v=a then A else 0) +
          (if v=b then B else 0) + (if v=c then C else 0)) (j : Fin n) :
        coord x j =
          (match a with | none => 0 | some (t,k) => if k=j then r t*A else 0) +
          (match b with | none => 0 | some (t,k) => if k=j then r t*B else 0) +
          (match c with | none => 0 | some (t,k) => if k=j then r t*C else 0) := by
      dsimp [coord]
      simp only [hw, mul_add, Finset.sum_add_distrib]
      have aux (v : V) (z : ℝ) :
          (∑ t : Fin (steps+1), r t * (if some (t,j)=v then z else 0)) =
          (match v with | none => 0 | some (t,k) => if k=j then r t*z else 0) := by
        cases v with
        | none => simp
        | some p =>
          rcases p with ⟨s,k⟩
          by_cases hk : k=j
          · subst k
            simp
          · simp [hk,Ne.symm hk]
      rw [aux,aux,aux]
      cases a <;> cases b <;> cases c <;> rfl
    intro q hq hsum hsupport
    change ∃! x : RealizationPoint K, ∀ j, coord x j = q j
    -- Choose the cap or the two triangles in the unique radial band.
    have hex : ∃ x : RealizationPoint K, ∀ j, coord x j = q j := by
      obtain ⟨j,hj⟩ := hsupport
      change ∀ k, k ∉ ({j,next j} : Finset (Fin n)) → q k = 0 at hj
      have hqsum : (∑ k, q k) = q j + q (next j) := by
        rw [← Finset.sum_subset (Finset.subset_univ ({j,next j} : Finset (Fin n)))
          (fun k _ hk => hj k hk)]
        simp [hnxt,Ne.symm (hnxt j)]
      let S : ℝ := q j + q (next j)
      have hS : 0 ≤ S := add_nonneg (hq j) (hq (next j))
      have hS1 : S ≤ 1 := by simpa [hqsum,S] using hsum
      have hql (k) : q k = if j=k then q j else if next j=k then q (next j) else 0 := by
        by_cases h1 : j=k
        · subst k
          simp
        · by_cases h2 : next j=k
          · subst k
            simp [hnxt,Ne.symm (hnxt j)]
          · rw [if_neg h1,if_neg h2]
            apply hj
            simpa [eq_comm] using And.intro h1 h2
      by_cases hcap : S ≤ r (Fin.last steps)
      · let a := r (Fin.last steps)
        have ha : 0 < a := hr _
        obtain ⟨x,hx⟩ := make_point none (some (Fin.last steps,j))
          (some (Fin.last steps,next j)) (1-S/a) (q j/a) (q (next j)/a)
          (by exact sub_nonneg.mpr ((div_le_one ha).mpr hcap))
          (div_nonneg (hq _) ha.le) (div_nonneg (hq _) ha.le)
          (by dsimp [S]; ring)
          ((hK _).mpr ⟨by simp,Or.inl ⟨j,by simp [next]⟩⟩)
        refine ⟨x,fun k => ?_⟩
        rw [coord_formula x _ _ _ _ _ _ hx k,hql k]
        dsimp only
        have hmul (z : ℝ) : r (Fin.last steps) * (z/a) = z := by
          change a * (z/a) = z
          field_simp
        rw [hmul,hmul]
        by_cases h1 : j=k
        · subst k
          simp [hnxt]
        · by_cases h2 : next j=k
          · simp [h1,h2]
          · simp [h1,h2]
      · have hfloor0 : 0 ≤ (1-S)*((steps : ℝ)+1) :=
          mul_nonneg (sub_nonneg.mpr hS1) hd.le
        have hfloorlt : (1-S)*((steps : ℝ)+1) < (steps : ℝ) := by
          have hcap' : 1-(steps : ℝ)/((steps : ℝ)+1) < S := lt_of_not_ge hcap
          have hmul := (lt_div_iff₀ hd).mp (show (steps : ℝ)/((steps : ℝ)+1) > 1-S by linarith)
          nlinarith
        let t : Fin steps := ⟨⌊(1-S)*((steps : ℝ)+1)⌋₊,(Nat.floor_lt hfloor0).mpr hfloorlt⟩
        let a := r t.castSucc
        let b := r t.succ
        have ha : 0 < a := hr _
        have hb : 0 < b := hr _
        have hab : b < a := by
          dsimp [a,b,r]
          rw [Nat.cast_add,Nat.cast_one]
          apply sub_lt_sub_left
          exact (div_lt_div_iff_of_pos_right hd).mpr (by linarith)
        have hSa : S ≤ a := by
          have hf := Nat.floor_le hfloor0
          change (⌊(1-S)*((steps : ℝ)+1)⌋₊ : ℝ) ≤ (1-S)*((steps : ℝ)+1) at hf
          dsimp [a,r,t]
          apply le_sub_iff_add_le.mpr
          have hh := (div_le_iff₀ hd).mpr hf
          linarith
        have hbS : b < S := by
          have hf := Nat.lt_floor_add_one ((1-S)*((steps : ℝ)+1))
          dsimp [b,r,t]
          rw [Nat.cast_add,Nat.cast_one]
          have hh := (lt_div_iff₀ hd).mpr hf
          linarith
        let u := (S-b)/(a-b)
        have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hbS.le) (sub_pos.mpr hab).le
        have hu1 : u ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr (by linarith)
        have hSu : S = a*u+b*(1-u) := by dsimp [u]; field_simp [ne_of_gt (sub_pos.mpr hab)]; ring
        by_cases hdiag : q j ≤ a*u
        · let A := q j/a
          let B := u-A
          let C := 1-u
          have hA : 0 ≤ A := div_nonneg (hq j) ha.le
          have hB : 0 ≤ B := sub_nonneg.mpr ((div_le_iff₀ ha).mpr (by nlinarith [hdiag]))
          have hC : 0 ≤ C := sub_nonneg.mpr hu1
          have hAeq : a*A = q j := by dsimp [A]; field_simp
          have hBeq : a*B+b*C = q (next j) := by dsimp [B,C,S] at *; nlinarith [hSu]
          obtain ⟨x,hx⟩ := make_point (some (t.castSucc,j)) (some (t.castSucc,next j))
            (some (t.succ,next j)) A B C hA hB hC (by dsimp [B,C]; ring)
            ((hK _).mpr ⟨by simp,Or.inr (Or.inl ⟨t,j,by simp [next]⟩)⟩)
          refine ⟨x,fun k => ?_⟩
          rw [coord_formula x _ _ _ _ _ _ hx k,hql k]
          dsimp only
          change (if j=k then a*A else 0) + (if next j=k then a*B else 0) +
            (if next j=k then b*C else 0) = _
          by_cases h1 : j=k
          · subst k
            simp [hnxt,hAeq]
          · by_cases h2 : next j=k
            · simp [h1,h2,hBeq]
            · simp [h1,h2]
        · let A := u
          let B := (q j-a*u)/b
          let C := q (next j)/b
          have hA : 0 ≤ A := hu0
          have hB : 0 ≤ B := div_nonneg (by linarith) hb.le
          have hC : 0 ≤ C := div_nonneg (hq _) hb.le
          have hBeq : b*B = q j-a*u := by dsimp [B]; field_simp
          have hCeq : b*C = q (next j) := by dsimp [C]; field_simp
          have htotal : A+B+C=1 := by dsimp [A,S] at *; nlinarith [hSu]
          obtain ⟨x,hx⟩ := make_point (some (t.castSucc,j)) (some (t.succ,j))
            (some (t.succ,next j)) A B C hA hB hC htotal
            ((hK _).mpr ⟨by simp,Or.inr (Or.inr ⟨t,j,by simp [next]⟩)⟩)
          refine ⟨x,fun k => ?_⟩
          rw [coord_formula x _ _ _ _ _ _ hx k,hql k]
          dsimp only
          change (if j=k then a*A else 0) + (if j=k then b*B else 0) +
            (if next j=k then b*C else 0) = _
          by_cases h1 : j=k
          · subst k
            simp only [ite_true,hnxt,ite_false,add_zero]
            dsimp [A]
            linarith
          · by_cases h2 : next j=k
            · simp [h1,h2,hCeq]
            · simp [h1,h2]
    obtain ⟨x,hx⟩ := hex
    refine ⟨x,hx,?_⟩
    intro y hy
    obtain ⟨j,hj⟩ := hsupport
    change ∀ k, k ∉ ({j,next j} : Finset (Fin n)) → q k = 0 at hj
    have next_inj : Function.Injective next := by
      intro i k he
      have hh := congrArg Fin.val he
      dsimp [next] at hh
      have hi := i.isLt
      have hk := k.isLt
      apply Fin.ext
      by_cases h1 : i.val+1 < n <;> by_cases h2 : k.val+1 < n
      · rw [Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h2] at hh
        omega
      · have he2 : k.val+1=n := by omega
        rw [Nat.mod_eq_of_lt h1,he2,Nat.mod_self] at hh
        omega
      · have he1 : i.val+1=n := by omega
        rw [he1,Nat.mod_self,Nat.mod_eq_of_lt h2] at hh
        omega
      · omega
    have next_next_ne (i : Fin n) : next (next i) ≠ i := by
      intro he
      have hh := congrArg Fin.val he
      have hi := i.isLt
      dsimp [next] at hh
      by_cases h1 : i.val+1 < n
      · rw [Nat.mod_eq_of_lt h1] at hh
        by_cases h2 : i.val+1+1 < n
        · rw [Nat.mod_eq_of_lt h2] at hh
          omega
        · have he2 : i.val+1+1=n := by omega
          rw [he2,Nat.mod_self] at hh
          omega
      · have he1 : i.val+1=n := by omega
        rw [he1,Nat.mod_self,zero_add,Nat.mod_eq_of_lt (by omega)] at hh
        omega
    let cap : Finset V := {none,some (Fin.last steps,j),some (Fin.last steps,next j)}
    let upper (t : Fin steps) : Finset V :=
      {some (t.castSucc,j),some (t.castSucc,next j),some (t.succ,next j)}
    let lower (t : Fin steps) : Finset V :=
      {some (t.castSucc,j),some (t.succ,j),some (t.succ,next j)}
    let supported (z : RealizationPoint K) (F : Finset V) := ∀ v, v ∉ F → z.weight v=0
    have off_sector (z : RealizationPoint K) (hz : ∀ k, coord z k = q k)
        (t : Fin (steps+1)) (k : Fin n) (hkj : k≠j) (hkn : k≠next j) :
        z.weight (some (t,k))=0 := by
      have hqk := hj k (by simp [hkj,hkn])
      have hh := hz k
      rw [hqk] at hh
      have hnon (s : Fin (steps+1)) (_ : s ∈ Finset.univ) :
          0 ≤ r s*z.weight (some (s,k)) := mul_nonneg (hr s).le (z.nonneg _)
      have hh' := (Finset.sum_eq_zero_iff_of_nonneg hnon).mp hh t (Finset.mem_univ _)
      exact (mul_eq_zero.mp hh').resolve_left (ne_of_gt (hr t))
    -- Zero radial coordinates force all weights on that ray to vanish.
    -- Hence every competitor is supported in this same cyclic sector.
    have shape (z : RealizationPoint K) (hz : ∀ k, coord z k=q k) :
        supported z cap ∨ (∃ t, supported z (upper t)) ∨ ∃ t, supported z (lower t) := by
      obtain ⟨σ,hσ,hzero,_⟩ := z.liesInFace
      rcases (hK σ).mp hσ with ⟨_,⟨i,hi⟩ | ⟨t,i,hi⟩ | ⟨t,i,hi⟩⟩
      · left
        intro v hv
        by_cases hmem : v∈σ
        · have hm := hi hmem
          simp only [Finset.mem_insert,Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl
          · exact False.elim (hv (by simp [cap]))
          · apply off_sector z hz <;> intro he <;> apply hv <;> simp [cap,he,next]
          · apply off_sector z hz <;> intro he <;> apply hv <;> simp [cap,he,next]
        · exact hzero v hmem
      · by_cases hij : i=j
        · subst i
          exact Or.inr (Or.inl ⟨t,fun v hv => hzero v (fun h => hv (hi h))⟩)
        · by_cases hin : i=next j
          · subst i
            right; left
            refine ⟨t,fun v hv => ?_⟩
            by_cases hmem : v∈σ
            · have hm := hi hmem
              simp only [Finset.mem_insert,Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl
              · exact False.elim (hv (by simp [upper]))
              · exact off_sector z hz _ _ (next_next_ne j) (hnxt (next j))
              · exact off_sector z hz _ _ (next_next_ne j) (hnxt (next j))
            · exact hzero v hmem
          · right; right
            refine ⟨t,fun v hv => ?_⟩
            by_cases hmem : v∈σ
            · have hm := hi hmem
              simp only [Finset.mem_insert,Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl
              · exact off_sector z hz _ _ hij hin
              · apply off_sector z hz
                · intro he
                  apply hv
                  simp [lower,← he,next]
                · exact fun he => hij (next_inj he)
              · apply off_sector z hz
                · intro he
                  apply hv
                  simp [lower,← he,next]
                · exact fun he => hij (next_inj he)
            · exact hzero v hmem
      · by_cases hij : i=j
        · subst i
          exact Or.inr (Or.inr ⟨t,fun v hv => hzero v (fun h => hv (hi h))⟩)
        · by_cases hin : i=next j
          · subst i
            right; left
            refine ⟨t,fun v hv => ?_⟩
            by_cases hmem : v∈σ
            · have hm := hi hmem
              simp only [Finset.mem_insert,Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl
              · exact False.elim (hv (by simp [upper]))
              · exact False.elim (hv (by simp [upper]))
              · exact off_sector z hz _ _ (next_next_ne j) (hnxt (next j))
            · exact hzero v hmem
          · right; right
            refine ⟨t,fun v hv => ?_⟩
            by_cases hmem : v∈σ
            · have hm := hi hmem
              simp only [Finset.mem_insert,Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl
              · exact off_sector z hz _ _ hij hin
              · exact off_sector z hz _ _ hij hin
              · apply off_sector z hz
                · intro he
                  apply hv
                  simp [lower,← he,next]
                · exact fun he => hij (next_inj he)
            · exact hzero v hmem
    have r_le (t : Fin (steps+1)) : r t ≤ 1 := by
      dsimp [r]
      have hh : 0 ≤ (t.val : ℝ) / ((steps : ℝ)+1) := div_nonneg (Nat.cast_nonneg _) hd.le
      linarith
    have r_anti : StrictAnti r := by
      intro s t hst
      dsimp [r]
      apply sub_lt_sub_left
      exact (div_lt_div_iff_of_pos_right hd).mpr (by exact_mod_cast hst)
    -- A small asymmetric quadratic lift distinguishes the prescribed diagonals.
    -- Each triangle has a supporting plane meeting exactly its three vertices.
    let L : ℝ := 1 + 1 / (2*((steps : ℝ)+1))
    have hL : 1 < L := by
      dsimp [L]
      exact lt_add_of_pos_right 1 (by positivity)
    have hL0 : 0 < L := by linarith
    have band_gap (t : Fin steps) : L*r t.succ < r t.castSucc := by
      have hstep : r t.castSucc-r t.succ=1/((steps : ℝ)+1) := by
        dsimp [r]
        rw [Nat.cast_add,Nat.cast_one]
        ring
      have hs := r_le t.succ
      have hd2 : 0 < 1/((steps : ℝ)+1) := by positivity
      have hmul : 1 / (2*((steps : ℝ)+1)) * r t.succ ≤ 1/(2*((steps : ℝ)+1)) := by
        simpa using mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1/(2*((steps : ℝ)+1)))
      have he : 1/(2*((steps : ℝ)+1)) = (1/((steps : ℝ)+1))/2 := by field_simp
      dsimp [L]
      nlinarith
    have band_cases (t : Fin steps) (s : Fin (steps+1)) :
        s=t.castSucc ∨ s=t.succ ∨ r t.castSucc < r s ∨ r s < r t.succ := by
      by_cases h1 : s=t.castSucc
      · exact Or.inl h1
      by_cases h2 : s=t.succ
      · exact Or.inr (Or.inl h2)
      by_cases hst : s.val < t.val
      · exact Or.inr (Or.inr (Or.inl (r_anti hst)))
      · apply Or.inr ∘ Or.inr ∘ Or.inr
        apply r_anti
        change t.val+1 < s.val
        have hv1 : s.val ≠ t.val := fun he => h1 (Fin.ext he)
        have hv2 : s.val ≠ t.val+1 := fun he => h2 (Fin.ext he)
        omega
    let P : V → ℝ := fun v => match v with
      | none => 0
      | some (t,k) => if k=j then r t else 0
    let Q : V → ℝ := fun v => match v with
      | none => 0
      | some (t,k) => if k=next j then r t else 0
    let H : V → ℝ := fun v => match v with
      | none => 0
      | some (t,k) => if k=j then (r t)^2 else if k=next j then L*(r t)^2 else 0
    let sector : Set V := {v | v=none ∨ ∃ t, v=some (t,j) ∨ v=some (t,next j)}
    let cert (F : Finset V) := ∃ A B C : ℝ, ∀ v∈sector,
      0 ≤ H v - A*P v - B*Q v - C ∧
        (H v - A*P v - B*Q v - C=0 ↔ v∈F)
    have hne (t : Fin steps) : t.castSucc ≠ t.succ := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castSucc,Fin.val_succ] at hv
      omega
    have cap_cert : cert cap := by
      refine ⟨r (Fin.last steps),L*r (Fin.last steps),0,?_⟩
      intro v hv
      rcases hv with rfl | ⟨s,rfl | rfl⟩
      · simp [H,P,Q,cap]
      · have hl : r (Fin.last steps) ≤ r s := r_anti.antitone (Fin.le_last _)
        by_cases he : s=Fin.last steps
        · subst s
          simp [H,P,Q,cap,Ne.symm (hnxt j),pow_two]
        · have hlt : r (Fin.last steps) < r s :=
            r_anti (lt_of_le_of_ne (Fin.le_last s) he)
          have hp : 0 < r s * (r s-r (Fin.last steps)) :=
            mul_pos (hr _) (sub_pos.mpr hlt)
          have hm : some (s,j) ∉ cap := by simp [cap,he,hnxt,Ne.symm (hnxt j)]
          simp only [H,P,Q,ite_true,Ne.symm (hnxt j),ite_false,mul_zero,sub_zero]
          constructor
          · nlinarith
          · exact iff_of_false (by nlinarith) hm
      · have hl : r (Fin.last steps) ≤ r s := r_anti.antitone (Fin.le_last _)
        by_cases he : s=Fin.last steps
        · subst s
          simp [H,P,Q,cap,hnxt,pow_two,mul_assoc]
        · have hlt : r (Fin.last steps) < r s :=
            r_anti (lt_of_le_of_ne (Fin.le_last s) he)
          have hp : 0 < L * (r s * (r s-r (Fin.last steps))) :=
            mul_pos hL0 (mul_pos (hr _) (sub_pos.mpr hlt))
          have hm : some (s,next j) ∉ cap := by simp [cap,he,hnxt,Ne.symm (hnxt j)]
          simp only [H,P,Q,hnxt,ite_false,ite_true,mul_zero,sub_zero]
          constructor
          · nlinarith
          · exact iff_of_false (by nlinarith) hm
    have upper_cert (t : Fin steps) : cert (upper t) := by
      let a := r t.castSucc
      let b := r t.succ
      have ha := hr t.castSucc
      have hb := hr t.succ
      have hab : b<a := r_anti (by simp)
      have hg : L*b<a := band_gap t
      have hLb : b<L*b := by nlinarith
      refine ⟨a+L*b,L*(a+b),-(L*a*b),?_⟩
      intro v hv
      rcases hv with rfl | ⟨s,rfl | rfl⟩
      · simp only [H,P,Q,mul_zero,sub_zero,zero_sub,neg_neg]
        have hp : 0<L*a*b := mul_pos (mul_pos hL0 ha) hb
        exact ⟨hp.le,iff_of_false (ne_of_gt hp) (by simp [upper])⟩
      · have heq : H (some (s,j))-(a+L*b)*P (some (s,j))-
            (L*(a+b))*Q (some (s,j))- -(L*a*b) = (r s-a)*(r s-L*b) := by
          simp [H,P,Q,Ne.symm (hnxt j)]
          ring
        rw [heq]
        rcases band_cases t s with rfl | rfl | hs | hs
        · simp [a,upper]
        · have hp : 0 < (b-a)*(b-L*b) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
          exact ⟨hp.le,iff_of_false (ne_of_gt hp) (by simp [V,upper,Option.some.injEq,Prod.mk.injEq,hne,Ne.symm (hne t),hnxt,Ne.symm (hnxt j)])⟩
        · have hp : 0<(r s-a)*(r s-L*b) := mul_pos (by exact sub_pos.mpr hs) (by linarith)
          refine ⟨hp.le,iff_of_false (ne_of_gt hp) ?_⟩
          have h1 : s≠t.castSucc := fun he => by subst s; exact (lt_irrefl _ hs)
          simp [V,upper,Option.some.injEq,Prod.mk.injEq,hne,Ne.symm (hne t),h1,Ne.symm (hnxt j)]
        · have hp : 0<(r s-a)*(r s-L*b) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
          refine ⟨hp.le,iff_of_false (ne_of_gt hp) ?_⟩
          have h1 : s≠t.castSucc := fun he => by subst s; exact (not_lt_of_gt hab hs)
          simp [V,upper,Option.some.injEq,Prod.mk.injEq,hne,Ne.symm (hne t),h1,Ne.symm (hnxt j)]
      · have heq : H (some (s,next j))-(a+L*b)*P (some (s,next j))-
            (L*(a+b))*Q (some (s,next j))- -(L*a*b) = L*((r s-a)*(r s-b)) := by
          simp [H,P,Q,hnxt]
          ring
        rw [heq]
        rcases band_cases t s with rfl | rfl | hs | hs
        · simp [a,upper]
        · simp [b,upper]
        · have hp : 0<L*((r s-a)*(r s-b)) :=
            mul_pos hL0 (mul_pos (by exact sub_pos.mpr hs) (by linarith))
          refine ⟨hp.le,iff_of_false (ne_of_gt hp) ?_⟩
          have h1 : s≠t.castSucc := fun he => by subst s; exact (lt_irrefl _ hs)
          have h2 : s≠t.succ := fun he => by subst s; exact (not_lt_of_gt hab hs)
          simp [V,upper,Option.some.injEq,Prod.mk.injEq,hne,Ne.symm (hne t),h1,h2]
        · have hp : 0<L*((r s-a)*(r s-b)) :=
            mul_pos hL0 (mul_pos_of_neg_of_neg (by linarith) (by exact sub_neg.mpr hs))
          refine ⟨hp.le,iff_of_false (ne_of_gt hp) ?_⟩
          have h1 : s≠t.castSucc := fun he => by subst s; exact (not_lt_of_gt hab hs)
          have h2 : s≠t.succ := fun he => by subst s; exact (lt_irrefl _ hs)
          simp [V,upper,Option.some.injEq,Prod.mk.injEq,hne,Ne.symm (hne t),h1,h2]
    have lower_cert (t : Fin steps) : cert (lower t) := by
      let a := r t.castSucc
      let b := r t.succ
      have ha := hr t.castSucc
      have hb := hr t.succ
      have hab : b<a := r_anti (by simp)
      have hg : L*b<a := band_gap t
      have hLa : a<L*a := by nlinarith
      refine ⟨a+b,L*b+a,-(a*b),?_⟩
      intro v hv
      rcases hv with rfl | ⟨s,rfl | rfl⟩
      · simp only [H,P,Q,mul_zero,sub_zero,zero_sub,neg_neg]
        have hp : 0<a*b := mul_pos ha hb
        exact ⟨hp.le,iff_of_false (ne_of_gt hp) (by simp [lower])⟩
      · have heq : H (some (s,j))-(a+b)*P (some (s,j))-
            (L*b+a)*Q (some (s,j))- -(a*b) = (r s-a)*(r s-b) := by
          simp [H,P,Q,Ne.symm (hnxt j)]
          ring
        rw [heq]
        rcases band_cases t s with rfl | rfl | hs | hs
        · simp [a,lower]
        · simp [b,lower]
        · have hp : 0<(r s-a)*(r s-b) := mul_pos (by exact sub_pos.mpr hs) (by linarith)
          refine ⟨hp.le,iff_of_false (ne_of_gt hp) ?_⟩
          have h1 : s≠t.castSucc := fun he => by subst s; exact (lt_irrefl _ hs)
          have h2 : s≠t.succ := fun he => by subst s; exact (not_lt_of_gt hab hs)
          simp [V,lower,Option.some.injEq,Prod.mk.injEq,hne,Ne.symm (hne t),h1,h2]
        · have hp : 0<(r s-a)*(r s-b) := mul_pos_of_neg_of_neg (by linarith) (by exact sub_neg.mpr hs)
          refine ⟨hp.le,iff_of_false (ne_of_gt hp) ?_⟩
          have h1 : s≠t.castSucc := fun he => by subst s; exact (not_lt_of_gt hab hs)
          have h2 : s≠t.succ := fun he => by subst s; exact (lt_irrefl _ hs)
          simp [V,lower,Option.some.injEq,Prod.mk.injEq,hne,Ne.symm (hne t),h1,h2]
      · have heq : H (some (s,next j))-(a+b)*P (some (s,next j))-
            (L*b+a)*Q (some (s,next j))- -(a*b) = (r s-b)*(L*r s-a) := by
          simp [H,P,Q,hnxt]
          ring
        rw [heq]
        rcases band_cases t s with rfl | rfl | hs | hs
        · have hp : 0 < (a-b)*(L*a-a) := mul_pos (by linarith) (by linarith)
          exact ⟨hp.le,iff_of_false (ne_of_gt hp) (by simp [V,lower,Option.some.injEq,Prod.mk.injEq,hne,Ne.symm (hne t),hnxt])⟩
        · simp [b,lower]
        · have hp : 0<(r s-b)*(L*r s-a) := mul_pos (by linarith) (by nlinarith)
          refine ⟨hp.le,iff_of_false (ne_of_gt hp) ?_⟩
          have h2 : s≠t.succ := fun he => by subst s; exact (not_lt_of_gt hab hs)
          simp [V,lower,Option.some.injEq,Prod.mk.injEq,hne,Ne.symm (hne t),h2,hnxt]
        · have hp : 0<(r s-b)*(L*r s-a) := mul_pos_of_neg_of_neg (by exact sub_neg.mpr hs) (by nlinarith)
          refine ⟨hp.le,iff_of_false (ne_of_gt hp) ?_⟩
          have h2 : s≠t.succ := fun he => by subst s; exact (lt_irrefl _ hs)
          simp [V,lower,Option.some.injEq,Prod.mk.injEq,hne,Ne.symm (hne t),h2,hnxt]
    have offS (z : RealizationPoint K) (hz : ∀ k, coord z k=q k) (v : V) (hv : v∉sector) :
        z.weight v=0 := by
      cases v with
      | none => exact False.elim (hv (Or.inl rfl))
      | some p =>
        rcases p with ⟨t,k⟩
        apply off_sector z hz
        · intro he
          subst k
          exact hv (Or.inr ⟨t,Or.inl rfl⟩)
        · intro he
          subst k
          exact hv (Or.inr ⟨t,Or.inr rfl⟩)
    have moment (z : RealizationPoint K) (k : Fin n) :
        (∑ v : V, (match v with | none => 0 | some (t,i) => if i=k then r t else 0)*z.weight v)=coord z k := by
      rw [Fintype.sum_option]
      simp only [zero_mul,zero_add,add_zero,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro t _
      simp only [ite_mul,zero_mul]
      rw [Finset.sum_ite_eq']
      simp
    have gap_sum (z : RealizationPoint K) (hz : ∀ k, coord z k=q k) (A B C : ℝ) :
        (∑ v, (H v-A*P v-B*Q v-C)*z.weight v) =
        (∑ v,H v*z.weight v)-A*q j-B*q (next j)-C := by
      simp only [sub_mul,Finset.sum_sub_distrib]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_weights, mul_one, moment, moment, hz, hz]
    have cert_nonneg (z : RealizationPoint K) (hz : ∀ k, coord z k=q k)
        (F : Finset V) (A B C : ℝ)
        (hc : ∀ v∈sector, 0 ≤ H v-A*P v-B*Q v-C ∧
          (H v-A*P v-B*Q v-C=0 ↔ v∈F)) (v : V) :
        0 ≤ (H v-A*P v-B*Q v-C)*z.weight v := by
      by_cases hv : v∈sector
      · exact mul_nonneg (hc v hv).1 (z.nonneg v)
      · rw [offS z hz v hv,mul_zero]
    have cert_eq (z : RealizationPoint K) (hz : ∀ k, coord z k=q k)
        (F : Finset V) (hs : supported z F) (A B C : ℝ)
        (hc : ∀ v∈sector, 0 ≤ H v-A*P v-B*Q v-C ∧
          (H v-A*P v-B*Q v-C=0 ↔ v∈F)) :
        (∑ v,H v*z.weight v)=A*q j+B*q (next j)+C := by
      have hh : (∑ v,(H v-A*P v-B*Q v-C)*z.weight v)=0 := by
        apply Finset.sum_eq_zero
        intro v _
        by_cases hv : v∈sector
        · by_cases hf : v∈F
          · rw [(hc v hv).2.mpr hf,zero_mul]
          · rw [hs v hf,mul_zero]
        · rw [offS z hz v hv,mul_zero]
      rw [gap_sum z hz] at hh
      linarith
    have supported_cert (z : RealizationPoint K) (hz : ∀ k, coord z k=q k) :
        ∃ F : Finset V, supported z F ∧ cert F := by
      rcases shape z hz with hs | ⟨t,hs⟩ | ⟨t,hs⟩
      · exact ⟨cap,hs,cap_cert⟩
      · exact ⟨upper t,hs,upper_cert t⟩
      · exact ⟨lower t,hs,lower_cert t⟩
    -- Comparing both supporting planes forces equal lifted moments, so the
    -- competing point has no weight outside the first point's triangle.
    have transport_support (F : Finset V) (hF : cert F) (hxs : supported x F) :
        supported y F := by
      obtain ⟨A,B,C,hc⟩ := hF
      obtain ⟨G,hys,D,E,F',hc'⟩ := supported_cert y hy
      have hexp := cert_eq x hx F hxs A B C hc
      have heyp := cert_eq y hy G hys D E F' hc'
      have hxy : (∑ v,H v*x.weight v) ≤ ∑ v,H v*y.weight v := by
        have hh := Finset.sum_nonneg (s := Finset.univ) (fun v _ => cert_nonneg y hy F A B C hc v)
        rw [gap_sum y hy] at hh
        linarith
      have hyx : (∑ v,H v*y.weight v) ≤ ∑ v,H v*x.weight v := by
        have hh := Finset.sum_nonneg (s := Finset.univ) (fun v _ => cert_nonneg x hx G D E F' hc' v)
        rw [gap_sum x hx] at hh
        linarith
      have heh := le_antisymm hxy hyx
      have hzero : (∑ v,(H v-A*P v-B*Q v-C)*y.weight v)=0 := by
        rw [gap_sum y hy,← heh,hexp]
        ring
      intro v hv
      by_cases hvS : v∈sector
      · have hh := (Finset.sum_eq_zero_iff_of_nonneg
            (fun v _ => cert_nonneg y hy F A B C hc v)).mp hzero v (Finset.mem_univ _)
        exact (mul_eq_zero.mp hh).resolve_left (fun he => hv ((hc v hvS).2.mp he))
      · exact offS y hy v hvS
    have tri_sum (z : RealizationPoint K) (a b c : V)
        (hab : a≠b) (hac : a≠c) (hbc : b≠c) (hs : supported z {a,b,c}) (f : V → ℝ) :
        (∑ v,f v*z.weight v)=f a*z.weight a+f b*z.weight b+f c*z.weight c := by
      have hh : (∑ v∈({a,b,c} : Finset V),f v*z.weight v) = ∑ v,f v*z.weight v :=
        Finset.sum_subset (Finset.subset_univ _) (by
          intro v _ hv
          rw [hs v hv,mul_zero])
      simpa [hab,hac,hbc,add_assoc] using hh.symm
    have tri_inj (a b c : V) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
        (hlin : ∀ U T W : ℝ, U+T+W=0 → P a*U+P b*T+P c*W=0 →
          Q a*U+Q b*T+Q c*W=0 → U=0 ∧ T=0 ∧ W=0)
        (hxs : supported x {a,b,c}) (hys : supported y {a,b,c}) : y=x := by
      have hxt := tri_sum x a b c hab hac hbc hxs (fun _ => 1)
      have hyt := tri_sum y a b c hab hac hbc hys (fun _ => 1)
      simp only [one_mul] at hxt hyt
      rw [sum_weights] at hxt hyt
      have hxp := tri_sum x a b c hab hac hbc hxs P
      have hyp := tri_sum y a b c hab hac hbc hys P
      have hxq := tri_sum x a b c hab hac hbc hxs Q
      have hyq := tri_sum y a b c hab hac hbc hys Q
      rw [moment x j,hx] at hxp
      rw [moment y j,hy] at hyp
      rw [moment x (next j),hx] at hxq
      rw [moment y (next j),hy] at hyq
      obtain ⟨ha,hb,hc⟩ := hlin (y.weight a-x.weight a) (y.weight b-x.weight b)
        (y.weight c-x.weight c) (by linarith only [hxt,hyt])
        (by nlinarith only [hxp,hyp]) (by nlinarith only [hxq,hyq])
      apply RealizationPoint.ext
      funext v
      by_cases hv : v∈({a,b,c} : Finset V)
      · simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact sub_eq_zero.mp ha
        · exact sub_eq_zero.mp hb
        · exact sub_eq_zero.mp hc
      · rw [hxs v hv,hys v hv]
    rcases shape x hx with hxs | ⟨t,hxs⟩ | ⟨t,hxs⟩
    · have hys := transport_support cap cap_cert hxs
      apply tri_inj none (some (Fin.last steps,j)) (some (Fin.last steps,next j))
        (by simp) (by simp) (by simpa [V,Option.some.injEq,Prod.mk.injEq] using Ne.symm (hnxt j))
        ?_ hxs hys
      intro U T W ht hp hq'
      simp only [P,Q,ite_true,hnxt,Ne.symm (hnxt j),ite_false,zero_mul,zero_add,add_zero] at hp hq'
      have hT := (mul_eq_zero.mp hp).resolve_left (ne_of_gt (hr _))
      have hW := (mul_eq_zero.mp hq').resolve_left (ne_of_gt (hr _))
      exact ⟨by linarith,hT,hW⟩
    · have hys := transport_support (upper t) (upper_cert t) hxs
      apply tri_inj (some (t.castSucc,j)) (some (t.castSucc,next j)) (some (t.succ,next j))
        (by simpa [V,Option.some.injEq,Prod.mk.injEq] using Ne.symm (hnxt j))
        (by simp [V,Option.some.injEq,Prod.mk.injEq,hne])
        (by simpa [V,Option.some.injEq,Prod.mk.injEq] using hne t) ?_ hxs hys
      intro U T W ht hp hq'
      simp only [P,Q,ite_true,hnxt,Ne.symm (hnxt j),ite_false,zero_mul,zero_add,add_zero] at hp hq'
      have hU := (mul_eq_zero.mp hp).resolve_left (ne_of_gt (hr _))
      have hh : (r t.castSucc-r t.succ)*T=0 := by
        linear_combination hq' - r t.succ * ht + r t.succ * hU
      have hT := (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (ne_of_gt (r_anti (show t.castSucc<t.succ by simp))))
      exact ⟨hU,hT,by linarith⟩
    · have hys := transport_support (lower t) (lower_cert t) hxs
      apply tri_inj (some (t.castSucc,j)) (some (t.succ,j)) (some (t.succ,next j))
        (by simpa [V,Option.some.injEq,Prod.mk.injEq] using hne t)
        (by simp [V,Option.some.injEq,Prod.mk.injEq,hne])
        (by simpa [V,Option.some.injEq,Prod.mk.injEq] using Ne.symm (hnxt j)) ?_ hxs hys
      intro U T W ht hp hq'
      simp only [P,Q,ite_true,hnxt,Ne.symm (hnxt j),ite_false,zero_mul,zero_add,add_zero] at hp hq'
      have hW := (mul_eq_zero.mp hq').resolve_left (ne_of_gt (hr _))
      have hh : (r t.castSucc-r t.succ)*U=0 := by
        linear_combination hp - r t.succ * ht + r t.succ * hW
      have hU := (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (ne_of_gt (r_anti (show t.castSucc<t.succ by simp))))
      exact ⟨hU,by linarith,hW⟩

end CurveComplex.FiniteArcDisk
