import CurveComplexGenusTwo.Topology.InternalCollar
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Connected.LocallyPathConnected
open Set Metric unitInterval Filter Topology
namespace Schoenflies

/-- A convergent path assembled on dyadic time intervals. Avoidance is proved
by eventual stabilization at each positive time, not by closedness of the complement. -/
theorem continuous_approach_of_dyadic_paths
    {P : Set Plane} {a : Plane} {z : ℕ → Plane}
    (q : ∀ n, Path (z (n+1)) (z n))
    (hq : ∀ n t, dist (q n t) a ≤ (1/2 : ℝ)^n ∧ q n t ∉ P) :
    ∃ g : Path a (z 0), (∀ t : I, t ≠ 0 → g t ∉ P) ∧
      ∀ n (t : I), (1/2 : ℝ)^(n+1) ≤ t → (t : ℝ) ≤ (1/2 : ℝ)^n →
        g t = (q n).extend (2*(t : ℝ)/((1/2 : ℝ)^n)-1) := by
  classical
  let r := fun n : ℕ => (1/2 : ℝ)^n
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrs (n : ℕ) : r (n+1) = r n / 2 := by dsimp [r]; rw [pow_succ]; ring
  have hrmono : Antitone r := antitone_nat_of_succ_le (fun n => by rw [hrs]; linarith [hr n])
  have hr1 (n : ℕ) : r n ≤ 1 := by simpa [r] using hrmono (Nat.zero_le n)
  have hqe (n : ℕ) (t : ℝ) : dist ((q n).extend t) a ≤ r n ∧ (q n).extend t ∉ P := by
    obtain ⟨s, hs⟩ : (q n).extend t ∈ range (q n) := by
      rw [← Path.extend_range]; exact ⟨t, rfl⟩
    simpa only [hs] using hq n s
  have hz (n : ℕ) : dist (z n) a ≤ r n ∧ z n ∉ P := by
    simpa using hqe n 1
  let d : ℕ → ℝ → Plane := fun n t =>
    if t ≤ r n then (q n).extend (2*t/r n-1) - z n else 0
  have hdcont (n : ℕ) : Continuous (d n) := by
    apply Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
    intro t ht
    change t = r n at ht
    have heq : 2*t/r n-1 = 1 := by rw [ht]; field_simp [ne_of_gt (hr n)]; ring
    simp [heq]
  have hdnorm (n : ℕ) (t : ℝ) : ‖d n t‖ ≤ 2*r n := by
    dsimp [d]
    split_ifs with h
    · rw [← dist_eq_norm]
      have htri := dist_triangle ((q n).extend (2*t/r n-1)) a (z n)
      rw [dist_comm a (z n)] at htri
      linarith [(hqe n (2*t/r n-1)).1, (hz n).1]
    · simp only [norm_zero]; positivity
  have hsum : Summable (fun n => 2*r n) := (summable_geometric_two).mul_left 2
  have hdsum (t : ℝ) : Summable (fun n => d n t) := hsum.of_norm_bounded (fun n => hdnorm n t)
  let F := fun (n : ℕ) (t : ℝ) => z 0 + ∑ i ∈ Finset.range n, d i t
  have hFstep (n : ℕ) (t : ℝ) : F (n+1) t = F n t + d n t := by
    dsimp [F]; rw [Finset.sum_range_succ]; abel
  have hFsmall (n : ℕ) : ∀ t, t ≤ r n → F n t = z n := by
    induction n with
    | zero => intro t ht; simp [F]
    | succ n ih =>
      intro t ht
      have htn : t ≤ r n := ht.trans (hrmono (Nat.le_succ n))
      have harg : 2*t/r n-1 ≤ 0 := by
        have ht' : t ≤ r n / 2 := by rwa [hrs] at ht
        have : 2*t/r n ≤ 1 := (div_le_iff₀ (hr n)).2 (by linarith)
        linarith
      rw [hFstep, ih t htn]
      simp only [d, ite_eq_left htn, Path.extend_of_le_zero _ harg]
      abel
  have hFavoid (n : ℕ) (t : ℝ) : F n t ∉ P := by
    induction n with
    | zero => simpa [F] using (hz 0).2
    | succ n ih =>
      rw [hFstep]
      by_cases ht : t ≤ r n
      · rw [hFsmall n t ht]
        have heq : z n + ((q n).extend (2*t/r n-1) - z n) = (q n).extend (2*t/r n-1) := by abel
        simpa only [d, ite_eq_left ht, heq] using (hqe n (2*t/r n-1)).2
      · simpa only [d, ite_eq_right ht, add_zero] using ih
  let g := fun t : ℝ => z 0 + ∑' n, d n t
  have hg : Continuous g := continuous_const.add (continuous_tsum hdcont hsum hdnorm)
  have hrlim : Tendsto r atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hzlim : Tendsto z atTop (𝓝 a) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hz n).1) hrlim
  have hg0 : g 0 = a := by
    have hlim : Tendsto (fun n => F n 0) atTop (𝓝 (g 0)) :=
      tendsto_const_nhds.add (hdsum 0).tendsto_sum_tsum_nat
    have hzero : (fun n => F n 0) = z := funext (fun n => hFsmall n 0 (hr n).le)
    rw [hzero] at hlim
    exact tendsto_nhds_unique hlim hzlim
  have hstable (t : ℝ) (m : ℕ) (ht : r m < t) : g t = F m t := by
    dsimp [g, F]
    congr 1
    apply tsum_eq_sum
    intro n hn
    have hmn : m ≤ n := Nat.le_of_not_lt (by simpa using hn)
    have hnt : ¬ t ≤ r n := not_le.mpr ((hrmono hmn).trans_lt ht)
    simp [d, hnt]
  have hgavoid (t : ℝ) (ht : 0 < t) : g t ∉ P := by
    obtain ⟨m, hm⟩ := (hrlim.eventually (gt_mem_nhds ht)).exists
    rw [hstable t m hm]
    exact hFavoid m t
  have hg1 : g 1 = z 0 := by
    have hd1 (n : ℕ) : d n 1 = 0 := by
      by_cases h : 1 ≤ r n
      · have heq : r n = 1 := le_antisymm (hr1 n) h
        norm_num [d, heq]
      · simp [d, h]
    simp [g, hd1]
  refine ⟨Path.ofLine hg.continuousOn hg0 hg1, ?_, ?_⟩
  · intro t ht
    exact hgavoid t (lt_of_le_of_ne t.property.1 (fun heq => ht (Subtype.ext heq.symm)))
  · intro n t hlow hhigh
    have hsumtail : g t = F (n+1) t := by
      dsimp [g, F]
      congr 1
      apply tsum_eq_sum
      intro j hj
      have hnj : n+1 ≤ j := Nat.le_of_not_lt (by simpa using hj)
      have hjt : r j ≤ (t : ℝ) := (hrmono hnj).trans hlow
      by_cases hle : (t : ℝ) ≤ r j
      · have heq : (t : ℝ) = r j := le_antisymm hle hjt
        have harg : 2*(t : ℝ)/r j-1 = 1 := by rw [heq]; field_simp [ne_of_gt (hr j)]; ring
        simp [d, hle, harg]
      · simp [d, hle]
    change g t = _
    rw [hsumtail, hFstep, hFsmall n t hhigh]
    simp only [d, r, ite_eq_left hhigh]
    abel

end Schoenflies
#print axioms Schoenflies.continuous_approach_of_dyadic_paths
namespace Schoenflies
/-- A compatible shrinking chain produces a continuous endpoint path.
The path is not asserted injective. -/
theorem continuous_approach_of_null_chain
    {P : Set Plane} {a : Plane} (U : ℕ → Set Plane)
    (hU : ∀ n, IsOpen (U n) ∧ IsConnected (U n) ∧
      U n ⊆ ball a (1 / ((n : ℝ)+1)) \ P)
    (hover : ∀ n, (U n ∩ U (n+1)).Nonempty) :
    ∃ u : Plane, u ∉ P ∧ ∃ g : Path a u, ∀ t : I, t ≠ 0 → g t ∉ P := by
  classical
  let V := fun n : ℕ => ⋃ k : ℕ, U (n+k)
  have hVo (n : ℕ) : IsOpen (V n) := isOpen_iUnion (fun k => (hU (n+k)).1)
  have hVc (n : ℕ) : IsConnected (V n) := by
    apply IsConnected.iUnion_of_chain (fun k => (hU (n+k)).2.1)
    intro k
    simpa only [Order.succ_eq_add_one, Nat.add_assoc] using hover (n+k)
  have hVmono {n m : ℕ} (hnm : n ≤ m) : V m ⊆ V n := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨m-n+k, ?_⟩
    have heq : n+(m-n+k) = m+k := by omega
    simpa only [heq] using hk
  have hVb (n : ℕ) : V n ⊆ ball a (1 / ((n : ℝ)+1)) \ P := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    have hb := (hU (n+k)).2.2 hk
    refine ⟨?_, hb.2⟩
    change dist x a < 1 / ((n : ℝ)+1)
    apply lt_of_lt_of_le (show dist x a < 1 / (((n+k : ℕ) : ℝ)+1) from hb.1)
    apply one_div_le_one_div_of_le (by positivity)
    simp only [Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  let z := fun n => (hVc (2^n)).nonempty.some
  have hz (n : ℕ) : z n ∈ V (2^n) := (hVc (2^n)).nonempty.some_mem
  have hpath (n : ℕ) : JoinedIn (V (2^n)) (z (n+1)) (z n) := by
    apply ((hVo (2^n)).isConnected_iff_isPathConnected.mp (hVc (2^n))).joinedIn
    · exact hVmono (pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (Nat.le_succ n)) (hz (n+1))
    · exact hz n
  let q := fun n => (hpath n).somePath
  have hq (n : ℕ) (t : I) : dist (q n t) a ≤ (1/2:ℝ)^n ∧ q n t ∉ P := by
    have hb := hVb (2^n) ((hpath n).somePath_mem t)
    refine ⟨hb.1.le.trans ?_, hb.2⟩
    have hpow : (0:ℝ) < 2^n := by positivity
    have heq : (1/2:ℝ)^n = 1/(2^n) := by rw [one_div_pow]
    rw [heq]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact one_div_le_one_div_of_le hpow (by linarith)
  obtain ⟨g, hg, _⟩ := continuous_approach_of_dyadic_paths q hq
  exact ⟨z 0, (hVb (2^0) (hz 0)).2, g, hg⟩

/-- Continuous endpoint access for an arbitrary embedded planar arc. -/
theorem continuous_endpoint_access
    {Q : Set Plane} {x y : Plane} (hQ : IsArcBetween Q x y) :
    ∃ u : Plane, u ∉ Q ∧ ∃ g : Path x u, ∀ t : I, t ≠ 0 → g t ∉ Q := by
  obtain ⟨f, hf, hi, hfr, hf0, _⟩ := hQ
  obtain ⟨U, hU, hover⟩ := endpoint_compatible_open_regions hf hi
  obtain ⟨u, hu, g, hg⟩ := continuous_approach_of_null_chain U hU hover
  refine ⟨u, by simpa only [hfr] using hu, g.cast hf0.symm rfl, ?_⟩
  intro t ht
  change g t ∉ Q
  rw [← hfr]
  exact hg t ht
end Schoenflies
#print axioms Schoenflies.continuous_approach_of_null_chain
#print axioms Schoenflies.continuous_endpoint_access
namespace Schoenflies
/-- A compact set avoiding the limiting endpoint meets only finitely many arcs
of a null sequence. This supplies the last-contact index for infinite loop erasure. -/
theorem finite_contacts_of_null_sequence
    {a : Plane} {B : Set Plane} (hB : IsCompact B) (ha : a ∉ B)
    {A : ℕ → Set Plane}
    (hnull : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, A n ⊆ ball a ε) :
    {n : ℕ | (B ∩ A n).Nonempty}.Finite := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hB.isClosed.isOpen_compl a ha
  obtain ⟨N, hN⟩ := hnull ε hε
  apply (Set.finite_lt_nat N).subset
  intro n hn
  by_contra h
  obtain ⟨p, hpB, hpA⟩ := hn
  exact hball (hN n (not_lt.mp h) hpA) hpB

/-- Last contact with a null sequence, for a nonempty contact set. -/
theorem exists_last_contact_of_null_sequence
    {a : Plane} {B : Set Plane} (hB : IsCompact B) (ha : a ∉ B)
    {A : ℕ → Set Plane}
    (hnull : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, A n ⊆ ball a ε)
    (hne : ∃ n, (B ∩ A n).Nonempty) :
    ∃ m : ℕ, (B ∩ A m).Nonempty ∧ ∀ n > m, Disjoint B (A n) := by
  obtain ⟨m, hm, hmax⟩ := (finite_contacts_of_null_sequence hB ha hnull).bddAbove.exists_isGreatest_of_nonempty hne
  refine ⟨m, hm, ?_⟩
  intro n hn
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra h
  have hne' : (B ∩ A n).Nonempty := Set.nonempty_iff_ne_empty.mpr h
  exact (not_le.mpr hn) (hmax hne')

/-- The first contact of one arc with another freezes an initial subarc meeting
 the second arc only at the contact point. -/
theorem first_contact_split
    {B A : Set Plane} {c b d e : Plane}
    (hB : IsArcBetween B c b) (hA : IsArcBetween A d e)
    (hc : c ∉ A) (hmeet : (B ∩ A).Nonempty) (he : e ∉ B) :
    ∃ w : Plane, ∃ C D : Set Plane,
      C ⊆ B ∧ D ⊆ A ∧ IsArcBetween C c w ∧ IsArcBetween D w e ∧
      C ∩ A = {w} := by
  obtain ⟨f, hf, hi, hfr, hf0, hf1⟩ := hB
  let S : Set I := {t | f t ∈ A}
  have hcF : Continuous (fun t : I => f t) := continuousOn_iff_continuous_domRestrict.mp hf
  have hSclosed : IsClosed S := hA.isArc.isCompact.isClosed.preimage hcF
  have hSne : S.Nonempty := by
    obtain ⟨p, hpB, hpA⟩ := hmeet
    rw [← hfr] at hpB
    obtain ⟨t, ht, rfl⟩ := hpB
    exact ⟨⟨t, ht⟩, hpA⟩
  obtain ⟨t, htS, htmin⟩ := hSclosed.isCompact.exists_isLeast hSne
  have htA : f t ∈ A := htS
  have ht0 : 0 < (t : ℝ) := by
    by_contra h
    have heq : (t : ℝ) = 0 := le_antisymm (not_lt.mp h) t.property.1
    exact hc (by simpa [heq, hf0] using htA)
  let C := f '' Icc 0 (t : ℝ)
  have hC : IsArcBetween C c (f t) := by
    rw [← hf0]
    simpa [C, uIcc_of_le ht0.le] using
      isArcBetween_subarc_of_injOn_I hf hi (by simp) t.property (ne_of_lt ht0)
  have hCB : C ⊆ B := by
    rw [← hfr]
    exact image_mono (fun s hs => ⟨hs.1, hs.2.trans t.property.2⟩)
  have hCA : C ∩ A = {f t} := by
    apply Subset.antisymm
    · rintro p ⟨⟨s, hs, rfl⟩, hsA⟩
      have hsI : s ∈ I := ⟨hs.1, hs.2.trans t.property.2⟩
      have hts : (t : ℝ) ≤ s := htmin (show (⟨s, hsI⟩ : I) ∈ S from hsA)
      have heq : s = t := le_antisymm hs.2 hts
      simp [heq]
    · rintro p rfl
      exact ⟨hC.right_mem, htA⟩
  have hne : f t ≠ e := by
    intro h
    exact he (h ▸ hCB hC.right_mem)
  obtain ⟨D, hDA, hD⟩ := hA.isArc.exists_isArcBetween_subset htA hA.right_mem hne
  exact ⟨f t, C, D, hCB, hDA, hC, hD, hCA⟩
end Schoenflies
#print axioms Schoenflies.finite_contacts_of_null_sequence
#print axioms Schoenflies.exists_last_contact_of_null_sequence
#print axioms Schoenflies.first_contact_split
namespace Schoenflies
/-- One frozen-prefix extension step for a null chain of arcs. -/
theorem null_arc_chain_step
    {a : Plane} {z : ℕ → Plane} {A : ℕ → Set Plane}
    (hA : ∀ n, IsArcBetween (A n) (z n) (z (n+1)))
    (hnull : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, A n ⊆ ball a ε)
    {k : ℕ} {c : Plane} {B : Set Plane}
    (hB : IsArcBetween B c (z (k+1))) (ha : a ∉ B)
    (hc : ∀ n > k, c ∉ A n) :
    ∃ m : ℕ, k < m ∧ ∃ w : Plane, ∃ C D : Set Plane,
      C ⊆ B ∧ D ⊆ A m ∧ IsArcBetween C c w ∧
      IsArcBetween D w (z (m+1)) ∧ C ∩ A m = {w} ∧
      (∀ n > m, Disjoint B (A n)) ∧ (∀ n > m, w ∉ A n) := by
  obtain ⟨m, hm, hlast⟩ := exists_last_contact_of_null_sequence hB.isArc.isCompact ha hnull
    ⟨k+1, z (k+1), hB.right_mem, (hA (k+1)).left_mem⟩
  have hkm : k < m := by
    by_contra h
    have hmle : m < k+1 := by omega
    exact Set.disjoint_left.mp (hlast (k+1) hmle) hB.right_mem (hA (k+1)).left_mem
  have he : z (m+1) ∉ B := by
    intro hz
    exact Set.disjoint_left.mp (hlast (m+1) (Nat.lt_succ_self m)) hz (hA (m+1)).left_mem
  obtain ⟨w, C, D, hCB, hDA, hC, hD, hCA⟩ := first_contact_split hB (hA m) (hc m hkm) hm he
  refine ⟨m, hkm, w, C, D, hCB, hDA, hC, hD, hCA, hlast, ?_⟩
  intro n hn hw
  exact Set.disjoint_left.mp (hlast n hn) (hCB hC.right_mem) hw
end Schoenflies
#print axioms Schoenflies.null_arc_chain_step

namespace Schoenflies
/-- A null chain of simple arcs in the complement, with distinct adjacent endpoints. -/
theorem simple_arc_chain_of_null_chain
    {P : Set Plane} {a : Plane} (U : ℕ → Set Plane)
    (hU : ∀ n, IsOpen (U n) ∧ IsConnected (U n) ∧
      U n ⊆ ball a (1 / ((n : ℝ)+1)) \ P)
    (hover : ∀ n, (U n ∩ U (n+1)).Nonempty) :
    ∃ z : ℕ → Plane, ∃ A : ℕ → Set Plane,
      ∀ n, IsArcBetween (A n) (z n) (z (n+1)) ∧
        A n ⊆ closedBall a ((1/2 : ℝ)^n) \ P := by
  classical
  let V := fun n : ℕ => ⋃ k : ℕ, U (n+k)
  have hVo (n : ℕ) : IsOpen (V n) := isOpen_iUnion (fun k => (hU (n+k)).1)
  have hVc (n : ℕ) : IsConnected (V n) := by
    apply IsConnected.iUnion_of_chain (fun k => (hU (n+k)).2.1)
    intro k
    simpa only [Order.succ_eq_add_one, Nat.add_assoc] using hover (n+k)
  have hVmono {n m : ℕ} (hnm : n ≤ m) : V m ⊆ V n := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨m-n+k, ?_⟩
    have heq : n+(m-n+k) = m+k := by omega
    simpa only [heq] using hk
  have hVb (n : ℕ) : V n ⊆ ball a (1 / ((n : ℝ)+1)) \ P := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    have hb := (hU (n+k)).2.2 hk
    refine ⟨?_, hb.2⟩
    change dist x a < 1 / ((n : ℝ)+1)
    apply lt_of_lt_of_le (show dist x a < 1 / (((n+k : ℕ) : ℝ)+1) from hb.1)
    apply one_div_le_one_div_of_le (by positivity)
    simp only [Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hnext (n : ℕ) (p : Plane) : ∃ q ∈ V (2^(n+1)), q ≠ p := by
    obtain ⟨w, hw⟩ := (hVc (2^(n+1))).nonempty
    obtain ⟨q, hq, hqp⟩ := mem_closure_iff.mp ((dense_compl_singleton p) w)
      (V (2^(n+1))) (hVo (2^(n+1))) hw
    exact ⟨q, hq, hqp⟩
  let z : ℕ → Plane := Nat.rec (hVc (2^0)).nonempty.some
    (fun n p => Classical.choose (hnext n p))
  have hz (n : ℕ) : z n ∈ V (2^n) := by
    cases n with
    | zero => exact (hVc (2^0)).nonempty.some_mem
    | succ n => exact (Classical.choose_spec (hnext n (z n))).1
  have hne (n : ℕ) : z n ≠ z (n+1) :=
    (Classical.choose_spec (hnext n (z n))).2.symm
  have hex (n : ℕ) : ∃ A : Set Plane, A ⊆ V (2^n) ∧ IsArcBetween A (z n) (z (n+1)) := by
    have hzn := hVmono (pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (Nat.le_succ n)) (hz (n+1))
    obtain ⟨A, hAV, _, hA⟩ := exists_simple_arc_of_isPreconnected
      (hVo (2^n)) (hVc (2^n)).isPreconnected (hz n) hzn (hne n)
    exact ⟨A, hAV, hA⟩
  let A := fun n => Classical.choose (hex n)
  refine ⟨z, A, ?_⟩
  intro n
  refine ⟨(Classical.choose_spec (hex n)).2, ?_⟩
  intro x hx
  have hb := hVb (2^n) ((Classical.choose_spec (hex n)).1 hx)
  refine ⟨?_, hb.2⟩
  change dist x a ≤ (1/2 : ℝ)^n
  apply (show dist x a < 1 / (((2^n : ℕ) : ℝ)+1) from hb.1).le.trans
  rw [one_div_pow]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)
end Schoenflies
#print axioms Schoenflies.simple_arc_chain_of_null_chain
namespace Schoenflies
/-- Infinite last-contact loop erasure. The retained arcs have only their
prescribed adjacent endpoint intersections; all nonadjacent arcs are disjoint. -/
theorem erase_null_arc_chain
    {P : Set Plane} {a : Plane} (ha : a ∈ P)
    {z : ℕ → Plane} {A : ℕ → Set Plane}
    (hA : ∀ n, IsArcBetween (A n) (z n) (z (n+1)) ∧
      A n ⊆ closedBall a ((1/2 : ℝ)^n) \ P) :
    ∃ c : ℕ → Plane, ∃ C : ℕ → Set Plane, c 0 = z 0 ∧
      (∀ n, IsArcBetween (C n) (c n) (c (n+1)) ∧
        C n ⊆ closedBall a ((1/2 : ℝ)^n) \ P) ∧
      (∀ n, C n ∩ C (n+1) ⊆ {c (n+1)}) ∧
      ∀ n m, n+1 < m → Disjoint (C n) (C m) := by
  classical
  have haA (n : ℕ) : a ∉ A n := fun h => (hA n).2 h |>.2 ha
  have hnull : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, A n ⊆ ball a ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).eventually (gt_mem_nhds hε))
    refine ⟨N, ?_⟩
    intro n hn x hx
    exact ((hA n).2 hx).1.trans_lt (hN n hn)
  let T := {s : ℕ × Plane × Set Plane //
    s.2.2 ⊆ A s.1 ∧ IsArcBetween s.2.2 s.2.1 (z (s.1+1)) ∧
    ∀ n > s.1, s.2.1 ∉ A n}
  have hbase : ∃ s : T, s.val.2.1 = z 0 := by
    have haz : a ≠ z 0 := fun h => haA 0 (h ▸ (hA 0).1.left_mem)
    obtain ⟨k, hk, hlast⟩ := exists_last_contact_of_null_sequence
      (isCompact_singleton (x := z 0)) (by simpa using haz) hnull
      ⟨0, z 0, rfl, (hA 0).1.left_mem⟩
    have hzA : z 0 ∈ A k := by
      obtain ⟨p, hp, hpA⟩ := hk
      simpa only [Set.mem_singleton_iff.mp hp] using hpA
    have hne : z 0 ≠ z (k+1) := by
      intro heq
      exact Set.disjoint_left.mp (hlast (k+1) (Nat.lt_succ_self k))
        (show z 0 ∈ ({z 0} : Set Plane) from rfl) (heq ▸ (hA (k+1)).1.left_mem)
    obtain ⟨B, hBA, hB⟩ := (hA k).1.isArc.exists_isArcBetween_subset hzA (hA k).1.right_mem hne
    refine ⟨⟨(k, z 0, B), hBA, hB, ?_⟩, rfl⟩
    intro n hn hz
    exact Set.disjoint_left.mp (hlast n hn) rfl hz
  have hstep : ∀ s : T, ∃ t : T, s.val.1 < t.val.1 ∧ ∃ B : Set Plane,
      B ⊆ s.val.2.2 ∧ IsArcBetween B s.val.2.1 t.val.2.1 ∧
      B ∩ A t.val.1 = {t.val.2.1} ∧
      ∀ n > t.val.1, Disjoint s.val.2.2 (A n) := by
    intro s
    obtain ⟨m, hm, w, C, D, hCB, hDA, hC, hD, hCA, hlast, hw⟩ :=
      null_arc_chain_step (fun n => (hA n).1) hnull s.property.2.1
        (fun h => haA s.val.1 (s.property.1 h)) s.property.2.2
    exact ⟨⟨(m,w,D), hDA, hD, hw⟩, hm, C, hCB, hC, hCA, hlast⟩
  let states : ℕ → T := Nat.rec (Classical.choose hbase) (fun _ s => Classical.choose (hstep s))
  let k := fun n => (states n).val.1
  let c := fun n => (states n).val.2.1
  let C := fun n => Classical.choose (Classical.choose_spec (hstep (states n))).2
  have hk (n : ℕ) : k n < k (n+1) := (Classical.choose_spec (hstep (states n))).1
  have hC (n : ℕ) : C n ⊆ (states n).val.2.2 ∧
      IsArcBetween (C n) (c n) (c (n+1)) ∧ C n ∩ A (k (n+1)) = {c (n+1)} ∧
      ∀ j > k (n+1), Disjoint (states n).val.2.2 (A j) :=
    Classical.choose_spec (Classical.choose_spec (hstep (states n))).2
  have hCA (n : ℕ) : C n ⊆ A (k n) := (hC n).1.trans (states n).property.1
  have hkn (n : ℕ) : n ≤ k n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => have := hk n; omega
  have hkm : StrictMono k := strictMono_nat_of_lt_succ hk
  have hrmono : Antitone (fun n => (1/2 : ℝ)^n) :=
    antitone_nat_of_succ_le (fun n => by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) n])
  refine ⟨c, C, Classical.choose_spec hbase, ?_, ?_, ?_⟩
  · intro n
    refine ⟨(hC n).2.1, ?_⟩
    intro p hp
    have hb := (hA (k n)).2 (hCA n hp)
    exact ⟨hb.1.trans (hrmono (hkn n)), hb.2⟩
  · intro n p hp
    rw [← (hC n).2.2.1]
    exact ⟨hp.1, hCA (n+1) hp.2⟩
  · intro n m hnm
    apply ((hC n).2.2.2 (k m) (hkm hnm)).mono (hC n).1 (hCA m)
end Schoenflies
#print axioms Schoenflies.erase_null_arc_chain
namespace Schoenflies
/-- A simple null chain assembles to an injective endpoint-access arc. -/
theorem access_arc_of_simple_null_chain
    {P : Set Plane} {a : Plane} (ha : a ∈ P)
    {c : ℕ → Plane} {C : ℕ → Set Plane}
    (hC : ∀ n, IsArcBetween (C n) (c n) (c (n+1)) ∧
      C n ⊆ closedBall a ((1/2 : ℝ)^n) \ P)
    (hadj : ∀ n, C n ∩ C (n+1) ⊆ {c (n+1)})
    (hfar : ∀ n m, n+1 < m → Disjoint (C n) (C m)) :
    ∃ E : Set Plane, IsArcBetween E a (c 0) ∧ c 0 ∉ P ∧ E \ {a} ⊆ Pᶜ := by
  classical
  have hex (n : ℕ) : ∃ q : Path (c (n+1)) (c n), Function.Injective q ∧ range q = C n := by
    obtain ⟨f, hf, hi, hfr, hf0, hf1⟩ := (hC n).1.reverse
    refine ⟨Path.ofLine hf hf0 hf1, ?_, ?_⟩
    · intro s t hst
      apply Subtype.ext
      exact hi s.property t.property hst
    · ext x
      constructor
      · rintro ⟨t, rfl⟩
        rw [← hfr]
        exact ⟨t, t.property, rfl⟩
      · intro hx
        rw [← hfr] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        exact ⟨⟨t,ht⟩, rfl⟩
  let q := fun n => Classical.choose (hex n)
  have hqi (n : ℕ) : Function.Injective (q n) := (Classical.choose_spec (hex n)).1
  have hqr (n : ℕ) : range (q n) = C n := (Classical.choose_spec (hex n)).2
  have hq (n : ℕ) (t : I) : dist (q n t) a ≤ (1/2 : ℝ)^n ∧ q n t ∉ P := by
    have hm : q n t ∈ C n := hqr n ▸ mem_range_self t
    exact (hC n).2 hm
  obtain ⟨g, hgavoid, hgform⟩ := continuous_approach_of_dyadic_paths q hq
  let r := fun n : ℕ => (1/2 : ℝ)^n
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrs (n : ℕ) : r (n+1) = r n / 2 := by dsimp [r]; rw [pow_succ]; ring
  have hcover (t : I) (ht : t ≠ 0) : ∃ n : ℕ, r (n+1) < (t : ℝ) ∧ (t : ℝ) ≤ r n := by
    have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (fun heq => ht (Subtype.ext heq.symm))
    have he : ∃ n : ℕ, r n < (t : ℝ) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).eventually (gt_mem_nhds htpos)).exists
    have hn0 : Nat.find he ≠ 0 := by
      intro hn
      have hh := Nat.find_spec he
      rw [hn] at hh
      have : (1 : ℝ) < t := by simpa [r] using hh
      linarith [t.property.2]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨n, ?_, ?_⟩
    · simpa only [hn] using Nat.find_spec he
    · by_contra h
      have hh := Nat.find_min' he (not_le.mp h)
      omega
  have hparam (n : ℕ) (t : I) (hlow : r (n+1) < (t : ℝ)) (hhigh : (t : ℝ) ≤ r n) :
      0 < 2*(t : ℝ)/r n-1 ∧ 2*(t : ℝ)/r n-1 ≤ 1 := by
    rw [hrs] at hlow
    have hh : 1 < 2*(t : ℝ)/r n := (lt_div_iff₀ (hr n)).2 (by linarith)
    have hh' : 2*(t : ℝ)/r n ≤ 2 := (div_le_iff₀ (hr n)).2 (by linarith)
    constructor <;> linarith
  have hloc (n : ℕ) (t : I) (hlow : r (n+1) < (t : ℝ)) (hhigh : (t : ℝ) ≤ r n) :
      g t ∈ C n ∧ g t ≠ c (n+1) := by
    have hp := hparam n t hlow hhigh
    have hform := hgform n t hlow.le hhigh
    rw [Path.extend_apply _ ⟨hp.1.le, hp.2⟩] at hform
    constructor
    · rw [hform, ← hqr n]
      exact mem_range_self _
    · intro heq
      have hvals : q n ⟨2*(t : ℝ)/r n-1, ⟨hp.1.le, hp.2⟩⟩ = q n 0 := by
        rw [← hform, heq, Path.source]
      have hp0 := congrArg Subtype.val (hqi n hvals)
      have : 2*(t : ℝ)/r n-1 = 0 := hp0
      linarith [hp.1]
  have hdifferent (n m : ℕ) (p : Plane) (hnm : n < m)
      (hpn : p ∈ C n) (hpm : p ∈ C m) (hne : p ≠ c (n+1)) : False := by
    by_cases hm : m = n+1
    · subst m
      exact hne (hadj n ⟨hpn, hpm⟩)
    · exact Set.disjoint_left.mp (hfar n m (by omega)) hpn hpm
  have hginj : Function.Injective g := by
    intro t s heq
    by_cases ht : t = 0
    · subst t
      by_contra hs
      exact hgavoid s (Ne.symm hs) (heq ▸ (show g 0 ∈ P by simpa using ha))
    by_cases hs : s = 0
    · subst s
      exact False.elim (hgavoid t ht (heq.symm ▸ (show g 0 ∈ P by simpa using ha)))
    obtain ⟨n, hnt, htn⟩ := hcover t ht
    obtain ⟨m, hms, hsm⟩ := hcover s hs
    have hlt := hloc n t hnt htn
    have hls := hloc m s hms hsm
    have hnm : n = m := by
      rcases lt_trichotomy n m with h | h | h
      · exact False.elim (hdifferent n m (g t) h hlt.1 (heq.symm ▸ hls.1) hlt.2)
      · exact h
      · exact False.elim (hdifferent m n (g s) h hls.1 (heq ▸ hlt.1) hls.2)
    subst m
    have hpt := hparam n t hnt htn
    have hps := hparam n s hms hsm
    rw [hgform n t hnt.le htn, hgform n s hms.le hsm,
      Path.extend_apply _ ⟨hpt.1.le, hpt.2⟩,
      Path.extend_apply _ ⟨hps.1.le, hps.2⟩] at heq
    have hv := congrArg Subtype.val (hqi n heq)
    change 2*(t : ℝ)/r n-1 = 2*(s : ℝ)/r n-1 at hv
    apply Subtype.ext
    have hh : 2*(t : ℝ)/r n = 2*(s : ℝ)/r n := by linarith
    have hh' := (div_left_inj' (ne_of_gt (hr n))).mp hh
    linarith
  refine ⟨range g, ?_, ((hC 0).2 (hC 0).1.left_mem).2, ?_⟩
  · refine ⟨g.extend, g.continuous_extend.continuousOn, ?_,
      g.image_extend_of_subset subset_rfl, g.extend_zero, g.extend_one⟩
    intro t ht s hs hts
    rw [Path.extend_apply _ ht, Path.extend_apply _ hs] at hts
    exact congrArg Subtype.val (hginj hts)
  · rintro p ⟨⟨t, rfl⟩, hp⟩
    apply hgavoid t
    intro ht
    subst t
    exact hp (by simpa using g.source)
end Schoenflies
#print axioms Schoenflies.access_arc_of_simple_null_chain
namespace Schoenflies
/-- Null-chain extraction, including continuous assembly and proved injectivity. -/
theorem access_arc_of_null_chain
    {P : Set Plane} {a : Plane} (ha : a ∈ P)
    (U : ℕ → Set Plane)
    (hU : ∀ n, IsOpen (U n) ∧ IsConnected (U n) ∧
      U n ⊆ ball a (1 / ((n : ℝ)+1)) \ P)
    (hover : ∀ n, (U n ∩ U (n+1)).Nonempty) :
    ∃ E : Set Plane, ∃ u : Plane,
      IsArcBetween E a u ∧ u ∉ P ∧ E \ {a} ⊆ Pᶜ := by
  obtain ⟨z, A, hA⟩ := simple_arc_chain_of_null_chain U hU hover
  obtain ⟨c, C, _, hC, hadj, hfar⟩ := erase_null_arc_chain ha hA
  obtain ⟨E, hE, hu, havoid⟩ := access_arc_of_simple_null_chain ha hC hadj hfar
  exact ⟨E, c 0, hE, hu, havoid⟩

/-- Endpoint accessibility for an arbitrary planar embedded arc. No tameness,
polygonality, smoothness, or endpoint accessibility hypothesis is imposed. -/
theorem endpoint_access_of_isArcBetween
    {Q : Set Plane} {x y : Plane} (hQ : IsArcBetween Q x y) :
    ∃ E : Set Plane, ∃ u : Plane,
      IsArcBetween E x u ∧ u ∉ Q ∧ E \ {x} ⊆ Qᶜ := by
  obtain ⟨f, hf, hi, hfr, hf0, _⟩ := hQ
  obtain ⟨U, hU, hover⟩ := endpoint_compatible_open_regions hf hi
  have hx : f 0 ∈ f '' I := ⟨0, by simp, rfl⟩
  simpa only [hfr, hf0] using access_arc_of_null_chain hx U hU hover
end Schoenflies
#print axioms Schoenflies.access_arc_of_null_chain
#print axioms Schoenflies.endpoint_access_of_isArcBetween
