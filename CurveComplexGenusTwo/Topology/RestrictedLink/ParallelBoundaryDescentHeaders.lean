import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
import CurveComplexGenusTwo.Topology.ArcStraightening
namespace CurveComplex.HyperellipticModel
open Set Schoenflies
set_option maxHeartbeats 2000000
theorem parallel_family_inside_face_boundary {I : Type} [DecidableEq I] (F : Finset I) (r : I → Set Plane)
    (p q x : Plane) (harc : ∀ i ∈ F, IsArcBetween (r i) p q)
    (hmeet : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → r i ∩ r j = {p, q})
    (hx : ∀ i ∈ F, x ∉ r i)
    (i j : I) (hi : i ∈ F) (hj : j ∈ F) (hij : i ≠ j)
    (hxi : x ∈ inside (r i ∪ r j)) :
    ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧
      IsComplementComponent (⋃ k ∈ F, r k) (inside (r a ∪ r b)) ∧
      x ∈ inside (r a ∪ r b) ∧ frontier (inside (r a ∪ r b)) = r a ∪ r b := by
  classical
  have arcconn {P : Set Plane} {a b : Plane} (hP : IsArcBetween P a b) :
    IsConnected (P \ {a, b}) := by
  
    obtain ⟨f, hf, hi, hPimage, hf0, hf1⟩ := hP
    have he : P \ {a, b} = f '' Ioo (0 : ℝ) 1 := by
      ext x
      constructor
      · rintro ⟨hxP, hxends⟩
        rw [← hPimage] at hxP
        obtain ⟨t, ht, rfl⟩ := hxP
        have ht0 : t ≠ 0 := by
          intro h; subst t
          exact hxends (by simp [hf0])
        have ht1 : t ≠ 1 := by
          intro h; subst t
          exact hxends (by simp [hf1])
        exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        have htc : t ∈ unitInterval := ⟨ht.1.le, ht.2.le⟩
        refine ⟨hPimage ▸ ⟨t, htc, rfl⟩, ?_⟩
        intro h
        have hend : f t = a ∨ f t = b := by simpa using h
        rcases hend with h | h
        · have heq := hi htc (by norm_num : (0 : ℝ) ∈ unitInterval) (h.trans hf0.symm)
          exact (ne_of_gt ht.1) heq
        · have heq := hi htc (by norm_num : (1 : ℝ) ∈ unitInterval) (h.trans hf1.symm)
          exact (ne_of_lt ht.2) heq
    rw [he]
    exact (isConnected_Ioo (by norm_num : (0 : ℝ) < 1)).image f
      (hf.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩))
  have region {C : Set Plane} (hC : IsJordanCurve C) :
    IsComplementComponent C (inside C) := by
  
    have hs := jordan_curve_theorem hC
    refine ⟨hs.isConnected_inside.nonempty, hs.isConnected_inside, inside_subset_compl, ?_⟩
    intro V hV hsub hVc
    apply Subset.antisymm
    · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_inside
      · obtain ⟨x, hx⟩ := hs.isConnected_inside.nonempty
        exact ⟨x, hsub hx, hx⟩
      · intro x hx
        rw [(IsRegionOf.inside C).closure_eq hs] at hx
        rcases hx.1 with hi | hc
        · exact hi
        · exact False.elim (hVc hx.2 hc)
    · exact hsub
  have jordan : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → IsJordanCurve (r a ∪ r b) := by
    intro a ha b hb hab
    apply isJordanCurve_union (harc a ha) (harc b hb)
    intro z hza hzb
    have hz : z ∈ ({p, q} : Set Plane) := hmeet a ha b hb hab ▸ ⟨hza, hzb⟩
    simpa using hz
  let candidates : I → I → Finset I := fun a b => F.filter
    (fun k => ((r k \ {p, q}) ∩ inside (r a ∪ r b)).Nonempty)
  have descend : ∀ n : ℕ, ∀ a ∈ F, ∀ b ∈ F, a ≠ b →
      (candidates a b).card = n → x ∈ inside (r a ∪ r b) →
      ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧
        IsComplementComponent (⋃ k ∈ F, r k) (inside (r a ∪ r b)) ∧
        x ∈ inside (r a ∪ r b) ∧ frontier (inside (r a ∪ r b)) = r a ∪ r b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha b hb hab hn hxin
      have hJ := jordan a ha b hb hab
      have hs := jordan_curve_theorem hJ
      by_cases hempty : candidates a b = ∅
      · have hdis : Disjoint (inside (r a ∪ r b)) (⋃ k ∈ F, r k) := by
          apply Set.disjoint_left.mpr
          intro z hzI hzG
          obtain ⟨k, hzK⟩ := Set.mem_iUnion.mp hzG
          obtain ⟨hkF, hzK⟩ := Set.mem_iUnion.mp hzK
          have hzends : z ∉ ({p, q} : Set Plane) := by
            intro hz
            rcases (by simpa using hz : z = p ∨ z = q) with rfl | rfl
            · exact inside_subset_compl hzI (Or.inl (harc a ha).left_mem)
            · exact inside_subset_compl hzI (Or.inl (harc a ha).right_mem)
          have hkC : k ∈ candidates a b := Finset.mem_filter.mpr ⟨hkF, z, ⟨hzK, hzends⟩, hzI⟩
          simpa [hempty] using hkC
        refine ⟨a, ha, b, hb, hab, ?_, hxin, hs.frontier_inside⟩
        apply complementComponent_of_graph_enlargement (region hJ) _ hdis
        intro z hz
        rcases hz with hz | hz
        · exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, hz⟩⟩
        · exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hz⟩⟩
      · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨hkF, y, hyK, hyI⟩ := Finset.mem_filter.mp hk
        have hka : k ≠ a := by
          intro he; subst k
          exact inside_subset_compl hyI (Or.inl hyK.1)
        have hkb : k ≠ b := by
          intro he; subst k
          exact inside_subset_compl hyI (Or.inr hyK.1)
        have hkdis : r k \ {p, q} ⊆ (r a ∪ r b)ᶜ := by
          intro z hz hzg
          rcases hzg with hza | hzb
          · exact hz.2 (hmeet k hkF a ha hka ▸ ⟨hz.1, hza⟩)
          · exact hz.2 (hmeet k hkF b hb hkb ▸ ⟨hz.1, hzb⟩)
        have hkinside : r k \ {p, q} ⊆ inside (r a ∪ r b) := by
          apply (arcconn (harc k hkF)).isPreconnected.subset_of_closure_inter_subset hs.isOpen_inside
          · exact ⟨y, hyK, hyI⟩
          · intro z hz
            rw [(IsRegionOf.inside (r a ∪ r b)).closure_eq hs] at hz
            rcases hz.1 with hzI | hzC
            · exact hzI
            · exact False.elim (hkdis hz.2 hzC)
        have hcut : IsCutPair (r a ∪ r b) p q (r a) (r b) :=
          ⟨harc a ha, harc b hb, rfl, hmeet a ha b hb hab⟩
        obtain ⟨hcover, _, _, _, _, _, _, _, _, _⟩ :=
          general_crosscut_arbitrary_of_endpoints hJ (harc k hkF) hcut hkinside
        have hxK : x ∈ inside (r a ∪ r b) \ r k := ⟨hxin, hx k hkF⟩
        rw [hcover] at hxK
        have child : ∀ c ∈ F, c ≠ k →
            inside (r c ∪ r k) ⊆ inside (r a ∪ r b) →
            x ∈ inside (r c ∪ r k) →
            ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧
              IsComplementComponent (⋃ k ∈ F, r k) (inside (r a ∪ r b)) ∧
              x ∈ inside (r a ∪ r b) ∧ frontier (inside (r a ∪ r b)) = r a ∪ r b := by
          intro c hc hck hsub hxchild
          have hcsub : candidates c k ⊆ candidates a b := by
            intro z hz
            obtain ⟨hzF, t, htZ, htC⟩ := Finset.mem_filter.mp hz
            exact Finset.mem_filter.mpr ⟨hzF, t, htZ, hsub htC⟩
          have hknot : k ∉ candidates c k := by
            intro hz
            obtain ⟨_, t, htK, htC⟩ := Finset.mem_filter.mp hz
            exact inside_subset_compl htC (Or.inr htK.1)
          have hlt : (candidates c k).card < n := by
            rw [← hn]
            exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
              ⟨hcsub, fun he => hknot (he ▸ hk)⟩)
          exact ih _ hlt c hc k hkF hck rfl hxchild
        rcases hxK with hxA | hxB
        · apply child a ha hka.symm _ hxA
          intro z hz
          have hz' : z ∈ inside (r a ∪ r b) \ r k := hcover.symm ▸ Or.inl hz
          exact hz'.1
        · apply child b hb hkb.symm _ hxB
          intro z hz
          have hz' : z ∈ inside (r a ∪ r b) \ r k := hcover.symm ▸ Or.inr hz
          exact hz'.1
  exact descend _ i hi j hj hij rfl hxi

end CurveComplex.HyperellipticModel
