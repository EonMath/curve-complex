import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.CountControlledChordAndTails

open Set Schoenflies
namespace CurveComplex

/-- Extract a regular entire arc from spatially separated regular tails and an
actual chord. All cardinality estimates concern the actual axis-contact sets. -/
theorem countCrosscutArcInSeparatedRegularTailsAndChord
    (L T D : Set Plane) (a u v b : Plane)
    (hL : IsArcBetween L a u) (hT : IsArcBetween T v b)
    (hau : a ≠ v) (hab : a ≠ b) (huv : u ≠ v)
    (ha0 : a 0 ≠ 0) (hu0 : u 0 ≠ 0) (hb0 : b 0 ≠ 0)
    (hLT : Disjoint L T)
    (hchordContacts : ∀ p ∈ segment ℝ u v, p 0=0 → p ∉ L ∧ p ∉ T)
    (hLf : (L ∩ {z : Plane | z 0=0}).Finite)
    (hTf : (T ∩ {z : Plane | z 0=0}).Finite)
    (hLreg : ∀ p ∈ L ∩ {z : Plane | z 0=0}, ∃ W : Set Plane,
      IsOpen W ∧ p ∈ W ∧ ∃ m : ℝ, ∀ z ∈ L ∩ W, z 1=p 1+m*z 0)
    (hTreg : ∀ p ∈ T ∩ {z : Plane | z 0=0}, ∃ W : Set Plane,
      IsOpen W ∧ p ∈ W ∧ ∃ m : ℝ, ∀ z ∈ T ∩ W, z 1=p 1+m*z 0)
    (hLD : L \ {a,b} ⊆ D) (hTD : T \ {a,b} ⊆ D)
    (hchordD : segment ℝ u v ⊆ D) (hD : IsOpen D) :
    ∃ C : Set Plane, IsArcBetween C a b ∧
      C ⊆ (L ∪ segment ℝ u v) ∪ T ∧ C \ {a,b} ⊆ D ∧
      (C ∩ {z : Plane | z 0 = 0}).Finite ∧
      (C ∩ {z : Plane | z 0 = 0}).ncard ≤
        (L ∩ {z : Plane | z 0=0}).ncard + (T ∩ {z : Plane | z 0=0}).ncard + 1 ∧
      ∀ p ∈ C ∩ {z : Plane | z 0 = 0},
        ∃ W : Set Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ D ∧
        ∃ m : ℝ, ∀ z ∈ W, (z ∈ C ↔ z 1 = p 1 + m*z 0) := by
  classical
  have hsegmentLine (x y p : Plane) (hx : x 0 ≠ 0)
      (hp : p ∈ segment ℝ x y) (hp0 : p 0 = 0) :
      ∃ m : ℝ, ∀ z ∈ segment ℝ x y, z 1 = p 1 + m * z 0 := by
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨s, hs, hsp⟩ := hp
    have hpcoord (i : Fin 2) : p i = (1-s) * x i + s * y i := by
      rw [← hsp]
      simp [AffineMap.lineMap_apply_module]
    have hxy : y 0 - x 0 ≠ 0 := by
      intro h
      have hh := hpcoord 0
      have hyx := sub_eq_zero.mp h
      rw [hyx, hp0] at hh
      exact hx (by nlinarith)
    refine ⟨(y 1 - x 1) / (y 0 - x 0), ?_⟩
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, htz⟩ := hz
    have hzcoord (i : Fin 2) : z i = (1-t) * x i + t * y i := by
      rw [← htz]
      simp [AffineMap.lineMap_apply_module]
    rw [hzcoord 0, hzcoord 1, hpcoord 1]
    have hh := hpcoord 0
    rw [hp0] at hh
    field_simp
    nlinarith [congrArg (fun a : ℝ => a * (y 1-x 1)) hh]
  have hsegmentSingleton (x y : Plane) (hx : x 0 ≠ 0) :
      (segment ℝ x y ∩ {z : Plane | z 0 = 0}).Subsingleton := by
    intro p hp q hq
    rw [segment_eq_image_lineMap] at hp hq
    obtain ⟨s, hs, hsp⟩ := hp.1
    obtain ⟨t, ht, htq⟩ := hq.1
    have hcoord : ∀ u : ℝ, (AffineMap.lineMap x y u) 0 =
        (1-u) * x 0 + u * y 0 := by
      intro u
      simp [AffineMap.lineMap_apply_module]
    have hps : (1-s) * x 0 + s * y 0 = 0 := by
      rw [← hcoord, hsp]; exact hp.2
    have hqt : (1-t) * x 0 + t * y 0 = 0 := by
      rw [← hcoord, htq]; exact hq.2
    have hxy : y 0 - x 0 ≠ 0 := by
      intro h
      have hh := sub_eq_zero.mp h
      rw [hh] at hps
      exact hx (by nlinarith)
    have hst : s = t := by
      have hh : (s-t) * (y 0-x 0) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hxy)
    rw [← hsp, ← htq, hst]
  obtain ⟨C0,hC0sub,hC0arc⟩ := exists_arc_in_union_of_arcs hL
    (isArcBetween_segment huv) hau
  obtain ⟨C,hCsub,hCarc⟩ := exists_arc_in_union_of_arcs hC0arc hT hab
  have hcover : C ⊆ (L ∪ segment ℝ u v) ∪ T :=
    hCsub.trans (union_subset_union hC0sub subset_rfl)
  let KL := L ∩ {z : Plane | z 0=0}
  let KT := T ∩ {z : Plane | z 0=0}
  let K := segment ℝ u v ∩ {z : Plane | z 0=0}
  have hKsub : K.Subsingleton := hsegmentSingleton u v hu0
  have hKf : K.Finite := hKsub.finite
  have hKcount : K.ncard ≤ 1 := (Set.ncard_le_one hKf).mpr
    (fun _ hp _ hq => hKsub hp hq)
  have hcontact : C ∩ {z : Plane | z 0=0} ⊆ (KL ∪ KT) ∪ K := by
    intro z hz
    rcases hcover hz.1 with (h | h) | h
    · exact Or.inl (Or.inl ⟨h,hz.2⟩)
    · exact Or.inr ⟨h,hz.2⟩
    · exact Or.inl (Or.inr ⟨h,hz.2⟩)
  have hfinite := (hLf.union hTf |>.union hKf).subset hcontact
  have hcount : (C ∩ {z : Plane | z 0=0}).ncard ≤ KL.ncard+KT.ncard+1 := by
    have hc := Set.ncard_le_ncard hcontact (hLf.union hTf |>.union hKf)
    have hc1 := Set.ncard_union_le (KL ∪ KT) K
    have hc2 := Set.ncard_union_le KL KT
    omega
  have hproper : C \ {a,b} ⊆ D := by
    intro z hz
    rcases hcover hz.1 with (hzL | hzChord) | hzT
    · exact hLD ⟨hzL,hz.2⟩
    · exact hchordD hzChord
    · exact hTD ⟨hzT,hz.2⟩
  refine ⟨C,hCarc,hcover,hproper,hfinite,hcount,?_⟩
  intro p hp
  have hp0 : p 0=0 := hp.2
  have hpa : p ≠ a := fun he => ha0 (he ▸ hp0)
  have hpb : p ≠ b := fun he => hb0 (he ▸ hp0)
  have hpD : p ∈ D := hproper ⟨hp.1,by
    rintro (he | he)
    · exact hpa he
    · exact hpb (Set.mem_singleton_iff.mp he)⟩
  have hlocal : ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ V ⊆ D ∧
      ∃ m : ℝ, ∀ z ∈ C ∩ V, z 1=p 1+m*z 0 := by
    rcases hcover hp.1 with (hpL | hpK) | hpT
    · obtain ⟨W,hWo,hpW,m,hm⟩ := hLreg p ⟨hpL,hp0⟩
      have hpnotT : p ∉ T := fun h => Set.disjoint_left.mp hLT hpL h
      have hpnotK : p ∉ segment ℝ u v := fun h => (hchordContacts p h hp0).1 hpL
      let V := (W ∩ (T ∪ segment ℝ u v)ᶜ) ∩ D
      refine ⟨V,(hWo.inter (hT.isArc.isCompact.union (isCompact_segment _ _)).isClosed.isOpen_compl).inter hD,
        ⟨⟨hpW,by rintro (h | h); exact hpnotT h; exact hpnotK h⟩,hpD⟩,
        fun z hz => hz.2,m,?_⟩
      intro z hz
      have hzL : z ∈ L := by
        rcases hcover hz.1 with (h | h) | h
        · exact h
        · exact False.elim (hz.2.1.2 (Or.inr h))
        · exact False.elim (hz.2.1.2 (Or.inl h))
      exact hm z ⟨hzL,hz.2.1.1⟩
    · obtain ⟨m,hm⟩ := hsegmentLine u v p hu0 hpK hp0
      have hpnotL := (hchordContacts p hpK hp0).1
      have hpnotT := (hchordContacts p hpK hp0).2
      let V := (L ∪ T)ᶜ ∩ D
      refine ⟨V,(hL.isArc.isCompact.union hT.isArc.isCompact).isClosed.isOpen_compl.inter hD,
        ⟨by rintro (h | h); exact hpnotL h; exact hpnotT h,hpD⟩,
        fun z hz => hz.2,m,?_⟩
      intro z hz
      have hzK : z ∈ segment ℝ u v := by
        rcases hcover hz.1 with (h | h) | h
        · exact False.elim (hz.2.1 (Or.inl h))
        · exact h
        · exact False.elim (hz.2.1 (Or.inr h))
      exact hm z hzK
    · obtain ⟨W,hWo,hpW,m,hm⟩ := hTreg p ⟨hpT,hp0⟩
      have hpnotL : p ∉ L := fun h => Set.disjoint_left.mp hLT h hpT
      have hpnotK : p ∉ segment ℝ u v := fun h => (hchordContacts p h hp0).2 hpT
      let V := (W ∩ (L ∪ segment ℝ u v)ᶜ) ∩ D
      refine ⟨V,(hWo.inter (hL.isArc.isCompact.union (isCompact_segment _ _)).isClosed.isOpen_compl).inter hD,
        ⟨⟨hpW,by rintro (h | h); exact hpnotL h; exact hpnotK h⟩,hpD⟩,
        fun z hz => hz.2,m,?_⟩
      intro z hz
      have hzT : z ∈ T := by
        rcases hcover hz.1 with (h | h) | h
        · exact False.elim (hz.2.1.2 (Or.inl h))
        · exact False.elim (hz.2.1.2 (Or.inr h))
        · exact h
      exact hm z ⟨hzT,hz.2.1.1⟩
  obtain ⟨V,hVo,hpV,hVD,m,hm⟩ := hlocal
  obtain ⟨W,hWo,hpW,hWV,hline⟩ := position_arc_local_affine hCarc hp.1 hpa hpb
    hVo hpV m (by intro z hz; simpa [hp0] using hm z hz)
  refine ⟨W,hWo,hpW,(fun z hz => hVD (hWV hz)),m,?_⟩
  intro z hz
  simpa [hp0] using hline z hz

end CurveComplex
