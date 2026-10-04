import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalFamilyEmptyBigon
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalSupportingSubdisk

open Set Topology Schoenflies CurveComplex Bornology

/-- The actual finite compact contact minimum gives a family-empty bigon whose
open disk avoids every horizontal grid fiber. No disk-emptiness certificate. -/
theorem actual_horizontal_positive_count_has_grid_family_empty_bigon
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hfinite : {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.Finite)
    (hcount : 0<{t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.ncard)
    (htrans : ∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) → q 1=c+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 1=c+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
    : ∃ (k : ℤ) (r s : ℝ), r<s ∧ G r 1=c+(k:ℝ)*T ∧ G s 1=c+(k:ℝ)*T ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
        (⋃ j : ℤ,range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ∧
      (∀ (i : ℤ) (t : ℝ),Plane.mk t (c+(i:ℝ)*T) ∉
        inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) := by
  classical
  let L := ⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))
  let E := L ∩ {z : Plane | ∃ i : ℤ, z 1=c+(i:ℝ)*T}
  let C := fun r s : ℝ => (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  let Cand := fun (k : ℤ) (r s : ℝ) => r<s ∧ G r 1=c+(k:ℝ)*T ∧ G s 1=c+(k:ℝ)*T ∧
    IsJordanCurve (C r s) ∧ Disjoint (inside (C r s)) L
  let count := fun r s : ℝ => (E ∩ closure (inside (C r s))).ncard
  let Q : ℕ → Prop := fun n => ∃ k r s, Cand k r s ∧ count r s=n
  have hex : ∃ n,Q n := by
    obtain ⟨k,r,s,hrs,hr,hs,hJ,hno,he⟩ :=
      actual_horizontal_positive_count_has_family_empty_bigon G hG T c hT hp hc hfinite hcount htrans
    exact ⟨count r s,k,r,s,⟨hrs,hr,hs,hJ,he⟩,rfl⟩
  obtain ⟨k,r,s,hcand,hn⟩ := Nat.find_spec hex
  obtain ⟨hrs,hr,hs,hJ,he⟩ := hcand
  have hmin (i : ℤ) (a b : ℝ) (hab : Cand i a b) : count r s ≤ count a b := by
    rw [hn]
    exact Nat.find_min' hex ⟨i,a,b,hab,rfl⟩
  refine ⟨k,r,s,hrs,hr,hs,hJ,he,?_⟩
  intro i t ht
  by_cases hik : i=k
  · subst i
    have hGL : range G ⊆ L := by
      rintro z ⟨u,rfl⟩
      refine mem_iUnion.mpr ⟨0,u,?_⟩
      ext q
      fin_cases q <;> simp [Plane.mk]
    have hcompact : IsCompact (closure (inside (C r s))) :=
      (jordan_curve_theorem hJ).isBounded_inside.isCompact_closure
    have hEf : (E ∩ closure (inside (C r s))).Finite :=
      actual_horizontal_full_family_grid_contacts_finite_in_compact G T c hT hp hfinite _ hcompact
    obtain ⟨a,b,hra,hab,hbs,ha0,hb0,hD,hboundary,p,hpends,hpD⟩ :=
      supporting_horizontal_fiber_entering_empty_bigon_has_actual_subdisk G hG (c+(k:ℝ)*T) r s
        hrs hr hs hJ (he.mono_right hGL) t ht
    have hpC : p∈C r s := by
      rcases hpends with hh|hh
      · rw [hh]; exact Or.inl ⟨r,⟨le_rfl,hrs.le⟩,rfl⟩
      · rw [mem_singleton_iff.mp hh]; exact Or.inl ⟨s,⟨hrs.le,le_rfl⟩,rfl⟩
    have hpE : p∈E := by
      rcases hpends with hh|hh
      · rw [hh]; exact ⟨hGL ⟨r,rfl⟩,k,hr⟩
      · rw [mem_singleton_iff.mp hh]; exact ⟨hGL ⟨s,rfl⟩,k,hs⟩
    have hlt := jordan_subdisk_contact_count_strict _ _ E hJ hD hboundary hEf p hpE hpC hpD
    have hsub := (jordan_subdisk_of_boundary_in_closed_disk _ _ hJ hD hboundary).1
    have hDe : Disjoint (inside (C a b)) L := he.mono_left hsub
    have hle := hmin k a b ⟨hab,ha0,hb0,hD,hDe⟩
    exact not_lt_of_ge hle hlt
  ·
    have hcc : c+(i:ℝ)*T≠c+(k:ℝ)*T := by
      intro hh
      have hcast : (i:ℝ)=(k:ℝ) := by nlinarith
      exact hik (Int.cast_injective hcast)
    have hGL : range G ⊆ L := by
      rintro z ⟨u,rfl⟩
      refine mem_iUnion.mpr ⟨0,u,?_⟩
      ext q
      fin_cases q <;> simp [Plane.mk]
    have hcompact : IsCompact (closure (inside (C r s))) :=
      (jordan_curve_theorem hJ).isBounded_inside.isCompact_closure
    have hEf : (E ∩ closure (inside (C r s))).Finite :=
      actual_horizontal_full_family_grid_contacts_finite_in_compact G T c hT hp hfinite _ hcompact
    have hcontact : G r∈E := ⟨hGL ⟨r,rfl⟩,k,hr⟩
    obtain ⟨a,b,hra,hab,hbs,ha0,hb0,hD,hcl,hDe,hlt⟩ :=
      shifted_horizontal_fiber_actual_subdisk_strict_contacts G hG (c+(k:ℝ)*T) (c+(i:ℝ)*T) r s
        hrs hr hs hcc hJ L E hGL he hEf hcontact t ht
    have hboundary : C a b ⊆ closure (inside (C r s)) := by
      have hDc : C a b ⊆ closure (inside (C a b)) := by
        intro z hz
        exact frontier_subset_closure ((jordan_curve_theorem hD).frontier_inside.symm ▸ hz)
      exact hDc.trans hcl
    have hle := hmin i a b ⟨hab,ha0,hb0,hD,hDe⟩
    exact not_lt_of_ge hle hlt


#print axioms actual_horizontal_positive_count_has_grid_family_empty_bigon
