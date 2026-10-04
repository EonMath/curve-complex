import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalLatticeSeparatedBigon

open Set Topology Schoenflies CurveComplex

/-- Source transversality rules out extra supporting-fiber contacts on the
constructed grid-free boundary arc, so the actual full-lattice-separated bigon
is short. No shortness or clean-boundary certificate supplied. -/
theorem actual_horizontal_positive_count_has_short_separated_bigon
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
    : ∃ (k : ℤ) (r s : ℝ), r<s ∧ s<r+T ∧ G r 1=c+(k:ℝ)*T ∧ G s 1=c+(k:ℝ)*T ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
        (⋃ j : ℤ,range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ∧
      (∀ u∈Ioo r s,G u 1≠c+(k:ℝ)*T) ∧
      Pairwise (fun i j : ℤ×ℤ => Disjoint
        (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) ∧
      (∀ (i : ℤ) (t : ℝ),Plane.mk t (c+(i:ℝ)*T) ∉
        inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) := by
  obtain ⟨k,r,s,hrs,hr,hs,hJ,he,hsep,hgrid⟩ :=
    actual_horizontal_positive_count_has_lattice_separated_bigon G hG T c hT hp hc hfinite hcount htrans
  let C := (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  let d := c+(k:ℝ)*T
  have hnoInside : ∀ z∈inside C,z 1≠d := by
    intro z hz hd
    have hzEq : z=Plane.mk (z 0) d := by
      ext q
      fin_cases q
      · rfl
      · exact hd
    rw [hzEq] at hz
    exact hgrid k _ hz
  have hSides := (jordan_curve_theorem hJ).isConnected_inside.isPreconnected.subset_or_subset
    (isOpen_lt (show Continuous (fun z : Plane => z 1) by fun_prop) continuous_const)
    (isOpen_lt continuous_const (show Continuous (fun z : Plane => z 1) by fun_prop))
    (show Disjoint {z : Plane | z 1<d} {z : Plane | d<z 1} from
      disjoint_left.mpr (fun z hl hu => lt_asymm (show z 1<d from hl) (show d<z 1 from hu)))
    (show inside C⊆{z : Plane | z 1<d}∪{z : Plane | d<z 1} from
      fun z hz => lt_or_gt_of_ne (hnoInside z hz))
  have hCcl : C⊆closure (inside C) := by
    intro z hz
    exact frontier_subset_closure ((jordan_curve_theorem hJ).frontier_inside.symm ▸ hz)
  have hBoundarySide : (∀ z∈C,z 1≤d) ∨ (∀ z∈C,d≤z 1) := by
    rcases hSides with hl | hu
    · left
      have hClosed : IsClosed {z : Plane | z 1≤d} := isClosed_le (by fun_prop) continuous_const
      have hCl : closure (inside C)⊆{z : Plane | z 1≤d} :=
        closure_minimal (fun z hz => (show z 1<d from hl hz).le) hClosed
      exact fun z hz => hCl (hCcl hz)
    · right
      have hClosed : IsClosed {z : Plane | d≤z 1} := isClosed_le continuous_const (by fun_prop)
      have hCl : closure (inside C)⊆{z : Plane | d≤z 1} :=
        closure_minimal (fun z hz => (show d<z 1 from hu hz).le) hClosed
      exact fun z hz => hCl (hCcl hz)
  have hArcSide : (∀ x∈Icc r s,G x 1≤d) ∨ (∀ x∈Icc r s,d≤G x 1) := by
    rcases hBoundarySide with hl | hu
    · exact Or.inl (fun x hx => hl _ (Or.inl ⟨x,hx,rfl⟩))
    · exact Or.inr (fun x hx => hu _ (Or.inl ⟨x,hx,rfl⟩))
  have hBase (x : ℝ) : G x∈⋃ j : ℤ,range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) := by
    refine mem_iUnion.mpr ⟨0,x,?_⟩
    ext q
    fin_cases q <;> simp [Plane.mk]
  have hno : ∀ u∈Ioo r s,G u 1≠d := by
    intro u hu hd
    obtain ⟨U,V,hqU,h,hU,hV,hZero,hAxes⟩ := htrans (G u) k (hBase u) hd
    exact actual_horizontal_transverse_family_no_internal_halfplane_touch
      G hG T r s u d hT hp hc hu hd hArcSide U V hqU h hU hV hZero hAxes
  obtain ⟨U,V,hqU,h,hU,hV,hZero,hAxes⟩ := htrans (G r) k (hBase r) hr
  obtain ⟨v,hv,hvContact⟩ := actual_horizontal_periodic_transverse_contact_has_interior_return
    G hG T d r hT hp hc hr U V hqU h hU hV hZero hAxes
  have hshort : s<r+T := by
    by_contra hn
    exact hno v ⟨hv.1,hv.2.trans_le (le_of_not_gt hn)⟩ hvContact
  exact ⟨k,r,s,hrs,hshort,hr,hs,hJ,he,hno,hsep,hgrid⟩

#print axioms actual_horizontal_positive_count_has_short_separated_bigon
