import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.TangentJordanHalfRegions
import Schoenflies.MatchedArc
import CurveComplexGenusTwo.Topology.CrosscutGlue

open Set Topology Schoenflies
namespace CurveComplex.HyperellipticModel

/-- Relative extensions of two Jordan boundaries glue when the closed regions
meet exactly along their common boundary. The full boundary map is retained. -/
theorem relative_two_jordan_region_filling
    {A B A' B' : Set Plane} {f g : Plane → Plane}
    (hA : IsJordanCurve A) (hB : IsJordanCurve B)
    (hA' : IsJordanCurve A') (hB' : IsJordanCurve B')
    (hf : IsHomeoOn f g (A ∪ B) (A' ∪ B'))
    (hfA : f '' A = A') (hfB : f '' B = B')
    (hmeet : closure (inside A) ∩ closure (inside B) = A ∩ B)
    (hmeet' : closure (inside A') ∩ closure (inside B') = A' ∩ B') :
    ∃ F G : Plane → Plane,
      IsHomeoOn F G (closure (inside A) ∪ closure (inside B))
        (closure (inside A') ∪ closure (inside B')) ∧
      EqOn F f (A ∪ B) := by
  have hfgA : IsHomeoOn f g A A' := hf.mono subset_union_left subset_union_left
    (fun x hx => hfA ▸ mem_image_of_mem f hx)
    (fun y hy => by
      obtain ⟨x,hx,rfl⟩ := hfA.symm ▸ hy
      simpa only [hf.invOn.1 (Or.inl hx)] using hx)
  have hfgB : IsHomeoOn f g B B' := hf.mono subset_union_right subset_union_right
    (fun x hx => hfB ▸ mem_image_of_mem f hx)
    (fun y hy => by
      obtain ⟨x,hx,rfl⟩ := hfB.symm ▸ hy
      simpa only [hf.invOn.1 (Or.inr hx)] using hx)
  obtain ⟨F₀,G₀,h₀,h₀eq⟩ := closed_interior_extension squareExtension hA hA' hfgA
  obtain ⟨F₁,G₁,h₁,h₁eq⟩ := closed_interior_extension squareExtension hB hB' hfgB
  have clA : closure (inside A) = A ∪ inside A := by
    rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem hA),union_comm]
  have clB : closure (inside B) = B ∪ inside B := by
    rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem hB),union_comm]
  have clA' : closure (inside A') = A' ∪ inside A' := by
    rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem hA'),union_comm]
  have clB' : closure (inside B') = B' ∪ inside B' := by
    rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem hB'),union_comm]
  have h₀' : IsHomeoOn F₀ G₀ (closure (inside A)) (closure (inside A')) := by
    simpa only [clA,clA'] using h₀
  have h₁' : IsHomeoOn F₁ G₁ (closure (inside B)) (closure (inside B')) := by
    simpa only [clB,clB'] using h₁
  have hagree : ∀ x ∈ closure (inside A) ∩ closure (inside B), F₀ x = F₁ x := by
    intro x hx
    rw [hmeet] at hx
    exact (h₀eq hx.1).trans (h₁eq hx.2).symm
  have himage : F₀ '' (closure (inside A) ∩ closure (inside B)) =
      closure (inside A') ∩ closure (inside B') := by
    rw [hmeet,hmeet']
    calc
      F₀ '' (A ∩ B) = f '' (A ∩ B) := (h₀eq.mono inter_subset_left).image_eq
      _ = (f '' A) ∩ (f '' B) := by
        apply subset_antisymm
        · rintro y ⟨x,hx,rfl⟩
          exact ⟨mem_image_of_mem f hx.1,mem_image_of_mem f hx.2⟩
        · rintro y ⟨⟨x,hx,rfl⟩,z,hz,he⟩
          have heq := hf.injOn (Or.inr hz) (Or.inl hx) he
          exact ⟨x,⟨hx,heq ▸ hz⟩,rfl⟩
      _ = A' ∩ B' := by rw [hfA,hfB]
  obtain ⟨F,G,hFG,hF₀,hF₁⟩ := CurveComplex.glue_closed_homeoOn
    isClosed_closure isClosed_closure isClosed_closure isClosed_closure h₀' h₁' hagree himage
  refine ⟨F,G,hFG,?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact (hF₀ x (clA.symm ▸ Or.inl hx)).trans (h₀eq hx)
  · exact (hF₁ x (clB.symm ▸ Or.inl hx)).trans (h₁eq hx)

/-- Glue prescribed maps on the three arcs of a Jordan triangle. -/
theorem three_arc_boundary_map
    {A B P A' B' P' : Set Plane} {p x y p' x' y' : Plane}
    (hA : IsArcBetween A p x) (hB : IsArcBetween B p y)
    (hP : IsArcBetween P x y)
    (hA' : IsArcBetween A' p' x') (hB' : IsArcBetween B' p' y')
    (hP' : IsArcBetween P' x' y')
    (hAP : A ∩ P = {x}) (hAB : A ∩ B = {p}) (hPB : P ∩ B = {y})
    (hAP' : A' ∩ P' = {x'}) (hAB' : A' ∩ B' = {p'}) (hPB' : P' ∩ B' = {y'})
    (a : ArcHomeo A A' p x p' x') (b : ArcHomeo B B' p y p' y')
    (c : ArcHomeo P P' x y x' y') :
    ∃ f g : Plane → Plane, IsHomeoOn f g (A ∪ P ∪ B) (A' ∪ P' ∪ B') ∧
      EqOn f a.toFun A ∧ EqOn f b.toFun B ∧ EqOn f c.toFun P := by
  have arcHomeo {K L : Set Plane} {u v u' v' : Plane}
      (a : ArcHomeo K L u v u' v') : IsHomeoOn a.toFun a.invFun K L :=
    ⟨a.mapsTo,a.mapsTo_invFun,a.continuousOn_toFun,a.continuousOn_invFun,
      a.leftInvOn,a.rightInvOn⟩
  have hac : ∀ z ∈ A ∩ P, a.toFun z = c.toFun z := by
    intro z hz
    have : z = x := mem_singleton_iff.mp (hAP ▸ hz)
    subst z
    exact a.map_right.trans c.map_left.symm
  have him : a.toFun '' (A ∩ P) = A' ∩ P' := by
    rw [hAP,hAP',image_singleton,a.map_right]
  obtain ⟨f₀,g₀,h₀,h₀a,h₀c⟩ := CurveComplex.glue_closed_homeoOn
    hA.isArc.isCompact.isClosed hP.isArc.isCompact.isClosed
    hA'.isArc.isCompact.isClosed hP'.isArc.isCompact.isClosed
    (arcHomeo a) (arcHomeo c) hac him
  have hmeet : (A ∪ P) ∩ B = {p,y} := by
    rw [union_inter_distrib_right,hAB,hPB]; rfl
  have hmeet' : (A' ∪ P') ∩ B' = {p',y'} := by
    rw [union_inter_distrib_right,hAB',hPB']; rfl
  have h₀p : f₀ p = p' := (h₀a p hA.left_mem).trans a.map_left
  have h₀y : f₀ y = y' := (h₀c y hP.right_mem).trans c.map_right
  have h₀b : ∀ z ∈ (A ∪ P) ∩ B, f₀ z = b.toFun z := by
    intro z hz
    have hz' : z = p ∨ z = y := by
      have hh : z ∈ ({p,y} : Set Plane) := hmeet ▸ hz
      simpa using hh
    rcases hz' with rfl | rfl
    · exact h₀p.trans b.map_left.symm
    · exact h₀y.trans b.map_right.symm
  have him₂ : f₀ '' ((A ∪ P) ∩ B) = (A' ∪ P') ∩ B' := by
    rw [hmeet,hmeet',image_pair,h₀p,h₀y]
  obtain ⟨f,g,hfg,hf₀,hfb⟩ := CurveComplex.glue_closed_homeoOn
    (hA.isArc.isCompact.isClosed.union hP.isArc.isCompact.isClosed)
    hB.isArc.isCompact.isClosed
    (hA'.isArc.isCompact.isClosed.union hP'.isArc.isCompact.isClosed)
    hB'.isArc.isCompact.isClosed h₀ (arcHomeo b) h₀b him₂
  exact ⟨f,g,hfg,fun z hz => (hf₀ z (Or.inl hz)).trans (h₀a z hz),
    fun z hz => hfb z hz,fun z hz => (hf₀ z (Or.inr hz)).trans (h₀c z hz)⟩

/-- Build both relative fillings from the five actual arcs. Their connector map
is chosen once, so the two filled maps agree on the entire overlap. -/
theorem two_triangle_region_homeomorphism
    (A B A' B' : Fin 2 → Set Plane) (P P' : Set Plane) (p x y p' x' y' : Plane)
    (hA : ∀ i, IsArcBetween (A i) p x) (hB : ∀ i, IsArcBetween (B i) p y)
    (hP : IsArcBetween P x y)
    (hA' : ∀ i, IsArcBetween (A' i) p' x') (hB' : ∀ i, IsArcBetween (B' i) p' y')
    (hP' : IsArcBetween P' x' y')
    (hAP : ∀ i, A i ∩ P = {x}) (hAB : ∀ i, A i ∩ B i = {p})
    (hPB : ∀ i, P ∩ B i = {y})
    (hAP' : ∀ i, A' i ∩ P' = {x'}) (hAB' : ∀ i, A' i ∩ B' i = {p'})
    (hPB' : ∀ i, P' ∩ B' i = {y'})
    (hJ : ∀ i, IsJordanCurve (A i ∪ P ∪ B i))
    (hJ' : ∀ i, IsJordanCurve (A' i ∪ P' ∪ B' i))
    (hmeet : closure (inside (A 0 ∪ P ∪ B 0)) ∩
      closure (inside (A 1 ∪ P ∪ B 1)) = P ∪ {p})
    (hmeet' : closure (inside (A' 0 ∪ P' ∪ B' 0)) ∩
      closure (inside (A' 1 ∪ P' ∪ B' 1)) = P' ∪ {p'}) :
    ∃ F G : Plane → Plane,
      IsHomeoOn F G
        (closure (inside (A 0 ∪ P ∪ B 0)) ∪ closure (inside (A 1 ∪ P ∪ B 1)))
        (closure (inside (A' 0 ∪ P' ∪ B' 0)) ∪ closure (inside (A' 1 ∪ P' ∪ B' 1))) ∧
      F p = p' ∧ F '' P = P' ∧
      (∀ i, F '' A i = A' i) ∧ (∀ i, F '' B i = B' i) := by
  classical
  obtain ⟨c⟩ := exists_arcHomeo hP hP'
  have hfilling (i : Fin 2) : ∃ F G : Plane → Plane,
      IsHomeoOn F G (closure (inside (A i ∪ P ∪ B i)))
        (closure (inside (A' i ∪ P' ∪ B' i))) ∧
      F p = p' ∧ EqOn F c.toFun P ∧ F '' A i = A' i ∧ F '' B i = B' i := by
    obtain ⟨a⟩ := exists_arcHomeo (hA i) (hA' i)
    obtain ⟨b⟩ := exists_arcHomeo (hB i) (hB' i)
    obtain ⟨f,g,hfg,hfa,hfb,hfc⟩ := three_arc_boundary_map (hA i) (hB i) hP
      (hA' i) (hB' i) hP' (hAP i) (hAB i) (hPB i) (hAP' i) (hAB' i) (hPB' i) a b c
    obtain ⟨F,G,hFG,heq⟩ := closed_interior_extension squareExtension (hJ i) (hJ' i) hfg
    have hcl : closure (inside (A i ∪ P ∪ B i)) = (A i ∪ P ∪ B i) ∪ inside (A i ∪ P ∪ B i) := by
      rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem (hJ i)),union_comm]
    have hcl' : closure (inside (A' i ∪ P' ∪ B' i)) =
        (A' i ∪ P' ∪ B' i) ∪ inside (A' i ∪ P' ∪ B' i) := by
      rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem (hJ' i)),union_comm]
    have hFA : EqOn F a.toFun (A i) := fun z hz => (heq (Or.inl (Or.inl hz))).trans (hfa hz)
    have hFB : EqOn F b.toFun (B i) := fun z hz => (heq (Or.inr hz)).trans (hfb hz)
    refine ⟨F,G,by simpa only [hcl,hcl'] using hFG,
      (hFA (hA i).left_mem).trans a.map_left,?_,hFA.image_eq.trans a.image_eq,
      hFB.image_eq.trans b.image_eq⟩
    intro z hz
    exact (heq (Or.inl (Or.inr hz))).trans (hfc hz)
  choose F G hFG hp hPmap hAmap hBmap using hfilling
  have hagree : ∀ z ∈ closure (inside (A 0 ∪ P ∪ B 0)) ∩
      closure (inside (A 1 ∪ P ∪ B 1)), F 0 z = F 1 z := by
    intro z hz
    rw [hmeet] at hz
    rcases hz with hz | rfl
    · exact (hPmap 0 hz).trans (hPmap 1 hz).symm
    · exact (hp 0).trans (hp 1).symm
  have himage : F 0 '' (closure (inside (A 0 ∪ P ∪ B 0)) ∩
      closure (inside (A 1 ∪ P ∪ B 1))) =
      closure (inside (A' 0 ∪ P' ∪ B' 0)) ∩ closure (inside (A' 1 ∪ P' ∪ B' 1)) := by
    rw [hmeet,hmeet',image_union,(hPmap 0).image_eq,c.image_eq,image_singleton,hp]
  obtain ⟨f,g,hfg,hf₀,hf₁⟩ := CurveComplex.glue_closed_homeoOn
    isClosed_closure isClosed_closure isClosed_closure isClosed_closure (hFG 0) (hFG 1) hagree himage
  have hfi (i : Fin 2) : EqOn f (F i) (closure (inside (A i ∪ P ∪ B i))) := by
    fin_cases i
    · exact fun z hz => hf₀ z hz
    · exact fun z hz => hf₁ z hz
  have hbound (i : Fin 2) : A i ∪ P ∪ B i ⊆ closure (inside (A i ∪ P ∪ B i)) := by
    intro z hz
    exact frontier_subset_closure ((jordan_curve_theorem (hJ i)).frontier_inside.symm ▸ hz)
  refine ⟨f,g,hfg,(hfi 0 (hbound 0 (Or.inl (Or.inl (hA 0).left_mem)))).trans (hp 0),?_,?_,?_⟩
  · exact ((hfi 0).mono (fun z hz => hbound 0 (Or.inl (Or.inr hz)))).image_eq.trans
      ((hPmap 0).image_eq.trans c.image_eq)
  · intro i
    exact ((hfi i).mono (fun z hz => hbound i (Or.inl (Or.inl hz)))).image_eq.trans (hAmap i)
  · intro i
    exact ((hfi i).mono (fun z hz => hbound i (Or.inr hz))).image_eq.trans (hBmap i)

end CurveComplex.HyperellipticModel
