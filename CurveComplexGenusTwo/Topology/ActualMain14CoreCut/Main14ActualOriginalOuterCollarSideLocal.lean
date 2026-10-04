import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualOriginalAnnulusFrontierLocal

open Lean Elab Tactic in
elab "audit_main14_side_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in Main14 side proof from {c}: {ax}"
  logInfo m!"Main14 local proof axiom audit: {found.toList}"

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]
set_option maxHeartbeats 5000000

-- Genuine inside/outside assignment of an actual original outer collar.
example (M : HyperellipticModel E S) (U : Set E)
    (T : Circle × Interval ≃ₜ U)
    (hfront : Set.range (fun z : Circle => (T (z,0)).val) ∪
      Set.range (fun z : Circle => (T (z,1)).val) = frontier U)
    (e : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (he : Topology.IsOpenEmbedding e)
    (hcenter : ∀ z, e (⟨0,by norm_num⟩,z) = (T (z,0)).val)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1)
    (hclear : Disjoint (e '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε})
      (Set.range (fun z : Circle => (T (z,1)).val))) :
    (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∈ interior U) ∧
      (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∉ U) ∨
    (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∉ U) ∧
      (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∈ interior U) := by
  audit_main14_side_base3
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    letI : CompactSpace U := T.compactSpace
    have hclosed : IsClosed U := by
      have hh := (isCompact_univ : IsCompact (Set.univ : Set U)).image
        (continuous_subtype_val : Continuous (Subtype.val : U → E))
      have hr : (Subtype.val : U → E) '' Set.univ = U := by
        rw [Set.image_univ,Subtype.range_coe_subtype]
        rfl
      exact (hr ▸ hh).isClosed
    have actual_embedded_annulus_interior_isOpen
        (B : Circle × Interval → E) (hB : IsEmbedding B) :
        IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
      rw [isOpen_iff_forall_mem_open]
      rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
      have hu0 : (0:ℝ) < (u : ℝ) := hu.1
      have hu1 : (u : ℝ) < 1 := hu.2
      let lo : ℝ := (u : ℝ)/2
      let hi : ℝ := ((u : ℝ)+1)/2
      have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
      have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
      have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
      have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
      have hlh : lo ≤ hi := (hlu.trans huh).le
      let width : ℝ → Interval := fun s =>
        ⟨(Set.projIcc lo hi hlh s : ℝ),
          ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
            le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
      have hwc : Continuous width :=
        (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
      let θ := Complex.arg (z : ℂ)
      let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
      have hfc : Continuous f := hB.continuous.comp
        ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
      let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
        {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
      have hΩ : IsOpen Ω :=
        (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
      have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
          (width (x 0) : ℝ) = x 0 :=
        congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
      have hfi : Set.InjOn f Ω := by
        intro x hx w hw he
        have hp := hB.injective he
        have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
          (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
          ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
        have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
        change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
        rw [hclip x hx,hclip w hw] at hwidth
        ext i
        fin_cases i
        · exact hwidth
        · exact hangle
      have hopen : IsOpen (f '' Ω) :=
        CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
      have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
        rintro q ⟨x,hx,rfl⟩
        refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
        · change 0 < (width (x 0) : ℝ)
          rw [hclip x hx]
          exact hl0.trans hx.1.1
        · change (width (x 0) : ℝ) < 1
          rw [hclip x hx]
          exact hx.1.2.trans hh1
      let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
      have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
      have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
      have hx : x ∈ Ω := by
        refine ⟨?_,?_⟩
        · rw [hx0]; exact ⟨hlu,huh⟩
        · rw [hx1]; constructor <;> linarith [Real.pi_pos]
      have hwu : width (u : ℝ) = u := by
        apply Subtype.ext
        change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
        exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
      have hpoint : f x = B (z,u) := by
        dsimp [f]
        rw [hx0,hx1,hwu,Circle.exp_arg]
      exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
    let f : Circle × Interval → E := fun p => (T p).val
    have hfe : Topology.IsEmbedding f := Topology.IsEmbedding.subtypeVal.comp T.isEmbedding
    let I := f '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
    have hIo : IsOpen I := actual_embedded_annulus_interior_isOpen f hfe
    have hIU : I ⊆ U := by rintro x ⟨p,hp,rfl⟩; exact (T p).property
    have hIint : I ⊆ interior U := hIo.subset_interior_iff.mpr hIU
    have hdense : U ⊆ closure (interior U) := by
      intro x hx
      let p := T.symm ⟨x,hx⟩
      have hp : p ∈ closure ((Set.univ : Set Circle) ×ˢ Set.Ioo (0:Interval) 1) := by
        rw [closure_prod_eq,closure_univ,closure_Ioo (show (0:Interval) ≠ 1 by norm_num)]
        exact ⟨Set.mem_univ _,p.2.property.1,p.2.property.2⟩
      have him : f p ∈ closure I := image_closure_subset_closure_image hfe.continuous ⟨p,hp,rfl⟩
      have heq : f p = x := congrArg Subtype.val (T.apply_symm_apply ⟨x,hx⟩)
      rw [heq] at him
      exact closure_mono hIint him
    let w0 : Set.Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
    let wp : Set.Ioo (-1:ℝ) 1 := ⟨ε,by constructor <;> linarith⟩
    let wn : Set.Ioo (-1:ℝ) 1 := ⟨-ε,by constructor <;> linarith⟩
    let P := e '' (Set.Ioo w0 wp ×ˢ (Set.univ : Set Circle))
    let Q := e '' (Set.Ioo wn w0 ×ˢ (Set.univ : Set Circle))
    let O := e '' (Set.Ioo wn wp ×ˢ (Set.univ : Set Circle))
    have h0p : w0 < wp := hε
    have hn0 : wn < w0 := by change -ε < 0; linarith
    have hInterval (a b : Set.Ioo (-1:ℝ) 1) (hab : a < b) : IsConnected (Set.Ioo a b) := by
      letI : ConnectedSpace (Set.Ioo (a:ℝ) (b:ℝ)) := Subtype.connectedSpace (isConnected_Ioo (show (a:ℝ) < (b:ℝ) from hab))
      let inc : Set.Ioo (a:ℝ) (b:ℝ) → Set.Ioo (-1:ℝ) 1 := fun x =>
        ⟨x.val,⟨a.property.1.trans x.property.1,x.property.2.trans b.property.2⟩⟩
      have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
      have hr : Set.range inc = Set.Ioo a b := by
        ext x
        constructor
        · rintro ⟨y,rfl⟩
          exact y.property
        · intro hx
          exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
      rw [← hr]
      exact isConnected_range hinc
    have hP : IsPreconnected P :=
      ((hInterval w0 wp h0p).prod isConnected_univ).isPreconnected.image e e.continuous.continuousOn
    have hQ : IsPreconnected Q :=
      ((hInterval wn w0 hn0).prod isConnected_univ).isPreconnected.image e e.continuous.continuousOn
    have hO : IsOpen O := he.isOpenMap _ (isOpen_Ioo.prod isOpen_univ)
    have hOcenter (z : Circle) : e (w0,z) ∈ O :=
      ⟨(w0,z),⟨⟨hn0,h0p⟩,Set.mem_univ _⟩,rfl⟩
    have hAvoid (w : Set.Ioo (-1:ℝ) 1) (hw : |(w:ℝ)| < ε)
        (hn : (w:ℝ) ≠ 0) (z : Circle) : e (w,z) ∉ frontier U := by
      intro hx
      rw [← hfront] at hx
      rcases hx with ⟨v,hv⟩ | hx
      · have hh : e (w,z) = e (w0,v) := by rw [hcenter]; exact hv.symm
        have heq := congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => (p.1:ℝ))
          (he.injective hh)
        exact hn heq
      · exact Set.disjoint_left.mp hclear ⟨(w,z),hw,rfl⟩ hx
    have hPavoid : P ⊆ (frontier U)ᶜ := by
      rintro x ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩
      have hw0 : 0 < (w:ℝ) := hw.1
      have hwε : (w:ℝ) < ε := hw.2
      exact hAvoid w (by rw [abs_of_pos hw0]; exact hwε) hw0.ne' z
    have hQavoid : Q ⊆ (frontier U)ᶜ := by
      rintro x ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩
      have hw0 : (w:ℝ) < 0 := hw.2
      have hwε : -ε < (w:ℝ) := hw.1
      exact hAvoid w (by rw [abs_of_neg hw0]; linarith) hw0.ne z
    have hsub (D : Set E) (hD : D ⊆ (frontier U)ᶜ) : D ⊆ interior U ∪ Uᶜ := by
      intro x hx
      by_cases hxu : x ∈ U
      · apply Or.inl
        by_contra hn
        exact hD hx ((mem_frontier_iff_notMem_interior hxu).mpr hn)
      · exact Or.inr hxu
    have hid : Disjoint (interior U) Uᶜ := Set.disjoint_left.mpr
      (fun x hx hn => hn (interior_subset hx))
    have hPd : P ⊆ interior U ∨ P ⊆ Uᶜ :=
      IsPreconnected.subset_or_subset isOpen_interior hclosed.isOpen_compl hid (hsub P hPavoid) hP
    have hQd : Q ⊆ interior U ∨ Q ⊆ Uᶜ :=
      IsPreconnected.subset_or_subset isOpen_interior hclosed.isOpen_compl hid (hsub Q hQavoid) hQ
    have hcenterFront (z : Circle) : e (w0,z) ∈ frontier U := by
      rw [hcenter,← hfront]
      exact Or.inl (Set.mem_range_self z)
    have hsplit (x : E) (hx : x ∈ O) : x ∈ P ∨ x ∈ Q ∨ ∃ z, x = e (w0,z) := by
      obtain ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩ := hx
      rcases lt_trichotomy w w0 with hh | hh | hh
      · exact Or.inr (Or.inl ⟨(w,z),⟨⟨hw.1,hh⟩,Set.mem_univ _⟩,rfl⟩)
      · exact Or.inr (Or.inr ⟨z,by rw [hh]⟩)
      · exact Or.inl ⟨(w,z),⟨⟨hh,hw.2⟩,Set.mem_univ _⟩,rfl⟩
    have hnotbothin : ¬ (P ⊆ interior U ∧ Q ⊆ interior U) := by
      rintro ⟨hp,hq⟩
      have hOU : O ⊆ U := by
        intro x hx
        rcases hsplit x hx with hx | hx | ⟨z,rfl⟩
        · exact interior_subset (hp hx)
        · exact interior_subset (hq hx)
        · rw [hcenter]
          exact (T (z,0)).property
      have hint : e (w0,1) ∈ interior U := hO.subset_interior_iff.mpr hOU (hOcenter 1)
      exact Set.disjoint_left.mp disjoint_interior_frontier hint (hcenterFront 1)
    have hnotbothout : ¬ (P ⊆ Uᶜ ∧ Q ⊆ Uᶜ) := by
      rintro ⟨hp,hq⟩
      have hcU : e (w0,1) ∈ U := by rw [hcenter]; exact (T (1,0)).property
      have hccl := hdense hcU
      obtain ⟨x,hxO,hxi⟩ := mem_closure_iff.mp hccl O hO (hOcenter 1)
      rcases hsplit x hxO with hx | hx | ⟨z,rfl⟩
      · exact hp hx (interior_subset hxi)
      · exact hq hx (interior_subset hxi)
      · exact Set.disjoint_left.mp disjoint_interior_frontier hxi (hcenterFront z)
    have hPmem (w : Set.Ioo (-1:ℝ) 1) (h0 : 0 < (w:ℝ)) (h1 : (w:ℝ) < ε) (z : Circle) :
        e (w,z) ∈ P := ⟨(w,z),⟨⟨h0,h1⟩,Set.mem_univ _⟩,rfl⟩
    have hQmem (w : Set.Ioo (-1:ℝ) 1) (h0 : -ε < (w:ℝ)) (h1 : (w:ℝ) < 0) (z : Circle) :
        e (w,z) ∈ Q := ⟨(w,z),⟨⟨h0,h1⟩,Set.mem_univ _⟩,rfl⟩
    rcases hPd with hp | hp <;> rcases hQd with hq | hq
    · exact False.elim (hnotbothin ⟨hp,hq⟩)
    · exact Or.inl ⟨fun w h0 h1 z => hp (hPmem w h0 h1 z),fun w h0 h1 z => hq (hQmem w h0 h1 z)⟩
    · exact Or.inr ⟨fun w h0 h1 z => hp (hPmem w h0 h1 z),fun w h0 h1 z => hq (hQmem w h0 h1 z)⟩
    · exact False.elim (hnotbothout ⟨hp,hq⟩)

end CurveComplex.HyperellipticModel
