import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Literal two-sided interior germs and compact tails of a finite family
through one unmarked point, including original loop arcs. -/
theorem actual_marked_interior_contact_fan_preprocessing
    (M : HyperellipticModel E S) {I : Type} [Fintype I] [Nonempty I]
    (c : I → EssentialMarkedArc M) (p : S) (hpmark : p ∉ M.cover.branch)
    (hp : ∀ i, p ∈ (c i).val.image)
    (hfinite : ∀ i j, i ≠ j → (ArcSurgery.crossings M (c i) (c j)).Finite)
    (U : Set S) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ τ : I → Interval, ∃ ε : ℝ, 0 < ε ∧
      (∀ i, ε < (τ i : ℝ) ∧ (τ i : ℝ) + ε < 1 ∧ (c i).val.map (τ i) = p) ∧
    let γ : I × Bool → Interval → S := fun j s =>
      (c j.1).val.map (Set.projIcc 0 1 zero_le_one
        (if j.2 then (τ j.1 : ℝ) + ε * (s : ℝ)
         else (τ j.1 : ℝ) - ε * (s : ℝ)))
    let K : I → Set S := fun i => (c i).val.map ''
      {t : Interval | (t : ℝ) ≤ (τ i : ℝ) - ε ∨ (τ i : ℝ) + ε ≤ (t : ℝ)};
      (∀ j, Topology.IsClosedEmbedding (γ j) ∧ γ j 0 = p ∧ Set.range (γ j) ⊆ U) ∧
      (∀ j k, j ≠ k → Set.range (γ j) ∩ Set.range (γ k) = {p}) ∧
      (∀ i, IsCompact (K i) ∧ p ∉ K i ∧
        (c i).val.image = Set.range (γ (i,false)) ∪ Set.range (γ (i,true)) ∪ K i) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  choose τ hτ using hp
  have hτ01 (i : I) : 0 < (τ i : ℝ) ∧ (τ i : ℝ) < 1 := by
    have h0 : τ i ≠ 0 := by
      intro hh
      exact hpmark (hτ i ▸ (hh ▸ (c i).val.start_marked))
    have h1 : τ i ≠ 1 := by
      intro hh
      exact hpmark (hτ i ▸ (hh ▸ (c i).val.end_marked))
    exact ⟨lt_of_le_of_ne (τ i).property.1 (fun hh => h0 (Subtype.ext hh.symm)),
      lt_of_le_of_ne (τ i).property.2 (fun hh => h1 (Subtype.ext hh))⟩
  have hunique (i : I) (t : Interval) (ht : (c i).val.map t = p) : t = τ i := by
    rcases (c i).val.injective_except_loop_closure t (τ i) (ht.trans (hτ i).symm) with h | h | h
    · exact h
    · exact (hpmark (ht ▸ (h.1.symm ▸ (c i).val.start_marked))).elim
    · exact (hpmark (ht ▸ (h.1.symm ▸ (c i).val.end_marked))).elim
  let nodes : Set S := ⋃ i : I, ⋃ k : I,
    if i = k then ∅ else ArcSurgery.crossings M (c i) (c k)
  have hn : nodes.Finite := Set.finite_iUnion (fun i => Set.finite_iUnion (fun k => by
    split_ifs with h
    · exact Set.finite_empty
    · exact hfinite i k h))
  let V : Set S := (U ∩ (M.cover.branch : Set S)ᶜ) ∩ (nodes \ {p})ᶜ
  have hV : IsOpen V := (hU.inter M.cover.branch.finite_toSet.isClosed.isOpen_compl).inter
    (hn.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hpV : p ∈ V := ⟨⟨hpU,hpmark⟩,fun h => h.2 (Set.mem_singleton p)⟩
  let ψ : I → ℝ → S := fun i r => (c i).val.map
    (Set.projIcc 0 1 zero_le_one ((τ i : ℝ) + r))
  have hψ (i : I) : Continuous (ψ i) := (c i).val.continuous.comp
    (continuous_projIcc.comp (continuous_const.add continuous_id))
  have hψ0 (i : I) : ψ i 0 = p := by simp [ψ,Set.projIcc_of_mem, (τ i).property,hτ]
  let A : Set ℝ := (⋂ i, ψ i ⁻¹' V) ∩
    (⋂ i, Set.Ioo (-(τ i : ℝ)) (1-(τ i : ℝ)))
  have hA : IsOpen A := (isOpen_iInter_of_finite (fun i => hV.preimage (hψ i))).inter
    (isOpen_iInter_of_finite (fun _ => isOpen_Ioo))
  have h0A : (0 : ℝ) ∈ A := by
    constructor
    · exact Set.mem_iInter.mpr (fun i => by simpa [hψ0] using hpV)
    · exact Set.mem_iInter.mpr (fun i => ⟨by linarith [(hτ01 i).1],by linarith [(hτ01 i).2]⟩)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hA 0 h0A
  let ε : ℝ := r/2
  have hε : 0 < ε := half_pos hr
  have hεr : ε < r := by dsimp [ε]; linarith
  have hsmall (x : ℝ) (hx : x ∈ Icc (-ε) ε) : x ∈ A := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
    constructor <;> linarith [hx.1,hx.2]
  have hbound (i : I) : ε < (τ i : ℝ) ∧ (τ i : ℝ)+ε < 1 := by
    have hminus := Set.mem_iInter.mp (hsmall (-ε) ⟨le_rfl,by linarith⟩).2 i
    have hplus := Set.mem_iInter.mp (hsmall ε ⟨by linarith,le_rfl⟩).2 i
    exact ⟨by linarith [hminus.1],by linarith [hplus.2]⟩
  let θ : I × Bool → Interval → ℝ := fun j t =>
    if j.2 then (τ j.1 : ℝ)+ε*(t : ℝ) else (τ j.1 : ℝ)-ε*(t : ℝ)
  have hθ (j : I × Bool) (t : Interval) : 0 < θ j t ∧ θ j t < 1 := by
    dsimp [θ]
    split_ifs <;> constructor <;> nlinarith [t.property.1,t.property.2,(hbound j.1).1,(hbound j.1).2]
  let α : I × Bool → Interval → Interval := fun j t => ⟨θ j t,le_of_lt (hθ j t).1,le_of_lt (hθ j t).2⟩
  let γ : I × Bool → Interval → S := fun j t => (c j.1).val.map (α j t)
  have hαproj (j : I × Bool) (t : Interval) :
      Set.projIcc 0 1 zero_le_one (θ j t) = α j t := Set.projIcc_of_mem _ _
  have hγcont (j : I × Bool) : Continuous (γ j) := (c j.1).val.continuous.comp
    (Continuous.subtype_mk (by dsimp [θ]; split_ifs <;> fun_prop) _)
  have hγ0 (j : I × Bool) : γ j 0 = p := by
    have hh : α j 0 = τ j.1 := by apply Subtype.ext; simp [α,θ]
    exact congrArg (c j.1).val.map hh |>.trans (hτ j.1)
  have hγV (j : I × Bool) (t : Interval) : γ j t ∈ V := by
    have hh : (if j.2 then ε*(t : ℝ) else -(ε*(t : ℝ))) ∈ Icc (-ε) ε := by
      split_ifs <;> constructor <;> nlinarith [t.property.1,t.property.2]
    have hv := Set.mem_iInter.mp (hsmall _ hh).1 j.1
    change ψ j.1 _ ∈ V at hv
    convert hv using 1
    dsimp [γ,ψ,θ] at *
    congr 1
    rw [← hαproj]
    split_ifs <;> congr 1
  have hinj (i : I) (t u : Interval) (ht : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
      (he : (c i).val.map t = (c i).val.map u) : t = u := by
    rcases (c i).val.injective_except_loop_closure t u he with h | h | h
    · exact h
    · have hh : (t : ℝ) = 0 := congrArg (fun z : Interval => (z : ℝ)) h.1; linarith
    · have hh : (t : ℝ) = 1 := congrArg (fun z : Interval => (z : ℝ)) h.1; linarith
  have hγinj (j : I × Bool) : Function.Injective (γ j) := by
    intro t u he
    have hh := congrArg Subtype.val (hinj j.1 (α j t) (α j u) (hθ j t).1 (hθ j t).2 he)
    apply Subtype.ext
    change θ j t = θ j u at hh
    dsimp [θ] at hh
    split_ifs at hh <;> nlinarith
  have hmeet (j k : I × Bool) (hjk : j ≠ k) : range (γ j) ∩ range (γ k) = {p} := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨t,rfl⟩,⟨u,hu⟩⟩
      by_cases hi : j.1 = k.1
      · have he : (c j.1).val.map (α j t) = (c j.1).val.map (α k u) := by
          simpa [γ,hi] using hu.symm
        have hh := congrArg Subtype.val (hinj j.1 _ _ (hθ j t).1 (hθ j t).2 he)
        have hb : j.2 ≠ k.2 := fun h => hjk (Prod.ext hi h)
        have ht0 : (t : ℝ) = 0 := by
          change θ j t = θ k u at hh
          dsimp [θ] at hh
          rw [hi] at hh
          cases hj : j.2 <;> cases hk : k.2
          · exact (hb (hj.trans hk.symm)).elim
          · simp [hj,hk] at hh; nlinarith [t.property.1,u.property.1]
          · simp [hj,hk] at hh; nlinarith [t.property.1,u.property.1]
          · exact (hb (hj.trans hk.symm)).elim
        rw [show t = 0 from Subtype.ext ht0,hγ0]
        exact Set.mem_singleton p
      · have hv := hγV j t
        have hnode : γ j t ∈ nodes := Set.mem_iUnion.mpr ⟨j.1,Set.mem_iUnion.mpr ⟨k.1,by
          rw [ite_eq_right hi]
          exact ⟨⟨⟨α j t,rfl⟩,hv.1.2⟩,⟨α k u,hu⟩,hv.1.2⟩⟩⟩
        by_contra hh
        exact hv.2 ⟨hnode,hh⟩
    · rintro x rfl
      exact ⟨⟨0,hγ0 j⟩,⟨0,hγ0 k⟩⟩
  refine ⟨τ,ε,hε,(fun i => ⟨(hbound i).1,(hbound i).2,hτ i⟩),?_⟩
  have hγeq (j : I × Bool) :
      (fun s : Interval => (c j.1).val.map (Set.projIcc 0 1 zero_le_one
        (if j.2 then (τ j.1 : ℝ)+ε*(s : ℝ) else (τ j.1 : ℝ)-ε*(s : ℝ)))) = γ j := by
    funext t
    exact congrArg (c j.1).val.map (hαproj j t)
  change (∀ j, Topology.IsClosedEmbedding (fun s => (c j.1).val.map
    (Set.projIcc 0 1 zero_le_one (θ j s))) ∧
    (c j.1).val.map (Set.projIcc 0 1 zero_le_one (θ j 0)) = p ∧
    range (fun s => (c j.1).val.map (Set.projIcc 0 1 zero_le_one (θ j s))) ⊆ U) ∧ _
  have hge (j : I × Bool) (t : Interval) :
      (c j.1).val.map (Set.projIcc 0 1 zero_le_one (θ j t)) = γ j t :=
    congrArg (c j.1).val.map (hαproj j t)
  have hgf (i : I) : (fun s : Interval => (c i).val.map
      (Set.projIcc 0 1 zero_le_one ((τ i : ℝ)-ε*(s : ℝ)))) = γ (i,false) := by
    simpa using hγeq (i,false)
  have hgt (i : I) : (fun s : Interval => (c i).val.map
      (Set.projIcc 0 1 zero_le_one ((τ i : ℝ)+ε*(s : ℝ)))) = γ (i,true) := by
    simpa using hγeq (i,true)
  simp only [Bool.false_eq_true,ite_false,ite_true]
  simp_rw [hge,hγeq,hgf,hgt]
  change (∀ j, Topology.IsClosedEmbedding (γ j) ∧ γ j 0 = p ∧ range (γ j) ⊆ U) ∧
    (∀ j k, j ≠ k → range (γ j) ∩ range (γ k) = {p}) ∧
    (∀ i, IsCompact ((c i).val.map '' {t : Interval | (t : ℝ) ≤ (τ i : ℝ)-ε ∨ (τ i : ℝ)+ε ≤ (t : ℝ)}) ∧
      p ∉ (c i).val.map '' {t : Interval | (t : ℝ) ≤ (τ i : ℝ)-ε ∨ (τ i : ℝ)+ε ≤ (t : ℝ)} ∧
      (c i).val.image = range (γ (i,false)) ∪ range (γ (i,true)) ∪
        (c i).val.map '' {t : Interval | (t : ℝ) ≤ (τ i : ℝ)-ε ∨ (τ i : ℝ)+ε ≤ (t : ℝ)})
  refine ⟨(fun j => ⟨(hγcont j).isClosedEmbedding (hγinj j),hγ0 j,
    fun x hx => by obtain ⟨t,rfl⟩ := hx; exact (hγV j t).1.1⟩),hmeet,?_⟩
  intro i
  let T : Set Interval := {t | (t : ℝ) ≤ (τ i : ℝ)-ε ∨ (τ i : ℝ)+ε ≤ (t : ℝ)}
  have hT : IsClosed T := (isClosed_le continuous_subtype_val continuous_const).union
    (isClosed_le continuous_const continuous_subtype_val)
  refine ⟨hT.isCompact.image (c i).val.continuous,?_,?_⟩
  · rintro ⟨t,ht,he⟩
    have hh := hunique i t he
    subst t
    rcases ht with ht | ht <;> linarith
  · apply Set.Subset.antisymm
    · rintro x ⟨t,rfl⟩
      by_cases ht : t ∈ T
      · exact Or.inr ⟨t,ht,rfl⟩
      · have hb : (τ i : ℝ)-ε < (t : ℝ) ∧ (t : ℝ) < (τ i : ℝ)+ε := by
          exact ⟨lt_of_not_ge (fun h => ht (Or.inl h)),lt_of_not_ge (fun h => ht (Or.inr h))⟩
        by_cases hl : (t : ℝ) ≤ (τ i : ℝ)
        · let s : Interval := ⟨((τ i : ℝ)-(t : ℝ))/ε,by
            constructor
            · apply (le_div_iff₀ hε).2; nlinarith
            · apply (div_le_iff₀ hε).2; nlinarith⟩
          have he : α (i,false) s = t := by
            apply Subtype.ext
            change (τ i : ℝ)-ε*(((τ i : ℝ)-(t : ℝ))/ε)=(t : ℝ)
            field_simp; ring
          exact Or.inl (Or.inl ⟨s,congrArg (c i).val.map he⟩)
        · let s : Interval := ⟨((t : ℝ)-(τ i : ℝ))/ε,by
            constructor
            · apply (le_div_iff₀ hε).2; nlinarith
            · apply (div_le_iff₀ hε).2; nlinarith⟩
          have he : α (i,true) s = t := by
            apply Subtype.ext
            change (τ i : ℝ)+ε*(((t : ℝ)-(τ i : ℝ))/ε)=(t : ℝ)
            field_simp; ring
          exact Or.inl (Or.inr ⟨s,congrArg (c i).val.map he⟩)
    · intro x hx
      rcases hx with (⟨t,rfl⟩ | ⟨t,rfl⟩) | ⟨t,ht,rfl⟩
      · exact ⟨α (i,false) t,rfl⟩
      · exact ⟨α (i,true) t,rfl⟩
      · exact ⟨t,rfl⟩
end CurveComplex.HyperellipticModel
