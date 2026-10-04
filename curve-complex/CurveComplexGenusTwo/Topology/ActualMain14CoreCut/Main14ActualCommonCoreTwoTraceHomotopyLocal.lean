import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualSuppliedAnnulusSidePairingSourceLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E : Type} [TopologicalSpace E]
set_option maxHeartbeats 4000000

-- The actual two source sides are homotoped simultaneously without crossing
-- one another or the common midpoint. This does not assert ambient extension.
example (U V : Set E) (A : Circle × Interval ≃ₜ U)
    (B : Circle × Interval ≃ₜ V)
    (G : C(Circle × Interval,Circle × Interval))
    (hGe : Topology.IsEmbedding G)
    (hG : ∀ p, (B (G p)).val = (A p).val)
    (r : Circle ≃ₜ Circle)
    (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩) = (r z,⟨1/2,by norm_num⟩))
    (hsides :
      ((∀ z (u : Interval), (u:ℝ) < 1/2 → ((G (z,u)).2:ℝ) < 1/2) ∧
        (∀ z (u : Interval), 1/2 < (u:ℝ) → 1/2 < ((G (z,u)).2:ℝ))) ∨
      ((∀ z (u : Interval), (u:ℝ) < 1/2 → 1/2 < ((G (z,u)).2:ℝ)) ∧
        (∀ z (u : Interval), 1/2 < (u:ℝ) → ((G (z,u)).2:ℝ) < 1/2))) :
    ∃ F0 F1 : C(Interval × Circle,E),
      (∀ z, F0 (0,z) = (A (z,0)).val) ∧
      (∀ z, F1 (0,z) = (A (z,1)).val) ∧
      Set.range (fun z => F0 (1,z)) ∪ Set.range (fun z => F1 (1,z)) =
        Set.range (fun z : Circle => (B (z,⟨1/4,by norm_num⟩)).val) ∪
          Set.range (fun z : Circle => (B (z,⟨3/4,by norm_num⟩)).val) ∧
      (∀ t, Topology.IsEmbedding (fun z => F0 (t,z)) ∧ Topology.IsEmbedding (fun z => F1 (t,z))) ∧
      (∀ t, Disjoint (Set.range (fun z => F0 (t,z)))
        (Set.range (fun z => F1 (t,z)))) ∧
      (∀ t, Disjoint (Set.range (fun z => F0 (t,z)) ∪ Set.range (fun z => F1 (t,z)))
        (Set.range (fun z : Circle => (B (z,⟨1/2,by norm_num⟩)).val))) := by
  audit_main14_base3
    let c : Interval := ⟨1/2,by norm_num⟩
    let q : Interval := ⟨1/4,by norm_num⟩
    let s : Interval := ⟨3/4,by norm_num⟩
    let w (t u : Interval) : Interval :=
      ⟨(1-(t:ℝ))*(u:ℝ)+(t:ℝ)/2,by constructor <;> nlinarith [t.property.1,t.property.2,u.property.1,u.property.2]⟩
    -- Both source levels move toward the SAME midpoint of the actual G.
    -- A positive affine map of the TARGET height retains injectivity of every slice.
    let f (a b : Interval) : C(Interval × Circle,Circle × Interval) :=
      ⟨fun p => ((G (p.2,w p.1 a)).1,
        ⟨(1-(p.1:ℝ)/2)*((G (p.2,w p.1 a)).2:ℝ)+(p.1:ℝ)*(b:ℝ)/2,by
          constructor <;> nlinarith [p.1.property.1,p.1.property.2,b.property.1,b.property.2,
            (G (p.2,w p.1 a)).2.property.1,(G (p.2,w p.1 a)).2.property.2]⟩),by dsimp [w]; fun_prop⟩
    have hf0 (a b : Interval) (z : Circle) : f a b (0,z) = G (z,a) := by
      have hw : w 0 a = a := Subtype.ext (by simp [w])
      apply Prod.ext
      · simp [f,hw]
      · apply Subtype.ext
        simp [f,hw]
    have hf1 (a b : Interval) (z : Circle) :
        f a b (1,z) = (r z,⟨1/4+(b:ℝ)/2,by constructor <;> linarith [b.property.1,b.property.2]⟩) := by
      have hw : w 1 a = c := Subtype.ext (by simp [w,c])
      apply Prod.ext
      · change (G (z,w 1 a)).1 = r z
        rw [hw]
        exact congrArg Prod.fst (hcore z)
      · apply Subtype.ext
        have hc : ((G (z,c)).2:ℝ) = 1/2 := congrArg (fun p : Circle × Interval => (p.2:ℝ)) (hcore z)
        change (1-(1:ℝ)/2)*((G (z,w 1 a)).2:ℝ)+(1:ℝ)*(b:ℝ)/2 = _
        rw [hw,hc]
        ring
    have hfi (a b t : Interval) : Topology.IsEmbedding (fun z : Circle => f a b (t,z)) := by
      have hc : Continuous (fun z : Circle => f a b (t,z)) :=
        (f a b).continuous.comp (continuous_const.prodMk continuous_id)
      have hi : Function.Injective (fun z : Circle => f a b (t,z)) := by
        intro z z' he
        have hz := congrArg Prod.fst he
        have hv := congrArg (fun p : Circle × Interval => (p.2:ℝ)) he
        have hfactor : 0 < 1-(t:ℝ)/2 := by linarith [t.property.2]
        have hheight : ((G (z,w t a)).2:ℝ) = ((G (z',w t a)).2:ℝ) := by
          change (1-(t:ℝ)/2)*((G (z,w t a)).2:ℝ)+(t:ℝ)*(b:ℝ)/2 =
            (1-(t:ℝ)/2)*((G (z',w t a)).2:ℝ)+(t:ℝ)*(b:ℝ)/2 at hv
          exact (mul_left_cancel₀ hfactor.ne' (add_right_cancel hv))
        have hg := hGe.injective (Prod.ext hz (Subtype.ext hheight))
        exact congrArg Prod.fst hg
      exact (hc.isClosedEmbedding hi).isEmbedding
    have hlo (a : Interval)
        (ha : ∀ t : Interval, (t:ℝ) < 1 → ∀ z, ((G (z,w t a)).2:ℝ) < 1/2)
        (t : Interval) (z : Circle) : ((f a 0 (t,z)).2:ℝ) < 1/2 := by
      by_cases ht : (t:ℝ) = 1
      · have htI : t = 1 := Subtype.ext ht
        rw [htI,hf1]
        change (1/4:ℝ)+(0:ℝ)/2 < 1/2
        norm_num
      · have ht1 : (t:ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
        have hh := ha t ht1 z
        change (1-(t:ℝ)/2)*((G (z,w t a)).2:ℝ)+(t:ℝ)*(0:ℝ)/2 < 1/2
        have hfactor : 0 < 1-(t:ℝ)/2 := by linarith [t.property.2]
        nlinarith [mul_pos hfactor (sub_pos.mpr hh),t.property.1]
    have hhi (a : Interval)
        (ha : ∀ t : Interval, (t:ℝ) < 1 → ∀ z, 1/2 < ((G (z,w t a)).2:ℝ))
        (t : Interval) (z : Circle) : 1/2 < ((f a 1 (t,z)).2:ℝ) := by
      by_cases ht : (t:ℝ) = 1
      · have htI : t = 1 := Subtype.ext ht
        rw [htI,hf1]
        change (1/2:ℝ) < 1/4+(1:ℝ)/2
        norm_num
      · have ht1 : (t:ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
        have hh := ha t ht1 z
        change 1/2 < (1-(t:ℝ)/2)*((G (z,w t a)).2:ℝ)+(t:ℝ)*(1:ℝ)/2
        have hfactor : 0 < 1-(t:ℝ)/2 := by linarith [t.property.2]
        nlinarith [mul_pos hfactor (sub_pos.mpr hh),t.property.1]
    have hBuild (a0 a1 : Interval)
        (hlevels : (a0 = 0 ∧ a1 = 1) ∨ (a0 = 1 ∧ a1 = 0))
        (hseparate : ∀ t z z', (f 0 a0 (t,z)).2 ≠ (f 1 a1 (t,z')).2)
        (havoid0 : ∀ t z, (f 0 a0 (t,z)).2 ≠ c)
        (havoid1 : ∀ t z, (f 1 a1 (t,z)).2 ≠ c) :
        ∃ F0 F1 : C(Interval × Circle,E),
          (∀ z, F0 (0,z) = (A (z,0)).val) ∧
          (∀ z, F1 (0,z) = (A (z,1)).val) ∧
          Set.range (fun z => F0 (1,z)) ∪ Set.range (fun z => F1 (1,z)) =
            Set.range (fun z : Circle => (B (z,q)).val) ∪
              Set.range (fun z : Circle => (B (z,s)).val) ∧
          (∀ t, Topology.IsEmbedding (fun z => F0 (t,z)) ∧ Topology.IsEmbedding (fun z => F1 (t,z))) ∧
          (∀ t, Disjoint (Set.range (fun z => F0 (t,z))) (Set.range (fun z => F1 (t,z)))) ∧
          (∀ t, Disjoint (Set.range (fun z => F0 (t,z)) ∪ Set.range (fun z => F1 (t,z)))
            (Set.range (fun z : Circle => (B (z,c)).val))) := by
      let F0 : C(Interval × Circle,E) :=
        ⟨fun p => (B (f 0 a0 p)).val,continuous_subtype_val.comp (B.continuous.comp (f 0 a0).continuous)⟩
      let F1 : C(Interval × Circle,E) :=
        ⟨fun p => (B (f 1 a1 p)).val,continuous_subtype_val.comp (B.continuous.comp (f 1 a1).continuous)⟩
      have hrange (a b : Interval) :
          Set.range (fun z => (B (f a b (1,z))).val) = Set.range (fun z : Circle => (B (z,⟨1/4+(b:ℝ)/2,by constructor <;> linarith [b.property.1,b.property.2]⟩)).val) := by
        simp_rw [hf1]
        ext x
        constructor
        · rintro ⟨z,rfl⟩
          exact Set.mem_range_self (r z)
        · rintro ⟨z,rfl⟩
          exact ⟨r.symm z,by simp⟩
      refine ⟨F0,F1,?_,?_,?_,?_,?_,?_⟩
      · intro z; change (B (f 0 a0 (0,z))).val = _; rw [hf0,hG]
      · intro z; change (B (f 1 a1 (0,z))).val = _; rw [hf0,hG]
      · change Set.range (fun z => (B (f 0 a0 (1,z))).val) ∪
          Set.range (fun z => (B (f 1 a1 (1,z))).val) = _
        rw [hrange,hrange]
        have hzero : (⟨1/4+((0:Interval):ℝ)/2,by norm_num⟩ : Interval) = q :=
          Subtype.ext (by norm_num [q])
        have hone : (⟨1/4+((1:Interval):ℝ)/2,by norm_num⟩ : Interval) = s :=
          Subtype.ext (by norm_num [s])
        rcases hlevels with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rw [hzero,hone]
        · rw [hzero,hone]
          exact Set.union_comm _ _
      · intro t
        exact ⟨Topology.IsEmbedding.subtypeVal.comp (B.isEmbedding.comp (hfi 0 a0 t)),
          Topology.IsEmbedding.subtypeVal.comp (B.isEmbedding.comp (hfi 1 a1 t))⟩
      · intro t
        apply Set.disjoint_left.mpr
        rintro x ⟨z,rfl⟩ ⟨z',hz'⟩
        have he := B.injective (Subtype.ext hz')
        exact hseparate t z z' (congrArg Prod.snd he).symm
      · intro t
        apply Set.disjoint_left.mpr
        rintro x (⟨z,rfl⟩ | ⟨z,rfl⟩) ⟨z',hz'⟩
        · have he := B.injective (Subtype.ext hz')
          exact havoid0 t z (congrArg Prod.snd he).symm
        · have he := B.injective (Subtype.ext hz')
          exact havoid1 t z (congrArg Prod.snd he).symm
    have hwlo (t : Interval) (ht : (t:ℝ) < 1) : (w t 0:ℝ) < 1/2 := by
      change (1-(t:ℝ))*(0:ℝ)+(t:ℝ)/2 < 1/2
      linarith
    have hwhi (t : Interval) (ht : (t:ℝ) < 1) : 1/2 < (w t 1:ℝ) := by
      change 1/2 < (1-(t:ℝ))*(1:ℝ)+(t:ℝ)/2
      linarith
    rcases hsides with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · have hL := hlo 0 (fun t ht z => hl z (w t 0) (hwlo t ht))
      have hR := hhi 1 (fun t ht z => hr z (w t 1) (hwhi t ht))
      exact hBuild 0 1 (Or.inl ⟨rfl,rfl⟩)
        (fun t z z' he => by have hh := congrArg Subtype.val he; have := hL t z; have := hR t z'; linarith)
        (fun t z he => by have hh := congrArg Subtype.val he; have := hL t z; change _ = (1/2:ℝ) at hh; linarith)
        (fun t z he => by have hh := congrArg Subtype.val he; have := hR t z; change _ = (1/2:ℝ) at hh; linarith)
    · have hL := hhi 0 (fun t ht z => hl z (w t 0) (hwlo t ht))
      have hR := hlo 1 (fun t ht z => hr z (w t 1) (hwhi t ht))
      exact hBuild 1 0 (Or.inr ⟨rfl,rfl⟩)
        (fun t z z' he => by have hh := congrArg Subtype.val he; have := hL t z; have := hR t z'; linarith)
        (fun t z he => by have hh := congrArg Subtype.val he; have := hL t z; change _ = (1/2:ℝ) at hh; linarith)
        (fun t z he => by have hh := congrArg Subtype.val he; have := hR t z; change _ = (1/2:ℝ) at hh; linarith)
end CurveComplex.HyperellipticModel
