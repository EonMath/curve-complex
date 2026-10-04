import CurveComplexGenusTwo.Topology.LocalOrientation.LocalReflectionGerm
import CurveComplexGenusTwo.CWHurewicz.HomotopyHomologyIso
import CurveComplexGenusTwo.CWHurewicz.ConnectingNaturality
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements
import Mathlib.Analysis.Normed.Module.Connected
open CategoryTheory CategoryTheory.Limits Set Metric Topology
open CurveComplexGenusTwo.CWHurewicz
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

private theorem actual_literal_punctured_disc_boundary_fixed_deformation
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    let D := closedBall z₀ ρ;
    let P : Set D := {x | x.val ≠ z₀};
    let B : Set P := {x | dist x.val.val z₀ = ρ};
    ∃ r : C(P,P),
      (∀ x, dist (r x).val.val z₀ = ρ) ∧
      Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id P) r B) := by
  dsimp only
  let D := closedBall z₀ ρ
  let P : Set D := {x | x.val ≠ z₀}
  let B : Set P := {x | dist x.val.val z₀ = ρ}
  have hn (x : P) : 0 < ‖x.val.val-z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr x.property)
  have hnle (x : P) : ‖x.val.val-z₀‖ ≤ ρ := by
    simpa only [D,mem_closedBall,dist_eq_norm] using x.val.property
  let a (x : P) : ℝ := ρ / ‖x.val.val-z₀‖
  have ha (x : P) : 0 < a x := div_pos hρ (hn x)
  have han (x : P) : a x * ‖x.val.val-z₀‖ = ρ := by
    dsimp [a]; exact div_mul_cancel₀ ρ (hn x).ne'
  have hrnorm (x : P) : dist (z₀+a x • (x.val.val-z₀)) z₀ = ρ := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (ha x),han]
  let c (t : unitInterval) (x : P) : ℝ := 1-(t:ℝ)+(t:ℝ)*a x
  have hc (t : unitInterval) (x : P) : 0 < c t x := by
    have ht₀ := t.property.1; have ht₁ := t.property.2
    dsimp [c]
    by_cases ht : (t:ℝ)=0
    · simp only [ht,sub_zero,zero_mul,add_zero]; norm_num
    · have hp := mul_pos (lt_of_le_of_ne ht₀ (Ne.symm ht)) (ha x)
      linarith
  have hcn (t : unitInterval) (x : P) : c t x * ‖x.val.val-z₀‖ ≤ ρ := by
    have ht₀ := t.property.1; have ht₁ := t.property.2
    have he := han x; have hb := hnle x
    dsimp [c]
    nlinarith
  have hclosed (t : unitInterval) (x : P) : z₀+c t x • (x.val.val-z₀) ∈ D := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_pos (hc t x)]
    exact hcn t x
  have hne (t : unitInterval) (x : P) : z₀+c t x • (x.val.val-z₀) ≠ z₀ := by
    intro he
    have hz : c t x • (x.val.val-z₀) = 0 := by
      have hh := congrArg (fun z : ℂ => z-z₀) he
      simpa only [add_sub_cancel_left,sub_self] using hh
    exact (smul_ne_zero (hc t x).ne' (sub_ne_zero.mpr x.property)) hz
  let r : C(P,P) := ⟨fun x => ⟨⟨z₀+a x • (x.val.val-z₀),
      by rw [mem_closedBall,hrnorm]⟩, by
        intro he
        have hz : a x • (x.val.val-z₀) = 0 := by
          have hh := congrArg (fun z : ℂ => z-z₀) he
          simpa only [add_sub_cancel_left,sub_self] using hh
        exact (smul_ne_zero (ha x).ne' (sub_ne_zero.mpr x.property)) hz⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hv : Continuous (fun x : P => x.val.val-z₀) := by fun_prop
    exact continuous_const.add ((continuous_const.div hv.norm (fun x => (hn x).ne')).smul hv)⟩
  let H : ContinuousMap.HomotopyRel (ContinuousMap.id P) r B := {
    toFun := fun tx => ⟨⟨z₀+c tx.1 tx.2 • (tx.2.val.val-z₀),
      hclosed tx.1 tx.2⟩, hne tx.1 tx.2⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      have ht : Continuous (fun tx : unitInterval × P => (tx.1:ℝ)) := by fun_prop
      have hv : Continuous (fun tx : unitInterval × P => tx.2.val.val-z₀) := by fun_prop
      have hav : Continuous (fun tx : unitInterval × P => a tx.2) :=
        continuous_const.div hv.norm (fun tx => (hn tx.2).ne')
      exact continuous_const.add (((continuous_const.sub ht).add (ht.mul hav)).smul hv)
    map_zero_left := by
      intro x
      apply Subtype.ext; apply Subtype.ext
      change z₀+(1-(0:ℝ)+(0:ℝ)*a x) • (x.val.val-z₀) = x.val.val
      simp
    map_one_left := by
      intro x
      apply Subtype.ext; apply Subtype.ext
      change z₀+(1-(1:ℝ)+(1:ℝ)*a x) • (x.val.val-z₀) = z₀+a x • (x.val.val-z₀)
      simp
    prop' := by
      intro t x hx
      apply Subtype.ext; apply Subtype.ext
      have hnx : ‖x.val.val-z₀‖ = ρ := by
        have hx' : dist x.val.val z₀ = ρ := hx
        simpa only [dist_eq_norm] using hx'
      change z₀+c t x • (x.val.val-z₀) = x.val.val
      have haone : a x = 1 := by dsimp [a]; rw [hnx,div_self hρ.ne']
      simp only [c,haone,mul_one,sub_add_cancel,one_smul]
      abel }
  exact ⟨r,hrnorm,⟨H⟩⟩
private theorem actual_literal_chart_closedBall_image_isClosed
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    IsClosed ((chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ) := by
  exact ((isCompact_closedBall ((chartAt ℂ q) q) ρ).image_of_continuousOn
    ((chartAt ℂ q).symm.continuousOn.mono htarget)).isClosed
private theorem actual_literal_chart_ball_image_isOpen
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    IsOpen ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ) := by
  exact (chartAt ℂ q).isOpen_image_symm_of_subset_target isOpen_ball
    (ball_subset_closedBall.trans htarget)

private theorem actual_literal_chart_disc_exterior_closed_cover
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    let K := (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ;
    let P := ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ)ᶜ;
    IsClosed K ∧ IsClosed P ∧ K ∪ P = Set.univ := by
  dsimp only
  let K := (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ
  let P := ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ)ᶜ
  refine ⟨actual_literal_chart_closedBall_image_isClosed E q ρ htarget,
    (actual_literal_chart_ball_image_isOpen E q ρ htarget).isClosed_compl, ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ P
  · exact Or.inr hx
  · apply Or.inl
    exact Set.image_mono ball_subset_closedBall (not_not.mp hx)

private theorem actual_literal_chart_closed_disc_homeomorph_image
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    ∃ e : closedBall ((chartAt ℂ q) q) ρ ≃ₜ
        ((chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ),
      (∀ d, (e d).val = (chartAt ℂ q).symm d.val) ∧
      (∀ y, (e.symm y).val = (chartAt ℂ q) y.val) := by
  let cq := chartAt ℂ q
  let D := closedBall (cq q) ρ
  let K := cq.symm '' D
  have hsource (y : K) : y.val ∈ cq.source := by
    obtain ⟨z,hz,he⟩ := y.property
    rw [← he]
    exact cq.map_target (htarget hz)
  have hD (y : K) : cq y.val ∈ D := by
    obtain ⟨z,hz,he⟩ := y.property
    rw [← he,cq.right_inv (htarget hz)]
    exact hz
  let e : D ≃ₜ K := {
    toFun := fun d => ⟨cq.symm d.val, ⟨d.val,d.property,rfl⟩⟩
    invFun := fun y => ⟨cq y.val, hD y⟩
    left_inv := by
      intro d
      apply Subtype.ext
      exact cq.right_inv (htarget d.property)
    right_inv := by
      intro y
      apply Subtype.ext
      exact cq.left_inv (hsource y)
    continuous_toFun := (cq.symm.continuousOn.comp_continuous continuous_subtype_val
      (fun d => htarget d.property)).subtype_mk _
    continuous_invFun := (cq.continuousOn.comp_continuous continuous_subtype_val
      hsource).subtype_mk hD }
  exact ⟨e,fun _ => rfl,fun _ => rfl⟩

private theorem actual_literal_chart_puncture_local_radial
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ) (hρ : 0 < ρ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    let K := (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ;
    let P := ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ)ᶜ;
    let Q : Set E := {q}ᶜ;
    ∃ loc : C(unitInterval × {x : Q | x.val ∈ K}, Q),
      (∀ x : {x : Q | x.val ∈ K}, loc (0,x) = x.val) ∧
      (∀ x : {x : Q | x.val ∈ K}, (loc (1,x)).val ∈ P) ∧
      (∀ (t : unitInterval) (x : {x : Q | x.val ∈ K}), x.val.val ∈ P →
        loc (t,x) = x.val) := by
  dsimp only
  let cq := chartAt ℂ q
  let z₀ := cq q
  let D := closedBall z₀ ρ
  let K := cq.symm '' D
  let P := (cq.symm '' ball z₀ ρ)ᶜ
  let Q : Set E := {q}ᶜ
  let S : Set Q := {x | x.val ∈ K}
  obtain ⟨e,heval,heinv⟩ := actual_literal_chart_closed_disc_homeomorph_image
    E q ρ htarget
  let V : Set D := {d | d.val ≠ z₀}
  let B : Set V := {d | dist d.val.val z₀ = ρ}
  obtain ⟨r,hr,⟨H⟩⟩ :=
    actual_literal_punctured_disc_boundary_fixed_deformation z₀ ρ hρ
  have hsource (x : S) : x.val.val ∈ cq.source := by
    obtain ⟨z,hz,he⟩ := x.property
    rw [← he]
    exact cq.map_target (htarget hz)
  have hjne (x : S) : (e.symm ⟨x.val.val,x.property⟩).val ≠ z₀ := by
    intro he
    apply x.val.property
    have hxchart : cq x.val.val = z₀ := by
      rw [← heinv ⟨x.val.val,x.property⟩]
      exact he
    exact cq.injOn (hsource x) (mem_chart_source ℂ q) hxchart
  let j : C(S,V) := ⟨fun x => ⟨e.symm ⟨x.val.val,x.property⟩,hjne x⟩, by
    apply Continuous.subtype_mk
    apply e.symm.continuous.comp
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun x => x.property)⟩
  have hgne (d : V) : (e d.val).val ≠ q := by
    intro he
    have hh := congrArg cq he
    rw [heval,cq.right_inv (htarget d.val.property)] at hh
    exact d.property hh
  let g : C(V,Q) := ⟨fun d => ⟨(e d.val).val,hgne d⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (e.continuous.comp continuous_subtype_val)⟩
  have hgj (x : S) : g (j x) = x.val := by
    apply Subtype.ext
    change (e (e.symm ⟨x.val.val,x.property⟩)).val = x.val.val
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x.val.val,x.property⟩)
  let loc : C(unitInterval × S,Q) := ⟨fun tx => g (H (tx.1,j tx.2)),
    g.continuous.comp (H.continuous.comp
      (continuous_fst.prodMk (j.continuous.comp continuous_snd)))⟩
  refine ⟨loc,?_,?_,?_⟩
  · intro x
    change g (H (0,j x)) = x.val
    rw [H.apply_zero]
    exact hgj x
  · intro x
    change (g (H (1,j x))).val ∈ P
    rw [H.apply_one]
    intro hy
    obtain ⟨w,hw,hew⟩ := hy
    have htargetw : w ∈ cq.target := htarget (ball_subset_closedBall hw)
    have hzw : w = (r (j x)).val.val := by
      have hh := congrArg cq hew
      change cq (cq.symm w) = cq ((e (r (j x)).val).val) at hh
      rw [heval,cq.right_inv htargetw,
        cq.right_inv (htarget (r (j x)).val.property)] at hh
      exact hh
    have hlt : dist (r (j x)).val.val z₀ < ρ := by
      rw [← hzw]
      exact hw
    rw [hr (j x)] at hlt
    exact (lt_irrefl ρ) hlt
  · intro t x hxP
    have hboundary : j x ∈ B := by
      have hle : dist (j x).val.val z₀ ≤ ρ := (j x).val.property
      have hnot : ¬ dist (j x).val.val z₀ < ρ := by
        intro hlt
        apply hxP
        refine ⟨(j x).val.val,hlt,?_⟩
        have hh := congrArg Subtype.val (e.apply_symm_apply ⟨x.val.val,x.property⟩)
        change cq.symm (e.symm ⟨x.val.val,x.property⟩).val = x.val.val
        simpa only [heval] using hh
      exact le_antisymm hle (le_of_not_gt hnot)
    change g (H (t,j x)) = x.val
    rw [H.eq_fst t hboundary]
    exact hgj x

private theorem actual_closed_cover_relative_retraction
    (X : Type) [TopologicalSpace X] (K P Q : Set X)
    (hK : IsClosed K) (hP : IsClosed P) (hcover : K ∪ P = Set.univ)
    (hPQ : P ⊆ Q)
    (loc : C(unitInterval × {x : Q | x.val ∈ K}, Q))
    (hzero : ∀ x : {x : Q | x.val ∈ K}, loc (0,x) = x.val)
    (hone : ∀ x : {x : Q | x.val ∈ K}, (loc (1,x)).val ∈ P)
    (hfix : ∀ (t : unitInterval) (x : {x : Q | x.val ∈ K}), x.val.val ∈ P →
      loc (t,x) = x.val) :
    ∃ r : C(Q,P),
      r.comp (ContinuousMap.inclusion hPQ) = ContinuousMap.id P ∧
      Nonempty (ContinuousMap.Homotopy (ContinuousMap.id Q)
        ((ContinuousMap.inclusion hPQ).comp r)) := by
  classical
  let S : Set Q := {x | x.val ∈ K}
  let T : Set Q := {x | x.val ∈ P}
  have hS : IsClosed S := hK.preimage continuous_subtype_val
  have hT : IsClosed T := hP.preimage continuous_subtype_val
  have hST : S ∪ T = Set.univ := by
    ext x
    change (x.val ∈ K ∨ x.val ∈ P) ↔ True
    simp only [iff_true]
    have hh : x.val ∈ K ∪ P := by rw [hcover]; trivial
    simpa only [mem_union] using hh
  let F : unitInterval × Q → Q := fun tx =>
    if hx : tx.2 ∈ S then loc (tx.1, ⟨tx.2,hx⟩) else tx.2
  have hFs : ContinuousOn F (Prod.snd ⁻¹' S) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun tx : (Prod.snd ⁻¹' S : Set (unitInterval × Q)) => F tx.val)
    let k : (Prod.snd ⁻¹' S : Set (unitInterval × Q)) →
        unitInterval × S := fun tx => (tx.val.1, ⟨tx.val.2,tx.property⟩)
    have hk : Continuous k := by
      apply Continuous.prodMk
      · fun_prop
      · exact (continuous_snd.comp continuous_subtype_val).subtype_mk
          (fun tx => tx.property)
    have he : (fun tx : (Prod.snd ⁻¹' S : Set (unitInterval × Q)) => F tx.val) =
        loc ∘ k := by
      funext tx
      dsimp only [F, k, Function.comp_apply]
      rw [dif_pos (show tx.val.2 ∈ S from tx.property)]
    rw [he]
    exact loc.continuous.comp hk
  have hFt : ContinuousOn F (Prod.snd ⁻¹' T) := by
    have he : Set.EqOn F Prod.snd (Prod.snd ⁻¹' T) := by
      intro tx htx
      dsimp only [F]
      split_ifs with hx
      · exact hfix tx.1 ⟨tx.2,hx⟩ htx
      · rfl
    exact continuous_snd.continuousOn.congr he
  have hFc : Continuous F := by
    rw [← continuousOn_univ]
    have hcover' : ((Prod.snd : unitInterval × Q → Q) ⁻¹' S) ∪
        ((Prod.snd : unitInterval × Q → Q) ⁻¹' T) = Set.univ := by
      rw [← preimage_union, hST, preimage_univ]
    rw [← hcover']
    exact hFs.union_of_isClosed hFt
      (hS.preimage continuous_snd) (hT.preimage continuous_snd)
  have hFzero (x : Q) : F (0,x) = x := by
    dsimp only [F]
    split_ifs with hx
    · exact hzero ⟨x,hx⟩
    · rfl
  have hFone (x : Q) : (F (1,x)).val ∈ P := by
    dsimp only [F]
    split_ifs with hx
    · exact hone ⟨x,hx⟩
    · have hmem : x ∈ S ∪ T := hST.symm ▸ mem_univ x
      exact hmem.resolve_left hx
  let r : C(Q,P) := ⟨fun x => ⟨(F (1,x)).val,hFone x⟩,
    (continuous_subtype_val.comp (hFc.comp (continuous_const.prodMk continuous_id))).subtype_mk _⟩
  have hri : r.comp (ContinuousMap.inclusion hPQ) = ContinuousMap.id P := by
    ext x
    change (F (1,⟨x.val,hPQ x.property⟩)).val = x.val
    dsimp only [F]
    split_ifs with hx
    · exact congrArg Subtype.val (hfix 1 ⟨⟨x.val,hPQ x.property⟩,hx⟩ x.property)
    · rfl
  let H : ContinuousMap.Homotopy (ContinuousMap.id Q)
      ((ContinuousMap.inclusion hPQ).comp r) := {
    toFun := F
    continuous_toFun := hFc
    map_zero_left := hFzero
    map_one_left := by
      intro x
      rfl }
  exact ⟨r,hri,⟨H⟩⟩

private theorem actual_pair_relative_injective_of_subspace_maps
    (E : Type) [TopologicalSpace E] (P Q : Set E)
    (hPQ : P ⊆ Q)
    (h₁ : Function.Injective
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map
        (pairMapOnSubspace P Q (ContinuousMap.id E) (fun x hx => hPQ hx)))))
    (h₂ : Function.Surjective
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).map
        (pairMapOnSubspace P Q (ContinuousMap.id E) (fun x hx => hPQ hx))))) :
    Function.Injective
      (pairRelativeHomologyMap P Q (ContinuousMap.id E)
        (fun x hx => hPQ hx) 2) := by
  let f₁ := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map
    (pairMapOnSubspace P Q (ContinuousMap.id E) (fun x hx => hPQ hx))
  let f₂ := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).map
    (pairMapOnSubspace P Q (ContinuousMap.id E) (fun x hx => hPQ hx))
  let m := pairRelativeHomologyMap P Q (ContinuousMap.id E)
    (fun x hx => hPQ hx) 2
  have hδ := relativeConnecting_natural P Q (ContinuousMap.id E)
    (fun x hx => hPQ hx) 1
  have hι := pairHomologyInclusion_commutes P Q (ContinuousMap.id E)
    (fun x hx => hPQ hx) 2
  have hη := pairRelativeHomologyMap_commutes P Q (ContinuousMap.id E)
    (fun x hx => hPQ hx) 2
  suffices hker : ∀ a : relativeHomology E P 2, m a = 0 → a = 0 by
    intro a b hab
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hab, sub_self]
  intro a ha
  have hconn : relativeConnecting E P 1 a = 0 := by
    apply h₁
    have he := congrArg (fun f => f a) hδ
    change f₁ (relativeConnecting E P 1 a) =
      relativeConnecting E Q 1 (m a) at he
    rw [ha, map_zero] at he
    simpa using he
  obtain ⟨_, hexP⟩ := pairHomology_exact_at_relative E P 1
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexP a hconn
  change homologyToRelative E P 2 t = a at ht
  have htQ : homologyToRelative E Q 2 t = 0 := by
    have hη' : homologyToRelative E P 2 ≫ m =
        homologyToRelative E Q 2 := by simpa using hη
    have he := congrArg (fun f => f t) hη'
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at he
    rw [ht, ha] at he
    exact he.symm
  obtain ⟨_, hexQ⟩ := pairHomology_exact_at_absolute E Q 2
  obtain ⟨u, hu⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexQ t htQ
  change homologyInclusion E Q 2 u = t at hu
  obtain ⟨v, hv⟩ := h₂ u
  have htP : homologyInclusion E P 2 v = t := by
    have hι' : homologyInclusion E P 2 =
        f₂ ≫ homologyInclusion E Q 2 := by simpa using hι
    have he := congrArg (fun f => f v) hι'
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at he
    rw [hv, hu] at he
    exact he
  obtain ⟨hzP, _⟩ := pairHomology_exact_at_absolute E P 2
  have ha0 : a = 0 := by
    rw [← ht, ← htP]
    exact congrArg (fun f => f v) hzP
  exact ha0

private theorem actual_literal_chart_disc_exterior_point_detection
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ) (hρ : 0 < ρ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    let P : Set E :=
      ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ)ᶜ;
    ∃ havoid : ∀ x ∈ P, x ≠ q,
      Function.Injective
        (pairRelativeHomologyMap P ({q}ᶜ)
          (ContinuousMap.id E) havoid 2) := by
  dsimp only
  let P : Set E := ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ)ᶜ
  have hq : q ∈ ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ) := by
    refine ⟨(chartAt ℂ q) q, mem_ball_self hρ, ?_⟩
    exact (chartAt ℂ q).left_inv (mem_chart_source ℂ q)
  let havoid : ∀ x ∈ P, x ≠ q := by
    intro x hx he
    exact hx (he ▸ hq)
  refine ⟨havoid, ?_⟩
  let K := (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ
  let Q : Set E := {q}ᶜ
  obtain ⟨hK,hP,hcover⟩ :=
    actual_literal_chart_disc_exterior_closed_cover E q ρ htarget
  obtain ⟨loc,hzero,hone,hfix⟩ :=
    actual_literal_chart_puncture_local_radial E q ρ hρ htarget
  let i : C(P,Q) := ContinuousMap.inclusion havoid
  obtain ⟨r,hri,⟨H⟩⟩ :=
    actual_closed_cover_relative_retraction E K P Q hK hP hcover havoid
      loc hzero hone hfix
  have hmap (n : ℕ) :
      IsIso ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map
        (pairMapOnSubspace P Q (ContinuousMap.id E) havoid))) := by
    have heq : pairMapOnSubspace P Q (ContinuousMap.id E) havoid =
        TopCat.ofHom i := by ext x; rfl
    rw [heq]
    have hPht : (r.comp i).Homotopic (ContinuousMap.id P) := by
      rw [hri]
    have hQht : (i.comp r).Homotopic (ContinuousMap.id Q) := ⟨H.symm⟩
    let e := singularHomologyIsoOfHomotopyInverse (ModuleCat.of ℤ ℤ) n i r
      hPht hQht
    exact e.isIso_hom
  apply actual_pair_relative_injective_of_subspace_maps E P Q havoid
  · haveI := hmap 1
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  · haveI := hmap 2
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
