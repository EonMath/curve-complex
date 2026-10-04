import CurveComplexGenusTwo.Dictionary.OneBranchDiscBoundary
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S X : Type} [TopologicalSpace E] [TopologicalSpace S] [TopologicalSpace X]
 [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
theorem two_cell_disc_pasting_closed_lift (K : Set X) (f : C(K,S)) (hf : IsEmbedding f)
 (a b : K) (P χ : Path a b) (Q : Path b a)
 (F : Fin 2 → C(Metric.closedBall (0 : Schoenflies.Plane) 1,S))
 (hF : ∀ i, IsEmbedding (F i)) (m : Fin 2 → Metric.closedBall (0 : Schoenflies.Plane) 1)
 (hm : ∀ i, ‖(m i).val‖<1) (honly : ∀ i z, F i z ∈ M.cover.branch ↔ z=m i)
 (hcell0 : Set.range (fun t => f ((P.trans χ.symm) t))=F 0 '' {z | ‖z.val‖=1})
 (hcell1 : Set.range (fun t => f ((χ.trans Q) t))=F 1 '' {z | ‖z.val‖=1})
 (hcoll0 : ∀ s t, (P.trans χ.symm) s=(P.trans χ.symm) t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
 (hcoll1 : ∀ s t, (χ.trans Q) s=(χ.trans Q) t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
 (γ : C(Interval,E)) (hγπ : ∀ t, M.cover.projection (γ t)=f ((P.trans Q) t)) : γ 1=γ 0 := by
  have hTwoDisc (a b : M.cover.unramifiedBase) (P χ : Path a b) (Q : Path b a)
   (F : Fin 2 → C(Metric.closedBall (0 : Schoenflies.Plane) 1,S))
   (hF : ∀ i, IsEmbedding (F i)) (m : Fin 2 → Metric.closedBall (0 : Schoenflies.Plane) 1)
   (hm : ∀ i, ‖(m i).val‖<1) (honly : ∀ i z, F i z ∈ M.cover.branch ↔ z=m i)
   (hcell0 : Set.range (fun t => ((P.trans χ.symm) t).val) = F 0 '' {z | ‖z.val‖=1})
   (hcell1 : Set.range (fun t => ((χ.trans Q) t).val) = F 1 '' {z | ‖z.val‖=1})
   (hcoll0 : ∀ s t, ((P.trans χ.symm) s).val=((P.trans χ.symm) t).val → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
   (hcoll1 : ∀ s t, ((χ.trans Q) s).val=((χ.trans Q) t).val → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
   (γ : C(Interval,E)) (hγπ : ∀ t, M.cover.projection (γ t)=((P.trans Q) t).val) : γ 1=γ 0 := by
    have hOne (f : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
      (m : Metric.closedBall (0 : Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1)
      (honly : ∀ z, f z ∈ M.cover.branch ↔ z = m)
      (β : C(Interval,S)) (hends : β 0 = β 1)
      (hcoll : ∀ s t, β s = β t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
      (hrange : Set.range β = f '' {z | ‖z.val‖ = 1})
      (γ : C(Interval,E)) (hγπ : ∀ t, M.cover.projection (γ t) = β t) :
      γ 1 = M.cover.deck (γ 0) := by
      let h := hf.toHomeomorph
      have hβrange (t : Interval) : β t ∈ Set.range f := by
        have ht : β t ∈ Set.range β := Set.mem_range_self t
        rw [hrange] at ht
        rcases ht with ⟨z,hz,hzt⟩
        exact ⟨z,hzt⟩
      let bs : C(Interval,Set.range f) :=
        ⟨fun t => ⟨β t,hβrange t⟩,β.continuous.subtype_mk hβrange⟩
      let B : C(Interval,Metric.closedBall (0 : Schoenflies.Plane) 1) :=
        ⟨h.symm ∘ bs,h.symm.continuous.comp bs.continuous⟩
      have hBproj (t) : f (B t) = β t := congrArg Subtype.val (h.apply_symm_apply (bs t))
      have hBends : B 0 = B 1 := hf.injective (by rw [hBproj,hBproj,hends])
      have hBcoll : ∀ s t, B s = B t →
          s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
        intro s t he
        apply hcoll s t
        rw [← hBproj s,← hBproj t,he]
      have hBrange : Set.range B = {z | ‖z.val‖ = 1} := by
        ext z
        constructor
        · rintro ⟨t,rfl⟩
          have ht : β t ∈ f '' {z | ‖z.val‖ = 1} := hrange ▸ Set.mem_range_self t
          rcases ht with ⟨w,hw,hwt⟩
          have he : w = B t := hf.injective (hwt.trans (hBproj t).symm)
          exact he ▸ hw
        · intro hz
          have hfz : f z ∈ Set.range β := by
            rw [hrange]
            exact ⟨z,hz,rfl⟩
          rcases hfz with ⟨t,ht⟩
          exact ⟨t,hf.injective ((hBproj t).trans ht)⟩
      apply M.one_branch_disc_boundary_sheet_exchange f hf m hm honly B hBends hBcoll hBrange γ
      intro t
      rw [hBproj]
      exact hγπ t
    have hTwo (q : BranchedDoubleCover E S) (a b : q.unramifiedBase)
      (P χ : Path a b) (Q : Path b a)
      (hleft : ∀ γ : C(Interval,E),
        (∀ t, q.projection (γ t) = ((P.trans χ.symm) t).val) → γ 1 = q.deck (γ 0))
      (hright : ∀ γ : C(Interval,E),
        (∀ t, q.projection (γ t) = ((χ.trans Q) t).val) → γ 1 = q.deck (γ 0))
      (γ : C(Interval,E)) (hγπ : ∀ t, q.projection (γ t) = ((P.trans Q) t).val) :
      γ 1 = γ 0 := by
      have hswap (q : BranchedDoubleCover E S) (a : q.unramifiedBase) (ℓ : Path a a)
        (hexchange : ∀ γ : C(Interval, E),
          (∀ t, q.projection (γ t) = (ℓ t).val) → γ 1 = q.deck (γ 0)) :
        ∀ x : q.unramifiedProjection ⁻¹' {a},
          (q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk ℓ) x).val.val =
            q.deck x.val.val := by
        intro x
        let g := q.unramified_isCoveringMap.liftPath ℓ.toContinuousMap x.val
          (ℓ.source.trans x.property.symm)
        let γ : C(Interval, E) := ⟨fun t => (g t).val,
          continuous_subtype_val.comp g.continuous⟩
        have hγπ (t : Interval) : q.projection (γ t) = (ℓ t).val := by
          have h := congrFun (q.unramified_isCoveringMap.liftPath_lifts
            ℓ.toContinuousMap x.val (ℓ.source.trans x.property.symm)) t
          exact congrArg Subtype.val h
        have hs := hexchange γ hγπ
        change (g 1).val = q.deck (g 0).val at hs
        have hzero : g 0 = x.val := q.unramified_isCoveringMap.liftPath_zero ..
        rw [hzero] at hs
        exact hs
      have hcomp (q : BranchedDoubleCover E S) (a b : q.unramifiedBase)
        (P χ : Path a b) (Q : Path b a) (x : q.unramifiedProjection ⁻¹' {a}) :
        q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (P.trans Q)) x =
          q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (χ.trans Q))
            (q.unramified_isCoveringMap.monodromy
              (Path.Homotopic.Quotient.mk (P.trans χ.symm)) x) := by
        have hclass : (Path.Homotopic.Quotient.mk (P.trans χ.symm)).trans
            (Path.Homotopic.Quotient.mk (χ.trans Q)) =
            Path.Homotopic.Quotient.mk (P.trans Q) := by
          simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
          rw [Path.Homotopic.Quotient.trans_assoc,
            ← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk χ).symm,
            Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
        rw [← hclass]
        exact q.unramified_isCoveringMap.monodromy_trans_apply _ _ x
      have hback (q : BranchedDoubleCover E S) (a : q.unramifiedBase) (ℓ : Path a a)
        (hmon : ∀ x : q.unramifiedProjection ⁻¹' {a},
          (q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk ℓ) x).val.val =
            x.val.val)
        (γ : C(Interval, E)) (hγπ : ∀ t, q.projection (γ t) = (ℓ t).val) :
        γ 1 = γ 0 := by
        have hγavoid (t : Interval) : q.projection (γ t) ∉ q.branch := by
          rw [hγπ]
          exact (ℓ t).property
        let Γ : C(Interval, q.unramifiedTotal) :=
          ⟨fun t => ⟨γ t, hγavoid t⟩, γ.continuous.subtype_mk hγavoid⟩
        have hΓπ : q.unramifiedProjection ∘ Γ = ℓ := by
          funext t
          exact Subtype.ext (hγπ t)
        let x : q.unramifiedProjection ⁻¹' {a} :=
          ⟨Γ 0, by
            change q.unramifiedProjection (Γ 0) = a
            exact (congrFun hΓπ 0).trans ℓ.source⟩
        have hΓlift : Γ = q.unramified_isCoveringMap.liftPath ℓ.toContinuousMap x.val
            (ℓ.source.trans x.property.symm) :=
          (q.unramified_isCoveringMap.eq_liftPath_iff' (ℓ.source.trans x.property.symm)).mpr
            ⟨hΓπ, rfl⟩
        have hs := hmon x
        change (q.unramified_isCoveringMap.liftPath ℓ.toContinuousMap x.val
          (ℓ.source.trans x.property.symm) 1).val = γ 0 at hs
        rw [← hΓlift] at hs
        exact hs
      apply hback q a (P.trans Q) _ γ hγπ
      intro x
      have hL := hswap q a (P.trans χ.symm) hleft x
      have hR := hswap q a (χ.trans Q) hright
        (q.unramified_isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (P.trans χ.symm)) x)
      rw [hcomp]
      rw [hR,hL,q.deck_involution]
    apply hTwo M.cover a b P χ Q _ _ γ hγπ
    · intro γ hγπ
      let β : C(Interval,S) := ⟨fun t => ((P.trans χ.symm) t).val,continuous_subtype_val.comp (P.trans χ.symm).continuous⟩
      have hends : β 0=β 1 := congrArg Subtype.val ((P.trans χ.symm).source.trans (P.trans χ.symm).target.symm)
      exact hOne (F 0) (hF 0) (m 0) (hm 0) (honly 0) β hends hcoll0 hcell0 γ hγπ
    · intro γ hγπ
      let β : C(Interval,S) := ⟨fun t => ((χ.trans Q) t).val,continuous_subtype_val.comp (χ.trans Q).continuous⟩
      have hends : β 0=β 1 := congrArg Subtype.val ((χ.trans Q).source.trans (χ.trans Q).target.symm)
      exact hOne (F 1) (hF 1) (m 1) (hm 1) (honly 1) β hends hcoll1 hcell1 γ hγπ
  have hPhi {X : Type} [TopologicalSpace X] (K : Set X) (f : C(K,S)) (hf : IsEmbedding f) :
    ∃ Φ : C({z : K | f z ∉ M.cover.branch},M.cover.unramifiedBase),
      IsEmbedding Φ ∧ (∀ z, (Φ z).val = f z.val) := by
    let Φ : C({z : K | f z ∉ M.cover.branch},M.cover.unramifiedBase) :=
      ⟨fun z => ⟨f z.val,z.property⟩,
        (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hcomp : IsEmbedding (Subtype.val ∘ Φ) := hf.comp IsEmbedding.subtypeVal
    exact ⟨Φ,IsEmbedding.subtypeVal.of_comp_iff.mp hcomp,fun _ => rfl⟩
  have hLift {X : Type} [TopologicalSpace X] (K : Set X) (f : C(K,S)) (a b : K)
    (ha : f a ∉ M.cover.branch) (hb : f b ∉ M.cover.branch)
    (P : Path a b) (hP : ∀ t, f (P t) ∉ M.cover.branch) :
    ∃ Q : Path (⟨a,ha⟩ : {z : K | f z ∉ M.cover.branch}) ⟨b,hb⟩,
      ∀ t, (Q t).val = P t := by
    let r : C(Interval,{z : K | f z ∉ M.cover.branch}) :=
      ⟨fun t => ⟨P t,hP t⟩,P.continuous.subtype_mk hP⟩
    let Q : Path (⟨a,ha⟩ : {z : K | f z ∉ M.cover.branch}) ⟨b,hb⟩ :=
      ⟨r,Subtype.ext P.source,Subtype.ext P.target⟩
    exact ⟨Q,fun _ => rfl⟩
  have hBoundaryAvoid (i : Fin 2) : ∀ y ∈ F i '' {z | ‖z.val‖=1}, y ∉ M.cover.branch := by
    rintro y ⟨z,hz,rfl⟩ hy
    have he := (honly i z).mp hy
    exact (hm i).ne (he ▸ hz)
  have hLoopAvoid0 : ∀ z ∈ Set.range (P.trans χ.symm), f z ∉ M.cover.branch := by
    rintro z ⟨t,rfl⟩; apply hBoundaryAvoid 0; rw [← hcell0]; exact Set.mem_range_self t
  have hLoopAvoid1 : ∀ z ∈ Set.range (χ.trans Q), f z ∉ M.cover.branch := by
    rintro z ⟨t,rfl⟩; apply hBoundaryAvoid 1; rw [← hcell1]; exact Set.mem_range_self t
  have hPavoid (t) : f (P t) ∉ M.cover.branch := by
    apply hLoopAvoid0; rw [Path.trans_range]; exact Or.inl (Set.mem_range_self t)
  have hχavoid (t) : f (χ t) ∉ M.cover.branch := by
    apply hLoopAvoid0; rw [Path.trans_range,Path.symm_range]; exact Or.inr (Set.mem_range_self t)
  have hQavoid (t) : f (Q t) ∉ M.cover.branch := by
    apply hLoopAvoid1; rw [Path.trans_range]; exact Or.inr (Set.mem_range_self t)
  have ha : f a ∉ M.cover.branch := by simpa only [P.source] using hPavoid 0
  have hb : f b ∉ M.cover.branch := by simpa only [χ.target] using hχavoid 1
  obtain ⟨Φ,hΦ,hΦmap⟩ := hPhi K f hf
  obtain ⟨PG,hPG⟩ := hLift K f a b ha hb P hPavoid
  obtain ⟨χG,hχG⟩ := hLift K f a b ha hb χ hχavoid
  obtain ⟨QG,hQG⟩ := hLift K f b a hb ha Q hQavoid
  let incl : C({z : K | f z ∉ M.cover.branch},K) := ⟨Subtype.val,continuous_subtype_val⟩
  have hPGmap : PG.map incl.continuous=P := by apply Path.ext; funext t; exact hPG t
  have hχGmap : χG.map incl.continuous=χ := by apply Path.ext; funext t; exact hχG t
  have hQGmap : QG.map incl.continuous=Q := by apply Path.ext; funext t; exact hQG t
  have hLoopProjection {u v : {z : K | f z ∉ M.cover.branch}}
      (L : Path u v) (R : Path v u) (t : Interval) :
      (((L.map Φ.continuous).trans (R.map Φ.continuous)) t).val =
      f (((L.map incl.continuous).trans (R.map incl.continuous)) t) := by
    rw [← Path.map_trans,← Path.map_trans]
    exact hΦmap ((L.trans R) t)
  let P' := PG.map Φ.continuous
  let χ' := χG.map Φ.continuous
  let Q' := QG.map Φ.continuous
  have hp0 (t) : ((P'.trans χ'.symm) t).val=f ((P.trans χ.symm) t) := by
    have h := hLoopProjection PG χG.symm t
    simpa only [← Path.map_symm,hPGmap,hχGmap] using h
  have hp1 (t) : ((χ'.trans Q') t).val=f ((χ.trans Q) t) := by
    have h := hLoopProjection χG QG t
    simpa only [hχGmap,hQGmap] using h
  have hpo (t) : ((P'.trans Q') t).val=f ((P.trans Q) t) := by
    have h := hLoopProjection PG QG t
    simpa only [hPGmap,hQGmap] using h
  have hcell0' : Set.range (fun t => ((P'.trans χ'.symm) t).val)=F 0 '' {z | ‖z.val‖=1} := by simpa only [hp0] using hcell0
  have hcell1' : Set.range (fun t => ((χ'.trans Q') t).val)=F 1 '' {z | ‖z.val‖=1} := by simpa only [hp1] using hcell1
  refine hTwoDisc _ _ P' χ' Q' F hF m hm honly hcell0' hcell1' ?_ ?_ γ ?_
  · intro s t he; rw [hp0,hp0] at he; exact hcoll0 s t (hf.injective he)
  · intro s t he; rw [hp1,hp1] at he; exact hcoll1 s t (hf.injective he)
  · intro t; rw [hpo]; exact hγπ t
end CurveComplex.HyperellipticModel
