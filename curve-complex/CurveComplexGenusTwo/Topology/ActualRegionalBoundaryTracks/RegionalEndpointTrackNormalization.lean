import CurveComplexGenusTwo.Topology.ActualRegionalBoundaryTracks.RegionalDecreaseSupport
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.BoundaryPairCore
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.BoundaryCircle

open CurveComplex Set Topology RegionalTotalDecrease
open CurveComplex.BranchedDoubleCover
open CoherentEndpointMotion.FreeBoundaryContactRepair
universe v
private noncomputable local instance regionalEndpointTrackNormalizationDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem regional_actual_comparison_endpoint_tracks_normalization
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
      isRelLowerSet_faces := by
        intro τ hτ
        refine ⟨hτ.1,?_⟩
        intro μ hμτ hne
        obtain ⟨rep,hclass,hd⟩ := hτ.2
        refine ⟨hne,(fun u => rep ⟨u.val,hμτ u.property⟩),?_,?_⟩
        · intro u
          exact hclass ⟨u.val,hμτ u.property⟩
        · intro u w huw
          apply hd
          intro he
          exact huw (Subtype.ext (congrArg (fun z : ↥τ => z.val) he))
      singleton_mem := by
        intro u
        obtain ⟨a,ha⟩ := Quot.exists_rep u
        refine ⟨Finset.singleton_nonempty u,(fun _ => a),?_,?_⟩
        · intro z
          exact ha.trans (Finset.mem_singleton.mp z.property).symm
        · intro z w hzw
          exact False.elim (hzw (Subtype.ext
            ((Finset.mem_singleton.mp z.property).trans (Finset.mem_singleton.mp w.property).symm))) }
    ∀ (b bStar : IntrinsicEssentialArc) (H : AmbientIsotopy ↥F),
      ClassMovie {y | y.val ∈ boundaryCircle} {y | y.val ∈ frontier F}
        b.val.val bStar.val.val H →
      ∀ (Y : Type v) [TopologicalSpace Y] (p : Y → ↥F), IsCoveringMap p →
        ∀ (ρ : Interval ≃ₜ Interval) (D E : C(Interval,Y))
          (W : C(Interval × Interval,Y)),
          ((ρ 0 = 0 ∧ ρ 1 = 1) ∨ (ρ 0 = 1 ∧ ρ 1 = 0)) →
          (∀ s, p (D s) = b.val.val s) → (∀ s, p (E s) = bStar.val.val s) →
          (∀ s, W (0,s) = D s) → (∀ s, W (1,s) = E (ρ s)) →
          (∀ t, IsEmbedding (fun s => W (t,s))) →
          (∀ t s, p (W (t,s)) = H.map (t,b.val.val s)) →
          (∀ t s, p (W (t,s)) ∈ {y | y.val ∈ boundaryCircle} ↔ s = 0 ∨ s = 1) →
          ∀ (τ : Fin 2 → C(Interval,↥F)),
            (∀ i t, τ i t = H.map (t,b.val.val (endpoint i))) →
            ∃ (β : Circle ≃ₜ ↥({y : ↥F | y.val ∈ boundaryCircle} : Set ↥F))
              (θ : Fin 2 → C(Interval,ℝ)) (ℓ : Fin 2 → C(Interval,↥F))
              (J : ∀ i, ContinuousMap.HomotopyRel (τ i) (ℓ i) ({0,1} : Set Interval))
              (L : Fin 2 → C(Interval,Y)),
              (range (fun z : Circle => (β z).val) = {y | y.val ∈ boundaryCircle}) ∧
              (∀ i t, (β (Circle.exp (θ i t))).val = τ i t) ∧
              (∀ t, 0 < θ 1 t - θ 0 t ∧ θ 1 t - θ 0 t < 2*Real.pi) ∧
              (∀ i t, ℓ i t = (β (Circle.exp ((1-t.val)*θ i 0+t.val*θ i 1))).val) ∧
              (∀ i, ℓ i 0 = τ i 0 ∧ ℓ i 1 = τ i 1) ∧
              (∀ i r t, J i (r,t) = (β (Circle.exp ((1-r.val)*θ i t+
                r.val*((1-t.val)*θ i 0+t.val*θ i 1)))).val) ∧
              (∀ i t, J i (0,t) = τ i t ∧ J i (1,t) = ℓ i t) ∧
              (∀ i r, J i (r,0) = τ i 0 ∧ J i (r,1) = τ i 1) ∧
              (∀ i r t, (J i (r,t)).val ∈ boundaryCircle) ∧
              (∀ r t, J 0 (r,t) ≠ J 1 (r,t)) ∧
              (∀ t, ℓ 0 t ≠ ℓ 1 t) ∧
              (∀ i t, p (L i t) = ℓ i t) ∧
              (∀ i, L i 0 = D (endpoint i) ∧ L i 1 = E (ρ (endpoint i))) ∧
              (∀ i, θ i 0 = θ i 1 → ∀ t, ℓ i t = b.val.val (endpoint i)) := by
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    b bStar H hmovie Y instY p hp ρ D E W hρ hD hE hW0 hW1 hWemb hWp hWboundary τ hτ
  letI : ClosedSurface S := hS.2.1.some
  obtain ⟨cB, hcB⟩ := chartSphere_curve S
    (chartAt (EuclideanSpace ℝ (Fin 2)) x)
    ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R hR htarget
  have hmem (z : Circle) : cB.map z ∈ boundaryCircle := by
    change cB.map z ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    rw [← hcB]
    exact mem_range_self z
  let B : Set ↥F := {y | y.val ∈ boundaryCircle}
  let f : Circle → B := fun z => ⟨⟨cB.map z, hbase (hmem z)⟩, hmem z⟩
  have hfc : Continuous f := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact cB.embedded.continuous
  have hfi : Function.Injective f := by
    intro z w he
    exact cB.embedded.injective (congrArg (fun y : B => y.val.val) he)
  have hfs : Function.Surjective f := by
    intro y
    have hy : y.val.val ∈ cB.image := hcB.symm ▸ y.property
    obtain ⟨z, hz⟩ := hy
    exact ⟨z, Subtype.ext (Subtype.ext hz)⟩
  let β : Circle ≃ₜ B := (hfc.isClosedEmbedding hfi).isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr (Set.range_eq_univ.mpr hfs)).trans (Homeomorph.Set.univ B))
  have hτB (i : Fin 2) (t : Interval) : τ i t ∈ B := by
    rw [hτ i t, ← hWp t (endpoint i)]
    exact (hWboundary t (endpoint i)).mpr (by fin_cases i <;> simp [endpoint])
  have hτne (t : Interval) : τ 0 t ≠ τ 1 t := by
    intro he
    obtain ⟨h, hh⟩ := H.homeomorphism_at t
    have hb : b.val.val (0 : Interval) = b.val.val 1 := h.injective (by
      rw [hh, hh]
      simpa [hτ, endpoint] using he)
    exact zero_ne_one (b.val.property.1.injective hb)
  obtain ⟨θ, ℓ, JH, hθ, hgap, hℓ, hend, hJ, hJ01, hJend, hJB, hJneq, hℓneq, hcover⟩ :=
    boundary_pair_affine_normalization.{0, v} β τ hτB hτne
  let T : Fin 2 → C(Interval, Y) := fun i =>
    ⟨fun t => W (t, endpoint i), W.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hT (i : Fin 2) (t : Interval) : p (T i t) = τ i t := by
    exact (hWp t (endpoint i)).trans (hτ i t).symm
  obtain ⟨L, hL, hLend⟩ := hcover Y p hp T hT
  refine ⟨β, θ, ℓ, JH, L, ?_, hθ, hgap, hℓ, hend, hJ, hJ01, hJend,
    hJB, hJneq, hℓneq, hL, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, rfl⟩; exact (β z).property
    · intro hy
      exact ⟨β.symm ⟨y, hy⟩, congrArg Subtype.val (β.apply_symm_apply _)⟩
  · intro i
    exact ⟨(hLend i).1.trans (hW0 (endpoint i)), (hLend i).2.trans (hW1 (endpoint i))⟩
  · intro i hi t
    have he : (1 - t.val) * θ i 0 + t.val * θ i 1 = θ i 0 := by
      rw [← hi]; ring
    calc ℓ i t = (β (Circle.exp (θ i 0))).val := by rw [hℓ i t, he]
         _ = τ i 0 := hθ i 0
         _ = b.val.val (endpoint i) := by rw [hτ i 0]; exact H.at_zero _
