import CurveComplexGenusTwo.Topology.ActualSourceGeometry.ActualTopologicalUniversalCoverPROVED

namespace RegionalEmbeddedFamily
open Filter Topology Set Matrix TopologicalSpace Bundle Path.Homotopic.Quotient CurveComplex.LocalSurgery
open scoped Manifold unitInterval ContDiff UpperHalfPlane ENNReal MatrixGroups
set_option maxHeartbeats 4000000

/-- Canonical path-class universal cover from an open contractible neighborhood basis.
Extracted from the existing surface construction, replacing its chart use by the basis. -/
theorem contact_path_class_universal_cover
    {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hbasis : ∀ (x : S) (W : Set S), IsOpen W → x ∈ W →
      ∃ U : Set S, x ∈ U ∧ IsOpen U ∧ U ⊆ W ∧ ContractibleSpace U)
    (x₀ : S) :
    ∃ t : TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z),
      let := t
      SimplyConnectedSpace (Σ z : S, Path.Homotopic.Quotient x₀ z) ∧
      T2Space (Σ z : S, Path.Homotopic.Quotient x₀ z) ∧
      IsCoveringMap (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) ∧
      Function.Surjective (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) := by
  classical
  have hcover
      (x₀ : S) (U : S → Set S) (hU : ∀ i, IsOpen (U i))
      [∀ i, ContractibleSpace (U i)] (hi : ∀ i, i ∈ U i)
      (q : ∀ i, Path x₀ i) (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z) :
      ∃ t : TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z),
        @IsCoveringMap (Σ z : S, Path.Homotopic.Quotient x₀ z) S t _ Sigma.fst ∧
        Function.Surjective (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S) ∧
        ∀ (i : S) (γ : Path.Homotopic.Quotient x₀ i),
          @Continuous (U i) (Σ z : S, Path.Homotopic.Quotient x₀ z) _ t
            (fun z => ⟨(z : S), γ.trans ((mk (p i z)).map
              ⟨Subtype.val, continuous_subtype_val⟩)⟩) := by
    classical
    have hcore
        (x₀ : S) (U : S → Set S) (hU : ∀ i, IsOpen (U i))
        [∀ i, ContractibleSpace (U i)] (hi : ∀ i, i ∈ U i)
        (q : ∀ i, Path x₀ i) (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z) :
        let F := Path.Homotopic.Quotient x₀ x₀
        let _ : TopologicalSpace F := ⊥
        let a : ∀ i z : S, Path.Homotopic.Quotient x₀ z := fun i z =>
          if hz : z ∈ U i then (mk (q i)).trans ((mk (p i ⟨z, hz⟩)).map
            ⟨Subtype.val, continuous_subtype_val⟩) else mk (q z)
        ∃ Z : FiberBundleCore S S F, Z.baseSet = U ∧
          ∀ i j z v, Z.coordChange i j z v = v.trans ((a i z).trans (a j z).symm) := by
      classical
      have htransition
          (x₀ : S) (U V : Set S) (hU : IsOpen U) (hV : IsOpen V)
          [ContractibleSpace U] [ContractibleSpace V]
          (u : U) (v : V) (qU : Path.Homotopic.Quotient x₀ (u : S))
          (qV : Path.Homotopic.Quotient x₀ (v : S))
          (pU : ∀ z : U, Path u z) (pV : ∀ z : V, Path v z) :
          IsLocallyConstant (fun z : ↥(U ∩ V) =>
            (qU.trans ((mk (pU ⟨(z : S), z.property.1⟩)).map
              ⟨Subtype.val, continuous_subtype_val⟩)).trans
            (qV.trans ((mk (pV ⟨(z : S), z.property.2⟩)).map
              ⟨Subtype.val, continuous_subtype_val⟩)).symm) := by
        classical
        have hcohere {S : Type} [TopologicalSpace S] (U W : Set S) [ContractibleSpace U]
            (hWU : W ⊆ U) (u : U) (w z : W)
            (p : Path u ⟨(w : S), hWU w.property⟩)
            (r : Path u ⟨(z : S), hWU z.property⟩) (s : Path w z)
            (x₀ : S) (q : Path.Homotopic.Quotient x₀ (u : S)) :
            q.trans ((mk r).map ⟨Subtype.val, continuous_subtype_val⟩) =
              (q.trans ((mk p).map ⟨Subtype.val, continuous_subtype_val⟩)).trans
                ((mk s).map ⟨Subtype.val, continuous_subtype_val⟩) := by
          let i : C(W, U) := ⟨fun z => ⟨(z : S), hWU z.property⟩, by fun_prop⟩
          let j : C(U, S) := ⟨Subtype.val, continuous_subtype_val⟩
          have hr : mk r = mk (p.trans (s.map i.continuous)) := Subsingleton.elim _ _
          have hmap : (mk (p.trans (s.map i.continuous))).map j =
              ((mk p).map j).trans ((mk s).map ⟨Subtype.val, continuous_subtype_val⟩) := by
            change mk ((p.trans (s.map i.continuous)).map j.continuous) =
              mk ((p.map j.continuous).trans (s.map continuous_subtype_val))
            congr 1
            ext t
            simp only [Path.map_trans]
            rfl
          rw [hr, hmap, trans_assoc]
        have hcancel {S : Type} [TopologicalSpace S] {x₀ w z : S}
            (a b : Path.Homotopic.Quotient x₀ w) (s : Path.Homotopic.Quotient w z) :
            (a.trans s).trans (b.trans s).symm = a.trans b.symm := by
          have hi : (b.trans s).symm = s.symm.trans b.symm := by
            induction b using Quotient.ind
            rename_i b
            induction s using Quotient.ind
            rename_i s
            change mk (b.trans s).symm = mk (s.symm.trans b.symm)
            rw [Path.trans_symm]
          rw [hi, trans_assoc, ← trans_assoc s, trans_symm, refl_trans]
        rw [IsLocallyConstant.iff_exists_open]
        intro z
        obtain ⟨W, hzW, hW, hWUV, hcW⟩ :=
          hbasis (z : S) (U ∩ V) (hU.inter hV) z.property
        let : ContractibleSpace W := hcW
        refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hzW, ?_⟩
        intro z' hz'W
        let w : W := ⟨(z : S), hzW⟩
        let w' : W := ⟨(z' : S), hz'W⟩
        let s : Path w w' := PathConnectedSpace.somePath w w'
        let q : Path.Homotopic.Quotient (z : S) (z' : S) :=
          (mk s).map ⟨Subtype.val, continuous_subtype_val⟩
        have hWU : W ⊆ U := fun y hy => (hWUV hy).1
        have hWV : W ⊆ V := fun y hy => (hWUV hy).2
        have ha := hcohere U W hWU u w w' (pU ⟨(z : S), z.property.1⟩)
          (pU ⟨(z' : S), z'.property.1⟩) s x₀ qU
        have hb := hcohere V W hWV v w w' (pV ⟨(z : S), z.property.2⟩)
          (pV ⟨(z' : S), z'.property.2⟩) s x₀ qV
        rw [ha, hb]
        exact hcancel _ _ q
      dsimp only
      let F := Path.Homotopic.Quotient x₀ x₀
      let : TopologicalSpace F := ⊥
      let : DiscreteTopology F := ⟨rfl⟩
      let a : ∀ i z : S, Path.Homotopic.Quotient x₀ z := fun i z =>
        if hz : z ∈ U i then (mk (q i)).trans ((mk (p i ⟨z, hz⟩)).map
          ⟨Subtype.val, continuous_subtype_val⟩) else mk (q z)
      let k (i j z : S) : F := (a i z).trans (a j z).symm
      have hc (i j : S) : ContinuousOn (k i j) (U i ∩ U j) := by
        rw [continuousOn_iff_continuous_domRestrict]
        have hk := htransition x₀ (U i) (U j) (hU i) (hU j)
          ⟨i, hi i⟩ ⟨j, hi j⟩ (mk (q i)) (mk (q j)) (p i) (p j)
        exact hk.continuous.congr (fun z => by simp [k, a, z.property.1, z.property.2])
      have hcancel {w : S} (b : Path.Homotopic.Quotient x₀ w)
          (c d : Path.Homotopic.Quotient x₀ w) :
          (b.trans c.symm).trans (c.trans d.symm) = b.trans d.symm := by
        rw [trans_assoc, ← trans_assoc c.symm, symm_trans, refl_trans]
      let Z : FiberBundleCore S S F := {
        baseSet := U
        isOpen_baseSet := hU
        indexAt := id
        mem_baseSet_at := hi
        coordChange := fun i j z v => v.trans (k i j z)
        coordChange_self := by
          intro i z hz v
          simp [k]
        continuousOn_coordChange := by
          intro i j
          have hkc : ContinuousOn (fun t : S × F => k i j t.1)
              ((U i ∩ U j) ×ˢ univ) :=
            (hc i j).comp continuous_fst.continuousOn (fun _ ht => ht.1)
          have hop : Continuous (fun t : F × F => t.2.trans t.1) := continuous_of_discreteTopology
          exact hop.comp_continuousOn (hkc.prodMk continuous_snd.continuousOn)
        coordChange_comp := by
          intro i j l z hz v
          change (v.trans (k i j z)).trans (k j l z) = v.trans (k i l z)
          rw [trans_assoc]
          congr 1
          exact hcancel _ _ _ }
      exact ⟨Z, rfl, fun _ _ _ _ => rfl⟩
    let F := Path.Homotopic.Quotient x₀ x₀
    let : TopologicalSpace F := ⊥
    let : DiscreteTopology F := ⟨rfl⟩
    let a : ∀ i z : S, Path.Homotopic.Quotient x₀ z := fun i z =>
      if hz : z ∈ U i then (mk (q i)).trans ((mk (p i ⟨z, hz⟩)).map
        ⟨Subtype.val, continuous_subtype_val⟩) else mk (q z)
    obtain ⟨Z, hZU, hZc⟩ := hcore x₀ U hU hi q p
    let P := Σ z : S, Path.Homotopic.Quotient x₀ z
    let e : P ≃ Z.TotalSpace := {
      toFun := fun z => ⟨z.1, z.2.trans (a (Z.indexAt z.1) z.1).symm⟩
      invFun := fun z => ⟨z.1, z.2.trans (a (Z.indexAt z.1) z.1)⟩
      left_inv := by
        rintro ⟨z, γ⟩
        simp only [trans_assoc, symm_trans, trans_refl]
      right_inv := by
        rintro ⟨z, γ⟩
        change F at γ
        change (⟨z, ((γ : F).trans (a (Z.indexAt z) z)).trans
          (a (Z.indexAt z) z).symm⟩ : Z.TotalSpace) = ⟨z, γ⟩
        congr 1
        rw [trans_assoc, trans_symm, trans_refl] }
    let : TopologicalSpace P := TopologicalSpace.induced e inferInstance
    let E : P ≃ₜ Z.TotalSpace := e.toHomeomorphOfIsInducing (Topology.IsInducing.induced e)
    have hcover : IsCoveringMap Z.proj := FiberBundle.isCoveringMap
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · exact hcover.comp_homeomorph E
    · intro z
      exact ⟨⟨z, mk (q z)⟩, rfl⟩
    · intro i γ
      let v : F := γ.trans (mk (q i)).symm
      let g : U i → S × F := fun z => ((z : S), v)
      have hg : Continuous g := continuous_subtype_val.prodMk continuous_const
      have hgtr : ∀ z : U i, g z ∈ (Z.localTriv i).target := by
        intro z
        rw [Z.mem_localTriv_target, ← Z.baseSet_at, hZU]
        exact z.property
      have hG : Continuous (fun z : U i =>
          E.symm ((Z.localTriv i).toOpenPartialHomeomorph.symm (g z))) :=
        E.symm.continuous.comp
          ((Z.localTriv i).continuousOn_invFun.comp_continuous hg hgtr)
      apply hG.congr
      intro z
      change (⟨(z : S),
        (Z.coordChange i (Z.indexAt (z : S)) (z : S) v).trans
          (a (Z.indexAt (z : S)) (z : S))⟩ : P) = _
      congr 1
      rw [hZc]
      change (v.trans ((a i (z : S)).trans (a (Z.indexAt (z : S)) (z : S)).symm)).trans
        (a (Z.indexAt (z : S)) (z : S)) = _
      simp only [trans_assoc, symm_trans, trans_refl]
      dsimp [v, a]
      rw [dite_eq_left z.property]
      rw [trans_assoc, ← trans_assoc (mk (q i)).symm, symm_trans, refl_trans]
  have hsimply {S : Type} [TopologicalSpace S] (x₀ : S)
      (U : S → Set S) (hU : ∀ i, IsOpen (U i))
      [∀ i, ContractibleSpace (U i)] (hi : ∀ i, i ∈ U i)
      (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z)
      [TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z)]
      (hsheet : ∀ (i : S) (γ : Path.Homotopic.Quotient x₀ i),
        Continuous (fun z : U i => (⟨(z : S), γ.trans ((mk (p i z)).map
          ⟨Subtype.val, continuous_subtype_val⟩)⟩ : Σ z : S, Path.Homotopic.Quotient x₀ z)))
      (hcov : IsCoveringMap (Sigma.fst : (Σ z : S, Path.Homotopic.Quotient x₀ z) → S)) :
      SimplyConnectedSpace (Σ z : S, Path.Homotopic.Quotient x₀ z) := by
    classical
    have hcanonical {S : Type} [TopologicalSpace S] (x₀ : S)
        (U : S → Set S) (hU : ∀ i, IsOpen (U i))
        [∀ i, ContractibleSpace (U i)] (hi : ∀ i, i ∈ U i)
        (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z)
        [TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z)]
        (hsheet : ∀ (i : S) (γ : Path.Homotopic.Quotient x₀ i),
          Continuous (fun z : U i => (⟨(z : S), γ.trans ((mk (p i z)).map
            ⟨Subtype.val, continuous_subtype_val⟩)⟩ : Σ z : S, Path.Homotopic.Quotient x₀ z)))
        (α : C(unitInterval, S)) (γ : Path.Homotopic.Quotient x₀ (α 0)) :
        ∃ L : C(unitInterval, (Σ z : S, Path.Homotopic.Quotient x₀ z)),
          (∀ t, (L t).1 = α t) ∧ L 0 = ⟨α 0, γ⟩ ∧
          L 1 = ⟨α 1, γ.trans ((mk Path.id).map α)⟩ := by
      classical
      have hcont {S : Type} [TopologicalSpace S] (x₀ : S)
          (U : S → Set S) (hU : ∀ i, IsOpen (U i))
          [∀ i, ContractibleSpace (U i)] (hi : ∀ i, i ∈ U i)
          (p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z)
          [TopologicalSpace (Σ z : S, Path.Homotopic.Quotient x₀ z)]
          (hsheet : ∀ (i : S) (γ : Path.Homotopic.Quotient x₀ i),
            Continuous (fun z : U i => (⟨(z : S), γ.trans ((mk (p i z)).map
              ⟨Subtype.val, continuous_subtype_val⟩)⟩ : Σ z : S, Path.Homotopic.Quotient x₀ z)))
          (α : C(unitInterval, S)) (γ : Path.Homotopic.Quotient x₀ (α 0)) :
          let : ContractibleSpace unitInterval :=
            (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
          Continuous (fun t : unitInterval =>
            (⟨α t, γ.trans ((mk (PathConnectedSpace.somePath (0 : unitInterval) t)).map α)⟩ :
              Σ z : S, Path.Homotopic.Quotient x₀ z)) := by
        classical
        let : ContractibleSpace unitInterval :=
          (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
        let : LocallyPathConnectedSpace unitInterval :=
          (isQuotientMap_projIcc (a := (0 : ℝ)) (b := 1) (h := by norm_num)).locallyPathConnectedSpace
        let η (t : unitInterval) := (mk (PathConnectedSpace.somePath (0 : unitInterval) t)).map α
        let Γ (t : unitInterval) : Σ z : S, Path.Homotopic.Quotient x₀ z := ⟨α t, γ.trans (η t)⟩
        change Continuous Γ
        rw [continuous_iff_continuousAt]
        intro t₀
        let i := α t₀
        let A := α ⁻¹' U i
        have hA : IsOpen A := (hU i).preimage α.continuous
        have htA : t₀ ∈ A := hi i
        let J := pathComponentIn A t₀
        have hJ : IsOpen J := hA.pathComponentIn t₀
        have htJ : t₀ ∈ J := mem_pathComponentIn_self htA
        have hJA : J ⊆ A := pathComponentIn_subset
        have hJP : IsPathConnected J := isPathConnected_pathComponentIn htA
        let β : J → U i := fun t => ⟨α t, hJA t.property⟩
        have hβ : Continuous β := by fun_prop
        have hΓJ : Continuous (fun t : J => Γ t) := by
          apply ((hsheet i (γ.trans (η t₀))).comp hβ).congr
          intro t
          obtain ⟨s, hs⟩ := hJP.joinedIn t₀ htJ t t.property
          have hη : η (t : unitInterval) = (η t₀).trans ((mk s).map α) := by
            have hp : mk (PathConnectedSpace.somePath (0 : unitInterval) (t : unitInterval)) =
                mk ((PathConnectedSpace.somePath (0 : unitInterval) t₀).trans s) := Subsingleton.elim _ _
            dsimp [η]
            rw [hp]
            change mk (((PathConnectedSpace.somePath (0 : unitInterval) t₀).trans s).map α.continuous) =
              mk (((PathConnectedSpace.somePath (0 : unitInterval) t₀).map α.continuous).trans
                (s.map α.continuous))
            congr 1
            exact Path.map_trans _ _ _
          let l : Path ⟨i, hi i⟩ (β t) := {
            toFun := fun v => ⟨α (s v), hJA (hs v)⟩
            continuous_toFun := by fun_prop
            source' := by apply Subtype.ext; exact congrArg α s.source
            target' := by apply Subtype.ext; exact congrArg α s.target }
          have hl : mk (p i (β t)) = mk l := Subsingleton.elim _ _
          have hlmap : (mk l).map ⟨Subtype.val, continuous_subtype_val⟩ = (mk s).map α := by
            change mk (l.map continuous_subtype_val) = mk (s.map α.continuous)
            rfl
          change (⟨α t, (γ.trans (η t₀)).trans
            ((mk (p i (β t))).map ⟨Subtype.val, continuous_subtype_val⟩)⟩ :
            Σ z : S, Path.Homotopic.Quotient x₀ z) = Γ t
          rw [hl, hlmap]
          dsimp [Γ]
          congr 1
          rw [hη, trans_assoc]
        have hΓon : ContinuousOn Γ J := continuousOn_iff_continuous_domRestrict.mpr hΓJ
        exact hΓon.continuousAt (hJ.mem_nhds htJ)
      let : ContractibleSpace unitInterval :=
        (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
      let L : C(unitInterval, (Σ z : S, Path.Homotopic.Quotient x₀ z)) :=
        ⟨fun t => ⟨α t, γ.trans ((mk (PathConnectedSpace.somePath (0 : unitInterval) t)).map α)⟩,
          hcont x₀ U hU hi p hsheet α γ⟩
      refine ⟨L, fun _ => rfl, ?_, ?_⟩
      · have hz : mk (PathConnectedSpace.somePath (0 : unitInterval) 0) =
            Path.Homotopic.Quotient.refl 0 := Subsingleton.elim _ _
        change (⟨α 0, γ.trans ((mk (PathConnectedSpace.somePath (0 : unitInterval) 0)).map α)⟩ :
          Σ z : S, Path.Homotopic.Quotient x₀ z) = _
        rw [hz]
        have hmap : (Path.Homotopic.Quotient.refl (0 : unitInterval)).map α =
            Path.Homotopic.Quotient.refl (α 0) := rfl
        rw [hmap, trans_refl]
      · have ho : mk (PathConnectedSpace.somePath (0 : unitInterval) 1) = mk Path.id :=
            Subsingleton.elim _ _
        change (⟨α 1, γ.trans ((mk (PathConnectedSpace.somePath (0 : unitInterval) 1)).map α)⟩ :
          Σ z : S, Path.Homotopic.Quotient x₀ z) = _
        rw [ho]
    have hpc : PathConnectedSpace (Σ z : S, Path.Homotopic.Quotient x₀ z) := by
      let P := Σ z : S, Path.Homotopic.Quotient x₀ z
      let root : P := ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩
      have hroot (y : P) : Joined root y := by
        rcases y with ⟨z, η⟩
        obtain ⟨q⟩ := η
        let α : C(unitInterval, S) := q.toContinuousMap
        let γ : Path.Homotopic.Quotient x₀ (α 0) :=
          (Path.Homotopic.Quotient.refl x₀).cast rfl q.source
        obtain ⟨L, hproj, hz, ho⟩ := hcanonical x₀ U hU hi p hsheet α γ
        have hzero : L 0 = root := by
          rw [hz]
          apply Sigma.ext q.source
          exact Path.Homotopic.Quotient.cast_heq (γ := Path.Homotopic.Quotient.refl x₀) rfl q.source
        have hclass : HEq (γ.trans ((mk Path.id).map α)) (mk q) := by
          change HEq (mk (((Path.refl x₀).cast rfl q.source).trans (Path.id.map α.continuous))) (mk q)
          have he : HEq (mk (((Path.refl x₀).cast rfl q.source).trans (Path.id.map α.continuous)))
              (mk ((Path.refl x₀).trans q)) := Path.Homotopic.hpath_hext (fun _ => rfl)
          apply he.trans
          apply heq_of_eq
          rw [mk_trans, mk_refl, refl_trans]
        have hone : L 1 = ⟨z, mk q⟩ := by
          rw [ho]
          exact Sigma.ext q.target hclass
        exact ⟨⟨L, hzero, hone⟩⟩
      exact ⟨⟨root⟩, fun x y => (hroot x).symm.trans (hroot y)⟩
    rw [simply_connected_iff_loops_nullhomotopic]
    refine ⟨hpc, ?_⟩
    rintro ⟨w, η⟩ δ
    obtain ⟨q⟩ := η
    let x : Σ z : S, Path.Homotopic.Quotient x₀ z := ⟨w, mk q⟩
    let α : Path w w := δ.map hcov.continuous
    let γ : Path.Homotopic.Quotient x₀ (α 0) := (mk q).cast rfl α.source
    obtain ⟨L, hproj, hz, ho⟩ := hcanonical x₀ U hU hi p hsheet α.toContinuousMap γ
    have hzero : L 0 = x := by
      rw [hz]
      apply Sigma.ext α.source
      exact Path.Homotopic.Quotient.cast_heq (γ := mk q) rfl α.source
    have hsame : (L : unitInterval → (Σ z : S, Path.Homotopic.Quotient x₀ z)) = δ :=
      hcov.eq_of_comp_eq L.continuous δ.continuous (funext hproj) 0
        (hzero.trans δ.source.symm)
    have hone : L 1 = x := by rw [hsame]; exact δ.target
    have hh : HEq (γ.trans ((mk Path.id).map α.toContinuousMap)) (mk q) :=
      (Sigma.mk.inj_iff.mp (ho.symm.trans hone)).2
    have he : HEq (γ.trans ((mk Path.id).map α.toContinuousMap)) ((mk q).trans (mk α)) := by
      change HEq (mk ((q.cast rfl α.source).trans (Path.id.map α.continuous))) (mk (q.trans α))
      exact Path.Homotopic.hpath_hext (fun _ => rfl)
    have heq : (mk q).trans (mk α) = mk q := eq_of_heq (he.symm.trans hh)
    have hα : mk α = Path.Homotopic.Quotient.refl w := by
      have hc := congrArg (fun r : Path.Homotopic.Quotient x₀ w => (mk q).symm.trans r) heq
      simpa only [← trans_assoc, symm_trans, refl_trans] using hc
    apply Path.Homotopic.Quotient.eq.mp
    apply hcov.injective_path_homotopic_map
    change mk α = Path.Homotopic.Quotient.refl w
    exact hα
  have hlocal (i : S) : ∃ A : Set S, i ∈ A ∧ IsOpen A ∧ ContractibleSpace A := by
    obtain ⟨A, hi, hA, _, hc⟩ := hbasis i univ isOpen_univ (mem_univ i)
    exact ⟨A, hi, hA, hc⟩
  choose U hi hU hc using hlocal
  let : ∀ i, ContractibleSpace (U i) := hc
  let p : ∀ i, ∀ z : U i, Path ⟨i, hi i⟩ z :=
    fun i z => PathConnectedSpace.somePath ⟨i, hi i⟩ z
  let : StronglyLocallyContractibleSpace S := ⟨fun x => by
    rw [hasBasis_self]
    intro V hV
    obtain ⟨W, hWV, hW, hxW⟩ := mem_nhds_iff.mp hV
    obtain ⟨A, hxA, hA, hAW, hcA⟩ := hbasis x W hW hxW
    exact ⟨A, hA.mem_nhds hxA, hcA, hAW.trans hWV⟩⟩
  let : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
  let q : ∀ i, Path x₀ i := fun i => PathConnectedSpace.somePath x₀ i
  obtain ⟨t, hcov, hsurj, hsheet⟩ := hcover x₀ U hU hi q p
  let := t
  have hsc := hsimply x₀ U hU hi p hsheet hcov
  have ht : T2Space (Σ z : S, Path.Homotopic.Quotient x₀ z) := ⟨fun x y hxy => by
    by_cases he : x.1 = y.1
    · exact hcov.isSeparatedMap x y he hxy
    · obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation he
      exact ⟨Sigma.fst ⁻¹' U, Sigma.fst ⁻¹' V,
        hU.preimage hcov.continuous, hV.preimage hcov.continuous, hx, hy,
        hUV.preimage Sigma.fst⟩⟩
  exact ⟨t, hsc, ht, hcov, hsurj⟩

end RegionalEmbeddedFamily
