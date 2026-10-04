import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteTransverseCrosscutRedrawing

open Lean Elab Tactic in
elab "audit_main14_relative_redrawing_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in relative transverse redrawing: {ax}"
  logInfo m!"Relative transverse redrawing proof axiom audit: {found.toList}"
namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_relative_finite_transverse_crosscut_redrawing
    (M : HyperellipticModel E S) {ι K : Type} [Fintype ι] [Fintype K]
    (old : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
    (e F : K → OpenPartialHomeomorph S Plane) (label : K → Option ι)
    (α β : K → ℝ) (hbounds : ∀ k, 0 < α k ∧ α k < β k ∧ β k < 1)
    (V : Set S) (hFV : ∀ k, (F k).source ⊆ V)
    (hEsub : ∀ k, (F k).source ⊆ (e k).source)
    (hEdis : ∀ i j, i ≠ j → Disjoint (F i).source (F j).source)
    (hEmarks : ∀ k, Disjoint (F k).source (M.cover.branch : Set S))
    (hEsquare : ∀ k, Plane.closedSquare 0 1 ⊆ (F k).target)
    (hcentral : ∀ k, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) ⊆ (F k).source)
    (hEends : ∀ k, F k ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k)) = Plane.mk (-1) 0 ∧
      F k ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k)) = Plane.mk 1 0)
    (hEcurve : ∀ k x, x ∈ (F k).source → (x ∈ a.val.image ↔ F k x 1 = 0))
    (hEslice : ∀ k, {x : S | x ∈ (F k).source ∧ F k x ∈ Plane.closedSquare 0 1} ∩ a.val.image =
      (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k))
    (hlabel : ∀ k j x, x ∈ (e k).source →
      (x ∈ (old j).val.image ↔ label k = some j ∧ e k x 0 = 0))
    (hends : ∀ k j, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) ∉ (old j).val.image ∧
      (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) ∉ (old j).val.image)
    (houtside : ∀ j, Disjoint
      (arcInterior M a \ ⋃ k, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k))
      (old j).val.image) :
    ∃ d : EssentialMarkedArc M, ∃ H : AmbientIsotopy S,
      Quotient.mk (essentialArcSetoid M) d = Quotient.mk (essentialArcSetoid M) a ∧
      d.val.image = H.finalMap '' a.val.image ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
      (∀ t x, x ∉ V → H.map (t,x)=x) ∧
      ∀ j, (arcInterior M d ∩ (old j).val.image).Finite ∧
        ∀ p ∈ arcInterior M d ∩ (old j).val.image, ArcSurgery.CrossesInDisk M (old j) d p := by
  audit_main14_relative_redrawing_base3
    have hReplacement
        {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
        (M : HyperellipticModel E S)
        (c : EssentialMarkedArc M) (K : Type) [Fintype K]
        (E : K → OpenPartialHomeomorph S Schoenflies.Plane)
        (V : Set S) (hEV : ∀ k, (E k).source ⊆ V)
        (hdis : ∀ i j, i ≠ j → Disjoint (E i).source (E j).source)
        (hmarks : ∀ k, Disjoint (E k).source (M.cover.branch : Set S))
        (hSquare : ∀ k, Schoenflies.Plane.closedSquare 0 1 ⊆ (E k).target)
        (A : Set Schoenflies.Plane)
        (hA : Schoenflies.IsArcBetween A (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0))
        (hAi : A \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆
          Schoenflies.Plane.openSquare 0 1)
        (hc : ∀ k, {x : S | x ∈ (E k).source ∧ E k x ∈ Schoenflies.Plane.closedSquare 0 1} ∩
          c.val.image = {x : S | x ∈ (E k).source ∧ E k x ∈ A})
        (B : K → Set Schoenflies.Plane)
        (hB : ∀ k, Schoenflies.IsArcBetween (B k)
          (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0))
        (hBi : ∀ k, B k \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆
          Schoenflies.Plane.openSquare 0 1) :
        ∃ H : AmbientIsotopy S, ∃ d : EssentialMarkedArc M,
          d.val.image = H.finalMap '' c.val.image ∧
          Quotient.mk (essentialArcSetoid M) d = Quotient.mk (essentialArcSetoid M) c ∧
          (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
          (∀ t x, x ∉ V → H.map (t,x)=x) ∧
          d.val.image =
            (c.val.image \ ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ A}) ∪
            ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ B k} := by
      classical
      letI : T2Space S := M.sphere.symm.t2Space
      letI : CompactSpace S := M.sphere.symm.compactSpace
      let Ap : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ A}
      let Bp : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ B k}
      let Dp : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ Plane.openSquare 0 1}
      have hAsquare : A ⊆ Plane.closedSquare 0 1 := by
        intro z hz
        by_cases he : z ∈ ({Plane.mk (-1) 0,Plane.mk 1 0} : Set Plane)
        · rcases he with rfl | he
          · norm_num [Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk]
          · rw [Set.mem_singleton_iff.mp he]
            norm_num [Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk]
        · exact Plane.openSquare_subset_closedSquare 0 1 (hAi ⟨hz,he⟩)
      have hApcurve (k : K) : Ap k ⊆ c.val.image := by
        intro z hz
        have hh : z ∈ {x : S | x ∈ (E k).source ∧ E k x ∈ Plane.closedSquare 0 1} ∩ c.val.image := by
          rw [hc k]
          exact hz
        exact hh.2
      have hDcurve (k : K) : Dp k ∩ c.val.image ⊆ Ap k := by
        intro x hx
        change x ∈ {x : S | x ∈ (E k).source ∧ E k x ∈ A}
        rw [← hc k]
        exact ⟨⟨hx.1.1,Plane.openSquare_subset_closedSquare 0 1 hx.1.2⟩,hx.2⟩
      have hPull (k : K) (F : Set Plane) :
          {x : S | ∃ u : (E k).source, u.val = x ∧
            ((E k).toHomeomorphSourceTarget u : Plane) ∈ F} =
          {x : S | x ∈ (E k).source ∧ E k x ∈ F} := by
        ext x
        constructor
        · rintro ⟨u,rfl,hu⟩
          exact ⟨u.property,hu⟩
        · intro hx
          exact ⟨⟨x,hx.1⟩,rfl,hx.2⟩
      have hpatch (k : K) : ∃ G : AmbientIsotopy S,
          G.finalMap '' Ap k = Bp k ∧ ∀ t x, x ∉ Dp k → G.map (t,x) = x := by
        obtain ⟨G,hGA,hGfix⟩ := position_crosscut_surface_square_support S
          (E k).source (E k).target (E k).open_source (E k).toHomeomorphSourceTarget
          (hSquare k) A (B k) (Plane.mk (-1) 0) (Plane.mk 1 0) hA (hB k)
          (by norm_num [modelCurve,Plane.supNorm,Plane.mk])
          (by norm_num [modelCurve,Plane.supNorm,Plane.mk]) hAi (hBi k)
        rw [hPull,hPull] at hGA
        simp only [hPull] at hGfix
        exact ⟨G,hGA,hGfix⟩
      choose G hGA hGfix using hpatch
      have hGmarks (k : K) (t : Interval) (x : S) (hx : x ∈ M.cover.branch) :
          (G k).map (t,x) = x := by
        apply hGfix k t x
        intro hD
        exact Set.disjoint_left.mp (hmarks k) hD.1 hx
      have hfixRest (k : K) (x : S) (hx : x ∈ c.val.image \ Ap k) : (G k).finalMap x = x := by
        apply hGfix k ⟨1,by norm_num⟩
        intro hD
        exact hx.2 (hDcurve k ⟨hD,hx.1⟩)
      have hfixOther (k j : K) (hkj : k ≠ j) (x : S) (hx : x ∈ (E j).source) :
          (G k).finalMap x = x := by
        apply hGfix k ⟨1,by norm_num⟩
        intro hD
        exact Set.disjoint_left.mp (hdis k j hkj) hD.1 hx
      have hcompose (H G : AmbientIsotopy S) :
          ∃ K : AmbientIsotopy S, ∀ t x, K.map (t,x) = G.map (t,H.map (t,x)) := by
        refine ⟨{
          map := ⟨fun z => G.map (z.1,H.map z),
          G.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩,
          homeomorphism_at := ?_, at_zero := ?_ },fun _ _ => rfl⟩
        · intro t
          obtain ⟨e,he⟩ := H.homeomorphism_at t
          obtain ⟨f,hf⟩ := G.homeomorphism_at t
          exact ⟨e.trans f,fun x => (hf (e x)).trans
            (congrArg (fun z => G.map (t,z)) (he x))⟩
        · intro x
          change G.map (⟨0,by norm_num⟩,H.map (⟨0,by norm_num⟩,x)) = x
          rw [H.at_zero,G.at_zero]
      let As : Finset K → Set S := fun P => ⋃ k ∈ P, Ap k
      let Bs : Finset K → Set S := fun P => ⋃ k ∈ P, Bp k
      have hbuild (P : Finset K) : ∃ H : AmbientIsotopy S,
          H.finalMap '' c.val.image = (c.val.image \ As P) ∪ Bs P ∧
          (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
          (∀ t x, x ∉ V → H.map (t,x)=x) := by
        induction P using Finset.induction_on with
        | empty =>
          let H : AmbientIsotopy S := {
            map := ⟨fun z => z.2,continuous_snd⟩
            homeomorphism_at := fun _ => ⟨Homeomorph.refl S,fun _ => rfl⟩
            at_zero := fun _ => rfl }
          refine ⟨H,?_,(fun _ _ _ => rfl),(fun _ _ _ => rfl)⟩
          change (fun x : S => x) '' c.val.image = _
          simp [As,Bs]
        | @insert k P hk ih =>
          obtain ⟨H,hH,hHmarks,hHout⟩ := ih
          have hAsinsert : As (insert k P) = Ap k ∪ As P := by simp [As]
          have hBsinsert : Bs (insert k P) = Bp k ∪ Bs P := by simp [Bs]
          have hnotAs (x : S) (hx : x ∈ Ap k) : x ∉ As P := by
            intro h
            obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp h
            have hkj : k ≠ j := fun he => hk (he.symm ▸ hj)
            exact Set.disjoint_left.mp (hdis k j hkj) hx.1 hxj.1
          let R : Set S := (c.val.image \ As (insert k P)) ∪ Bs P
          have hdecomp : (c.val.image \ As P) ∪ Bs P = Ap k ∪ R := by
            ext x
            constructor
            · intro hx
              rcases hx with hx | hx
              · by_cases hxA : x ∈ Ap k
                · exact Or.inl hxA
                · exact Or.inr (Or.inl ⟨hx.1,by rw [hAsinsert]; exact fun h => h.elim hxA hx.2⟩)
              · exact Or.inr (Or.inr hx)
            · intro hx
              rcases hx with hx | hx
              · exact Or.inl ⟨hApcurve k hx,hnotAs x hx⟩
              · rcases hx with hx | hx
                · exact Or.inl ⟨hx.1,fun h => hx.2 (hAsinsert.symm ▸ Or.inr h)⟩
                · exact Or.inr hx
          have hRfix (x : S) (hx : x ∈ R) : (G k).finalMap x = x := by
            rcases hx with hx | hx
            · apply hfixRest k x
              refine ⟨hx.1,?_⟩
              intro h
              exact hx.2 (hAsinsert.symm ▸ Or.inl h)
            · obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp hx
              exact hfixOther k j (fun he => hk (he.symm ▸ hj)) x hxj.1
          have hGR : (G k).finalMap '' R = R := by
            ext x
            constructor
            · rintro ⟨y,hy,rfl⟩
              simpa [hRfix y hy] using hy
            · intro hx
              exact ⟨x,hx,hRfix x hx⟩
          have hnew : (G k).finalMap '' ((c.val.image \ As P) ∪ Bs P) =
              (c.val.image \ As (insert k P)) ∪ Bs (insert k P) := by
            rw [hdecomp,Set.image_union,hGA k,hGR,hBsinsert]
            change Bp k ∪ ((c.val.image \ As (insert k P)) ∪ Bs P) =
              (c.val.image \ As (insert k P)) ∪ (Bp k ∪ Bs P)
            ext x
            simp only [Set.mem_union]
            tauto
          obtain ⟨F,hF⟩ := hcompose H (G k)
          refine ⟨F,?_,?_,?_⟩
          · have hmaps : F.finalMap = (G k).finalMap ∘ H.finalMap :=
              funext (hF ⟨1,by norm_num⟩)
            calc
              F.finalMap '' c.val.image = (G k).finalMap '' (H.finalMap '' c.val.image) := by
                rw [Set.image_image,hmaps]
                rfl
              _ = _ := by rw [hH,hnew]
          · intro t x hx
            rw [hF,hHmarks t x hx]
            exact hGmarks k t x hx
          · intro t x hx
            rw [hF,hHout t x hx]
            apply hGfix k t x
            exact fun hD => hx (hEV k hD.1)
      obtain ⟨H,hH,hHmarks,hHout⟩ := hbuild Finset.univ
      obtain ⟨h,hh⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
      have hfinal : H.finalMap = h := funext (fun x => (hh x).symm)
      have hfix : ∀ x, x ∈ M.cover.branch → h x = x := by
        intro x hx
        rw [← hfinal]
        exact hHmarks ⟨1,by norm_num⟩ x hx
      let d := c.transport h hfix
      have hd : d.val.image = H.finalMap '' c.val.image := by
        rw [hfinal]
        exact MarkedArc.transport_image c.val h hfix
      refine ⟨H,d,hd,?_,hHmarks,hHout,?_⟩
      · apply Eq.symm
        apply Quotient.sound
        exact ⟨H,hHmarks,hd.symm⟩
      · rw [hd,hH]
        simp [As,Bs,Ap,Bp]
    classical
    have hhorizontal : segment ℝ (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) =
        {z : Schoenflies.Plane | z ∈ Schoenflies.Plane.closedSquare 0 1 ∧ z 1 = 0} := by
      ext z
      constructor
      · intro hz
        rw [segment_eq_image_lineMap] at hz
        obtain ⟨t,ht,rfl⟩ := hz
        have h0 : (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0)
            (Schoenflies.Plane.mk 1 0) t) 0 = 2*t-1 := by
          simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]; ring
        have h1 : (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0)
            (Schoenflies.Plane.mk 1 0) t) 1 = 0 := by
          simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]
        refine ⟨?_,h1⟩
        change Schoenflies.Plane.supDist (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) t) 0 ≤ 1
        simp only [Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,sub_zero]
        rw [h0,h1,abs_zero,max_le_iff]
        constructor
        · rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
        · norm_num
      · intro hz
        have hnorm : Schoenflies.Plane.supNorm z ≤ 1 := by
          simpa [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist] using hz.1
        have hbound : |z 0| ≤ 1 :=
          (Schoenflies.Plane.abs_zero_le_supNorm z).trans hnorm
        rw [abs_le] at hbound
        rw [segment_eq_image_lineMap]
        refine ⟨(z 0+1)/2,⟨by linarith [hbound.1],by linarith [hbound.2]⟩,?_⟩
        ext i
        fin_cases i
        · simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]; ring
        · simpa [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk] using hz.2.symm
    let A : Set Schoenflies.Plane := segment ℝ (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0)
    have hA : Schoenflies.IsArcBetween A (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) :=
      Schoenflies.isArcBetween_segment (by intro h; have hh := congrArg (fun z : Schoenflies.Plane => z 0) h; norm_num [Schoenflies.Plane.mk] at hh)
    have hAi : A \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆
        Schoenflies.Plane.openSquare 0 1 := by
      intro z hz
      have hzline := hhorizontal.le hz.1
      have h0 : |z 0| ≤ 1 := by
        have hnorm : Schoenflies.Plane.supNorm z ≤ 1 := by
          simpa [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist] using hzline.1
        exact (Schoenflies.Plane.abs_zero_le_supNorm z).trans hnorm
      have hne0 : z 0 ≠ -1 := by
        intro h
        apply hz.2
        left
        ext i
        fin_cases i
        · simpa [Schoenflies.Plane.mk] using h
        · simpa [Schoenflies.Plane.mk] using hzline.2
      have hne1 : z 0 ≠ 1 := by
        intro h
        apply hz.2
        right
        apply Set.mem_singleton_iff.mpr
        ext i
        fin_cases i
        · simpa [Schoenflies.Plane.mk] using h
        · simpa [Schoenflies.Plane.mk] using hzline.2
      rw [Schoenflies.Plane.mem_openSquare_iff]
      intro i
      fin_cases i
      · simp only [PiLp.zero_apply,sub_zero]
        rw [abs_lt]
        exact ⟨lt_of_le_of_ne (abs_le.mp h0).1 hne0.symm,
          lt_of_le_of_ne (abs_le.mp h0).2 hne1⟩
      · simp [hzline.2]
    have hselected (k : K) :
        {x : S | x ∈ (F k).source ∧ F k x ∈ A} =
        (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) := by
      rw [← hEslice k]
      ext x
      constructor
      · intro hx
        have hz := hhorizontal.le hx.2
        exact ⟨⟨hx.1,hz.1⟩,(hEcurve k x hx.1).mpr hz.2⟩
      · intro hx
        exact ⟨hx.1.1,hhorizontal.ge ⟨hx.1.2,(hEcurve k x hx.1.1).mp hx.2⟩⟩
    have hactual (k : K) :
        {x : S | x ∈ (F k).source ∧ F k x ∈ Schoenflies.Plane.closedSquare 0 1} ∩ a.val.image =
        {x : S | x ∈ (F k).source ∧ F k x ∈ A} := (hEslice k).trans (hselected k).symm
    let T : K → OpenPartialHomeomorph Schoenflies.Plane Schoenflies.Plane :=
      fun k => (F k).symm.trans (e k)
    have hTsquare (k : K) : Schoenflies.Plane.closedSquare 0 1 ⊆ (T k).source := by
      intro z hz
      have hzE : z ∈ (F k).target := hEsquare k hz
      exact ⟨hzE,hEsub k ((F k).symm.map_source hzE)⟩
    have hleftSource (k : K) : (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) ∈ (F k).source :=
      hcentral k (Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr (hbounds k).2.1.le))
    have hrightSource (k : K) : (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) ∈ (F k).source :=
      hcentral k (Set.mem_image_of_mem _ (Set.right_mem_Icc.mpr (hbounds k).2.1.le))
    have hleftInv (k : K) : (F k).symm (Schoenflies.Plane.mk (-1) 0) =
        (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) := by
      rw [← (hEends k).1,(F k).left_inv (hleftSource k)]
    have hrightInv (k : K) : (F k).symm (Schoenflies.Plane.mk 1 0) =
        (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) := by
      rw [← (hEends k).2,(F k).left_inv (hrightSource k)]
    have hTargets (k : K) : ∃ B : Set Schoenflies.Plane,
        Schoenflies.IsArcBetween B (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) ∧
        B \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆ Schoenflies.Plane.openSquare 0 1 ∧
        ∀ j, label k = some j → ((T k '' B) ∩ {z : Schoenflies.Plane | z 0 = 0}).Finite ∧
          ∀ p ∈ (T k '' B) ∩ {z : Schoenflies.Plane | z 0 = 0},
          ∃ W : Set Schoenflies.Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ (T k).target ∧
          ∃ m : ℝ, ∀ z ∈ W, (z ∈ T k '' B ↔ z 1 = p 1 + m*z 0) := by
      cases hL : label k with
      | none =>
        refine ⟨A,hA,hAi,?_⟩
        intro j hj
        cases hj
      | some j =>
        have ha0 : T k (Schoenflies.Plane.mk (-1) 0) 0 ≠ 0 := by
          intro h0
          have hh : (e k) ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k)) 0 = 0 := by
            simpa only [T,OpenPartialHomeomorph.trans_apply,hleftInv] using h0
          exact (hends k j).1 ((hlabel k j _ (hEsub k (hleftSource k))).mpr ⟨hL,hh⟩)
        have hb0 : T k (Schoenflies.Plane.mk 1 0) 0 ≠ 0 := by
          intro h0
          have hh : (e k) ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k)) 0 = 0 := by
            simpa only [T,OpenPartialHomeomorph.trans_apply,hrightInv] using h0
          exact (hends k j).2 ((hlabel k j _ (hEsub k (hrightSource k))).mpr ⟨hL,hh⟩)
        obtain ⟨B,hB,hBi,hfinite,hgraph⟩ := position_proper_affine_crosscut (T k) (hTsquare k) ha0 hb0
        exact ⟨B,hB,hBi,fun _ _ => ⟨hfinite,hgraph⟩⟩
    choose B hB hBi hBcontrol using hTargets
    obtain ⟨G,d,hdimage,hdclass,hGmarks,hGout,hdreplace⟩ := hReplacement
      M a K F V hFV hEdis hEmarks hEsquare A hA hAi hactual B hB hBi
    let Bp : K → Set S := fun k => {x | x ∈ (F k).source ∧ F k x ∈ B k}
    have hfinite (k : K) (j : ι) : (Bp k ∩ (old j).val.image).Finite := by
      by_cases hj : label k = some j
      · apply (((hBcontrol k j hj).1).image (e k).symm).subset
        rintro x ⟨hx,hxold⟩
        have hxE : x ∈ (e k).source := hEsub k hx.1
        refine ⟨e k x,⟨?_,((hlabel k j x hxE).mp hxold).2⟩,(e k).left_inv hxE⟩
        refine ⟨F k x,hx.2,?_⟩
        simp only [T,OpenPartialHomeomorph.trans_apply]
        rw [(F k).left_inv hx.1]
      · apply Set.Finite.subset Set.finite_empty
        rintro x ⟨hx,hxold⟩
        exact (hj ((hlabel k j x (hEsub k hx.1)).mp hxold).1).elim
    have hfiniteD (j : ι) : (arcInterior M d ∩ (old j).val.image).Finite := by
      apply (Set.finite_iUnion (fun k => hfinite k j)).subset
      rintro x ⟨hx,hxold⟩
      have hximage : x ∈ d.val.image := hx.1
      rw [hdreplace] at hximage
      rcases hximage with hxrest | hxnew
      · have hxA : x ∈ arcInterior M a := ⟨hxrest.1,hx.2⟩
        have hxoutside : x ∈ arcInterior M a \ ⋃ k,
            (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) := by
          refine ⟨hxA,?_⟩
          intro hh
          obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hh
          exact hxrest.2 (Set.mem_iUnion.mpr ⟨k,(hselected k).symm ▸ hk⟩)
        exact (Set.disjoint_left.mp (houtside j) hxoutside hxold).elim
      · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hxnew
        exact Set.mem_iUnion.mpr ⟨k,hk,hxold⟩
    have hBsq (k : K) : B k ⊆ Schoenflies.Plane.closedSquare 0 1 := by
      intro z hz
      by_cases he : z ∈ ({Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} : Set Schoenflies.Plane)
      · rcases he with rfl | he
        · norm_num [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,Schoenflies.Plane.mk]
        · rw [Set.mem_singleton_iff.mp he]
          norm_num [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,Schoenflies.Plane.mk]
      · exact Schoenflies.Plane.openSquare_subset_closedSquare 0 1 (hBi k ⟨hz,he⟩)
    have hd2local (k : K) (x : S) (hx : x ∈ (F k).source)
        (hxo : F k x ∈ Schoenflies.Plane.openSquare 0 1) :
        x ∈ d.val.image ↔ F k x ∈ B k := by
      rw [hdreplace]
      constructor
      · intro h
        rcases h with h | h
        · have hAselect : x ∈ {x : S | x ∈ (F k).source ∧ F k x ∈ A} := by
            rw [← hactual k]
            exact ⟨⟨hx,Schoenflies.Plane.openSquare_subset_closedSquare 0 1 hxo⟩,h.1⟩
          exact False.elim (h.2 (Set.mem_iUnion.mpr ⟨k,hAselect⟩))
        · obtain ⟨l,hl⟩ := Set.mem_iUnion.mp h
          by_cases hkl : k = l
          · subst l
            exact hl.2
          · exact False.elim (Set.disjoint_left.mp (hEdis k l hkl) hx hl.1)
      · intro h
        exact Or.inr (Set.mem_iUnion.mpr ⟨k,hx,h⟩)
    have hTimage (k : K) (x : S) (hx : x ∈ (F k).source) :
        e k x ∈ T k '' B k ↔ F k x ∈ B k := by
      constructor
      · rintro ⟨z,hz,heq⟩
        have hzT := hTsquare k (hBsq k hz)
        have hzE : z ∈ (F k).target := hzT.1
        have hze : (F k).symm z ∈ (e k).source := hzT.2
        have hsymm : (F k).symm z = x :=
          (e k).injOn hze (hEsub k hx) heq
        have hzcoord : z = F k x := by rw [← hsymm,(F k).right_inv hzE]
        exact hzcoord ▸ hz
      · intro hz
        refine ⟨F k x,hz,?_⟩
        change e k ((F k).symm (F k x)) = e k x
        rw [(F k).left_inv hx]
    refine ⟨d,G,hdclass,hdimage,hGmarks,hGout,?_⟩
    intro j
    refine ⟨hfiniteD j,?_⟩
    intro p hp
    have hpBunion : p ∈ ⋃ k, {x : S | x ∈ (F k).source ∧ F k x ∈ B k} := by
      have hpd : p ∈ d.val.image := hp.1.1
      rw [hdreplace] at hpd
      rcases hpd with hrem | hBmem
      · have hrem' : p ∈ arcInterior M a \ ⋃ k,
            (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) := by
          refine ⟨⟨hrem.1,hp.1.2⟩,?_⟩
          intro hh
          obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hh
          exact hrem.2 (Set.mem_iUnion.mpr ⟨k,(hselected k).symm ▸ hk⟩)
        exact False.elim (Set.disjoint_left.mp (houtside j) hrem' hp.2)
      · exact hBmem
    obtain ⟨k,hpk⟩ := Set.mem_iUnion.mp hpBunion
    have hpe : p ∈ (e k).source := hEsub k hpk.1
    have hplabel : label k = some j := ((hlabel k j p hpe).mp hp.2).1
    have hp0 : e k p 0 = 0 := ((hlabel k j p hpe).mp hp.2).2
    have hpint : F k p ∈ Schoenflies.Plane.openSquare 0 1 := by
      apply hBi k
      refine ⟨hpk.2,?_⟩
      intro he
      rcases he with he | he
      · have hpa : p = (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) := by
          rw [← hleftInv k,← he,(F k).left_inv hpk.1]
        exact (hends k j).1 (hpa ▸ hp.2)
      · have hpb : p = (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) := by
          rw [← hrightInv k,← Set.mem_singleton_iff.mp he,(F k).left_inv hpk.1]
        exact (hends k j).2 (hpb ▸ hp.2)
    have hpT : e k p ∈ T k '' B k := (hTimage k p hpk.1).mpr hpk.2
    obtain ⟨W,hWo,hpW,hWtarget,m,hm⟩ := (hBcontrol k j hplabel).2 (e k p) ⟨hpT,hp0⟩
    have hnear : (F k).source ∩ ((F k) ⁻¹' Schoenflies.Plane.openSquare 0 1 ∩ (e k) ⁻¹' W) ∈ nhds p :=
      Filter.inter_mem ((F k).open_source.mem_nhds hpk.1)
        (Filter.inter_mem (((F k).continuousAt hpk.1).preimage_mem_nhds
          ((Schoenflies.Plane.isOpen_openSquare 0 1).mem_nhds hpint))
          (((e k).continuousAt hpe).preimage_mem_nhds (hWo.mem_nhds hpW)))
    obtain ⟨V,hVsub,hVo,hpV⟩ := mem_nhds_iff.mp hnear
    let F := (e k).restr V
    have hFsource : F.source = (e k).source ∩ V := by
      rw [OpenPartialHomeomorph.restr_source,hVo.interior_eq]
    have hpF : p ∈ F.source := hFsource.symm ▸ ⟨hpe,hpV⟩
    apply actual_affine_graph_crosses_in_disk M (old j) d F p hpF
      ((hEmarks k).mono (fun x hx => (hVsub (hFsource.le hx).2).1) Set.Subset.rfl) hp0 m
    · intro x hx
      have hxe := (hFsource.le hx).1
      change x ∈ (old j).val.image ↔ e k x 0 = 0
      simpa only [hplabel,eq_self,true_and] using hlabel k j x hxe
    · intro x hx
      have hxV := (hFsource.le hx).2
      have hxloc := hVsub hxV
      change x ∈ d.val.image ↔ e k x 1 = e k p 1+m*e k x 0
      rw [hd2local k x hxloc.1 hxloc.2.1,← hTimage k x hxloc.1]
      exact hm (e k x) hxloc.2.2

end CurveComplex.HyperellipticModel
