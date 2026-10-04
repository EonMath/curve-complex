import CurveComplexGenusTwo.Topology.ActualNoTriplePosition.MarkedGermRadialCore
import CurveComplexGenusTwo.Topology.ActualNoTriplePosition.SupportedUnitBend

namespace CurveComplex.HyperellipticModel
open Set Schoenflies Topology

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

noncomputable section

theorem actual_centered_chart_from_crossing
    (M : HyperellipticModel E S)
    (c d : EssentialMarkedArc M) (p : S)
    (hp : ArcSurgery.CrossesInDisk M c d p) :
    ∃ F : OpenPartialHomeomorph S Plane,
      p ∈ F.source ∧ F p = 0 ∧
      Disjoint F.source (M.cover.branch : Set S) ∧
      (∀ x ∈ F.source, x ∈ c.val.image ↔ F x 1 = 0) ∧
      (∀ x ∈ F.source, x ∈ d.val.image ↔ F x 0 = 0) := by
  obtain ⟨U,hU,hpU,hfree,e,hep,hc,hd⟩ := hp
  have : Nonempty U := ⟨⟨p,hpU⟩⟩
  let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
  have hV : IsOpen V :=
    (isOpen_lt (continuous_fst.abs) continuous_const).inter
      (isOpen_lt (continuous_snd.abs) continuous_const)
  let coeU : OpenPartialHomeomorph U S :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  let f : U → ℝ × ℝ := fun u => (e u).val
  have hf : IsOpenEmbedding f := hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  let coeE : OpenPartialHomeomorph U (ℝ × ℝ) := hf.toOpenPartialHomeomorph f
  let G := coeU.symm.trans coeE
  have hGsource : G.source = U := by
    simp [G,coeU,coeE,IsOpenEmbedding.toOpenPartialHomeomorph_target]
  have hGp : G p = (0,0) := by
    have hu : coeU.symm p = ⟨p,hpU⟩ :=
      hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv
        (x := ⟨p,hpU⟩)
    change f (coeU.symm p) = _
    rw [hu]
    exact hep
  let L : Plane ≃ₜ ℝ × ℝ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
  let F := G.trans L.symm.toOpenPartialHomeomorph
  have hFsource : F.source = G.source := by simp [F]
  have hGvalue (x : S) (hx : x ∈ G.source) :
      G x = (e ⟨x,hGsource ▸ hx⟩).val := by
    have hu : coeU.symm x = ⟨x,hGsource ▸ hx⟩ :=
      hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv
        (x := ⟨x,hGsource ▸ hx⟩)
    change f (coeU.symm x) = _
    rw [hu]
  refine ⟨F,hFsource.symm ▸ hGsource.symm ▸ hpU,?_,?_,?_,?_⟩
  · change L.symm (G p) = 0
    rw [hGp]
    ext i
    fin_cases i <;> rfl
  · exact hfree.mono_left (fun x hx => hGsource ▸ (hFsource ▸ hx))
  · intro x hx
    have hxG : x ∈ G.source := hFsource ▸ hx
    have hxU : x ∈ U := hGsource ▸ hxG
    have hval := hGvalue x hxG
    change x ∈ c.val.image ↔ (L.symm (G x) : Plane) 1 = 0
    rw [hval]
    simpa [L] using hc ⟨x,hxU⟩
  · intro x hx
    have hxG : x ∈ G.source := hFsource ▸ hx
    have hxU : x ∈ U := hGsource ▸ hxG
    have hval := hGvalue x hxG
    change x ∈ d.val.image ↔ (L.symm (G x) : Plane) 0 = 0
    rw [hval]
    simpa [L] using hd ⟨x,hxU⟩

theorem actual_centered_chart_avoiding_nonincident_family
    (M : HyperellipticModel E S) {K : Type} [Fintype K]
    (c d : EssentialMarkedArc M) (u : K → EssentialMarkedArc M)
    (p : S) (hp : ArcSurgery.CrossesInDisk M c d p)
    (hnot : ∀ k, p ∉ (u k).val.image) :
    ∃ F : OpenPartialHomeomorph S Plane,
      p ∈ F.source ∧ F p = 0 ∧
      Disjoint F.source (M.cover.branch : Set S) ∧
      ∀ k, Disjoint F.source (u k).val.image := by
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨F₀,hpF₀,hzero,hmarks,haxisC,haxisD⟩ :=
    actual_centered_chart_from_crossing M c d p hp
  let B : Set S := ⋃ k : K, (u k).val.image
  have hB : IsClosed B := isClosed_iUnion_of_finite (fun k =>
    (isCompact_range (u k).val.continuous).isClosed)
  have hpB : p ∉ B := by
    intro h
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp h
    exact hnot k hk
  let O : Set S := F₀.source \ B
  have hO : IsOpen O := F₀.open_source.sdiff hB
  have hpO : p ∈ O := ⟨hpF₀,hpB⟩
  let F := F₀.restrOpen O hO
  refine ⟨F,⟨hpF₀,hpO⟩,hzero,
    hmarks.mono_left (fun x hx => hx.1),?_⟩
  intro k
  apply Set.disjoint_left.mpr
  intro x hx hxu
  exact hx.2.2 (Set.mem_iUnion.mpr ⟨k,hxu⟩)

theorem actual_crossing_persists_off_closed_support
    (M : HyperellipticModel E S)
    (c c' b : EssentialMarkedArc M) (p : S)
    (hc : ArcSurgery.CrossesInDisk M c b p)
    (K : Set S) (hK : IsClosed K) (hpK : p ∉ K)
    (hagree : ∀ x, x ∉ K →
      (x ∈ c'.val.image ↔ x ∈ c.val.image)) :
    ArcSurgery.CrossesInDisk M c' b p := by
  obtain ⟨F,hpF,hFp,hmarks,haxisC,haxisB⟩ :=
    actual_centered_chart_from_crossing M c b p hc
  let O : Set S := F.source \ K
  have hO : IsOpen O := F.open_source.sdiff hK
  have hpO : p ∈ O := ⟨hpF,hpK⟩
  let G := F.restrOpen O hO
  have hpG : p ∈ G.source := ⟨hpF,hpO⟩
  have hGmarks : Disjoint G.source (M.cover.branch : Set S) :=
    hmarks.mono_left (fun x hx => hx.1)
  have hp0 : G p 0 = 0 := by
    change F p 0 = 0
    rw [hFp]
    rfl
  have hold (x : S) (hx : x ∈ G.source) :
      x ∈ b.val.image ↔ G x 0 = 0 := haxisB x hx.1
  have hnew (x : S) (hx : x ∈ G.source) :
      x ∈ c'.val.image ↔ G x 1 = G p 1 + (0 : ℝ) * G x 0 := by
    change x ∈ c'.val.image ↔ F x 1 = F p 1 + (0 : ℝ) * F x 0
    rw [hFp]
    simpa using (hagree x hx.2.2).trans (haxisC x hx.1)
  exact ArcSurgery.crossesSymm M b c' p
    (actual_affine_graph_crosses_in_disk M b c' G p hpG
      hGmarks hp0 0 hold hnew)

theorem actual_unit_bend_all_incident_transverse
    (M : HyperellipticModel E S)
    (c d b : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane) (p : S)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (hmarks : Disjoint F.source (M.cover.branch : Set S))
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target)
    (v w : Plane) (hv : 0 < v 1) (hw : w 1 < 0)
    (haxis : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ c.val.image ↔ F x 1 = 0))
    (hmodel : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ b.val.image ↔ F x ∈ segment ℝ (0 : Plane) v ∪
        segment ℝ (0 : Plane) w))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsmall : δ * |v 0| < (1 / 2 : ℝ) * v 1)
    (hinside : δ < v 1)
    (himage : d.val.image =
      (c.val.image \
        {x : S | x ∈ F.source ∧ F x ∈
          segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
        {x : S | x ∈ F.source ∧
          F x ∈ ArcSurgery.bendGraph (1 / 2) 1 δ})
    (hOldTrans : ∀ q ∈ ArcSurgery.crossings M c b,
      ArcSurgery.CrossesInDisk M c b q) :
    ∀ q ∈ ArcSurgery.crossings M d b,
      ArcSurgery.CrossesInDisk M d b q := by
  let K : Set S := F.symm '' Plane.closedSquare 0 1
  letI : T2Space S := M.sphere.symm.t2Space
  have hK : IsClosed K :=
    (ArcSurgery.actual_unit_square_support_compact M F hSquare).isClosed
  have hagree := ArcSurgery.actual_supported_unit_bend_agrees_outside_square
    M c d F hSquare δ hδ hδ1 himage
  have hold := ArcSurgery.actual_unit_bend_old_crossing_singleton M c b F p
    hpF hFp hmarks v w (ne_of_gt hv) (ne_of_lt hw) haxis hmodel
  have huniq := ArcSurgery.actual_unit_square_old_crossing_unique M c b F p
    hpF hFp hmarks hSquare v w hv hw haxis hmodel
  have hnew := ArcSurgery.actual_unit_bend_new_crossing_singleton M b F hmarks
    hSquare v w hv hw hmodel δ hδ hδ1 hsmall hinside
  have hformula := ArcSurgery.actual_supported_unit_bend_crossings_formula
    M c d b F δ himage
  rw [hnew] at hformula
  intro q hq
  have hq' := hformula ▸ hq
  rcases hq' with hqold | hqnew
  · have hqK : q ∉ K := by
      intro hqK
      have he := huniq q hqold.1 hqK
      have hpA : p ∈ {x : S | x ∈ F.source ∧
          F x ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)} := by
        have hp : p ∈ ({p} : Set S) := Set.mem_singleton p
        exact (hold.symm ▸ hp).2
      exact hqold.2 (he ▸ hpA)
    exact actual_crossing_persists_off_closed_support M c d b q
      (hOldTrans q hqold.1) K hK hqK hagree
  · have he : q = F.symm (Plane.mk (δ * v 0 / v 1) δ) :=
      Set.mem_singleton_iff.mp hqnew
    subst q
    exact ArcSurgery.actual_unit_bend_radial_new_contact_transverse
      M c d b F hmarks hSquare v w hv hw haxis hmodel
      δ hδ hδ1 hsmall hinside himage

theorem actual_oriented_incident_unit_chart
    (M : HyperellipticModel E S) {J : Type} [Fintype J]
    (c : EssentialMarkedArc M) (b : J → EssentialMarkedArc M)
    (p : S) (hpmark : p ∉ M.cover.branch)
    (hpc : p ∈ c.val.image) (hpb : ∀ j, p ∈ (b j).val.image)
    (hfinite : ∀ i k : Option J, i ≠ k →
      (ArcSurgery.crossings M
        (Option.elim i c b) (Option.elim k c b)).Finite)
    (hcross : ∀ j, ArcSurgery.CrossesInDisk M c (b j) p)
    (E0 : OpenPartialHomeomorph S Plane)
    (hpE : p ∈ E0.source) (hEp : E0 p = 0)
    (hmarkE : Disjoint E0.source (M.cover.branch : Set S))
    (C : Set S) (hC : C.Finite)
    (hCcontains : ∀ j, ArcSurgery.crossings M c (b j) ⊆ C) :
    ∃ F : OpenPartialHomeomorph S Plane, ∃ v w : J → Plane,
      p ∈ F.source ∧ F p = 0 ∧
      F.source ⊆ E0.source ∧
      Disjoint F.source (M.cover.branch : Set S) ∧
      Plane.closedSquare 0 1 ⊆ F.target ∧
      (∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
        (x ∈ c.val.image ↔ F x 1 = 0)) ∧
      (∀ j x, x ∈ F.source → F x ∈ Plane.closedSquare 0 1 →
        (x ∈ (b j).val.image ↔ F x ∈ segment ℝ (0 : Plane) (v j) ∪
          segment ℝ (0 : Plane) (w j))) ∧
      (∀ j, 0 < (v j) 1 ∧ (w j) 1 < 0) ∧
      (∀ j k, j ≠ k →
        Disjoint (segment ℝ (0 : Plane) (v j) \ {0})
          (segment ℝ (0 : Plane) (v k) \ {0})) := by
  let r : Option J → EssentialMarkedArc M := fun i => Option.elim i c b
  obtain ⟨G,hpG,hGp,hGsource,hGdis⟩ :=
    actual_isolate_finite_contact_chart M E0 p hpE hEp C hC
  have hGmarks : Disjoint G.source (M.cover.branch : Set S) :=
    hmarkE.mono_left hGsource
  have hpR : ∀ i : Option J, p ∈ (r i).val.image := by
    intro i
    cases i with
    | none => exact hpc
    | some j => exact hpb j
  obtain ⟨F,a,d,hsource,hzero,hSquare,haxis,hmodel,hdistinct⟩ :=
    actual_unit_square_radial_chart_from_interior_fan M r p hpmark hpR
      hfinite G hpG hGp none
  have hpF : p ∈ F.source := hsource.symm ▸ hpG
  have hFmarks : Disjoint F.source (M.cover.branch : Set S) :=
    hGmarks.mono_left (hsource ▸ Subset.rfl)
  have hmeet (j : J) (x : S) (hx : x ∈ F.source)
      (hxc : x ∈ c.val.image ∩ (b j).val.image) : x = p := by
    have hxG : x ∈ G.source := hsource ▸ hx
    have hxnotmark : x ∉ (M.cover.branch : Set S) :=
      fun hm => Set.disjoint_left.mp hGmarks hxG hm
    have hxC : x ∈ C := hCcontains j
      ⟨⟨hxc.1,hxnotmark⟩,⟨hxc.2,hxnotmark⟩⟩
    by_contra hne
    exact Set.disjoint_left.mp hGdis hxG ⟨hxC,hne⟩
  have hprod (j : J) : (a (some j)) 1 * (d (some j)) 1 < 0 :=
    actual_unit_square_crossing_ray_signs M c (b j) p (hcross j)
      F hpF hzero (a (some j)) (d (some j))
      (by simpa [r] using haxis)
      (by simpa [r] using hmodel (some j))
      (hmeet j)
  have hdistJ (j k : J × Bool) (hjk : j ≠ k) :
      Disjoint
        (segment ℝ (0 : Plane)
          (if j.2 then d (some j.1) else a (some j.1)) \ {0})
        (segment ℝ (0 : Plane)
          (if k.2 then d (some k.1) else a (some k.1)) \ {0}) := by
    have hne : (some j.1,j.2) ≠ (some k.1,k.2) := by
      intro he
      apply hjk
      cases j with
      | mk j β =>
        cases k with
        | mk k γ =>
          have h1 : j = k := Option.some.inj (congrArg Prod.fst he)
          have h2 : β = γ := congrArg Prod.snd he
          exact Prod.ext h1 h2
    exact hdistinct (some j.1,j.2) (some k.1,k.2) hne
  obtain ⟨v,w,hvw,hunion,hdistv⟩ :=
    orient_radial_family (fun j => a (some j)) (fun j => d (some j))
      hprod hdistJ
  refine ⟨F,v,w,hpF,hzero,?_,hFmarks,hSquare,?_,?_,hvw,hdistv⟩
  · exact hsource ▸ hGsource
  · simpa [r] using haxis
  · intro j x hx hsquare
    rw [← hunion j]
    exact hmodel (some j) x hx hsquare

theorem actual_incident_family_one_point_redraw
    (M : HyperellipticModel E S) {J K : Type}
    [Fintype J] [Nonempty J] [Fintype K]
    (c : EssentialMarkedArc M) (b : J → EssentialMarkedArc M)
    (u : K → EssentialMarkedArc M)
    (p : S) (hpmark : p ∉ M.cover.branch)
    (hpc : p ∈ c.val.image) (hpb : ∀ j, p ∈ (b j).val.image)
    (hnot : ∀ k, p ∉ (u k).val.image)
    (hfinite : ∀ i k : Option J, i ≠ k →
      (ArcSurgery.crossings M
        (Option.elim i c b) (Option.elim k c b)).Finite)
    (hcross : ∀ j q, q ∈ ArcSurgery.crossings M c (b j) →
      ArcSurgery.CrossesInDisk M c (b j) q)
    (hUnontrans : ∀ k q, q ∈ ArcSurgery.crossings M c (u k) →
      ArcSurgery.CrossesInDisk M c (u k) q) :
    ∃ F : OpenPartialHomeomorph S Plane, ∃ v : J → Plane,
      ∃ δ : ℝ, ∃ d : EssentialMarkedArc M,
      0 < δ ∧ δ < 1 ∧
      ArcSurgery.vertex M d = ArcSurgery.vertex M c ∧
      d.val.image =
        (c.val.image \
          {x : S | x ∈ F.source ∧ F x ∈
            segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
          {x : S | x ∈ F.source ∧
            F x ∈ ArcSurgery.bendGraph (1 / 2) 1 δ} ∧
      p ∉ d.val.image ∧
      (∀ j, (ArcSurgery.crossings M d (b j)).Finite ∧
        (ArcSurgery.crossings M d (b j)).ncard =
          (ArcSurgery.crossings M c (b j)).ncard ∧
        (∀ q ∈ ArcSurgery.crossings M d (b j),
          ArcSurgery.CrossesInDisk M d (b j) q) ∧
        ArcSurgery.crossings M d (b j) =
          (ArcSurgery.crossings M c (b j) \ {p}) ∪
            {F.symm (Plane.mk (δ * (v j) 0 / (v j) 1) δ)} ∧
        (∀ k, F.symm (Plane.mk (δ * (v j) 0 / (v j) 1) δ)
          ∉ (u k).val.image)) ∧
      (∀ j k, j ≠ k →
        F.symm (Plane.mk (δ * (v j) 0 / (v j) 1) δ) ∉ (b k).val.image) ∧
      ∀ k, ArcSurgery.crossings M d (u k) =
        ArcSurgery.crossings M c (u k) ∧
        ∀ q ∈ ArcSurgery.crossings M d (u k),
          ArcSurgery.CrossesInDisk M d (u k) q := by
  classical
  let j0 : J := Classical.choice inferInstance
  have hpcross (j : J) : p ∈ ArcSurgery.crossings M c (b j) := by
    have hpnonmark : p ∉ (M.cover.branch : Set S) := hpmark
    exact ⟨⟨hpc,hpnonmark⟩,⟨hpb j,hpnonmark⟩⟩
  obtain ⟨E0,hpE,hEp,hmarkE,havoidE⟩ :=
    actual_centered_chart_avoiding_nonincident_family M c (b j0) u p
      (hcross j0 p (hpcross j0)) hnot
  let C : Set S := ⋃ j : J, ArcSurgery.crossings M c (b j)
  have hC : C.Finite := Set.finite_iUnion (fun j =>
    hfinite none (some j) (by simp))
  have hCcontains (j : J) : ArcSurgery.crossings M c (b j) ⊆ C := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨j,hx⟩
  obtain ⟨F,v,w,hpF,hFp,hFsource,hmarks,hSquare,haxis,hmodel,hvw,hdistinct⟩ :=
    actual_oriented_incident_unit_chart M c b p hpmark hpc hpb hfinite
      (fun j => hcross j p (hpcross j)) E0 hpE hEp hmarkE C hC hCcontains
  obtain ⟨δ,d,hδ,hδ1,hclass,hbounds,himage,hremove,hcounts,havoid⟩ :=
    ArcSurgery.actual_unit_bend_finite_family_redraw M c b F p hpF hFp
      hmarks hSquare v w (fun j => (hvw j).1) (fun j => (hvw j).2)
      haxis hmodel hdistinct
      (fun j => hfinite none (some j) (by simp))
  refine ⟨F,v,δ,d,hδ,hδ1,hclass,himage,hremove,?_,havoid,?_⟩
  · intro j
    have hj := hcounts j
    refine ⟨hj.1,hj.2.1,?_,hj.2.2.1,?_⟩
    · exact actual_unit_bend_all_incident_transverse M c d (b j) F p hpF hFp
        hmarks hSquare (v j) (w j) (hvw j).1 (hvw j).2
        haxis (hmodel j) δ hδ hδ1 (hbounds j).1 (hbounds j).2
        himage (hcross j)
    · intro k
      have hnew := ArcSurgery.actual_unit_bend_new_crossing_singleton M (b j)
        F hmarks hSquare (v j) (w j) (hvw j).1 (hvw j).2 (hmodel j)
        δ hδ hδ1 (hbounds j).1 (hbounds j).2
      have hqnew : F.symm (Plane.mk (δ * (v j) 0 / (v j) 1) δ) ∈
          {x : S | x ∈ F.source ∧ F x ∈ ArcSurgery.bendGraph (1 / 2) 1 δ} ∩
            arcInterior M (b j) := by
        rw [hnew]
        exact Set.mem_singleton _
      exact Set.disjoint_left.mp ((havoidE k).mono_left hFsource)
        hqnew.1.1
  letI : T2Space S := M.sphere.symm.t2Space
  let Ksupport : Set S := F.symm '' Plane.closedSquare 0 1
  have hKclosed : IsClosed Ksupport :=
    (ArcSurgery.actual_unit_square_support_compact M F hSquare).isClosed
  have hagree := ArcSurgery.actual_supported_unit_bend_agrees_outside_square
    M c d F hSquare δ hδ hδ1 himage
  intro k
  have havoidF : Disjoint F.source (u k).val.image :=
    (havoidE k).mono_left hFsource
  have heq := ArcSurgery.actual_supported_unit_bend_nonincident_crossings
    M c d (u k) F δ havoidF himage
  refine ⟨heq,?_⟩
  intro q hq
  have hqold : q ∈ ArcSurgery.crossings M c (u k) := heq ▸ hq
  have hqK : q ∉ Ksupport := by
    rintro ⟨z,hz,rfl⟩
    have hqF : F.symm z ∈ F.source := F.map_target (hSquare hz)
    exact Set.disjoint_left.mp havoidF hqF hqold.2.1
  exact actual_crossing_persists_off_closed_support M c d (u k) q
    (hUnontrans k q hqold) Ksupport hKclosed hqK hagree

end
end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.actual_centered_chart_from_crossing
#print axioms CurveComplex.HyperellipticModel.actual_crossing_persists_off_closed_support
#print axioms CurveComplex.HyperellipticModel.actual_unit_bend_all_incident_transverse
#print axioms CurveComplex.HyperellipticModel.actual_oriented_incident_unit_chart
#print axioms CurveComplex.HyperellipticModel.actual_incident_family_one_point_redraw
