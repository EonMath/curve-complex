import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Topology.RestrictedLink.HomeomorphismComponentHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.RegionComponentHeaders
import CurveComplexGenusTwo.Topology.ArcStraightening
import CurveComplexGenusTwo.Topology.Extraction
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
namespace CurveComplex.HyperellipticModel
open Set Schoenflies
open scoped Classical
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actual_good_gap_arc (M : HyperellipticModel E S) (U : Set S)
    (C : Set Plane) (hC : IsJordanCurve C)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (heU : U = f '' inside C) (z : Plane) (hz : z ∈ C)
    (hzB : f z ∈ M.cover.branch)
    (hlo : 1 ≤ (M.cover.branch.filter (fun x => x ∈ U)).card)
    (hhi : (M.cover.branch.filter (fun x => x ∈ U)).card ≤ 2) :
    ∃ a : EssentialMarkedArc M,
      a.val.map 0 ≠ a.val.map 1 ∧ arcInterior M a ⊆ U ∧
      (a.val.map 0 ∈ U ∨ a.val.map 1 ∈ U) := by
  classical
  have boundaryArc (M : HyperellipticModel E S) (f : Plane → S)
      (hf : Topology.IsOpenEmbedding f) (C : Set Plane) (hC : IsJordanCurve C)
      (x y : Plane) (hx : x ∈ C) (hy : y ∈ inside C)
      (hxB : f x ∈ M.cover.branch) (hyB : f y ∈ M.cover.branch)
      (hmarks : ∀ z ∈ inside C, f z ∈ M.cover.branch → z = y) :
      ∃ a : EssentialMarkedArc M,
        a.val.map 0 = f x ∧ a.val.map 1 = f y ∧
        a.val.image ⊆ f '' inside C ∪ {f x} := by
    classical
    have chart {C : Set Plane} (hC : IsJordanCurve C) :
        ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
      classical
      have outsideComponent {C : Set Plane} (hC : IsJordanCurve C) :
          IsComplementComponent C (outside C) := by
        have hs := jordan_curve_theorem hC
        refine ⟨hs.isConnected_outside.nonempty, hs.isConnected_outside, outside_subset_compl, ?_⟩
        intro V hV hsub hVc
        apply Set.Subset.antisymm
        · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_outside
          · obtain ⟨x, hx⟩ := hs.isConnected_outside.nonempty
            exact ⟨x, hsub hx, hx⟩
          · intro x hx
            rw [(IsRegionOf.outside C).closure_eq hs] at hx
            rcases hx.1 with hi | hc
            · exact hi
            · exact False.elim (hVc hx.2 hc)
        · exact hsub
      obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
      obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
      have him : F '' C = modelCurve := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [hF ⟨y, hy⟩]
          exact (e ⟨y, hy⟩).property
        · intro hx
          let y := e.symm ⟨x, hx⟩
          refine ⟨y.val, y.property, ?_⟩
          rw [hF y]
          exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
      have hc := homeomorphism_complement_component F (jordan_inside_complement_component hC)
      rw [him] at hc
      have hi := jordan_inside_complement_component isJordanCurve_modelCurve
      have ho := outsideComponent isJordanCurve_modelCurve
      obtain ⟨x, hx⟩ := hc.1
      have hxin : x ∈ inside modelCurve ∪ outside modelCurve :=
        (inside_union_outside modelCurve).symm ▸ hc.2.2.1 hx
      have heinside : F '' inside C = inside modelCurve := by
        rcases hxin with hxI | hxO
        · by_contra hn
          exact Set.disjoint_left.mp (complementComponents_disjoint hc hi hn) hx hxI
        · have heoutside : F '' inside C = outside modelCurve := by
            by_contra hn
            exact Set.disjoint_left.mp (complementComponents_disjoint hc ho hn) hx hxO
          have hs := jordan_curve_theorem hC
          have hk : IsCompact (closure (inside C)) :=
            Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
          have hb : Bornology.IsBounded (F '' inside C) :=
            (hk.image F.continuous).isBounded.subset (image_mono subset_closure)
          exact False.elim ((jordan_curve_theorem isJordanCurve_modelCurve).not_isBounded_outside
            (heoutside ▸ hb))
      exact ⟨F, him, heinside.trans inside_modelCurve⟩
    obtain ⟨F,himage,hin⟩ := chart hC
    have hFx : F x ∈ modelCurve := himage ▸ mem_image_of_mem F hx
    have hFy : F y ∈ Plane.openSquare 0 1 := hin ▸ mem_image_of_mem F hy
    have hxy : F x ≠ F y := by
      intro he
      have h1 : Plane.supNorm (F x) = 1 := hFx
      have h2 : Plane.supNorm (F y) < 1 := mem_openSquare_zero_one.mp hFy
      rw [he] at h1
      linarith
    let l : ℝ → Plane := fun t => F x + t • (F y - F x)
    have hl : l = AffineMap.lineMap (F x) (F y) := by
      ext t
      simp [l, AffineMap.lineMap_apply_module]
      <;> ring
    have hli : Function.Injective l := hl ▸ AffineMap.lineMap_injective ℝ hxy
    have hl0 : l 0 = F x := by simp [l]
    have hl1 : l 1 = F y := by simp [l]
    have hinside (t : Interval) (ht : t ≠ 0) : l t.val ∈ Plane.openSquare 0 1 := by
      have htpos : 0 < t.val := lt_of_le_of_ne t.property.1 (fun he => ht (Subtype.ext he.symm))
      have h := (Plane.convex_closedSquare 0 1).add_smul_sub_mem_interior
        (modelCurve_subset_closedSquare hFx)
        (show F y ∈ interior (Plane.closedSquare 0 1) by rw [interior_closedSquare_zero_one]; exact hFy)
        (show t.val ∈ Ioc (0:ℝ) 1 from ⟨htpos,t.property.2⟩)
      rwa [interior_closedSquare_zero_one] at h
    let g : Interval → S := fun t => f (F.symm (l t.val))
    have hg0 : g 0 = f x := by simp [g,hl0]
    have hg1 : g 1 = f y := by simp [g,hl1]
    have hgi : Function.Injective g := by
      intro t u he
      apply Subtype.ext
      exact hli (F.symm.injective (hf.injective he))
    have hgin (t : Interval) (ht : t ≠ 0) : F.symm (l t.val) ∈ inside C := by
      have hh : l t.val ∈ F '' inside C := hin.symm ▸ hinside t ht
      obtain ⟨z,hz,he⟩ := hh
      simpa [← he] using hz
    let a : MarkedArc M := {
      map := g
      continuous := hf.continuous.comp (F.symm.continuous.comp (by dsimp [l]; fun_prop))
      injective_except_loop_closure := fun t u h => Or.inl (hgi h)
      start_marked := hg0 ▸ hxB
      end_marked := hg1 ▸ hyB
      marked_only_at_ends := by
        intro t ht
        by_cases ht0 : t = 0
        · exact Or.inl ht0
        · have he := hmarks (F.symm (l t.val)) (hgin t ht0) ht
          exact Or.inr (hgi (show g t = g 1 by rw [hg1]; exact congrArg f he)) }
    have hessential : IsEssentialMarkedArc M a := Or.inl (by
      change g 0 ≠ g 1
      rw [hg0,hg1]
      intro he
      exact hxy (congrArg F (hf.injective he)))
    refine ⟨⟨a,hessential⟩,hg0,hg1,?_⟩
    rintro z ⟨t,rfl⟩
    by_cases ht : t = 0
    · apply Or.inr
      change g t = f x
      rw [ht,hg0]
    · exact Or.inl (mem_image_of_mem f (hgin t ht))
  have twoArc (M : HyperellipticModel E S) (U : Set S) (e : Plane ≃ₜ U)
      (p q : S) (hp : p ∈ U) (hq : q ∈ U) (hpB : p ∈ M.cover.branch)
      (hqB : q ∈ M.cover.branch) (hpq : p ≠ q)
      (hmarks : ∀ x ∈ U, x ∈ M.cover.branch → x = p ∨ x = q) :
      ∃ a : EssentialMarkedArc M,
        a.val.map 0 = p ∧ a.val.map 1 = q ∧ a.val.image ⊆ U := by
    let x : Plane := e.symm ⟨p, hp⟩
    let y : Plane := e.symm ⟨q, hq⟩
    have hxy : x ≠ y := by
      intro h
      have he := congrArg (fun z => (e z).val) h
      simp only [x, y, e.apply_symm_apply] at he
      exact hpq he
    obtain ⟨A, _, _, f, hf, hi, hA, hf0, hf1⟩ :=
      exists_simple_arc_of_isPreconnected isOpen_univ isPreconnected_univ
        (mem_univ x) (mem_univ y) hxy
    let g : Interval → S := fun t => (e (f t.val)).val
    have hg0 : g 0 = p := by simp [g, hf0, x]
    have hg1 : g 1 = q := by simp [g, hf1, y]
    have hgi : Function.Injective g := by
      intro t u h
      apply Subtype.ext
      apply hi t.property u.property
      exact e.injective (Subtype.ext h)
    let a : MarkedArc M := {
      map := g
      continuous := continuous_subtype_val.comp (e.continuous.comp
        (continuousOn_iff_continuous_restrict.mp hf))
      injective_except_loop_closure := fun t u h => Or.inl (hgi h)
      start_marked := hg0 ▸ hpB
      end_marked := hg1 ▸ hqB
      marked_only_at_ends := by
        intro t ht
        have htg : g t ∈ U := (e (f t.val)).property
        rcases hmarks (g t) htg ht with ht | ht
        · exact Or.inl (hgi (ht.trans hg0.symm))
        · exact Or.inr (hgi (ht.trans hg1.symm)) }
    have hae : IsEssentialMarkedArc M a := Or.inl (by
      change g 0 ≠ g 1
      rwa [hg0, hg1])
    refine ⟨⟨a, hae⟩, hg0, hg1, ?_⟩
    rintro z ⟨t, rfl⟩
    exact (e (f t.val)).property
  have disc {C : Set Plane} (hC : IsJordanCurve C) : Nonempty (Plane ≃ₜ inside C) := by
    have straight {C : Set Plane} (hC : IsJordanCurve C) :
      ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
    
      classical
      have outsideComponent {C : Set Plane} (hC : IsJordanCurve C) :
          IsComplementComponent C (outside C) := by
        have hs := jordan_curve_theorem hC
        refine ⟨hs.isConnected_outside.nonempty, hs.isConnected_outside, outside_subset_compl, ?_⟩
        intro V hV hsub hVc
        apply Set.Subset.antisymm
        · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_outside
          · obtain ⟨x, hx⟩ := hs.isConnected_outside.nonempty
            exact ⟨x, hsub hx, hx⟩
          · intro x hx
            rw [(IsRegionOf.outside C).closure_eq hs] at hx
            rcases hx.1 with hi | hc
            · exact hi
            · exact False.elim (hVc hx.2 hc)
        · exact hsub
      obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
      obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
      have him : F '' C = modelCurve := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [hF ⟨y, hy⟩]
          exact (e ⟨y, hy⟩).property
        · intro hx
          let y := e.symm ⟨x, hx⟩
          refine ⟨y.val, y.property, ?_⟩
          rw [hF y]
          exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
      have hc := homeomorphism_complement_component F (jordan_inside_complement_component hC)
      rw [him] at hc
      have hi := jordan_inside_complement_component isJordanCurve_modelCurve
      have ho := outsideComponent isJordanCurve_modelCurve
      obtain ⟨x, hx⟩ := hc.1
      have hxin : x ∈ inside modelCurve ∪ outside modelCurve :=
        (inside_union_outside modelCurve).symm ▸ hc.2.2.1 hx
      have heinside : F '' inside C = inside modelCurve := by
        rcases hxin with hxI | hxO
        · by_contra hn
          exact Set.disjoint_left.mp (complementComponents_disjoint hc hi hn) hx hxI
        · have heoutside : F '' inside C = outside modelCurve := by
            by_contra hn
            exact Set.disjoint_left.mp (complementComponents_disjoint hc ho hn) hx hxO
          have hs := jordan_curve_theorem hC
          have hk : IsCompact (closure (inside C)) :=
            Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
          have hb : Bornology.IsBounded (F '' inside C) :=
            (hk.image F.continuous).isBounded.subset (image_mono subset_closure)
          exact False.elim ((jordan_curve_theorem isJordanCurve_modelCurve).not_isBounded_outside
            (heoutside ▸ hb))
      exact ⟨F, him, heinside.trans inside_modelCurve⟩
    have square : Nonempty (Plane ≃ₜ Plane.openSquare 0 1) := by
    
      let H : Plane ≃ₜ (Fin 2 → ℝ) := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
      let B : (Fin 2 → ℝ) ≃ₜ Metric.ball (0 : Fin 2 → ℝ) 1 := Homeomorph.unitBall
      let K : Metric.ball (0 : Fin 2 → ℝ) 1 ≃ₜ Plane.openSquare 0 1 :=
        H.symm.subtype (fun x => by
          simp only [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
          change (∀ i : Fin 2, ‖x i‖ < 1) ↔ (H.symm x).supDist 0 < 1
          simp [Schoenflies.Plane.supDist, Schoenflies.Plane.supNorm, Fin.forall_fin_two, H, EuclideanSpace.equiv,
            PiLp.toLp_apply, Real.norm_eq_abs])
      exact ⟨(H.trans B).trans K⟩
    obtain ⟨F, _, hFI⟩ := straight hC
    obtain ⟨H⟩ := square
    let R : inside C ≃ₜ Plane.openSquare 0 1 :=
      (F.isEmbedding.homeomorphImage (inside C)).trans (Homeomorph.setCongr hFI)
    exact ⟨H.trans R.symm⟩
  let P := M.cover.branch.filter (fun x => x ∈ U)
  have hnotU : f z ∉ U := by
    rw [heU]
    rintro ⟨t,ht,he⟩
    exact inside_subset_compl ht (hf.injective he ▸ hz)
  have hc : P.card = 1 ∨ P.card = 2 := by dsimp [P]; omega
  rcases hc with hc | hc
  · obtain ⟨q,hP⟩ := Finset.card_eq_one.mp hc
    have hqP : q ∈ P := hP.symm ▸ Finset.mem_singleton_self q
    obtain ⟨hqB,hqU⟩ := Finset.mem_filter.mp hqP
    have hqin : q ∈ f '' inside C := heU ▸ hqU
    obtain ⟨y,hy,hey⟩ := hqin
    have hmarks : ∀ t ∈ inside C, f t ∈ M.cover.branch → t = y := by
      intro t ht hb
      have hm : f t ∈ P := Finset.mem_filter.mpr ⟨hb,heU.symm ▸ mem_image_of_mem f ht⟩
      rw [hP] at hm
      exact hf.injective ((Finset.mem_singleton.mp hm).trans hey.symm)
    obtain ⟨a,ha0,ha1,haim⟩ := boundaryArc M f hf C hC z y hz hy hzB (hey.symm ▸ hqB) hmarks
    refine ⟨a,?_,?_,Or.inr ?_⟩
    · rw [ha0,ha1]
      intro he
      exact hnotU (he ▸ (heU.symm ▸ mem_image_of_mem f hy))
    · intro x hx
      rcases haim hx.1 with hi | he
      · exact heU.symm ▸ hi
      · exact False.elim (hx.2 ((Set.mem_singleton_iff.mp he).symm ▸ hzB))
    · rw [ha1]
      exact heU.symm ▸ mem_image_of_mem f hy
  · obtain ⟨p,q,hpq,hP⟩ := Finset.card_eq_two.mp hc
    have hpP : p ∈ P := hP.symm ▸ Finset.mem_insert_self p {q}
    have hqP : q ∈ P := hP.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    obtain ⟨hpB,hpU⟩ := Finset.mem_filter.mp hpP
    obtain ⟨hqB,hqU⟩ := Finset.mem_filter.mp hqP
    have hmarks : ∀ x ∈ U, x ∈ M.cover.branch → x = p ∨ x = q := by
      intro x hx hb
      have hm : x ∈ P := Finset.mem_filter.mpr ⟨hb,hx⟩
      rw [hP] at hm
      simpa using hm
    obtain ⟨H⟩ := disc hC
    let e : Plane ≃ₜ U := (H.trans (hf.isEmbedding.homeomorphImage (inside C))).trans
      (Homeomorph.setCongr heU.symm)
    obtain ⟨a,ha0,ha1,haim⟩ := twoArc M U e p q hpU hqU hpB hqB hpq hmarks
    exact ⟨a,by rwa [ha0,ha1],fun x hx => haim hx.1,Or.inl (ha0.symm ▸ hpU)⟩
end CurveComplex.HyperellipticModel
