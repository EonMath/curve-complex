import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.CWHurewicz.ExcisionDifferentialTransport
import CurveComplexGenusTwo.Topology.Orientation.CompactHomologySupport
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.Convex.Topology

open CategoryTheory CategoryTheory.Limits Topology Set
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace CurveComplex.GenusOrientationCandidate

/-- An actual top-dimensional singular homology class on a closed surface
is determined by its localizations at all points. -/
theorem surface_top_homology_detection
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (z : H S 2)
    (hz : ∀ x : S, homologyToRelative S ({x}ᶜ : Set S) 2 z = 0) :
    z = 0 := by
  classical
  have hchart (X : Type) [TopologicalSpace X] [T2Space X]
      (e : OpenPartialHomeomorph X (ℝ × ℝ)) (K : Set X)
      (hK : IsCompact K) (hKe : K ⊆ e.source) :
      IsZero (relativeHomology X Kᶜ 3) := by
    classical
    have hplane (O : Set (ℝ × ℝ)) (hO : IsOpen O) (m : ℕ) :
        IsZero (H O (m + 2)) := by
      classical
      have hrows (U I : ℕ → Set ℝ)
          (hU : ∀ i, IsOpen (U i)) (hI : ∀ i, IsOpen (I i))
          (hcI : ∀ i, Convex ℝ (I i))
          (hsep : ∀ i j k : ℕ, i < j → j < k → Disjoint (I i) (I k))
          (m N : ℕ) : IsZero (H (↥(⋃ i ∈ Finset.range N, U i ×ˢ I i)) (m + 2)) := by
        classical
        have hstrip (U I : Set ℝ) (hU : IsOpen U) (hI : Convex ℝ I)
            (hne : I.Nonempty) (n : ℕ) (hn : 0 < n) : IsZero (H (↥(U ×ˢ I)) n) := by
          classical
          have hreal : IsZero (H U n) := by
            classical
            let : LocallyConnectedSpace U := hU.locallyConnectedSpace
            let D := _root_.ConnectedComponents U
            choose r hr using (ConnectedComponents.surjective_coe :
              Function.Surjective (ConnectedComponents.mk : U → D))
            let p : C(U,D) := ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
            let q : C(D,U) := ⟨r, continuous_of_discreteTopology⟩
            have hseg (t : unitInterval) (x : U) :
                (1 - (t : ℝ)) • x.val + (t : ℝ) • (r (p x)).val ∈ U := by
              have hc : Convex ℝ (Subtype.val '' connectedComponent x) :=
                (isPreconnected_connectedComponent.image Subtype.val
                  continuous_subtype_val.continuousOn).ordConnected.convex
              have hx : x.val ∈ Subtype.val '' connectedComponent x :=
                ⟨x, mem_connectedComponent, rfl⟩
              have hrx : (r (p x)).val ∈ Subtype.val '' connectedComponent x :=
                ⟨r (p x), (ConnectedComponents.coe_eq_coe').mp (hr (p x)), rfl⟩
              obtain ⟨v, hv, he⟩ := hc hx hrx (by linarith [t.property.2])
                t.property.1 (by ring : (1 - (t : ℝ)) + (t : ℝ) = 1)
              exact he ▸ v.property
            let h : ContinuousMap.Homotopy (ContinuousMap.id U) (q.comp p) :=
              { toFun := fun tx => ⟨(1 - (tx.1 : ℝ)) • tx.2.val +
                  (tx.1 : ℝ) • (r (p tx.2)).val, hseg tx.1 tx.2⟩
                continuous_toFun := ((continuous_const.sub
                  (continuous_subtype_val.comp continuous_fst)).smul
                    (continuous_subtype_val.comp continuous_snd) |>.add
                  ((continuous_subtype_val.comp continuous_fst).smul
                    (continuous_subtype_val.comp (q.continuous.comp
                      (p.continuous.comp continuous_snd))))).subtype_mk _
                map_zero_left := by intro x; apply Subtype.ext; simp
                map_one_left := by intro x; apply Subtype.ext; simp [q, p] }
            let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
              (ModuleCat.of ℤ ℤ)
            have hzD : IsZero (H D n) :=
              AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
                (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of D) (by omega)
            let hTop : TopCat.Homotopy (TopCat.ofHom (ContinuousMap.id U))
                (TopCat.ofHom (q.comp p)) := h
            have he := hTop.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) n
            change F.map (TopCat.ofHom (ContinuousMap.id U)) =
              F.map (TopCat.ofHom (q.comp p)) at he
            have hcomp : TopCat.ofHom (q.comp p) = TopCat.ofHom p ≫ TopCat.ofHom q := rfl
            rw [hcomp, F.map_comp] at he
            have hpzero : F.map (TopCat.ofHom p) = 0 := hzD.eq_of_tgt _ _
            rw [hpzero, zero_comp] at he
            apply (IsZero.iff_id_eq_zero _).mpr
            simpa only [show TopCat.ofHom (ContinuousMap.id U) = 𝟙 (TopCat.of U) from rfl,
              F.map_id] using he
          obtain ⟨y0, hy0⟩ := hne
          let r : C(↥(U ×ˢ I), U) :=
            ⟨fun x => ⟨x.val.1, x.property.1⟩,
              (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩
          let i : C(U, ↥(U ×ˢ I)) :=
            ⟨fun x => ⟨(x.val, y0), x.property, hy0⟩,
              (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩
          have hv (t : unitInterval) (x : ↥(U ×ˢ I)) :
              (1 - (t : ℝ)) • x.val.2 + (t : ℝ) • y0 ∈ I :=
            hI x.property.2 hy0 (by linarith [t.property.2]) t.property.1 (by ring)
          let h : ContinuousMap.Homotopy (ContinuousMap.id (↥(U ×ˢ I))) (i.comp r) :=
            { toFun := fun tx => ⟨(tx.2.val.1,
                (1 - (tx.1 : ℝ)) • tx.2.val.2 + (tx.1 : ℝ) • y0),
                  tx.2.property.1, hv tx.1 tx.2⟩
              continuous_toFun := ((continuous_fst.comp
                (continuous_subtype_val.comp continuous_snd)).prodMk
                (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
                  (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))).add
                  ((continuous_subtype_val.comp continuous_fst).smul continuous_const))).subtype_mk _
              map_zero_left := by intro x; apply Subtype.ext; simp
              map_one_left := by intro x; apply Subtype.ext; simp [i, r] }
          let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
            (ModuleCat.of ℤ ℤ)
          let hTop : TopCat.Homotopy (TopCat.ofHom (ContinuousMap.id (↥(U ×ˢ I))))
              (TopCat.ofHom (i.comp r)) := h
          have he := hTop.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) n
          change F.map (TopCat.ofHom (ContinuousMap.id (↥(U ×ˢ I)))) =
            F.map (TopCat.ofHom (i.comp r)) at he
          have hcomp : TopCat.ofHom (i.comp r) = TopCat.ofHom r ≫ TopCat.ofHom i := rfl
          rw [hcomp, F.map_comp] at he
          have hrzero : F.map (TopCat.ofHom r) = 0 := hreal.eq_of_tgt _ _
          rw [hrzero, zero_comp] at he
          apply (IsZero.iff_id_eq_zero _).mpr
          simpa only [show TopCat.ofHom (ContinuousMap.id (↥(U ×ˢ I))) =
              𝟙 (TopCat.of (↥(U ×ˢ I))) from rfl, F.map_id] using he
        have hmerge (m : ℕ) (T : Type) [TopologicalSpace T] (U V : Set T)
            (hU : IsOpen U) (hV : IsOpen V)
            (hzU : IsZero (H U (m + 2))) (hzV : IsZero (H V (m + 2)))
            (hzUV : IsZero (H (↥(U ∩ V)) (m + 1))) :
            IsZero (H (↥(U ∪ V)) (m + 2)) := by
          classical
          let Z := U ∪ V
          let A : Set Z := {z | z.val ∈ U}
          let B : Set Z := {z | z.val ∈ V}
          let eA : A ≃ₜ U :=
            { toFun := fun t => ⟨t.val.val, t.property⟩
              invFun := fun t => ⟨⟨t.val, Or.inl t.property⟩, t.property⟩
              left_inv := by intro t; rfl
              right_inv := by intro t; rfl
              continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
              continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
          let eB : B ≃ₜ V :=
            { toFun := fun t => ⟨t.val.val, t.property⟩
              invFun := fun t => ⟨⟨t.val, Or.inr t.property⟩, t.property⟩
              left_inv := by intro t; rfl
              right_inv := by intro t; rfl
              continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
              continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
          let eAB : (↥(A ∩ B)) ≃ₜ (↥(U ∩ V)) :=
            { toFun := fun t => ⟨t.val.val, t.property⟩
              invFun := fun t => ⟨⟨t.val, Or.inl t.property.1⟩, t.property⟩
              left_inv := by intro t; rfl
              right_inv := by intro t; rfl
              continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
              continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
          let F (n : ℕ) := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
            (ModuleCat.of ℤ ℤ)
          have hzeroA : IsZero (H A (m + 2)) :=
            ((F (m + 2)).mapIso (TopCat.isoOfHomeo eA)).isZero_iff.mpr hzU
          have hzeroB : IsZero (H B (m + 2)) :=
            ((F (m + 2)).mapIso (TopCat.isoOfHomeo eB)).isZero_iff.mpr hzV
          have hzeroAB : IsZero (H (↥(A ∩ B)) (m + 1)) :=
            ((F (m + 1)).mapIso (TopCat.isoOfHomeo eAB)).isZero_iff.mpr hzUV
          have hA : IsOpen A := hU.preimage continuous_subtype_val
          have hB : IsOpen B := hV.preimage continuous_subtype_val
          have hcover : A ∪ B = Set.univ := by
            ext z
            simp only [Set.mem_union, Set.mem_univ, iff_true]
            exact z.property
          have hconnzero : actualMVConnecting (TopCat.of Z) A B hA hB hcover (m + 1) = 0 :=
            hzeroAB.eq_of_tgt _ _
          let _ : Subsingleton (H A (m + 2)) := ModuleCat.subsingleton_of_isZero hzeroA
          let _ : Subsingleton (H B (m + 2)) := ModuleCat.subsingleton_of_isZero hzeroB
          apply ModuleCat.isZero_iff_subsingleton.mpr
          apply _root_.subsingleton_of_forall_eq 0
          intro z
          have hz : actualMVConnecting (TopCat.of Z) A B hA hB hcover (m + 1) z = 0 := by
            rw [hconnzero]
            rfl
          obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).mp
            (actualMV_exact_ambient (TopCat.of Z) A B hA hB hcover (m + 1)) z hz
          change actualMVSum (TopCat.of Z) A B (m + 2) v = z at hv
          have hvzero : v = 0 := Subsingleton.elim _ _
          rw [hvzero, map_zero] at hv
          exact hv.symm
        have hprod (U I : Set ℝ) (hU : IsOpen U) (hI : Convex ℝ I)
            (n : ℕ) (hn : 0 < n) : IsZero (H (↥(U ×ˢ I)) n) := by
          rcases I.eq_empty_or_nonempty with he | hne
          · rw [he, Set.prod_empty]
            exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
              (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (↥(∅ : Set (ℝ × ℝ)))) (by omega)
          · exact hstrip U I hU hI hne n hn
        induction N with
        | zero =>
          have he : (⋃ i ∈ Finset.range 0, U i ×ˢ I i) = ∅ := by ext x; simp
          rw [he]
          exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
            (ModuleCat.{0} ℤ) (m + 2) (ModuleCat.of ℤ ℤ) (TopCat.of (↥(∅ : Set (ℝ × ℝ)))) (by omega)
        | succ N ih =>
          let P : Set (ℝ × ℝ) := ⋃ i ∈ Finset.range N, U i ×ˢ I i
          have hopenP : IsOpen P := isOpen_biUnion fun i _ => (hU i).prod (hI i)
          have hintersection : IsZero (H (↥(P ∩ (U N ×ˢ I N))) (m + 1)) := by
            cases N with
            | zero =>
              have he : P ∩ (U 0 ×ˢ I 0) = ∅ := by simp [P]
              rw [he]
              exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
                (ModuleCat.{0} ℤ) (m + 1) (ModuleCat.of ℤ ℤ) (TopCat.of (↥(∅ : Set (ℝ × ℝ)))) (by omega)
            | succ k =>
              have he : P ∩ (U (k + 1) ×ˢ I (k + 1)) =
                  (U k ∩ U (k + 1)) ×ˢ (I k ∩ I (k + 1)) := by
                ext x
                constructor
                · rintro ⟨hxP, hxrow⟩
                  change x ∈ ⋃ i ∈ Finset.range (k + 1), U i ×ˢ I i at hxP
                  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxP
                  obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxi
                  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
                  have hieq : i = k := by
                    by_contra hne
                    have hil : i < k := lt_of_le_of_ne hik hne
                    exact Set.disjoint_left.mp (hsep i k (k + 1) hil (by omega)) hxi.2 hxrow.2
                  subst i
                  exact ⟨⟨hxi.1, hxrow.1⟩, hxi.2, hxrow.2⟩
                · rintro ⟨⟨hxuk, hxun⟩, hxik, hxin⟩
                  refine ⟨?_, hxun, hxin⟩
                  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨by simp, hxuk, hxik⟩⟩
              rw [he]
              exact hprod _ _ ((hU k).inter (hU (k + 1))) ((hcI k).inter (hcI (k + 1))) (m + 1) (by omega)
          have he : (⋃ i ∈ Finset.range (N + 1), U i ×ˢ I i) = P ∪ (U N ×ˢ I N) := by
            simp [P, Finset.range_add_one, Set.union_comm]
          rw [he]
          exact hmerge m (ℝ × ℝ) P _ hopenP ((hU N).prod (hI N)) ih
            (hprod _ _ (hU N) (hcI N) (m + 2) (by omega)) hintersection
      have hneighborhood (K O : Set (ℝ × ℝ)) (hK : IsCompact K)
          (hO : IsOpen O) (hKO : K ⊆ O) :
          ∃ (N : ℕ) (U I : ℕ → Set ℝ),
            (∀ j, IsOpen (U j)) ∧ (∀ j, IsOpen (I j)) ∧
            (∀ j, Convex ℝ (I j)) ∧
            (∀ i j k : ℕ, i < j → j < k → Disjoint (I i) (I k)) ∧
            K ⊆ (⋃ i ∈ Finset.range N, U i ×ˢ I i) ∧
            (⋃ i ∈ Finset.range N, U i ×ˢ I i) ⊆ O := by
        classical
        obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hO hKO
        let s := δ / 4
        have hs : 0 < s := by dsimp [s]; positivity
        obtain ⟨b, hb⟩ := hK.bddBelow_image continuous_snd.continuousOn
        let a := b - s
        let c (j : ℕ) : ℝ := a + s * j
        let I (j : ℕ) : Set ℝ := Ioo (c j - 3*s/4) (c j + 3*s/4)
        let P (j : ℕ) := {p : ℝ × ℝ | 0 < p.2 ∧
          (Ioo (p.1 - p.2) (p.1 + p.2)) ×ˢ I j ⊆ O}
        let U (j : ℕ) : Set ℝ := ⋃ p : P j, Ioo (p.val.1 - p.val.2) (p.val.1 + p.val.2)
        have hU : ∀ j, IsOpen (U j) := fun j => isOpen_iUnion fun _ => isOpen_Ioo
        have hI : ∀ j, IsOpen (I j) := fun _ => isOpen_Ioo
        have hstrip : ∀ j, U j ×ˢ I j ⊆ O := by
          intro j q hq
          obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hq.1
          exact p.property.2 ⟨hp, hq.2⟩
        have hcover : K ⊆ ⋃ j : ℕ, U j ×ˢ I j := by
          intro p hp
          have hbyp : b ≤ p.2 := hb ⟨p, hp, rfl⟩
          let t := (p.2 - a) / s + 1/2
          have hpa : 0 ≤ p.2 - a := by dsimp [a]; linarith
          have ht : 0 ≤ t := by
            have hd := div_nonneg hpa hs.le
            dsimp [t]
            linarith
          let j := Nat.floor t
          have hjlo : (j : ℝ) ≤ t := Nat.floor_le ht
          have hjhi : t < (j : ℝ) + 1 := Nat.lt_floor_add_one t
          have hjslo : (j : ℝ) * s ≤ (p.2 - a) + s/2 := by
            have hh := mul_le_mul_of_nonneg_right hjlo hs.le
            dsimp [t] at hh
            field_simp at hh
            nlinarith
          have hjshi : (p.2 - a) + s/2 < ((j : ℝ) + 1) * s := by
            have hh := mul_lt_mul_of_pos_right hjhi hs
            dsimp [t] at hh
            field_simp at hh
            nlinarith
          have hpy : p.2 ∈ I j := by dsimp [I, c]; constructor <;> nlinarith
          have hrect : Ioo (p.1 - s) (p.1 + s) ×ˢ I j ⊆ O := by
            intro q hq
            apply hthick
            apply Metric.mem_thickening_iff.mpr
            refine ⟨p, hp, ?_⟩
            rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
            dsimp [I, c] at hq
            have hδs : δ = 4 * s := by dsimp [s]; ring
            constructor <;> constructor <;> nlinarith [hδs, hq.1.1, hq.1.2, hq.2.1, hq.2.2]
          let patch : P j := ⟨(p.1, s), hs, hrect⟩
          apply Set.mem_iUnion.mpr
          refine ⟨j, ?_, hpy⟩
          apply Set.mem_iUnion.mpr
          exact ⟨patch, by change p.1 - s < p.1 ∧ p.1 < p.1 + s; constructor <;> linarith⟩
        obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun j => U j ×ˢ I j)
          (fun j => (hU j).prod (hI j)) hcover
        let N := F.sup id + 1
        refine ⟨N, U, I, hU, hI, fun _ => convex_Ioo _ _, ?_, ?_, ?_⟩
        · intro i j k hij hjk
          apply Set.disjoint_left.mpr
          intro y hyi hyk
          have hik : (i : ℝ) + 2 ≤ k := by exact_mod_cast (show i + 2 ≤ k by omega)
          dsimp [I, c] at hyi hyk
          nlinarith [hyi.2, hyk.1]
        · intro p hp
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hF hp)
          obtain ⟨hjF, hpj⟩ := Set.mem_iUnion.mp hj
          have hjN : j < N := by
            have hle : j ≤ F.sup id := Finset.le_sup (f := id) hjF
            dsimp [N]
            omega
          exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hjN, hpj⟩⟩
        · intro p hp
          obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hp
          obtain ⟨_, hpj⟩ := Set.mem_iUnion.mp hpj
          exact hstrip j hpj
      apply ModuleCat.isZero_iff_subsingleton.mpr
      apply _root_.subsingleton_of_forall_eq 0
      intro z
      obtain ⟨K, hK, v, hv⟩ := homology_class_compact_support (↥O) (m + 2) z
      let L : Set (ℝ × ℝ) := Subtype.val '' K
      have hL : IsCompact L := hK.image continuous_subtype_val
      have hLO : L ⊆ O := by
        rintro x ⟨t, ht, rfl⟩
        exact t.property
      obtain ⟨N, U, I, hU, hI, hcI, hsep, hLR, hRO⟩ := hneighborhood L O hL hO hLO
      let R : Set (ℝ × ℝ) := ⋃ i ∈ Finset.range N, U i ×ˢ I i
      have hRzero : IsZero (H R (m + 2)) := hrows U I hU hI hcI hsep m N
      let q : TopCat.of K ⟶ TopCat.of R := TopCat.ofHom
        ⟨fun t => ⟨t.val.val, hLR ⟨t.val, t.property, rfl⟩⟩,
          (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
      let j : TopCat.of R ⟶ TopCat.of O := TopCat.ofHom
        ⟨fun t => ⟨t.val, hRO t.property⟩, continuous_subtype_val.subtype_mk _⟩
      let jK : TopCat.of K ⟶ TopCat.of O := TopCat.ofHom
        ⟨Subtype.val, continuous_subtype_val⟩
      have hcomp : q ≫ j = jK := by ext t <;> rfl
      let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj
        (ModuleCat.of ℤ ℤ)
      have hqzero : F.map q = 0 := hRzero.eq_of_tgt _ _
      change F.map jK v = z at hv
      rw [← hcomp, F.map_comp, hqzero, zero_comp] at hv
      exact hv.symm
    let V := e.source
    let Y := Excised X Vᶜ
    let B : Set Y := excisedSubspace Kᶜ Vᶜ
    let ey : Y ≃ₜ e.target :=
      (Homeomorph.setCongr (compl_compl V)).trans e.toPartialHomeomorph.toHomeomorphSourceTarget
    let F (n : ℕ) := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)
    have hYzero : IsZero (H Y 3) :=
      ((F 3).mapIso (TopCat.isoOfHomeo ey)).isZero_iff.mpr (hplane e.target e.open_target 1)
    have hBopen : IsOpen B := hK.isClosed.isOpen_compl.preimage continuous_subtype_val
    have hEmb : IsOpenEmbedding (fun y : Y => (ey y).val) :=
      e.open_target.isOpenEmbedding_subtypeVal.comp ey.isOpenEmbedding
    let eb : B ≃ₜ (Subtype.val ∘ ey) '' B := hEmb.isEmbedding.homeomorphImage B
    have hImageOpen : IsOpen ((Subtype.val ∘ ey) '' B) := hEmb.isOpenMap B hBopen
    have hBzero : IsZero (H B 2) :=
      ((F 2).mapIso (TopCat.isoOfHomeo eb)).isZero_iff.mpr (hplane _ hImageOpen 0)
    have hrelative : IsZero (relativeHomology Y B 3) := by
      have hc : relativeConnecting Y B 2 = 0 := hBzero.eq_of_tgt _ _
      apply ModuleCat.isZero_iff_subsingleton.mpr
      apply _root_.subsingleton_of_forall_eq 0
      intro z
      have hz : relativeConnecting Y B 2 z = 0 := by rw [hc]; rfl
      obtain ⟨_, hexact⟩ := pairHomology_exact_at_relative Y B 2
      obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexact z hz
      change homologyToRelative Y B 3 w = z at hw
      have hm : homologyToRelative Y B 3 = 0 := hYzero.eq_of_src _ _
      rw [hm] at hw
      exact hw.symm
    have hexc : closure Vᶜ ⊆ interior Kᶜ := by
      rw [e.open_source.isClosed_compl.closure_eq, hK.isClosed.isOpen_compl.interior_eq]
      exact Set.compl_subset_compl.mpr hKe
    let f := HomologicalComplex.homologyMap (excisionRelativeChainMap Kᶜ Vᶜ) 3
    let : IsIso f := canonicalExcisionHomologyMap_isIso X Kᶜ Vᶜ hexc 2
    exact (asIso f).isZero_iff.mp hrelative
  have hcover (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
      (n : ℕ) (z : H S n)
      (hz : ∀ x : S, homologyToRelative S ({x}ᶜ : Set S) n z = 0)
      (O : S → Set S) (hO : ∀ x, IsOpen (O x)) (hxO : ∀ x, x ∈ O x) :
      ∃ (F : Finset S) (C : S → Set S),
        (∀ x, IsCompact (C x) ∧ x ∈ interior (C x) ∧ C x ⊆ O x ∧
          homologyToRelative S (C x)ᶜ n z = 0) ∧
        (Set.univ : Set S) ⊆ ⋃ x ∈ F, interior (C x) := by
    classical
    have hlocal (x : S) (U : Set S) (hU : IsOpen U) (hxU : x ∈ U) :
        ∃ C : Set S, IsCompact C ∧ x ∈ interior C ∧ C ⊆ U ∧
          homologyToRelative S Cᶜ n z = 0 := by
      obtain ⟨hzero, hexact⟩ := pairHomology_exact_at_absolute S ({x}ᶜ : Set S) n
      obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexact z (hz x)
      change homologyInclusion S ({x}ᶜ : Set S) n w = z at hw
      obtain ⟨K, hK, v, hv⟩ := homology_class_compact_support (↥({x}ᶜ : Set S)) n w
      let L : Set S := Subtype.val '' K
      have hL : IsCompact L := hK.image continuous_subtype_val
      have hxL : x ∈ Lᶜ := by
        rintro ⟨t, ht, he⟩
        exact t.property he
      have hnhds : U ∩ Lᶜ ∈ nhds x :=
        (hU.inter hL.isClosed.isOpen_compl).mem_nhds ⟨hxU, hxL⟩
      obtain ⟨C, hCx, hCc, hCsub⟩ := exists_mem_nhds_isClosed_subset hnhds
      refine ⟨C, hCc.isCompact, mem_interior_iff_mem_nhds.mpr hCx,
        fun y hy => (hCsub hy).1, ?_⟩
      have havoid (t : K) : t.val.val ∈ Cᶜ := by
        intro hmem
        exact (hCsub hmem).2 ⟨t.val, t.property, rfl⟩
      let q : TopCat.of K ⟶ TopCat.of (↥(Cᶜ)) :=
        TopCat.ofHom ⟨fun t => ⟨t.val.val, havoid t⟩,
          (continuous_subtype_val.comp continuous_subtype_val).subtype_mk havoid⟩
      let j : TopCat.of K ⟶ TopCat.of (↥({x}ᶜ : Set S)) :=
        TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)
      have hcomp : q ≫ pairInclusion S Cᶜ = j ≫ pairInclusion S ({x}ᶜ : Set S) := by
        ext t
        rfl
      have hrep : homologyInclusion S Cᶜ n (F.map q v) = z := by
        change (F.map q ≫ F.map (pairInclusion S Cᶜ)) v = z
        rw [← F.map_comp, hcomp, F.map_comp]
        change homologyInclusion S ({x}ᶜ : Set S) n (F.map j v) = z
        rw [hv]
        exact hw
      obtain ⟨hzeroC, _⟩ := pairHomology_exact_at_absolute S Cᶜ n
      have he := congrArg (fun f => f (F.map q v)) hzeroC
      change homologyToRelative S Cᶜ n
        (homologyInclusion S Cᶜ n (F.map q v)) = 0 at he
      simpa only [hrep] using he
    choose C hCc hCi hCs hCz using fun x => hlocal x (O x) (hO x) (hxO x)
    have hcover : (Set.univ : Set S) ⊆ ⋃ x : S, interior (C x) := by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hCi x⟩
    obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
      (fun x => interior (C x)) (fun _ => isOpen_interior) hcover
    exact ⟨F, C, fun x => ⟨hCc x, hCi x, hCs x, hCz x⟩, hF⟩
  have hmerge (T : Type) [TopologicalSpace T] (K L : Set T)
      (hK : IsClosed K) (hL : IsClosed L)
      (hvanish : IsZero (relativeHomology T (K ∩ L)ᶜ 3))
      (z : H T 2) (hzK : homologyToRelative T Kᶜ 2 z = 0)
      (hzL : homologyToRelative T Lᶜ 2 z = 0) :
      homologyToRelative T (K ∪ L)ᶜ 2 z = 0 := by
    classical
    let Y := (K ∩ L)ᶜ
    let A : Set Y := {y | y.val ∈ Kᶜ}
    let B : Set Y := {y | y.val ∈ Lᶜ}
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)
    have hA : IsOpen A := hK.isOpen_compl.preimage continuous_subtype_val
    have hB : IsOpen B := hL.isOpen_compl.preimage continuous_subtype_val
    have hcover : A ∪ B = Set.univ := by
      ext y
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      change y.val ∉ K ∨ y.val ∉ L
      simpa only [Y, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] using y.property
    obtain ⟨hzsub, hexactsub⟩ := pairHomology_exact_at_subspace T Y 2
    have hconn : relativeConnecting T Y 2 = 0 := hvanish.eq_of_src _ _
    let : Mono (homologyInclusion T Y 2) := hexactsub.mono_g hconn
    have hinj := (ModuleCat.mono_iff_injective (homologyInclusion T Y 2)).mp inferInstance
    obtain ⟨_, hexK⟩ := pairHomology_exact_at_absolute T Kᶜ 2
    obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexK z hzK
    change homologyInclusion T Kᶜ 2 a = z at ha
    obtain ⟨_, hexL⟩ := pairHomology_exact_at_absolute T Lᶜ 2
    obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexL z hzL
    change homologyInclusion T Lᶜ 2 b = z at hb
    let qa : TopCat.of (↥(Kᶜ)) ⟶ TopCat.of A := TopCat.ofHom
      ⟨fun t => ⟨⟨t.val, fun h => t.property h.1⟩, t.property⟩,
        (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
    let qb : TopCat.of (↥(Lᶜ)) ⟶ TopCat.of B := TopCat.ofHom
      ⟨fun t => ⟨⟨t.val, fun h => t.property h.2⟩, t.property⟩,
        (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
    have heqa : qa ≫ pairInclusion Y A ≫ pairInclusion T Y = pairInclusion T Kᶜ := by
      ext t
      rfl
    have heqb : qb ≫ pairInclusion Y B ≫ pairInclusion T Y = pairInclusion T Lᶜ := by
      ext t
      rfl
    have hclassa : homologyInclusion T Y 2 (homologyInclusion Y A 2 (F.map qa a)) = z := by
      change (F.map qa ≫ F.map (pairInclusion Y A) ≫ F.map (pairInclusion T Y)) a = z
      rw [← F.map_comp, ← F.map_comp, heqa]
      exact ha
    have hclassb : homologyInclusion T Y 2 (homologyInclusion Y B 2 (F.map qb b)) = z := by
      change (F.map qb ≫ F.map (pairInclusion Y B) ≫ F.map (pairInclusion T Y)) b = z
      rw [← F.map_comp, ← F.map_comp, heqb]
      exact hb
    let v : H A 2 × H B 2 := (F.map qa a, -(F.map qb b))
    have hv : actualMVSum (TopCat.of Y) A B 2 v = 0 := by
      rw [actualMVSum_apply]
      change homologyInclusion Y A 2 (F.map qa a) + homologyInclusion Y B 2 (-(F.map qb b)) = 0
      rw [map_neg]
      apply hinj
      rw [map_add, map_neg, map_zero, hclassa, hclassb]
      exact add_neg_cancel _
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (actualMV_exact_pair (TopCat.of Y) A B hA hB hcover 2) v hv
    change actualMVDifference (TopCat.of Y) A B 2 w = v at hw
    have hwfst := congrArg Prod.fst hw
    rw [actualMVDifference_apply] at hwfst
    change actualSubsetHomologyMap (TopCat.of Y) (A ∩ B) A Set.inter_subset_left 2 w = F.map qa a at hwfst
    let q : TopCat.of (↥(A ∩ B)) ⟶ TopCat.of (↥((K ∪ L)ᶜ)) := TopCat.ofHom
      ⟨fun t => ⟨t.val.val, fun h => h.elim t.property.1 t.property.2⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    have heq : q ≫ pairInclusion T (K ∪ L)ᶜ =
        singularSubsetInclusion (TopCat.of Y) (A ∩ B) A Set.inter_subset_left ≫
          pairInclusion Y A ≫ pairInclusion T Y := by
      ext t
      rfl
    have hrep : homologyInclusion T (K ∪ L)ᶜ 2 (F.map q w) = z := by
      change (F.map q ≫ F.map (pairInclusion T (K ∪ L)ᶜ)) w = z
      rw [← F.map_comp, heq, F.map_comp, F.map_comp]
      change homologyInclusion T Y 2 (homologyInclusion Y A 2
        (actualSubsetHomologyMap (TopCat.of Y) (A ∩ B) A Set.inter_subset_left 2 w)) = z
      rw [hwfst]
      exact hclassa
    obtain ⟨hzero, _⟩ := pairHomology_exact_at_absolute T (K ∪ L)ᶜ 2
    have he := congrArg (fun f => f (F.map q w)) hzero
    change homologyToRelative T (K ∪ L)ᶜ 2
      (homologyInclusion T (K ∪ L)ᶜ 2 (F.map q w)) = 0 at he
    simpa only [hrep] using he
  let plane : EuclideanSpace ℝ (Fin 2) ≃ₜ (ℝ × ℝ) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.piFinTwo (fun _ => ℝ))
  let e (x : S) : OpenPartialHomeomorph S (ℝ × ℝ) :=
    (chartAt (EuclideanSpace ℝ (Fin 2)) x).trans plane.toOpenPartialHomeomorph
  have he_source (x : S) : (e x).source = (chartAt (EuclideanSpace ℝ (Fin 2)) x).source := by
    simp [e]
  have hx_source (x : S) : x ∈ (e x).source := by
    rw [he_source]
    exact mem_chart_source _ x
  obtain ⟨F, C, hC, hFcover⟩ := hcover S 2 z hz (fun x => (e x).source)
    (fun x => (e x).open_source) hx_source
  have hfinite : ∀ G : Finset S, G.Nonempty →
      homologyToRelative S (⋃ x ∈ G, C x)ᶜ 2 z = 0 := by
    intro G
    induction G using Finset.induction_on with
    | empty =>
      intro hempty
      exact False.elim (Finset.not_nonempty_empty hempty)
    | @insert x G hxG ih =>
      intro _
      rcases G.eq_empty_or_nonempty with rfl | hG
      · have heq : (⋃ y ∈ insert x (∅ : Finset S), C y) = C x := by simp
        exact (congrArg (fun A : Set S => homologyToRelative S Aᶜ 2 z = 0) heq).mpr
          (hC x).2.2.2
      · let P : Set S := ⋃ y ∈ G, C y
        have hP : IsCompact P := G.isCompact_biUnion (fun y _ => (hC y).1)
        have hPx : IsCompact (P ∩ C x) := hP.inter_right (hC x).1.isClosed
        have hsub : P ∩ C x ⊆ (e x).source :=
          fun _ ht => (hC x).2.2.1 ht.2
        have hzP : homologyToRelative S Pᶜ 2 z = 0 := ih hG
        have hzunion := hmerge S P (C x) hP.isClosed (hC x).1.isClosed
          (hchart S (e x) (P ∩ C x) hPx hsub) z hzP (hC x).2.2.2
        have heq : (⋃ y ∈ insert x G, C y) = P ∪ C x := by
          simp [P, Set.union_comm]
        exact (congrArg (fun A : Set S => homologyToRelative S Aᶜ 2 z = 0) heq).mpr hzunion
  have hFnonempty : F.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty S)
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hFcover (Set.mem_univ x))
    obtain ⟨hyF, _⟩ := Set.mem_iUnion.mp hy
    exact ⟨y, hyF⟩
  have hfull : (⋃ x ∈ F, C x) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hFcover (Set.mem_univ x))
    obtain ⟨hyF, hxy⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyF, interior_subset hxy⟩⟩
  have hzempty : homologyToRelative S ∅ 2 z = 0 := by
    have hh := (congrArg (fun A : Set S => homologyToRelative S Aᶜ 2 z = 0) hfull).mp
      (hfinite F hFnonempty)
    exact (congrArg (fun A : Set S => homologyToRelative S A 2 z = 0)
      (compl_univ : (Set.univ : Set S)ᶜ = ∅)).mp hh
  obtain ⟨_, hexact⟩ := pairHomology_exact_at_absolute S ∅ 2
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexact z hzempty
  change homologyInclusion S ∅ 2 w = z at hw
  have hempty : IsZero (H (↥(∅ : Set S)) 2) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℤ) 2 (ModuleCat.of ℤ ℤ) (TopCat.of (↥(∅ : Set S))) (by omega)
  have hm : homologyInclusion S ∅ 2 = 0 := hempty.eq_of_src _ _
  rw [hm] at hw
  exact hw.symm

end CurveComplex.GenusOrientationCandidate
