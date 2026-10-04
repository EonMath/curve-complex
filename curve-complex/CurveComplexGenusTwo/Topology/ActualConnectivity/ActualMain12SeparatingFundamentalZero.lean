import CurveComplexGenusTwo.Topology.ActualConnectivity.ActualMain12SeparatingRegions
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseCircleFundamentalCycle
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
namespace CurveComplex
open Set Topology Schoenflies CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
theorem source_separating_curve_actual_annular_fundamental_zero (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
    (c : Curve S) (hc : ¬ Nonseparating c)
    (e : C(Set.Ioo (-1:ℝ) 1 × Circle,S)) (he : IsOpenEmbedding e)
    (hcore : ∀ w : Circle, e (⟨0,by norm_num⟩,w)=c.map w) :
    HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass=0 := by
  have hCover (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
      (c : Curve S) (hc : ¬ Nonseparating c)
      (e : C(Set.Ioo (-1:ℝ) 1 × Circle,S)) (he : IsOpenEmbedding e)
      (hcore : ∀ w : Circle, e (⟨0,by norm_num⟩,w)=c.map w) :
      ∃ U V N : Set S, IsOpen U ∧ IsOpen V ∧ IsOpen N ∧
        U ∪ V = Set.univ ∧ U ∩ V = N ∧ c.image ⊆ N ∧
        homologyInclusion S U 2=0 ∧ homologyInclusion S V 2=0 ∧
        N=e '' {z : Set.Ioo (-1:ℝ) 1 × Circle | z.1.val ∈ Set.Ioo (-1/2:ℝ) (1/2)} := by
    classical
    let : ClosedSurface S := Classical.choice hS.2.1
    obtain ⟨L,R,hLO,hRO,hLC,hRC,hdis,hcover,hLzero,hRzero⟩ :=
      source_separating_curve_actual_complementary_regions S hS c hc
    have hLQ : L ⊆ c.imageᶜ := by intro x hx; rw [←hcover];exact Or.inl hx
    have hRQ : R ⊆ c.imageᶜ := by intro x hx; rw [←hcover];exact Or.inr hx
    let pos : Set S := Set.range (fun z : Set.Ioo (0:ℝ) 1 × Circle =>
      e (⟨z.1.val,⟨by linarith [z.1.property.1],z.1.property.2⟩⟩,z.2))
    let neg : Set S := Set.range (fun z : Set.Ioo (-1:ℝ) 0 × Circle =>
      e (⟨z.1.val,⟨z.1.property.1,by linarith [z.1.property.2]⟩⟩,z.2))
    let : ConnectedSpace (Set.Ioo (0:ℝ) 1) := isConnected_iff_connectedSpace.mp (isConnected_Ioo (by norm_num))
    let : ConnectedSpace (Set.Ioo (-1:ℝ) 0) := isConnected_iff_connectedSpace.mp (isConnected_Ioo (by norm_num))
    have hpC : IsConnected pos := isConnected_range (by fun_prop)
    have hnC : IsConnected neg := isConnected_range (by fun_prop)
    have haxis (z : Set.Ioo (-1:ℝ) 1 × Circle) : e z ∈ c.image ↔ z.1.val=0 := by
      constructor
      · rintro ⟨w,hw⟩
        have hh := he.injective ((hcore w).trans hw)
        exact (congrArg (fun p => p.1.val) hh).symm
      · intro hz
        refine ⟨z.2,?_⟩
        rw [←hcore]
        apply congrArg e
        exact Prod.ext (Subtype.ext hz.symm) rfl
    have hpQ : pos ⊆ c.imageᶜ := by
      rintro x ⟨z,rfl⟩ hh
      have hz := (haxis _).mp hh
      exact (ne_of_gt z.1.property.1) hz
    have hnQ : neg ⊆ c.imageᶜ := by
      rintro x ⟨z,rfl⟩ hh
      have hz := (haxis _).mp hh
      exact (ne_of_lt z.1.property.2) hz
    have hpLR : pos ⊆ L ∨ pos ⊆ R :=
      hpC.isPreconnected.subset_or_subset hLO hRO hdis (hcover.symm ▸ hpQ)
    have hnLR : neg ⊆ L ∨ neg ⊆ R :=
      hnC.isPreconnected.subset_or_subset hLO hRO hdis (hcover.symm ▸ hnQ)
    have hrange : Set.range e ⊆ pos ∪ neg ∪ c.image := by
      rintro x ⟨z,rfl⟩
      rcases lt_trichotomy 0 z.1.val with hz|hz|hz
      · exact Or.inl (Or.inl ⟨(⟨z.1.val,⟨hz,z.1.property.2⟩⟩,z.2),rfl⟩)
      · exact Or.inr ((haxis z).mpr hz.symm)
      · exact Or.inl (Or.inr ⟨(⟨z.1.val,⟨z.1.property.1,hz⟩⟩,z.2),rfl⟩)
    have hcoreRange : c.image ⊆ Set.range e := by
      rintro x ⟨w,rfl⟩
      exact ⟨(⟨0,by norm_num⟩,w),hcore w⟩
    have hnotboth (A B : Set S) (hAO : IsOpen A) (hBO : IsOpen B)
        (hBne : B.Nonempty) (hD : Disjoint A B) (hAB : A ∪ B=c.imageᶜ)
        (hP : pos ⊆ A) (hN : neg ⊆ A) : False := by
      have hrr : Set.range e ⊆ A ∪ c.image := by
        intro x hx
        rcases hrange hx with (hp|hn)|hc
        · exact Or.inl (hP hp)
        · exact Or.inl (hN hn)
        · exact Or.inr hc
      have hEq : A ∪ c.image=A ∪ Set.range e := by
        apply Set.Subset.antisymm
        · exact Set.union_subset_union_right A hcoreRange
        · exact Set.union_subset (Set.subset_union_left) hrr
      have hACopen : IsOpen (A ∪ c.image) := hEq ▸ hAO.union he.isOpen_range
      have hBQ : B ⊆ c.imageᶜ := by intro x hx; rw [←hAB];exact Or.inr hx
      have hd : Disjoint (A ∪ c.image) B := by
        rw [Set.disjoint_left]
        rintro x (hx|hx) hy
        · exact Set.disjoint_left.mp hD hx hy
        · exact hBQ hy hx
      have hcu : Set.univ ⊆ (A ∪ c.image) ∪ B := by
        intro x _
        by_cases hx : x ∈ c.image
        · exact Or.inl (Or.inr hx)
        · have hh : x ∈ A ∪ B := hAB ▸ hx
          rcases hh with ha|hb
          · exact Or.inl (Or.inl ha)
          · exact Or.inr hb
      have hall : Set.univ ⊆ A ∪ c.image :=
        isPreconnected_univ.subset_left_of_subset_union hACopen hBO hd hcu
          ⟨c.map 1,Set.mem_univ _,Or.inr ⟨1,rfl⟩⟩
      obtain ⟨b,hb⟩ := hBne
      exact Set.disjoint_left.mp hd (hall (Set.mem_univ b)) hb
    have hopposite : (pos ⊆ L ∧ neg ⊆ R) ∨ (pos ⊆ R ∧ neg ⊆ L) := by
      rcases hpLR with hp|hp <;> rcases hnLR with hn|hn
      · exact (hnotboth L R hLO hRO hRC.nonempty hdis hcover hp hn).elim
      · exact Or.inl ⟨hp,hn⟩
      · exact Or.inr ⟨hp,hn⟩
      · exact (hnotboth R L hRO hLO hLC.nonempty hdis.symm (Set.union_comm _ _ ▸ hcover) hp hn).elim
    let W : Set (Set.Ioo (-1:ℝ) 1 × Circle) := {z | z.1.val ∈ Set.Ioo (-1/2:ℝ) (1/2)}
    let N : Set S := e '' W
    have hNO : IsOpen N := he.isOpenMap _
      (isOpen_Ioo.preimage (continuous_subtype_val.comp continuous_fst))
    have hcoreN : c.image ⊆ N := by
      rintro x ⟨w,rfl⟩
      exact ⟨(⟨0,by norm_num⟩,w),by norm_num [W],hcore w⟩
    let U := L ∪ N
    let V := R ∪ N
    have hUV : U ∪ V=Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_cases hx : x ∈ c.image
      · exact Or.inl (Or.inr (hcoreN hx))
      · have hh : x ∈ L ∪ R := hcover ▸ hx
        rcases hh with hL|hR
        · exact Or.inl (Or.inl hL)
        · exact Or.inr (Or.inl hR)
    have hI : U ∩ V=N := by
      ext x
      constructor
      · rintro ⟨hx|hx,hy|hy⟩
        · exact (Set.disjoint_left.mp hdis hx hy).elim
        · exact hy
        · exact hx
        · exact hx
      · intro hx
        exact ⟨Or.inr hx,Or.inr hx⟩
    have hproper (A : Set S) (x : S) (hx : x ∉ A) : homologyInclusion S A 2 = 0 := by
      let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)
      let j : TopCat.of A ⟶ TopCat.of ↥({x}ᶜ : Set S) :=
        TopCat.ofHom ⟨fun a => ⟨a.val,fun he => hx (he ▸ a.property)⟩,
          continuous_subtype_val.subtype_mk _⟩
      have hh : j ≫ pairInclusion S ({x}ᶜ : Set S) = pairInclusion S A := by ext a; rfl
      change F.map (pairInclusion S A) = 0
      rw [← hh,F.map_comp]
      change F.map j ≫ homologyInclusion S ({x}ᶜ : Set S) 2 = 0
      rw [GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x,
        CategoryTheory.Limits.comp_zero]
    let p : S := e (⟨3/4,by norm_num⟩,1)
    let n : S := e (⟨-3/4,by norm_num⟩,1)
    have hp : p ∈ pos := ⟨(⟨3/4,by norm_num⟩,1),rfl⟩
    have hn : n ∈ neg := ⟨(⟨-3/4,by norm_num⟩,1),rfl⟩
    have hpN : p ∉ N := by
      rintro ⟨z,hz,hh⟩
      have heq := congrArg (fun z : Set.Ioo (-1:ℝ) 1 × Circle => z.1.val) (he.injective hh)
      have hhi := hz.2
      dsimp [p] at heq
      linarith
    have hnN : n ∉ N := by
      rintro ⟨z,hz,hh⟩
      have heq := congrArg (fun z : Set.Ioo (-1:ℝ) 1 × Circle => z.1.val) (he.injective hh)
      have hlo := hz.1
      dsimp [n] at heq
      linarith
    have hfinish (x y : S) (hx : x ∈ L) (hy : y ∈ R) (hxN : x ∉ N) (hyN : y ∉ N) :
        homologyInclusion S U 2=0 ∧ homologyInclusion S V 2=0 := by
      constructor
      · apply hproper U y
        rintro (hyL|hyN')
        · exact Set.disjoint_left.mp hdis hyL hy
        · exact hyN hyN'
      · apply hproper V x
        rintro (hxR|hxN')
        · exact Set.disjoint_left.mp hdis hx hxR
        · exact hxN hxN'
    have hzero : homologyInclusion S U 2=0 ∧ homologyInclusion S V 2=0 := by
      rcases hopposite with ⟨hP,hN⟩|⟨hP,hN⟩
      · exact hfinish p n (hP hp) (hN hn) hpN hnN
      · exact hfinish n p (hN hn) (hP hp) hnN hpN
    exact ⟨U,V,N,hLO.union hNO,hRO.union hNO,hNO,hUV,hI,hcoreN,hzero.1,hzero.2,rfl⟩
  have hMV (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
      (U V : Set S) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V=Set.univ)
      (hUZ : homologyInclusion S U 2=0) (hVZ : homologyInclusion S V 2=0)
      (f : C(Circle,↥(U ∩ V)))
      (hgen : ∀ q : H ↥(U ∩ V) 1, ∃ n : ℤ,
        n • HomologicalComplex.homologyMap
          (actualSingularFunctor.map (TopCat.ofHom f)) 1
          CircleFundamentalCycle.fundamentalClass=q) :
      HomologicalComplex.homologyMap (actualSingularFunctor.map
        (TopCat.ofHom f ≫ pairInclusion S (U ∩ V))) 1
          CircleFundamentalCycle.fundamentalClass=0 := by
    classical
    let d := actualMVConnecting (TopCat.of S) U V hU hV hcover 1
    have hsum : actualMVSum (TopCat.of S) U V 2=0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro q
      rw [actualMVSum_apply,hUZ,hVZ]
      simp
    have hdMono : Mono d :=
      (ShortComplex.exact_iff_mono _ hsum).mp
        (actualMV_exact_ambient (TopCat.of S) U V hU hV hcover 1)
    have hdInj := (ModuleCat.mono_iff_injective d).mp hdMono
    obtain ⟨e2⟩ := hS.2.2.1
    let z : H S 2 := e2.inv 1
    have hz : z ≠ 0 := by
      intro hh
      have he := e2.toLinearEquiv.apply_symm_apply (1:ℤ)
      change e2.hom z=1 at he
      rw [hh,map_zero] at he
      exact zero_ne_one he
    have hdz : d z ≠ 0 := by
      intro hh
      apply hz
      exact hdInj (hh.trans d.hom.map_zero.symm)
    obtain ⟨n,hn⟩ := hgen (d z)
    have hn0 : n ≠ 0 := by
      intro hh
      rw [hh,zero_smul] at hn
      exact hdz hn.symm
    have hdiff := congrArg (fun m => m z)
      (actualMVConnecting_difference (TopCat.of S) U V hU hV hcover 1)
    change actualMVDifference (TopCat.of S) U V 1 (d z)=0 at hdiff
    rw [actualMVDifference_apply] at hdiff
    have hleft : actualSubsetHomologyMap (TopCat.of S) (U ∩ V) U Set.inter_subset_left 1 (d z)=0 :=
      congrArg Prod.fst hdiff
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)
    have hj : singularSubsetInclusion (TopCat.of S) (U ∩ V) U Set.inter_subset_left ≫
        pairInclusion S U=pairInclusion S (U ∩ V) := by ext x; rfl
    have hinc : homologyInclusion S (U ∩ V) 1 (d z)=0 := by
      change F.map (pairInclusion S (U ∩ V)) (d z)=0
      rw [←hj,F.map_comp]
      change homologyInclusion S U 1
        (actualSubsetHomologyMap (TopCat.of S) (U ∩ V) U Set.inter_subset_left 1 (d z))=0
      rw [hleft,map_zero]
    let y : H S 1 := homologyInclusion S (U ∩ V) 1
      (HomologicalComplex.homologyMap (actualSingularFunctor.map (TopCat.ofHom f)) 1
        CircleFundamentalCycle.fundamentalClass)
    have hny : n • y=0 := by
      rw [←hn] at hinc
      rw [map_zsmul] at hinc
      exact hinc
    obtain ⟨e1⟩ := hS.2.2.2
    have hy : y=0 := by
      apply e1.toLinearEquiv.injective
      rw [map_zero]
      have he : n • e1.hom y=0 := by
        rw [←map_zsmul,hny,map_zero]
      funext i
      have hi := congrFun he i
      change n * e1.hom y i=0 at hi
      exact (mul_eq_zero.mp hi).resolve_left hn0
    have hm := congrArg (fun m => m CircleFundamentalCycle.fundamentalClass)
      (HomologicalComplex.homologyMap_comp
        (actualSingularFunctor.map (TopCat.ofHom f))
        (actualSingularFunctor.map (pairInclusion S (U ∩ V))) 1)
    rw [←actualSingularFunctor.map_comp] at hm
    exact hm.trans hy
  have hGen (X : Type) [TopologicalSpace X]
      (h : (Set.Ioo (-1/2:ℝ) (1/2) × Circle) ≃ₜ X) :
      ∀ q : H X 1, ∃ n : ℤ,
        n • HomologicalComplex.homologyMap
          (actualSingularFunctor.map (TopCat.ofHom
            ⟨fun w => h (⟨0,by norm_num⟩,w),by fun_prop⟩)) 1
          CircleFundamentalCycle.fundamentalClass=q := by
    let a : C(Circle,X) := ⟨fun w => h (⟨0,by norm_num⟩,w),by fun_prop⟩
    let r : C(X,Circle) := ⟨fun x => (h.symm x).2,by fun_prop⟩
    have hwidth (t : unitInterval) (u : Set.Ioo (-1/2:ℝ) (1/2)) :
        (1-(t:ℝ))*(u:ℝ) ∈ Set.Ioo (-1/2:ℝ) (1/2) := by
      have h0 := t.property.1
      have h1 := t.property.2
      have hL := u.property.1
      have hR := u.property.2
      have hp := mul_nonneg h0 (le_of_lt (by linarith : 0 < (u:ℝ)+1/2))
      have hm := mul_nonneg h0 (le_of_lt (by linarith : 0 < 1/2-(u:ℝ)))
      constructor <;> nlinarith
    let Ht : ContinuousMap.Homotopy (ContinuousMap.id X) (a.comp r) := {
      toFun := fun z => h (⟨(1-(z.1:ℝ))*((h.symm z.2).1:ℝ),hwidth z.1 (h.symm z.2).1⟩,
        (h.symm z.2).2)
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; simp
      map_one_left := by intro x; simp [a,r]
    }
    have hh : TopCat.Homotopy (𝟙 (TopCat.of X)) (TopCat.ofHom r ≫ TopCat.ofHom a) := Ht
    have hm := hh.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) 1
    rw [actualSingularFunctor.map_id,HomologicalComplex.homologyMap_id,
      actualSingularFunctor.map_comp,HomologicalComplex.homologyMap_comp] at hm
    intro q
    have hq := congrArg (fun m => m q) hm
    change q=HomologicalComplex.homologyMap (actualSingularFunctor.map (TopCat.ofHom a)) 1
      (HomologicalComplex.homologyMap (actualSingularFunctor.map (TopCat.ofHom r)) 1 q) at hq
    obtain ⟨n,hn⟩ := CircleFundamentalCycle.fundamentalClass_generates
      (HomologicalComplex.homologyMap (actualSingularFunctor.map (TopCat.ofHom r)) 1 q)
    refine ⟨n,?_⟩
    rw [←hn,map_zsmul] at hq
    exact hq.symm
  have hSmall (S : Type) [TopologicalSpace S]
      (e : C(Set.Ioo (-1:ℝ) 1 × Circle,S)) (he : IsOpenEmbedding e) :
      ∃ h : (Set.Ioo (-1/2:ℝ) (1/2) × Circle) ≃ₜ
          ↥(e '' {z : Set.Ioo (-1:ℝ) 1 × Circle | z.1.val ∈ Set.Ioo (-1/2:ℝ) (1/2)}),
        ∀ z, (h z).val=e (⟨z.1.val,⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩⟩,z.2) := by
    classical
    let j : Set.Ioo (-1/2:ℝ) (1/2) → Set.Ioo (-1:ℝ) 1 :=
      fun u => ⟨u.val,⟨by linarith [u.property.1],by linarith [u.property.2]⟩⟩
    have hj : IsEmbedding j := by
      apply (IsEmbedding.of_comp_iff (f:=j) (g:= (Subtype.val : Set.Ioo (-1:ℝ) 1 → ℝ)) IsEmbedding.subtypeVal).mp
      exact IsEmbedding.subtypeVal
    let q := e ∘ Prod.map j (id : Circle → Circle)
    have hq : IsEmbedding q := he.isEmbedding.comp (hj.prodMap IsEmbedding.id)
    have hEq : Set.range q = e ''
        {z : Set.Ioo (-1:ℝ) 1 × Circle | z.1.val ∈ Set.Ioo (-1/2:ℝ) (1/2)} := by
      ext x
      constructor
      · rintro ⟨z,rfl⟩
        exact ⟨(j z.1,z.2),z.1.property,rfl⟩
      · rintro ⟨z,hz,rfl⟩
        exact ⟨(⟨z.1.val,hz⟩,z.2),rfl⟩
    let h := hq.toHomeomorph.trans (Homeomorph.setCongr hEq)
    refine ⟨h,?_⟩
    intro z
    change (hq.toHomeomorph z).val= _
    rfl
  obtain ⟨U,V,N,hU,hV,hN,hUV,hI,hcN,hUZ,hVZ,hNEq⟩ := hCover S hS c hc e he hcore
  obtain ⟨h0,hh0⟩ := hSmall S e he
  have hEq : (e '' {z : Set.Ioo (-1:ℝ) 1 × Circle |
      z.1.val ∈ Set.Ioo (-1/2:ℝ) (1/2)})=U ∩ V := hNEq.symm.trans hI.symm
  let h := h0.trans (Homeomorph.setCongr hEq)
  let f : C(Circle,↥(U ∩ V)) := ⟨fun w => h (⟨0,by norm_num⟩,w),by fun_prop⟩
  have hfgen : ∀ q : H ↥(U ∩ V) 1, ∃ n : ℤ,
      n • HomologicalComplex.homologyMap (actualSingularFunctor.map (TopCat.ofHom f)) 1
        CircleFundamentalCycle.fundamentalClass=q := hGen ↥(U ∩ V) h
  have hfc : TopCat.ofHom f ≫ pairInclusion S (U ∩ V)=
      TopCat.ofHom ⟨c.map,c.embedded.continuous⟩ := by
    ext w
    change (h0 (⟨0,by norm_num⟩,w)).val=c.map w
    rw [hh0,hcore]
  have hz := hMV S hS U V hU hV hUV hUZ hVZ f hfgen
  rw [hfc] at hz
  exact hz
end CurveComplex
