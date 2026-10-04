import Mathlib

namespace CurveComplex
open Set Topology
set_option maxHeartbeats 4000000
/-- Doubling a supported strict crossing decrease across a disjoint involutive
translate remains a strict decrease. The restored symmetry is constructed;
no paired crossing-count certificate is an input. -/
theorem paired_supported_homeomorph_crossing_drop
    {E : Type} [TopologicalSpace E]
    (τ H : E ≃ₜ E) (hτ : ∀ x, τ (τ x) = x)
    (V : Set E) (hsep : Disjoint V (τ '' V))
    (hfix : ∀ x, x ∉ V → H x = x)
    (A B : Set E) (hA : τ '' A = A) (hB : τ '' B = B)
    (hOld : (A ∩ B).Finite) (hNew : (H '' A ∩ B).Finite)
    (hdrop : (H '' A ∩ B).ncard < (A ∩ B).ncard) :
    let J := (τ.trans H).trans τ
    let K := H.trans J
    (K '' A ∩ B).Finite ∧ (K '' A ∩ B).ncard < (A ∩ B).ncard := by
  classical
  let W := τ '' V
  let J := (τ.trans H).trans τ
  let K := H.trans J
  let O := A ∩ B
  let N := H '' A ∩ B
  let P := K '' A ∩ B
  have hτmem (C : Set E) (x : E) : x ∈ τ '' C ↔ τ x ∈ C := by
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [hτ] using hy
    · intro hx
      exact ⟨τ x,hx,hτ x⟩
  have hAτ (x : E) : τ x ∈ A ↔ x ∈ A := by rw [← hτmem A x,hA]
  have hBτ (x : E) : τ x ∈ B ↔ x ∈ B := by rw [← hτmem B x,hB]
  have hVW (x : E) : x ∈ W ↔ τ x ∈ V := hτmem V x
  have hHV (x : E) : H x ∈ V ↔ x ∈ V := by
    constructor
    · intro hx
      by_contra hn
      rw [hfix x hn] at hx
      exact hn hx
    · intro hx
      by_contra hn
      have he : H (H x) = H x := hfix _ hn
      have he' : H x = x := H.injective he
      exact hn (he'.symm ▸ hx)
  have hJfix (x : E) (hx : x ∉ W) : J x = x := by
    change τ (H (τ x)) = x
    rw [hfix _ (fun h => hx ((hVW x).mpr h)),hτ]
  have outsideImage (F : E ≃ₜ E) (U : Set E)
      (hF : ∀ x, x ∉ U → F x = x) (C : Set E) (x : E) (hx : x ∉ U) :
      x ∈ F '' C ↔ x ∈ C := by
    constructor
    · rintro ⟨y,hy,he⟩
      have hyx : y = x := F.injective (he.trans (hF x hx).symm)
      exact hyx ▸ hy
    · intro hc
      exact ⟨x,hc,hF x hx⟩
  have hKimage : K '' A = J '' (H '' A) := by rw [Set.image_image]; rfl
  have hPoutside (x : E) (hx : x ∉ W) : x ∈ P ↔ x ∈ N := by
    change (x ∈ K '' A ∧ x ∈ B) ↔ (x ∈ H '' A ∧ x ∈ B)
    rw [hKimage,outsideImage J W hJfix (H '' A) x hx]
  have hPinsideW (x : E) (hx : x ∈ W) : x ∈ P ↔ τ x ∈ N := by
    have hxV : τ x ∈ V := (hVW x).mp hx
    have hIntermediate (u : E) (hu : u ∈ V) : u ∈ τ '' (H '' A) ↔ u ∈ A := by
      have hτuW : τ u ∈ W := Set.mem_image_of_mem τ hu
      have hτuNV : τ u ∉ V := fun h => Set.disjoint_left.mp hsep h hτuW
      rw [hτmem,outsideImage H V hfix A (τ u) hτuNV,hAτ]
    have hHlocal : τ x ∈ H '' (τ '' (H '' A)) ↔ τ x ∈ H '' A := by
      constructor
      · rintro ⟨u,hu,he⟩
        have huV : u ∈ V := (hHV u).mp (he.symm ▸ hxV)
        exact ⟨u,(hIntermediate u huV).mp hu,he⟩
      · rintro ⟨u,hu,he⟩
        have huV : u ∈ V := (hHV u).mp (he.symm ▸ hxV)
        exact ⟨u,(hIntermediate u huV).mpr hu,he⟩
    have hKτimage : K '' A = τ '' (H '' (τ '' (H '' A))) := by
      simp only [Set.image_image]
      rfl
    change (x ∈ K '' A ∧ x ∈ B) ↔ (τ x ∈ H '' A ∧ τ x ∈ B)
    rw [hKτimage,hτmem,hHlocal,hBτ]
  have hPV : P ∩ V = N ∩ V := by
    ext x
    by_cases hx : x ∈ V
    · have hxNW : x ∉ W := fun h => Set.disjoint_left.mp hsep hx h
      simp only [Set.mem_inter_iff,hx,and_true,hPoutside x hxNW]
    · simp only [Set.mem_inter_iff,hx,and_false]
  have hPW : P ∩ W = τ '' (N ∩ V) := by
    ext x
    rw [hτmem,Set.mem_inter_iff,Set.mem_inter_iff]
    constructor
    · rintro ⟨hp,hw⟩
      exact ⟨(hPinsideW x hw).mp hp,(hVW x).mp hw⟩
    · rintro ⟨hn,hv⟩
      have hw := (hVW x).mpr hv
      exact ⟨(hPinsideW x hw).mpr hn,hw⟩
  have hOW : O ∩ W = τ '' (O ∩ V) := by
    ext x
    rw [hτmem]
    change (x ∈ A ∧ x ∈ B) ∧ x ∈ W ↔ (τ x ∈ A ∧ τ x ∈ B) ∧ τ x ∈ V
    rw [hAτ,hBτ,hVW]
  have hNW : N ∩ W = O ∩ W := by
    ext x
    by_cases hx : x ∈ W
    · have hxNV : x ∉ V := fun h => Set.disjoint_left.mp hsep h hx
      change (x ∈ H '' A ∧ x ∈ B) ∧ x ∈ W ↔ (x ∈ A ∧ x ∈ B) ∧ x ∈ W
      rw [outsideImage H V hfix A x hxNV]
    · simp only [Set.mem_inter_iff,hx,and_false]
  have hNR : N \ (V ∪ W) = O \ (V ∪ W) := by
    ext x
    by_cases hx : x ∈ V ∪ W
    · simp only [Set.mem_sdiff,Set.mem_union,hx,not_true_eq_false,and_false]
    · have hxNV : x ∉ V := fun h => hx (Or.inl h)
      change (x ∈ H '' A ∧ x ∈ B) ∧ x ∉ V ∪ W ↔ (x ∈ A ∧ x ∈ B) ∧ x ∉ V ∪ W
      rw [outsideImage H V hfix A x hxNV]
  have hPR : P \ (V ∪ W) = O \ (V ∪ W) := by
    ext x
    by_cases hx : x ∈ V ∪ W
    · simp only [Set.mem_sdiff,hx,not_true_eq_false,and_false]
    · have hxNW : x ∉ W := fun h => hx (Or.inr h)
      have hxNV : x ∉ V := fun h => hx (Or.inl h)
      change (x ∈ P ∧ x ∉ V ∪ W) ↔ (x ∈ O ∧ x ∉ V ∪ W)
      rw [hPoutside x hxNW]
      change ((x ∈ H '' A ∧ x ∈ B) ∧ x ∉ V ∪ W) ↔ ((x ∈ A ∧ x ∈ B) ∧ x ∉ V ∪ W)
      rw [outsideImage H V hfix A x hxNV]
  have split (X : Set E) : X = (X ∩ V ∪ X ∩ W) ∪ (X \ (V ∪ W)) := by
    ext x
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_sdiff]
    tauto
  have hPfin : P.Finite := by
    rw [split P,hPV,hPW,hPR]
    exact ((hNew.inter_of_left V).union ((hNew.inter_of_left V).image τ)).union
      hOld.sdiff
  have splitcard (X : Set E) (hX : X.Finite) :
      X.ncard = (X ∩ V).ncard + (X ∩ W).ncard + (X \ (V ∪ W)).ncard := by
    have hdisj : Disjoint (X ∩ V) (X ∩ W) := hsep.mono inter_subset_right inter_subset_right
    have hdisjR : Disjoint (X ∩ V ∪ X ∩ W) (X \ (V ∪ W)) := by
      apply Set.disjoint_left.mpr
      rintro x (⟨hx,hv⟩ | ⟨hx,hw⟩) ⟨hx',hn⟩
      · exact hn (Or.inl hv)
      · exact hn (Or.inr hw)
    calc
      X.ncard = ((X ∩ V ∪ X ∩ W) ∪ (X \ (V ∪ W))).ncard := congrArg Set.ncard (split X)
      _ = (X ∩ V ∪ X ∩ W).ncard + (X \ (V ∪ W)).ncard :=
        Set.ncard_union_eq hdisjR ((hX.inter_of_left V).union (hX.inter_of_left W)) hX.sdiff
      _ = _ := by rw [Set.ncard_union_eq hdisj (hX.inter_of_left V) (hX.inter_of_left W)]
  have hOc := splitcard O hOld
  have hNc := splitcard N hNew
  have hPc := splitcard P hPfin
  rw [hOW,Set.ncard_image_of_injective _ τ.injective] at hOc
  rw [hNW,hOW,Set.ncard_image_of_injective _ τ.injective,hNR] at hNc
  rw [hPV,hPW,Set.ncard_image_of_injective _ τ.injective,hPR] at hPc
  change N.ncard < O.ncard at hdrop
  exact ⟨hPfin,by change P.ncard < O.ncard; omega⟩
end CurveComplex
