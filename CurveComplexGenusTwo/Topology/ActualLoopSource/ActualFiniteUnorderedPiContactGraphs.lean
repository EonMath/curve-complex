import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteOrderedPiContactGraphs
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual source phase stripe indices select the direction themselves,
including equal stripes with no contacts. Construct ALL contacts as finitely
many disjoint embedded time graphs; no ordered bank assumption is supplied. -/
theorem actual_finite_unordered_pi_contact_graphs
    {X : Type} [TopologicalSpace X] (a b : C(X,ℝ)) (p q : ℤ)
    (ha : ∀ x, a x ∈ Ioo ((p:ℝ)*Real.pi) (((p:ℝ)+1)*Real.pi))
    (hb : ∀ x, b x ∈ Ioo ((q:ℝ)*Real.pi) (((q:ℝ)+1)*Real.pi)) :
    ∃ levels : Finset ℤ, ∃ γ : ↑levels → C(X,unitInterval),
      (∀ k x, 0<(γ k x:ℝ) ∧ (γ k x:ℝ)<1) ∧
      (∀ k, IsEmbedding (fun x => (γ k x,x))) ∧
      (∀ k l, k≠l → ∀ x, γ k x≠γ l x) ∧
      ∀ x (τ : unitInterval),
        (∃ k : ℤ, (1-(τ:ℝ))*a x+(τ:ℝ)*b x=(k:ℝ)*Real.pi) ↔
          ∃ k : ↑levels, τ=γ k x := by
  classical
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · obtain ⟨levels,γ,_,hproper,hemb,hdis,hiff⟩ :=
      actual_finite_ordered_pi_contact_graphs a b p q ha hb hpq
    refine ⟨levels,γ,hproper,hemb,hdis,?_⟩
    intro x τ
    constructor
    · rintro ⟨k,hk⟩
      obtain ⟨hmem,he⟩ := (hiff x τ k).mp hk
      exact ⟨⟨k,hmem⟩,he⟩
    · rintro ⟨k,hk⟩
      exact ⟨k.val,(hiff x τ k.val).mpr ⟨k.property,hk⟩⟩
  · subst q
    let levels : Finset ℤ := ∅
    have hnone (k : ↑levels) : False := by
      have hh := k.property
      change k.val ∈ (∅ : Finset ℤ) at hh
      exact Finset.notMem_empty k.val hh
    let γ : ↑levels → C(X,unitInterval) := fun k => False.elim (hnone k)
    refine ⟨levels,γ,(fun k => False.elim (hnone k)),(fun k => False.elim (hnone k)),
      (fun k => False.elim (hnone k)),?_⟩
    intro x τ
    constructor
    · rintro ⟨k,hk⟩
      exact False.elim (actual_affine_pi_same_stripe_no_contacts a b p ha hb x τ k hk)
    · rintro ⟨k,_⟩; exact False.elim (hnone k)
  · obtain ⟨levels,δ,_,hproper,_,hdis,hiff⟩ :=
      actual_finite_ordered_pi_contact_graphs b a q p hb ha hqp
    let γ : ↑levels → C(X,unitInterval) := fun k =>
      ⟨fun x => unitInterval.symmHomeomorph (δ k x), unitInterval.symmHomeomorph.continuous.comp (δ k).continuous⟩
    have hflip (k : ↑levels) (x : X) : unitInterval.symmHomeomorph (γ k x)=δ k x := by
      simp [γ]
    have hγproper (k : ↑levels) (x : X) : 0<(γ k x:ℝ) ∧ (γ k x:ℝ)<1 := by
      have hh := hproper k x
      change 0<1-(δ k x:ℝ) ∧ 1-(δ k x:ℝ)<1
      constructor <;> linarith
    have hγemb (k : ↑levels) : IsEmbedding (fun x => (γ k x,x)) := by
      apply IsEmbedding.of_comp ((γ k).continuous.prodMk continuous_id) continuous_snd
      exact IsEmbedding.id
    have hγdis (k l : ↑levels) (hkl : k≠l) (x : X) : γ k x≠γ l x := by
      intro he
      have hh := congrArg unitInterval.symmHomeomorph he
      rw [hflip,hflip] at hh
      exact hdis k l hkl x hh
    have hswap (x : X) (τ : unitInterval) :
        (1-(τ:ℝ))*a x+(τ:ℝ)*b x=
          (1-(unitInterval.symmHomeomorph τ:ℝ))*b x+
            (unitInterval.symmHomeomorph τ:ℝ)*a x := by
      change (1-(τ:ℝ))*a x+(τ:ℝ)*b x=(1-(1-(τ:ℝ)))*b x+(1-(τ:ℝ))*a x
      ring
    refine ⟨levels,γ,hγproper,hγemb,hγdis,?_⟩
    intro x τ
    constructor
    · rintro ⟨k,hk⟩
      rw [hswap] at hk
      obtain ⟨hm,he⟩ := (hiff x (unitInterval.symmHomeomorph τ) k).mp hk
      refine ⟨⟨k,hm⟩,unitInterval.symmHomeomorph.injective ?_⟩
      rw [hflip]; exact he
    · rintro ⟨k,he⟩
      have hh : unitInterval.symmHomeomorph τ=δ k x := by rw [he,hflip]
      refine ⟨k.val,?_⟩
      rw [hswap]
      exact (hiff x (unitInterval.symmHomeomorph τ) k.val).mpr ⟨k.property,hh⟩
end CurveComplex.HyperellipticModel
