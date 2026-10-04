import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualAffinePiContactIndexBounds
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Distinct ordered consecutive-π boundary stripes construct ALL contact
time graphs, a genuine finite family with embedded/disjoint parameter graphs.
No finite contact family, matching stages, or projection bank is supplied. -/
theorem actual_finite_ordered_pi_contact_graphs
    {X : Type} [TopologicalSpace X] (a b : C(X,ℝ)) (p q : ℤ)
    (ha : ∀ x, a x ∈ Ioo ((p:ℝ)*Real.pi) (((p:ℝ)+1)*Real.pi))
    (hb : ∀ x, b x ∈ Ioo ((q:ℝ)*Real.pi) (((q:ℝ)+1)*Real.pi)) (hpq : p<q) :
    ∃ levels : Finset ℤ, ∃ γ : ↑levels → C(X,unitInterval),
      levels=Finset.Icc (p+1) q ∧
      (∀ k x, 0<(γ k x:ℝ) ∧ (γ k x:ℝ)<1) ∧
      (∀ k, IsEmbedding (fun x => (γ k x,x))) ∧
      (∀ k l, k≠l → ∀ x, γ k x≠γ l x) ∧
      ∀ x (τ : unitInterval) (k : ℤ),
        (1-(τ:ℝ))*a x+(τ:ℝ)*b x=(k:ℝ)*Real.pi ↔
          ∃ hk : k ∈ levels, τ=γ ⟨k,hk⟩ x := by
  classical
  let levels : Finset ℤ := Finset.Icc (p+1) q
  have hlevels (k : ↑levels) : p<k.val ∧ k.val≤q :=
    ⟨Int.add_one_le_iff.mp (Finset.mem_Icc.mp k.property).1,(Finset.mem_Icc.mp k.property).2⟩
  choose γ hproper hformula hiff using (fun k : ↑levels =>
    actual_affine_pi_level_graph a b p q k.val ha hb (hlevels k).1 (hlevels k).2)
  have hemb (k : ↑levels) : IsEmbedding (fun x => (γ k x,x)) := by
    apply IsEmbedding.of_comp ((γ k).continuous.prodMk continuous_id) continuous_snd
    exact IsEmbedding.id
  have hdistinct (k l : ↑levels) (hkl : k≠l) (x : X) : γ k x≠γ l x := by
    intro he
    have hk := (hiff k x (γ k x)).mpr rfl
    have hl := (hiff l x (γ l x)).mpr rfl
    rw [he] at hk
    have hi : (k.val:ℝ)*Real.pi=(l.val:ℝ)*Real.pi := hk.symm.trans hl
    have hiv : (k.val:ℝ)=(l.val:ℝ) := mul_right_cancel₀ Real.pi_pos.ne' hi
    exact hkl (Subtype.ext (by exact_mod_cast hiv))
  refine ⟨levels,γ,rfl,hproper,hemb,hdistinct,?_⟩
  intro x τ k
  constructor
  · intro he
    have hk := actual_affine_pi_contact_index_bounds a b p q ha hb x τ k he
    have hk' : k ∈ levels := by simpa only [min_eq_left hpq.le,max_eq_right hpq.le] using hk
    exact ⟨hk',(hiff ⟨k,hk'⟩ x τ).mp he⟩
  · rintro ⟨hk,he⟩
    exact (hiff ⟨k,hk⟩ x τ).mpr he
end CurveComplex.HyperellipticModel
