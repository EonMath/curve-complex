import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTerminalEndpointAlignment

open Set Topology Schoenflies CurveComplex

/-- Choose an ACTUAL interior physical fiber avoiding both the mark and the
reference orbit, and an ACTUAL source point on that fiber. The two explicit
candidate fibers cannot both contain a translate of the marked first coordinate. -/
theorem actual_terminal_source_has_puncture_free_interior_fiber
    (G : C(ℝ,Plane)) (c r : ℝ) (p : Plane)
    (hLeft : G r 0=c) (hRight : G (r+2*Real.pi) 0=c+2*Real.pi) :
    ∃ b s : ℝ, c<b ∧ b<c+2*Real.pi ∧ s∈Ioo r (r+2*Real.pi) ∧ G s 0=b ∧
      (∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠b) ∧
      (∀ i : ℤ, c+(i:ℝ)*(2*Real.pi)≠b) := by
  let b₁ := c+2*Real.pi/3
  let b₂ := c+4*Real.pi/3
  have hB₁ : c<b₁ ∧ b₁<c+2*Real.pi := by dsimp [b₁]; constructor <;> linarith [Real.pi_pos]
  have hB₂ : c<b₂ ∧ b₂<c+2*Real.pi := by dsimp [b₂]; constructor <;> linarith [Real.pi_pos]
  have hCandidate : ∃ b : ℝ, c<b ∧ b<c+2*Real.pi ∧
      ∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠b := by
    by_cases h₁ : ∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠b₁
    · exact ⟨b₁,hB₁.1,hB₁.2,h₁⟩
    · push Not at h₁
      obtain ⟨i,hi⟩ := h₁
      refine ⟨b₂,hB₂.1,hB₂.2,?_⟩
      intro j hj
      have hh : (3:ℝ)*((j:ℝ)-(i:ℝ))=1 := by dsimp [b₁] at hi; dsimp [b₂] at hj; nlinarith [Real.pi_pos]
      have hhZ : (3:ℤ)*(j-i)=1 := by exact_mod_cast hh
      omega
  obtain ⟨b,hcb,hbc,hb⟩ := hCandidate
  have hRef (i : ℤ) : c+(i:ℝ)*(2*Real.pi)≠b := by
    intro hi
    by_cases hi0 : i≤0
    · have hh : (i:ℝ)≤0 := by exact_mod_cast hi0
      nlinarith [Real.pi_pos]
    · have hi1 : (1:ℤ)≤ i := by omega
      have hh : (1:ℝ)≤(i:ℝ) := by exact_mod_cast hi1
      nlinarith [Real.pi_pos]
  have hCont : Continuous (fun x : ℝ => G x 0) := by fun_prop
  obtain ⟨s,hs,hGs⟩ := intermediate_value_Icc (by linarith [Real.pi_pos] : r≤r+2*Real.pi)
    hCont.continuousOn (by simpa only [hLeft,hRight] using (show b∈Icc c (c+2*Real.pi) from ⟨hcb.le,hbc.le⟩))
  change G s 0=b at hGs
  have hsLeft : r<s := by
    by_contra hn
    have he : s=r := le_antisymm (le_of_not_gt hn) hs.1
    have hh := he ▸ hGs
    rw [hLeft] at hh
    linarith
  have hsRight : s<r+2*Real.pi := by
    by_contra hn
    have he : s=r+2*Real.pi := le_antisymm hs.2 (le_of_not_gt hn)
    have hh := he ▸ hGs
    rw [hRight] at hh
    linarith
  exact ⟨b,s,hcb,hbc,⟨hsLeft,hsRight⟩,hGs,hb,hRef⟩

#print axioms actual_terminal_source_has_puncture_free_interior_fiber
