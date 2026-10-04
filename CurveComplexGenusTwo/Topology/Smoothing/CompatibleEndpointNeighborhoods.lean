import CurveComplexGenusTwo.Topology.Smoothing.ActualSmoothChartStar

open Set
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The six actual marked stars have pairwise disjoint smooth-coordinate
neighborhoods, simultaneously avoiding all central and nonincident arc pieces.
These are actual support regions for independently assembling vertex moves. -/
theorem compatible_actual_endpoint_neighborhoods
    (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
    (ι : Type) [Fintype ι] (a : ι → EssentialMarkedArc M) :
    letI := C.charts
    ∃ U : {p : S // p ∈ M.cover.branch} → Set S,
      (∀ p, IsOpen (U p) ∧ p.val ∈ U p ∧
        U p ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p.val).source) ∧
      (∀ p q, p ≠ q → Disjoint (U p) (U q)) ∧
      (∀ p i t, (1 / 4 : ℝ) ≤ (t : Interval).val →
        t.val ≤ 3 / 4 → (a i).val.map t ∉ U p) ∧
      ∀ p i, (a i).val.map ⟨0, by norm_num⟩ ≠ p.val →
        (a i).val.map ⟨1, by norm_num⟩ ≠ p.val → Disjoint (a i).val.image (U p) := by
  classical
  letI := C.charts
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  let P := {p : S // p ∈ M.cover.branch}
  have hpairs (p q : P) : ∃ A B : Set S,
      IsOpen A ∧ IsOpen B ∧ p.val ∈ A ∧ q.val ∈ B ∧ (p ≠ q → Disjoint A B) := by
    by_cases hpq : p = q
    · exact ⟨univ, univ, isOpen_univ, isOpen_univ, mem_univ _, mem_univ _,
        fun hn => (hn hpq).elim⟩
    · have hdis : Disjoint ({p.val} : Set S) {q.val} := by
        rw [Set.disjoint_singleton]
        exact fun heq => hpq (Subtype.ext heq)
      obtain ⟨A, B, hA, hB, hpA, hqB, hAB⟩ :=
        normal_separation isClosed_singleton isClosed_singleton hdis
      exact ⟨A, B, hA, hB, hpA (mem_singleton _), hqB (mem_singleton _), fun _ => hAB⟩
  choose A B hA hB hpA hqB hAB using hpairs
  have hlocal (p : P) := actual_endpoint_star_in_smooth_chart M C ι a p.val p.property
  choose V hV hpV hchart hmarks hcentral hnoninc hrest using hlocal
  let U : P → Set S := fun p => V p ∩ (⋂ q : P, A p q) ∩ (⋂ q : P, B q p)
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro p
    refine ⟨((hV p).inter (isOpen_iInter_of_finite (hA p))).inter
      (isOpen_iInter_of_finite (fun q => hB q p)), ?_, ?_⟩
    · exact ⟨⟨hpV p, mem_iInter.mpr (hpA p)⟩, mem_iInter.mpr (fun q => hqB q p)⟩
    · intro x hx
      exact hchart p hx.1.1
  · intro p q hpq
    exact (hAB p q hpq).mono
      (fun x hx => mem_iInter.mp hx.1.2 q)
      (fun x hx => mem_iInter.mp hx.2 p)
  · intro p i t ht0 ht1 hx
    exact hcentral p i t ht0 ht1 hx.1.1
  · intro p i hi0 hi1
    exact (hnoninc p i hi0 hi1).mono_right (fun x hx => hx.1.1)

#print axioms compatible_actual_endpoint_neighborhoods
end CurveComplex.HyperellipticModel
