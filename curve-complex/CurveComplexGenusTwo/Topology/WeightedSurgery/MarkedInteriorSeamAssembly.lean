import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedIntervalMesh

namespace CurveComplex.HyperellipticModel
open Set Schoenflies CurveComplex.ArcFinitePosition
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Internal seams of the literal new-arc mesh are repaired by a genuine
marked-fixing isotopy whose support avoids both complete exterior tails. -/
theorem actual_new_arc_internal_mesh_seam_repair
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M)
    (hne : ∀ i, (old i).val.map 0 ≠ (old i).val.map 1)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M) (ha : a.val.map 0 ≠ a.val.map 1)
    (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1) :
    ∃ η : C(Interval,S),
      (∀ t, η t = a.val.map ⟨l+(u-l)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩) ∧
      Topology.IsClosedEmbedding η ∧
      ∃ n : ℕ, ∃ hn : 0 < n,
      ∃ e : Fin n → OpenPartialHomeomorph S Plane, ∃ label : Fin n → Option ι,
      ∃ H : AmbientIsotopy S, ∃ b : EssentialMarkedArc M,
        (∀ k, Disjoint (e k).source (M.cover.branch : Set S)) ∧
        (∀ k j x, x ∈ (e k).source →
          (x ∈ (old j).val.image ↔ label k = some j ∧ e k x 0 = 0)) ∧
        Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
        (∀ t, b.val.map t = H.finalMap (a.val.map t)) ∧
        (∀ t : Interval, (t:ℝ) ≤ l ∨ u ≤ (t:ℝ) → b.val.map t = a.val.map t) ∧
        (∀ k t, H.finalMap (η (intervalMeshParameter n hn k t)) ∈ (e k).source) ∧
        ∀ k : Fin (n-1), ∀ j,
          H.finalMap (η ⟨((k.val:ℝ)+1)/n,by
            have hnR : (0:ℝ) < n := by exact_mod_cast hn
            constructor
            · positivity
            · apply (div_le_one hnR).mpr
              have hk : k.val+1 ≤ n := by omega
              exact_mod_cast hk⟩) ∉ (old j).val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨η,hη,hi,n,hn,e,label,hemarks,hlabel,hchart⟩ :=
    actual_new_arc_compact_interior_chart_subdivision M old hne hd a ha l u hl hlu hu
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let σ : Fin (n-1) → Interval := fun k => ⟨((k.val:ℝ)+1)/n,by
    constructor
    · positivity
    · apply (div_le_one hnR).mpr
      have hk : k.val+1 ≤ n := by omega
      exact_mod_cast hk⟩
  have hσ0 (k : Fin (n-1)) : 0 < (σ k:ℝ) := div_pos (by positivity) hnR
  have hσ1 (k : Fin (n-1)) : (σ k:ℝ) < 1 := by
    apply (div_lt_one hnR).mpr
    have hk : k.val+1 < n := by omega
    exact_mod_cast hk
  let p : Fin (n-1) → S := fun k => η (σ k)
  have hpi : Function.Injective p := by
    intro k j he
    have hh := congrArg Subtype.val (hi.injective he)
    change ((k.val:ℝ)+1)/n = ((j.val:ℝ)+1)/n at hh
    have hh' := (div_left_inj' hnR.ne').mp hh
    apply Fin.ext
    exact Nat.cast_injective (by linarith : (k.val:ℝ) = j.val)
  have hpm (k : Fin (n-1)) : p k ∉ M.cover.branch := by
    rw [show p k = η (σ k) from rfl,hη]
    intro hm
    rcases a.val.marked_only_at_ends _ hm with he | he
    · have hh := congrArg Subtype.val he
      change l+(u-l)*(σ k:ℝ) = 0 at hh
      nlinarith [hσ0 k]
    · have hh := congrArg Subtype.val he
      change l+(u-l)*(σ k:ℝ) = 1 at hh
      nlinarith [hσ1 k]
  let tailParameters : Set Interval := {t | (t:ℝ) ≤ l ∨ u ≤ (t:ℝ)}
  let tails : Set S := a.val.map '' tailParameters
  have htailClosed : IsClosed tailParameters :=
    (isClosed_le continuous_subtype_val continuous_const).union
      (isClosed_le continuous_const continuous_subtype_val)
  have htails : IsClosed tails := (htailClosed.isCompact.image a.val.continuous).isClosed
  have hpTail (k : Fin (n-1)) : p k ∉ tails := by
    rintro ⟨t,ht,he⟩
    rw [show p k = η (σ k) from rfl,hη] at he
    have heq := congrArg Subtype.val (NonLoopArc.injective ⟨a.val,ha⟩ he)
    change (t:ℝ) = l+(u-l)*(σ k:ℝ) at heq
    rcases ht with ht | ht <;> nlinarith [hσ0 k,hσ1 k]
  let arc : Fin n → C(Interval,S) := fun k =>
    ⟨η ∘ intervalMeshParameter n hn k,η.continuous.comp (intervalMeshParameter_continuous n hn k)⟩
  have hpiece (k : Fin n) : Set.range (arc k) ⊆ (e k).source := by
    rintro x ⟨t,rfl⟩
    apply hchart k
    · change (k.val:ℝ)/n ≤ ((k.val:ℝ)+(t:ℝ))/n
      exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith [t.property.1])
    · change ((k.val:ℝ)+(t:ℝ))/n ≤ (k.val+1:ℝ)/n
      exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith [t.property.2])
  obtain ⟨U,H,_,_,hUW,_,havoid,hmarks,hout,hpreserve⟩ :=
    actual_localized_marked_seam_repair M old hne hd p hpi hpm arc e hpiece
      (fun _ => tailsᶜ) (fun _ => htails.isOpen_compl) hpTail
  have htailfix (t : Interval) (x : S) (hx : x ∈ tails) : H.map (t,x) = x := by
    apply hout t x
    intro hh
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hh
    exact hUW k hk hx
  obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
  have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
    intro x hx; rw [← hfinal]; exact hmarks ⟨1,by norm_num⟩ x hx
  let b := a.transport g hfix
  refine ⟨η,hη,hi,n,hn,e,label,H,b,hemarks,hlabel,?_,?_,?_,?_,havoid⟩
  · apply Eq.symm; apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    rw [hfinal]
    exact (MarkedArc.transport_image a.val g hfix).symm
  · intro t; change g (a.val.map t) = H.finalMap (a.val.map t); rw [hfinal]
  · intro t ht
    change g (a.val.map t) = a.val.map t
    rw [← hfinal]
    exact htailfix 1 _ ⟨t,ht,rfl⟩
  · intro k t
    exact hpreserve k 1 ⟨η (intervalMeshParameter n hn k t),Set.mem_range_self t,rfl⟩

end CurveComplex.HyperellipticModel
