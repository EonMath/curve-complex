import CurveComplexGenusTwo.Topology.Smoothing.FiniteIntervalCompatibleChartsProof
import CurveComplexGenusTwo.Foundations.Definitions
universe u
namespace CurveComplex.HyperellipticModel
/-- Select compatible disjoint actual square-crosscut patches for a specified
finite collection of disjoint central parameter subarcs, inside their assigned
old-family charts. Their compact patches meet the whole curve in EXACTLY the
selected central subarcs. -/
theorem actual_marked_finite_compatible_crosscuts
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (c : EssentialMarkedArc M) (K : Type*) [Fintype K]
    (a b : K → ℝ) (hab : ∀ k, a k < b k)
    (ha : ∀ k, 0 < a k) (hb : ∀ k, b k < 1)
    (e : K → OpenPartialHomeomorph S Schoenflies.Plane)
    (hsub : ∀ k, (c.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (a k) (b k) ⊆ (e k).source)
    (hdis : ∀ i j, i ≠ j → Disjoint
      ((c.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (a i) (b i))
      ((c.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (a j) (b j))) :
    ∃ E : K → OpenPartialHomeomorph S Schoenflies.Plane,
      (∀ k, (E k).source ⊆ (e k).source) ∧
      (∀ i j, i ≠ j → Disjoint (E i).source (E j).source) ∧
      (∀ k, Schoenflies.Plane.closedSquare 0 1 ⊆ (E k).target) ∧
      (∀ k, (c.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (a k) (b k) ⊆ (E k).source) ∧
      (∀ k, E k ((c.val.map ∘ Set.projIcc 0 1 zero_le_one) (a k)) = Schoenflies.Plane.mk (-1) 0 ∧
        E k ((c.val.map ∘ Set.projIcc 0 1 zero_le_one) (b k)) = Schoenflies.Plane.mk 1 0) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ c.val.image ↔ E k x 1 = 0)) ∧
      (∀ k, {x : S | x ∈ (E k).source ∧ E k x ∈ Schoenflies.Plane.closedSquare 0 1} ∩
        c.val.image = (c.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (a k) (b k)) := by
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  let q := Fintype.equivFin K
  obtain ⟨F,hFsub,hFdis,hFsq,hFcore,hFends,hFflat,hFexact⟩ :=
    finite_actual_interval_compatible_crosscut_charts (Fin (Fintype.card K)) (fun _ => c.val.map)
    (fun _ => c.val.continuous) (fun _ => c.val.injective_except_loop_closure)
    (a ∘ q.symm) (b ∘ q.symm) (fun k => ha (q.symm k))
    (fun k => hab (q.symm k)) (fun k => hb (q.symm k)) (e ∘ q.symm)
    (fun k => hsub (q.symm k))
    (fun i j hij => hdis _ _ (fun he => hij (q.symm.injective he)))
  refine ⟨F ∘ q,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k; simpa using hFsub (q k)
  · intro i j hij; exact hFdis _ _ (fun he => hij (q.injective he))
  · intro k; exact hFsq (q k)
  · intro k; simpa using hFcore (q k)
  · intro k; simpa using hFends (q k)
  · intro k x hx; exact hFflat (q k) x hx
  · intro k; simpa [MarkedArc.image] using hFexact (q k)

end CurveComplex.HyperellipticModel
