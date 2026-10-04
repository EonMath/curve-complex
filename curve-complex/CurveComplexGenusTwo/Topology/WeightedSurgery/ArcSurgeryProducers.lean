import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions
namespace CurveComplex.HyperellipticModel
namespace ArcSurgery
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance instDecidableEqEssentialArcClass_arcSurgeryProducers (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

abbrev vertex (M : HyperellipticModel E S) (a : EssentialMarkedArc M) :=
  Quotient.mk (essentialArcSetoid M) a

def crossings (M : HyperellipticModel E S)
    (a b : EssentialMarkedArc M) : Set S := arcInterior M a ∩ arcInterior M b

/- Topological transversality: in an open marked-point-free disk chart the two
arc traces are the two coordinate axes. This needs no new smooth atlas on S. -/
def CrossesInDisk (M : HyperellipticModel E S)
    (a b : EssentialMarkedArc M) (p : S) : Prop :=
  ∃ U : Set S, ∃ _hU : IsOpen U, ∃ hp : p ∈ U,
    Disjoint U (M.cover.branch : Set S) ∧
    ∃ e : U ≃ₜ {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1},
      (e ⟨p, hp⟩).val = (0, 0) ∧
      (∀ x : U, x.val ∈ a.val.image ↔ (e x).val.2 = 0) ∧
      (∀ x : U, x.val ∈ b.val.image ↔ (e x).val.1 = 0)

/- One simultaneous family for the entire finite full subcomplex, not unrelated
choices for each face. Nonadjacent vertices may intersect each other. -/
structure FinitePosition (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M)) where
  rep : (v : {v // v ∈ F}) → EssentialMarkedArc M
  represents : ∀ v, vertex M (rep v) = v.val
  simplex_disjoint : ∀ v w, v ≠ w →
    IsArcSimplex M {v.val, w.val} →
      Disjoint (arcInterior M (rep v)) (arcInterior M (rep w))
  finite : ∀ v, (crossings M anchor (rep v)).Finite
  transverse : ∀ v p, p ∈ crossings M anchor (rep v) →
    CrossesInDisk M anchor (rep v) p
  distinct_crossings : ∀ v w, v ≠ w →
    Disjoint (crossings M anchor (rep v)) (crossings M anchor (rep w))
  minimal : ∀ v (b : EssentialMarkedArc M), vertex M b = v.val →
    (crossings M anchor b).Finite →
      (crossings M anchor (rep v)).ncard ≤ (crossings M anchor b).ncard

/- Intrinsic intersection count, minimized over the actual marked-isotopy class.
Finite-position existence must establish that the set being minimized is nonempty. -/
noncomputable def intersectionNumber (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (v : EssentialArcClass M) : ℕ :=
  sInf {n : ℕ | ∃ a : EssentialMarkedArc M, vertex M a = v ∧
    (crossings M anchor a).Finite ∧ n = (crossings M anchor a).ncard}

noncomputable def complexity (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M)) : ℕ :=
  ∑ v ∈ F, intersectionNumber M anchor v

/- Source pp.4–5: simultaneous minimal position. This PRODUCES the certificate. -/
structure FirstCrossing (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) where
  selected : {v // v ∈ F}
  t : Interval
  s : Interval
  t_interior : 0 < t.val ∧ t.val < 1
  s_interior : 0 < s.val ∧ s.val < 1
  same_point : anchor.val.map t = (P.rep selected).val.map s
  first : ∀ v (r : Interval), 0 < r.val → r.val < t.val →
    anchor.val.map r ∉ arcInterior M (P.rep v)

def spliceTrace (M : HyperellipticModel E S)
    (anchor old : EssentialMarkedArc M) (t s : Interval) (side : Bool) : Set S :=
  (anchor.val.map '' {r : Interval | r.val ≤ t.val}) ∪
    (old.val.map '' {r : Interval |
      if side then s.val ≤ r.val else r.val ≤ s.val})

/- Surgery data, with actual marked arcs for BOTH branches; essential branches
are retained, inessential ones discarded. Push-offs fix the marked points.
The certificate is an output, never an assumption of the acyclicity theorem. -/
structure SurgeryPair (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P) where
  raw : Bool → MarkedArc M
  raw_trace : ∀ side, (raw side).image =
    spliceTrace M anchor (P.rep x.selected) x.t x.s side
  raw_start : ∀ side, (raw side).map ⟨0, by norm_num⟩ =
    anchor.val.map ⟨0, by norm_num⟩
  raw_end : ∀ side, (raw side).map ⟨1, by norm_num⟩ =
    (P.rep x.selected).val.map
      (if side then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩)
  retained : Finset Bool
  retained_iff : ∀ side, side ∈ retained ↔ IsEssentialMarkedArc M (raw side)
  nonempty : retained.Nonempty
  pushed : (side : {side // side ∈ retained}) → EssentialMarkedArc M
  push_isotopy : ∀ side,
    MarkedIsotopyRel M (raw side.val).image (pushed side).val.image
  pushed_disjoint : ∀ i j, i ≠ j →
    Disjoint (arcInterior M (pushed i)) (arcInterior M (pushed j))
  disjoint_old : ∀ side,
    Disjoint (arcInterior M (pushed side)) (arcInterior M (P.rep x.selected))
  disjoint_neighbors : ∀ side v, v ≠ x.selected →
    IsArcSimplex M {v.val, x.selected.val} →
      Disjoint (arcInterior M (pushed side)) (arcInterior M (P.rep v))
  finite : ∀ side, (crossings M anchor (pushed side)).Finite
  decreases : ∀ side,
    (crossings M anchor (pushed side)).ncard <
      (crossings M anchor (P.rep x.selected)).ncard
  total_decreases :
    (∑ side ∈ retained.attach, (crossings M anchor (pushed side)).ncard) <
      (crossings M anchor (P.rep x.selected)).ncard

/- The missing outermost geometric producer, including loops and discarded
inessential branches. Quotient duplicates are removed by Finset.image later. -/
noncomputable def replacementClasses (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R : SurgeryPair M anchor F P x) : Finset (EssentialArcClass M) :=
  R.retained.attach.image (fun side => vertex M (R.pushed side))

/- Old and both surviving new classes lie in one simplex for every incident
face, including when a new class equals an old vertex. -/
structure FiniteContraction (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M)) where
  stages : ℕ
  map : Fin (stages + 1) → EssentialArcClass M → EssentialArcClass M
  starts : ∀ v ∈ F, map ⟨0, by omega⟩ v = v
  simplicial : ∀ i σ, σ ⊆ F → IsArcSimplex M σ →
    IsArcSimplex M (σ.image (map i))
  contiguous : ∀ (i : ℕ) (hi : i < stages) σ,
    σ ⊆ F → IsArcSimplex M σ →
      IsArcSimplex M (σ.image (map ⟨i, by omega⟩) ∪
        σ.image (map ⟨i + 1, by omega⟩))
  ends_in_star : ∀ σ, σ ⊆ F → IsArcSimplex M σ →
    IsArcSimplex M (insert (vertex M anchor)
      (σ.image (map ⟨stages, by omega⟩)))

/- Finite simplicial approximation of the surgery argument. This is a producer
with NO contraction or filling hypothesis. This finite variant is sufficient
for homology; it does not assert a globally canonical vertexwise flow. -/

end ArcSurgery
end CurveComplex.HyperellipticModel
