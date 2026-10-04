import CurveComplexGenusTwo.Filtration.CarrierInverseHomotopies
open CategoryTheory Topology Convexity
open scoped Simplicial
open CurveComplexGenusTwo.CWHurewicz
namespace CurveGenusTwo.Filtration.UniverseSubdivision
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable def singularBoundaryFinsupp (X : TopCat.{u}) (n : ℕ) :
    ((TopCat.toSSet.obj X) _⦋n+1⦌ →₀ ℤ) →ₗ[ℤ] ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun x => ∑ i : Fin (n+2),
    (-1 : ℤ)^i.val • Finsupp.single ((TopCat.toSSet.obj X).δ i x) 1

theorem singularBoundaryFinsupp_single (X : TopCat.{u}) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n+1⦌) :
    singularBoundaryFinsupp X n (Finsupp.single x 1) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.single ((TopCat.toSSet.obj X).δ i x) 1 := by
  simp [singularBoundaryFinsupp]

noncomputable def singularBarycentricFinsupp (X : TopCat.{u}) (n : ℕ) :
    ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) →ₗ[ℤ] ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun x => ∑ π : Equiv.Perm (Fin (n+1)),
    (π.sign : ℤ) • Finsupp.single (barycentricFlagSingular X n π x) 1

theorem singularBarycentricFinsupp_single (X : TopCat.{u}) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularBarycentricFinsupp X n (Finsupp.single x 1) =
      ∑ π : Equiv.Perm (Fin (n+1)), (π.sign : ℤ) • Finsupp.single (barycentricFlagSingular X n π x) 1 := by
  simp [singularBarycentricFinsupp]

private theorem affineUniversalHomotopy_single (n m : ℕ)
    (f : affineSimplex n m) :
    affineUniversalHomotopy n m (Finsupp.single f 1) =
      affinePostcompose (n + 1) n m f (universalCarrierHomotopy n) := by
  simp [affineUniversalHomotopy]

private theorem affineBoundaryMap_single_identity (n : ℕ) :
    affineBoundaryMap n (n + 1)
        (Finsupp.single (standardAffineIdentity (n + 1)) 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        Finsupp.single (affineFaceInclusion n i) 1 := by
  simp only [affineBoundaryMap, Finsupp.linearCombination_single,
    affineBoundary, one_smul]
  congr 1
  funext i
  have hface : affineFace (standardAffineIdentity (n + 1)) i =
      affineFaceInclusion n i := by
    apply StdSimplex.affineMap_ext
    intro j
    simp [affineFace, affineFaceInclusion, standardAffineIdentity]
  rw [hface]

private theorem affinePostcompose_identity (k n : ℕ)
    (c : affineSimplex k n →₀ ℤ) :
    affinePostcompose k n n (standardAffineIdentity n) c = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single f a =>
      simp only [affinePostcompose, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single]
      congr 1
      apply StdSimplex.affineMap_ext
      intro j
      simp [standardAffineIdentity]

noncomputable def singularAffinePushforward (X : TopCat.{u}) (k n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    (affineSimplex k n →₀ ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj X) _⦋k⦌ →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun a =>
    (TopCat.toSSetObjEquiv X (.op ⦋k⦌)).symm
      ((TopCat.toSSetObjEquiv X (.op ⦋n⦌) x).comp (TopCat.toSSetObjEquiv (TopCat.of (StdSimplex ℝ (Fin (n+1)))) (.op ⦋k⦌) (affineAsSingular k n a))))

theorem singularAffinePushforward_single (X : TopCat.{u}) (k n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌)
    (a : affineSimplex k n) :
    singularAffinePushforward X k n x (Finsupp.single a 1) =
      Finsupp.single
        ((TopCat.toSSetObjEquiv X (.op ⦋k⦌)).symm
          ((TopCat.toSSetObjEquiv X (.op ⦋n⦌) x).comp
            (TopCat.toSSetObjEquiv (TopCat.of (StdSimplex ℝ (Fin (n+1)))) (.op ⦋k⦌) (affineAsSingular k n a)))) 1 := by
  simp [singularAffinePushforward, Finsupp.lmapDomain_apply]

theorem singularAffinePushforward_boundary (X : TopCat.{u}) (k n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌)
    (c : affineSimplex (k + 1) n →₀ ℤ) :
    singularBoundaryFinsupp X k
      (singularAffinePushforward X (k + 1) n x c) =
    singularAffinePushforward X k n x (affineBoundaryMap k n c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single a z =>
      have hs : Finsupp.single a z = z • Finsupp.single a 1 := by
        ext q
        by_cases hq : q = a <;> simp [hq]
      rw [hs]
      simp only [LinearMap.map_smul]
      rw [singularAffinePushforward_single, singularBoundaryFinsupp_single]
      simp only [affineBoundaryMap, Finsupp.linearCombination_single,
        affineBoundary, one_smul, map_sum, map_smul,
        singularAffinePushforward_single]
      congr 1

noncomputable def singularCarrierHomotopy (X : TopCat.{u}) (n : ℕ) :
    (((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ)) :=
  Finsupp.linearCombination ℤ (fun x =>
    singularAffinePushforward X (n + 1) n x
      (universalCarrierHomotopy n))

theorem singularCarrierHomotopy_zero (X : TopCat.{u})
    (c : (TopCat.toSSet.obj X) _⦋0⦌ →₀ ℤ) :
    singularCarrierHomotopy X 0 c = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single x a =>
      simp [singularCarrierHomotopy, universalCarrierHomotopy_zero]

private theorem singularAffinePushforward_face (X : TopCat.{u}) (n k : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌) (i : Fin (n + 2))
    (c : affineSimplex k n →₀ ℤ) :
    singularAffinePushforward X k n ((TopCat.toSSet.obj X).δ i x) c =
      singularAffinePushforward X k (n + 1) x
        (affinePostcompose k n (n + 1) (affineFaceInclusion n i) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single a z =>
      simp only [singularAffinePushforward, affinePostcompose,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      congr 1

private theorem singularAffinePushforward_identity (X : TopCat.{u}) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularAffinePushforward X n n x
      (Finsupp.single (standardAffineIdentity n) 1) = Finsupp.single x 1 := by
  rw [singularAffinePushforward_single]
  congr 1
  apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
  ext z
  change (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) (standardAffineIdentity n z) = _
  simp [standardAffineIdentity]

private theorem singularAffinePushforward_barycentric_identity (X : TopCat.{u}) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularAffinePushforward X n n x
      (affineBarycentricDegree n n
        (Finsupp.single (standardAffineIdentity n) 1)) =
      singularBarycentricFinsupp X n (Finsupp.single x 1) := by
  classical
  rw [affineBarycentricDegree, Finsupp.linearCombination_single]
  simp only [map_sum, map_smul, singularAffinePushforward_single, one_smul]
  rw [singularBarycentricFinsupp_single]
  congr 1
  funext σ
  congr 1
  congr 1
  apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
  ext z
  change (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x)
    ((standardAffineIdentity n).comp (barycentricFlagAffine n σ) z) =
    (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) (barycentricFlag n σ z)
  simp [standardAffineIdentity, barycentricFlag, barycentricFlagAffine]

private theorem singularCarrierHomotopy_single (X : TopCat.{u}) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularCarrierHomotopy X n (Finsupp.single x 1) =
      singularAffinePushforward X (n + 1) n x
        (universalCarrierHomotopy n) := by
  simp [singularCarrierHomotopy]

private theorem singularCarrierHomotopy_boundary_single (X : TopCat.{u}) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    singularCarrierHomotopy X n
        (singularBoundaryFinsupp X n (Finsupp.single x 1)) =
      singularAffinePushforward X (n + 1) (n + 1) x
        (affineUniversalHomotopy n (n + 1)
          (affineBoundaryMap n (n + 1)
            (Finsupp.single (standardAffineIdentity (n + 1)) 1))) := by
  classical
  rw [singularBoundaryFinsupp_single, affineBoundaryMap_single_identity]
  simp only [map_sum, map_smul, singularCarrierHomotopy_single,
    affineUniversalHomotopy_single]
  congr 1
  funext i
  exact congrArg ((-1 : ℤ) ^ i.val • ·)
    (singularAffinePushforward_face X n (n + 1) x i
      (universalCarrierHomotopy n))

/-- Barycentric subdivision is chain homotopic to the identity on singular
chains, with the homotopy induced by the universal affine carrier. -/
theorem singularCarrierHomotopy_boundary_succ (X : TopCat.{u}) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ) :
    singularBoundaryFinsupp X (n + 1)
        (singularCarrierHomotopy X (n + 1) c) +
      singularCarrierHomotopy X n (singularBoundaryFinsupp X n c) =
      singularBarycentricFinsupp X (n + 1) c - c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp only [map_add]
      calc
        _ = (singularBoundaryFinsupp X (n + 1) (singularCarrierHomotopy X (n + 1) c) +
              singularCarrierHomotopy X n (singularBoundaryFinsupp X n c)) +
            (singularBoundaryFinsupp X (n + 1) (singularCarrierHomotopy X (n + 1) d) +
              singularCarrierHomotopy X n (singularBoundaryFinsupp X n d)) := by abel
        _ = (singularBarycentricFinsupp X (n + 1) c - c) +
              (singularBarycentricFinsupp X (n + 1) d - d) := by rw [hc, hd]
        _ = _ := by abel
  | single x a =>
      have hs : Finsupp.single x a = a • Finsupp.single x 1 := by
        ext q
        by_cases hq : q = x <;> simp [hq]
      rw [hs]
      simp only [LinearMap.map_smul, ← smul_add, ← smul_sub]
      congr 1
      let e : affineSimplex (n + 1) (n + 1) →₀ ℤ :=
        Finsupp.single (standardAffineIdentity (n + 1)) 1
      have he : affineUniversalHomotopy (n + 1) (n + 1) e =
          universalCarrierHomotopy (n + 1) := by
        dsimp [e]
        rw [affineUniversalHomotopy_single, affinePostcompose_identity]
      calc
        _ = singularAffinePushforward X (n + 1) (n + 1) x
              (affineBoundaryMap (n + 1) (n + 1)
                (universalCarrierHomotopy (n + 1))) +
            singularAffinePushforward X (n + 1) (n + 1) x
              (affineUniversalHomotopy n (n + 1)
                (affineBoundaryMap n (n + 1) e)) := by
                rw [singularCarrierHomotopy_single,
                  singularAffinePushforward_boundary,
                  singularCarrierHomotopy_boundary_single]
        _ = singularAffinePushforward X (n + 1) (n + 1) x
              (affineBoundaryMap (n + 1) (n + 1)
                (universalCarrierHomotopy (n + 1)) +
               affineUniversalHomotopy n (n + 1)
                (affineBoundaryMap n (n + 1) e)) := by rw [map_add]
        _ = singularAffinePushforward X (n + 1) (n + 1) x
              (affineBarycentricDegree (n + 1) (n + 1) e - e) := by
                rw [← he, affineCarrierHomotopy_boundary_succ]
        _ = singularBarycentricFinsupp X (n + 1) (Finsupp.single x 1) -
              Finsupp.single x 1 := by
                rw [map_sub, singularAffinePushforward_barycentric_identity,
                  singularAffinePushforward_identity]


theorem toFinsupp_boundary (X : TopCat.{u}) (n : ℕ)
    (c : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n+1⦌)) :
    FreeAbelianGroup.toFinsupp (RawCone.boundary X n c) =
      singularBoundaryFinsupp X n (FreeAbelianGroup.toFinsupp c) := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | of x => simp only [RawCone.boundary_of, map_sum, map_zsmul,
      FreeAbelianGroup.toFinsupp_of, singularBoundaryFinsupp_single]
  | neg c hc => simp only [map_neg, hc]
  | add c d hc hd => simp only [map_add, hc, hd]

theorem singularBoundaryFinsupp_comp_zero (X : TopCat.{u}) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n+2⦌ →₀ ℤ) :
    singularBoundaryFinsupp X n (singularBoundaryFinsupp X (n+1) c) = 0 := by
  have he := congrArg (fun f => f.hom (Finsupp.toFreeAbelianGroup c))
    ((RawCone.chains X).d_comp_d (n+2) (n+1) n)
  change RawCone.boundary X n (RawCone.boundary X (n+1) (Finsupp.toFreeAbelianGroup c)) = 0 at he
  have hf := congrArg FreeAbelianGroup.toFinsupp he
  simpa only [toFinsupp_boundary, FreeAbelianGroup.toFinsupp_toFreeAbelianGroup, map_zero] using hf

theorem singularBarycentricFinsupp_zero (X : TopCat.{u})
    (c : (TopCat.toSSet.obj X) _⦋0⦌ →₀ ℤ) : singularBarycentricFinsupp X 0 c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single x a =>
    have hs : Finsupp.single x a = a • Finsupp.single x 1 := by simp
    rw [hs, map_smul, ← singularAffinePushforward_barycentric_identity,
      affineBarycentricDegree_zero, singularAffinePushforward_identity]

theorem singularBarycentric_boundary_compat (X : TopCat.{u}) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n+1⦌ →₀ ℤ) :
    singularBoundaryFinsupp X n (singularBarycentricFinsupp X (n+1) c) =
      singularBarycentricFinsupp X n (singularBoundaryFinsupp X n c) := by
  cases n with
  | zero =>
    have h := congrArg (singularBoundaryFinsupp X 0)
      (singularCarrierHomotopy_boundary_succ X 0 c)
    simp only [map_add, map_sub, singularBoundaryFinsupp_comp_zero,
      singularCarrierHomotopy_zero, map_zero, add_zero] at h
    rw [singularBarycentricFinsupp_zero]
    exact sub_eq_zero.mp h.symm
  | succ n =>
    have h := congrArg (singularBoundaryFinsupp X (n+1))
      (singularCarrierHomotopy_boundary_succ X (n+1) c)
    simp only [map_add, map_sub, singularBoundaryFinsupp_comp_zero, zero_add] at h
    have h' := singularCarrierHomotopy_boundary_succ X n (singularBoundaryFinsupp X (n+1) c)
    simp only [singularBoundaryFinsupp_comp_zero, map_zero, add_zero] at h'
    exact sub_left_inj.mp (h.symm.trans h')

#print axioms singularCarrierHomotopy_boundary_succ
#print axioms singularBarycentric_boundary_compat
end CurveGenusTwo.Filtration.UniverseSubdivision
