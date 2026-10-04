import CurveComplexGenusTwo.Filtration.CarrierFilling

set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

theorem carrierChainInclusion_injective (A B : FiniteComplex V)
    (h : A.simplices ⊆ B.simplices) (q : ℤ) :
    Function.Injective (chainInclusion A B h q) := by
  classical
  let r : chains B q →+ chains A q := FreeAbelianGroup.lift fun σ =>
    if hσ : σ.1 ∈ A then
      FreeAbelianGroup.of (⟨σ.1, hσ, σ.2.2⟩ : SimplexAt A q)
    else 0
  have hr : r.comp (chainInclusion A B h q) = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    simp only [AddMonoidHom.comp_apply, chainInclusion,
      FreeAbelianGroup.lift_apply_of, r, AddMonoidHom.id_apply]
    rw [dite_eq_left σ.2.1]
    rfl
  intro a b hab
  have := congrArg r hab
  simpa only [← AddMonoidHom.comp_apply, hr, AddMonoidHom.id_apply] using this

theorem exists_realizationCarrier_filling (K : FiniteComplex V)
    (S : Set (geometricRealization K)) (hS : S.Nonempty)
    (v : ActiveVertex K)
    (hstar : S ⊆ CurveComplex.openVertexStar (geometricComplex K) v)
    (q : ℤ) (hq : 0 ≤ q) (c : chains K (q - 1))
    (hc : boundary K (q - 1) c = 0)
    (hcarried : c ∈ (chainInclusion (realizationCarrier K S) K
      (realizationCarrier_subcomplex K S) (q - 1)).range) :
    ∃ d : chains (realizationCarrier K S) q,
      boundary K q (chainInclusion (realizationCarrier K S) K
        (realizationCarrier_subcomplex K S) q d) = c := by
  let L := realizationCarrier K S
  let hLK := realizationCarrier_subcomplex K S
  obtain ⟨a, ha⟩ := hcarried
  have haCycle : a ∈ cycles L (q - 1) := by
    change boundary L (q - 1) a = 0
    apply carrierChainInclusion_injective L K hLK (q - 1 - 1)
    have hcomm := DFunLike.congr_fun (chainInclusion_boundary L K hLK (q - 1)) a
    change boundary K (q - 1) (chainInclusion L K hLK (q - 1) a) =
      chainInclusion L K hLK (q - 1 - 1) (boundary L (q - 1) a) at hcomm
    rw [ha, hc] at hcomm
    simpa only [map_zero] using hcomm.symm
  have hb := realizationCarrier_cycle_bounds K S hS v hstar (q - 1)
    (by omega) ⟨a, haCycle⟩
  have hb' : a ∈ (boundary L q).range := by
    change a ∈ boundaries L (q - 1) at hb
    have aux (i j : ℤ) (e : i = j) :
        Eq.mp (congrArg (fun m => AddSubgroup (chains L (m - 1))) e)
          (boundary L i).range = (boundary L j).range := by
      cases e
      rfl
    have he : boundaries L (q - 1) = (boundary L q).range :=
      aux (q - 1 + 1) q (by omega)
    rw [he] at hb
    exact hb
  obtain ⟨d, hd⟩ := hb'
  refine ⟨d, ?_⟩
  have hcomm := DFunLike.congr_fun (chainInclusion_boundary L K hLK q) d
  change boundary K q (chainInclusion L K hLK q d) =
    chainInclusion L K hLK (q - 1) (boundary L q d) at hcomm
  rw [hd, ha] at hcomm
  exact hcomm
end CurveGenusTwo.Filtration
