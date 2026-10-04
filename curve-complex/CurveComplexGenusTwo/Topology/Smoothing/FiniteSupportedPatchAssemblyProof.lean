import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
open Set CurveComplex
theorem finite_supported_patch_assembly {S J : Type} [TopologicalSpace S] [Fintype J]
    (K : J → Set S) (hdis : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (moves : J → AmbientIsotopy S)
    (hfix : ∀ j t x, x ∉ K j → (moves j).map (t,x) = x) :
    ∃ H : AmbientIsotopy S,
      (∀ t x, x ∉ ⋃ j, K j → H.map (t,x) = x) ∧
      (∀ j t x, x ∈ K j → H.map (t,x) = (moves j).map (t,x)) := by
  classical
  have hpres (j : J) (t : Interval) (x : S) (hx : x ∈ K j) : (moves j).map (t,x) ∈ K j := by
    obtain ⟨g,hg⟩ := (moves j).homeomorphism_at t
    by_contra hy
    have he : g ((moves j).map (t,x)) = g x := by
      rw [hg,hfix j t _ hy,hg]
    exact hy ((g.injective he).symm ▸ hx)
  have listFix (l : List J) (j : J) (hj : j ∉ l) :
      ∀ t x, x ∈ K j → (AmbientIsotopy.finiteCompose (l.map moves)).map (t,x) = x := by
    apply AmbientIsotopy.finiteCompose_fixes _ (K j)
    intro H hH t x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    have hij : i ≠ j := by intro he; exact hj (he ▸ hi)
    exact hfix i t x (fun hxi => Set.disjoint_left.mp (hdis i j hij) hxi hx)
  have listAt (l : List J) (hnd : l.Nodup) (j : J) (hj : j ∈ l) :
      ∀ t x, x ∈ K j → (AmbientIsotopy.finiteCompose (l.map moves)).map (t,x) = (moves j).map (t,x) := by
    induction l with
    | nil => simp at hj
    | cons i l ih =>
      have hndi := List.nodup_cons.mp hnd
      intro t x hx
      change (AmbientIsotopy.finiteCompose (l.map moves)).map (t,(moves i).map (t,x)) = _
      by_cases hij : i=j
      · subst i
        exact listFix l j hndi.1 t _ (hpres j t x hx)
      · have hxnot : x ∉ K i := fun hxi => Set.disjoint_left.mp (hdis i j hij) hxi hx
        rw [hfix i t x hxnot]
        exact ih hndi.2 (List.mem_of_ne_of_mem (Ne.symm hij) hj) t x hx
  let l : List J := Finset.univ.toList
  let H := AmbientIsotopy.finiteCompose (l.map moves)
  refine ⟨H,?_,?_⟩
  · apply AmbientIsotopy.finiteCompose_fixes _ (⋃ j, K j)ᶜ
    intro G hG t x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hG
    exact hfix j t x (fun hxj => hx (mem_iUnion.mpr ⟨j,hxj⟩))
  · intro j
    exact listAt l (Finset.nodup_toList Finset.univ) j (by simp [l])

#print axioms finite_supported_patch_assembly
