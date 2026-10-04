import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.ActualRelativeFiniteCancellationComplete
import CurveComplexGenusTwo.Topology.ActualMain14FinitePreparation.Main14ActualOriginalDiskRelativeFinitePreparationNamedPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.ActualOriginalDisjointDiskArcsSupportedTerminalAlignment
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 3000000
theorem actual_two_mark_disk_arcs_supported_marked_isotopy
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hends : ({a.val.map 0,a.val.map 1} : Set S) = {b.val.map 0,b.val.map 1}) :
    ∃ H : AmbientIsotopy S,
      (∀ t x, x ∉ interior N.closedSet → H.map (t,x) = x) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      H.finalMap '' a.image = b.image := by
  classical
  let Q : Set S := (interior N.closedSet)ᶜ ∪ (M.cover.branch:Set S)
  let R : Set S → Set S → Prop := fun A B => ∃ H : AmbientIsotopy S,
    (∀ t x, x ∈ Q → H.map (t,x)=x) ∧ H.finalMap '' A=B
  have hEquiv : Equivalence R := by
      let zero : Interval := ⟨0, by norm_num⟩
      let one : Interval := ⟨1, by norm_num⟩
      let reverse : Interval → Interval := fun t =>
        ⟨1 - (t : ℝ), by
          rcases t.property with ⟨h0, h1⟩
          constructor <;> linarith⟩
      have reverse_cont : Continuous reverse :=
        (continuous_const.sub continuous_subtype_val).subtype_mk (fun t => (reverse t).property)
      let first : Interval → Interval := fun t =>
        ⟨min (2 * (t : ℝ)) 1, by
          rcases t.property with ⟨h0, h1⟩
          exact ⟨le_min (by linarith) (by norm_num), min_le_right _ _⟩⟩
      let second : Interval → Interval := fun t =>
        ⟨max (2 * (t : ℝ) - 1) 0, by
          rcases t.property with ⟨h0, h1⟩
          exact ⟨le_max_right _ _, max_le (by linarith) (by norm_num)⟩⟩
      have first_cont : Continuous first :=
        ((continuous_const.mul continuous_subtype_val).min continuous_const).subtype_mk
          (fun t => (first t).property)
      have second_cont : Continuous second :=
        (((continuous_const.mul continuous_subtype_val).sub continuous_const).max
          continuous_const).subtype_mk (fun t => (second t).property)
      have reverse_zero : reverse zero = one := Subtype.ext (by norm_num [reverse, zero, one])
      have reverse_one : reverse one = zero := Subtype.ext (by norm_num [reverse, zero, one])
      have first_zero : first zero = zero := Subtype.ext (by norm_num [first, zero])
      have first_one : first one = one := Subtype.ext (by norm_num [first, one])
      have second_zero : second zero = zero := Subtype.ext (by norm_num [second, zero])
      have second_one : second one = one := Subtype.ext (by norm_num [second, one])
      constructor
      · intro a
        refine ⟨{ map := ⟨fun p => p.2, continuous_snd⟩
                  homeomorphism_at := ?_
                  at_zero := by intro x; rfl }, ?_, ?_⟩
        · intro t
          exact ⟨Homeomorph.refl S, fun x => rfl⟩
        · intro t x hx; rfl
        · change (id : S → S) '' a = a
          exact Set.image_id a
      · intro a b hab
        obtain ⟨H, hfixH, hH⟩ := hab
        obtain ⟨h, hh⟩ := H.homeomorphism_at one
        have hfinal : ∀ x, h x = H.finalMap x := hh
        let K : AmbientIsotopy S := {
          map := ⟨fun p => H.map (reverse p.1, h.symm p.2), by
            exact H.map.continuous.comp
              ((reverse_cont.comp continuous_fst).prodMk
                (h.symm.continuous.comp continuous_snd))⟩
          homeomorphism_at := by
            intro t
            obtain ⟨g, hg⟩ := H.homeomorphism_at (reverse t)
            exact ⟨h.symm.trans g, fun x => by
              simpa [Homeomorph.trans_apply] using (hg (h.symm x))⟩
          at_zero := by
            intro x
            change H.map (reverse zero, h.symm x) = x
            rw [reverse_zero]
            rw [← hh]
            exact h.apply_symm_apply x }
        refine ⟨K, ?_, ?_⟩
        · intro t x hx
          have hf : h x = x := by rw [hh]; exact hfixH one x hx
          have hi : h.symm x = x := (congrArg h.symm hf.symm).trans (h.symm_apply_apply x)
          change H.map (reverse t, h.symm x)=x
          rw [hi]
          exact hfixH (reverse t) x hx
        · have hKfinal : ∀ x, K.finalMap x = h.symm x := by
            intro x
            change H.map (reverse one, h.symm x) = h.symm x
            rw [reverse_one]
            exact H.at_zero _
          simp_rw [hKfinal]
          have himage : h '' a = b := by
            simpa only [← hfinal] using hH
          rw [← himage]
          simp [Set.image_image]
      · intro a b c hab hbc
        obtain ⟨H, hfixH, hH⟩ := hab
        obtain ⟨K, hfixK, hK⟩ := hbc
        let L : AmbientIsotopy S := {
          map := ⟨fun p => K.map (second p.1, H.map (first p.1, p.2)), by
            exact K.map.continuous.comp
              ((second_cont.comp continuous_fst).prodMk
                (H.map.continuous.comp
                  ((first_cont.comp continuous_fst).prodMk continuous_snd)))⟩
          homeomorphism_at := by
            intro t
            obtain ⟨h, hh⟩ := H.homeomorphism_at (first t)
            obtain ⟨k, hk⟩ := K.homeomorphism_at (second t)
            exact ⟨h.trans k, fun x => by simp [Homeomorph.trans_apply, hh, hk]⟩
          at_zero := by
            intro x
            change K.map (second zero, H.map (first zero, x)) = x
            rw [first_zero, second_zero]
            rw [H.at_zero, K.at_zero] }
        refine ⟨L, ?_, ?_⟩
        · intro t x hx
          change K.map (second t, H.map (first t,x))=x
          rw [hfixH (first t) x hx,hfixK (second t) x hx]
        · have hLfinal : ∀ x, L.finalMap x = K.finalMap (H.finalMap x) := by
            intro x
            change K.map (second one, H.map (first one, x)) =
              K.map (one, H.map (one, x))
            rw [first_one, second_one]
          simp_rw [hLfinal]
          change (K.finalMap ∘ H.finalMap) '' a = c
          rw [Set.image_comp, hH, hK]
      
  have hEnds (u v : NonLoopArc M) (H : AmbientIsotopy S)
      (hfix : ∀ t x, x ∈ M.cover.branch → H.map (t,x)=x)
      (himage : H.finalMap '' u.image=v.image) :
      ({u.val.map 0,u.val.map 1}:Set S)={v.val.map 0,v.val.map 1} := by
    have hE : (markedArcEndset u.val:Set S)=(markedArcEndset v.val:Set S) := by
      rw [←markedArc_image_inter_branch,←markedArc_image_inter_branch]
      obtain ⟨f,hf⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
      have hi : Function.Injective H.finalMap := by
        intro x y h; exact f.injective (by simpa only [hf,AmbientIsotopy.finalMap] using h)
      ext x
      constructor
      · rintro ⟨hu,hx⟩
        refine ⟨?_,hx⟩
        change x ∈ v.image
        rw [←himage]
        exact ⟨x,hu,hfix _ x hx⟩
      · rintro ⟨hv,hx⟩
        change x ∈ v.image at hv
        rw [←himage] at hv
        obtain ⟨y,hy,he⟩ := hv
        have hyx : y=x := hi (he.trans (hfix _ x hx).symm)
        exact ⟨hyx ▸ hy,hx⟩
    simp only [markedArcEndset,Finset.coe_insert,Finset.coe_singleton] at hE
    convert hE using 1
  obtain ⟨a',b',H,K,hHo,hKo,hHm,hKm,hHi,hKi,ha',hb',hfinite,hcross⟩ :=
    M.actual_two_mark_disk_relative_finite_transverse_preparation a b N hb hends
  have hea := hEnds a a' H hHm hHi
  have heb := hEnds b b' K hKm hKi
  have heab : ({a'.val.map 0,a'.val.map 1}:Set S)={b'.val.map 0,b'.val.map 1} :=
    hea.symm.trans (hends.trans heb)
  let N' : ArcNeighborhood a' := {
    closedSet := N.closedSet
    disk := N.disk
    arc_inside := ha'
    marked_inside := N.marked_inside.trans hea
    boundary := N.boundary
    boundary_eq_frontier := N.boundary_eq_frontier }
  have hCancellation : ∃ b'' : NonLoopArc M, ∃ L : AmbientIsotopy S,
      (∀ t x, x ∉ interior N'.closedSet → L.map (t,x)=x) ∧
      (∀ t x, x ∈ M.cover.branch → L.map (t,x)=x) ∧
      L.finalMap '' b'.image=b''.image ∧ b''.image ⊆ interior N'.closedSet ∧
      Disjoint (a'.image \ (M.cover.branch:Set S))
        (b''.image \ (M.cover.branch:Set S)) := by
    exact M.actual_two_mark_disk_relative_finite_cancellation a' b' N' hb' heab hfinite hcross
  obtain ⟨b'',L,hLo,hLm,hLi,hb'',hd⟩ := hCancellation
  have heab'' := heab.trans (hEnds b' b'' L hLm hLi)
  have hmeet : a'.image ∩ b''.image={a'.val.map 0,a'.val.map 1} := by
    change a'.val.image ∩ b''.val.image=_
    change Disjoint (a'.val.image \ (M.cover.branch:Set S)) (b''.val.image \ (M.cover.branch:Set S)) at hd
    rw [markedArc_disjoint_interiors_inter_image a'.val b''.val hd]
    simp only [markedArcEndset,Finset.coe_insert,Finset.coe_singleton]
    have hh : (markedArcEndset a'.val:Set S)=(markedArcEndset b''.val:Set S) := by
      simp only [markedArcEndset,Finset.coe_insert,Finset.coe_singleton]
      convert heab'' using 1
    simp only [markedArcEndset,Finset.coe_insert,Finset.coe_singleton] at hh
    rw [←hh]
    convert Set.inter_self ({a'.val.map 0,a'.val.map 1}:Set S) using 1

  obtain ⟨T,hTo,hTm,hTi⟩ :=
    M.actual_original_disjoint_disk_arcs_supported_terminal_alignment a' b'' N' hb'' heab'' hmeet
  have fixed (F : AmbientIsotopy S)
      (ho : ∀ t x, x ∉ interior N.closedSet → F.map (t,x)=x)
      (hm : ∀ t x, x ∈ M.cover.branch → F.map (t,x)=x) :
      ∀ t x, x ∈ Q → F.map (t,x)=x := by
    intro t x hx
    rcases hx with hx | hx
    · exact ho t x hx
    · exact hm t x hx
  have hrH : R a.image a'.image := ⟨H,fixed H hHo hHm,hHi⟩
  have hrK : R b.image b'.image := ⟨K,fixed K hKo hKm,hKi⟩
  have hrL : R b'.image b''.image := ⟨L,fixed L hLo hLm,hLi⟩
  have hrT : R a'.image b''.image := ⟨T,fixed T hTo hTm,hTi⟩
  obtain ⟨F,hFfix,hFi⟩ := hEquiv.trans hrH
    (hEquiv.trans hrT (hEquiv.trans (hEquiv.symm hrL) (hEquiv.symm hrK)))
  exact ⟨F,(fun t x hx => hFfix t x (Or.inl hx)),
    (fun t x hx => hFfix t x (Or.inr hx)),hFi⟩
end CurveComplex.HyperellipticModel
