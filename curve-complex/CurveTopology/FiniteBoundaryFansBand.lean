import FiniteBoundaryBandCore
import ClassificationOfSurfaces.StrongVertexStar
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Paths
import ClassificationOfSurfaces.Moise.GeometricTriangulation
import ClassificationOfSurfaces.Topology.InvarianceOfDomain
import Mathlib.Analysis.Complex.Circle
import CurveComplexGenusTwo.Foundations.Definitions
import WholeBoundaryFanSector
import BoundaryEdgeTriangleTrapezoid

open Set Topology CurveComplex SimpleGraph
open scoped Manifold ContDiff
open LeanEval.Topology.ClassificationOfSurfaces

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry

/-- Intrinsic boundary recognition and all ordered fans of the actual faithful
triangulation. Connectedness is confined to this component-level helper. -/
theorem geometric_surface_triangulation_boundary_fans
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (𝓡∂ 2) 0 M] (T : GeometricTriangulation M) :
    (∀ q : T.realization,
      T.homeo q ∈ (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ ↔
        q ∈ boundaryLocus T.faces) ∧
    HasOrderedBoundaryFans T.faces := by
  have hfans : HasOrderedBoundaryFans T.faces := by
    classical
    have hlinear : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (a : V)
        (hdegree : ∀ x y z w, G.Adj x y → G.Adj x z → G.Adj x w →
          y = z ∨ y = w ∨ z = w)
        (hleaf : ∃ b, G.Adj a b ∧ ∀ z, G.Adj a z → z = b),
        ∃ (b : V) (p : G.Walk a b), p.IsPath ∧ 1 ≤ p.length ∧
          (∀ x y, G.Reachable a x → (G.Adj x y ↔ p.toSubgraph.Adj x y)) := by
      intro V _ G a hdegree hleaf
      classical
      let lengths : Set ℕ := {n | ∃ (b : V) (p : G.Walk a b), p.IsPath ∧ p.length = n}
      have hfinite : lengths.Finite := (Set.finite_lt_nat (Fintype.card V)).subset
        (by rintro n ⟨b,p,hp,rfl⟩; exact hp.length_lt)
      obtain ⟨n, ⟨⟨b,p,hp,rfl⟩,hmax⟩⟩ := hfinite.exists_maximal
        (show lengths.Nonempty from ⟨0,a,.nil,by simp⟩)
      have hmax' : ∀ (c : V) (q : G.Walk a c), q.IsPath → q.length ≤ p.length := by
        intro c q hq
        by_cases h : p.length ≤ q.length
        · exact hmax ⟨c,q,hq,rfl⟩ h
        · omega
      obtain ⟨a₁,haa₁,hleaf⟩ := hleaf
      have hpos : 1 ≤ p.length := by
        have h := hmax' a₁ haa₁.toWalk (Walk.IsPath.of_adj haa₁)
        simpa using h
      have hnotnil : ¬p.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
      have hstart : ∀ y, G.Adj a y → p.toSubgraph.Adj a y := by
        intro y hay
        have hsnd := p.adj_snd hnotnil
        rw [hleaf y hay, ← hleaf p.snd hsnd]
        exact p.toSubgraph_adj_snd hnotnil
      have hinternal : ∀ i, i ≠ 0 → i < p.length → ∀ y,
          G.Adj (p.getVert i) y → p.toSubgraph.Adj (p.getVert i) y := by
        intro i hi0 hi y hay
        have hprev : G.Adj (p.getVert i) (p.getVert (i-1)) := by
          have h := (p.adj_getVert_succ (by omega : i-1 < p.length)).symm
          simpa [show i-1+1=i by omega] using h
        have hnext := p.adj_getVert_succ hi
        have hne : p.getVert (i-1) ≠ p.getVert (i+1) := by
          intro heq
          have := hp.getVert_injOn (by simp; omega) (by simp; omega) heq
          omega
        rcases hdegree (p.getVert i) (p.getVert (i-1)) (p.getVert (i+1)) y
            hprev hnext hay with heq | heq | heq
        · exact (hne heq).elim
        · rw [← heq]
          have h := (p.toSubgraph_adj_getVert (by omega : i-1 < p.length)).symm
          simpa [show i-1+1=i by omega] using h
        · rw [← heq]
          exact p.toSubgraph_adj_getVert hi
      have hend : ∀ y, G.Adj b y → p.toSubgraph.Adj b y := by
        intro y hby
        have hy : y ∈ p.support := by
          by_contra hy
          have h := hmax' y (p.concat hby) (hp.concat hy hby)
          simp only [Walk.length_concat] at h
          omega
        obtain ⟨i,heq,hi⟩ := Walk.mem_support_iff_exists_getVert.mp hy
        rw [← heq]
        by_cases hi0 : i = 0
        · subst i
          simpa using (hstart b (by simpa [← heq] using hby.symm)).symm
        by_cases hilast : i = p.length
        · subst i
          simp only [Walk.getVert_length] at heq
          exact (hby.ne heq).elim
        · exact (hinternal i hi0 (by omega) b (by simpa [heq] using hby.symm)).symm
      have hclosed : ∀ x ∈ p.support, ∀ y, G.Adj x y → p.toSubgraph.Adj x y := by
        intro x hx y hxy
        obtain ⟨i,rfl,hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
        by_cases hi0 : i=0
        · subst i
          simpa using hstart y (by simpa using hxy)
        by_cases hilast : i=p.length
        · subst i
          simpa using hend y (by simpa using hxy)
        exact hinternal i hi0 (by omega) y hxy
      refine ⟨b,p,hp,hpos,?_⟩
      intro x y hax
      have hx : x ∈ p.toSubgraph.verts := hax.mem_subgraphVerts
        (by intro u hu w huw; exact hclosed u (p.mem_verts_toSubgraph.mp hu) w huw)
        p.start_mem_verts_toSubgraph
      exact ⟨hclosed x (p.mem_verts_toSubgraph.mp hx) y, fun h => h.adj_sub⟩
    have hval := T.surfaceIncidence.edge_valence_le_two
    have hstar := T.faces_isStrongVertexStarConnected
    have htriple : ∀ (t : Finset T.Vertex) (a b : T.Vertex),
        t ∈ T.faces → a ∈ t → b ∈ t → a ≠ b →
        ∃ c, c ≠ a ∧ c ≠ b ∧ t = {a,b,c} := by
      intro t a b ht ha hb hab
      obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := Finset.card_eq_three.mp (T.faces_card t ht)
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      all_goals try exact (hab rfl).elim
      · exact ⟨z,hxz.symm,hyz.symm,rfl⟩
      · exact ⟨y,hxy.symm,hyz,by ext; simp [or_left_comm,or_comm]⟩
      · exact ⟨z,hyz.symm,hxz.symm,by ext; simp [or_left_comm,or_comm]⟩
      · exact ⟨x,hxy,hxz,by ext; simp [or_left_comm,or_comm]⟩
      · exact ⟨y,hyz,hxy.symm,by ext; simp [or_left_comm,or_comm]⟩
      · exact ⟨x,hxz,hxy,by ext; simp [or_left_comm,or_comm]⟩
    intro v hv
    obtain ⟨e,he,hve⟩ := Finset.mem_biUnion.mp hv
    dsimp only [id] at hve
    have hecard : e.card = 2 := T.card_of_mem_edges (Finset.mem_filter.mp he).1
    obtain ⟨a,hav,hea⟩ : ∃ a, a ≠ v ∧ e = {v,a} := by
      obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hecard
      simp only [Finset.mem_insert, Finset.mem_singleton] at hve
      rcases hve with rfl | rfl
      · exact ⟨y,hxy.symm,rfl⟩
      · exact ⟨x,hxy,by ext; simp [or_comm]⟩
    subst e
    have hcard1 := (Finset.mem_filter.mp he).2
    obtain ⟨t,ht⟩ := Finset.card_eq_one.mp hcard1
    have htm : t ∈ T.faces ∧ {v,a} ⊆ t := by
      have : t ∈ T.faces.filter (fun t => {v,a} ⊆ t) := by rw [ht]; simp
      exact Finset.mem_filter.mp this
    obtain ⟨b,hbv,hba,htb⟩ := htriple t v a htm.1 (htm.2 (by simp))
      (htm.2 (by simp)) hav.symm
    let G : SimpleGraph T.Vertex := {
      Adj := fun x y => x ≠ v ∧ y ≠ v ∧ x ≠ y ∧ {v,x,y} ∈ T.faces
      symm := ⟨by
        intro x y h
        exact ⟨h.2.1,h.1,h.2.2.1.symm,by convert h.2.2.2 using 1 <;> ext <;> simp [or_left_comm,or_comm]⟩⟩
      loopless := ⟨by intro x h; exact h.2.2.1 rfl⟩ }
    have gadj (x y : T.Vertex) : G.Adj x y ↔
        x ≠ v ∧ y ≠ v ∧ x ≠ y ∧ {v,x,y} ∈ T.faces := Iff.rfl
    have hadj_unique (x y z : T.Vertex) (hxy : G.Adj x y) (hxz : G.Adj x z)
        (h : ({v,x,y} : Finset T.Vertex) = {v,x,z}) : y = z := by
      have hm : y ∈ ({v,x,z} : Finset T.Vertex) := h ▸ (by simp)
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      exact hm.resolve_left hxy.2.1 |>.resolve_left hxy.2.2.1.symm
    have hdegree : ∀ x y z w, G.Adj x y → G.Adj x z → G.Adj x w →
        y = z ∨ y = w ∨ z = w := by
      intro x y z w hxy hxz hxw
      by_contra h
      push Not at h
      have hyz : ({v,x,y} : Finset T.Vertex) ≠ {v,x,z} := fun heq => h.1 (hadj_unique x y z hxy hxz heq)
      have hyw : ({v,x,y} : Finset T.Vertex) ≠ {v,x,w} := fun heq => h.2.1 (hadj_unique x y w hxy hxw heq)
      have hzw : ({v,x,z} : Finset T.Vertex) ≠ {v,x,w} := fun heq => h.2.2 (hadj_unique x z w hxz hxw heq)
      have hsub : ({ {v,x,y}, {v,x,z}, {v,x,w} } : Finset (Finset T.Vertex)) ⊆
          T.faces.filter (fun t => {v,x} ⊆ t) := by
        intro s hs
        simp only [Finset.mem_insert,Finset.mem_singleton] at hs
        rcases hs with rfl | rfl | rfl <;>
          apply Finset.mem_filter.mpr
        · exact ⟨hxy.2.2.2,by simp⟩
        · exact ⟨hxz.2.2.2,by simp⟩
        · exact ⟨hxw.2.2.2,by simp⟩
      have hbound := hval {v,x} (T.mem_edges_of_subset_face hxy.2.2.2 (by simp)
        (by simp [hxy.1.symm]))
      have hc := Finset.card_le_card hsub
      have h3 : ({ {v,x,y}, {v,x,z}, {v,x,w} } : Finset (Finset T.Vertex)).card = 3 := by
        simp [hyz,hyw,hzw]
      omega
    have hab : G.Adj a b := ⟨hav,hbv,hba.symm,htb ▸ htm.1⟩
    have hleaf : ∀ z, G.Adj a z → z = b := by
      intro z haz
      have hz : {v,a,z} ∈ T.faces.filter (fun t => {v,a} ⊆ t) :=
        Finset.mem_filter.mpr ⟨haz.2.2.2,by simp⟩
      rw [ht,Finset.mem_singleton] at hz
      exact hadj_unique a z b haz hab (hz.trans htb)
    obtain ⟨last,p,hp,hpos,hfull⟩ := hlinear G a hdegree ⟨b,hab,hleaf⟩
    have hreach : ∀ (s : T.Triangle), v ∈ s.val → ∀ x ∈ s.val,
        x ≠ v → G.Reachable a x := by
      intro s hvs
      have hchain := hstar v (⟨t,htm.1⟩ : T.Triangle) s
        (htm.2 (by simp)) hvs
      induction hchain with
      | refl =>
          intro x hx hxv
          by_cases hxa : x = a
          · subst x; exact SimpleGraph.Reachable.refl a
          · have hs : t = {v,a,x} := by
              have hsubset : ({v,a,x} : Finset T.Vertex) ⊆ t := by
                simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
                exact (show v ∈ t ∧ a ∈ t ∧ x ∈ t from
                  ⟨htm.2 (by simp),htm.2 (by simp),hx⟩)
              exact (Finset.eq_of_subset_of_card_le hsubset (by
                rw [T.faces_card t htm.1]; simp [hav.symm,hxv.symm,(Ne.symm hxa)])).symm
            exact (show G.Adj a x from ⟨hav,hxv,(Ne.symm hxa),hs ▸ htm.1⟩).reachable
      | @tail s'' s' hchain hstep ih =>
          intro x hx hxv
          obtain ⟨edge,hcard,hvedge,hleft,hright⟩ := hstep
          obtain ⟨w,hwv,hwe⟩ : ∃ w, w ≠ v ∧ w ∈ edge := by
            obtain ⟨u,w,huw,heq⟩ := Finset.card_eq_two.mp hcard
            rw [heq] at hvedge
            simp only [Finset.mem_insert,Finset.mem_singleton] at hvedge
            rcases hvedge with rfl | rfl
            · exact ⟨w,huw.symm,by simp [heq]⟩
            · exact ⟨u,huw,by simp [heq]⟩
          have hwreach := ih (hleft hvedge) w (hleft hwe) hwv
          by_cases hxw : x = w
          · simpa [hxw] using hwreach
          · have hsubset : ({v,w,x} : Finset T.Vertex) ⊆ s'.val := by
              simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
              exact (show v ∈ s'.val ∧ w ∈ s'.val ∧ x ∈ s'.val from
                ⟨hright hvedge,hright hwe,hx⟩)
            have hs : s'.val = {v,w,x} :=
              (Finset.eq_of_subset_of_card_le hsubset (by
                rw [T.faces_card s'.val s'.property]; simp [hwv.symm,hxv.symm,(Ne.symm hxw)])).symm
            exact hwreach.trans (show G.Adj w x from
              ⟨hwv,hxv,(Ne.symm hxw),hs ▸ s'.property⟩).reachable
    have hpv : ∀ i : Fin (p.length+1), p.getVert i.val ≠ v := by
      intro i
      by_cases hi : i.val < p.length
      · exact (p.adj_getVert_succ hi).1
      · have hi' : i.val = p.length := by omega
        have h := p.adj_getVert_succ (by omega : p.length-1 < p.length)
        simpa [hi',show p.length-1+1=p.length by omega] using h.2.1
    have htriangles : ∀ s : Finset T.Vertex, s ∈ T.faces ∧ v ∈ s ↔
        ∃ i : Fin p.length, s = {v,p.getVert i.val,p.getVert (i.val+1)} := by
      intro s
      constructor
      · rintro ⟨hs,hvs⟩
        obtain ⟨x,hx,hxv⟩ : ∃ x ∈ s, x ≠ v := by
          by_contra h
          push Not at h
          have hsub : s ⊆ {v} := by intro x hx; simp [h x hx]
          have hh := Finset.card_le_card hsub
          simp [T.faces_card s hs] at hh
        obtain ⟨y,hyv,hyx,hsy⟩ := htriple s v x hs hvs hx hxv.symm
        have hxy : G.Adj x y := ⟨hxv,hyv,hyx.symm,hsy ▸ hs⟩
        have hpathadj := (hfull x y (hreach ⟨s,hs⟩ hvs x hx hxv)).mp hxy
        obtain ⟨i,heq,hi⟩ := p.toSubgraph_adj_iff.mp hpathadj
        refine ⟨⟨i,hi⟩,?_⟩
        simp only [Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk] at heq
        rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hsy
        · rw [hsy,Finset.pair_comm (p.getVert (i+1)) (p.getVert i)]
      · rintro ⟨i,rfl⟩
        exact ⟨(p.adj_getVert_succ i.isLt).2.2.2,by simp⟩
    have hedgeUnique (x : T.Vertex) (hxv : x ≠ v) :
        {v,x} ∈ boundaryEdges T.faces ↔ ∃! y, G.Adj x y := by
      constructor
      · intro hedge
        obtain ⟨s,hs⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hedge).2
        have hsm : s ∈ T.faces ∧ {v,x} ⊆ s := by
          apply Finset.mem_filter.mp
          rw [hs]; simp
        obtain ⟨y,hyv,hyx,hsy⟩ := htriple s v x hsm.1
          (hsm.2 (by simp)) (hsm.2 (by simp)) hxv.symm
        have hxy : G.Adj x y := ⟨hxv,hyv,hyx.symm,hsy ▸ hsm.1⟩
        refine ⟨y,hxy,?_⟩
        intro z hxz
        have hz : {v,x,z} ∈ T.faces.filter (fun s => {v,x} ⊆ s) :=
          Finset.mem_filter.mpr ⟨hxz.2.2.2,by simp⟩
        rw [hs,Finset.mem_singleton] at hz
        exact hadj_unique x z y hxz hxy (hz.trans hsy)
      · rintro ⟨y,hxy,hunique⟩
        apply Finset.mem_filter.mpr
        refine ⟨T.mem_edges_of_subset_face hxy.2.2.2 (by simp) (by simp [hxv.symm]),?_⟩
        apply Finset.card_eq_one.mpr
        refine ⟨{v,x,y},?_⟩
        ext s
        simp only [Finset.mem_filter,Finset.mem_singleton]
        constructor
        · rintro ⟨hs,hsub⟩
          obtain ⟨z,hzv,hzx,hsz⟩ := htriple s v x hs
            (hsub (by simp)) (hsub (by simp)) hxv.symm
          have hz : G.Adj x z := ⟨hxv,hzv,hzx.symm,hsz ▸ hs⟩
          rw [hsz,hunique z hz]
        · rintro rfl
          exact ⟨hxy.2.2.2,by simp⟩
    have hnotnil : ¬p.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
    have hlastreach : G.Reachable a last := ⟨p⟩
    have hlastleaf : ∃! y, G.Adj last y := by
      refine ⟨p.penultimate,(p.toSubgraph_adj_penultimate hnotnil).symm.adj_sub,?_⟩
      intro y hy
      have hmem : y ∈ p.toSubgraph.neighborSet last := (hfull last y hlastreach).mp hy
      rwa [hp.neighborSet_toSubgraph_endpoint hnotnil,Set.mem_singleton_iff] at hmem
    refine ⟨{ length := p.length
              positive := hpos
              vertex := fun i => p.getVert i.val
              injective := ?_
              off_center := hpv
              triangles_exact := htriangles
              boundary_edges_exact := ?_ }⟩
    · intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn (by simp; omega) (by simp; omega) hij
    · intro e
      simp only [Fin.val_zero,Walk.getVert_zero,Fin.val_last,Walk.getVert_length]
      constructor
      · rintro ⟨hedge,hve⟩
        have hecard : e.card = 2 := T.card_of_mem_edges (Finset.mem_filter.mp hedge).1
        obtain ⟨x,hxv,hex⟩ : ∃ x, x ≠ v ∧ e = {v,x} := by
          obtain ⟨u,w,huw,rfl⟩ := Finset.card_eq_two.mp hecard
          simp only [Finset.mem_insert,Finset.mem_singleton] at hve
          rcases hve with rfl | rfl
          · exact ⟨w,huw.symm,rfl⟩
          · exact ⟨u,huw,Finset.pair_comm _ _⟩
        subst e
        obtain ⟨y,hxy,hunique⟩ := (hedgeUnique x hxv).mp hedge
        have hxreach := hreach ⟨{v,x,y},hxy.2.2.2⟩ (by simp) x (by simp) hxv
        have hpathadj := (hfull x y hxreach).mp hxy
        have hxm := p.mem_support_of_adj_toSubgraph hpathadj
        obtain ⟨i,heq,hi⟩ := Walk.mem_support_iff_exists_getVert.mp hxm
        by_cases hi0 : i=0
        · left; simpa [hi0] using congrArg (fun z : T.Vertex => ({v,z} : Finset T.Vertex)) heq.symm
        by_cases hilast : i=p.length
        · right; simpa [hilast] using congrArg (fun z : T.Vertex => ({v,z} : Finset T.Vertex)) heq.symm
        have hiprev : G.Adj x (p.getVert (i-1)) := by
          have h := (p.adj_getVert_succ (by omega : i-1 < p.length)).symm
          simpa [show i-1+1=i by omega,heq] using h
        have hinext : G.Adj x (p.getVert (i+1)) := by
          simpa [heq] using p.adj_getVert_succ (by omega : i < p.length)
        have hiEq := (hunique _ hiprev).trans (hunique _ hinext).symm
        have := hp.getVert_injOn (by simp; omega) (by simp; omega) hiEq
        omega
      · rintro (rfl | rfl)
        · exact ⟨(hedgeUnique a hav).mpr ⟨b,hab,hleaf⟩,by simp⟩
        · have hlastv : last ≠ v := by simpa using hpv (Fin.last p.length)
          exact ⟨(hedgeUnique last hlastv).mpr hlastleaf,by simp⟩
  have hInteriorOpen : IsOpen (ModelWithCorners.interior (I := 𝓡∂ 2) M) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    let e := chartAt (EuclideanHalfSpace 2) x
    let P : Set (EuclideanHalfSpace 2) := {y | 0 < y.val 0}
    have hPopen : IsOpen P := isOpen_lt continuous_const (by fun_prop)
    have hNopen : IsOpen (e.source ∩ e ⁻¹' P) :=
      e.continuousOn.isOpen_inter_preimage e.open_source hPopen
    have hxP : e x ∈ P := by
      have h := (InvarianceOfDomain.isInteriorPoint_iff_any_chart
        (𝓡∂ 2) (mem_chart_source (EuclideanHalfSpace 2) x)).mp hx
      rw [interior_range_modelWithCornersEuclideanHalfSpace] at h
      exact h
    apply Filter.mem_of_superset (hNopen.mem_nhds ⟨mem_chart_source _ _,hxP⟩)
    intro y hy
    apply (InvarianceOfDomain.isInteriorPoint_iff_any_chart (𝓡∂ 2) hy.1).mpr
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    exact hy.2
  have hBoundaryInChart (e : OpenPartialHomeomorph M (EuclideanHalfSpace 2))
      (y : M) (hy : y ∈ e.source) :
      y ∈ (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ ↔ (e y).val 0 = 0 := by
    change ¬ (𝓡∂ 2).IsInteriorPoint y ↔ _
    rw [InvarianceOfDomain.isInteriorPoint_iff_any_chart (𝓡∂ 2) hy,
      interior_range_modelWithCornersEuclideanHalfSpace]
    change ¬ 0 < (e y).val 0 ↔ (e y).val 0 = 0
    constructor
    · intro h
      exact le_antisymm (le_of_not_gt h) (e y).property
    · intro h
      rw [h]
      exact lt_irrefl 0
  have hBoundaryClosed : IsClosed
      (T.homeo ⁻¹' (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ) :=
    hInteriorOpen.isClosed_compl.preimage T.homeo.continuous
  have hLocusClosed : IsClosed (boundaryLocus T.faces) := by
    have heq : boundaryLocus T.faces =
        ⋃ e ∈ boundaryEdges T.faces,
          (Subtype.val : T.realization → T.Vertex → ℝ) ⁻¹' GeometricFace T.Vertex e := by
      ext q
      simp [boundaryLocus]
    rw [heq]
    exact (boundaryEdges T.faces).finite_toSet.isClosed_biUnion
      (fun e _ => (GeometricFace.isClosed e).preimage continuous_subtype_val)
  classical
  have hOnePage (a b : T.Vertex) (hab : a ≠ b)
      (hcard : (T.faces.filter (fun t => {a,b} ⊆ t)).card = 1)
      (q : T.realization) (hqa : 0 < q.val a) (hqb : 0 < q.val b)
      (hqsupp : q.val ∈ GeometricFace T.Vertex {a,b}) :
      T.homeo q ∉ ModelWithCorners.interior (I := 𝓡∂ 2) M := by
    have hPlanarInterior : ∀ (U : Set M), IsOpen U →
        ∀ (f : U → EuclideanSpace ℝ (Fin 2)), Continuous f → Function.Injective f →
          ∀ (x : U), (𝓡∂ 2).IsInteriorPoint x.val → f x ∈ interior (range f) := by
      intro U hU f hf hinj x hx
      let c := extChartAt (𝓡∂ 2) x.val
      let W : Set (EuclideanSpace ℝ (Fin 2)) := interior c.target ∩ c.symm ⁻¹' U
      have hWopen : IsOpen W := by
        exact ((continuousOn_extChartAt_symm (I := 𝓡∂ 2) x.val).mono interior_subset
          ).isOpen_inter_preimage isOpen_interior hU
      have hcx : c.symm (c x.val) = x.val := c.left_inv (mem_extChartAt_source x.val)
      have hcxW : c x.val ∈ W := ⟨(ModelWithCorners.isInteriorPoint_iff.mp hx),by simpa [hcx] using x.property⟩
      let g : W → U := fun y => ⟨c.symm y.val,y.property.2⟩
      have hg : Continuous g := by
        apply Continuous.subtype_mk
        exact ContinuousOn.restrict ((continuousOn_extChartAt_symm (I := 𝓡∂ 2) x.val
          ).mono (fun y hy => interior_subset hy.1))
      have hginj : Function.Injective g := by
        intro y z heq
        apply Subtype.ext
        exact c.symm.injOn (interior_subset y.property.1) (interior_subset z.property.1)
          (congrArg Subtype.val heq)
      have hfg : IsOpen (range (f ∘ g)) :=
        InvarianceOfDomain.isOpen_range_of_isOpen_of_continuous_injective
          (𝓘(ℝ,EuclideanSpace ℝ (Fin 2))) hWopen (f ∘ g) (hf.comp hg) (hinj.comp hginj)
      have hgx : g ⟨c x.val,hcxW⟩ = x := Subtype.ext hcx
      apply mem_interior_iff_mem_nhds.mpr
      apply Filter.mem_of_superset (hfg.mem_nhds ⟨⟨c x.val,hcxW⟩,by simp [hgx]⟩)
      rintro y ⟨z,rfl⟩
      exact mem_range_self (g z)
    obtain ⟨t,ht⟩ := Finset.card_eq_one.mp hcard
    have htm : t ∈ T.faces ∧ {a,b} ⊆ t := by
      apply Finset.mem_filter.mp
      rw [ht]; simp
    have hdiff : (t \ {a,b}).card = 1 := by
      rw [Finset.card_sdiff_of_subset htm.2,T.faces_card t htm.1]
      simp [hab]
    obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hdiff
    have hcnot : c ∉ ({a,b} : Finset T.Vertex) := by
      apply (Finset.mem_sdiff.mp (show c ∈ t \ {a,b} by rw [hc]; simp)).2
    have hca : c ≠ a := fun h => hcnot (by simp [h])
    have hcb : c ≠ b := fun h => hcnot (by simp [h])
    have htc : t = {a,b,c} := by
      rw [← Finset.sdiff_union_of_subset htm.2,hc]
      ext x; simp [or_comm,or_left_comm]
    let U : Set M := {y | 0 < (T.homeo.symm y).val a ∧ 0 < (T.homeo.symm y).val b}
    have hU : IsOpen U := by
      exact (isOpen_lt continuous_const ((continuous_apply a).comp
        (continuous_subtype_val.comp T.homeo.symm.continuous))).inter
        (isOpen_lt continuous_const ((continuous_apply b).comp
          (continuous_subtype_val.comp T.homeo.symm.continuous)))
    have hsupp (y : U) : ∀ k ∉ t, (T.homeo.symm y.val).val k = 0 := by
      obtain ⟨s,hs,hys⟩ := (T.homeo.symm y.val).property.2
      have has : a ∈ s := by
        by_contra h
        have := hys a h
        have := y.property.1
        change 0 < (T.homeo.symm y.val).val a at this
        linarith
      have hbs : b ∈ s := by
        by_contra h
        have := hys b h
        have := y.property.2
        change 0 < (T.homeo.symm y.val).val b at this
        linarith
      have hsfilter : s ∈ T.faces.filter (fun t => {a,b} ⊆ t) :=
        Finset.mem_filter.mpr ⟨hs,by
          intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · exact has
          · simpa only [Finset.mem_singleton.mp hk] using hbs⟩
      rw [ht,Finset.mem_singleton] at hsfilter
      simpa [hsfilter] using hys
    have hsum (y : U) : (T.homeo.symm y.val).val a +
        (T.homeo.symm y.val).val b + (T.homeo.symm y.val).val c = 1 := by
      have hh := Finset.sum_subset (Finset.subset_univ t)
        (fun k _ hkt => hsupp y k hkt)
      have hy := (T.homeo.symm y.val).property.1.2
      rw [← hh,htc] at hy
      simpa [hab,hca.symm,hcb.symm,add_assoc] using hy
    let f : U → EuclideanSpace ℝ (Fin 2) := fun y =>
      WithLp.toLp 2 ![(T.homeo.symm y.val).val c,(T.homeo.symm y.val).val a]
    have hf : Continuous f := by
      change Continuous (fun y : U => WithLp.toLp 2 ![(T.homeo.symm y.val).val c,(T.homeo.symm y.val).val a])
      have hbase : Continuous (fun y : U => (T.homeo.symm y.val).val) :=
        continuous_subtype_val.comp (T.homeo.symm.continuous.comp continuous_subtype_val)
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i
      · exact (continuous_apply c).comp hbase
      · exact (continuous_apply a).comp hbase
    have hinj : Function.Injective f := by
      intro y z heq
      have hec : (T.homeo.symm y.val).val c = (T.homeo.symm z.val).val c :=
        congrArg (fun r : EuclideanSpace ℝ (Fin 2) => r 0) heq
      have hea : (T.homeo.symm y.val).val a = (T.homeo.symm z.val).val a :=
        congrArg (fun r : EuclideanSpace ℝ (Fin 2) => r 1) heq
      have heb : (T.homeo.symm y.val).val b = (T.homeo.symm z.val).val b := by
        linarith [hsum y,hsum z]
      apply Subtype.ext
      apply T.homeo.symm.injective
      apply Subtype.ext
      funext k
      by_cases hka : k = a
      · simpa [hka] using hea
      by_cases hkb : k = b
      · simpa [hkb] using heb
      by_cases hkc : k = c
      · simpa [hkc] using hec
      have hkt : k ∉ t := by simp [htc,hka,hkb,hkc]
      rw [hsupp y k hkt,hsupp z k hkt]
    let x : U := ⟨T.homeo q,by simpa [U] using And.intro hqa hqb⟩
    intro hq
    have hfx := hPlanarInterior U hU f hf hinj x hq
    have hhalf : range f ⊆ range (𝓡∂ 2) := by
      rintro z ⟨y,rfl⟩
      exact ⟨⟨f y,(T.homeo.symm y.val).property.1.1 c⟩,rfl⟩
    have hpos := interior_mono hhalf hfx
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at hpos
    change 0 < (T.homeo.symm (T.homeo q)).val c at hpos
    rw [T.homeo.symm_apply_apply] at hpos
    have hqc := hqsupp.2 c hcnot
    linarith
  have hBoundaryContainsLocus : boundaryLocus T.faces ⊆
      T.homeo ⁻¹' (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ := by
    let B : Set (T.Vertex → ℝ) := Subtype.val ''
      (T.homeo ⁻¹' (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ)
    have hBclosed : IsClosed B :=
      GeometricRealization.isClosed.isClosedMap_subtype_val _ hBoundaryClosed
    rintro q ⟨e,he,hqe⟩
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp
      (T.card_of_mem_edges (Finset.mem_filter.mp he).1)
    let da : T.Vertex → ℝ := Pi.single a 1
    let db : T.Vertex → ℝ := Pi.single b 1
    have hseg : openSegment ℝ da db ⊆ B := by
      rintro z ⟨r,s,hr,hs,hrs,rfl⟩
      have hz : r • da + s • db ∈ GeometricFace T.Vertex {a,b} := by
        refine ⟨(convex_stdSimplex ℝ T.Vertex) (single_mem_stdSimplex ℝ a)
          (single_mem_stdSimplex ℝ b) hr.le hs.le hrs,?_⟩
        intro k hk
        have hka : k ≠ a := fun h => hk (by simp [h])
        have hkb : k ≠ b := fun h => hk (by simp [h])
        simp [da,db,Pi.single_apply,hka,hkb]
      obtain ⟨t,ht⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp he).2
      have htm : t ∈ T.faces ∧ {a,b} ⊆ t :=
        Finset.mem_filter.mp (by rw [ht]; simp)
      let z' : T.realization := ⟨r • da + s • db,hz.1,t,htm.1,
        fun k hk => hz.2 k (fun h => hk (htm.2 h))⟩
      refine ⟨z',?_,rfl⟩
      apply hOnePage a b hab (Finset.mem_filter.mp he).2 z' _ _ hz
      · simpa [z',da,db,Pi.single_apply,hab,hab.symm] using hr
      · simpa [z',da,db,Pi.single_apply,hab,hab.symm] using hs
    have hqsum : q.val a + q.val b = 1 := by
      have hh := Finset.sum_subset (Finset.subset_univ ({a,b} : Finset T.Vertex))
        (fun k _ hk => hqe.2 k hk)
      have hy := q.property.1.2
      rw [← hh] at hy
      simpa [hab] using hy
    have hqseg : q.val ∈ segment ℝ da db := by
      refine ⟨q.val a,q.val b,q.property.1.1 a,q.property.1.1 b,hqsum,?_⟩
      funext k
      by_cases hka : k = a
      · subst k; simp [da,db,hab,hab.symm]
      by_cases hkb : k = b
      · subst k; simp [da,db,hab,hab.symm]
      simp [da,db,Pi.single_apply,hka,hkb,hqe.2 k (by simp [hka,hkb])]
    have hqB : q.val ∈ B := (closure_minimal hseg hBclosed)
      (segment_subset_closure_openSegment hqseg)
    obtain ⟨z,hz,hzq⟩ := hqB
    exact (Subtype.ext hzq : z = q) ▸ hz
  have hTwoPage (t u : Finset T.Vertex) (htF : t ∈ T.faces) (huF : u ∈ T.faces)
    (a b c d : T.Vertex) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (htc : t = insert c {a,b}) (hud : u = insert d {a,b})
    (q : T.realization) (hqa : 0 < q.val a) (hqb : 0 < q.val b)
    (hqsupp : q.val ∈ GeometricFace T.Vertex {a,b}) :
    (𝓡∂ 2).IsInteriorPoint (T.homeo q) := by
    classical
    have hPlaneImage : ∀ (U : Set (EuclideanSpace ℝ (Fin 2))), IsOpen U →
        ∀ (f : U → M), Continuous f → Function.Injective f →
          ∀ (x : U), (𝓡∂ 2).IsInteriorPoint (f x) := by
      intro U hU f hf hinj x
      let c := extChartAt (𝓡∂ 2) (f x)
      let V : Set (EuclideanSpace ℝ (Fin 2)) := Subtype.val '' (f ⁻¹' c.source)
      have hVopen : IsOpen V := hU.isOpenEmbedding_subtypeVal.isOpenMap _
        ((isOpen_extChartAt_source (I := 𝓡∂ 2) (f x)).preimage hf)
      have hsub : V ⊆ U := by rintro z ⟨y,hy,rfl⟩; exact y.property
      let g : V → U := fun y => ⟨y.val,hsub y.property⟩
      have hg : Continuous g := continuous_subtype_val.subtype_mk _
      have hgc (y : V) : f (g y) ∈ c.source := by
        obtain ⟨z,hz,hzy⟩ := y.property
        have hzg : z = g y := Subtype.ext hzy
        exact hzg ▸ hz
      have hcomp : Continuous (fun y : V => c (f (g y))) :=
        (continuousOn_extChartAt (I := 𝓡∂ 2) (f x)).comp_continuous (hf.comp hg) hgc
      have hicomp : Function.Injective (fun y : V => c (f (g y))) := by
        intro y z hyz
        have hh := hinj (c.injOn (hgc y) (hgc z) hyz)
        exact Subtype.ext (congrArg (fun z : U => z.val) hh)
      have hopen : IsOpen (range (fun y : V => c (f (g y)))) :=
        InvarianceOfDomain.isOpen_range_of_isOpen_of_continuous_injective
          (𝓘(ℝ,EuclideanSpace ℝ (Fin 2))) hVopen _ hcomp hicomp
      have hxV : x.val ∈ V := ⟨x,mem_extChartAt_source (f x),rfl⟩
      have hcx : c (f x) ∈ range (fun y : V => c (f (g y))) :=
        ⟨⟨x.val,hxV⟩,rfl⟩
      have hsubrange : range (fun y : V => c (f (g y))) ⊆ c.target := by
        rintro z ⟨y,rfl⟩
        exact c.map_source (hgc y)
      apply ModelWithCorners.isInteriorPoint_iff.mpr
      exact mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hopen.mem_nhds hcx) hsubrange)
    have max_pos_add_max_neg_eq_abs (x : ℝ) : max x 0 + max (-x) 0 = |x| := by
      by_cases hx : 0 ≤ x
      · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx),add_zero,abs_of_nonneg hx]
      · have hx' : x ≤ 0 := le_of_not_ge hx
        rw [max_eq_right hx',max_eq_left (neg_nonneg.mpr hx'),zero_add,abs_of_nonpos hx']
    have max_pos_sub_max_neg_eq_self (x : ℝ) : max x 0 - max (-x) 0 = x := by
      by_cases hx : 0 ≤ x
      · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx),sub_zero]
      · have hx' : x ≤ 0 := le_of_not_ge hx
        rw [max_eq_right hx',max_eq_left (neg_nonneg.mpr hx'),zero_sub,neg_neg]
    have hqsum : q.val a + q.val b = 1 := by
      have hh := Finset.sum_subset (Finset.subset_univ ({a,b} : Finset T.Vertex))
        (fun k _ hk => hqsupp.2 k hk)
      have hy := q.property.1.2
      rw [← hh] at hy
      simpa [hab] using hy
    let O : Set (EuclideanSpace ℝ (Fin 2)) := {x | |x 0| < min (q.val a) (q.val b) / 4 ∧ |x 1| < min (q.val a) (q.val b) / 4}
    have hOopen : IsOpen O := by
      have h0 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ |x 0|) := by fun_prop
      have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ |x 1|) := by fun_prop
      exact (isOpen_lt h0 continuous_const).inter (isOpen_lt h1 continuous_const)
    let weight (x : EuclideanSpace ℝ (Fin 2)) : T.Vertex → ℝ :=
      (q.val a - x 0) • Pi.single a 1 +
        (q.val b + x 0 - |x 1|) • Pi.single b 1 +
        max (x 1) 0 • Pi.single c 1 + max (-x 1) 0 • Pi.single d 1
    have weight_a (x : EuclideanSpace ℝ (Fin 2)) : weight x a = q.val a - x 0 := by
      simp [weight, hab, hac, had]
    have weight_b (x : EuclideanSpace ℝ (Fin 2)) : weight x b = q.val b + x 0 - |x 1| := by
      simp [weight, hab, hbc, hbd]
    have weight_c (x : EuclideanSpace ℝ (Fin 2)) : weight x c = max (x 1) 0 := by
      simp [weight, hac, hbc, hcd]
    have weight_d (x : EuclideanSpace ℝ (Fin 2)) : weight x d = max (-x 1) 0 := by
      simp [weight, had, hbd, hcd]
    have weight_other (x : EuclideanSpace ℝ (Fin 2)) {z : T.Vertex}
        (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) (hzd : z ≠ d) : weight x z = 0 := by
      simp [weight, hza, hzb, hzc, hzd]
    have sum_pi_single (v : T.Vertex) : ∑ z, Pi.single v (1 : ℝ) z = 1 := by
      rw [Fintype.sum_eq_single v]
      · simp
      · intro z hz
        exact Pi.single_eq_of_ne hz 1
    have weight_nonneg (x : O) (z : T.Vertex) : 0 ≤ weight x.1 z := by
      by_cases hza : z = a
      · subst z
        rw [weight_a]
        linarith [(abs_lt.mp x.2.1).2,min_le_left (q.val a) (q.val b)]
      by_cases hzb : z = b
      · subst z
        rw [weight_b]
        linarith [(abs_lt.mp x.2.1).1, x.2.2,min_le_right (q.val a) (q.val b)]
      by_cases hzc : z = c
      · subst z
        rw [weight_c]
        exact le_max_right _ _
      by_cases hzd : z = d
      · subst z
        rw [weight_d]
        exact le_max_right _ _
      rw [weight_other _ hza hzb hzc hzd]
    have weight_sum (x : EuclideanSpace ℝ (Fin 2)) : ∑ z, weight x z = 1 := by
      simp_rw [weight, Pi.add_apply, Pi.smul_apply]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum,
        sum_pi_single a, sum_pi_single b, sum_pi_single c, sum_pi_single d]
      simp only [smul_eq_mul, mul_one]
      linarith [max_pos_add_max_neg_eq_abs (x 1)]
    have weight_supported (x : O) : ∃ s ∈ T.faces, ∀ z ∉ s, weight x.1 z = 0 := by
      by_cases hx : 0 ≤ x.1 1
      · refine ⟨t, htF, ?_⟩
        intro z hzt
        have hza : z ≠ a := fun h ↦ hzt (h ▸ by simp [htc])
        have hzb : z ≠ b := fun h ↦ hzt (h ▸ by simp [htc])
        have hzc : z ≠ c := fun h ↦ hzt (h ▸ by simp [htc])
        by_cases hzd : z = d
        · subst z
          rw [weight_d, max_eq_right (neg_nonpos.mpr hx)]
        · exact weight_other _ hza hzb hzc hzd
      · have hx' : x.1 1 ≤ 0 := le_of_not_ge hx
        refine ⟨u, huF, ?_⟩
        intro z hzu
        have hza : z ≠ a := fun h ↦ hzu (h ▸ by simp [hud])
        have hzb : z ≠ b := fun h ↦ hzu (h ▸ by simp [hud])
        have hzd : z ≠ d := fun h ↦ hzu (h ▸ by simp [hud])
        by_cases hzc : z = c
        · subst z
          rw [weight_c, max_eq_right hx']
        · exact weight_other _ hza hzb hzc hzd
    let fan : O → T.realization := fun x ↦
      ⟨weight x.1, ⟨weight_nonneg x, weight_sum x.1⟩, weight_supported x⟩
    have fan_continuous : Continuous fan := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro z
      change Continuous fun x : O ↦ weight x.1 z
      simp only [weight, Pi.add_apply, Pi.smul_apply]
      fun_prop
    have fan_injective : Function.Injective fan := by
      intro x y hxy
      apply Subtype.ext
      apply PiLp.ext
      intro i
      have hval : weight x.1 = weight y.1 := congrArg Subtype.val hxy
      fin_cases i
      · change x.1 (0 : Fin 2) = y.1 (0 : Fin 2)
        have ha := congrFun hval a
        rw [weight_a, weight_a] at ha
        linarith
      · change x.1 (1 : Fin 2) = y.1 (1 : Fin 2)
        have hc := congrFun hval c
        have hd := congrFun hval d
        rw [weight_c, weight_c] at hc
        rw [weight_d, weight_d] at hd
        linarith [max_pos_sub_max_neg_eq_self (x.1 1),
          max_pos_sub_max_neg_eq_self (y.1 1)]
    let zeroO : O := ⟨0,by simp [O]; constructor <;> positivity⟩
    have hzero : fan zeroO = q := by
      apply Subtype.ext
      funext k
      by_cases hka : k = a
      · subst k; simp [fan,weight,zeroO,hab,hac,had]
      by_cases hkb : k = b
      · subst k; simp [fan,weight,zeroO,hab,hbc,hbd]
      simp [fan,weight,zeroO,hka,hkb,hqsupp.2 k (by simp [hka,hkb])]
    have hi := hPlaneImage O hOopen (T.homeo ∘ fan)
      (T.homeo.continuous.comp fan_continuous) (T.homeo.injective.comp fan_injective) zeroO
    simpa only [Function.comp_apply,hzero] using hi
  have hTriangleInterior (a b c : T.Vertex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : {a,b,c} ∈ T.faces) (q : T.realization)
    (hqa : 0 < q.val a) (hqb : 0 < q.val b) (hqc : 0 < q.val c)
    (hqsupp : q.val ∈ GeometricFace T.Vertex {a,b,c}) :
    (𝓡∂ 2).IsInteriorPoint (T.homeo q) := by
    classical
    have hPlaneImage : ∀ (U : Set (EuclideanSpace ℝ (Fin 2))), IsOpen U →
        ∀ (f : U → M), Continuous f → Function.Injective f →
          ∀ (x : U), (𝓡∂ 2).IsInteriorPoint (f x) := by
      intro U hU f hf hinj x
      let c := extChartAt (𝓡∂ 2) (f x)
      let V : Set (EuclideanSpace ℝ (Fin 2)) := Subtype.val '' (f ⁻¹' c.source)
      have hVopen : IsOpen V := hU.isOpenEmbedding_subtypeVal.isOpenMap _
        ((isOpen_extChartAt_source (I := 𝓡∂ 2) (f x)).preimage hf)
      have hsub : V ⊆ U := by rintro z ⟨y,hy,rfl⟩; exact y.property
      let g : V → U := fun y => ⟨y.val,hsub y.property⟩
      have hg : Continuous g := continuous_subtype_val.subtype_mk _
      have hgc (y : V) : f (g y) ∈ c.source := by
        obtain ⟨z,hz,hzy⟩ := y.property
        have hzg : z = g y := Subtype.ext hzy
        exact hzg ▸ hz
      have hcomp : Continuous (fun y : V => c (f (g y))) :=
        (continuousOn_extChartAt (I := 𝓡∂ 2) (f x)).comp_continuous (hf.comp hg) hgc
      have hicomp : Function.Injective (fun y : V => c (f (g y))) := by
        intro y z hyz
        have hh := hinj (c.injOn (hgc y) (hgc z) hyz)
        exact Subtype.ext (congrArg (fun z : U => z.val) hh)
      have hopen : IsOpen (range (fun y : V => c (f (g y)))) :=
        InvarianceOfDomain.isOpen_range_of_isOpen_of_continuous_injective
          (𝓘(ℝ,EuclideanSpace ℝ (Fin 2))) hVopen _ hcomp hicomp
      have hxV : x.val ∈ V := ⟨x,mem_extChartAt_source (f x),rfl⟩
      have hcx : c (f x) ∈ range (fun y : V => c (f (g y))) :=
        ⟨⟨x.val,hxV⟩,rfl⟩
      have hsubrange : range (fun y : V => c (f (g y))) ⊆ c.target := by
        rintro z ⟨y,rfl⟩
        exact c.map_source (hgc y)
      apply ModelWithCorners.isInteriorPoint_iff.mpr
      exact mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hopen.mem_nhds hcx) hsubrange)
  
    let O : Set (EuclideanSpace ℝ (Fin 2)) := {x | 0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < 1}
    have hOopen : IsOpen O := by
      have h0 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) => x 0) := by fun_prop
      have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) => x 1) := by fun_prop
      exact (isOpen_lt continuous_const h0).inter
        ((isOpen_lt continuous_const h1).inter (isOpen_lt (h0.add h1) continuous_const))
    let weight (x : EuclideanSpace ℝ (Fin 2)) : T.Vertex → ℝ :=
      x 0 • Pi.single a 1 + x 1 • Pi.single b 1 + (1-x 0-x 1) • Pi.single c 1
    have weight_a (x : EuclideanSpace ℝ (Fin 2)) : weight x a = x 0 := by
      simp [weight,hab,hac]
    have weight_b (x : EuclideanSpace ℝ (Fin 2)) : weight x b = x 1 := by
      simp [weight,hab,hbc]
    have weight_c (x : EuclideanSpace ℝ (Fin 2)) : weight x c = 1-x 0-x 1 := by
      simp [weight,hac,hbc]
    have weight_other (x : EuclideanSpace ℝ (Fin 2)) {z : T.Vertex}
        (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) : weight x z = 0 := by
      simp [weight,hza,hzb,hzc]
    have weight_nonneg (x : O) (z : T.Vertex) : 0 ≤ weight x.val z := by
      by_cases ha : z = a
      · subst z; rw [weight_a]; exact x.property.1.le
      by_cases hb : z = b
      · subst z; rw [weight_b]; exact x.property.2.1.le
      by_cases hc : z = c
      · subst z; rw [weight_c]; linarith [x.property.2.2]
      rw [weight_other _ ha hb hc]
    have sum_pi_single (v : T.Vertex) : ∑ z, Pi.single v (1 : ℝ) z = 1 := by
      rw [Fintype.sum_eq_single v]
      · simp
      · intro z hz; exact Pi.single_eq_of_ne hz 1
    have weight_sum (x : EuclideanSpace ℝ (Fin 2)) : ∑ z,weight x z = 1 := by
      simp_rw [weight,Pi.add_apply,Pi.smul_apply]
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
        ← Finset.smul_sum,← Finset.smul_sum,← Finset.smul_sum,
        sum_pi_single a,sum_pi_single b,sum_pi_single c]
      simp only [smul_eq_mul,mul_one]
      ring
    let fan : O → T.realization := fun x => ⟨weight x.val,
      ⟨weight_nonneg x,weight_sum x.val⟩,{a,b,c},ht,by
        intro z hz
        exact weight_other _ (fun h => hz (by simp [h]))
          (fun h => hz (by simp [h])) (fun h => hz (by simp [h]))⟩
    have hfan : Continuous fan := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro z
      change Continuous (fun x : O => weight x.val z)
      simp only [weight,Pi.add_apply,Pi.smul_apply]
      fun_prop
    have hfinj : Function.Injective fan := by
      intro x y heq
      apply Subtype.ext
      apply PiLp.ext
      intro i
      have hv : weight x.val = weight y.val := congrArg Subtype.val heq
      fin_cases i
      · change x.val (0 : Fin 2) = y.val (0 : Fin 2)
        simpa only [weight_a] using congrFun hv a
      · change x.val (1 : Fin 2) = y.val (1 : Fin 2)
        simpa only [weight_b] using congrFun hv b
    have hqsum : q.val a + q.val b + q.val c = 1 := by
      have hh := Finset.sum_subset (Finset.subset_univ ({a,b,c} : Finset T.Vertex))
        (fun k _ hk => hqsupp.2 k hk)
      have hy := q.property.1.2
      rw [← hh] at hy
      simpa [hab,hac,hbc,add_assoc] using hy
    let qO : O := ⟨WithLp.toLp 2 ![q.val a,q.val b],hqa,hqb,by
      change q.val a + q.val b < 1
      linarith⟩
    have heq : fan qO = q := by
      apply Subtype.ext
      funext k
      by_cases ha : k = a
      · subst k; exact weight_a _
      by_cases hb : k = b
      · subst k; exact weight_b _
      by_cases hc : k = c
      · subst k; change weight qO.val c = q.val c; rw [weight_c]; change 1-q.val a-q.val b=q.val c; linarith
      change weight qO.val k = q.val k
      rw [weight_other _ ha hb hc,hqsupp.2 k (by simp [ha,hb,hc])]
    simpa only [Function.comp_apply,heq] using
      hPlaneImage O hOopen (T.homeo ∘ fan) (T.homeo.continuous.comp hfan)
        (T.homeo.injective.comp hfinj) qO
  have hEdgeBoundary (q : T.realization)
      (hq : T.homeo q ∈ (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ)
      (hnv : ∀ v, q.val ≠ Pi.single v 1)
      (a b : T.Vertex) (hab : a ≠ b)
      (t : Finset T.Vertex) (ht : t ∈ T.faces) (habt : {a,b} ⊆ t)
      (hsupp : q.val ∈ GeometricFace T.Vertex {a,b}) : q ∈ boundaryLocus T.faces := by
    have hsum : q.val a + q.val b = 1 := by
      have hh := Finset.sum_subset (Finset.subset_univ ({a,b} : Finset T.Vertex))
        (fun k _ hk => hsupp.2 k hk)
      have hy := q.property.1.2
      rw [← hh] at hy
      simpa [hab] using hy
    have hqa : 0 < q.val a := by
      by_contra h
      have ha : q.val a = 0 := le_antisymm (le_of_not_gt h) (q.property.1.1 a)
      have hb : q.val b = 1 := by linarith
      apply hnv b
      funext k
      by_cases hka : k = a
      · subst k; simp [ha,hab]
      by_cases hkb : k = b
      · subst k; simp [hb]
      simp [hkb,hsupp.2 k (by simp [hka,hkb])]
    have hqb : 0 < q.val b := by
      by_contra h
      have hb : q.val b = 0 := le_antisymm (le_of_not_gt h) (q.property.1.1 b)
      have ha : q.val a = 1 := by linarith
      apply hnv a
      funext k
      by_cases hka : k = a
      · subst k; simp [ha]
      by_cases hkb : k = b
      · subst k; simp [hb,hab.symm]
      simp [hka,hsupp.2 k (by simp [hka,hkb])]
    have he : {a,b} ∈ T.edges := T.mem_edges_of_subset_face ht habt (by simp [hab])
    have hle := T.surfaceIncidence.edge_valence_le_two {a,b} he
    have hpos : 0 < (T.faces.filter (fun u => {a,b} ⊆ u)).card :=
      Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,habt⟩⟩
    by_cases hcard : (T.faces.filter (fun u => {a,b} ⊆ u)).card = 1
    · exact ⟨{a,b},Finset.mem_filter.mpr ⟨he,hcard⟩,hsupp⟩
    have htwo : (T.faces.filter (fun u => {a,b} ⊆ u)).card = 2 := by omega
    obtain ⟨t',u,htu,hfilter⟩ := Finset.card_eq_two.mp htwo
    have htt' : t' ∈ T.faces ∧ {a,b} ⊆ t' :=
      Finset.mem_filter.mp (by rw [hfilter]; simp)
    have huu : u ∈ T.faces ∧ {a,b} ⊆ u :=
      Finset.mem_filter.mp (by rw [hfilter]; simp)
    have hthird (s : Finset T.Vertex) (hs : s ∈ T.faces) (habs : {a,b} ⊆ s) :
        ∃ c, c ≠ a ∧ c ≠ b ∧ s = insert c {a,b} := by
      have hdiff : (s \ {a,b}).card = 1 := by
        rw [Finset.card_sdiff_of_subset habs,T.faces_card s hs]; simp [hab]
      obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hdiff
      have hcnot : c ∉ ({a,b} : Finset T.Vertex) :=
        (Finset.mem_sdiff.mp (show c ∈ s \ {a,b} by rw [hc]; simp)).2
      refine ⟨c,(fun h => hcnot (by simp [h])),(fun h => hcnot (by simp [h])),?_⟩
      rw [← Finset.sdiff_union_of_subset habs,hc]
      ext k; simp [or_left_comm]
    obtain ⟨c,hca,hcb,htc⟩ := hthird t' htt'.1 htt'.2
    obtain ⟨d,hda,hdb,hud⟩ := hthird u huu.1 huu.2
    have hcd : c ≠ d := by intro h; apply htu; rw [htc,hud,h]
    exact (hq (hTwoPage t' u htt'.1 huu.1 a b c d hab hca.symm hcb.symm
      hda.symm hdb.symm hcd htc hud q hqa hqb hsupp)).elim
  have hNonvertexBoundary (q : T.realization)
      (hq : T.homeo q ∈ (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ)
      (hnv : ∀ v, q.val ≠ Pi.single v 1) : q ∈ boundaryLocus T.faces := by
    obtain ⟨t,ht,hqt⟩ := q.property.2
    obtain ⟨a,b,c,hab,hac,hbc,htabc⟩ := Finset.card_eq_three.mp (T.faces_card t ht)
    subst t
    by_cases hqa : q.val a = 0
    · apply hEdgeBoundary q hq hnv b c hbc {a,b,c} ht (by simp) ⟨q.property.1,?_⟩
      intro k hk
      by_cases hka : k = a
      · simpa [hka] using hqa
      exact hqt k (by simpa [hka] using hk)
    by_cases hqb : q.val b = 0
    · apply hEdgeBoundary q hq hnv a c hac {a,b,c} ht (by simp) ⟨q.property.1,?_⟩
      intro k hk
      by_cases hkb : k = b
      · simpa [hkb] using hqb
      exact hqt k (by simpa [hkb] using hk)
    have hqc : q.val c = 0 := by
      by_contra hc
      exact hq (hTriangleInterior a b c hab hac hbc ht q
        (lt_of_le_of_ne (q.property.1.1 a) (Ne.symm hqa))
        (lt_of_le_of_ne (q.property.1.1 b) (Ne.symm hqb))
        (lt_of_le_of_ne (q.property.1.1 c) (Ne.symm hc)) ⟨q.property.1,hqt⟩)
    apply hEdgeBoundary q hq hnv a b hab {a,b,c} ht (by simp) ⟨q.property.1,?_⟩
    intro k hk
    by_cases hkc : k = c
    · simpa [hkc] using hqc
    exact hqt k (by simpa [hkc] using hk)
  have hBoundaryDenseAwayFinite (C K : Set M) (hC : IsClosed C) (hK : K.Finite)
      (hCK : ∀ y, y ∈ (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ → y ∉ K → y ∈ C) :
      (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ ⊆ C := by
    classical
    have hBoundaryInChart (e : OpenPartialHomeomorph M (EuclideanHalfSpace 2))
        (y : M) (hy : y ∈ e.source) :
        y ∈ (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ ↔ (e y).val 0 = 0 := by
      change ¬ (𝓡∂ 2).IsInteriorPoint y ↔ _
      rw [InvarianceOfDomain.isInteriorPoint_iff_any_chart (𝓡∂ 2) hy,
        interior_range_modelWithCornersEuclideanHalfSpace]
      change ¬ 0 < (e y).val 0 ↔ (e y).val 0 = 0
      constructor
      · intro h; exact le_antisymm (le_of_not_gt h) (e y).property
      · intro h; rw [h]; exact lt_irrefl 0
    intro x hx
    by_contra hxc
    let e := chartAt (EuclideanHalfSpace 2) x
    let line : ℝ → EuclideanHalfSpace 2 := fun s => ⟨WithLp.toLp 2 ![0,s],by simp⟩
    have hl : Continuous line := by
      apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop
    let U : Set (EuclideanHalfSpace 2) := e.target ∩ e.symm ⁻¹' Cᶜ
    have hU : IsOpen U := e.symm.continuousOn.isOpen_inter_preimage e.open_target hC.isOpen_compl
    have hex : e x ∈ U := ⟨e.map_source (mem_chart_source _ _),by
      change e.symm (e x) ∈ Cᶜ
      rw [e.left_inv (mem_chart_source _ _)]; exact hxc⟩
    have hline : line ((e x).val 1) = e x := by
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · exact (hBoundaryInChart e x (mem_chart_source _ _) |>.mp hx).symm
      · rfl
    have hnonempty : (e x).val 1 ∈ line ⁻¹' U := by
      change line ((e x).val 1) ∈ U
      rw [hline]; exact hex
    have hinfinite : (line ⁻¹' U).Infinite :=
      infinite_of_mem_nhds ((e x).val 1) ((hU.preimage hl).mem_nhds hnonempty)
    obtain ⟨s,hs,hsK⟩ := (hinfinite.sdiff (hK.image (fun y => (e y).val 1))).nonempty
    let y := e.symm (line s)
    have hysource : y ∈ e.source := e.map_target hs.1
    have hey : e y = line s := e.right_inv hs.1
    have hyB : y ∈ (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ := by
      apply (hBoundaryInChart e y hysource).mpr
      rw [hey]; rfl
    have hynK : y ∉ K := by
      intro hyK
      apply hsK
      refine ⟨y,hyK,?_⟩
      change (e y).val 1 = s
      rw [hey]; rfl
    exact hs.2 (hCK y hyB hynK)
  let K0 : Set T.realization := Subtype.val ⁻¹' range (fun v : T.Vertex => Pi.single v (1 : ℝ))
  have hK0 : K0.Finite := Set.Finite.preimage Subtype.val_injective.injOn
    (Set.finite_range (fun v : T.Vertex => Pi.single v (1 : ℝ)))
  let K : Set M := T.homeo '' K0
  have hK : K.Finite := hK0.image T.homeo
  let C : Set M := T.homeo.symm ⁻¹' boundaryLocus T.faces
  have hC : IsClosed C := hLocusClosed.preimage T.homeo.symm.continuous
  have hrecognition : (ModelWithCorners.interior (I := 𝓡∂ 2) M)ᶜ ⊆ C := by
    apply hBoundaryDenseAwayFinite C K hC hK
    intro y hy hynK
    apply hNonvertexBoundary (T.homeo.symm y)
    · simpa using hy
    · intro v hv
      apply hynK
      refine ⟨T.homeo.symm y,?_,T.homeo.apply_symm_apply y⟩
      exact ⟨v,hv.symm⟩
  refine ⟨?_,hfans⟩
  intro q
  constructor
  · intro hq
    have hh := hrecognition hq
    change T.homeo.symm (T.homeo q) ∈ boundaryLocus T.faces at hh
    simpa using hh
  · exact fun hq => hBoundaryContainsLocus hq


end CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry

-- Restore the A2 donor elaboration option before its exact source block.
set_option backward.isDefEq.respectTransparency true

set_option maxHeartbeats 2000000

open Set Topology CurveComplex
open LeanEval.Topology.ClassificationOfSurfaces

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry

/-- Finite geometry from explicit ordered fans and one literal boundary cycle.
The neighborhood is arbitrary; no global surface/collar premise is supplied. -/
theorem finite_boundary_fan_cycle_inward_band
    (V : Type) [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) (hfaces : ∀ t ∈ F, t.card = 3)
    (fans : (v : ↥(boundaryVertices F)) → OrderedBoundaryFan F v.val)
    (c : BoundaryCycle F)
    (U : Set (GeometricRealization V F)) (hU : IsOpen U)
    (hcontains : range c.circle ⊆ U) :
    Nonempty (BoundaryCycleInwardBand c U) := by
  classical
  have actualEdgeTriangle : ∀ i : Fin c.length, ∃ z : V,
      z ≠ c.vertex i ∧ z ≠ c.vertex (cyclicNext c.length c.length_ge_three i) ∧
      {c.vertex i, c.vertex (cyclicNext c.length c.length_ge_three i), z} ∈ F ∧
      (∀ τ ∈ F, {c.vertex i, c.vertex (cyclicNext c.length c.length_ge_three i)} ⊆ τ →
        τ = {c.vertex i, c.vertex (cyclicNext c.length c.length_ge_three i), z}) := by
    intro i
    let a := c.vertex i
    let b := c.vertex (cyclicNext c.length c.length_ge_three i)
    have hab : a ≠ b := c.consecutive_vertices_ne i
    have he := c.consecutive_edge_mem i
    obtain ⟨τ, hτ, hunique⟩ := boundaryEdge_unique_triangle he
    have hτcard := hfaces τ hτ.1
    have hex : ∃ z ∈ τ, z ∉ ({a,b} : Finset V) := by
      by_contra hn
      push Not at hn
      have hsub : τ ⊆ {a,b} := by intro z hz; exact hn z hz
      have hc := Finset.card_le_card hsub
      simp [hab, hτcard] at hc
    obtain ⟨z, hz, hzne⟩ := hex
    have hza : z ≠ a := by intro h; subst z; simp at hzne
    have hzb : z ≠ b := by intro h; subst z; simp at hzne
    have hsub : ({a,b,z} : Finset V) ⊆ τ := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hτ.2 (by simp [a])
      · exact hτ.2 (by simp [b])
      · exact hz
    have heq : ({a,b,z} : Finset V) = τ := by
      apply Finset.eq_of_subset_of_card_le hsub
      simp [hτcard, hab, Ne.symm hza, Ne.symm hzb]
    refine ⟨z, hza, hzb, ?_, ?_⟩
    · change ({a,b,z} : Finset V) ∈ F
      rw [heq]
      exact hτ.1
    · intro σ hσ hσedge
      exact (hunique σ ⟨hσ,hσedge⟩).trans heq.symm

  have incidentExtremeTriangle : ∀ (a b z : V) (fan : OrderedBoundaryFan F a),
      a ≠ b → {a,b} ∈ boundaryEdges F →
      (∀ τ ∈ F, {a,b} ⊆ τ → τ = {a,b,z}) →
      (fan.vertex 0 = b ∧ fan.vertex ⟨1, by have := fan.positive; omega⟩ = z) ∨
      (fan.vertex (Fin.last fan.length) = b ∧
        fan.vertex ⟨fan.length - 1, by omega⟩ = z) := by
    intro a b z fan hab he hunique
    have hext := (fan.boundary_edges_exact {a,b}).mp ⟨he, by simp⟩
    rcases hext with hfirst | hlast
    · left
      have hb : fan.vertex 0 = b := by
        have hm : b ∈ ({a,fan.vertex 0} : Finset V) := by rw [← hfirst]; simp
        simpa [Ne.symm hab, eq_comm] using hm
      let i : Fin fan.length := ⟨0, fan.positive⟩
      have hi0 : i.castSucc = 0 := by apply Fin.ext; rfl
      have hi1 : i.succ = ⟨1, by have := fan.positive; omega⟩ := by apply Fin.ext; rfl
      have ht : {a,b,fan.vertex i.succ} ∈ F := by
        simpa only [hi0, hb] using fan.face_mem i
      have htri := hunique _ ht (by intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢; tauto)
      have hm : fan.vertex i.succ ∈ ({a,b,z} : Finset V) := by rw [← htri]; simp
      have hna := fan.off_center i.succ
      have hnb : fan.vertex i.succ ≠ b := by
        rw [← hb, ← hi0]
        exact Ne.symm (fan.consecutive_vertices_ne i)
      have hz : fan.vertex i.succ = z := by
        simpa [hna, hnb] using hm
      exact ⟨hb, hi1 ▸ hz⟩
    · right
      have hb : fan.vertex (Fin.last fan.length) = b := by
        have hm : b ∈ ({a,fan.vertex (Fin.last fan.length)} : Finset V) := by rw [← hlast]; simp
        simpa [Ne.symm hab, eq_comm] using hm
      let i : Fin fan.length := ⟨fan.length - 1, by have := fan.positive; omega⟩
      have hi0 : i.castSucc = ⟨fan.length - 1, by omega⟩ := by apply Fin.ext; rfl
      have hi1 : i.succ = Fin.last fan.length := by apply Fin.ext; dsimp [i]; have := fan.positive; omega
      have ht : {a,fan.vertex i.castSucc,b} ∈ F := by
        simpa only [hi1, hb] using fan.face_mem i
      have htri := hunique _ ht (by intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢; tauto)
      have hm : fan.vertex i.castSucc ∈ ({a,b,z} : Finset V) := by rw [← htri]; simp
      have hna := fan.off_center i.castSucc
      have hnb : fan.vertex i.castSucc ≠ b := by
        rw [← hb, ← hi1]
        exact fan.consecutive_vertices_ne i
      have hz : fan.vertex i.castSucc = z := by simpa [hna, hnb] using hm
      exact ⟨hb, hi0 ▸ hz⟩

  have calibratedExtremePorts : ∀ (a b z : V) (fan : OrderedBoundaryFan F a),
      a ≠ b → {a,b} ∈ boundaryEdges F →
      (∀ τ ∈ F, {a,b} ⊆ τ → τ = {a,b,z}) →
      (fan.vertex 0 = b ∧
        ∀ (r : Interval) (w : V),
          (fan.trianglePoint ⟨0, fan.positive⟩ r ⟨1/3,by norm_num,by norm_num⟩).val w =
            (1 - (r : ℝ)) * (if a = w then 1 else 0) +
            (2 * (r : ℝ) / 3) * (if b = w then 1 else 0) +
            ((r : ℝ) / 3) * (if z = w then 1 else 0)) ∨
      (fan.vertex (Fin.last fan.length) = b ∧
        ∀ (r : Interval) (w : V),
          (fan.trianglePoint ⟨fan.length-1,by have := fan.positive; omega⟩ r
            ⟨2/3,by norm_num,by norm_num⟩).val w =
            (1 - (r : ℝ)) * (if a = w then 1 else 0) +
            (2 * (r : ℝ) / 3) * (if b = w then 1 else 0) +
            ((r : ℝ) / 3) * (if z = w then 1 else 0)) := by
    intro a b z fan hab he hunique
    rcases incidentExtremeTriangle a b z fan hab he hunique with ⟨hb,hz⟩ | ⟨hb,hz⟩
    · left
      refine ⟨hb, ?_⟩
      intro r w
      let i : Fin fan.length := ⟨0,fan.positive⟩
      have hi0 : i.castSucc = 0 := by apply Fin.ext; rfl
      have hi1 : i.succ = ⟨1, by have := fan.positive; omega⟩ := by apply Fin.ext; rfl
      change (fan.trianglePoint i r _).val w = _
      rw [fan.trianglePoint_coordinate,hi0,hi1,hb,hz]
      dsimp only [Subtype.coe_mk]
      ring
    · right
      refine ⟨hb, ?_⟩
      intro r w
      let i : Fin fan.length := ⟨fan.length-1,by have := fan.positive; omega⟩
      have hi0 : i.castSucc = ⟨fan.length-1,by omega⟩ := by apply Fin.ext; rfl
      have hi1 : i.succ = Fin.last fan.length := by apply Fin.ext; dsimp [i]; have := fan.positive; omega
      change (fan.trianglePoint i r _).val w = _
      rw [fan.trianglePoint_coordinate,hi0,hi1,hb,hz]
      dsimp only [Subtype.coe_mk]
      ring

  have successor_bijection : Function.Bijective (cyclicNext c.length c.length_ge_three) := by
    have hinj : Function.Injective (cyclicNext c.length c.length_ge_three) := by
      intro i j he
      apply Fin.ext
      have he := congrArg Fin.val he
      dsimp [cyclicNext] at he
      by_cases hi : i.val + 1 = c.length
      · rw [hi, Nat.mod_self] at he
        by_cases hj : j.val + 1 = c.length
        · omega
        · rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)] at he
          omega
      · rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)] at he
        by_cases hj : j.val + 1 = c.length
        · rw [hj, Nat.mod_self] at he
          omega
        · rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)] at he
          omega
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩

  let fanAt (i : Fin c.length) : OrderedBoundaryFan F (c.vertex i) :=
    fans ⟨c.vertex i, c.vertex_mem_boundary i⟩
  have fanOrientation : ∀ (i j : Fin c.length),
      cyclicNext c.length c.length_ge_three j = i →
      ((fanAt i).vertex 0 = c.vertex j ∧
        (fanAt i).vertex (Fin.last (fanAt i).length) =
          c.vertex (cyclicNext c.length c.length_ge_three i)) ∨
      ((fanAt i).vertex (Fin.last (fanAt i).length) = c.vertex j ∧
        (fanAt i).vertex 0 = c.vertex (cyclicNext c.length c.length_ge_three i)) := by
    intro i j hj
    have hneighbors : c.vertex j ≠ c.vertex (cyclicNext c.length c.length_ge_three i) := by
      intro he
      have hidx := c.vertex_injective he
      have ht : cyclicNext c.length c.length_ge_three
          (cyclicNext c.length c.length_ge_three i) = i := by rw [← hidx, hj]
      exact cyclicNext_twice_ne c.length_ge_three i ht
    have hin : {c.vertex i,c.vertex j} ∈ boundaryEdges F := by
      have he := c.consecutive_edge_mem j
      rw [hj, Finset.pair_comm] at he
      exact he
    have hout := c.consecutive_edge_mem i
    have hi := ((fanAt i).boundary_edges_exact _).mp ⟨hin, by simp⟩
    have ho := ((fanAt i).boundary_edges_exact _).mp ⟨hout, by simp⟩
    have hprevne : c.vertex j ≠ c.vertex i := by
      intro he
      have hji := c.vertex_injective he
      apply cyclicNext_ne c.length_ge_three j
      exact hj.trans hji.symm
    have hnextne := Ne.symm (c.consecutive_vertices_ne i)
    have hprev : (fanAt i).vertex 0 = c.vertex j ∨
        (fanAt i).vertex (Fin.last (fanAt i).length) = c.vertex j := by
      rcases hi with hi | hi
      · left
        have hm : c.vertex j ∈ ({c.vertex i,(fanAt i).vertex 0} : Finset V) := by rw [← hi]; simp
        simpa [hprevne,eq_comm] using hm
      · right
        have hm : c.vertex j ∈ ({c.vertex i,(fanAt i).vertex (Fin.last (fanAt i).length)} : Finset V) := by rw [← hi]; simp
        simpa [hprevne,eq_comm] using hm
    have hnext : (fanAt i).vertex 0 = c.vertex (cyclicNext c.length c.length_ge_three i) ∨
        (fanAt i).vertex (Fin.last (fanAt i).length) = c.vertex (cyclicNext c.length c.length_ge_three i) := by
      rcases ho with ho | ho
      · left
        have hm : c.vertex (cyclicNext c.length c.length_ge_three i) ∈
            ({c.vertex i,(fanAt i).vertex 0} : Finset V) := by rw [← ho]; simp
        simpa [hnextne,eq_comm] using hm
      · right
        have hm : c.vertex (cyclicNext c.length c.length_ge_three i) ∈
            ({c.vertex i,(fanAt i).vertex (Fin.last (fanAt i).length)} : Finset V) := by rw [← ho]; simp
        simpa [hnextne,eq_comm] using hm
    rcases hprev with hp | hp <;> rcases hnext with hn | hn
    · exact (hneighbors (hp.symm.trans hn)).elim
    · exact Or.inl ⟨hp,hn⟩
    · exact Or.inr ⟨hp,hn⟩
    · exact (hneighbors (hp.symm.trans hn)).elim

  have descendClock {X : Type} [TopologicalSpace X] (m : ℕ) (hm : 3 ≤ m)
      (H : Fin m → C(Interval × Interval, X))
      (hseam : ∀ (i : Fin m) (t : Interval), H i (t,1) = H (cyclicNext m hm i) (t,0)) :
      ∃! G : C(Interval × Circle, X),
        ∀ (i : Fin m) (t s : Interval), G (t,edgeClock m i s) = H i (t,s) := by
    classical
    have clockFiber : ∀ (m : ℕ) (hm : 3 ≤ m) (i j : Fin m) (s t : Interval)
        (he : edgeClock m i s = edgeClock m j t),
        (i = j ∧ s = t) ∨
          (s = 1 ∧ t = 0 ∧ cyclicNext m hm i = j) ∨
          (s = 0 ∧ t = 1 ∧ cyclicNext m hm j = i) := by
      intro m hm i j s t he
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
      have hp0 : 2 * Real.pi ≠ 0 := by positivity
      change Circle.exp (2 * Real.pi * ((i.val : ℝ) + (s : ℝ)) / m) =
        Circle.exp (2 * Real.pi * ((j.val : ℝ) + (t : ℝ)) / m) at he
      obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
      have heq : (i.val : ℝ) + (s : ℝ) =
          (j.val : ℝ) + (t : ℝ) + (k : ℝ) * (m : ℝ) := by
        apply mul_left_cancel₀ hp0
        calc
          (2 * Real.pi) * ((i.val : ℝ) + (s : ℝ)) =
              (2 * Real.pi * ((i.val : ℝ) + (s : ℝ)) / m) * m := by field_simp [hm0]
          _ = (2 * Real.pi * ((j.val : ℝ) + (t : ℝ)) / m + k * (2 * Real.pi)) * m := by rw [hk]
          _ = (2 * Real.pi) * ((j.val : ℝ) + (t : ℝ) + (k : ℝ) * (m : ℝ)) := by
            field_simp [hm0]
      have hi : (i.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast i.isLt
      have hj : (j.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast j.isLt
      have hin := Nat.cast_nonneg (α := ℝ) i.val
      have hjn := Nat.cast_nonneg (α := ℝ) j.val
      have hklo : -1 ≤ k := by
        by_contra hn
        have hn' : (k : ℝ) ≤ -2 := by exact_mod_cast (by omega : k ≤ -2)
        nlinarith [s.property.1, t.property.2]
      have hkhi : k ≤ 1 := by
        by_contra hn
        have hn' : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
        nlinarith [s.property.2, t.property.1]
      rcases (by omega : k = -1 ∨ k = 0 ∨ k = 1) with hkval | hkval | hkval
      · have hs : (s : ℝ) = 0 := by simp [hkval] at heq; linarith [s.property.1, t.property.2]
        have ht : (t : ℝ) = 1 := by simp [hkval] at heq; linarith [s.property.1, t.property.2]
        have hi0 : i.val = 0 := by
          have : (i.val : ℝ) = 0 := by simp [hkval] at heq; linarith [s.property.1, t.property.2]
          exact_mod_cast this
        have hjlast : j.val + 1 = m := by
          have : (j.val : ℝ) + 1 = (m : ℝ) := by simp [hkval] at heq; linarith [s.property.1, t.property.2]
          exact_mod_cast this
        right; right
        refine ⟨Subtype.ext hs, Subtype.ext ht, ?_⟩
        apply Fin.ext
        simp [cyclicNext, hjlast, hi0]
      · simp only [hkval, Int.cast_zero, zero_mul, add_zero] at heq
        by_cases hij : i = j
        · left
          refine ⟨hij, Subtype.ext ?_⟩
          rw [hij] at heq; linarith
        · by_cases hlt : i.val < j.val
          · have hlt' : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hlt
            have hs : (s : ℝ) = 1 := by linarith [s.property.2, t.property.1]
            have ht : (t : ℝ) = 0 := by linarith [s.property.2, t.property.1]
            have hstep : i.val + 1 = j.val := by
              have : (i.val : ℝ) + 1 = (j.val : ℝ) := by linarith
              exact_mod_cast this
            right; left
            refine ⟨Subtype.ext hs, Subtype.ext ht, ?_⟩
            apply Fin.ext
            simp [cyclicNext, hstep, Nat.mod_eq_of_lt j.isLt]
          · have hlt : j.val < i.val := by
              have : i.val ≠ j.val := by intro h; exact hij (Fin.ext h)
              omega
            have hlt' : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hlt
            have hs : (s : ℝ) = 0 := by linarith [s.property.1, t.property.2]
            have ht : (t : ℝ) = 1 := by linarith [s.property.1, t.property.2]
            have hstep : j.val + 1 = i.val := by
              have : (j.val : ℝ) + 1 = (i.val : ℝ) := by linarith
              exact_mod_cast this
            right; right
            refine ⟨Subtype.ext hs, Subtype.ext ht, ?_⟩
            apply Fin.ext
            simp [cyclicNext, hstep, Nat.mod_eq_of_lt i.isLt]
      · have hs : (s : ℝ) = 1 := by simp [hkval] at heq; linarith [s.property.2, t.property.1]
        have ht : (t : ℝ) = 0 := by simp [hkval] at heq; linarith [s.property.2, t.property.1]
        have hj0 : j.val = 0 := by
          have : (j.val : ℝ) = 0 := by simp [hkval] at heq; linarith [s.property.2, t.property.1]
          exact_mod_cast this
        have hilast : i.val + 1 = m := by
          have : (i.val : ℝ) + 1 = (m : ℝ) := by simp [hkval] at heq; linarith [s.property.2, t.property.1]
          exact_mod_cast this
        right; left
        refine ⟨Subtype.ext hs, Subtype.ext ht, ?_⟩
        apply Fin.ext
        simp [cyclicNext, hilast, hj0]
    let q : C(Fin m × (Interval × Interval), Interval × Circle) := ⟨
      fun p => (p.2.1, edgeClock m p.1 p.2.2), by
        rw [continuous_prod_of_discrete_left]
        intro i
        apply continuous_fst.prodMk
        unfold edgeClock
        fun_prop⟩
    have hsurj : Function.Surjective q := by
      intro p
      obtain ⟨i,s,hs,he⟩ := edgeClock_cover hm p.2
      exact ⟨(i,p.1,s), by apply Prod.ext <;> simp [q,he]⟩
    have hq : IsQuotientMap q := IsQuotientMap.of_surjective_continuous hsurj q.continuous
    let Htotal : C(Fin m × (Interval × Interval), X) := ⟨fun p => H p.1 p.2,
      continuous_prod_of_discrete_left.mpr (fun i => (H i).continuous)⟩
    have hfactor : Function.FactorsThrough Htotal q := by
      intro p p' he
      change (p.2.1, edgeClock m p.1 p.2.2) = (p'.2.1, edgeClock m p'.1 p'.2.2) at he
      have ht : p.2.1 = p'.2.1 := congrArg (fun q : Interval × Circle => q.1) he
      have hs : edgeClock m p.1 p.2.2 = edgeClock m p'.1 p'.2.2 :=
        congrArg (fun q : Interval × Circle => q.2) he
      change H p.1 (p.2.1,p.2.2) = H p'.1 (p'.2.1,p'.2.2)
      rcases clockFiber m hm p.1 p'.1 p.2.2 p'.2.2 hs with ⟨hi,hs⟩ | ⟨hs,hs',hi⟩ | ⟨hs,hs',hi⟩
      · rw [hi,ht,hs]
      · rw [hs,hs',ht,← hi]
        exact hseam p.1 p'.2.1
      · rw [hs,hs',ht,← hi]
        exact (hseam p'.1 p'.2.1).symm
    let G := hq.lift Htotal hfactor
    have hG : ∀ (i : Fin m) (t s : Interval), G (t,edgeClock m i s) = H i (t,s) := by
      intro i t s
      have he := congrArg (fun h : C(Fin m × (Interval × Interval), X) => h (i,t,s))
        (hq.lift_comp Htotal hfactor)
      exact he
    refine ⟨G,hG,?_⟩
    intro G' hG'
    apply ContinuousMap.ext
    intro p
    obtain ⟨i,s,hs,he⟩ := edgeClock_cover hm p.2
    change G' (p.1,p.2) = G (p.1,p.2)
    rw [← he, hG', hG]

  choose third third_ne_start third_ne_end third_triangle third_unique using actualEdgeTriangle
  have hEdgeStrips := fun i : Fin c.length =>
    boundary_edge_triangle_trapezoid V F hfaces (c.vertex i)
      (c.vertex (cyclicNext c.length c.length_ge_three i)) (third i)
      (third_triangle i) (c.consecutive_edge_mem i) (1/8 : ℝ) (by norm_num) (by norm_num)
  choose edgeStrip edgeStrip_coordinates edgeStrip_embedded edgeStrip_boundary edgeStrip_range using hEdgeStrips
  have hSectors : ∀ i : Fin c.length,
      Nonempty ((fanAt i).WholeSector (1/4 : ℝ)
        ⟨1/3,by norm_num,by norm_num⟩ ⟨2/3,by norm_num,by norm_num⟩) := by
    intro i
    apply whole_ordered_boundary_fan_sector_two_ports V F hfaces (c.vertex i) (fanAt i)
      (1/4) (by norm_num) (by norm_num) _ _
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hn := Nat.cast_nonneg (α := ℝ) ((fanAt i).length - 1)
    dsimp
    linarith
  let sectorAt (i : Fin c.length) := Classical.choice (hSectors i)

  have edgeVertexIntersection (a b z : V) (hab : a ≠ b) (hza : z ≠ a) (hzb : z ≠ b)
      (fan : OrderedBoundaryFan F a)
      (hext : (fan.vertex 0 = b ∧ fan.vertex ⟨1,by have := fan.positive; omega⟩ = z) ∨
        (fan.vertex (Fin.last fan.length) = b ∧ fan.vertex ⟨fan.length-1,by omega⟩ = z))
      (E : C(↥(Icc (0 : ℝ) (1/8)) × Interval, GeometricRealization V F))
      (hE : ∀ r s w, (E (r,s)).val w =
        ((1 - (r : ℝ)) - (s : ℝ) * (1 - 5 * (r : ℝ) / 3)) * (if a = w then 1 else 0) +
        (2 * (r : ℝ) / 3 + (s : ℝ) * (1 - 5 * (r : ℝ) / 3)) * (if b = w then 1 else 0) +
        ((r : ℝ) / 3) * (if z = w then 1 else 0))
      (VP : Set (GeometricRealization V F))
      (hVP : ∀ q, q ∈ VP ↔ 0 ≤ 1 - q.val a ∧ 1 - q.val a ≤ 1/8 ∧
        (1 - q.val a) / 3 ≤ fan.linkMoment q ∧
        fan.linkMoment q ≤ ((fan.length : ℝ) - 1/3) * (1 - q.val a)) :
      ∀ (r : ↥(Icc (0 : ℝ) (1/8))) (s : Interval), E (r,s) ∈ VP ↔ s = 0 := by
    classical
    have hn : (1 : ℝ) ≤ (fan.length : ℝ) := by exact_mod_cast fan.positive
    have hface : ∀ r s, (E (r,s)).val ∈ GeometricFace V {a,b,z} := by
      intro r s
      refine ⟨(E (r,s)).property.1, ?_⟩
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hw
      rw [hE]
      simp [Ne.symm hw.1,Ne.symm hw.2.1,Ne.symm hw.2.2]
    have ha : ∀ r s, (E (r,s)).val a = (1 - (r : ℝ)) - (s : ℝ) * (1 - 5 * (r : ℝ) / 3) := by
      intro r s; rw [hE]; simp [Ne.symm hab,hza]
    have hz : ∀ r s, (E (r,s)).val z = (r : ℝ) / 3 := by
      intro r s; rw [hE]; simp [Ne.symm hza,Ne.symm hzb]
    rcases hext with ⟨hb,hzv⟩ | ⟨hb,hzv⟩
    · have hm : ∀ r s, fan.linkMoment (E (r,s)) = (r : ℝ) / 3 := by
        intro r s
        let i : Fin fan.length := ⟨0,fan.positive⟩
        have hi0 : i.castSucc = 0 := by apply Fin.ext; rfl
        have hi1 : i.succ = ⟨1,by have := fan.positive; omega⟩ := by apply Fin.ext; rfl
        have hqface : (E (r,s)).val ∈ GeometricFace V {a,fan.vertex i.castSucc,fan.vertex i.succ} := by
          simpa only [hi0,hi1,hb,hzv] using hface r s
        obtain ⟨ρ,θ,hq⟩ := WholeFanProof.point_of_face fan i (E (r,s)) hqface
        have hqz : (E (r,s)).val z = (ρ : ℝ) * (θ : ℝ) := by
          rw [hq,← hzv,← hi1,fan.trianglePoint_next]
        rw [hq,fan.trianglePoint_linkMoment]
        simp only [i, Fin.val_mk, Nat.cast_zero, zero_add]
        rw [← hqz,hz]
      intro r s
      rw [hVP,ha,hm]
      have hr := r.property.1
      have hrδ := r.property.2
      have hs := s.property.1
      have hgap : 0 < 1 - 5 * (r : ℝ) / 3 := by linarith
      constructor
      · rintro ⟨h1,h2,h3,h4⟩
        apply Subtype.ext
        change (s : ℝ) = 0
        nlinarith
      · rintro rfl
        change 0 ≤ 1 - (1 - (r : ℝ) - 0 * _) ∧ _
        norm_num only [show ((0 : Interval) : ℝ) = 0 from rfl, zero_mul, sub_zero, sub_sub_cancel]
        refine ⟨hr,hrδ,le_rfl,?_⟩
        nlinarith
    · have hm : ∀ r s, fan.linkMoment (E (r,s)) =
          (fan.length : ℝ) * (1 - (E (r,s)).val a) - (r : ℝ) / 3 := by
        intro r s
        let i : Fin fan.length := ⟨fan.length-1,by have := fan.positive; omega⟩
        have hi0 : i.castSucc = ⟨fan.length-1,by omega⟩ := by apply Fin.ext; rfl
        have hi1 : i.succ = Fin.last fan.length := by apply Fin.ext; dsimp [i]; have := fan.positive; omega
        have hqface : (E (r,s)).val ∈ GeometricFace V {a,fan.vertex i.castSucc,fan.vertex i.succ} := by
          have ht : ({a,z,b} : Finset V) = {a,b,z} := by
            ext w; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
          rw [hi0,hi1,hb,hzv,ht]
          exact hface r s
        obtain ⟨ρ,θ,hq⟩ := WholeFanProof.point_of_face fan i (E (r,s)) hqface
        have hqz : (E (r,s)).val z = (ρ : ℝ) * (1 - (θ : ℝ)) := by
          rw [hq,← hzv,← hi0,fan.trianglePoint_start]
        have hqn : (E (r,s)).val a = 1 - (ρ : ℝ) := by rw [hq,fan.trianglePoint_center]
        have hidx : (i.val : ℝ) + 1 = (fan.length : ℝ) := by
          have hi : i.val + 1 = fan.length := by dsimp [i]; have := fan.positive; omega
          exact_mod_cast hi
        rw [hq,fan.trianglePoint_linkMoment,← hq,hqn]
        calc
          (ρ : ℝ) * ((i.val : ℝ) + (θ : ℝ)) =
              ((i.val : ℝ) + 1) * (ρ : ℝ) - (ρ : ℝ) * (1 - (θ : ℝ)) := by ring
          _ = (fan.length : ℝ) * (ρ : ℝ) - (r : ℝ) / 3 := by rw [hidx,← hqz,hz]
          _ = _ := by ring
      intro r s
      rw [hVP,hm,ha]
      have hr := r.property.1
      have hrδ := r.property.2
      have hs := s.property.1
      have hgap : 0 < 1 - 5 * (r : ℝ) / 3 := by linarith
      constructor
      · rintro ⟨h1,h2,h3,h4⟩
        apply Subtype.ext
        change (s : ℝ) = 0
        nlinarith
      · rintro rfl
        change 0 ≤ 1 - (1 - (r : ℝ) - 0 * _) ∧ _
        norm_num only [show ((0 : Interval) : ℝ) = 0 from rfl, zero_mul, sub_zero, sub_sub_cancel]
        refine ⟨hr,hrδ,?_,?_⟩ <;> nlinarith

  have edgeExtremeMoments (a b z : V) (hab : a ≠ b) (hza : z ≠ a) (hzb : z ≠ b)
      (fan : OrderedBoundaryFan F a)
      (hext : (fan.vertex 0 = b ∧ fan.vertex ⟨1,by have := fan.positive; omega⟩ = z) ∨
        (fan.vertex (Fin.last fan.length) = b ∧ fan.vertex ⟨fan.length-1,by omega⟩ = z))
      (E : C(↥(Icc (0 : ℝ) (1/8)) × Interval, GeometricRealization V F))
      (hE : ∀ r s w, (E (r,s)).val w =
        ((1 - (r : ℝ)) - (s : ℝ) * (1 - 5 * (r : ℝ) / 3)) * (if a = w then 1 else 0) +
        (2 * (r : ℝ) / 3 + (s : ℝ) * (1 - 5 * (r : ℝ) / 3)) * (if b = w then 1 else 0) +
        ((r : ℝ) / 3) * (if z = w then 1 else 0)) :
      (fan.vertex 0 = b ∧ ∀ r s, fan.linkMoment (E (r,s)) = (r : ℝ) / 3) ∨
      (fan.vertex (Fin.last fan.length) = b ∧ ∀ r s,
        fan.linkMoment (E (r,s)) = (fan.length : ℝ) * (1 - (E (r,s)).val a) - (r : ℝ) / 3) := by
    classical
    have hn : (1 : ℝ) ≤ (fan.length : ℝ) := by exact_mod_cast fan.positive
    have hface : ∀ r s, (E (r,s)).val ∈ GeometricFace V {a,b,z} := by
      intro r s
      refine ⟨(E (r,s)).property.1, ?_⟩
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hw
      rw [hE]
      simp [Ne.symm hw.1,Ne.symm hw.2.1,Ne.symm hw.2.2]
    have ha : ∀ r s, (E (r,s)).val a = (1 - (r : ℝ)) - (s : ℝ) * (1 - 5 * (r : ℝ) / 3) := by
      intro r s; rw [hE]; simp [Ne.symm hab,hza]
    have hz : ∀ r s, (E (r,s)).val z = (r : ℝ) / 3 := by
      intro r s; rw [hE]; simp [Ne.symm hza,Ne.symm hzb]
    rcases hext with ⟨hb,hzv⟩ | ⟨hb,hzv⟩
    · left
      refine ⟨hb, ?_⟩
      have hm : ∀ r s, fan.linkMoment (E (r,s)) = (r : ℝ) / 3 := by
        intro r s
        let i : Fin fan.length := ⟨0,fan.positive⟩
        have hi0 : i.castSucc = 0 := by apply Fin.ext; rfl
        have hi1 : i.succ = ⟨1,by have := fan.positive; omega⟩ := by apply Fin.ext; rfl
        have hqface : (E (r,s)).val ∈ GeometricFace V {a,fan.vertex i.castSucc,fan.vertex i.succ} := by
          simpa only [hi0,hi1,hb,hzv] using hface r s
        obtain ⟨ρ,θ,hq⟩ := WholeFanProof.point_of_face fan i (E (r,s)) hqface
        have hqz : (E (r,s)).val z = (ρ : ℝ) * (θ : ℝ) := by
          rw [hq,← hzv,← hi1,fan.trianglePoint_next]
        rw [hq,fan.trianglePoint_linkMoment]
        simp only [i, Fin.val_mk, Nat.cast_zero, zero_add]
        rw [← hqz,hz]
      exact hm
    · right
      refine ⟨hb, ?_⟩
      have hm : ∀ r s, fan.linkMoment (E (r,s)) =
          (fan.length : ℝ) * (1 - (E (r,s)).val a) - (r : ℝ) / 3 := by
        intro r s
        let i : Fin fan.length := ⟨fan.length-1,by have := fan.positive; omega⟩
        have hi0 : i.castSucc = ⟨fan.length-1,by omega⟩ := by apply Fin.ext; rfl
        have hi1 : i.succ = Fin.last fan.length := by apply Fin.ext; dsimp [i]; have := fan.positive; omega
        have hqface : (E (r,s)).val ∈ GeometricFace V {a,fan.vertex i.castSucc,fan.vertex i.succ} := by
          have ht : ({a,z,b} : Finset V) = {a,b,z} := by
            ext w; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
          rw [hi0,hi1,hb,hzv,ht]
          exact hface r s
        obtain ⟨ρ,θ,hq⟩ := WholeFanProof.point_of_face fan i (E (r,s)) hqface
        have hqz : (E (r,s)).val z = (ρ : ℝ) * (1 - (θ : ℝ)) := by
          rw [hq,← hzv,← hi0,fan.trianglePoint_start]
        have hqn : (E (r,s)).val a = 1 - (ρ : ℝ) := by rw [hq,fan.trianglePoint_center]
        have hidx : (i.val : ℝ) + 1 = (fan.length : ℝ) := by
          have hi : i.val + 1 = fan.length := by dsimp [i]; have := fan.positive; omega
          exact_mod_cast hi
        rw [hq,fan.trianglePoint_linkMoment,← hq,hqn]
        calc
          (ρ : ℝ) * ((i.val : ℝ) + (θ : ℝ)) =
              ((i.val : ℝ) + 1) * (ρ : ℝ) - (ρ : ℝ) * (1 - (θ : ℝ)) := by ring
          _ = (fan.length : ℝ) * (ρ : ℝ) - (r : ℝ) / 3 := by rw [hidx,← hqz,hz]
          _ = _ := by ring
      exact hm

  have stripOppositesVanish (q : GeometricRealization V F)
      (a b z A B Z : V)
      (hab : a ≠ b) (hza : z ≠ a) (hzb : z ≠ b)
      (hAB : A ≠ B) (hZA : Z ≠ A) (hZB : Z ≠ B)
      (hface : q.val ∈ GeometricFace V {a,b,z})
      (hFace : q.val ∈ GeometricFace V {A,B,Z})
      (ha : 2 * q.val z ≤ q.val a) (hb : 2 * q.val z ≤ q.val b)
      (hA : 2 * q.val Z ≤ q.val A) (hB : 2 * q.val Z ≤ q.val B)
      (hedges : ({a,b} : Finset V) ≠ {A,B}) :
      q.val z = 0 ∧ q.val Z = 0 := by
    classical
    have positive_forces_equal : ∀ (a b z A B Z : V),
        a ≠ b → z ≠ a → z ≠ b → A ≠ B → Z ≠ A → Z ≠ B →
        q.val ∈ GeometricFace V {a,b,z} →
        q.val ∈ GeometricFace V {A,B,Z} →
        2 * q.val z ≤ q.val a → 2 * q.val z ≤ q.val b →
        2 * q.val Z ≤ q.val A → 2 * q.val Z ≤ q.val B →
        0 < q.val z → ({a,b} : Finset V) = {A,B} := by
      intro a b z A B Z hab hza hzb hAB hZA hZB hf hF ha hb hA hB hz
      have ha0 : 0 < q.val a := by linarith
      have hb0 : 0 < q.val b := by linarith
      have hsub : ({a,b,z} : Finset V) ⊆ {A,B,Z} := by
        intro w hw
        simp only [Finset.mem_insert,Finset.mem_singleton] at hw
        have hw0 : 0 < q.val w := by rcases hw with rfl | rfl | rfl <;> assumption
        by_contra hw
        have := hF.2 w hw
        linarith
      have htri : ({a,b,z} : Finset V) = {A,B,Z} := by
        apply Finset.eq_of_subset_of_card_le hsub
        simp [hab,Ne.symm hza,Ne.symm hzb,hAB,Ne.symm hZA,Ne.symm hZB]
      by_cases hzZ : z = Z
      · subst Z
        ext w
        have hw := Finset.ext_iff.mp htri w
        simp only [Finset.mem_insert,Finset.mem_singleton] at hw ⊢
        by_cases hwz : w = z
        · subst w
          simp [hza,hzb,hZA,hZB]
        · tauto
      · have hzmem : z ∈ ({A,B,Z} : Finset V) := hsub (by simp)
        have hZmem : Z ∈ ({a,b,z} : Finset V) := by rw [htri]; simp
        simp only [Finset.mem_insert,Finset.mem_singleton] at hzmem hZmem
        have h1 : 2 * q.val z ≤ q.val Z := by
          rcases hZmem with h | h | h
          · simpa [h] using ha
          · simpa [h] using hb
          · exact (hzZ h.symm).elim
        have h2 : 2 * q.val Z ≤ q.val z := by
          rcases hzmem with h | h | h
          · simpa [h] using hA
          · simpa [h] using hB
          · exact (hzZ h).elim
        exfalso
        linarith
    constructor
    · have hn := q.property.1.1 z
      by_contra hzero
      have hp : 0 < q.val z := lt_of_le_of_ne hn (Ne.symm hzero)
      exact hedges (positive_forces_equal a b z A B Z hab hza hzb hAB hZA hZB
        hface hFace ha hb hA hB hp)
    · have hn := q.property.1.1 Z
      by_contra hzero
      have hp : 0 < q.val Z := lt_of_le_of_ne hn (Ne.symm hzero)
      exact hedges (positive_forces_equal A B Z a b z hAB hZA hZB hab hza hzb
        hFace hface hA hB ha hb hp).symm

  have makeVertexPiece : ∀ (v : V) (fan : OrderedBoundaryFan F v)
      (sector : fan.WholeSector (1/4 : ℝ)
        ⟨1/3,by norm_num,by norm_num⟩ ⟨2/3,by norm_num,by norm_num⟩)
      (η : ℝ) (hη : η = 1 ∨ η = -1),
      let TD : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1/8 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1}
      ∃ vertexPiece : C(TD, GeometricRealization V F),
        IsEmbedding vertexPiece ∧
        (∀ p : TD, (1 - (vertexPiece p).val v, fan.linkMoment (vertexPiece p)) =
          (p.val.1, (fan.length : ℝ) / 2 * p.val.1 +
            η * ((fan.length : ℝ) / 2 - 1/3) * p.val.2)) ∧
        (∀ p : TD, vertexPiece p ∈ boundaryLocus F ↔ p.val.1 = 0) ∧
        (∀ q : GeometricRealization V F, q ∈ range vertexPiece ↔
          0 ≤ 1 - q.val v ∧ 1 - q.val v ≤ 1/8 ∧
            (1 - q.val v) / 3 ≤ fan.linkMoment q ∧
            fan.linkMoment q ≤ ((fan.length : ℝ) - 1/3) * (1 - q.val v)) := by
    intro v fan sector η hη
    classical
    dsimp only
    let TD : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1/8 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1}
    have hn : (1 : ℝ) ≤ (fan.length : ℝ) := by exact_mod_cast fan.positive
    have hD : 0 < (fan.length : ℝ) / 2 - 1/3 := by linarith
    have hp : ∀ p : TD,
        (p.val.1, (fan.length : ℝ) / 2 * p.val.1 +
          η * ((fan.length : ℝ) / 2 - 1/3) * p.val.2) ∈ fan.sectorDomain (1/4) := by
      intro p
      have hr := p.property.1
      have hrδ := p.property.2.1
      have hxmin := p.property.2.2.1
      have hxmax := p.property.2.2.2
      change 0 ≤ p.val.1 ∧ 0 ≤ _ ∧ _ ≤ _ ∧ p.val.1 < _
      rcases hη with rfl | rfl <;> constructor
      · exact hr
      · refine ⟨?_,?_,by linarith⟩ <;> nlinarith
      · exact hr
      · refine ⟨?_,?_,by linarith⟩ <;> nlinarith
    let coords : C(TD, ↥(fan.sectorDomain (1/4))) := ⟨fun p => ⟨
      (p.val.1, (fan.length : ℝ) / 2 * p.val.1 +
        η * ((fan.length : ℝ) / 2 - 1/3) * p.val.2), hp p⟩, by
          apply Continuous.subtype_mk
          fun_prop⟩
    let vertexPiece : C(TD, GeometricRealization V F) := ⟨
      fun p => (sector.chart (coords p)).val,
      continuous_subtype_val.comp (sector.chart.continuous.comp coords.continuous)⟩
    have hcoordinate : ∀ p : TD,
        (1 - (vertexPiece p).val v, fan.linkMoment (vertexPiece p)) =
          (p.val.1, (fan.length : ℝ) / 2 * p.val.1 +
            η * ((fan.length : ℝ) / 2 - 1/3) * p.val.2) := by
      intro p
      have he := sector.inverse_coordinates (sector.chart (coords p))
      rw [sector.chart.symm_apply_apply] at he
      exact he.symm
    have hinj : Function.Injective vertexPiece := by
      intro p q he
      have hc := congrArg (fun a : GeometricRealization V F =>
        (1 - a.val v, fan.linkMoment a)) he
      rw [hcoordinate, hcoordinate] at hc
      have hr := congrArg (fun a : ℝ × ℝ => a.1) hc
      change p.val.1 = q.val.1 at hr
      have hx : p.val.2 = q.val.2 := by
        have hu := congrArg (fun a : ℝ × ℝ => a.2) hc
        dsimp at hu
        rw [hr] at hu
        have hη0 : η ≠ 0 := by rcases hη with rfl | rfl <;> norm_num
        apply mul_left_cancel₀ (mul_ne_zero hη0 (ne_of_gt hD))
        linarith
      apply Subtype.ext
      exact Prod.ext hr hx
    have hTDclosed : IsClosed TD := by
      exact (isClosed_le continuous_const continuous_fst).inter
        ((isClosed_le continuous_fst continuous_const).inter
          ((isClosed_le continuous_fst.neg continuous_snd).inter
            (isClosed_le continuous_snd continuous_fst)))
    have hTDcompact : IsCompact TD := by
      apply ((isCompact_Icc : IsCompact (Icc (0 : ℝ) (1/8))).prod
        (isCompact_Icc : IsCompact (Icc (-1/8 : ℝ) (1/8)))).of_isClosed_subset hTDclosed
      intro p hp
      exact ⟨⟨hp.1,hp.2.1⟩,⟨by linarith [hp.2.1,hp.2.2.1],by linarith [hp.2.1,hp.2.2.2]⟩⟩
    have : CompactSpace TD := isCompact_iff_compactSpace.mp hTDcompact
    have hangle : ∀ p : TD,
        p.val.1 / 3 ≤ (fan.length : ℝ) / 2 * p.val.1 +
          η * ((fan.length : ℝ) / 2 - 1/3) * p.val.2 ∧
        (fan.length : ℝ) / 2 * p.val.1 +
          η * ((fan.length : ℝ) / 2 - 1/3) * p.val.2 ≤
            ((fan.length : ℝ) - 1/3) * p.val.1 := by
      intro p
      have hr := p.property.1
      have hxmin := p.property.2.2.1
      have hxmax := p.property.2.2.2
      rcases hη with rfl | rfl <;> constructor <;> nlinarith
    refine ⟨vertexPiece, (vertexPiece.continuous.isClosedEmbedding hinj).isEmbedding,
      hcoordinate, ?_, ?_⟩
    · intro p
      change (sector.chart (coords p)).val ∈ boundaryLocus F ↔ p.val.1 = 0
      rw [sector.boundary_exact]
      change (((fan.length : ℝ) / 2 * p.val.1 +
          η * ((fan.length : ℝ) / 2 - 1/3) * p.val.2) = 0 ∨
        ((fan.length : ℝ) / 2 * p.val.1 +
          η * ((fan.length : ℝ) / 2 - 1/3) * p.val.2) = (fan.length : ℝ) * p.val.1) ↔ p.val.1 = 0
      have hr := p.property.1
      have hxmin := p.property.2.2.1
      have hxmax := p.property.2.2.2
      have ha := hangle p
      constructor
      · intro he
        rcases he with he | he <;> linarith [ha.1,ha.2]
      · intro he
        have hx : p.val.2 = 0 := by linarith
        left; simp [he,hx]
    · intro q
      constructor
      · rintro ⟨p,rfl⟩
        have hc := hcoordinate p
        have hr := congrArg (fun a : ℝ × ℝ => a.1) hc
        have hu := congrArg (fun a : ℝ × ℝ => a.2) hc
        dsimp at hr hu
        rw [hr,hu]
        exact ⟨p.property.1,p.property.2.1,hangle p⟩
      · rintro ⟨hr,hrδ,huL,huR⟩
        let r : ℝ := 1 - q.val v
        let u : ℝ := fan.linkMoment q
        let D : ℝ := (fan.length : ℝ) / 2 - 1/3
        have hD0 : D ≠ 0 := ne_of_gt hD
        let x : ℝ := η * (u - (fan.length : ℝ) / 2 * r) / D
        have hx : -r ≤ x ∧ x ≤ r := by
          dsimp [x,r,u,D]
          rcases hη with rfl | rfl
          · constructor
            · apply (le_div_iff₀ hD).mpr
              nlinarith
            · apply (div_le_iff₀ hD).mpr
              nlinarith
          · constructor
            · apply (le_div_iff₀ hD).mpr
              nlinarith
            · apply (div_le_iff₀ hD).mpr
              nlinarith
        let p : TD := ⟨(r,x),hr,hrδ,hx⟩
        refine ⟨p,?_⟩
        apply WholeFanProof.coordinate_injective fan
        · have hp := congrArg (fun a : ℝ × ℝ => a.1) (hcoordinate p)
          dsimp [p,r] at hp
          linarith
        · linarith
        · rw [hcoordinate]
          apply Prod.ext
          · rfl
          · change (fan.length : ℝ) / 2 * r + η * D * x = u
            dsimp [x]
            rcases hη with rfl | rfl <;> field_simp [hD0] <;> ring

  let TD : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1/8 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1}
  let orientation (i : Fin c.length) : ℝ :=
    if (fanAt i).vertex (Fin.last (fanAt i).length) =
      c.vertex (cyclicNext c.length c.length_ge_three i) then 1 else -1
  have orientation_sign : ∀ i, orientation i = 1 ∨ orientation i = -1 := by
    intro i
    dsimp [orientation]
    split <;> simp
  have hVertexPieces := fun i : Fin c.length =>
    makeVertexPiece (c.vertex i) (fanAt i) (sectorAt i) (orientation i) (orientation_sign i)
  dsimp only at hVertexPieces
  choose vertexPiece vertexPiece_embedded vertexPiece_coordinates vertexPiece_boundary vertexPiece_range
    using hVertexPieces
  have distinctCycleEdges : ∀ i j : Fin c.length, i ≠ j →
      ({c.vertex i,c.vertex (cyclicNext c.length c.length_ge_three i)} : Finset V) ≠
        {c.vertex j,c.vertex (cyclicNext c.length c.length_ge_three j)} := by
    intro i j hij he
    have hm : c.vertex i ∈ ({c.vertex j,c.vertex (cyclicNext c.length c.length_ge_three j)} : Finset V) := by
      rw [← he]; simp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with h | h
    · exact hij (c.vertex_injective h)
    · have hi : i = cyclicNext c.length c.length_ge_three j := c.vertex_injective h
      have hn : c.vertex (cyclicNext c.length c.length_ge_three i) ∈
          ({c.vertex j,c.vertex (cyclicNext c.length c.length_ge_three j)} : Finset V) := by
        rw [← he]; simp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hn
      rcases hn with hn | hn
      · have hn := c.vertex_injective hn
        exact cyclicNext_twice_ne c.length_ge_three j (by rw [← hi,hn])
      · have hn := c.vertex_injective hn
        exact cyclicNext_ne c.length_ge_three i (hn.trans hi.symm)
  have edgeStartVertexIntersection : ∀ (i : Fin c.length)
      (r : ↥(Icc (0 : ℝ) (1/8))) (s : Interval),
      edgeStrip i (r,s) ∈ range (vertexPiece i) ↔ s = 0 := by
    intro i
    apply edgeVertexIntersection (c.vertex i)
      (c.vertex (cyclicNext c.length c.length_ge_three i)) (third i)
      (c.consecutive_vertices_ne i) (third_ne_start i) (third_ne_end i) (fanAt i)
      (incidentExtremeTriangle _ _ _ _ (c.consecutive_vertices_ne i)
        (c.consecutive_edge_mem i) (third_unique i))
      (edgeStrip i) (edgeStrip_coordinates i) (range (vertexPiece i))
      (vertexPiece_range i)

  have vertexPieceCenter : ∀ (i : Fin c.length) (p : TD),
      (vertexPiece i p).val (c.vertex i) = 1 - p.val.1 := by
    intro i p
    have he := congrArg (fun a : ℝ × ℝ => a.1) (vertexPiece_coordinates i p)
    dsimp at he
    linarith
  have vertexPieceRangesDisjoint : ∀ i j : Fin c.length, i ≠ j →
      Disjoint (range (vertexPiece i)) (range (vertexPiece j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro q ⟨p,hp⟩ ⟨p',hp'⟩
    have hv : c.vertex i ≠ c.vertex j := fun h => hij (c.vertex_injective h)
    apply Set.disjoint_left.mp (disjoint_positive_vertex_sectors (F := F) hv)
    · change (1/2 : ℝ) < q.val (c.vertex i)
      rw [← hp,vertexPieceCenter]
      linarith [p.property.2.1]
    · change (1/2 : ℝ) < q.val (c.vertex j)
      rw [← hp',vertexPieceCenter]
      linarith [p'.property.2.1]
  let reverseParameter : C(Interval,Interval) := ⟨fun s =>
    ⟨1 - (s : ℝ),by constructor <;> linarith [s.property.1,s.property.2]⟩,by
      apply Continuous.subtype_mk
      fun_prop⟩
  have reverse_zero : ∀ s : Interval, reverseParameter s = 0 ↔ s = 1 := by
    intro s
    constructor
    · intro hs
      apply Subtype.ext
      have he := congrArg (fun t : Interval => (t : ℝ)) hs
      change 1 - (s : ℝ) = 0 at he
      change (s : ℝ) = 1
      linarith
    · rintro rfl
      apply Subtype.ext
      change 1 - (1 : ℝ) = 0
      norm_num
  let reverseStrip (i : Fin c.length) :
      C(↥(Icc (0 : ℝ) (1/8)) × Interval, GeometricRealization V F) :=
    ⟨fun p => edgeStrip i (p.1,reverseParameter p.2),by
      exact (edgeStrip i).continuous.comp
        (continuous_fst.prodMk (reverseParameter.continuous.comp continuous_snd))⟩
  have reverse_coordinates : ∀ (i : Fin c.length)
      (r : ↥(Icc (0 : ℝ) (1/8))) (s : Interval) (w : V),
      (reverseStrip i (r,s)).val w =
        ((1 - (r : ℝ)) - (s : ℝ) * (1 - 5 * (r : ℝ) / 3)) *
          (if c.vertex (cyclicNext c.length c.length_ge_three i) = w then 1 else 0) +
        (2 * (r : ℝ) / 3 + (s : ℝ) * (1 - 5 * (r : ℝ) / 3)) *
          (if c.vertex i = w then 1 else 0) +
        ((r : ℝ) / 3) * (if third i = w then 1 else 0) := by
    intro i r s w
    change (edgeStrip i (r,reverseParameter s)).val w = _
    rw [edgeStrip_coordinates]
    dsimp only [reverseParameter,ContinuousMap.coe_mk,Subtype.coe_mk]
    ring
  have edgeEndVertexIntersection : ∀ (i : Fin c.length)
      (r : ↥(Icc (0 : ℝ) (1/8))) (s : Interval),
      edgeStrip i (r,s) ∈ range (vertexPiece (cyclicNext c.length c.length_ge_three i)) ↔ s = 1 := by
    intro i r s
    let j := cyclicNext c.length c.length_ge_three i
    have hunique : ∀ τ ∈ F, {c.vertex j,c.vertex i} ⊆ τ →
        τ = {c.vertex j,c.vertex i,third i} := by
      intro τ hτ he
      have ht := third_unique i τ hτ (by simpa only [Finset.pair_comm] using he)
      rw [ht]
      ext w
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    have hext := incidentExtremeTriangle (c.vertex j) (c.vertex i) (third i) (fanAt j)
      (Ne.symm (c.consecutive_vertices_ne i))
      (by simpa only [Finset.pair_comm] using c.consecutive_edge_mem i) hunique
    have he := edgeVertexIntersection (c.vertex j) (c.vertex i) (third i)
      (Ne.symm (c.consecutive_vertices_ne i)) (third_ne_end i) (third_ne_start i)
      (fanAt j) hext (reverseStrip i) (reverse_coordinates i)
      (range (vertexPiece j)) (vertexPiece_range j) r (reverseParameter s)
    have hrev : reverseParameter (reverseParameter s) = s := by
      apply Subtype.ext
      change 1 - (1 - (s : ℝ)) = (s : ℝ)
      ring
    change edgeStrip i (r,reverseParameter (reverseParameter s)) ∈ range (vertexPiece j) ↔
      reverseParameter s = 0 at he
    rw [hrev,reverse_zero] at he
    exact he
  have edgeThirdCoordinate : ∀ (i : Fin c.length)
      (r : ↥(Icc (0 : ℝ) (1/8))) (s : Interval),
      (edgeStrip i (r,s)).val (third i) = (r : ℝ) / 3 := by
    intro i r s
    rw [edgeStrip_coordinates]
    simp [Ne.symm (third_ne_start i),Ne.symm (third_ne_end i)]
  have distinctStripCollisionHeight : ∀ (i j : Fin c.length), i ≠ j →
      ∀ (r r' : ↥(Icc (0 : ℝ) (1/8))) (s s' : Interval),
      edgeStrip i (r,s) = edgeStrip j (r',s') → (r : ℝ) = 0 ∧ (r' : ℝ) = 0 := by
    intro i j hij r r' s s' he
    have hi := (edgeStrip_range i (edgeStrip i (r,s))).mp ⟨(r,s),rfl⟩
    have hj := (edgeStrip_range j (edgeStrip i (r,s))).mp ⟨(r',s'),he.symm⟩
    have hz := stripOppositesVanish (edgeStrip i (r,s))
      (c.vertex i) (c.vertex (cyclicNext c.length c.length_ge_three i)) (third i)
      (c.vertex j) (c.vertex (cyclicNext c.length c.length_ge_three j)) (third j)
      (c.consecutive_vertices_ne i) (third_ne_start i) (third_ne_end i)
      (c.consecutive_vertices_ne j) (third_ne_start j) (third_ne_end j)
      hi.1 hj.1 hi.2.2.2.1 hi.2.2.2.2 hj.2.2.2.1 hj.2.2.2.2
      (distinctCycleEdges i j hij)
    constructor
    · rw [edgeThirdCoordinate] at hz
      linarith [hz.1]
    · have h := hz.2
      rw [he,edgeThirdCoordinate] at h
      linarith
  have edgeOtherVertexDisjoint : ∀ (i j : Fin c.length),
      j ≠ i → j ≠ cyclicNext c.length c.length_ge_three i →
      Disjoint (range (edgeStrip i)) (range (vertexPiece j)) := by
    intro i j hji hjnext
    rw [Set.disjoint_left]
    rintro q ⟨⟨r,s⟩,he⟩ ⟨p,hp⟩
    have hja : c.vertex i ≠ c.vertex j := fun h => hji (c.vertex_injective h).symm
    have hjb : c.vertex (cyclicNext c.length c.length_ge_three i) ≠ c.vertex j :=
      fun h => hjnext (c.vertex_injective h).symm
    have hv := congrArg (fun a : GeometricRealization V F => a.val (c.vertex j)) (he.trans hp.symm)
    rw [edgeStrip_coordinates,vertexPieceCenter] at hv
    simp only [if_neg hja,if_neg hjb,mul_zero,zero_add] at hv
    have hr := r.property.2
    have hpδ := p.property.2.1
    split_ifs at hv <;> linarith

  have fan_extremes_ne (v : V) (fan : OrderedBoundaryFan F v) :
      fan.vertex 0 ≠ fan.vertex (Fin.last fan.length) := by
    intro he
    have hi := fan.injective he
    have hv := congrArg Fin.val hi
    have hp := fan.positive
    simp only [Fin.val_zero,Fin.val_last] at hv
    omega
  have vertexPieceByCoordinates (i : Fin c.length) (p : TD)
      (q : GeometricRealization V F)
      (hq : q.val (c.vertex i) = 1 - p.val.1)
      (hm : (fanAt i).linkMoment q =
        ((fanAt i).length : ℝ) / 2 * p.val.1 +
          orientation i * (((fanAt i).length : ℝ) / 2 - 1/3) * p.val.2) :
      vertexPiece i p = q := by
    apply WholeFanProof.coordinate_injective (fanAt i)
    · rw [vertexPieceCenter]
      linarith [p.property.2.1]
    · rw [hq]
      linarith [p.property.2.1]
    · rw [vertexPiece_coordinates]
      apply Prod.ext
      · dsimp; rw [hq]; ring
      · exact hm.symm
  have vertexOutgoingPort : ∀ (i : Fin c.length) (r : ↥(Icc (0 : ℝ) (1/8))),
      vertexPiece i ⟨((r : ℝ),(r : ℝ)),
        r.property.1,r.property.2,by linarith [r.property.1],le_rfl⟩ = edgeStrip i (r,0) := by
    intro i r
    apply vertexPieceByCoordinates
    · rw [edgeStrip_coordinates]
      simp [Ne.symm (c.consecutive_vertices_ne i),third_ne_start i]
    · have hext := edgeExtremeMoments (c.vertex i)
        (c.vertex (cyclicNext c.length c.length_ge_three i)) (third i)
        (c.consecutive_vertices_ne i) (third_ne_start i) (third_ne_end i) (fanAt i)
        (incidentExtremeTriangle _ _ _ _ (c.consecutive_vertices_ne i)
          (c.consecutive_edge_mem i) (third_unique i))
        (edgeStrip i) (edgeStrip_coordinates i)
      rcases hext with ⟨hb,hm⟩ | ⟨hb,hm⟩
      · have hlast : (fanAt i).vertex (Fin.last (fanAt i).length) ≠
            c.vertex (cyclicNext c.length c.length_ge_three i) := by
          intro hl
          exact fan_extremes_ne _ (fanAt i) (hb.trans hl.symm)
        have hη : orientation i = -1 := by dsimp [orientation]; rw [if_neg hlast]
        rw [hm,hη]
        ring
      · have hη : orientation i = 1 := by dsimp [orientation]; rw [if_pos hb]
        rw [hm,hη,edgeStrip_coordinates]
        simp [Ne.symm (c.consecutive_vertices_ne i),third_ne_start i] <;> ring
  have incomingOrientation : ∀ i : Fin c.length,
      (orientation (cyclicNext c.length c.length_ge_three i) = 1 ∧
        (fanAt (cyclicNext c.length c.length_ge_three i)).vertex 0 = c.vertex i) ∨
      (orientation (cyclicNext c.length c.length_ge_three i) = -1 ∧
        (fanAt (cyclicNext c.length c.length_ge_three i)).vertex
          (Fin.last (fanAt (cyclicNext c.length c.length_ge_three i)).length) = c.vertex i) := by
    intro i
    let j := cyclicNext c.length c.length_ge_three i
    have hne : c.vertex i ≠ c.vertex (cyclicNext c.length c.length_ge_three j) := by
      intro he
      exact cyclicNext_twice_ne c.length_ge_three i (c.vertex_injective he).symm
    rcases fanOrientation j i rfl with ⟨hf,hl⟩ | ⟨hl,hf⟩
    · left
      exact ⟨by dsimp [orientation]; rw [if_pos hl],hf⟩
    · right
      refine ⟨?_,hl⟩
      have hlast : (fanAt j).vertex (Fin.last (fanAt j).length) ≠
          c.vertex (cyclicNext c.length c.length_ge_three j) := by
        rw [hl]
        exact hne
      dsimp [orientation]
      rw [if_neg hlast]
  have vertexIncomingPort : ∀ (i : Fin c.length) (r : ↥(Icc (0 : ℝ) (1/8))),
      vertexPiece (cyclicNext c.length c.length_ge_three i)
        ⟨((r : ℝ),-(r : ℝ)),r.property.1,r.property.2,le_rfl,by linarith [r.property.1]⟩ =
      edgeStrip i (r,1) := by
    intro i r
    let j := cyclicNext c.length c.length_ge_three i
    have hunique : ∀ τ ∈ F, {c.vertex j,c.vertex i} ⊆ τ →
        τ = {c.vertex j,c.vertex i,third i} := by
      intro τ hτ he
      have ht := third_unique i τ hτ (by simpa only [Finset.pair_comm] using he)
      rw [ht]
      ext w
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    have hext := edgeExtremeMoments (c.vertex j) (c.vertex i) (third i)
      (Ne.symm (c.consecutive_vertices_ne i)) (third_ne_end i) (third_ne_start i) (fanAt j)
      (incidentExtremeTriangle _ _ _ _ (Ne.symm (c.consecutive_vertices_ne i))
        (by simpa only [Finset.pair_comm] using c.consecutive_edge_mem i) hunique)
      (reverseStrip i) (reverse_coordinates i)
    have hrev0 : reverseParameter (0 : Interval) = 1 := by
      apply Subtype.ext; norm_num [reverseParameter]
    have he : reverseStrip i (r,0) = edgeStrip i (r,1) := by
      change edgeStrip i (r,reverseParameter 0) = _
      rw [hrev0]
    rw [← he]
    apply vertexPieceByCoordinates
    · rw [reverse_coordinates]
      simp [j, c.consecutive_vertices_ne i,third_ne_end i]
    · rcases hext with ⟨hb,hm⟩ | ⟨hb,hm⟩
      · have hη : orientation j = 1 := by
          rcases incomingOrientation i with ⟨hη,_⟩ | ⟨hη,hl⟩
          · exact hη
          · exact (fan_extremes_ne _ (fanAt j) (hb.trans hl.symm)).elim
        rw [hm,hη]
        ring
      · have hη : orientation j = -1 := by
          rcases incomingOrientation i with ⟨hη,hf⟩ | ⟨hη,_⟩
          · exact (fan_extremes_ne _ (fanAt j) (hf.trans hb.symm)).elim
          · exact hη
        rw [hm,hη,reverse_coordinates]
        simp [j,c.consecutive_vertices_ne i,third_ne_end i] <;> ring

  have makeEdgePatch {X : Type} [TopologicalSpace X]
      (L R : C(↥{p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1/8 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1},X))
      (E : C(↥(Icc (0 : ℝ) (1/8)) × Interval,X))
      (hL : ∀ r : ↥(Icc (0 : ℝ) (1/8)),
        L ⟨((r : ℝ),(r : ℝ)),r.property.1,r.property.2,by linarith [r.property.1],le_rfl⟩ = E (r,0))
      (hR : ∀ r : ↥(Icc (0 : ℝ) (1/8)),
        R ⟨((r : ℝ),-(r : ℝ)),r.property.1,r.property.2,le_rfl,by linarith [r.property.1]⟩ = E (r,1)) :
      ∃ H : C(Interval × Interval,X),
        (∀ (t s : Interval)
          (p : ↥{p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1/8 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1}),
          p.val = ((t : ℝ)/8,(s : ℝ)) → (s : ℝ) ≤ (t : ℝ)/8 → H (t,s) = L p) ∧
        (∀ (t s : Interval) (r : ↥(Icc (0 : ℝ) (1/8))) (u : Interval),
          (r : ℝ) = (t : ℝ)/8 → (u : ℝ) = ((s : ℝ)-((t : ℝ)/8))/(1-2*((t : ℝ)/8)) →
          (t : ℝ)/8 ≤ (s : ℝ) → (s : ℝ) ≤ 1-(t : ℝ)/8 → H (t,s) = E (r,u)) ∧
        (∀ (t s : Interval)
          (p : ↥{p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1/8 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1}),
          p.val = ((t : ℝ)/8,(s : ℝ)-1) → 1-(t : ℝ)/8 ≤ (s : ℝ) → H (t,s) = R p) := by
    classical
    let TD : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1/8 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1}
    let radius : C(Interval,↥(Icc (0 : ℝ) (1/8))) := ⟨fun t =>
      ⟨(t : ℝ)/8,by constructor <;> linarith [t.property.1,t.property.2]⟩,by
        apply Continuous.subtype_mk
        fun_prop⟩
    have gap : ∀ t : Interval, 0 < 1-2*(radius t : ℝ) := by
      intro t; have := (radius t).property.2; linarith
    let lp : C(Interval × Interval,TD) := ⟨fun p =>
      ⟨((radius p.1 : ℝ),min (p.2 : ℝ) (radius p.1 : ℝ)),
        (radius p.1).property.1,(radius p.1).property.2,
        by have h := le_min p.2.property.1 (radius p.1).property.1
           linarith [(radius p.1).property.1],min_le_right _ _⟩,by
          apply Continuous.subtype_mk
          exact ((continuous_subtype_val.comp (radius.continuous.comp continuous_fst))).prodMk
            (((continuous_subtype_val.comp continuous_snd)).min
              (continuous_subtype_val.comp (radius.continuous.comp continuous_fst)))⟩
    let rp : C(Interval × Interval,TD) := ⟨fun p =>
      ⟨((radius p.1 : ℝ),max ((p.2 : ℝ)-1) (-(radius p.1 : ℝ))),
        (radius p.1).property.1,(radius p.1).property.2,
        le_max_right _ _,max_le (by linarith [p.2.property.2,(radius p.1).property.1])
          (by linarith [(radius p.1).property.1])⟩,by
          apply Continuous.subtype_mk
          fun_prop⟩
    let mp : C(Interval × Interval,↥(Icc (0 : ℝ) (1/8)) × Interval) := ⟨fun p =>
      (radius p.1,⟨max 0 (min 1 (((p.2 : ℝ)-(radius p.1 : ℝ))/(1-2*(radius p.1 : ℝ)))),
        le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩),by
          apply radius.continuous.comp continuous_fst |>.prodMk
          apply Continuous.subtype_mk
          apply continuous_const.max
          apply continuous_const.min
          apply Continuous.div
          · fun_prop
          · fun_prop
          · intro p; exact ne_of_gt (gap p.1)⟩
    let l := L.comp lp
    let r := R.comp rp
    let m := E.comp mp
    have lp_seam : ∀ p : Interval × Interval, (p.2 : ℝ) = (radius p.1 : ℝ) →
        lp p = ⟨((radius p.1 : ℝ),(radius p.1 : ℝ)),
          (radius p.1).property.1,(radius p.1).property.2,
          by linarith [(radius p.1).property.1],le_rfl⟩ := by
      intro p he; apply Subtype.ext
      change ((radius p.1 : ℝ),min (p.2 : ℝ) (radius p.1 : ℝ)) = _
      simp [he]
    have mp_left : ∀ p : Interval × Interval, (p.2 : ℝ) = (radius p.1 : ℝ) →
        mp p = (radius p.1,0) := by
      intro p he; apply Prod.ext
      · rfl
      · apply Subtype.ext
        change max 0 (min 1 (((p.2 : ℝ)-(radius p.1 : ℝ))/(1-2*(radius p.1 : ℝ)))) = 0
        rw [he]; norm_num
    have rp_seam : ∀ p : Interval × Interval, (p.2 : ℝ) = 1-(radius p.1 : ℝ) →
        rp p = ⟨((radius p.1 : ℝ),-(radius p.1 : ℝ)),
          (radius p.1).property.1,(radius p.1).property.2,le_rfl,
          by linarith [(radius p.1).property.1]⟩ := by
      intro p he; apply Subtype.ext
      change ((radius p.1 : ℝ),max ((p.2 : ℝ)-1) (-(radius p.1 : ℝ))) = _
      have hx : (p.2 : ℝ)-1 = -(radius p.1 : ℝ) := by linarith
      simp [hx]
    have mp_right : ∀ p : Interval × Interval, (p.2 : ℝ) = 1-(radius p.1 : ℝ) →
        mp p = (radius p.1,1) := by
      intro p he; apply Prod.ext
      · rfl
      · apply Subtype.ext
        change max 0 (min 1 (((p.2 : ℝ)-(radius p.1 : ℝ))/(1-2*(radius p.1 : ℝ)))) = 1
        have heq : (p.2 : ℝ)-(radius p.1 : ℝ) = 1-2*(radius p.1 : ℝ) := by linarith
        rw [heq,div_self (ne_of_gt (gap p.1))]; norm_num
    have lr_seam : ∀ p : Interval × Interval, (p.2 : ℝ) = (radius p.1 : ℝ) → l p = m p := by
      intro p he
      change L (lp p) = E (mp p)
      rw [lp_seam p he,mp_left p he]
      exact hL (radius p.1)
    have mr_seam : ∀ p : Interval × Interval, (p.2 : ℝ) = 1-(radius p.1 : ℝ) → m p = r p := by
      intro p he
      change E (mp p) = R (rp p)
      rw [rp_seam p he,mp_right p he]
      exact (hR (radius p.1)).symm
    let mr : C(Interval × Interval,X) := ⟨fun p =>
      if (p.2 : ℝ) ≤ 1-(radius p.1 : ℝ) then m p else r p,
      m.continuous.if_le r.continuous (by fun_prop) (by fun_prop) mr_seam⟩
    let H : C(Interval × Interval,X) := ⟨fun p =>
      if (p.2 : ℝ) ≤ (radius p.1 : ℝ) then l p else mr p,
      l.continuous.if_le mr.continuous (by fun_prop) (by fun_prop) (by
        intro p he
        change l p = if (p.2 : ℝ) ≤ 1-(radius p.1 : ℝ) then m p else r p
        rw [if_pos (by have := (radius p.1).property.2; linarith)]
        exact lr_seam p he)⟩
    refine ⟨H,?_,?_,?_⟩
    · intro t s p hp hs
      change (s : ℝ) ≤ (radius t : ℝ) at hs
      have he : lp (t,s) = p := by
        apply Subtype.ext
        rw [hp]
        change ((radius t : ℝ),min (s : ℝ) (radius t : ℝ)) = ((radius t : ℝ),(s : ℝ))
        rw [min_eq_left hs]
      change (if (s : ℝ) ≤ (radius t : ℝ) then l (t,s) else mr (t,s)) = L p
      rw [if_pos hs]
      change L (lp (t,s)) = L p
      rw [he]
    · intro t s rv u hr hu hsL hsR
      change (rv : ℝ) = (radius t : ℝ) at hr
      change (u : ℝ) = ((s : ℝ)-(radius t : ℝ))/(1-2*(radius t : ℝ)) at hu
      change (radius t : ℝ) ≤ (s : ℝ) at hsL
      change (s : ℝ) ≤ 1-(radius t : ℝ) at hsR
      have hm : mp (t,s) = (rv,u) := by
        apply Prod.ext
        · apply Subtype.ext; exact hr.symm
        · apply Subtype.ext
          change max 0 (min 1 (((s : ℝ)-(radius t : ℝ))/(1-2*(radius t : ℝ)))) = (u : ℝ)
          rw [← hu]
          rw [min_eq_right u.property.2,max_eq_right u.property.1]
      by_cases hs : (s : ℝ) ≤ (radius t : ℝ)
      · have he : (s : ℝ) = (radius t : ℝ) := by linarith
        have hE := lr_seam (t,s) he
        change (if (s : ℝ) ≤ (radius t : ℝ) then l (t,s) else mr (t,s)) = _
        rw [if_pos hs,hE]
        change E (mp (t,s)) = E (rv,u)
        rw [hm]
      · change (if (s : ℝ) ≤ (radius t : ℝ) then l (t,s) else
            if (s : ℝ) ≤ 1-(radius t : ℝ) then m (t,s) else r (t,s)) = _
        rw [if_neg hs,if_pos hsR]
        change E (mp (t,s)) = E (rv,u)
        rw [hm]
    · intro t s p hp hsR
      change 1-(radius t : ℝ) ≤ (s : ℝ) at hsR
      have he : rp (t,s) = p := by
        apply Subtype.ext
        rw [hp]
        change ((radius t : ℝ),max ((s : ℝ)-1) (-(radius t : ℝ))) = ((t : ℝ)/8,(s : ℝ)-1)
        rw [max_eq_left (by linarith)]
        rfl
      have hsL : ¬ (s : ℝ) ≤ (radius t : ℝ) := by
        have := (radius t).property.2
        linarith
      change (if (s : ℝ) ≤ (radius t : ℝ) then l (t,s) else
        if (s : ℝ) ≤ 1-(radius t : ℝ) then m (t,s) else r (t,s)) = _
      rw [if_neg hsL]
      by_cases hs : (s : ℝ) ≤ 1-(radius t : ℝ)
      · have hx : (s : ℝ) = 1-(radius t : ℝ) := by linarith
        rw [if_pos hs,mr_seam (t,s) hx]
        change R (rp (t,s)) = R p
        rw [he]
      · rw [if_neg hs]
        change R (rp (t,s)) = R p
        rw [he]

  have hPatches := fun i : Fin c.length => makeEdgePatch
    (vertexPiece i) (vertexPiece (cyclicNext c.length c.length_ge_three i)) (edgeStrip i)
    (vertexOutgoingPort i) (vertexIncomingPort i)
  choose patch patch_left patch_middle patch_right using hPatches
  have patchPieces : ∀ (i : Fin c.length) (t s : Interval),
      (∃ p : TD, p.val.1 = (t : ℝ)/8 ∧ p.val.2 = (s : ℝ) ∧
        (s : ℝ) ≤ (t : ℝ)/8 ∧ patch i (t,s) = vertexPiece i p) ∨
      (∃ (r : ↥(Icc (0 : ℝ) (1/8))) (u : Interval),
        (r : ℝ) = (t : ℝ)/8 ∧
        (u : ℝ) = ((s : ℝ)-(t : ℝ)/8)/(1-2*((t : ℝ)/8)) ∧
        (t : ℝ)/8 ≤ (s : ℝ) ∧ (s : ℝ) ≤ 1-(t : ℝ)/8 ∧
        patch i (t,s) = edgeStrip i (r,u)) ∨
      (∃ p : TD, p.val.1 = (t : ℝ)/8 ∧ p.val.2 = (s : ℝ)-1 ∧
        1-(t : ℝ)/8 ≤ (s : ℝ) ∧
        patch i (t,s) = vertexPiece (cyclicNext c.length c.length_ge_three i) p) := by
    intro i t s
    have hr0 : 0 ≤ (t : ℝ)/8 := by linarith [t.property.1]
    have hrδ : (t : ℝ)/8 ≤ 1/8 := by linarith [t.property.2]
    have hg : 0 < 1-2*((t : ℝ)/8) := by linarith
    by_cases hsL : (s : ℝ) ≤ (t : ℝ)/8
    · left
      let p : TD := ⟨((t : ℝ)/8,(s : ℝ)),hr0,hrδ,
        by linarith [s.property.1],hsL⟩
      exact ⟨p,rfl,rfl,hsL,patch_left i t s p rfl hsL⟩
    · by_cases hsR : (s : ℝ) ≤ 1-(t : ℝ)/8
      · right; left
        let r : ↥(Icc (0 : ℝ) (1/8)) := ⟨(t : ℝ)/8,hr0,hrδ⟩
        let u : Interval := ⟨((s : ℝ)-(t : ℝ)/8)/(1-2*((t : ℝ)/8)),
          div_nonneg (by linarith) hg.le,by
            apply (div_le_iff₀ hg).mpr
            linarith⟩
        exact ⟨r,u,rfl,rfl,by linarith,hsR,
          patch_middle i t s r u rfl rfl (by linarith) hsR⟩
      · right; right
        have hsR' : 1-(t : ℝ)/8 ≤ (s : ℝ) := by linarith
        let p : TD := ⟨((t : ℝ)/8,(s : ℝ)-1),hr0,hrδ,
          by linarith,by linarith [s.property.2]⟩
        exact ⟨p,rfl,rfl,hsR',patch_right i t s p rfl hsR'⟩
  have patchBoundaryExact : ∀ (i : Fin c.length) (t s : Interval),
      patch i (t,s) ∈ boundaryLocus F ↔ t = 0 := by
    intro i t s
    have ht0 : t = 0 ↔ (t : ℝ) = 0 := by
      constructor
      · rintro rfl; rfl
      · exact fun h => Subtype.ext h
    rcases patchPieces i t s with ⟨p,hr,hx,hs,he⟩ |
      ⟨r,u,hr,hu,hsL,hsR,he⟩ | ⟨p,hr,hx,hs,he⟩
    · rw [he,vertexPiece_boundary,hr,ht0]
      constructor <;> intro h <;> linarith
    · rw [he,edgeStrip_boundary,hr,ht0]
      constructor <;> intro h <;> linarith
    · rw [he,vertexPiece_boundary,hr,ht0]
      constructor <;> intro h <;> linarith
  have stripZeroClock : ∀ (i : Fin c.length) (s : Interval),
      edgeStrip i (⟨0,by norm_num,by norm_num⟩,s) = c.circle (edgeClock c.length i s) := by
    intro i s
    apply Subtype.ext
    funext w
    rw [edgeStrip_coordinates,c.circle_clock]
    norm_num
  have patchZeroClock : ∀ (i : Fin c.length) (s : Interval),
      patch i (0,s) = c.circle (edgeClock c.length i s) := by
    intro i s
    let p0 : TD := ⟨(0,0),by norm_num,by norm_num,by norm_num,by norm_num⟩
    rcases patchPieces i 0 s with ⟨p,hr,hx,hs,he⟩ |
      ⟨r,u,hr,hu,hsL,hsR,he⟩ | ⟨p,hr,hx,hs,he⟩
    · have hs0 : s = 0 := by apply Subtype.ext; change (s : ℝ) = 0; norm_num at hs; linarith [s.property.1]
      have hp0 : p = p0 := by
        apply Subtype.ext
        apply Prod.ext
        · change p.val.1 = 0; norm_num at hr; exact hr
        · change p.val.2 = 0; rw [hx,hs0]; rfl
      rw [he,hp0,hs0]
      exact (vertexOutgoingPort i ⟨0,by norm_num,by norm_num⟩).trans (stripZeroClock i 0)
    · have hr0 : r = ⟨0,by norm_num,by norm_num⟩ := by
        apply Subtype.ext; norm_num at hr; exact hr
      have hus : u = s := by apply Subtype.ext; norm_num at hu; exact hu
      rw [he,hr0,hus]
      exact stripZeroClock i s
    · have hs1 : s = 1 := by apply Subtype.ext; change (s : ℝ) = 1; norm_num at hs; linarith [s.property.2]
      have hp0 : p = p0 := by
        apply Subtype.ext
        apply Prod.ext
        · change p.val.1 = 0; norm_num at hr; exact hr
        · change p.val.2 = 0; rw [hx,hs1]; norm_num
      rw [he,hp0,hs1]
      simpa [p0] using (vertexIncomingPort i ⟨0,by norm_num,by norm_num⟩).trans (stripZeroClock i 1)
  have patchWholeSeam : ∀ (i : Fin c.length) (t : Interval),
      patch i (t,1) = patch (cyclicNext c.length c.length_ge_three i) (t,0) := by
    intro i t
    let p : TD := ⟨((t : ℝ)/8,0),by linarith [t.property.1],by linarith [t.property.2],
      by linarith [t.property.1],by linarith [t.property.1]⟩
    have heR := patch_right i t 1 p (by apply Prod.ext <;> norm_num [p])
      (by change 1-(t : ℝ)/8 ≤ 1; linarith [t.property.1])
    have heL := patch_left (cyclicNext c.length c.length_ge_three i) t 0 p rfl
      (by change 0 ≤ (t : ℝ)/8; linarith [t.property.1])
    exact heR.trans heL.symm

  have vertexPiecePatchFiber : ∀ (i : Fin c.length) (t s : Interval)
      (k : Fin c.length) (p : TD), patch i (t,s) = vertexPiece k p →
      (t : ℝ)/8 = p.val.1 ∧
        ((i = k ∧ (s : ℝ) = p.val.2) ∨
          (cyclicNext c.length c.length_ge_three i = k ∧ (s : ℝ) = 1+p.val.2)) := by
    intro i t s k p he
    rcases patchPieces i t s with ⟨p',hr,hx,hs,he'⟩ |
      ⟨r,u,hr,hu,hsL,hsR,he'⟩ | ⟨p',hr,hx,hs,he'⟩
    · have hV : vertexPiece i p' = vertexPiece k p := he'.symm.trans he
      have hik : i = k := by
        by_contra hik
        exact Set.disjoint_left.mp (vertexPieceRangesDisjoint i k hik)
          ⟨p',rfl⟩ ⟨p,hV.symm⟩
      subst k
      have hpp := (vertexPiece_embedded i).injective hV
      subst p'
      exact ⟨hr.symm,Or.inl ⟨rfl,hx.symm⟩⟩
    · have hE : edgeStrip i (r,u) = vertexPiece k p := he'.symm.trans he
      have hg : 0 < 1-2*(r : ℝ) := by linarith [r.property.2]
      have hu' : (u : ℝ) * (1-2*(r : ℝ)) = (s : ℝ)-(r : ℝ) := by
        rw [← hr] at hu
        exact (eq_div_iff (ne_of_gt hg)).mp hu
      by_cases hki : k = i
      · subst k
        have hu0 : u = 0 := (edgeStartVertexIntersection i r u).mp ⟨p,hE.symm⟩
        let p0 : TD := ⟨((r : ℝ),(r : ℝ)),r.property.1,r.property.2,
          by linarith [r.property.1],le_rfl⟩
        have hpp : p0 = p := (vertexPiece_embedded i).injective
          ((vertexOutgoingPort i r).trans (by simpa [hu0] using hE))
        have hpr : p.val.1 = (r : ℝ) := by rw [← hpp]
        have hpx : p.val.2 = (r : ℝ) := by rw [← hpp]
        refine ⟨hr.symm.trans hpr.symm,Or.inl ⟨rfl,?_⟩⟩
        rw [hpx]
        rw [hu0] at hu'
        norm_num at hu'
        linarith
      · by_cases hkn : k = cyclicNext c.length c.length_ge_three i
        · subst k
          have hu1 : u = 1 := (edgeEndVertexIntersection i r u).mp ⟨p,hE.symm⟩
          let p1 : TD := ⟨((r : ℝ),-(r : ℝ)),r.property.1,r.property.2,
            le_rfl,by linarith [r.property.1]⟩
          have hpp : p1 = p := (vertexPiece_embedded (cyclicNext c.length c.length_ge_three i)).injective
            ((vertexIncomingPort i r).trans (by simpa [hu1] using hE))
          have hpr : p.val.1 = (r : ℝ) := by rw [← hpp]
          have hpx : p.val.2 = -(r : ℝ) := by rw [← hpp]
          refine ⟨hr.symm.trans hpr.symm,Or.inr ⟨rfl,?_⟩⟩
          rw [hpx]
          rw [hu1] at hu'
          norm_num at hu'
          linarith
        · exact (Set.disjoint_left.mp (edgeOtherVertexDisjoint i k hki hkn)
            ⟨(r,u),rfl⟩ ⟨p,hE.symm⟩).elim
    · have hV : vertexPiece (cyclicNext c.length c.length_ge_three i) p' = vertexPiece k p :=
        he'.symm.trans he
      have hik : cyclicNext c.length c.length_ge_three i = k := by
        by_contra hik
        exact Set.disjoint_left.mp
          (vertexPieceRangesDisjoint (cyclicNext c.length c.length_ge_three i) k hik)
          ⟨p',rfl⟩ ⟨p,hV.symm⟩
      subst k
      have hpp := (vertexPiece_embedded (cyclicNext c.length c.length_ge_three i)).injective hV
      subst p'
      refine ⟨hr.symm,Or.inr ⟨rfl,?_⟩⟩
      linarith
  have vertexPiecePatchCollision : ∀ (i j : Fin c.length) (t s t' s' : Interval)
      (k : Fin c.length) (p : TD),
      patch i (t,s) = vertexPiece k p → patch j (t',s') = vertexPiece k p →
      t = t' ∧ edgeClock c.length i s = edgeClock c.length j s' := by
    intro i j t s t' s' k p he he'
    obtain ⟨hr,hi⟩ := vertexPiecePatchFiber i t s k p he
    obtain ⟨hr',hj⟩ := vertexPiecePatchFiber j t' s' k p he'
    have ht : t = t' := by apply Subtype.ext; linarith
    refine ⟨ht,?_⟩
    rcases hi with ⟨hi,hs⟩ | ⟨hi,hs⟩ <;> rcases hj with ⟨hj,hs'⟩ | ⟨hj,hs'⟩
    · have hij : i = j := hi.trans hj.symm
      have hss : s = s' := by apply Subtype.ext; linarith
      rw [hij,hss]
    · have hs0 : s = 0 := by apply Subtype.ext; change (s : ℝ) = 0; linarith [s.property.1,s'.property.2]
      have hs1 : s' = 1 := by apply Subtype.ext; change (s' : ℝ) = 1; linarith [s.property.1,s'.property.2]
      rw [hs0,hs1,hi,hj.symm]
      exact (edgeClock_whole_seam c.length_ge_three j).symm
    · have hs1 : s = 1 := by apply Subtype.ext; change (s : ℝ) = 1; linarith [s.property.2,s'.property.1]
      have hs0 : s' = 0 := by apply Subtype.ext; change (s' : ℝ) = 0; linarith [s.property.2,s'.property.1]
      rw [hs1,hs0,hj,hi.symm]
      exact edgeClock_whole_seam c.length_ge_three i
    · have hij : i = j := successor_bijection.1 (hi.trans hj.symm)
      have hss : s = s' := by apply Subtype.ext; linarith
      rw [hij,hss]
  obtain ⟨preBand,preBand_clock,preBand_unique⟩ :=
    descendClock c.length c.length_ge_three patch patchWholeSeam
  have preBandZeroClock : ∀ z, preBand (0,z) = c.circle z := by
    intro z
    obtain ⟨i,s,hs,he⟩ := edgeClock_cover c.length_ge_three z
    rw [← he,preBand_clock,patchZeroClock]
  have preBandBoundaryExact : ∀ (t : Interval) z,
      preBand (t,z) ∈ boundaryLocus F ↔ t = 0 := by
    intro t z
    obtain ⟨i,s,hs,he⟩ := edgeClock_cover c.length_ge_three z
    rw [← he,preBand_clock,patchBoundaryExact]

  have patchExactCollision : ∀ (i j : Fin c.length) (t s t' s' : Interval),
      patch i (t,s) = patch j (t',s') ↔
        t = t' ∧ edgeClock c.length i s = edgeClock c.length j s' := by
    intro i j t s t' s'
    constructor
    · intro he
      rcases patchPieces i t s with ⟨p,hr,hx,hs,heI⟩ |
        ⟨r,u,hr,hu,hsL,hsR,heI⟩ | ⟨p,hr,hx,hs,heI⟩
      · exact vertexPiecePatchCollision i j t s t' s' i p heI (he.symm.trans heI)
      · rcases patchPieces j t' s' with ⟨p',hr',hx',hs',heJ⟩ |
          ⟨r',u',hr',hu',hsL',hsR',heJ⟩ | ⟨p',hr',hx',hs',heJ⟩
        · have hc := vertexPiecePatchCollision j i t' s' t s j p' heJ (he.trans heJ)
          exact ⟨hc.1.symm,hc.2.symm⟩
        · have hE : edgeStrip i (r,u) = edgeStrip j (r',u') := heI.symm.trans (he.trans heJ)
          by_cases hij : i = j
          · subst j
            have hp := (edgeStrip_embedded i).injective hE
            have hrr : r = r' := congrArg Prod.fst hp
            have huu : u = u' := congrArg Prod.snd hp
            have ht : t = t' := by
              apply Subtype.ext
              have hrval := congrArg (fun a : ↥(Icc (0 : ℝ) (1/8)) => (a : ℝ)) hrr
              linarith
            have hs : s = s' := by
              apply Subtype.ext
              have hg : 1-2*((t : ℝ)/8) ≠ 0 := by linarith [t.property.2]
              rw [← huu,← ht] at hu'
              have hd := hu.symm.trans hu'
              have hn := (div_left_inj' hg).mp hd
              linarith
            rw [ht,hs]
            exact ⟨rfl,rfl⟩
          · have hz := distinctStripCollisionHeight i j hij r r' u u' hE
            have ht0 : t = 0 := by apply Subtype.ext; change (t : ℝ) = 0; linarith [hz.1]
            have ht'0 : t' = 0 := by apply Subtype.ext; change (t' : ℝ) = 0; linarith [hz.2]
            rw [ht0,ht'0,patchZeroClock,patchZeroClock] at he
            exact ⟨ht0.trans ht'0.symm,c.circle_injective he⟩
        · have hc := vertexPiecePatchCollision j i t' s' t s
            (cyclicNext c.length c.length_ge_three j) p' heJ (he.trans heJ)
          exact ⟨hc.1.symm,hc.2.symm⟩
      · exact vertexPiecePatchCollision i j t s t' s'
          (cyclicNext c.length c.length_ge_three i) p heI (he.symm.trans heI)
    · rintro ⟨rfl,he⟩
      rw [← preBand_clock,← preBand_clock,he]
  have preBandEmbedding : IsEmbedding preBand := by
    have hinj : Function.Injective preBand := by
      intro p q he
      obtain ⟨i,s,hs,hi⟩ := edgeClock_cover c.length_ge_three p.2
      obtain ⟨j,s',hs',hj⟩ := edgeClock_cover c.length_ge_three q.2
      change preBand (p.1,p.2) = preBand (q.1,q.2) at he
      rw [← hi,← hj,preBand_clock,preBand_clock] at he
      have hc := (patchExactCollision i j p.1 s q.1 s').mp he
      exact Prod.ext hc.1 (hi.symm.trans (hc.2.trans hj))
    exact (preBand.continuous.isClosedEmbedding hinj).isEmbedding

  obtain ⟨d,hd0,hd1,hUniform⟩ := c.uniform_neighborhood_height
    preBand preBandZeroClock U hU hcontains
  let scaleHeight : C(Interval × Circle,Interval × Circle) := ⟨fun p =>
    (⟨d * (p.1 : ℝ),by
      constructor
      · exact mul_nonneg hd0.le p.1.property.1
      · nlinarith [p.1.property.1,p.1.property.2]⟩,p.2),by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          fun_prop
        · exact continuous_snd⟩
  have scaleHeightEmbedding : IsEmbedding scaleHeight := by
    have hinj : Function.Injective scaleHeight := by
      intro p q he
      have ht := congrArg (fun a : Interval × Circle => (a.1 : ℝ)) he
      have hz := congrArg (fun a : Interval × Circle => a.2) he
      change d * (p.1 : ℝ) = d * (q.1 : ℝ) at ht
      have ht' : p.1 = q.1 := Subtype.ext (mul_left_cancel₀ (ne_of_gt hd0) ht)
      exact Prod.ext ht' hz
    exact (scaleHeight.continuous.isClosedEmbedding hinj).isEmbedding
  let G : C(Interval × Circle,GeometricRealization V F) := preBand.comp scaleHeight
  have GEmbedding : IsEmbedding G := preBandEmbedding.comp scaleHeightEmbedding
  have GZeroClock : ∀ z, G (0,z) = c.circle z := by
    intro z
    have he : scaleHeight (0,z) = (0,z) := by
      apply Prod.ext
      · apply Subtype.ext; change d * 0 = 0; ring
      · rfl
    change preBand (scaleHeight (0,z)) = _
    rw [he,preBandZeroClock]
  have GSupported : range G ⊆ U := by
    rintro q ⟨⟨t,z⟩,rfl⟩
    apply hUniform (scaleHeight (t,z)).1 z
    change d * (t : ℝ) ≤ d
    nlinarith [t.property.2]
  have GBoundaryExact : ∀ (t : Interval) z,
      G (t,z) ∈ boundaryLocus F ↔ t = 0 := by
    intro t z
    change preBand ((scaleHeight (t,z)).1,z) ∈ boundaryLocus F ↔ t = 0
    rw [preBandBoundaryExact]
    constructor
    · intro he
      apply Subtype.ext
      have ht := congrArg (fun a : Interval => (a : ℝ)) he
      change d * (t : ℝ) = 0 at ht
      change (t : ℝ) = 0
      exact (mul_eq_zero.mp ht).resolve_left (ne_of_gt hd0)
    · rintro rfl
      apply Subtype.ext
      change d * 0 = 0
      ring

  let positiveG : Ioo (0 : ℝ) 1 × Circle → GeometricRealization V F := fun p =>
    G (⟨p.1.val,p.1.property.1.le,p.1.property.2.le⟩,p.2)
  have positiveGEmbedding : IsEmbedding positiveG := by
    have hp : IsEmbedding (fun t : Ioo (0 : ℝ) 1 =>
        (⟨t.val,t.property.1.le,t.property.2.le⟩ : Interval)) := by
      have hc : IsEmbedding ((↑) : ↥(Ioo (0 : ℝ) 1) → ℝ) := IsEmbedding.subtypeVal
      exact hc.codRestrict Interval (fun t => ⟨t.property.1.le,t.property.2.le⟩)
    exact GEmbedding.comp (hp.prodMap IsEmbedding.id)
  have positiveVertexRange : ∀ (i : Fin c.length) (p : TD),
      0 < p.val.1 → p.val.1 < d/8 → vertexPiece i p ∈ range positiveG := by
    intro i p hr0 hrcap
    let t : Ioo (0 : ℝ) 1 := ⟨8*p.val.1/d,by
      constructor
      · exact div_pos (by linarith) hd0
      · apply (div_lt_iff₀ hd0).mpr; linarith⟩
    let tpre : Interval := ⟨8*p.val.1,by constructor <;> linarith⟩
    have scale_eq : ∀ z, scaleHeight (⟨t.val,t.property.1.le,t.property.2.le⟩,z) = (tpre,z) := by
      intro z; apply Prod.ext
      · apply Subtype.ext
        change d*(8*p.val.1/d) = 8*p.val.1
        field_simp [ne_of_gt hd0]
      · rfl
    by_cases hx : 0 ≤ p.val.2
    · let s : Interval := ⟨p.val.2,hx,by linarith [p.property.2.1,p.property.2.2.2]⟩
      have hpair : p.val = ((tpre : ℝ)/8,(s : ℝ)) := by
        apply Prod.ext
        · change p.val.1 = 8*p.val.1/8; ring
        · rfl
      have hpatch := patch_left i tpre s p hpair (by
        change p.val.2 ≤ 8*p.val.1/8
        linarith [p.property.2.2.2])
      refine ⟨(t,edgeClock c.length i s),?_⟩
      change preBand (scaleHeight (⟨t.val,t.property.1.le,t.property.2.le⟩,_)) = _
      rw [scale_eq,preBand_clock]
      exact hpatch
    · obtain ⟨j,hj⟩ := successor_bijection.2 i
      let s : Interval := ⟨1+p.val.2,by linarith [p.property.2.1,p.property.2.2.1],by linarith⟩
      have hpair : p.val = ((tpre : ℝ)/8,(s : ℝ)-1) := by
        apply Prod.ext
        · change p.val.1 = 8*p.val.1/8; ring
        · change p.val.2 = 1+p.val.2-1; ring
      have hs : 1-(tpre : ℝ)/8 ≤ (s : ℝ) := by
        change 1-8*p.val.1/8 ≤ 1+p.val.2
        linarith [p.property.2.2.1]
      have hpatch := patch_right j tpre s p hpair hs
      rw [hj] at hpatch
      refine ⟨(t,edgeClock c.length j s),?_⟩
      change preBand (scaleHeight (⟨t.val,t.property.1.le,t.property.2.le⟩,_)) = _
      rw [scale_eq,preBand_clock]
      exact hpatch
  have positiveStripRange : ∀ (i : Fin c.length)
      (r : ↥(Icc (0 : ℝ) (1/8))) (u : Interval),
      0 < (r : ℝ) → (r : ℝ) < d/8 → edgeStrip i (r,u) ∈ range positiveG := by
    intro i r u hr0 hrcap
    let t : Ioo (0 : ℝ) 1 := ⟨8*(r : ℝ)/d,by
      constructor
      · exact div_pos (by linarith) hd0
      · apply (div_lt_iff₀ hd0).mpr; linarith⟩
    let tpre : Interval := ⟨8*(r : ℝ),by constructor <;> linarith⟩
    have hg : 0 < 1-2*(r : ℝ) := by linarith [r.property.2]
    have hm0 : 0 ≤ (u : ℝ)*(1-2*(r : ℝ)) := mul_nonneg u.property.1 hg.le
    have hm1 : (u : ℝ)*(1-2*(r : ℝ)) ≤ 1-2*(r : ℝ) := by nlinarith [u.property.2]
    let s : Interval := ⟨(r : ℝ)+(1-2*(r : ℝ))*(u : ℝ),by constructor <;> nlinarith [r.property.1]⟩
    have hnorm : (u : ℝ) = ((s : ℝ)-(tpre : ℝ)/8)/(1-2*((tpre : ℝ)/8)) := by
      change (u : ℝ) = ((r : ℝ)+(1-2*(r : ℝ))*(u : ℝ)-8*(r : ℝ)/8)/(1-2*(8*(r : ℝ)/8))
      have h8 : 8*(r : ℝ)/8 = (r : ℝ) := by ring
      simp only [h8]
      apply (eq_div_iff (ne_of_gt hg)).mpr
      ring
    have hsL : (tpre : ℝ)/8 ≤ (s : ℝ) := by change 8*(r : ℝ)/8 ≤ _; dsimp [s]; nlinarith
    have hsR : (s : ℝ) ≤ 1-(tpre : ℝ)/8 := by change (r : ℝ)+(1-2*(r : ℝ))*(u : ℝ) ≤ _; dsimp [tpre]; nlinarith
    have hpatch := patch_middle i tpre s r u (by change (r : ℝ) = 8*(r : ℝ)/8; ring) hnorm hsL hsR
    have scale_eq : scaleHeight (⟨t.val,t.property.1.le,t.property.2.le⟩,edgeClock c.length i s) =
        (tpre,edgeClock c.length i s) := by
      apply Prod.ext
      · apply Subtype.ext
        change d*(8*(r : ℝ)/d) = 8*(r : ℝ)
        field_simp [ne_of_gt hd0]
      · rfl
    refine ⟨(t,edgeClock c.length i s),?_⟩
    change preBand (scaleHeight (⟨t.val,t.property.1.le,t.property.2.le⟩,_)) = _
    rw [scale_eq,preBand_clock]
    exact hpatch
  have positiveCarrier : ∀ q : GeometricRealization V F, q ∈ range positiveG ↔
      (∃ (i : Fin c.length) (p : TD), 0 < p.val.1 ∧ p.val.1 < d/8 ∧ vertexPiece i p = q) ∨
      (∃ (i : Fin c.length) (r : ↥(Icc (0 : ℝ) (1/8))) (u : Interval),
        0 < (r : ℝ) ∧ (r : ℝ) < d/8 ∧ edgeStrip i (r,u) = q) := by
    intro q
    constructor
    · rintro ⟨⟨t,z⟩,rfl⟩
      obtain ⟨i,s,hs,he⟩ := edgeClock_cover c.length_ge_three z
      let tpre := (scaleHeight (⟨t.val,t.property.1.le,t.property.2.le⟩,z)).1
      have hval : (tpre : ℝ) = d*t.val := rfl
      have hr0 : 0 < (tpre : ℝ)/8 := by rw [hval]; exact div_pos (mul_pos hd0 t.property.1) (by norm_num)
      have hrcap : (tpre : ℝ)/8 < d/8 := by rw [hval]; nlinarith [t.property.2]
      have hq : positiveG (t,z) = patch i (tpre,s) := by
        change preBand (tpre,z) = _
        rw [← he,preBand_clock]
      rcases patchPieces i tpre s with ⟨p,hr,hx,hs,hep⟩ |
        ⟨r,u,hr,hu,hsL,hsR,hep⟩ | ⟨p,hr,hx,hs,hep⟩
      · left; exact ⟨i,p,by rwa [hr],by rwa [hr],hep.symm.trans hq.symm⟩
      · right; exact ⟨i,r,u,by rwa [hr],by rwa [hr],hep.symm.trans hq.symm⟩
      · left; exact ⟨cyclicNext c.length c.length_ge_three i,p,by rwa [hr],by rwa [hr],hep.symm.trans hq.symm⟩
    · rintro (⟨i,p,h0,hcap,rfl⟩ | ⟨i,r,u,h0,hcap,rfl⟩)
      · exact positiveVertexRange i p h0 hcap
      · exact positiveStripRange i r u h0 hcap

  have positiveVertexCriterion (i : Fin c.length) (q : GeometricRealization V F)
      (hr0 : 0 < 1-q.val (c.vertex i)) (hrcap : 1-q.val (c.vertex i) < d/8)
      (hL : (1-q.val (c.vertex i))/3 ≤ (fanAt i).linkMoment q)
      (hR : (fanAt i).linkMoment q ≤ (((fanAt i).length : ℝ)-1/3)*(1-q.val (c.vertex i))) :
      q ∈ range positiveG := by
    have hq := (vertexPiece_range i q).mpr ⟨hr0.le,by linarith,hL,hR⟩
    obtain ⟨p,hp⟩ := hq
    have hr : p.val.1 = 1-q.val (c.vertex i) := by
      have hc := vertexPieceCenter i p
      rw [hp] at hc
      linarith
    rw [← hp]
    exact positiveVertexRange i p (by rwa [hr]) (by rwa [hr])
  have positiveEdgeCriterion (i : Fin c.length) (q : GeometricRealization V F)
      (hface : q.val ∈ GeometricFace V
        {c.vertex i,c.vertex (cyclicNext c.length c.length_ge_three i),third i})
      (hz0 : 0 < 3*q.val (third i)) (hzcap : 3*q.val (third i) < d/8)
      (ha : 2*q.val (third i) ≤ q.val (c.vertex i))
      (hb : 2*q.val (third i) ≤ q.val (c.vertex (cyclicNext c.length c.length_ge_three i))) :
      q ∈ range positiveG := by
    obtain ⟨⟨r,u⟩,hp⟩ := (edgeStrip_range i q).mpr ⟨hface,hz0.le,by linarith,ha,hb⟩
    have hr : (r : ℝ) = 3*q.val (third i) := by
      have hc := edgeThirdCoordinate i r u
      rw [hp] at hc
      linarith
    rw [← hp]
    exact positiveStripRange i r u (by rwa [hr]) (by rwa [hr])

  have triangleInteriorFacts (a b z : V) (hab : a ≠ b) (hza : z ≠ a) (hzb : z ≠ b) :
      (∀ q : GeometricRealization V F,
        0 < q.val a → 0 < q.val b → 0 < q.val z → q.val ∈ GeometricFace V {a,b,z}) ∧
      (∀ q : GeometricRealization V F, q.val ∈ GeometricFace V {a,b,z} →
        q.val a + q.val b + q.val z = 1) := by
    classical
    constructor
    · intro q ha hb hz
      obtain ⟨τ,hτ,hqτ⟩ := q.property.2
      have haτ : a ∈ τ := by by_contra h; have := hqτ a h; linarith
      have hbτ : b ∈ τ := by by_contra h; have := hqτ b h; linarith
      have hzτ : z ∈ τ := by by_contra h; have := hqτ z h; linarith
      have hsub : ({a,b,z} : Finset V) ⊆ τ := by
        intro w hw
        simp only [Finset.mem_insert,Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      have he : ({a,b,z} : Finset V) = τ := by
        apply Finset.eq_of_subset_of_card_le hsub
        simp [hab,Ne.symm hza,Ne.symm hzb,hfaces τ hτ]
      exact ⟨q.property.1,by simpa only [he] using hqτ⟩
    · intro q hq
      have hs := Finset.sum_subset (Finset.subset_univ ({a,b,z} : Finset V))
        (fun w _ hw => hq.2 w hw)
      simpa [hab,hza,hzb,Ne.symm hza,Ne.symm hzb,q.property.1.2,add_assoc] using hs

  have portNeighborhood (a b z : V) (hab : a ≠ b) (hza : z ≠ a) (hzb : z ≠ b)
      (fan : OrderedBoundaryFan F a)
      (hext : (fan.vertex 0 = b ∧ fan.vertex ⟨1,by have := fan.positive; omega⟩ = z) ∨
        (fan.vertex (Fin.last fan.length) = b ∧ fan.vertex ⟨fan.length-1,by omega⟩ = z))
      (cap : ℝ) (hcap : 0 < cap) (hcapδ : cap ≤ 1/8) :
      ∃ P : Set (GeometricRealization V F), IsOpen P ∧
        (∀ q ∈ P,
          (0 < 1-q.val a ∧ 1-q.val a < cap ∧
            (1-q.val a)/3 ≤ fan.linkMoment q ∧
            fan.linkMoment q ≤ ((fan.length : ℝ)-1/3)*(1-q.val a)) ∨
          (q.val ∈ GeometricFace V {a,b,z} ∧ 0 < 3*q.val z ∧ 3*q.val z < cap ∧
            2*q.val z ≤ q.val a ∧ 2*q.val z ≤ q.val b)) ∧
        (∀ (r : ℝ), 0 < r → r < cap → ∀ q : GeometricRealization V F,
          (∀ w, q.val w = (1-r)*(if a=w then 1 else 0) +
            (2*r/3)*(if b=w then 1 else 0) + (r/3)*(if z=w then 1 else 0)) → q ∈ P) := by
    have faceExtremeMoments (a b z : V) (fan : OrderedBoundaryFan F a)
        (hext : (fan.vertex 0 = b ∧ fan.vertex ⟨1,by have := fan.positive; omega⟩ = z) ∨
          (fan.vertex (Fin.last fan.length) = b ∧ fan.vertex ⟨fan.length-1,by omega⟩ = z)) :
        (fan.vertex 0 = b ∧ ∀ q : GeometricRealization V F,
          q.val ∈ GeometricFace V {a,b,z} → fan.linkMoment q = q.val z) ∨
        (fan.vertex (Fin.last fan.length) = b ∧ ∀ q : GeometricRealization V F,
          q.val ∈ GeometricFace V {a,b,z} →
          fan.linkMoment q = (fan.length : ℝ) * (1 - q.val a) - q.val z) := by
      classical
      rcases hext with ⟨hb,hzv⟩ | ⟨hb,hzv⟩
      · left
        refine ⟨hb,?_⟩
        intro q hface
        let i : Fin fan.length := ⟨0,fan.positive⟩
        have hi0 : i.castSucc = 0 := by apply Fin.ext; rfl
        have hi1 : i.succ = ⟨1,by have := fan.positive; omega⟩ := by apply Fin.ext; rfl
        have hqface : q.val ∈ GeometricFace V {a,fan.vertex i.castSucc,fan.vertex i.succ} := by
          simpa only [hi0,hi1,hb,hzv] using hface
        obtain ⟨ρ,θ,hq⟩ := WholeFanProof.point_of_face fan i q hqface
        have hqz : q.val z = (ρ : ℝ) * (θ : ℝ) := by
          rw [hq,← hzv,← hi1,fan.trianglePoint_next]
        rw [hq,fan.trianglePoint_linkMoment]
        simp only [i,Nat.cast_zero,zero_add]
        simpa only [hq,i] using hqz.symm
      · right
        refine ⟨hb,?_⟩
        intro q hface
        let i : Fin fan.length := ⟨fan.length-1,by have := fan.positive; omega⟩
        have hi0 : i.castSucc = ⟨fan.length-1,by omega⟩ := by apply Fin.ext; rfl
        have hi1 : i.succ = Fin.last fan.length := by apply Fin.ext; dsimp [i]; have := fan.positive; omega
        have hqface : q.val ∈ GeometricFace V {a,fan.vertex i.castSucc,fan.vertex i.succ} := by
          have ht : ({a,z,b} : Finset V) = {a,b,z} := by
            ext w; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
          rw [hi0,hi1,hb,hzv,ht]
          exact hface
        obtain ⟨ρ,θ,hq⟩ := WholeFanProof.point_of_face fan i q hqface
        have hqz : q.val z = (ρ : ℝ) * (1 - (θ : ℝ)) := by
          rw [hq,← hzv,← hi0,fan.trianglePoint_start]
        have hqn : q.val a = 1 - (ρ : ℝ) := by rw [hq,fan.trianglePoint_center]
        have hidx : (i.val : ℝ) + 1 = (fan.length : ℝ) := by
          have hi : i.val + 1 = fan.length := by dsimp [i]; have := fan.positive; omega
          exact_mod_cast hi
        rw [hq,fan.trianglePoint_linkMoment,← hq,hqn]
        calc
          (ρ : ℝ) * ((i.val : ℝ) + (θ : ℝ)) =
              ((i.val : ℝ) + 1) * (ρ : ℝ) - (ρ : ℝ) * (1 - (θ : ℝ)) := by ring
          _ = (fan.length : ℝ) * (ρ : ℝ) - q.val z := by rw [hidx,← hqz]
          _ = _ := by ring
    have triangleFacts :
      (∀ q : GeometricRealization V F,
        0 < q.val a → 0 < q.val b → 0 < q.val z → q.val ∈ GeometricFace V {a,b,z}) ∧
      (∀ q : GeometricRealization V F, q.val ∈ GeometricFace V {a,b,z} →
        q.val a + q.val b + q.val z = 1) := by
      classical
      constructor
      · intro q ha hb hz
        obtain ⟨τ,hτ,hqτ⟩ := q.property.2
        have haτ : a ∈ τ := by by_contra h; have := hqτ a h; linarith
        have hbτ : b ∈ τ := by by_contra h; have := hqτ b h; linarith
        have hzτ : z ∈ τ := by by_contra h; have := hqτ z h; linarith
        have hsub : ({a,b,z} : Finset V) ⊆ τ := by
          intro w hw
          simp only [Finset.mem_insert,Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl <;> assumption
        have he : ({a,b,z} : Finset V) = τ := by
          apply Finset.eq_of_subset_of_card_le hsub
          simp [hab,Ne.symm hza,Ne.symm hzb,hfaces τ hτ]
        exact ⟨q.property.1,by simpa only [he] using hqτ⟩
      · intro q hq
        have hs := Finset.sum_subset (Finset.subset_univ ({a,b,z} : Finset V))
          (fun w _ hw => hq.2 w hw)
        simpa [hab,hza,hzb,Ne.symm hza,Ne.symm hzb,q.property.1.2,add_assoc] using hs
    let P : Set (GeometricRealization V F) := {q |
      2*q.val z < q.val a ∧ 0 < q.val b ∧ 0 < q.val z ∧
        1-q.val a < cap ∧ 3*q.val z < cap ∧
        q.val z < ((fan.length : ℝ)-1/3)*(1-q.val a)}
    have hP : IsOpen P := by
      have hc (w : V) : Continuous (fun q : GeometricRealization V F => q.val w) :=
        (continuous_apply w).comp continuous_subtype_val
      have h2z : Continuous (fun q : GeometricRealization V F => 2*q.val z) := continuous_const.mul (hc z)
      have ha : Continuous (fun q : GeometricRealization V F => q.val a) := hc a
      have hb : Continuous (fun q : GeometricRealization V F => q.val b) := hc b
      have hz : Continuous (fun q : GeometricRealization V F => q.val z) := hc z
      have hr : Continuous (fun q : GeometricRealization V F => 1-q.val a) := continuous_const.sub ha
      have h3z : Continuous (fun q : GeometricRealization V F => 3*q.val z) := continuous_const.mul hz
      have hu : Continuous (fun q : GeometricRealization V F => ((fan.length : ℝ)-1/3)*(1-q.val a)) := continuous_const.mul hr
      exact (isOpen_lt h2z ha).inter ((isOpen_lt continuous_const hb).inter
        ((isOpen_lt continuous_const hz).inter ((isOpen_lt hr continuous_const).inter
          ((isOpen_lt h3z continuous_const).inter (isOpen_lt hz hu)))))

    have hn : (1 : ℝ) ≤ (fan.length : ℝ) := by exact_mod_cast fan.positive
    refine ⟨P,hP,?_,?_⟩
    · intro q hq
      rcases hq with ⟨ha,hb,hz,hr,hzcap,hupper⟩
      have hqa : 0 < q.val a := by linarith
      have hface := triangleFacts.1 q hqa hb hz
      have hsum := triangleFacts.2 q hface
      have hr0 : 0 < 1-q.val a := by linarith
      by_cases hlower : (1-q.val a)/3 ≤ q.val z
      · left
        refine ⟨hr0,hr,?_,?_⟩
        rcases faceExtremeMoments a b z fan hext with ⟨_,hm⟩ | ⟨_,hm⟩
        · rw [hm q hface]
          exact hlower
        · rw [hm q hface]
          nlinarith
        · rcases faceExtremeMoments a b z fan hext with ⟨_,hm⟩ | ⟨_,hm⟩
          · rw [hm q hface]
            exact hupper.le
          · rw [hm q hface]
            nlinarith
      · right
        exact ⟨hface,by linarith,hzcap,ha.le,by linarith⟩
    · intro r hr hrcap q hcoords
      have hrδ : r ≤ 1/8 := hrcap.le.trans hcapδ
      have hqa : q.val a = 1-r := by rw [hcoords]; simp [Ne.symm hab,hza]
      have hqb : q.val b = 2*r/3 := by rw [hcoords]; simp [hab,hzb]
      have hqz : q.val z = r/3 := by rw [hcoords]; simp [Ne.symm hza,Ne.symm hzb]
      change 2*q.val z < q.val a ∧ 0 < q.val b ∧ 0 < q.val z ∧
        1-q.val a < cap ∧ 3*q.val z < cap ∧ q.val z < ((fan.length : ℝ)-1/3)*(1-q.val a)
      rw [hqa,hqb,hqz]
      refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,?_⟩
      nlinarith

  have startPortOpenNeighborhood : ∀ (i : Fin c.length)
      (r : ↥(Icc (0 : ℝ) (1/8))), 0 < (r : ℝ) → (r : ℝ) < d/8 →
      ∃ P : Set (GeometricRealization V F), P ⊆ range positiveG ∧ IsOpen P ∧ edgeStrip i (r,0) ∈ P := by
    intro i r hr0 hrcap
    have hext := incidentExtremeTriangle _ _ _ (fanAt i) (c.consecutive_vertices_ne i)
      (c.consecutive_edge_mem i) (third_unique i)
    obtain ⟨P,hP,hcriteria,hport⟩ := portNeighborhood
      (c.vertex i) (c.vertex (cyclicNext c.length c.length_ge_three i)) (third i)
      (c.consecutive_vertices_ne i) (third_ne_start i) (third_ne_end i) (fanAt i) hext
      (d/8) (by linarith) (by linarith)
    refine ⟨P,?_,hP,?_⟩
    · intro q hq
      rcases hcriteria q hq with ⟨h0,hcap,hL,hR⟩ | ⟨hf,h0,hcap,ha,hb⟩
      · exact positiveVertexCriterion i q h0 hcap hL hR
      · exact positiveEdgeCriterion i q hf h0 hcap ha hb
    · apply hport (r : ℝ) hr0 hrcap (edgeStrip i (r,0))
      intro w
      simpa using edgeStrip_coordinates i r 0 w
  have endPortOpenNeighborhood : ∀ (i : Fin c.length)
      (r : ↥(Icc (0 : ℝ) (1/8))), 0 < (r : ℝ) → (r : ℝ) < d/8 →
      ∃ P : Set (GeometricRealization V F), P ⊆ range positiveG ∧ IsOpen P ∧ edgeStrip i (r,1) ∈ P := by
    intro i r hr0 hrcap
    let j := cyclicNext c.length c.length_ge_three i
    have ht : ({c.vertex j,c.vertex i,third i} : Finset V) =
        {c.vertex i,c.vertex j,third i} := by
      ext w; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
    have hunique : ∀ τ ∈ F, {c.vertex j,c.vertex i} ⊆ τ →
        τ = {c.vertex j,c.vertex i,third i} := by
      intro τ hτ he
      have h := third_unique i τ hτ (by simpa only [Finset.pair_comm] using he)
      rw [ht]
      exact h
    have hext := incidentExtremeTriangle _ _ _ (fanAt j) (Ne.symm (c.consecutive_vertices_ne i))
      (by simpa only [Finset.pair_comm] using c.consecutive_edge_mem i) hunique
    obtain ⟨P,hP,hcriteria,hport⟩ := portNeighborhood
      (c.vertex j) (c.vertex i) (third i)
      (Ne.symm (c.consecutive_vertices_ne i)) (third_ne_end i) (third_ne_start i) (fanAt j) hext
      (d/8) (by linarith) (by linarith)
    refine ⟨P,?_,hP,?_⟩
    · intro q hq
      rcases hcriteria q hq with ⟨h0,hcap,hL,hR⟩ | ⟨hf,h0,hcap,ha,hb⟩
      · exact positiveVertexCriterion j q h0 hcap hL hR
      · rw [ht] at hf
        exact positiveEdgeCriterion i q hf h0 hcap hb ha
    · apply hport (r : ℝ) hr0 hrcap (edgeStrip i (r,1))
      intro w
      have hrev : reverseStrip i (r,0) = edgeStrip i (r,1) := by
        have h0 : reverseParameter (0 : Interval) = 1 := by
          apply Subtype.ext
          change 1-(0 : ℝ) = 1
          norm_num
        change edgeStrip i (r,reverseParameter 0) = _
        rw [h0]
      rw [← hrev]
      simpa using reverse_coordinates i r 0 w

  have vertexStrictOpenNeighborhood : ∀ (i : Fin c.length) (p : TD),
      0 < p.val.1 → p.val.1 < d/8 → -p.val.1 < p.val.2 → p.val.2 < p.val.1 →
      ∃ A : Set (GeometricRealization V F), A ⊆ range positiveG ∧ IsOpen A ∧ vertexPiece i p ∈ A := by
    intro i p hr0 hrcap hxL hxR
    let A : Set (GeometricRealization V F) := {q |
      0 < 1-q.val (c.vertex i) ∧ 1-q.val (c.vertex i) < d/8 ∧
        (1-q.val (c.vertex i))/3 < (fanAt i).linkMoment q ∧
        (fanAt i).linkMoment q < (((fanAt i).length : ℝ)-1/3)*(1-q.val (c.vertex i))}
    have hc : Continuous (fun q : GeometricRealization V F => q.val (c.vertex i)) :=
      (continuous_apply _).comp continuous_subtype_val
    have hr : Continuous (fun q : GeometricRealization V F => 1-q.val (c.vertex i)) :=
      continuous_const.sub hc
    have hm := (fanAt i).continuous_linkMoment
    have hA : IsOpen A := (isOpen_lt continuous_const hr).inter
      ((isOpen_lt hr continuous_const).inter ((isOpen_lt (hr.div_const 3) hm).inter
        (isOpen_lt hm (continuous_const.mul hr))))
    refine ⟨A,?_,hA,?_⟩
    · intro q hq
      exact positiveVertexCriterion i q hq.1 hq.2.1 hq.2.2.1.le hq.2.2.2.le
    · have hrcoord : 1-(vertexPiece i p).val (c.vertex i) = p.val.1 := by
        rw [vertexPieceCenter]; ring
      have hum := congrArg (fun a : ℝ × ℝ => a.2) (vertexPiece_coordinates i p)
      change (fanAt i).linkMoment (vertexPiece i p) =
        ((fanAt i).length : ℝ)/2*p.val.1 +
          orientation i*(((fanAt i).length : ℝ)/2-1/3)*p.val.2 at hum
      change 0 < 1-(vertexPiece i p).val (c.vertex i) ∧ _
      rw [hrcoord,hum]
      refine ⟨hr0,hrcap,?_⟩
      have hn : (1 : ℝ) ≤ ((fanAt i).length : ℝ) := by exact_mod_cast (fanAt i).positive
      have hD : 0 < ((fanAt i).length : ℝ)/2-1/3 := by linarith
      have hplus : 0 < p.val.1+p.val.2 := by linarith
      have hminus : 0 < p.val.1-p.val.2 := by linarith
      have hprodPlus := mul_pos hD hplus
      have hprodMinus := mul_pos hD hminus
      rcases orientation_sign i with hη | hη <;> rw [hη] <;> constructor <;> nlinarith
  have edgeStrictOpenNeighborhood : ∀ (i : Fin c.length)
      (r : ↥(Icc (0 : ℝ) (1/8))) (u : Interval),
      0 < (r : ℝ) → (r : ℝ) < d/8 → 0 < (u : ℝ) → (u : ℝ) < 1 →
      ∃ A : Set (GeometricRealization V F), A ⊆ range positiveG ∧ IsOpen A ∧ edgeStrip i (r,u) ∈ A := by
    intro i r u hr0 hrcap hu0 hu1
    let a := c.vertex i
    let b := c.vertex (cyclicNext c.length c.length_ge_three i)
    let z := third i
    let A : Set (GeometricRealization V F) := {q |
      0 < q.val a ∧ 0 < q.val b ∧ 0 < q.val z ∧
        3*q.val z < d/8 ∧ 2*q.val z < q.val a ∧ 2*q.val z < q.val b}
    have hc (w : V) : Continuous (fun q : GeometricRealization V F => q.val w) :=
      (continuous_apply w).comp continuous_subtype_val
    have hA : IsOpen A := (isOpen_lt continuous_const (hc a)).inter
      ((isOpen_lt continuous_const (hc b)).inter ((isOpen_lt continuous_const (hc z)).inter
        ((isOpen_lt (continuous_const.mul (hc z)) continuous_const).inter
          ((isOpen_lt (continuous_const.mul (hc z)) (hc a)).inter
            (isOpen_lt (continuous_const.mul (hc z)) (hc b))))))
    refine ⟨A,?_,hA,?_⟩
    · intro q hq
      have hf := (triangleInteriorFacts a b z (c.consecutive_vertices_ne i)
        (third_ne_start i) (third_ne_end i)).1 q hq.1 hq.2.1 hq.2.2.1
      exact positiveEdgeCriterion i q hf (by linarith [hq.2.2.1])
        hq.2.2.2.1 hq.2.2.2.2.1.le hq.2.2.2.2.2.le
    · have hqrange := (edgeStrip_range i (edgeStrip i (r,u))).mp ⟨(r,u),rfl⟩
      have hz : (edgeStrip i (r,u)).val z = (r : ℝ)/3 := edgeThirdCoordinate i r u
      have ha : (edgeStrip i (r,u)).val a =
          (1-(r : ℝ))-(u : ℝ)*(1-5*(r : ℝ)/3) := by
        rw [edgeStrip_coordinates]
        simp [a,b,z,Ne.symm (c.consecutive_vertices_ne i),third_ne_start i]
      have hb : (edgeStrip i (r,u)).val b =
          2*(r : ℝ)/3+(u : ℝ)*(1-5*(r : ℝ)/3) := by
        rw [edgeStrip_coordinates]
        simp [a,b,z,c.consecutive_vertices_ne i,third_ne_end i]
      have hgap : 0 < 1-5*(r : ℝ)/3 := by linarith [r.property.2]
      have hleft : 2*(edgeStrip i (r,u)).val z < (edgeStrip i (r,u)).val a := by
        rw [hz,ha]
        nlinarith [mul_pos (sub_pos.mpr hu1) hgap]
      have hright : 2*(edgeStrip i (r,u)).val z < (edgeStrip i (r,u)).val b := by
        rw [hz,hb]
        nlinarith [mul_pos hu0 hgap]
      have hz0 : 0 < (edgeStrip i (r,u)).val z := by rw [hz]; linarith
      change 0 < (edgeStrip i (r,u)).val a ∧ _
      exact ⟨by linarith,by linarith,hz0,by rw [hz]; linarith,hleft,hright⟩
  have positiveGRangeOpen : IsOpen (range positiveG) := by
    rw [isOpen_iff_forall_mem_open]
    intro q hq
    rcases (positiveCarrier q).mp hq with ⟨i,p,hr0,hrcap,rfl⟩ | ⟨i,r,u,hr0,hrcap,rfl⟩
    · by_cases hxR : p.val.2 = p.val.1
      · let r : ↥(Icc (0 : ℝ) (1/8)) := ⟨p.val.1,p.property.1,p.property.2.1⟩
        let pR : TD := ⟨((r : ℝ),(r : ℝ)),r.property.1,r.property.2,
          by linarith [r.property.1],le_rfl⟩
        have hp : p = pR := by
          apply Subtype.ext
          exact Prod.ext rfl hxR
        have he : vertexPiece i p = edgeStrip i (r,0) :=
          (congrArg (vertexPiece i) hp).trans (vertexOutgoingPort i r)
        rw [he]
        exact startPortOpenNeighborhood i r hr0 hrcap
      · by_cases hxL : p.val.2 = -p.val.1
        · let r : ↥(Icc (0 : ℝ) (1/8)) := ⟨p.val.1,p.property.1,p.property.2.1⟩
          let pL : TD := ⟨((r : ℝ),-(r : ℝ)),r.property.1,r.property.2,
            le_rfl,by linarith [r.property.1]⟩
          have hp : p = pL := by
            apply Subtype.ext
            exact Prod.ext rfl hxL
          obtain ⟨j,hj⟩ := successor_bijection.2 i
          have hport := vertexIncomingPort j r
          rw [hj] at hport
          have he : vertexPiece i p = edgeStrip j (r,1) :=
            (congrArg (vertexPiece i) hp).trans hport
          rw [he]
          exact endPortOpenNeighborhood j r hr0 hrcap
        · exact vertexStrictOpenNeighborhood i p hr0 hrcap
            (lt_of_le_of_ne p.property.2.2.1 (Ne.symm hxL))
            (lt_of_le_of_ne p.property.2.2.2 hxR)
    · by_cases hu0 : u = 0
      · rw [hu0]
        exact startPortOpenNeighborhood i r hr0 hrcap
      · by_cases hu1 : u = 1
        · rw [hu1]
          exact endPortOpenNeighborhood i r hr0 hrcap
        · exact edgeStrictOpenNeighborhood i r u hr0 hrcap
            (lt_of_le_of_ne u.property.1 (fun h => hu0 (Subtype.ext h.symm)))
            (lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h)))

  have hgeometry : ∃ G : C(Interval × Circle, GeometricRealization V F),
      IsEmbedding G ∧ (∀ z, G (0,z) = c.circle z) ∧ range G ⊆ U ∧
      (∀ (t : Interval) z, G (t,z) ∈ boundaryLocus F ↔ t = 0) ∧
      IsOpenEmbedding (fun z : Ioo (0 : ℝ) 1 × Circle =>
        G (⟨z.1.val,⟨z.1.property.1.le,z.1.property.2.le⟩⟩,z.2)) := by
    refine ⟨G,GEmbedding,GZeroClock,GSupported,GBoundaryExact,?_⟩
    change IsOpenEmbedding positiveG
    exact ⟨positiveGEmbedding,positiveGRangeOpen⟩
  obtain ⟨G,hG,hzero,hsupport,hboundary,hopen⟩ := hgeometry
  exact inwardBandOfGeometricMap c U G hG hzero hsupport hboundary hopen


end CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry
