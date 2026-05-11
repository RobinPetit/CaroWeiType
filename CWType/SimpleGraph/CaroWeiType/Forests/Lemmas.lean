import CWType.SimpleGraph.CaroWeiType.Forests.Basic
import CWType.SimpleGraph.CaroWeiType.Degenerate

namespace SimpleGraph
open Finset

lemma InducesForest_singleton {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {v : Fin n} :
    G.InducesForest {v} := by
  simp only [InducesForest, IsDegenerateSet, subset_singleton_iff, ne_eq, degree_in,
    forall_eq_or_imp, not_true_eq_false, notMem_empty, inter_empty, card_empty, zero_le, and_true,
    exists_false, imp_self, forall_eq, singleton_ne_empty, not_false_eq_true, mem_singleton,
    exists_eq_left, mem_neighborFinset, SimpleGraph.irrefl, inter_singleton_of_notMem, and_self]

lemma InducesForest_pair {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {v w : Fin n} : G.InducesForest {v, w} := by
  simp only [InducesForest, IsDegenerateSet]
  intro t ht htne
  obtain ⟨u, hu⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr htne
  refine ⟨u, hu, ?_⟩
  have H : ({v, w} \ {u} : Finset _).card ≤ 1 := by grind
  refine le_trans ?_ H
  refine card_le_card ?_
  intro x hx
  simp only [mem_inter, mem_neighborFinset, mem_sdiff, mem_insert, mem_singleton] at hx ⊢
  grind [Adj.ne']

lemma InducesLinearForest_singleton {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {v : Fin n} : G.InducesLinearForest {v} := by
  simp [InducesLinearForest, InducesForest_singleton]

lemma InducesLinearForest_pair {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {v w : Fin n} : G.InducesLinearForest {v, w} := by
  simp only [InducesLinearForest, InducesForest_pair, mem_insert, mem_singleton, degree_in,
    forall_eq_or_imp, mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true,
    inter_insert_of_notMem, forall_eq, true_and]
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ <| one_le_two
    rw [← card_singleton w]
    exact card_le_card inter_subset_right
  · refine le_trans ?_ <| @card_le_two _ _ v w
    exact card_le_card inter_subset_right

lemma InducesForest_mono {n : ℕ} {G₁ G₂ : SimpleGraph (Fin n)}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    {s : Finset (Fin n)} (hle : G₁ ≤ G₂) (h : G₂.InducesForest s) : G₁.InducesForest s := by
  simp only [InducesForest] at h ⊢
  exact IsDegenerateSet_mono G₁ G₂ hle 1 s h

lemma InducesForest_mono' {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {s₁ s₂ : Finset (Fin n)} (hs : s₁ ∩ s₂ = ∅)
    (h : (G.deleteIncidencesOf s₂).InducesForest s₁) :
    G.InducesForest s₁ := by
  exact IsDegenerateSet_mono' G 1 s₁ s₂ hs h

lemma InducesForest_union_leaf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) (hs : G.InducesForest s) {v : Fin n} (hv : G.degree_in s v ≤ 1) :
    G.InducesForest (s ∪ {v}) := by
  simp only [InducesForest] at hs ⊢
  exact G.IsDegenerateSet_union_singleton s hs hv

lemma InducesForest_union_disjoint_neighborhoods {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {s₁ s₂ : Finset (Fin n)} (hs₁ : G.InducesForest s₁)
    (hs₂ : G.InducesForest s₂) (h : ∀ x ∈ s₁, ∀ y ∈ s₂, ¬G.Adj x y) :
    G.InducesForest (s₁ ∪ s₂) := by
  intro t ht htne
  if ht' : t ∩ s₁ ≠ ∅ then
    obtain ⟨x, hx, hdeg⟩ := hs₁ (t ∩ s₁) inter_subset_right ht'
    refine ⟨x, (mem_inter.mp hx).1, ?_⟩
    simp only [degree_in] at hdeg ⊢
    refine le_trans (le_of_eq ?_) hdeg
    refine congrArg card ?_
    ext y
    simp only [mem_inter, mem_neighborFinset, and_congr_right_iff, iff_self_and]
    grind
  else
    have ht' : t ∩ s₂ ≠ ∅ := by grind
    obtain ⟨x, hx, hdeg⟩ := hs₂ (t ∩ s₂) inter_subset_right ht'
    refine ⟨x, (mem_inter.mp hx).1, ?_⟩
    simp only [degree_in] at hdeg ⊢
    refine le_trans (le_of_eq ?_) hdeg
    refine congrArg card ?_
    ext y
    simp only [mem_inter, mem_neighborFinset, and_congr_right_iff, iff_self_and]
    grind [Adj.symm]

lemma InducesForest_of_iso {V V' : Type} [DecidableEq V] [Fintype V] [DecidableEq V'] [Fintype V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (φ : G ≃g G') {s : Finset V} (h : G.InducesForest s) :
    G'.InducesForest (s.image φ.toFun) :=
  GraphParameter.IsDegenerateSet_of_graph_iso φ s h

lemma InducesCaterpillar_of_iso {V V' : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableEq V'] [Fintype V'] {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (φ : G ≃g G') {s : Finset V} (h : G.InducesCaterpillar s) :
    G'.InducesCaterpillar (s.image φ.toFun) := by
  obtain ⟨h, h'⟩ := h
  refine ⟨?_, ?_⟩
  · suffices (s \ {x ∈ s | G.degree_in s x = 1}).image φ.toFun
        = (s.image φ.toFun \ {x ∈ image φ.toFun s | G'.degree_in (image φ.toFun s) x = 1}) by
      exact this ▸ InducesForest_of_iso φ h
    ext u
    simp only [mem_image, mem_sdiff, mem_filter, not_and]
    constructor
    · intro ⟨x, ⟨⟨h, h'⟩, hxu⟩⟩
      refine ⟨⟨x, h, hxu⟩, fun _ ↦ ?_⟩
      refine ne_of_eq_of_ne (hxu ▸ (degree_in_eq_of_iso _ s φ).symm) (h' h)
    · intro ⟨⟨x, hx, hxu⟩, h⟩
      refine ⟨x, ⟨hx, fun _ ↦ ?_⟩, hxu⟩
      exact ne_of_eq_of_ne (hxu ▸ degree_in_eq_of_iso _ s φ) (h ⟨x, hx, hxu⟩)
  · intro u
    simp only [mem_sdiff, mem_filter, not_and, and_imp, mem_image,
      forall_exists_index] at h' ⊢
    intro x hx hxu H
    refine le_of_eq_of_le ?_ (h' x hx ?_)
    · rw [← hxu]
      refine Eq.symm ?_
      have := degree_in_eq_of_iso x (s \ {x ∈ s | #(G.neighborFinset x ∩ s) = 1}) φ
      refine this.trans ?_
      refine congrArg (G'.degree_in · (φ.toFun x)) ?_
      ext u
      simp only [mem_image, mem_sdiff, mem_filter, not_and]
      constructor
      · intro ⟨x, ⟨hx, h⟩, hxu⟩
        refine ⟨⟨x, hx, hxu⟩, fun _ ↦ ?_⟩
        refine ne_of_eq_of_ne ?_ (h hx)
        rw [← degree_in, ← hxu]
        exact (degree_in_eq_of_iso x s φ).symm
      · intro ⟨⟨x, hx, hxu⟩, h'⟩
        refine ⟨x, ⟨⟨hx, fun _ ↦ ?_⟩, hxu⟩⟩
        refine ne_of_eq_of_ne ?_ (h' ⟨x, hx, hxu⟩)
        rw [← degree_in, ← hxu]
        exact degree_in_eq_of_iso x s φ
    · exact fun _ ↦ ne_of_eq_of_ne (hxu ▸ degree_in_eq_of_iso _ s φ) (H x hx hxu)

universe u in
lemma no_induced_K3_of_InducesForest {V : Type u} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V)
    {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) :
    G.InducesForest s → ¬{x, y, z} ⊆ s := by
  intro hf ht
  obtain ⟨w, hw, hwdeg⟩ := hf _ ht <| insert_ne_empty _ _
  simp only [mem_insert, mem_singleton] at hw
  simp only [degree_in] at hwdeg
  rcases hw with h | h | h <;> {
    suffices G.neighborFinset w ∩ {x, y, z} = ({x, y, z} : Finset _) \ {w} by
      grind [Adj.ne]
    subst h
    ext u
    simp only [mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true, inter_insert_of_notMem,
      mem_inter, mem_insert, mem_singleton, mem_sdiff]
    grind [Adj.ne, Adj.symm]
  }

lemma InducesForest_of_InducesCaterpillar {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} (hs : G.InducesCaterpillar s) :
    G.InducesForest s := by
  intro t ht htne
  simp only [InducesCaterpillar, InducesLinearForest] at hs
  if h : ∃ x ∈ t, G.degree_in s x = 1 then
    obtain ⟨x, hxt, hxd⟩ := h
    refine ⟨x, hxt, le_of_le_of_eq (degree_in_mono ht) hxd⟩
  else
    simp only [not_exists, not_and] at h
    refine hs.1 t ?_ htne
    intro y hy
    refine mem_sdiff.mpr ⟨ht hy, ?_⟩
    simp only [mem_filter, not_and, ht hy, forall_const, h y hy, not_false_eq_true]

end SimpleGraph
