import CWType.SimpleGraph.CaroWeiType.Forests.Basic
import CWType.SimpleGraph.CaroWeiType.Degenerate

namespace SimpleGraph
open Finset

lemma InducesForestIsUnionStable {V : Type*} [DecidableEq V] [Fintype V] :
    IsNonAdjacentUnionStableProp (fun G _ s ↦ @SimpleGraph.InducesForest V _ _ G _ s) :=
  IsDegenerateSetIsUnionStable _

lemma InducesForest_pair {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {v w : V} : G.InducesForest {v, w} := by
  refine IsDegenerateSet_of_degree_in_le _ _ _ ?_
  intro x hx
  refine le_trans (degree_in_le_card_minus_one_of_mem hx) (by grind)

lemma InducesForest_singleton {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    G.InducesForest {v} :=
  pair_eq_singleton v ▸ InducesForest_pair

lemma InducesLinearForestIsUnionStable {V : Type*} [DecidableEq V] [Fintype V] :
    IsNonAdjacentUnionStableProp (fun G _ s ↦ @SimpleGraph.InducesLinearForest V _ _ G _ s) := by
  intro G _ s s' hss' h ⟨hsf, hs⟩ ⟨hs'f, hs'⟩
  refine ⟨InducesForestIsUnionStable G _ _ hss' h hsf hs'f, ?_⟩
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · refine le_of_eq_of_le ?_ (hs _ hx)
    refine congrArg Finset.card ?_
    ext y
    simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, or_iff_left_iff_imp]
    exact fun hxy hy ↦ h x hx y hy hxy |>.elim
  · refine le_of_eq_of_le ?_ (hs' _ hx)
    refine congrArg Finset.card ?_
    ext y
    simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, or_iff_right_iff_imp]
    exact fun hxy hy ↦ h y hy x hx hxy.symm |>.elim

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

lemma InducesForest_mono {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s t : Finset V} (hle : s ⊆ t) (h : G.InducesForest t) :
    G.InducesForest s :=
  fun _ hs' hs'ne ↦ h _ (hs'.trans hle) hs'ne

lemma InducesForest_graph_mono {V : Type*} [DecidableEq V] [Fintype V] {G₁ G₂ : SimpleGraph V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    {s : Finset V} (hle : G₁ ≤ G₂) (h : G₂.InducesForest s) : G₁.InducesForest s := by
  simp only [InducesForest] at h ⊢
  exact IsDegenerateSet_mono G₁ G₂ hle 1 s h

lemma InducesForest_graph_mono' {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hs : s₁ ∩ s₂ = ∅)
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
  IsDegenerateSet_of_graph_iso φ s h

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

lemma InducesCaterpillarIsUnionStable {V : Type*} [DecidableEq V] [Fintype V] :
    IsNonAdjacentUnionStableProp (fun G _ s ↦ @SimpleGraph.InducesCaterpillar V _ _ G _ s) := by
  intro G _ s s' hss' h ⟨hslf, hs⟩ ⟨hs'lf, hs'⟩
  have hdegree_in_s {u} (hu : u ∈ s) :
      G.neighborFinset u ∩ s = G.neighborFinset u ∩ (s ∪ s') := by
    ext w
    simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, iff_self_or]
    exact fun huw hw ↦ h u hu w hw huw |>.elim
  have hdegree_in_s' {u} (hu : u ∈ s') :
      G.neighborFinset u ∩ s' = G.neighborFinset u ∩ (s ∪ s') := by
    ext w
    simp only [mem_inter, mem_neighborFinset, mem_union, and_congr_right_iff, iff_or_self]
    exact fun huw hw ↦ h w hw u hu huw.symm |>.elim
  refine ⟨?_, ?_⟩
  · suffices ((s ∪ s') \ {x ∈ s ∪ s' | G.degree_in (s ∪ s') x = 1})
        = (s \ {x ∈ s | G.degree_in s x = 1}) ∪ (s' \ {x ∈ s' | G.degree_in s' x = 1}) by
      rw [this]
      refine InducesForestIsUnionStable G _ _ ?_ ?_ hslf hs'lf
      · ext u
        simp only [mem_inter, mem_sdiff, mem_filter, not_and, notMem_empty, iff_false,
          Classical.not_imp, Decidable.not_not, and_imp]
        exact fun hus _ h ↦ notMem_of_mem_of_empty_inter hus hss' h |>.elim
      · exact fun x hx y hy ↦ h x (mem_sdiff.mp hx |>.1) y (mem_sdiff.mp hy |>.1)
    ext u
    simp only [degree_in, mem_sdiff, mem_union, mem_filter, not_and]
    constructor
    · intro ⟨hu, hu'⟩
      simp only [hu, forall_const] at hu'
      rcases hu with hu | hu
      · refine Or.inl <| ⟨hu, fun _ ↦ ne_of_eq_of_ne ?_ hu'⟩
        exact congrArg Finset.card <| hdegree_in_s hu
      · refine Or.inr <| ⟨hu, fun _ ↦ ne_of_eq_of_ne ?_ hu'⟩
        exact congrArg Finset.card <| hdegree_in_s' hu
    · intro h
      rcases h with ⟨hu, hu'⟩ | ⟨hu, hu'⟩
      · simp only [hu, true_or, forall_const, true_and]
        refine ne_of_eq_of_ne (Eq.symm <| ?_) (hu' hu)
        exact congrArg Finset.card <| hdegree_in_s hu
      · simp only [hu, or_true, forall_const, true_and]
        refine ne_of_eq_of_ne (Eq.symm <| ?_) (hu' hu)
        exact congrArg Finset.card <| hdegree_in_s' hu
  · intro x hx
    obtain ⟨hx, hx'⟩ := mem_sdiff.mp hx
    rcases mem_union.mp hx with hx | hx
    · refine le_of_eq_of_le ?_ (hs x ?_)
      · refine congrArg Finset.card ?_
        ext u
        simp only [degree_in, mem_inter, mem_neighborFinset, mem_sdiff, mem_union, mem_filter,
          not_and, and_congr_right_iff]
        grind
      · simp only [degree_in, mem_filter, mem_union, not_and, mem_sdiff] at hx' ⊢
        refine ⟨hx, fun _ ↦ ?_⟩
        refine ne_of_eq_of_ne ?_ (hx' <| Or.inl hx)
        exact congrArg Finset.card (hdegree_in_s hx)
    · refine le_of_eq_of_le ?_ (hs' x ?_)
      · refine congrArg Finset.card ?_
        ext u
        simp only [degree_in, mem_inter, mem_neighborFinset, mem_sdiff, mem_union, mem_filter,
          not_and, and_congr_right_iff]
        intro hxu
        have hu' : u ∉ s := fun hu ↦ h u hu x hx hxu.symm
        grind
      · simp only [degree_in, mem_filter, mem_union, not_and, mem_sdiff] at hx' ⊢
        refine ⟨hx, fun _ ↦ ?_⟩
        refine ne_of_eq_of_ne ?_ (hx' <| Or.inr hx)
        exact congrArg Finset.card (hdegree_in_s' hx)

lemma no_induced_K3_of_InducesForest {V : Type*} [DecidableEq V] [Fintype V]
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

lemma InducesLinearForest_mono' {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hcap : s₁ ∩ s₂ = ∅)
    (hs : (G.deleteIncidencesOf s₂).InducesLinearForest s₁) :
    G.InducesLinearForest s₁ := by
  obtain ⟨hs, hsdeg⟩ := hs
  refine ⟨InducesForest_graph_mono' hcap hs, fun x hx ↦ le_trans ?_ <| hsdeg x hx⟩
  refine degree_in_deleteIncidencesOf_of_le (inter_comm s₁ s₂ ▸ hcap) ?_ (le_refl _)
  exact notMem_of_mem_of_empty_inter hx hcap

lemma InducesCaterpillar_mono' {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hcap : s₁ ∩ s₂ = ∅)
    (hs : (G.deleteIncidencesOf s₂).InducesCaterpillar s₁) :
    G.InducesCaterpillar s₁ := by
  simp only [InducesCaterpillar] at hs
  refine @InducesLinearForest_mono' _ _ _ G _ _ s₂ ?_ ?_
  · ext u
    simp only [notMem_empty, iff_false, mem_inter, not_and]
    exact fun h ↦ notMem_of_mem_of_empty_inter (mem_sdiff.mp h |>.1) hcap
  · suffices (s₁ \ {x ∈ s₁ | (G.deleteIncidencesOf s₂).degree_in s₁ x = 1})
        = (s₁ \ {x ∈ s₁ | G.degree_in s₁ x = 1}) by
      exact this ▸ hs
    ext u
    simp only [mem_sdiff, mem_filter]
    constructor <;> {
      intro ⟨hus₁, h⟩
      simp only [hus₁, true_and] at h ⊢
      refine ne_of_eq_of_ne ?_ h
      refine le_antisymm_iff.mpr ?_
      simp only [degree_in_mono' deleteIncidencesOf_le, true_and, and_true]
      refine card_le_card ?_
      intro w
      simp only [mem_inter] at ⊢
      intro ⟨hw, hws₁⟩
      refine ⟨?_, hws₁⟩
      refine (mem_neighborFinset_deleteIncidencesOf_iff_of_notMem ?_ ?_).mp hw
      · exact notMem_of_mem_of_empty_inter hws₁ hcap
      · exact notMem_of_mem_of_empty_inter hus₁ hcap
    }

lemma InducesCaterpillar_union_deg_le_1 {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hs₂ : ∀ x ∈ s₂, G.degree x ≤ 1)
    (hs₁ : G.InducesLinearForest s₁) :
    G.InducesCaterpillar (s₁ ∪ s₂) := by
  refine ⟨?_, ?_⟩
  · intro t ht htne
    if h : ∃ x, x ∈ t ∩ s₂ then
      obtain ⟨x, hx⟩ := h
      obtain ⟨hxt, hxs₂⟩ := mem_inter.mp hx
      exact ⟨x, hxt, le_trans degree_in_le_degree (hs₂ _ hxs₂)⟩
    else
      simp only [mem_inter, not_exists, not_and] at h
      refine hs₁.1 t ?_ htne
      intro x hxt
      have hxt' := ht hxt
      simp only [degree_in, mem_sdiff, mem_union, mem_filter, not_and] at hxt' ⊢
      obtain ⟨hx, hd⟩ := hxt'
      rcases hx with hx | hx
      · exact hx
      · exact h x hxt hx |>.elim
  · intro x hx
    simp only [degree_in, mem_sdiff, mem_union, mem_filter, not_and] at hx
    obtain ⟨hxs, hxd⟩ := hx
    rcases hxs with hxs₁ | hxs₂
    · refine le_trans ?_ (hs₁.2 x hxs₁)
      refine card_le_card ?_
      intro u hu
      simp only [degree_in, mem_inter, mem_neighborFinset, mem_sdiff, mem_union, mem_filter,
        not_and] at hu ⊢
      obtain ⟨hxu, hus, hu⟩ := hu
      refine ⟨hxu, ?_⟩
      refine hus.elim (·) (fun hus₂ ↦ ?_)
      simp only [hus, forall_const] at hu
      have : #(G.neighborFinset u ∩ (s₁ ∪ s₂)) = 0 := by
        refine le_antisymm ?_ (Nat.zero_le _)
        grind [degree_in_le_degree]
      suffices x ∈ (∅ : Finset _) by grind
      rw [← card_eq_zero.mp this]
      exact mem_inter.mpr ⟨mem_neighborFinset .. |>.mpr hxu.symm, mem_union_left _ hxs₁⟩
    · exact le_trans degree_in_le_degree (le_trans (hs₂ x hxs₂) NeZero.one_le)

lemma InducesCaterpillar_iff {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (s : Finset V) :
    G.InducesCaterpillar s ↔ G.InducesForest s ∧
      ∀ v x y z, v ∈ s → x ∈ s → y ∈ s → z ∈ s → x ≠ y → x ≠ z → y ≠ z
        → 3 ≤ G.degree_in s v → 2 ≤ G.degree_in s x → 2 ≤ G.degree_in s y → 2 ≤ G.degree_in s z
        → G.Adj v x → G.Adj v y → ¬G.Adj v z := by
  constructor
  · intro hs
    refine ⟨InducesForest_of_InducesCaterpillar G hs, ?_⟩
    intro v x y z hvs hxs hys hzs hxy hxz hyz hdv hdx hdy hdz hvx hvy hvz
    have : 3 ≤ G.degree_in (s \ {x ∈ s | G.degree_in s x = 1}) v := by
      have : #({x, y, z} : Finset _) = 3 := by grind
      refine this ▸ card_le_card ?_
      refine subset_inter_iff.mpr ⟨by grind [mem_neighborFinset], ?_⟩
      intro u hu
      simp only [mem_insert, mem_singleton] at hu
      refine mem_sdiff.mpr ⟨by grind, ?_⟩
      simp only [degree_in, mem_filter, not_and]
      grind
    have H := by
      refine hs.2 v (mem_sdiff.mpr ⟨hvs, ?_⟩)
      simp only [mem_filter, hvs, true_and]
      have : 3 ≤ G.degree_in s v := le_trans this (degree_in_mono sdiff_subset)
      lia
    linarith
  · intro ⟨hsf, h⟩
    refine ⟨fun t ht ↦ hsf t (subset_eq_inter ht), ?_⟩
    intro v hv
    simp only [mem_sdiff, mem_filter, not_and] at hv
    obtain ⟨hvs, hvd⟩ := hv
    simp only [hvs, forall_const] at hvd
    by_contra
    simp only [not_le] at this
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset_three_le_card_iff _ |>.mp this
    have h2led {u : V} : u ∈ G.neighborFinset v ∩ (s \ {x ∈ s | G.degree_in s x = 1})
        → 2 ≤ G.degree_in s u := by
      intro hu
      suffices G.degree_in s u ≠ 0 ∧ G.degree_in s u ≠ 1 by lia
      refine ⟨?_, by grind⟩
      suffices 1 ≤ G.degree_in s u by linarith
      rw [degree_in, ← card_singleton v]
      refine card_le_card ?_
      refine singleton_subset_iff.mpr <| mem_inter.mpr ⟨?_, hvs⟩
      exact mem_neighborFinset_symm <| mem_inter.mp hu |>.1
    refine h v x y z hvs (mem_sdiff.mp (mem_inter.mp hx |>.2) |>.1)
      (mem_sdiff.mp (mem_inter.mp hy |>.2) |>.1) (mem_sdiff.mp (mem_inter.mp hz |>.2) |>.1)
      hxy hxz hyz (le_trans this (degree_in_mono sdiff_subset)) (h2led hx) (h2led hy) (h2led hz)
      (mem_neighborFinset .. |>.mp <| mem_inter.mp hx |>.1)
      (mem_neighborFinset .. |>.mp <| mem_inter.mp hy |>.1) ?_
    exact mem_neighborFinset .. |>.mp <| mem_inter.mp hz |>.1

lemma InducesCaterpillar_graph_mono' {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s₁ s₂ : Finset V} (hs : s₁ ∩ s₂ = ∅)
    (h : (G.deleteIncidencesOf s₂).InducesCaterpillar s₁) :
    G.InducesCaterpillar s₁ := by
  obtain ⟨hs₁f, h⟩ := InducesCaterpillar_iff _ |>.mp h
  refine InducesCaterpillar_iff _ |>.mpr ⟨InducesForest_graph_mono' hs hs₁f, ?_⟩
  intro v x y z hv hx hy hz hxy hxz hyz hdv hdx hdy hdz hvx hvy
  have hs' := inter_comm s₁ s₂ ▸ hs
  have := by
    refine h v x y z hv hx hy hz hxy hxz hyz
      (le_of_le_of_eq hdv <| Eq.symm <| degree_in_deleteIncidencesOf _ _ hs'
        (notMem_of_mem_of_empty_inter hv hs))
      (le_of_le_of_eq hdx <| Eq.symm <| degree_in_deleteIncidencesOf _ _ hs'
        (notMem_of_mem_of_empty_inter hx hs))
      (le_of_le_of_eq hdy <| Eq.symm <| degree_in_deleteIncidencesOf _ _ hs'
        (notMem_of_mem_of_empty_inter hy hs))
      (le_of_le_of_eq hdz <| Eq.symm <| degree_in_deleteIncidencesOf _ _ hs'
        (notMem_of_mem_of_empty_inter hz hs))
      (deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj
        (notMem_of_mem_of_empty_inter hv hs) (notMem_of_mem_of_empty_inter hx hs) hvx)
      (deleteIncidencesOf_adj_of_notMem_of_notMem_of_adj
        (notMem_of_mem_of_empty_inter hv hs) (notMem_of_mem_of_empty_inter hy hs) hvy)
  refine not_iff_not.mpr (deleteIncidencesOf_adj_iff_of_notMem ?_ ?_) |>.mpr this
  · exact notMem_of_mem_of_empty_inter hv hs
  · exact notMem_of_mem_of_empty_inter hz hs

lemma InducesCaterpillar_pair {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v w : V} :
    G.InducesCaterpillar {v, w} := by
  refine ⟨InducesForest_mono sdiff_subset InducesForest_pair, ?_⟩
  exact fun x hx ↦ le_trans₃ (degree_in_le_card_minus_one_of_mem hx) (by grind) one_le_two

lemma InducesCaterpillar_singleton {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V} :
    G.InducesCaterpillar {v} :=
  pair_eq_singleton v ▸ G.InducesCaterpillar_pair

end SimpleGraph
