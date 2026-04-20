import CWType.SimpleGraph.CaroWeiType.Forests.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Lemmas
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim5
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim7
import CWType.SimpleGraph.CaroWeiType.BoundedDegreeCaterpillars.Claim11

namespace CaroWeiType
namespace ABC
namespace Tripartition

open SimpleGraph
open Finset

lemma _notA23 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {u v : Fin n} (huv : u ≠ v)
    (hBu : ABC.B u) (hdu : G.degree u = 3) (hBv : ABC.B v) (hdv : G.degree v = 3)
    {x : Fin n} (hx : x ∈ (G.neighborFinset u ∩ G.neighborFinset v))
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC')
    (hAx : ABC.A x) (hdx : (G.degree x = 2 ∨ G.degree x = 3)) :
    Objective G ABC := by
  rcases hdx with hdx | hdx
  · refine Claim7 hG ih ⟨v, x, hdv, hBv, hdx, hAx, ?_⟩
    exact G.mem_neighborFinset .. |>.mp <| mem_inter.mp hx |>.2
  · obtain ⟨z, hNx⟩ := by
      refine triplet_of_2 hdx ?_ ?_ huv
      · exact mem_neighborFinset_symm <| (mem_inter.mp hx).1
      · exact mem_neighborFinset_symm <| (mem_inter.mp hx).2
    exact Claim11 hG hAx hdx hNx hBu hBv hdu hdv ih

lemma Claim12 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ABC : Tripartition n}
    (hG : G.support.toFinset ⊆ ABC.toFinset) {u v : Fin n} (huv : u ≠ v)
    (hBu : ABC.B u) (hdu : G.degree u = 3) (hBv : ABC.B v) (hdv : G.degree v = 3)
    {x y : Fin n} (hxy : x ≠ y)
    (hxyNuv : {x, y} ⊆ (G.neighborFinset u ∩ G.neighborFinset v))
    (ih : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (ABC' : Tripartition n),
      ABC'.card < ABC.card → Objective G' ABC') :
    Objective G ABC := by
  if hx : (ABC.A x ∧ (G.degree x = 2 ∨ G.degree x = 3)) then
    refine _notA23 hG huv hBu hdu hBv hdv (hxyNuv ?_) ih hx.1 hx.2
    simp only [mem_insert, mem_singleton, true_or]
  else if hy : (ABC.A y ∧ (G.degree y = 2 ∨ G.degree y = 3)) then
    refine _notA23 hG huv hBu hdu hBv hdv (hxyNuv ?_) ih hy.1 hy.2
    simp only [mem_insert, mem_singleton, or_true]
  else
    have hABC {z : Fin n} (hz : z ∈ ({x, y} : Finset _)) : z ∈ ABC := by
      refine (coe_mem_toFinset ABC).mpr <| hG <| Set.mem_toFinset.mpr ?_
      refine G.mem_support.mpr ⟨v, G.mem_neighborFinset .. |>.mp <| mem_neighborFinset_symm ?_⟩
      exact mem_inter.mp (hxyNuv hz) |>.2
    if hdx : G.degree x ≤ 1 then
      exact Claim5 hG ih ⟨x, hABC (by simp only [mem_insert, mem_singleton, true_or]), hdx⟩
    else if hdy : G.degree y ≤ 1 then
      exact Claim5 hG ih ⟨y, hABC (by simp only [mem_insert, mem_singleton, or_true]), hdy⟩
    else
      simp only [not_le] at hdx hdy
      have hf {z : Fin n} (hz : z ∈ ({x, y} : Finset _)) : f G ABC z < 1 / 2 := by
        rcases ABC.mem_iff.mp (hABC hz) with hA | hB | hC
        · simp only [f, hA, ↓reduceDIte]
          calc fA (G.degree z)
            _ ≤ fA 4 := by
              refine fA_decreasing ?_
              simp only [mem_insert, mem_singleton] at hz
              rcases hz with hz | hz <;> {
                subst hz
                simp [hA] at hx hy
                lia
              }
            _ = 2 / 5 := by grind only
            _ < 1 / 2 := by linarith
        · simp only [f, hB, not_A_of_B, ↓reduceDIte]
          calc fB (G.degree z)
            _ ≤ fB 2 := fB_decreasing <| Nat.succ_le_of_lt <| by grind
            _ = 1 / 3 := rfl
            _ < 1 / 2 := by linarith
        · simp only [f, hC, not_A_of_C, not_B_of_C, ↓reduceDIte]
          calc fC (G.degree z)
            _ ≤ fC 2 := fC_decreasing <| Nat.succ_le_of_lt <| by grind
            _ = 1 / 6 := rfl
            _ < 1 / 2 := by linarith
      obtain ⟨s, hs, hsforest, hsrespect, hcard⟩ := by
        refine ih (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) <| sdiff_card ABC ?_
        suffices x ∈ ABC.toFinset by
          refine nonempty_iff_ne_empty.mp <| nonempty_def.mpr ⟨x, mem_inter.mpr ⟨?_, this⟩⟩
          simp only [mem_insert, mem_singleton, true_or]
        refine ABC.coe_mem_toFinset.mp <| hABC <| by simp only [mem_insert, mem_singleton, true_or]
      refine ⟨s, ?_, ?_, ?_, ?_⟩
      · exact subset_trans (ABC.sdiff_toFinset ▸ hs) sdiff_subset
      · refine InducesForest_mono' ?_ hsforest
        simp only [sdiff_toFinset] at hs
        exact disjoint_of_sdiff hs
      · exact respects_mono G ABC hs hsrespect
      · refine le_trans ?_ hcard
        haveI : u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · refine Ne.symm <| ne_of_mem_neighborFinset G ?_
            refine mem_inter.mp (hxyNuv ?_) |>.1
            simp only [mem_insert, mem_singleton, true_or]
          · refine Ne.symm <| ne_of_mem_neighborFinset G ?_
            refine mem_inter.mp (hxyNuv ?_) |>.1
            simp only [mem_insert, mem_singleton, or_true]
          · refine Ne.symm <| ne_of_mem_neighborFinset G ?_
            refine mem_inter.mp (hxyNuv ?_) |>.2
            simp only [mem_insert, mem_singleton, true_or]
          · refine Ne.symm <| ne_of_mem_neighborFinset G ?_
            refine mem_inter.mp (hxyNuv ?_) |>.2
            simp only [mem_insert, mem_singleton, or_true]
        obtain ⟨hunex, huney, hvnex, hvney⟩ := this
        calc eval G ABC
          _ = ∑ w ∈ ABC.toFinset, f G ABC w := rfl
          _ = ∑ w ∈ (ABC.toFinset \ {x, y, u, v}), f G ABC w
              + ∑ w ∈ {x, y, u, v}, f G ABC w := by
            refine Eq.symm <| sum_sdiff ?_
            intro w hw
            simp only [mem_insert, mem_singleton] at hw
            rcases hw with hw | hw | hw | hw
            · refine hG <| Set.mem_toFinset.mpr ?_
              refine G.degree_pos_iff_mem_support _ |>.mp ?_
              exact lt_trans one_pos (hw ▸ hdx)
            · refine hG <| Set.mem_toFinset.mpr ?_
              refine G.degree_pos_iff_mem_support _ |>.mp ?_
              exact lt_trans one_pos (hw ▸ hdy)
            · refine hG <| Set.mem_toFinset.mpr ?_
              refine G.mem_support.mpr ⟨x, ?_⟩
              refine G.mem_neighborFinset .. |>.mp (hw ▸ ?_)
              refine mem_inter.mp (hxyNuv ?_) |>.1
              simp only [mem_insert, mem_singleton, true_or]
            · refine hG <| Set.mem_toFinset.mpr ?_
              refine G.mem_support.mpr ⟨x, ?_⟩
              refine G.mem_neighborFinset .. |>.mp (hw ▸ ?_)
              refine mem_inter.mp (hxyNuv ?_) |>.2
              simp only [mem_insert, mem_singleton, true_or]
          _ = ∑ w ∈ (ABC.toFinset \ {x, y, u, v}), f G ABC w
              + f G ABC x + f G ABC y + f G ABC u + f G ABC v := by
            grind
          _ ≤ ∑ w ∈ (ABC.toFinset \ {x, y, u, v}), f (G.deleteIncidencesOf {x, y}) ABC w
              + f G ABC x + f G ABC y + f G ABC u + f G ABC v := by
            repeat refine add_le_add_left ?_ _
            exact sum_le_sum <| fun _ _ ↦ f_mono deleteIncidencesOf_le
          _ = ∑ w ∈ (ABC.toFinset \ {x, y, u, v}), f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) w
              + f G ABC x + f G ABC y + f G ABC u + f G ABC v := by
            simp only [add_left_inj]
            refine sum_congr rfl ?_
            intro w hw
            rcases ABC.coe_mem_toFinset.mpr <| mem_sdiff.mp hw |>.1 with hA | hB | hC
            · have hA' : (ABC \ {x, y}).A w := ⟨hA, by grind⟩
              simp only [f, hA, hA', ↓reduceDIte]
            · have hB' : (ABC \ {x, y}).B w := ⟨hB, by grind⟩
              simp only [f, hB, hB', not_A_of_B, ↓reduceDIte]
            · have hC' : (ABC \ {x, y}).C w := ⟨hC, by grind⟩
              simp only [f, hC, hC', not_A_of_C, not_B_of_C, ↓reduceDIte]
          _ = ∑ w ∈ (ABC.toFinset \ {x, y, u, v}), f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) w
              + f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) u
              + f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) v
              - f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) u
              - f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) v
              + f G ABC x + f G ABC y + f G ABC u + f G ABC v := by
            simp only [add_left_inj]
            grind only
          _ = ∑ w ∈ (ABC.toFinset \ {x, y}), f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) w
              - f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) u
              - f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) v
              + f G ABC x + f G ABC y + f G ABC u + f G ABC v := by
            simp only [add_left_inj, sub_left_inj]
            suffices ((ABC.toFinset \ {x, y, u, v}) ∪ {u, v}) = (ABC.toFinset \ {x, y}) by
              rw [← this]
              have h' (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
                  ∑ w ∈ (ABC.toFinset \ {x, y, u, v}) ∪ {u, v},
                    f H (ABC \ {x, y}) w
                  = ∑ w ∈ ABC.toFinset \ {x, y, u, v}, f H (ABC \ {x, y}) w
                  + ∑ w ∈ {u, v}, f H (ABC \ {x, y}) w := by
                refine sum_union ?_
                intro s
                simp only [le_eq_subset, bot_eq_empty, subset_empty]
                grind
              rw [h' (G.deleteIncidencesOf {x, y})]
              repeat rw [add_assoc]
              simp only [add_right_inj]
              exact Eq.symm <| sum_pair huv
            ext w
            simp only [union_insert, union_singleton, mem_insert, mem_sdiff, mem_singleton, not_or]
            have _ : u ∈ ABC.toFinset ∧ v ∈ ABC.toFinset := by
              refine ⟨?_, ?_⟩ <;> {
                refine hG <| Set.mem_toFinset.mpr ?_
                refine G.mem_support.mpr ⟨x, ?_⟩
                refine G.mem_neighborFinset .. |>.mp ?_
                have hx : x ∈ ({x, y} : Finset _) := by
                  simp only [mem_insert, mem_singleton, true_or]
                simp only [mem_inter.mp (hxyNuv hx)]
              }
            grind only [coe_mem_toFinset]
          _ = ∑ w ∈ (ABC.toFinset \ {x, y}), f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) w
              + (f G ABC x + f G ABC y + f G ABC u + f G ABC v
                - f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) u
                - f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) v) := by
            lia
          _ = eval (G.deleteIncidencesOf {x, y}) (ABC \ {x, y})
              + (f G ABC x + f G ABC y + f G ABC u + f G ABC v
                - f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) u
                - f (G.deleteIncidencesOf {x, y}) (ABC \ {x, y}) v) := by
            simp only [add_left_inj]
            rw [← ABC.sdiff_toFinset, ← eval]
        simp only [add_le_iff_nonpos_right, tsub_le_iff_right, zero_add]
        rw [fB3 hBu hdu, fB3 hBv hdv]
        have hB'u : (ABC \ {x, y}).B u := ⟨hBu, by grind⟩
        have hB'v : (ABC \ {x, y}).B v := ⟨hBv, by grind⟩
        have hd'u : (G.deleteIncidencesOf {x, y}).degree u = 1 := by
          grind [degree_deleteIncidencesOf_neighbor G (subset_trans hxyNuv inter_subset_left)]
        have hd'v : (G.deleteIncidencesOf {x, y}).degree v = 1 := by
          grind [degree_deleteIncidencesOf_neighbor G (subset_trans hxyNuv inter_subset_right)]
        rw [fB1 hB'u hd'u, fB1 hB'v hd'v]
        calc f G ABC x + f G ABC y + 1 / 3 + 1 / 3
          _ ≤ 1 / (2 : ℝ) + 1 / 2 + 1 / 3 + 1 / 3 := by
            repeat refine add_le_add_left ?_ _
            refine add_le_add ?_ ?_
            · exact le_of_lt <| hf <| by simp only [mem_insert, mem_singleton, true_or]
            · exact le_of_lt <| hf <| by simp only [mem_insert, mem_singleton, or_true]
        linarith

end Tripartition
end ABC
end CaroWeiType
