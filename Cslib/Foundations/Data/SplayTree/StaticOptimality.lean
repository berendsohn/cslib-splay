module

public import Cslib.Foundations.Data.BinaryTree
public import Cslib.Foundations.Data.SplayTree.Basic
public import Cslib.Foundations.Data.SplayTree.Complexity
public import Cslib.Foundations.Data.SplayTree.Correctness
public import Cslib.Foundations.Data.SplayTree.Weighted
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Static optimality of Splay Trees
-/

@[expose] public section

namespace SplayTree

namespace Weighted

open Tree

def staticCost [LinearOrder α] (t : Tree α) (X : Fin m → α) : ℕ :=
  ∑ i, searchPathLen t (X i)

/-private noncomputable def static_weight [LinearOrder α] (s : Tree α) (q : α) : ℝ :=
    if q ∈ s then 3^(s.nodeCount - searchPathLen s q : ℝ) else 0-/

private noncomputable def static_weight [LinearOrder α] (s : Tree α) (q : α) : ℝ :=
    3^(s.nodeCount - searchPathLen s q : ℝ)

private lemma static_weight_pos [LinearOrder α] (s : Tree α) (q : α) : static_weight s q > 0 := by
  simp only [static_weight, gt_iff_lt]; apply Real.rpow_pos_of_pos (by simp)

-- TODO?
private lemma static_weight_lb [LinearOrder α] (s : Tree α) (q : α) (hq : q ∈ s) :
    1 ≤ static_weight s q := by
  simp only [static_weight, hq]
  apply Real.one_le_rpow (by simp)
  simp only [sub_nonneg, Nat.cast_le]; exact searchPathLen_le_nodeCount s q

private lemma searchPathLen_left [LinearOrder α] (v : α) (l r : Tree α) (q : α) (hqv : q < v) :
    searchPathLen (node v l r) q = 1 + searchPathLen l q := by
  simp [searchPathLen, hqv]

private lemma static_weight_left [LinearOrder α] (v : α) (l r : Tree α) (q : α) (hqv : q < v) :
    let s := node v l r
    static_weight s q = 3^(s.nodeCount - l.nodeCount-1 : ℝ) * static_weight l q := by
  simp only [static_weight, nodeCount_node, Nat.cast_add, Nat.cast_one]
  rw [←Real.rpow_add (by simp)]
  apply (Real.rpow_right_inj (by simp) (by simp)).mpr
  simp [searchPathLen_left v l r q hqv]; linarith

private lemma static_weight_size_left [LinearOrder α]
    (v : α) (l r : Tree α) (hbst : (node v l r).IsBST) :
    let s := node v l r
    size (static_weight s) l = 3^(s.nodeCount - l.nodeCount-1 : ℝ) * size (static_weight l) l := by
  simp only [size_from_toKeyList]
  have hlv : ∀ x ∈ l.toKeyList, x < v := by
    intro x hx
    apply lt_of_IsBST_left l v r x hbst
    exact mem_iff_mem_toKeyList.mpr hx
  have : ∀ xs, xs.Sublist l.toKeyList → (List.map (static_weight (l △[v] r)) xs).sum =
      3 ^ ((l △[v] r).nodeCount - ↑l.nodeCount - 1 : ℝ) * (List.map (static_weight l) xs).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro hsub
      have hxv : x < v := by apply hlv; exact List.mem_of_cons_sublist hsub
      have := ih (List.sublist_of_cons_sublist hsub)
      simp [this, static_weight_left v l r x hxv]; linarith
  exact this l.toKeyList (by rfl)

/-
TODO: Lots of duplicated code. Maybe some mirror-IsBST lemma with reverse linear order could help?
-/
private lemma searchPathLen_right [LinearOrder α] (v : α) (l r : Tree α) (q : α) (hqv : v < q) :
    searchPathLen (node v l r) q = 1 + searchPathLen r q := by
  simp only [searchPathLen, hqv, ↓reduceIte, ite_eq_right_iff, Nat.add_left_cancel_iff]
  intro h'; apply le_of_lt at h'; apply not_le_of_gt at hqv; contradiction

private lemma static_weight_right [LinearOrder α] (v : α) (l r : Tree α) (q : α) (hqv : v < q) :
    let s := node v l r
    static_weight s q = 3^(s.nodeCount - r.nodeCount-1 : ℝ) * static_weight r q := by
  simp only [static_weight, nodeCount_node, Nat.cast_add, Nat.cast_one]
  rw [←Real.rpow_add (by simp)]
  apply (Real.rpow_right_inj (by simp) (by simp)).mpr
  simp [searchPathLen_right v l r q hqv]; linarith

private lemma static_weight_size_right [LinearOrder α]
    (v : α) (l r : Tree α) (hbst : (node v l r).IsBST) :
    let s := node v l r
    size (static_weight s) r = 3^(s.nodeCount - r.nodeCount-1 : ℝ) * size (static_weight r) r := by
  simp only [size_from_toKeyList]
  have hrv : ∀ x ∈ r.toKeyList, v < x := by
    intro x hx
    apply gt_of_IsBST_right l v r x hbst
    exact mem_iff_mem_toKeyList.mpr hx
  have : ∀ xs, xs.Sublist r.toKeyList → (List.map (static_weight (l △[v] r)) xs).sum =
      3 ^ ((l △[v] r).nodeCount - ↑r.nodeCount - 1 : ℝ) * (List.map (static_weight r) xs).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro hsub
      have hxv : v < x := by apply hrv; exact List.mem_of_cons_sublist hsub
      have := ih (List.sublist_of_cons_sublist hsub)
      simp [this, static_weight_right v l r x hxv]; linarith
  exact this r.toKeyList (by rfl)


-- TODO: Lots of annoying casts and calculations
private lemma static_weight_size_self_ub [LinearOrder α] (s : Tree α) (hbst : s.IsBST) :
    size (static_weight s) s ≤ 3 ^ s.nodeCount := by
  induction s with
  | nil => simp
  | node v l r lih rih =>
    let s := node v l r
    simp only [size]
    have h1 : static_weight (l △[v] r) v ≤ 3^(s.nodeCount - 1 : ℝ) := by
      simp[static_weight, s, searchPathLen]
    have hl : size (static_weight (l △[v] r)) l ≤ 3^(s.nodeCount - 1 : ℝ) := by
      calc size (static_weight (l △[v] r)) l
          = 3^(s.nodeCount - l.nodeCount-1 : ℝ) * size (static_weight l) l := by
            exact static_weight_size_left v l r hbst
        _ ≤ 3^(s.nodeCount - l.nodeCount-1 : ℝ) * 3 ^ l.nodeCount := by
            gcongr; apply lih; exact IsBST_left_of_ISBST l v r hbst
        _ = 3^(s.nodeCount - 1 : ℝ) := by
          rw [←Real.rpow_natCast 3]
          rw [←Real.rpow_add (show 0 < 3 by simp)]
          apply (Real.rpow_right_inj (by simp) (by simp)).mpr
          linarith
    have hr : size (static_weight (l △[v] r)) r ≤ 3^(s.nodeCount - 1 : ℝ) := by
      -- TODO: Almost exact duplication :(
      calc size (static_weight (l △[v] r)) r
          = 3^(s.nodeCount - r.nodeCount-1 : ℝ) * size (static_weight r) r := by
            exact static_weight_size_right v l r hbst
        _ ≤ 3^(s.nodeCount - r.nodeCount-1 : ℝ) * 3 ^ r.nodeCount := by
            gcongr; apply rih; exact IsBST_right_of_ISBST l v r hbst
        _ = 3^(s.nodeCount - 1 : ℝ) := by
          rw [←Real.rpow_natCast 3]
          rw [←Real.rpow_add (show 0 < 3 by simp)]
          apply (Real.rpow_right_inj (by simp) (by simp)).mpr
          linarith
    have : 3^s.nodeCount = (3 : ℝ) * 3^(s.nodeCount - 1 : ℝ) := by
      have := Real.rpow_add (show 0 < 3 by simp) (s.nodeCount-1) 1
      simp only [sub_add_cancel, Real.rpow_natCast, Real.rpow_one] at this
      simp only [this]; apply mul_comm
    linarith

-- TODO: Move?
lemma size_le_size_of_toKeyList_Sublist {w : α → ℝ} (hw : FnNonneg w)
    {s t : Tree α} (h : s.toKeyList.Sublist t.toKeyList) :
    size w s ≤ size w t := by
  rw [size_from_toKeyList, size_from_toKeyList]
  have : (List.map w s.toKeyList).Sublist (List.map w t.toKeyList) := by
    exact List.Sublist.map w h
  apply List.Sublist.sum_le_sum
  · exact List.Sublist.map w h
  · intro x hx
    have := List.mem_map.mp hx
    rcases this with ⟨y, _, hy⟩
    rw [←hy]; exact hw y

-- TODO: Need variant with t.toKeyList.Sublist s.toKeyList
private lemma static_weight_size_ub [LinearOrder α] (s t : Tree α)
    (hst : t.toKeyList.Sublist s.toKeyList) (hbst : s.IsBST) :
    size (static_weight s) t ≤ 3 ^ s.nodeCount := by
  have := size_le_size_of_toKeyList_Sublist (FnNonneg_of_FnPos (static_weight_pos s)) hst
  have := static_weight_size_self_ub s hbst
  linarith

private lemma static_weight_rank_ub [LinearOrder α] (s t : Tree α)
    (hst : t.toKeyList.Sublist s.toKeyList) (hbst : s.IsBST) :
    rank (static_weight s) t ≤ s.nodeCount * Real.logb 2 3 := by
  unfold rank; cases t with
  | nil =>
    simp only; apply mul_nonneg (by simp)
    · exact Real.logb_nonneg (by simp) (by simp)
  | node v l r =>
    simp only
    rw [←Real.logb_pow 2 3]; apply logb_mono
    · apply size_pos_of_non_nil (static_weight_pos s)
      simp
    · exact static_weight_size_ub s _ hst hbst

private lemma static_weight_φ_ub_aux [LinearOrder α] (s t : Tree α)
    (hst : t.toKeyList.Sublist s.toKeyList) (hbst : s.IsBST) :
    φ (static_weight s) t ≤ s.nodeCount * t.nodeCount * Real.logb 2 3 := by
  induction t with
  | nil => simp
  | node v l r lih rih =>
    simp [φ]
    have : l.toKeyList.Sublist s.toKeyList := by
      have : l.toKeyList.Sublist (node v l r).toKeyList := by simp [toKeyList]
      exact List.Sublist.trans this hst
    simp [this] at lih
    have : r.toKeyList.Sublist s.toKeyList := by
      have : r.toKeyList.Sublist (node v l r).toKeyList := by simp [toKeyList]
      exact List.Sublist.trans this hst
    simp [this] at rih
    have := static_weight_rank_ub s (node v l r) hst hbst
    linarith

private lemma static_weight_φ_ub [LinearOrder α] (s t : Tree α)
    (hst : s.toKeyList = t.toKeyList) (hbst : s.IsBST) :
    φ (static_weight s) t ≤ s.nodeCount^2 * Real.logb 2 3 := by
  calc φ (static_weight s) t ≤ s.nodeCount * t.nodeCount * Real.logb 2 3 := by
        apply static_weight_φ_ub_aux
        · rw [hst]
        · exact hbst
    _ ≤ s.nodeCount^2 * Real.logb 2 3 := by
      have : s.nodeCount = t.nodeCount := by
        simp [nodeCount_of_toKeyList, hst]
      rw [pow_two, this]


--------------------

private lemma static_rank_lb [LinearOrder α] (s t : Tree α) (ht : t ≠ nil) :
    -s.nodeCount * (Real.logb 2 3) ≤ rank (static_weight s) t := by
  let h := static_size_lb s t ht
  apply (Real.le_logb_iff_rpow_le _ _).mpr at h
  calc -s.nodeCount * Real.logb 2 3 = (Real.logb 2 3) * (-↑s.nodeCount) := by linarith
    _ ≤ (Real.logb 2 3) * Real.logb 3 (size (static_weight s) t) := by
      have : 0 < Real.logb 2 3 := by exact Real.logb_pos (by simp) (by simp)
      apply (mul_le_mul_iff_right₀ this).mpr
      apply (Real.le_logb_iff_rpow_le _ _).mpr
      · exact static_size_lb s t ht
      · simp
      · exact size_pos_of_non_nil (static_weight_pos s) t ht
    _ = Real.logb 2 (size (static_weight s) t) := by
      apply Real.mul_logb; all_goals linarith
    _ = rank (static_weight s) t := by simp [rank]

private lemma static_φ_lb [LinearOrder α] (s t : Tree α) (hst : s.nodeCount = t.nodeCount) :
    -s.nodeCount^2 * (Real.logb 2 3) ≤ φ (static_weight s) t := by
  induction t with
  | nil => simp [hst]
  | node v l r lih rih =>
    simp only [φ] -- TODO
    calc -↑s.nodeCount * ↑(l △[v] r).nodeCount * Real.logb 2 3 ≤
      -↑s.nodeCount * (1 + ↑l.nodeCount + ↑r.nodeCount) * Real.logb 2 3 := by simp
      _ ≤  -↑s.nodeCount * Real.logb 2 3 + φ (static_weight s) l + φ (static_weight s) r := by
        linarith
      _ ≤ rank (static_weight s) (l △[v] r) + φ (static_weight s) l + φ (static_weight s) r := by
        linarith [static_rank_lb s (node v l r) (by simp)]



theorem splay_tree_static_optimality [LinearOrder α] (n m : ℕ) (X : Fin m → α)
    (init s : Tree α) :
    splay.sequenceCost init X ≤ staticCost static X + s.nodeCount * init.nodeCount * (Real.logb 2 3)
    := by
  set ε := (3 : ℝ)^(-s.nodeCount : ℝ)
  have hε_pos : ε > 0 := by simp[ε]
  have hstw_lb : FnLb ε (static_weight s) := by intro x; unfold ε; exact static_weight_lb s x
  let φ_lb := -s.nodeCount * t.nodeCount * (Real.logb 2 3)
  have hφ := static_φ_lb s
  #check hφ
  have := splay_total_weighted_cost_lb' hε_pos hstw_lb hφ

end Weighted

end SplayTree
