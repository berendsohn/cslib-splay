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

-- TODO: Use 3^(t.nodeCount - searchPathLen t q) instead?
private noncomputable def static_weight [LinearOrder α] (s : Tree α) (q : α) : ℝ :=
    if q ∈ s then 3^(s.nodeCount - searchPathLen s q : ℝ) else 0

/-private lemma static_weight_pos [LinearOrder α] (s : Tree α) (q : α) : static_weight s q > 0 := by
  simp [static_weight]-/

private lemma static_weight_lb [LinearOrder α] (s : Tree α) (q : α) (hq : q ∈ s) :
    1 ≤ static_weight s q := by
  simp only [static_weight, hq]
  apply Real.one_le_rpow (by simp)
  simp only [sub_nonneg, Nat.cast_le]; exact searchPathLen_le_nodeCount s q

private lemma searchPathLen_left [LinearOrder α] (v : α) (l r : Tree α) (q : α) (hqv : q < v) :
    searchPathLen (node v l r) q = 1 + searchPathLen l q := by
  simp [searchPathLen, hqv]

private lemma static_weight_left [LinearOrder α] (v : α) (l r : Tree α)
    (hbst : (node v l r).IsBST) (q : α) :
    static_weight l q ≤ 3 * static_weight (node v l r) q := by
  simp only [static_weight, nodeCount_node, Nat.cast_add, Nat.cast_one, searchPathLen]
  have h3: ∀ x : ℝ, (3 : ℝ) ^ (x + 1) = 3 * 3 ^ x := by
    intro x;  rw [Real.rpow_add (by simp)]; linarith
  if h : q ∈ l then
    have : q < v := lt_of_IsBST_left l v r q hbst h
    simp only [h, ↓reduceIte, mem_node_iff, true_or, or_true, this, Nat.cast_add, Nat.cast_one,
      ge_iff_le]
    rw [←h3]; apply Real.rpow_le_rpow_of_exponent_le (by simp); linarith
  else
    simp only [h, ↓reduceIte, mem_node_iff, false_or, Nat.cast_ite, Nat.cast_add, Nat.cast_one,
      mul_ite, mul_zero, ge_iff_le]
    if h' : q = v ∨ q ∈ r then
      simp only [h', ↓reduceIte, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
      apply Real.rpow_nonneg (by simp)
    else
      simp [h']

private lemma static_weight_size_left [LinearOrder α]
    (v : α) (l r : Tree α) (hbst : (node v l r).IsBST) :
    size (static_weight l) l ≤ 3 * size (static_weight (node v l r)) l := by
  simp only [size_from_toKeyList]
  --have hbst' : l.IsBST := by exact IsBST_left_of_ISBST l v r hbst
  induction l.toKeyList with
  | nil => simp
  | cons x xs ih =>
    have := static_weight_left v l r hbst x
    simp; linarith [this, ih]

-- TODO: awful, awful duplication
private lemma searchPathLen_right [LinearOrder α] (v : α) (l r : Tree α) (q : α) (hqv : v < q) :
    searchPathLen (node v l r) q = 1 + searchPathLen r q := by
  simp [searchPathLen, hqv, Std.not_gt_of_lt hqv]

private lemma static_weight_right [LinearOrder α] (v : α) (l r : Tree α)
    (hbst : (node v l r).IsBST) (q : α) :
    static_weight r q ≤ 3 * static_weight (node v l r) q := by
  simp only [static_weight, nodeCount_node, Nat.cast_add, Nat.cast_one, searchPathLen]
  have h3: ∀ x : ℝ, (3 : ℝ) ^ (x + 1) = 3 * 3 ^ x := by
    intro x;  rw [Real.rpow_add (by simp)]; linarith
  if h : q ∈ r then
    have hvq : v < q := gt_of_IsBST_right l v r q hbst h
    have hvq' : ¬ q < v := Std.not_gt_of_lt hvq
    simp only [h, ↓reduceIte, mem_node_iff, or_true, hvq', hvq, Nat.cast_add, Nat.cast_one,
      ge_iff_le]
    rw [←h3]; apply Real.rpow_le_rpow_of_exponent_le (by simp); linarith
  else
    simp only [h, ↓reduceIte, mem_node_iff, Nat.cast_ite, Nat.cast_add, Nat.cast_one,
      mul_ite, mul_zero, ge_iff_le]
    if h' : q = v ∨ q ∈ l then
      simp only [or_false, h', ↓reduceIte, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
      apply Real.rpow_nonneg (by simp)
    else
      simp [h']

private lemma static_weight_size_right [LinearOrder α]
    (v : α) (l r : Tree α) (hbst : (node v l r).IsBST) :
    size (static_weight r) r ≤ 3 * size (static_weight (node v l r)) r := by
  simp only [size_from_toKeyList]
  induction r.toKeyList with
  | nil => simp
  | cons x xs ih =>
    have := static_weight_right v l r hbst x
    simp; linarith [this, ih]

private lemma size_sum (t : Tree α) (w : α → ℝ) :
    size w t = ∑ x ∈ t.toKeyList, w x := sorry

private lemma static_weight_size_ub [LinearOrder α] (s t : Tree α) :
    size (static_weight s) s ≤ 3^s.nodeCount := by
  induction s with
  | nil => simp
  | node v l r lih rih =>
    simp
    have : size (static_weight (node v l r)) l = ?

private lemma static_size_lb [LinearOrder α] (s t : Tree α) (ht : t ≠ nil) :
    3^(-s.nodeCount : ℝ) ≤ size (static_weight s) t := by
  have hw : FnNonneg (static_weight s) := by intro x; linarith [static_weight_pos s x]
  cases t with
  | nil => contradiction
  | node v l r =>
    simp only [size_node]; linarith [static_weight_lb s v, size_nonneg hw l, size_nonneg hw r]

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
