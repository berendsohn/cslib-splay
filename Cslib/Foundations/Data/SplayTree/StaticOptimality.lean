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
private noncomputable def static_weight [LinearOrder α] (t : Tree α) (q : α) : ℝ :=
    3^(-searchPathLen t q : ℝ)

private lemma static_weight_pos [LinearOrder α] (t : Tree α) (q : α) : static_weight t q > 0 := by
  simp [static_weight]

-- TODO: Shouldn't be necessary
private lemma static_weight_lb [LinearOrder α] (t : Tree α) (q : α) :
    3^(-t.nodeCount : ℝ) ≤ static_weight t q := by
  simp only [static_weight, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  apply inv_pow_le_inv_pow_of_le (by simp)
  exact searchPathLen_le_nodeCount t q
-- TODO: Shouldn't be necessary

-- TODO: These inequalities are very loose, should improve

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
