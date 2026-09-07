/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai, Benjamin Aram Berendsohn
-/

module

public import Cslib.Foundations.Data.SplayTree.Basic
public import Cslib.Foundations.Data.SplayTree.Complexity
public import Cslib.Foundations.Data.SplayTree.Correctness
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Weighted Bounds of Splay Trees

TODO
-/

@[expose] public section

variable {α : Type}

namespace SplayTree

open Tree

namespace Weighted

section WeightedPotentialMethod

/-- Size of a tree: total weight of all nodes. -/
def size (w : α → ℝ) : Tree α → ℝ
  | nil => (0 : ℝ)
  | node b l r => w b + size w l + size w r

/-- A valid weight function maps to positive reals. -/
def WeightFunc (w : α → ℝ) : Prop :=
  ∀ x, 1 ≤ w x

/-- Rank of a tree: `log_2(nodeCount)`, or 0 for the empty tree. -/
noncomputable def rank (w : α → ℝ) (t : Tree α) : ℝ :=
  match t with
    | nil => 0
    | _ => Real.logb 2 (size w t)

/-- Potential of a tree: sum of ranks over all subtrees (including itself). -/
noncomputable def φ (w : α → ℝ) : Tree α → ℝ
  | .nil => 0
  | s@(l △[_] r) => rank w s + φ w l + φ w r


/-! #### Basic size, rank, and potential lemmas -/

variable {w : α → ℝ}

@[simp] lemma size_empty : size w (.nil : Tree α) = 0 := by simp only [size]
@[simp] lemma size_node : size w (node v l r : Tree α) = w v + size w l + size w r :=
  by simp only [size]

@[simp] theorem size_rotateRight (t : Tree α) :
    size w (rotateRight t) = size w t := by
  rcases t with _ | ⟨k, (_ | ⟨lk, ll, lr⟩), r⟩ <;>
    simp [rotateRight]; linarith

@[simp] theorem size_rotateLeft (t : Tree α) :
    size w (rotateLeft t) = size w t := by
  rcases t with _ | ⟨k, l, (_ | ⟨rk, rl, rr⟩)⟩ <;>
    simp [rotateLeft]; linarith

@[simp]
theorem size_bringUp (d : Dir) (t : Tree α) :
    size w (d.bringUp t) = size w t := by
  cases d <;> simp [Dir.bringUp]

@[simp]
theorem size_applyChild (d : Dir) (op : Tree α → Tree α)
    (hop : ∀ s, size w (op s) = size w s) (t : Tree α) :
    size w (applyChild d op t) = size w t := by
  cases t with
  | nil => rfl
  | node k l r =>
    cases d <;> simp [applyChild, hop]

lemma size_nonneg (hw : WeightFunc w) (t : Tree α) : 0 ≤ size w t := by
  induction t with
  | nil => simp [size_empty]
  | node v l r =>
    unfold size
    linarith [hw v]

lemma size_ge_root_value (hw : WeightFunc w) (v : α) (l r : Tree α) :
    w v ≤ size w (node v l r) := by
  unfold size
  linarith [size_nonneg hw l, size_nonneg hw r]

lemma size_ge_left_child (hw : WeightFunc w) (v : α) (l r : Tree α) :
    size w l ≤ size w (node v l r) := by
    simp[size_node]; linarith [hw v, size_nonneg hw r]

lemma size_ge_right_child (hw : WeightFunc w) (v : α) (l r : Tree α) :
    size w r ≤ size w (node v l r) := by
    simp[size_node]; linarith [hw v, size_nonneg hw l]

lemma size_pos_of_non_nil (hw : WeightFunc w) (t : Tree α) (h : t ≠ nil) : 0 < size w t := by
  cases t with
  | nil => by_contra; apply h; rfl
  | node v l r =>
    linarith [hw v, size_ge_root_value hw v l r]

lemma size_from_toKeyList (t : Tree α) :
  size w t = (t.toKeyList.map w).sum := by
  induction t with
  | nil => simp[size, toKeyList]
  | node a l r =>
    simp [size, toKeyList]
    linarith

lemma size_zero_iff_empty (hw : WeightFunc w) (t : Tree α) : size w t = 0 ↔ t = nil := by
  constructor
  · unfold size
    cases t with
    | nil => intro h; rfl
    | node v l r =>
      simp only [reduceCtorEq, imp_false]
      linarith [size_nonneg hw l, size_nonneg hw r, hw v]
  · intro h; simp [h]

lemma size_Frame_attach (s : Tree α) (f : Frame α) :
    size w (f.attach s) = size w s + w f.key + size w f.sibling := by
  simp [Frame.attach]
  cases f.dir; all_goals simp; linarith

@[simp] lemma size_splay [LinearOrder α] (s : Tree α) (q : α) : size w (splay s q) = size w s := by
  rw [size_from_toKeyList, size_from_toKeyList]; rw [toKeyList_splay]

@[simp] lemma rank_empty : rank w (.nil : Tree α) = 0 :=
  by simp [rank]

lemma rank_nonneg (hw : WeightFunc w) (t : Tree α) : 0 ≤ rank w t := by
  unfold rank; cases t with
  | nil => simp
  | node v l r =>
    simp only [size_node]
    have : w v + size w l + size w r ≥ 1 := by
      linarith [hw v, size_nonneg hw l, size_nonneg hw r]
    exact Real.logb_nonneg (show 1 < (2 : ℝ) by simp) this

-- TODO: Ridiculously long proof
lemma rank_le_of_size_le (hw : WeightFunc w) (s t : Tree α) (h : size w s ≤ size w t) :
    rank w s ≤ rank w t := by
  unfold rank
  cases s <;> cases t <;>
    all_goals simp only
  · rfl
  · expose_names
    apply Real.logb_nonneg (show 1 < 2 by simp); simp [size]
    linarith [hw value, size_nonneg hw left, size_nonneg hw right]
  · expose_names
    simp [size] at h
    linarith [hw value, size_nonneg hw left, size_nonneg hw right]
  · expose_names
    apply SplayTree.logb_mono
    · simp; linarith [hw value, size_nonneg hw left, size_nonneg hw right]
    · linarith [h]

@[simp] lemma φ_empty : φ w (.nil : Tree α) = 0 := rfl

@[simp] lemma φ_node (l : Tree α) (k : α) (r : Tree α) :
    φ w (l △[k] r) = rank w (l △[k] r) + φ w l + φ w r := rfl

lemma φ_nonneg (hw : WeightFunc w) (t : Tree α) : 0 ≤ φ w t := by
  induction t with
  | nil => rfl
  | node k l r => simp [φ]; linarith [rank_nonneg hw (l △[k] r), φ_nonneg hw l, φ_nonneg hw r]

lemma rank_eq_of_toKeyList_eq {s t : Tree α}
  (h : s.toKeyList = t.toKeyList) : rank w s = rank w t := by
  simp only [rank]
  cases s with
  | nil =>
    simp only
    simp only [toKeyList, List.nil_eq] at h
    rw [size_from_toKeyList, h, List.map_nil, List.sum_nil]
    rw [toKeyList_of_empty h]
  | node v l r =>
    have : t.toKeyList ≠ [] := by rw [←h]; simp
    have : t ≠ nil := by contrapose this; rw [this]; exact toKeyList_empty
    simp only; rw [size_from_toKeyList, size_from_toKeyList, h]

@[simp] lemma rank_splay [LinearOrder α] (w : α → ℝ) (t : Tree α) (q : α) :
    rank w (splay t q) = rank w t :=
  rank_eq_of_toKeyList_eq (toKeyList_splay t q)


/-! #### Potential of subtrees versus the whole tree -/

theorem φ_subtree_le_left (hw : WeightFunc w) (l : Tree α) (k : α) (r : Tree α) :
    φ w l + φ w r ≤ φ w (l △[k] r) := by
  simp [φ]; linarith [rank_nonneg hw (l △[k] r), φ_nonneg hw r]

/-theorem φ_subtree_le_right (l : Tree α) (k : α) (r : Tree α) :
    φ w r ≤ φ w (l △[k] r) := by
  simp [φ]; linarith [rank_nonneg (l △[k] r), φ_nonneg l]-/

theorem φ_le_attach (hw : WeightFunc w) (c : Tree α) (f : Frame α) :
  φ w c ≤ φ w (f.attach c) := by
  cases f with | mk d k s =>
  cases d <;> simp [Frame.attach, φ_node] <;>
  linarith [rank_nonneg hw (c △[k] s), rank_nonneg hw (s △[k] c),
  φ_nonneg hw c, φ_nonneg hw s]

theorem φ_le_reassemble (hw : WeightFunc w) (c : Tree α) (path : List (Frame α)) :
    φ w c ≤ φ w (reassemble c path) := by
  induction path generalizing c with
  | nil => simp
  | cons f rest ih => simp only [reassemble_cons]; exact le_trans (φ_le_attach hw c f) (ih _)

theorem φ_descend_subtree_le [LinearOrder α] (hw : WeightFunc w) (t : Tree α) (q : α) :
    φ w (descend t q).1 ≤ φ w t := by
  have h := descend_preserves_tree t q
  calc φ w (descend t q).1
      ≤ φ w (reassemble (descend t q).1 (descend t q).2) :=
        φ_le_reassemble hw _ _
    _ = φ w t := by rw [h]


/-! #### Mirror preserves rank and potential -/

lemma rank_mirror (t : Tree α) : rank w t.mirror = rank w t := by
  cases t
  · simp [rank]
  · simp only [rank, mirror_node, size_from_toKeyList, toKeyList_node, toKeyList_mirror,
    List.append_assoc, List.cons_append, List.nil_append, List.map_append, List.map_reverse,
    List.map_cons, List.sum_append, List.sum_reverse, List.sum_cons]
    apply congr
    · rfl
    · linarith


lemma φ_mirror (t : Tree α) : φ w t.mirror = φ w t := by
  induction t with
  | nil => rfl
  | node v r l =>
    rw [mirror_node, φ_node, φ_node, ← mirror, rank_mirror]
    simp_all; linarith

/-- Transfer a potential-step inequality from mirrored trees to the originals. -/
private lemma φ_transfer_mirror
    {step s c step' s' : Tree α}
    (hstep : step.mirror = step')
    (hs : s.mirror = s')
    (h : φ w step' - φ w s' + 2 ≤
      3 * (rank w step' - rank w c.mirror)) :
    φ w step - φ w s + 2 ≤ 3 * (rank w step - rank w c) := by
  rw [← hstep, φ_mirror, rank_mirror] at h
  rw [← hs, φ_mirror, rank_mirror c] at h
  assumption


/-! #### Splay step potential bounds -/

theorem φ_zig (hw : WeightFunc w) (c : Tree α) (f : Frame α) :
    φ w (f.dir.bringUp (f.attach c)) - φ w (f.attach c) ≤
      rank w (f.dir.bringUp (f.attach c)) - rank w c := by
  rcases f with ⟨d, key, sib⟩
  rcases c with _ | ⟨k, l, r⟩ <;> cases d <;>
    all_goals simp only [Dir.bringUp, rotateLeft, rotateRight,
    Frame.attach, φ_node, φ_empty, add_zero, sub_self, rank_empty, sub_zero]
  -- empty: 0 ≤ rank t; node: rank(child) ≤ rank(parent)
  · exact rank_nonneg hw _
  · exact rank_nonneg hw _
  · have : rank w (r △[key] sib) ≤ rank w ((l △[k] r) △[key] sib) := by
      apply rank_le_of_size_le hw
      simp [size_node]; linarith [hw k, size_nonneg hw l]
    linarith
  · have : rank w (sib △[key] l) ≤ rank w (sib △[key] (l △[k] r)) := by
      apply rank_le_of_size_le hw
      simp [size_node]; linarith [hw k, size_nonneg hw l, size_nonneg hw r]
    linarith

private theorem φ_zigzig_left (hw : WeightFunc w)
    (a b c : α) (t1 t2 t3 t4 : Tree α) :
    let x := node a t1 t2 -- The node we're rotating
    let s := node c (node b x t3) t4 -- The initial tree
    let s' := rotateRight (rotateRight s) -- The resulting tree
    φ w s' - φ w s + 2 ≤ 3 * (rank w s' - rank w x) := by
  -- TODO: Avoid repeating definitions?
  let x := node a t1 t2
  let s := node c (node b x t3) t4
  let s' := rotateRight (rotateRight s)
  let φ_children := φ w t1 + φ w t2 + φ w t3 + φ w t4
  -- Write out the potentials of both trees
  have : φ w s = rank w s + rank w (node b x t3) + rank w x + φ_children := by
    unfold s φ_children x; simp [φ_node]; linarith
  let x' := node c t3 t4
  have : φ w s' = rank w s' + rank w (node b t2 x') + rank w x' + φ_children := by
    unfold s' φ_children x' s rotateRight x; simp; linarith
  -- Total rank stays the same
  have : rank w s = rank w s' := by
    apply rank_eq_of_toKeyList_eq
    unfold s'; simp only [toKeyList_rotateRight]
  -- The calculation
  --have : φ w s' - φ w s = rank w (node b t2 x') + rank w x' - rank w (node b x t3) - rank w x := by
  --  linarith
  have : rank w (node b t2 x') ≤ rank w s' := by
    unfold s' s rotateRight x x'; simp only; apply rank_le_of_size_le hw
    exact size_ge_right_child hw _ _ _
  have : rank w x ≤ rank w (node b x t3) := by
    apply rank_le_of_size_le hw; apply size_ge_left_child hw
  --have : φ w s' - φ w s ≤ rank w s' + rank w x' - 2 * rank w x := by
  --  linarith
  have : rank w x + rank w x' ≤ 2 * rank w s' - 2 := by
    simp only [rank, reduceCtorEq, imp_self, (show s' ≠ nil by simp [s', rotateRight])]
    apply log_sum_le
    · exact size_pos_of_non_nil hw x (show x ≠ nil by simp)
    · exact size_pos_of_non_nil hw x' (show x' ≠ nil by simp)
    · unfold s' rotateRight s x x'; simp; linarith [hw b]
  linarith

theorem φ_zigzig (hw : WeightFunc w) (a : α) (l r : Tree α) (f1 f2 : Frame α)
    (heq : f1.dir = f2.dir) :
    let c := node a l r
    let s := f2.attach (f1.attach c)
    let step := f2.dir.bringUp (f2.dir.bringUp s)
    φ w step - φ w s + 2 ≤ 3 * (rank w step - rank w c) := by
  let c := node a l r
  rcases f1 with ⟨d, k1, n1⟩; rcases f2 with ⟨_, k2, n2⟩; subst heq
  cases d
  · exact φ_zigzig_left hw a k1 k2 l r n1 n2
  · have h := φ_zigzig_left hw a k1 k2 r.mirror l.mirror n1.mirror n2.mirror
    simp only [Frame.attach, Dir.bringUp, rotateRight, rotateLeft] at h ⊢
    repeat rw [← mirror] at h
    simp only [φ_mirror, rank_mirror] at h
    assumption

private theorem φ_zigzag_left (hw : WeightFunc w)
    (a b c : α) (t1 t2 t3 t4 : Tree α) :
    let x := node b t2 t3 -- The node we're rotating
    let s := node a t1 (node c x t4) -- The initial tree
    let s' := rotateLeft (applyChild .R rotateRight s) -- The resulting tree
    φ w s' - φ w s + 2 ≤ 3 * (rank w s' - rank w x) := by
  -- TODO: Avoid repeating definitions?
  let x := node b t2 t3 -- The node we're rotating
  let s := node a t1 (node c x t4) -- The initial tree
  let s' := rotateLeft (applyChild .R rotateRight s) -- The resulting tree
  let φ_children := φ w t1 + φ w t2 + φ w t3 + φ w t4
  -- Write out the potentials of both trees
  have : φ w s = rank w s + rank w (node c x t4) + rank w x + φ_children := by
    unfold s φ_children x; simp; linarith
  have : φ w s' = rank w s' + rank w (node a t1 t2) + rank w (node c t3 t4) + φ_children := by
    unfold s' s applyChild rotateLeft rotateRight x φ_children; simp; linarith
  -- Total rank stays the same
  have : rank w s = rank w s' := by
    apply rank_eq_of_toKeyList_eq
    unfold s'; simp [toKeyList_rotateRight]
  -- The calculation
  have : φ w s' - φ w s = (
      rank w (node a t1 t2) + rank w (node c t3 t4) - rank w (node c x t4) - rank w x ) := by
    linarith
  have : rank w x ≤ rank w (node c x t4) := by
    apply rank_le_of_size_le hw; apply size_ge_left_child hw
  have : rank w (node a t1 t2) + rank w (node c t3 t4) ≤ 2 * rank w s' - 2 := by
    simp only [rank, size_node, imp_self,
      (show s' ≠ nil by simp [s', rotateLeft, applyChild, rotateRight])]
    apply log_sum_le
    · linarith [hw a, size_nonneg hw t1, size_nonneg hw t2]
    · linarith [hw c, size_nonneg hw t3, size_nonneg hw t4]
    · unfold s' applyChild rotateRight rotateLeft s x; simp; linarith [hw b]
  have : rank w x ≤ rank w s' := by
    simp only [s', s, applyChild, x, rotateRight, rotateLeft]; apply rank_le_of_size_le hw
    simp; linarith [hw a, hw c, size_nonneg hw t1, size_nonneg hw t4]
  linarith


theorem φ_zigzag (hw : WeightFunc w) (a : α) (l r : Tree α) (f1 f2 : Frame α)
    (hne : f1.dir ≠ f2.dir) :
    let c := node a l r
    let s := f2.attach (f1.attach c)
    let step := f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
    φ w step - φ w s + 2 ≤ 3 * (rank w step - rank w c) := by
  let c := node a l r
  rcases f1 with ⟨d1, k1, n1⟩; rcases f2 with ⟨d2, k2, n2⟩
  cases d1 <;> cases d2 <;> simp_all +decide only [ne_eq]
  · exact φ_zigzag_left hw k2 a k1 n2 l r n1
  · have h := φ_zigzag_left hw k2 a k1 n2.mirror r.mirror l.mirror n1.mirror
    simp only [Frame.attach, Dir.bringUp, rotateRight, rotateLeft, applyChild] at h ⊢
    repeat rw [← mirror] at h
    simp only [φ_mirror, rank_mirror] at h
    assumption


/-! #### Telescoping: potential change along the full splayUp -/

lemma φ_attach_congr {s s' : Tree α} (f : Frame α)
    (h : size w s = size w s') :
    φ w (f.attach s') - φ w (f.attach s) = φ w s' - φ w s := by
  cases f with | mk d k sib =>
  cases d <;> simp only [Frame.attach, φ_node, add_sub_add_right_eq_sub] <;>
    (unfold rank; simp [h])

lemma φ_reassemble_congr {s s' : Tree α} (path : List (Frame α))
    (h : size w s = size w s') :
    φ w (reassemble s' path) - φ w (reassemble s path) = φ w s' - φ w s := by
  induction path generalizing s s' with
  | nil => simp
  | cons f rest ih =>
    simp only [reassemble_cons]
    rw [ih (by simp [size_Frame_attach, h])]
    exact φ_attach_congr f h

/-- The total potential change of splayUp plus the path length is at
    most 3 × the rank increase + 1. -/
theorem φ_splayUp (hw : WeightFunc w) (c : Tree α) (hc : c ≠ nil) (path : List (Frame α)) :
    φ w (splayUp c path) - φ w (reassemble c path) + path.length ≤
      3 * (rank w (splayUp c path) - rank w c) + 1 := by
  induction c, path using splayUp_induction with
  | nil c => simp
  | single c f =>
    simp only [splayUp_singleton, reassemble_cons,
      reassemble_nil, List.length_singleton, Nat.cast_one]
    have : rank w (f.dir.bringUp (Frame.attach c f)) = rank w (Frame.attach c f) := by
      simp only [Dir.bringUp]; cases f.dir
      all_goals simp only; apply rank_eq_of_toKeyList_eq
      · apply toKeyList_rotateRight
      · apply toKeyList_rotateLeft
    have : rank w c ≤ rank w (f.dir.bringUp (Frame.attach c f)) := by
      rw [this]; simp only [Frame.attach]; cases f.dir;
        all_goals simp only; apply rank_le_of_size_le hw
      · apply size_ge_left_child hw
      · apply size_ge_right_child hw
    linarith [φ_zig hw c f]
  | step c f1 f2 rest ih =>
    cases c with
    | nil =>
      contradiction -- TODO: Shorter?
      /-simp only [splayUp_niltree]
      set c' := (f2.dir.bringUp (Frame.attach (Frame.attach nil f1) f2))
      simp only [reassemble_cons, List.length_cons, Nat.cast_add, Nat.cast_one, rank_empty,
        sub_zero]
      #check ih c'

      simp [splayUp, Frame.attach, Dir.bringUp]; cases f1.dir <;> cases f2.dir
      all_goals simp [rotateRight, rotateLeft]
      · apply ih-/
    | node a l r =>
      rw [splayUp_cons_cons]; simp only [List.length_cons]
      split_ifs with hdir
      · set s := f2.attach (f1.attach (node a l r))
        set step_tree := f2.dir.bringUp (f2.dir.bringUp s)
        have hsize : size w step_tree = size w s := by
          simp [step_tree]
        simp only [reassemble_cons]; push_cast
        have : step_tree ≠ nil := by
          unfold step_tree; apply Dir.bringUp_ne_nil_of_ne_nil; apply Dir.bringUp_ne_nil_of_ne_nil
          unfold s; apply Frame.attach_ne_nil
        nlinarith [ih step_tree this,
          φ_reassemble_congr rest hsize.symm, φ_zigzig hw a l r f1 f2 hdir]
      · set s := f2.attach (f1.attach (node a l r))
        set step_tree := f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
        have hsize : size w step_tree = size w s := by
          simp [step_tree]
        simp only [reassemble_cons]; push_cast
        have : step_tree ≠ nil := by
          unfold step_tree; apply Dir.bringUp_ne_nil_of_ne_nil;
          apply Dir.applyChild_ne_nil_of_ne_nil
          unfold s; apply Frame.attach_ne_nil
        nlinarith [ih step_tree this,
          φ_reassemble_congr rest hsize.symm, φ_zigzag hw a l r f1 f2 hdir]

/-! #### The main amortized bound -/

/-private lemma rank_eq_logb {t : Tree α}
    (h : t.nodeCount ≠ 0) :
    rank w t = Real.logb 2 (size w t) := by
  have : t ≠ nil := by linarith[h]
  simp [rank, h]-/

/-private lemma nodeCount_pos_of_descend_nonempty_path
    [LinearOrder α] {t : Tree α} {q : α}
    {reached : Tree α} {path : List (Frame α)}
    (hdecomp : descend t q = (reached, path))
    (hpath : path ≠ []) : t.nodeCount ≠ 0 := by
  intro h0
  have hd := nodeCount_descend t q
  rw [hdecomp] at hd; simp at hd
  rcases path with _ | ⟨f, rest⟩
  · exact hpath rfl
  · simp [pathNodes, Frame.nodes] at hd; omega-/

/-- Slighly weaker version of Sleator and Tarjan's access lemma: Does not take into account the
  subtree rooted at q, only the weight of q itself. -/
theorem splay_access_lemma [LinearOrder α]
    (hw : WeightFunc w) (t : Tree α) (q : α) (hbst : IsBST t) (hq : q ∈ t) :
    φ w (splay t q) - φ w t + splay.cost t q ≤
      3 * Real.logb 2 ( (size w t) / w q ) + 1 := by
  rcases hdecomp : descend t q with ⟨reached, path⟩
  have : ∃ l r, (descend t q).1 = node q l r := descend_contains' t q hbst hq
  have hreached : ∃ l r, reached = node q l r := by simp_all only
  have hpres := descend_preserves_tree t q
  rw [hdecomp] at hpres; simp only at hpres
  rcases hreached with ⟨l,r,hreached⟩
  have h_splay : splay t q = splayUp reached path ∨
      (∃ f rest, reached = .nil ∧
        path = f :: rest ∧
        splay t q = splayUp (f.attach .nil) rest) := by
    simp only [splay, hdecomp]
    rw [hreached]; simp
  have h_cost : splay.cost t q = path.length := by simp [splay.cost, hdecomp, hreached]
  rw [h_cost]
  have h_eq : splay t q = splayUp (l △[q] r) path := by simp [splay, hdecomp, hreached]
  rw [h_eq]
  have hφ := φ_splayUp hw (l △[q] r) (by simp) path
  rw [←hreached, hpres, hreached] at hφ
  have hrank_eq : rank w (splayUp (l △[q] r) path) = rank w t := by
    have h := rank_splay w t q; simp only [splay, hdecomp, hreached] at h; exact h
  have htnn : t ≠ nil := nonnil_of_mem q hq
  calc φ w (splayUp (l △[q] r) path) - φ w t + ↑path.length
      ≤ 3 * (rank w (splayUp (l △[q] r) path) - rank w (l △[q] r)) + 1 := by exact_mod_cast hφ
    _ ≤ 3 * (rank w t - rank w (l △[q] r)) + 1 := by simp [hrank_eq]
    _ ≤ 3 * ( Real.logb 2 ( size w t ) - rank w (l △[q] r)) + 1 := by simp [rank]
    _ ≤ 3 * ( Real.logb 2 ( size w t ) - Real.logb 2 (w q)) + 1 := by
      have : Real.logb 2 (w q) ≤ rank w (l △[q] r) := by
        simp only [rank, size_node]; apply logb_mono (by linarith [hw q])
        linarith [size_nonneg hw l, size_nonneg hw r]
      linarith
    _ ≤ 3 * Real.logb 2 ( (size w t) / w q ) + 1 := by
      have hsizepos: size w t ≠ 0 := by linarith [size_pos_of_non_nil hw t htnn]
      have hwqpos: w q ≠ 0 := by linarith [hw q]
      simp [Real.logb_div hsizepos hwqpos]


end WeightedPotentialMethod


/-! ### Entropy bound -/
section EntropyBound

--variable {w : α → ℝ}

/-! #### Sequence cost with fixed weight function -/

theorem total_cost_bound {S : Type*} (m : ℕ)
    (s : Fin (m + 1) → S) (cost : Fin m → ℝ)
    (Φ : S → ℝ) (B : Fin m → ℝ)
    (hamort : ∀ i : Fin m,
      Φ (s i.succ) - Φ (s i.castSucc) + cost i ≤ B i) :
    ∑ i : Fin m, cost i ≤
      ∑ i : Fin m, (B i) + Φ (s 0) - Φ (s (Fin.last m)) := by
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    hamort i
  simp_all +decide only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ge_iff_le]
  linarith! [Fin.sum_univ_castSucc fun i => Φ (s i),
    Fin.sum_univ_succ fun i => Φ (s i)]

theorem total_cost_bound' {S : Type*} (m : ℕ)
    (s : Fin (m + 1) → S) (cost : Fin m → ℝ)
    (Φ : S → ℝ) (B : Fin m → ℝ)
    (hamort : ∀ i : Fin m,
      Φ (s i.succ) - Φ (s i.castSucc) + cost i ≤ B i) :
    ∑ i : Fin m, cost i ≤ ∑ i : Fin m, (B i) + Φ (s 0) - Φ (s (Fin.last m)) := by
  linarith [total_cost_bound m s cost Φ B hamort]

theorem total_cost_bound'' {S : Type*} (m : ℕ)
    (s : Fin (m + 1) → S) (cost : Fin m → ℝ)
    (Φ : S → ℝ) (B : Fin m → ℝ)
    (hamort : ∀ i : Fin m,
      Φ (s i.succ) - Φ (s i.castSucc) + cost i ≤ B i)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x) :
    ∑ i : Fin m, cost i ≤ ∑ i : Fin m, (B i) + Φ (s 0) := by
  linarith [total_cost_bound m s cost Φ B hamort,
    hΦ_nonneg (s (Fin.last m))]

theorem splay_total_weighted_cost' [LinearOrder α]
    (w : α → ℝ) -- TODO
    (hw : WeightFunc w)
    (m : ℕ)
    (t : Fin (m + 1) → Tree α)
    (q : Fin m → α)
    (hseq : ∀ i : Fin m, t i.succ = splay (t i.castSucc) (q i))
    (hbst : (t 0).IsBST)
    (hcont : ∀ i : Fin m, (q i) ∈ (t 0)) :
    ∑ i : Fin m, (splay.cost (t i.castSucc) (q i) : ℝ) ≤
    ∑ i : Fin m, (3 * Real.logb 2 ( size w (t 0) / w (q i) ) + 1) + φ w (t 0) - φ w (t (Fin.last m))
    := by
  -- TODO: want  - φ w (t (Fin.last m)) for later arbitrary-weight theorem
  cases m with
  | zero => simp --[φ_nonneg hw]
  | succ m' =>
    let m := m'+1
    let B := fun i => (3 * Real.logb 2 ( size w (t 0) / w (q i) ) + 1)
    have hbst' : ∀ i : Fin (m+1), (t i).IsBST := by
      intro i
      induction i using Fin.induction with
      | zero => exact hbst
      | succ i ih => rw [hseq i]; apply IsBST_splay; exact ih
    have hcont' : ∀ (i : Fin m) (j : Fin (m+1)), (q i) ∈ (t j) := by
      intro i j
      induction j using Fin.induction with
      | zero => apply hcont
      | succ j jh =>
        rw [hseq j]
        apply mem_iff_mem_toKeyList.mpr; simp only [toKeyList_splay]; apply mem_iff_mem_toKeyList.mp
        exact jh
    have hnn' : ∀ i : Fin (m+1), (t i) ≠ nil := by
      intro i; exact nonnil_of_mem (q 0) (hcont' 0 i)
    have hsize : ∀ i : Fin (m+1), size w (t i) = size w (t 0) := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih => rw [hseq, size_splay]; exact ih
    apply total_cost_bound' m t (fun i => (splay.cost (t i.castSucc) (q i) : ℝ)) (φ w) B
    intro i
    rw [hseq i]
    have hb := splay_access_lemma hw (t i.castSucc) (q i) (hbst' i.castSucc) (hcont' i i.castSucc)
    calc φ w (splay (t i.castSucc) (q i)) - φ w (t i.castSucc) +
          splay.cost (t i.castSucc) (q i)
      ≤ 3 * Real.logb 2 (size w (t i.castSucc) / w (q i)) + 1 := hb
    _ ≤ 3 * Real.logb 2 (size w (t 0) / w (q i)) + 1 := by rw[hsize i.castSucc]

def FnPositive (w : α → ℝ) : Prop :=
  ∀ x, 0 < w x

def FnLb (b : ℝ) (w : α → ℝ) : Prop :=
  ∀ x, b ≤ w x


theorem splay_total_weighted_cost [LinearOrder α] [Fintype α]
    {w : α → ℝ}
    {ε : ℝ} (heps : ε > 0) (hw : FnLb ε w)
    (m : ℕ)
    (t : Fin (m + 1) → Tree α)
    (q : Fin m → α)
    (hseq : ∀ i : Fin m, t i.succ = splay (t i.castSucc) (q i))
    (hbst : (t 0).IsBST)
    (hcont : ∀ i : Fin m, (q i) ∈ (t 0))
    :
    ∑ i : Fin m, (splay.cost (t i.castSucc) (q i) : ℝ) ≤
    ∑ i : Fin m, (3 * Real.logb 2 ( size w (t 0) / w (q i) ) + 1)
      + φ w (t 0) - φ w (t (Fin.last m)) := by
  let w' := fun x => (w x) / ε
  have hw': WeightFunc w' := by
    unfold WeightFunc; intro x; simp [w']; field_simp [heps]; exact hw x

  #check splay_total_weighted_cost' w' hw' m t q hseq hbst hcont
  /-apply splay_total_weighted_cost' w'
  · exact hw'-/

-- TODO: Try to generalize this to arbitrary positive weight functions

-- TODO: Give up on entropy, try static optimality based on
--   https://11011110.github.io/blog/2008/02/07/static-optimality-for.html

/-def freqCost (freq : ℕ) (m : ℕ) :=
  match freq with
  | .zero => 0
  | .succ i => m / (i+1)

noncomputable def entropy [Fintype α] (X : Fin m → α) :=
  ∑ x, freqCost (X ⁻¹' {x}).ncard m-/

/-
/-- Weight function for the entropy bound -/
noncomputable def entropy_weight [Fintype α] (X : Fin m → α) (x : α) :=
  (m : ℝ) / (X ⁻¹' {x}).ncard

private lemma div_ge_1_of_pos_of_le {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : (1 ≤ b/a) := by
  field_simp; exact h

lemma entropy_weight_ge_one [Fintype α] (X : Fin m → α) (hs : Function.Surjective X) (x : α) :
    entropy_weight X x ≥ 1 := by
  set pre := (X ⁻¹' {x})
  have h1: 0 < pre.ncard := by
    apply (Set.ncard_pos _).mpr
    · exact Set.preimage_singleton_nonempty.mpr (hs x)
    · exact Set.toFinite pre
  have h2: pre.ncard ≤ m := by
    calc pre.ncard ≤ Nat.card (Fin m) := Set.ncard_le_card pre
      _ ≤ m := by simp
  simp only [entropy_weight, ge_iff_le]
  exact div_ge_1_of_pos_of_le (Nat.cast_pos'.mpr h1) (Nat.cast_le.mpr h2)-/

/-- Frequency weight function for the entropy bound -/
noncomputable def fweight [Fintype α] (X : Fin m → α) (x : α) :=
  ((X ⁻¹' {x}).ncard : ℝ)

/-- ℕ varaint of nfweight for convenience -/
private noncomputable def nfweight [Fintype α] (X : Fin m → α) (x : α) :=
  (X ⁻¹' {x}).ncard

lemma fweight_ge_one [Fintype α] (X : Fin m → α) (hsur : Function.Surjective X) (x : α) :
    1 ≤ fweight X x := by
  unfold fweight
  set pre := (X ⁻¹' {x})
  have : 0 < pre.ncard := by
    apply (Set.ncard_pos _).mpr
    · exact Set.preimage_singleton_nonempty.mpr (hsur x)
    · exact Set.toFinite pre
  exact Nat.one_le_cast.mpr this

private lemma Fin_cast_succ_eq_card {m : ℕ} (s : Set (Fin m)) :
    s.ncard = (Fin.castSucc '' s).ncard := by
    apply Eq.symm; apply Set.InjOn.ncard_image; apply Set.injOn_of_injective
    exact Fin.castSucc_injective m

private lemma nfweight_sum [Fintype α] [DecidableEq α] {m : ℕ} (X : Fin m → α) :
    ∑ x, nfweight X x = m := by
  induction m with
  | zero =>
    have : ∀ x, nfweight X x = 0 := by
      intro x; unfold nfweight;
      have : (X ⁻¹' {x}) = ∅ := by
        unfold Set.preimage
        apply Set.eq_empty_of_forall_notMem
        intro y; exact Fin.elim0 y
      rw [this]; simp
    simp [this]
  | succ m ih =>
    let X' := fun (i : (Fin m)) => X i.castSucc
    have := ih X'
    let y := X (Fin.last m)
    have hyset : X ⁻¹' {y} = Fin.castSucc '' (X' ⁻¹' {y}) ∪ {(Fin.last m)} := by
      apply Set.ext; intro i; constructor
      · intro h
        simp at h
        cases i using Fin.reverseInduction with -- TODO: "induction"?
        | last => right; simp
        | cast i => left; simp [X', h]
      · intro h; simp at h
        cases h with
        | inl h' => simp [y]; rw [h']
        | inr h' =>
          rcases h' with ⟨x,hx,hxi⟩
          simp [X'] at hx
          simp; rw[←hxi]; assumption
    have hyw : nfweight X y = (nfweight X' y) + 1 := by
      have : 1 = Set.ncard {Fin.last m} := by simp
      simp [nfweight]; rw [hyset]; nth_rw 8 [this]
      rw [Fin_cast_succ_eq_card (X' ⁻¹' {y})]
      apply Set.ncard_union_eq (by simp)
    have hxset : ∀ x, x ≠ y → X ⁻¹' {x} = Fin.castSucc '' (X' ⁻¹' {x}) := by
      intro x h; apply Set.ext; intro i; constructor
      · intro h'; simp at h' ⊢
        cases i using Fin.reverseInduction with
        | last => rw [←h'] at h; contradiction
        | cast i =>
          use i
      · intro h'; simp at h' ⊢
        rcases h' with ⟨j, hj, hji⟩
        simp [X', hji] at hj; exact hj
    have hxw : ∀ x, x ≠ y → nfweight X x = (nfweight X' x) := by
      intro x h; simp [nfweight]; rw [hxset x h]
      simp [Fin_cast_succ_eq_card (X' ⁻¹' {x})]
    let codom := Finset.image X Finset.univ
    have : ∀ x, x ∈ codom := by
      intro x; unfold codom; simp
    /-have : ∑ x ∈ codom, nfweight X x = m := sorry
    apply?
    --calc ∑ x, nfweight X x = nfweight X y + ∑ x with (x ≠ y), nfweight X x
    rw [Finset.sum_filter]
    #check Finset.sum_filter
    apply Finset.sum_erase_add
    rw [hxw]-/




noncomputable def entropy [Fintype α] (X : Fin m → α) :=
  ∑ x, (X ⁻¹' {x}).ncard / m * Real.logb 2 (m / (X ⁻¹' {x}).ncard)

-- TODO: Without FinType, using init.toKeyList in the statement?
theorem entropy_bound [LinearOrder α] [Fintype α]
    (X : Fin m → α)
    (hs : Function.Surjective X)
    (init : Tree α) (hbst : init.IsBST)
    (hcont : ∀ i : Fin m, (X i) ∈ init) :
    let n := init.nodeCount
    splay.sequenceCost init X ≤ n * Real.logb 2 n + entropy X := by
  set n := init.nodeCount
  set w := fweight X
  have hw : WeightFunc w := fweight_ge_one X hs
  have h_amortized := splay_total_weighted_cost hw m (splaySeq init X) X (splaySeq_succ init X)
    (by simp [splaySeq]; exact hbst) (by simp [splaySeq]; exact hcont)
  unfold splay.sequenceCost; simp
  calc ∑ x, ↑(splay.cost (splaySeq init X x.castSucc) (X x))
    ≤  ∑ x, (3 * Real.logb 2 (size w (splaySeq init X 0) / w (X x)) + 1)
      + φ w (splaySeq init X 0) := h_amortized



end EntropyBound

end Weighted

end SplayTree
