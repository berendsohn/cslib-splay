/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Tree.Basic
public import Mathlib.Tactic.Linarith

/-!
# Binary Tree

In this file we introduce the `Tree` data structure and its basic operations.
-/

@[expose] public section

variable {α : Type}

namespace Tree

/-- A tree node. -/
notation:65 l:66 " △[" v "] " r:66 => Tree.node v l r

/-! ### Core Definitions -/
section CoreDefs

theorem non_empty_exist (s : Tree α) (h : s ≠ .nil) :
    ∃ A k B, s = A △[k] B := by
  induction s <;> grind

/-- The number of nodes in a tree. -/
def nodeCount : Tree α → ℕ
  | .nil => 0
  | .node _ l r => 1 + nodeCount l + nodeCount r

@[simp] lemma nodeCount_empty : nodeCount (nil : Tree α) = 0 := rfl

@[simp] lemma nodeCount_node (l : Tree α) (k : α) (r : Tree α) :
    (l △[k] r).nodeCount = 1 + l.nodeCount + r.nodeCount := rfl

lemma nodeCount_nonneg (t : Tree α) : nodeCount t ≥ 0 := by cases t; all_goals simp

/-- In-order traversal as a list of keys. -/
def toKeyList : Tree α → List α
  | .nil => []
  | l △[k] r => l.toKeyList ++ [k] ++ r.toKeyList

@[simp] lemma toKeyList_empty : toKeyList (nil : Tree α) = [] := rfl

@[simp] lemma toKeyList_node (l : Tree α) (k : α) (r : Tree α) :
    (l △[k] r).toKeyList = l.toKeyList ++ [k] ++ r.toKeyList := rfl

lemma toKeyList_of_empty {t : Tree α} (h : toKeyList t = []) : (t = nil) := by
  cases t
  · simp
  · simp [List.append_assoc] at h

lemma nodeCount_from_toKeyList (t : Tree α) :
    (t.nodeCount = t.toKeyList.length) := by
  induction t with
  | nil => simp
  | node v l r lih rih => simp [lih, rih]; linarith


/-- Number of nodes on the search path for `q` in `t`. Zero on the empty
tree; on a node this counts the root plus (if `q ≠ k`) the search path
length in the appropriate subtree. -/
def searchPathLen [LinearOrder α] (t : Tree α) (q : α) : ℕ :=
  match t with
  | nil => 0
  | l △[key] r =>
    if q < key then
      1 + l.searchPathLen q
    else if key < q then
      1 + r.searchPathLen q
    else
      1

lemma searchPathLen_le_nodeCount [LinearOrder α] (t : Tree α) (q : α) :
    searchPathLen t q ≤ t.nodeCount := by
  induction t with
  | nil => simp[searchPathLen]
  | node v l r ihl ihr => simp[searchPathLen]; split_ifs; all_goals linarith

/--
Remark:
This implementation is not really a "contain function",
because a binary tree could have q >/< key while being in
the left/right subtree of key respectively.
If `contains t q` is true, then `q` is in `t`; but
the converse need not necessarily hold true. The
converse is true for a binary search tree. Hence the name of it.
-/
def bstContains [LinearOrder α] (t : Tree α) (q : α) : Prop :=
  match t with
  | nil => False
  | l △[key] r =>
    if q < key then
      l.bstContains q
    else if key < q then
      r.bstContains q
    else
      True

end CoreDefs


/-! ### Membership -/
section Membership

/-- Inductive membership relation on binary trees, modelled on `List.Mem`. -/
inductive Mem (a : α) : Tree α → Prop where
  /-- `a` is the key at the root. -/
  | here  {l r : Tree α} : Mem a (l △[a] r)
  /-- `a` lies in the left subtree. -/
  | left  {k : α} {l r : Tree α} : Mem a l → Mem a (l △[k] r)
  /-- `a` lies in the right subtree. -/
  | right {k : α} {l r : Tree α} : Mem a r → Mem a (l △[k] r)

instance instMembership : Membership α (Tree α) := ⟨fun t a => Mem a t⟩

@[simp] lemma not_mem_nil (a : α) : a ∉ (nil : Tree α) := nofun

@[simp] lemma mem_node_iff {a k : α} {l r : Tree α} :
    a ∈ (l △[k] r) ↔ a = k ∨ a ∈ l ∨ a ∈ r := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | here    => exact Or.inl rfl
    | left h  => exact Or.inr (Or.inl h)
    | right h => exact Or.inr (Or.inr h)
  · rcases h with rfl | h | h
    · exact .here
    · exact .left h
    · exact .right h

/-- Membership agrees with membership in the in-order key list. -/
theorem mem_iff_mem_toKeyList {a : α} {t : Tree α} :
    a ∈ t ↔ a ∈ t.toKeyList := by
  induction t with
  | nil => simp
  | node k l r ihl ihr =>
    rw [toKeyList_node, mem_node_iff]
    simp only [List.mem_append, List.mem_singleton, ihl, ihr]
    tauto

instance decidableMem [DecidableEq α] (a : α) : ∀ t : Tree α, Decidable (a ∈ t)
  | .nil       => isFalse nofun
  | l △[k] r =>
    haveI : Decidable (a ∈ l) := decidableMem a l
    haveI : Decidable (a ∈ r) := decidableMem a r
    decidable_of_iff (a = k ∨ a ∈ l ∨ a ∈ r) mem_node_iff.symm

/-- The search-path `contains` implies membership. The converse needs the BST
invariant. -/
theorem contains_imp_mem [LinearOrder α] {t : Tree α} {q : α} :
    t.bstContains q → q ∈ t := by
  induction t with
  | nil => simp [bstContains]
  | node k l r ihl ihr =>
    intro h
    simp only [bstContains] at h
    split_ifs at h with h1 h2
    · exact .left (ihl h)
    · exact .right (ihr h)
    · have hqk : q = k := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      exact hqk ▸ .here

end Membership


/-! ### Rotations and Mirroring -/
section Transformations

/-- Right rotation at the root: pivot the left child up. Leaves the tree
unchanged if there is no left child. -/
def rotateRight : Tree α → Tree α
  | (a △[x] b) △[y] c => a △[x] (b △[y] c)
  | t => t

/-- Left rotation at the root: pivot the right child up. Leaves the tree
unchanged if there is no right child. -/
def rotateLeft : Tree α → Tree α
  | a △[x] (b △[y] c) => (a △[x] b) △[y] c
  | t => t

/-- Mirror a binary tree: swap every left and right subtree. -/
def mirror : Tree α → Tree α
  | .nil => .nil
  | l △[k] r => r.mirror △[k] l.mirror

@[simp] lemma mirror_empty : (nil : Tree α).mirror = nil := rfl

@[simp] lemma mirror_node (l : Tree α) (k : α) (r : Tree α) :
    (l △[k] r).mirror = r.mirror △[k] l.mirror := rfl

@[simp] lemma mirror_mirror (t : Tree α) : t.mirror.mirror = t := by
  induction t <;> simp_all

@[simp] lemma nodeCount_mirror (t : Tree α) : t.mirror.nodeCount = t.nodeCount := by
  induction t <;> simp_all [nodeCount]; omega

@[simp] lemma toKeyList_mirror (t : Tree α) : t.mirror.toKeyList = t.toKeyList.reverse := by
  induction t <;> simp_all [toKeyList]

@[simp] lemma mirror_rotateRight (t : Tree α) :
    (rotateRight t).mirror = rotateLeft t.mirror := by
  rcases t with _ | ⟨k, (_ | ⟨lk, ll, lr⟩), r⟩ <;>
    simp [rotateRight, rotateLeft, mirror]

@[simp] lemma mirror_rotateLeft (t : Tree α) :
    (rotateLeft t).mirror = rotateRight t.mirror := by
  rcases t with _ | ⟨k, l, (_ | ⟨rk, rl, rr⟩)⟩ <;>
    simp [rotateRight, rotateLeft, mirror]

@[simp] theorem nodeCount_rotateRight (t : Tree α) :
    (rotateRight t).nodeCount = t.nodeCount := by
  rcases t with _ | ⟨k, (_ | ⟨lk, ll, lr⟩), r⟩ <;>
    simp [rotateRight]; omega

@[simp] theorem nodeCount_rotateLeft (t : Tree α) :
    (rotateLeft t).nodeCount = t.nodeCount := by
  have h := nodeCount_rotateRight t.mirror
  simp only [← mirror_rotateLeft, nodeCount_mirror] at h; exact h

@[simp] theorem toKeyList_rotateRight (t : Tree α) :
    (rotateRight t).toKeyList = t.toKeyList := by
  rcases t with _ | ⟨k, (_ | ⟨lk, ll, lr⟩), r⟩ <;>
    simp [rotateRight]

@[simp] theorem toKeyList_rotateLeft (t : Tree α) :
    (rotateLeft t).toKeyList = t.toKeyList := by
  have h := toKeyList_rotateRight t.mirror
  simp only [← mirror_rotateLeft, toKeyList_mirror] at h
  apply List.reverse_inj.mp; exact h

end Transformations


/-! ### Contains Characterizations -/
section ContainsLemmas

@[simp] lemma not_contains_empty [LinearOrder α] (q : α) :
    ¬ (nil : Tree α).bstContains q := nofun

@[simp] lemma contains_node_lt [LinearOrder α] {l : Tree α} {k q : α}
    {r : Tree α} (h : q < k) :
    (l △[k] r).bstContains q ↔ l.bstContains q := by
  simp [bstContains, h]

@[simp] lemma contains_node_gt [LinearOrder α] {l : Tree α} {k q : α}
    {r : Tree α} (h : k < q) :
    (l △[k] r).bstContains q ↔ r.bstContains q := by
  simp [bstContains, h, not_lt_of_gt h]

@[simp] lemma contains_node_not_eq_not_lt [LinearOrder α]
    {l : Tree α} {k q : α} {r : Tree α}
    (h1 : ¬ q = k) (h2 : ¬ q < k) :
    (l △[k] r).bstContains q ↔ r.bstContains q := by
  have hgt : k < q := lt_of_le_of_ne (Std.not_lt.mp h2) (Ne.symm (Ne.intro h1))
  simp [bstContains, hgt, not_lt_of_gt hgt]

end ContainsLemmas


/-! ### Tree Invariants and BST Properties -/
section Invariants

/-- BST invariant parameterised by optional lower/upper key bounds.
`IsBSTAux t lb ub` holds iff every key in `t` lies strictly in `(lb, ub)`
(absent bound = ±∞) and children satisfy the BST property recursively. -/
inductive IsBSTAux [LinearOrder α] : Tree α → Option α → Option α → Prop where
  | nil (lb ub : Option α) : IsBSTAux .nil lb ub
  | node {l r : Tree α} {k : α} {lb ub : Option α}
      (hlb : lb.elim True (· < k))
      (hub : ub.elim True (k < ·))
      (hl  : IsBSTAux l lb (some k))
      (hr  : IsBSTAux r (some k) ub) :
      IsBSTAux (l △[k] r) lb ub

/-- A tree is a binary search tree when it satisfies `IsBSTAux` with no
bounds. -/
def IsBST [LinearOrder α] (t : Tree α) : Prop := t.IsBSTAux none none

end Invariants

/-! ### Accessor Lemmas for IsBST -/
section IsBSTAccessors

@[simp] lemma IsBSTAux_nil [LinearOrder α] (lb ub : Option α) :
    IsBSTAux (.nil : Tree α) lb ub := .nil lb ub

@[simp] lemma IsBSTAux_node [LinearOrder α] (l : Tree α) (k : α) (r : Tree α)
    (lb ub : Option α) :
    IsBSTAux (l △[k] r) lb ub ↔
      lb.elim True (· < k) ∧ ub.elim True (k < ·) ∧
      IsBSTAux l lb (some k) ∧ IsBSTAux r (some k) ub :=
  ⟨fun h => by cases h with | node hlb hub hl hr => exact ⟨hlb, hub, hl, hr⟩,
   fun ⟨h1, h2, h3, h4⟩ => .node h1 h2 h3 h4⟩

@[simp] lemma IsBST_node [LinearOrder α] (l : Tree α) (k : α) (r : Tree α) :
    IsBST (l △[k] r) ↔ IsBSTAux l none (some k) ∧ IsBSTAux r (some k) none := by
  simp [IsBST, IsBSTAux_node]

private lemma IsBSTAux_children_none [LinearOrder α] (t : Tree α) (x y : Option α)
    (h : IsBSTAux t x y) : IsBSTAux t none y ∧ IsBSTAux t x none ∧ IsBSTAux t none none := by
  induction t generalizing x y with
  | nil => simp
  | node k l r lih rih =>
    simp only [IsBSTAux_node] at h
    rcases h with ⟨_, _, h1, h2⟩
    rcases lih x (some k) h1 with ⟨_,_,_⟩
    rcases rih (some k) y h2 with ⟨_,_,_⟩
    simp only [IsBSTAux_node, Option.elim_none, true_and]; split_ands; all_goals assumption

-- TODO: Less explicit arguments
private lemma IsBST_of_IsBSTAux [LinearOrder α] (t : Tree α) (x y : Option α)
    (h : IsBSTAux t x y) : IsBST t := by
  unfold IsBST; rcases IsBSTAux_children_none t x y h with ⟨_,_,_⟩; assumption

theorem IsBST_left_of_IsBST [LinearOrder α] {k : α} {l r : Tree α}
    (hbst : IsBST (l △[k] r)) : IsBST l := by
  simp only [IsBST, IsBSTAux_node, Option.elim_none, true_and] at hbst; rcases hbst with ⟨hl,_⟩
  exact IsBST_of_IsBSTAux l none (some k) hl

theorem IsBST_right_of_IsBST [LinearOrder α] {k : α} {l r : Tree α}
    (hbst : IsBST (l △[k] r)) : IsBST r := by
  simp only [IsBST, IsBSTAux_node, Option.elim_none, true_and] at hbst; rcases hbst with ⟨_,hr⟩
  exact IsBST_of_IsBSTAux r (some k) none hr

end IsBSTAccessors


/-! ### BST Membership -/
section BSTMembership

/-- In a BST subtree with upper bound `some ub`, every member is `< ub`. -/
private lemma IsBSTAux.lt_of_mem_ub [LinearOrder α] {t : Tree α} {q ub : α}
    {lb : Option α} (h : IsBSTAux t lb (some ub)) (hmem : q ∈ t) : q < ub := by
  induction t generalizing lb ub with
  | nil => simp at hmem
  | node k l r ihl ihr =>
    obtain ⟨_, hub, hl, hr⟩ := (IsBSTAux_node l k r lb (some ub)).mp h
    rcases mem_node_iff.mp hmem with rfl | hml | hmr
    · exact hub
    · exact lt_trans (ihl hl hml) hub
    · exact ihr hr hmr

/-- In a BST subtree with lower bound `some lb`, every member is `> lb`. -/
private lemma IsBSTAux.gt_of_mem_lb [LinearOrder α] {t : Tree α} {q lb : α}
    {ub : Option α} (h : IsBSTAux t (some lb) ub) (hmem : q ∈ t) : lb < q := by
  induction t generalizing lb ub with
  | nil => simp at hmem
  | node k l r ihl ihr =>
    obtain ⟨hlb, _, hl, hr⟩ := (IsBSTAux_node l k r (some lb) ub).mp h
    rcases mem_node_iff.mp hmem with rfl | hml | hmr
    · exact hlb
    · exact ihl hl hml
    · exact lt_trans hlb (ihr hr hmr)

/-- Membership implies the BST search path finds the key, for any bound
configuration. -/
private theorem IsBSTAux.mem_imp_contains [LinearOrder α] {t : Tree α} {q : α}
    {lb ub : Option α} (h : IsBSTAux t lb ub) (hmem : q ∈ t) : t.bstContains q := by
  induction t generalizing lb ub with
  | nil => simp at hmem
  | node k l r ihl ihr =>
    obtain ⟨_, _, hl, hr⟩ := (IsBSTAux_node l k r lb ub).mp h
    rcases mem_node_iff.mp hmem with rfl | hml | hmr
    · simp [bstContains]
    · have hlt : q < k := IsBSTAux.lt_of_mem_ub hl hml
      simp only [bstContains, if_pos hlt]
      exact ihl hl hml
    · have hgt : k < q := IsBSTAux.gt_of_mem_lb hr hmr
      simp only [bstContains, if_neg (not_lt.mpr hgt.le), if_pos hgt]
      exact ihr hr hmr

/-- Converse of `contains_imp_mem` for BSTs: membership implies the search-path
`contains` succeeds. -/
theorem mem_imp_contains [LinearOrder α] {t : Tree α} (hbst : IsBST t)
    {q : α} (hmem : q ∈ t) : t.bstContains q :=
  IsBSTAux.mem_imp_contains hbst hmem

/-- For BSTs, the search-path `contains` coincides with membership. -/
theorem contains_iff_mem [LinearOrder α] {t : Tree α} (hbst : IsBST t) {q : α} :
    t.bstContains q ↔ q ∈ t :=
  ⟨contains_imp_mem, mem_imp_contains hbst⟩

/-- FOr BSTs, all keys in the left subtree are smaller than the root key. -/
theorem lt_of_IsBST_left [LinearOrder α] (l : Tree α) (k : α) (r : Tree α)
    (hbst : IsBST (l △[k] r)) {q : α} (hql : q ∈ l) : q < k := by
  simp only [IsBST_node] at hbst; rcases hbst with ⟨hl,_⟩
  exact IsBSTAux.lt_of_mem_ub hl hql

/-- FOr BSTs, all keys in the right subtree are greater than the root key. -/
theorem gt_of_IsBST_right [LinearOrder α] (l : Tree α) (k : α) (r : Tree α)
    (hbst : IsBST (l △[k] r)) {q : α} (hqr : q ∈ r) : k < q := by
  simp only [IsBST_node] at hbst; rcases hbst with ⟨_,hr⟩
  exact IsBSTAux.gt_of_mem_lb hr hqr

/-- A tree that contains something is not nil. -/
theorem nonnil_of_mem {t : Tree α} (q : α) (hq : q ∈ t) : (t ≠ nil) := by
  by_contra
  have : q ∉ t := by rw[this]; exact not_mem_nil q
  contradiction

end BSTMembership

section BSTMoreStuff -- TODO

private lemma IsBSTAux_from_IsBST_and_bounds [LinearOrder α] {t : Tree α} {lb ub : Option α}
    (hbst : t.IsBST) (hlb : lb.elim True (∀ x, x ∈ t → · < x))
    (hub : ub.elim True (∀ x, x ∈ t → x < ·)) : t.IsBSTAux lb ub := by
  induction t generalizing lb ub with
  | nil => simp
  | node v l r lih rih =>
    simp only [IsBSTAux_node]; constructor
    · cases lb with
      | none => simp
      | some b =>
        simp only [Option.elim_some]
        simp only [mem_node_iff, forall_eq_or_imp, Option.elim_some] at hlb
        cases hlb; assumption
    · constructor
      · cases ub with
        | none =>
          simp
        | some b =>
          simp only [Option.elim_some]
          simp only [mem_node_iff, forall_eq_or_imp, Option.elim_some] at hub
          cases hub; assumption
      · constructor
        · apply lih
          · exact IsBST_left_of_IsBST hbst
          · cases lb with
            | none => simp
            | some b =>
              simp only [Option.elim_some]; intro x hx
              apply hlb; simp only [mem_node_iff]; right; left; assumption
          · simp only [Option.elim_some]; intro x hx
            exact lt_of_IsBST_left l v r hbst hx
        · apply rih
          · exact IsBST_right_of_IsBST hbst
          · simp only [Option.elim_some]; intro x hx; exact gt_of_IsBST_right l v r hbst hx
          · cases ub with
            | none => simp
            | some b =>
              simp only [Option.elim_some]; intro x hx
              apply hub; simp only [mem_node_iff]; right; right; assumption

private lemma IsBST_and_bounds_from_IsBSTAux [LinearOrder α]
    {t : Tree α} {lb ub : Option α} (hbst : t.IsBSTAux lb ub) :
    t.IsBST ∧ lb.elim True (∀ x, x ∈ t → · < x) ∧ ub.elim True (∀ x, x ∈ t → x < ·) := by
  induction t generalizing lb ub with
  | nil => cases lb <;> cases ub <;> simp [IsBST, Option.elim]
  | node v l r lih rih =>
    constructor
    · exact IsBST_of_IsBSTAux _ _ _ hbst
    · constructor
      · cases lb with
      | none => simp
      | some b =>
        simp only [IsBSTAux_node, Option.elim_some] at hbst
        rcases hbst with ⟨hbv, _, hlbst, hrbst⟩
        simp only [mem_node_iff, forall_eq_or_imp, Option.elim_some]
        constructor
        · assumption
        · intro x hx; rcases hx with hx | hx
          · exact IsBSTAux.gt_of_mem_lb hlbst hx
          · have := rih hrbst
            simp only [Option.elim_some] at this; rcases this with ⟨_, this, _⟩
            exact lt_trans hbv (this x hx)
      · cases ub with
      | none => simp
      | some b =>
        simp only [IsBSTAux_node, Option.elim_some] at hbst
        rcases hbst with ⟨_, hbv, hlbst, hrbst⟩
        simp only [mem_node_iff, forall_eq_or_imp, Option.elim_some]
        constructor
        · assumption
        · intro x hx; rcases hx with hx | hx
          · have := lih hlbst
            simp only [Option.elim_some] at this; rcases this with ⟨_, _, this⟩
            exact lt_trans (this x hx) hbv
          · exact IsBSTAux.lt_of_mem_ub hrbst hx

private lemma ISBSTAux_iff_IsBST_and_bounds [LinearOrder α] (t : Tree α) (lb ub : Option α) :
    t.IsBSTAux lb ub ↔
    t.IsBST ∧ lb.elim True (∀ x, x ∈ t → · < x) ∧ ub.elim True (∀ x, x ∈ t → x < ·) := by
  constructor
  · intro h; exact IsBST_and_bounds_from_IsBSTAux h
  · intro h; rcases h with ⟨hbst, hlb, hub⟩; exact IsBSTAux_from_IsBST_and_bounds hbst hlb hub


private lemma List.sortedLT_cons [LinearOrder α] (x : α) (ys : List α) :
    (x :: ys).SortedLT ↔ (∀ y ∈ ys.head?, x < y) ∧ ys.SortedLT := by
  rw [List.sortedLT_iff_isChain]
  rw [List.isChain_cons]
  rw [←List.sortedLT_iff_isChain]

private lemma List.sortedGT_cons [LinearOrder α] (x : α) (ys : List α) :
    (x :: ys).SortedGT ↔ (∀ y ∈ ys.head?, y < x) ∧ ys.SortedGT := by
  rw [List.sortedGT_iff_isChain]
  rw [List.isChain_cons]
  rw [←List.sortedGT_iff_isChain]

private lemma List.sortedLT_append [LinearOrder α] (xs ys : List α) :
    (xs ++ ys).SortedLT ↔ xs.SortedLT ∧ ys.SortedLT ∧ ∀ x ∈ xs.getLast?, ∀ y ∈ ys.head?, x < y := by
  rw [List.sortedLT_iff_isChain]
  rw [List.isChain_append]
  rw [←List.sortedLT_iff_isChain, ←List.sortedLT_iff_isChain]

private lemma List.sortedLT_append_cons [LinearOrder α] (xs : List α) (y : α) (zs : List α) :
    (xs ++ y :: zs).SortedLT ↔
    xs.SortedLT ∧ zs.SortedLT ∧ (∀ x ∈ xs.getLast?, x < y) ∧ ∀ z ∈ zs.head?, y < z := by
  rw [List.sortedLT_append, List.sortedLT_cons]
  rw [and_assoc] --TODO: Could some congruence thing work better here?
  constructor
  · intro h; rcases h with ⟨hx, hyz, hz, hxy⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · assumption
    · assumption
    · simp only [Option.mem_def, List.head?_cons, Option.some.injEq, forall_eq'] at hxy
      intro x hx; exact lt_of_lt_of_eq (hxy x hx) rfl
    · assumption
  · intro h; rcases h with ⟨hx, hz, hxy, hyz⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · assumption
    · assumption
    · assumption
    · intro x hx y' hy'
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy'
      exact lt_of_lt_of_eq (hxy x hx) hy'

private lemma List.sortedLT_all_gt_iff_head?_gt [LinearOrder α] (x : α) (ys : List α)
    (hsorted : ys.SortedLT) : -- TODO: Need hsorted as part of iff
    (∀ y ∈ ys, x < y) ↔ ∀ y ∈ ys.head?, x < y := by
  induction ys generalizing x with
  | nil => simp
  | cons y ys ih =>
    constructor
    · intro h
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
      simp only [List.mem_cons, forall_eq_or_imp] at h; rcases h; assumption
    · intro h z hz
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq',
        List.mem_cons] at h hz
      rcases hz with hz | hz
      · simp [h, hz]
      · rw [List.sortedLT_cons] at hsorted; rcases hsorted with ⟨hyhead, yssort⟩
        have := (ih y yssort).mpr hyhead
        exact lt_trans h (this z hz)

private lemma List.sortedLT_all_gt_iff_head?_gt' [LinearOrder α] (x : α) (ys : List α) :
    (∀ y ∈ ys, x < y) ∧ ys.SortedLT ↔ (∀ y ∈ ys.head?, x < y) ∧ ys.SortedLT
  := and_congr_left (sortedLT_all_gt_iff_head?_gt x ys)

-- TODO: Almost exact copy of the above
private lemma List.sortedGT_all_lt_iff_head?_lt [LinearOrder α] (x : α) (ys : List α)
    (hsorted : ys.SortedGT) :
    (∀ y ∈ ys, y < x) ↔ ∀ y ∈ ys.head?, y < x := by
  induction ys generalizing x with
  | nil => simp
  | cons y ys ih =>
    constructor
    · intro h
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
      simp only [List.mem_cons, forall_eq_or_imp] at h; rcases h; assumption
    · intro h z hz
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq',
        List.mem_cons] at h hz
      rcases hz with hz | hz
      · simp [h, hz]
      · rw [List.sortedGT_cons] at hsorted; rcases hsorted with ⟨hyhead, yssort⟩
        have := (ih y yssort).mpr hyhead
        exact lt_trans (this z hz) h

private lemma List.sortedLT_all_lt_iff_getLast?_lt [LinearOrder α] (xs : List α) (y : α)
    (hsorted : xs.SortedLT) :
    (∀ x ∈ xs, x < y) ↔ ∀ x ∈ xs.getLast?, x < y := by
  rw [←List.sortedGT_reverse] at hsorted
  rw [←List.head?_reverse]
  rw [←List.sortedGT_all_lt_iff_head?_lt y xs.reverse hsorted]
  constructor
  · intro h y' hy'; rw[List.mem_reverse] at hy'; exact lt_of_lt_of_eq (h y' hy') rfl
  · intro h x hx; have := List.mem_reverse.mpr hx; exact lt_of_lt_of_eq (h x this) rfl

private lemma List.sortedLT_all_lt_iff_getLast?_lt' [LinearOrder α] (xs : List α) (y : α) :
    (∀ x ∈ xs, x < y) ∧ xs.SortedLT ↔ (∀ x ∈ xs.getLast?, x < y) ∧ xs.SortedLT
  := and_congr_left (List.sortedLT_all_lt_iff_getLast?_lt xs y)

private lemma List.sortedLT_append_cons' [LinearOrder α] (xs : List α) (y : α) (zs : List α) :
    (xs ++ y :: zs).SortedLT ↔
    xs.SortedLT ∧ zs.SortedLT ∧ (∀ x ∈ xs, x < y) ∧ ∀ z ∈ zs, y < z := by
  rw [List.sortedLT_append_cons]
  nth_rw 2 [←and_comm]; simp only [and_assoc]; rw [←List.sortedLT_all_gt_iff_head?_gt']
  nth_rw 1 [←and_assoc]; nth_rw 2 [and_comm]; rw [←List.sortedLT_all_lt_iff_getLast?_lt']
  tauto

-- TODO: Lots of proof simplification possible with grind
private lemma IsBSTAux_iff_toKeyList_sorted [LinearOrder α] {t : Tree α} {lb ub : Option α} :
    t.IsBSTAux lb ub ↔
    t.toKeyList.SortedLT
      ∧ lb.elim True (∀ x, x ∈ t.toKeyList → · < x)
      ∧ ub.elim True (∀ x, x ∈ t.toKeyList → x < ·) := by
  induction t generalizing lb ub with
  | nil => simp [List.sortedLT_iff_isChain]; cases lb <;> cases ub <;> simp
  | node v l r lih rih =>
    simp only [IsBSTAux_node]
    rw [lih, rih]
    simp only [Option.elim_some, toKeyList_node, List.append_assoc, List.cons_append,
      List.nil_append, List.mem_append, List.mem_cons]
    rw [List.sortedLT_append_cons']
    simp only [and_assoc]
    constructor
    · intro h; rcases h with ⟨hlbv, hubv, _, hlbl, hlv, _, hrv, hubr⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try assumption
      · cases lb with
        | none => simp
        | some b =>
          simp_all only [Option.elim_some]; intro x hx; rcases hx with (hxl | hxv | hxr)
          · exact lt_of_lt_of_eq (hlbl _ hxl) rfl
          · exact lt_of_lt_of_eq hlbv (symm hxv)
          · exact lt_trans hlbv (hrv _ hxr)
      · cases ub with
        | none => simp
        | some b =>
          simp_all only [Option.elim_some]; intro x hx; rcases hx with (hxl | hxv | hxr)
          · exact lt_trans (hlv _ hxl) hubv
          · exact lt_of_eq_of_lt hxv hubv
          · exact lt_of_lt_of_eq (hubr _ hxr) rfl
    · intro h; rcases h with ⟨_, _, _, _, _, _⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try assumption
      · cases lb <;> simp_all only [Option.elim_some, Option.elim_none]; grind only
      · cases ub <;> simp_all only [Option.elim_some, Option.elim_none]; grind only
      · cases lb <;> simp_all only [Option.elim_some, Option.elim_none]; grind only
      · cases ub with
        | none => simp_all
        | some b => simp_all only [Option.elim_some]; grind only

/- TODO: the following is much shorter, increases the build time significatnly; maybe some middle
ground is possible:

private lemma IsBSTAux_iff_toKeyList_sorted [LinearOrder α] {t : Tree α} {lb ub : Option α} :
    t.IsBSTAux lb ub ↔
    t.toKeyList.SortedLT
      ∧ lb.elim True (∀ x, x ∈ t.toKeyList → · < x)
      ∧ ub.elim True (∀ x, x ∈ t.toKeyList → x < ·) := by
  induction t generalizing lb ub with
  | nil => simp [List.sortedLT_iff_isChain]; cases lb <;> cases ub <;> simp
  | node v l r lih rih =>
    simp only [IsBSTAux_node]
    rw [lih, rih]
    simp only [Option.elim_some, toKeyList_node, List.append_assoc, List.cons_append,
      List.nil_append, List.mem_append, List.mem_cons]
    rw [List.sortedLT_append_cons']
    simp only [and_assoc]
    constructor
    · intro h; rcases h with ⟨hlbv, hubv, _, hlbl, hlv, _, hrv, hubr⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try assumption
      all_goals cases lb <;> cases ub <;>
      simp_all only [true_and, Option.elim_none, Option.elim_some]
      all_goals grind only
    · intro h; rcases h with ⟨_, _, _, _, _, _⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try assumption
      all_goals cases lb <;> cases ub <;>
      simp_all only [Option.elim_some, Option.elim_none, true_and, implies_true, and_self]
      all_goals grind only
-/

theorem IsBST_iff_toKeyList_sorted [LinearOrder α] {t : Tree α} :
    t.IsBST ↔ t.toKeyList.SortedLT := by
  rw [IsBST, IsBSTAux_iff_toKeyList_sorted]; simp

end BSTMoreStuff

end Tree
