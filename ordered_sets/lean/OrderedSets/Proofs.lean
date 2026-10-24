/-
The laws: union, inter and diff keep search trees valid and have the expected
membership; build produces valid trees. Priorities only decide shape, so every
priority comparison is case-split and both branches are proved.
-/
import OrderedSets.Sets

namespace OrderedSets
open Tree

/-! ## Membership and order as propositions -/

@[simp] theorem elem_leaf (x : Nat) : Tree.leaf.elem x = false := rfl

@[simp] theorem elem_node {x k : Nat} {l r : Tree} {p : UInt32} :
    (Tree.node l k p r).elem x = true ↔ x = k ∨ l.elem x = true ∨ r.elem x = true := by
  simp [Tree.elem]

theorem allLt_iff {b : Nat} {t : Tree} : t.allLt b = true ↔ ∀ x, t.elem x = true → x < b := by
  induction t with
  | leaf => simp [Tree.allLt]
  | node l k p r ihl ihr => simp only [Tree.allLt, Bool.and_eq_true, decide_eq_true_eq, ihl, ihr, elem_node]; grind

theorem allGt_iff {b : Nat} {t : Tree} : t.allGt b = true ↔ ∀ x, t.elem x = true → b < x := by
  induction t with
  | leaf => simp [Tree.allGt]
  | node l k p r ihl ihr => simp only [Tree.allGt, Bool.and_eq_true, decide_eq_true_eq, ihl, ihr, elem_node]; grind

@[simp] theorem valid_leaf : Tree.leaf.valid = true := rfl

@[simp] theorem valid_node {k : Nat} {l r : Tree} {p : UInt32} :
    (Tree.node l k p r).valid = true ↔ (∀ x, l.elem x = true → x < k) ∧
      (∀ x, r.elem x = true → k < x) ∧ l.valid = true ∧ r.valid = true := by
  simp [Tree.valid, allLt_iff, allGt_iff]

theorem spawn_get {α : Type} (f : Unit → α) (p : Task.Priority) : (Task.spawn f p).get = f () := rfl

/-! ## join -/

theorem joinP_elem (x : Nat) (l : Tree) (k : Nat) (pk : UInt32) (r : Tree) :
    (joinP l k pk r).elem x = true ↔ x = k ∨ l.elem x = true ∨ r.elem x = true := by
  fun_induction joinP l k pk r <;> simp_all <;> grind

theorem joinP_valid (l : Tree) (k : Nat) (pk : UInt32) (r : Tree) (hl : l.valid = true)
    (hr : r.valid = true) (hlk : ∀ y, l.elem y = true → y < k) (hrk : ∀ y, r.elem y = true → k < y) :
    (joinP l k pk r).valid = true := by
  fun_induction joinP l k pk r <;> simp_all [joinP_elem] <;> grind

theorem join2_elem (x : Nat) (l r : Tree) :
    (join2 l r).elem x = true ↔ l.elem x = true ∨ r.elem x = true := by
  fun_induction join2 l r <;> simp_all <;> grind

theorem join2_valid (l r : Tree) (hl : l.valid = true) (hr : r.valid = true)
    (hlr : ∀ y z, l.elem y = true → r.elem z = true → y < z) : (join2 l r).valid = true := by
  fun_induction join2 l r <;> simp_all [join2_elem] <;> grind

/-! ## split -/

theorem split_spec (k : Nat) (t : Tree) (ht : t.valid = true) :
    (split k t).1.valid = true ∧ (split k t).2.2.valid = true ∧ (split k t).2.1 = t.elem k ∧
      (∀ x, (split k t).1.elem x = true ↔ t.elem x = true ∧ x < k) ∧
      (∀ x, (split k t).2.2.elem x = true ↔ t.elem x = true ∧ k < x) := by
  induction t with
  | leaf => simp [split]
  | node l k' p r ihl ihr =>
    simp only [valid_node] at ht
    obtain ⟨hl, hr, vl, vr⟩ := ht
    unfold split
    split
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ihl vl
      simp_all [Tree.elem]
      grind
    · split
      · obtain ⟨h1, h2, h3, h4, h5⟩ := ihr vr
        simp_all [Tree.elem]
        grind
      · simp_all [Tree.elem]
        grind

/-! ## One step of union, inter and diff, whether or not it spawns a task -/

theorem unionGo_node (n : Nat) (l1 : Tree) (k1 : Nat) (p1 : UInt32) (r1 b : Tree) (hb : b ≠ .leaf) :
    unionGo n (.node l1 k1 p1 r1) b =
      join (unionGo (n - 1) l1 (split k1 b).1) k1 (unionGo (n - 1) r1 (split k1 b).2.2) := by
  cases b with
  | leaf => contradiction
  | node =>
    rw [unionGo]
    rcases split k1 _ with ⟨l2, f, r2⟩
    split <;> simp_all [spawn_get]

theorem interGo_node (n : Nat) (l1 : Tree) (k1 : Nat) (p1 : UInt32) (r1 b : Tree) (hb : b ≠ .leaf) :
    interGo n (.node l1 k1 p1 r1) b =
      if (split k1 b).2.1 then
        join (interGo (n - 1) l1 (split k1 b).1) k1 (interGo (n - 1) r1 (split k1 b).2.2)
      else join2 (interGo (n - 1) l1 (split k1 b).1) (interGo (n - 1) r1 (split k1 b).2.2) := by
  cases b with
  | leaf => contradiction
  | node =>
    rw [interGo]
    rcases split k1 _ with ⟨l2, f, r2⟩
    split <;> simp_all [spawn_get]

theorem diffGo_node (n : Nat) (l1 : Tree) (k1 : Nat) (p1 : UInt32) (r1 b : Tree) (hb : b ≠ .leaf) :
    diffGo n (.node l1 k1 p1 r1) b =
      if (split k1 b).2.1 then
        join2 (diffGo (n - 1) l1 (split k1 b).1) (diffGo (n - 1) r1 (split k1 b).2.2)
      else join (diffGo (n - 1) l1 (split k1 b).1) k1 (diffGo (n - 1) r1 (split k1 b).2.2) := by
  cases b with
  | leaf => contradiction
  | node =>
    rw [diffGo]
    rcases split k1 _ with ⟨l2, f, r2⟩
    split <;> simp_all [spawn_get]

/-! ## union -/

theorem unionGo_elem (x : Nat) (n : Nat) (a b : Tree) (ha : a.valid = true) (hb : b.valid = true) :
    (unionGo n a b).elem x = true ↔ a.elem x = true ∨ b.elem x = true := by
  induction a generalizing n b with
  | leaf => simp [unionGo]
  | node l1 k1 p1 r1 ihl ihr =>
    by_cases hb0 : b = .leaf
    · subst hb0; simp [unionGo]
    · rw [unionGo_node _ _ _ _ _ _ hb0]
      obtain ⟨h1, h2, h3, h4, h5⟩ := split_spec k1 _ hb
      simp only [valid_node] at ha
      simp only [join, joinP_elem, ihl _ _ ha.2.2.1 h1, ihr _ _ ha.2.2.2 h2, h4, h5, elem_node]
      grind

theorem unionGo_valid (n : Nat) (a b : Tree) (ha : a.valid = true) (hb : b.valid = true) :
    (unionGo n a b).valid = true := by
  induction a generalizing n b with
  | leaf => simpa [unionGo]
  | node l1 k1 p1 r1 ihl ihr =>
    by_cases hb0 : b = .leaf
    · subst hb0; simpa [unionGo] using ha
    · rw [unionGo_node _ _ _ _ _ _ hb0]
      obtain ⟨h1, h2, h3, h4, h5⟩ := split_spec k1 _ hb
      simp only [valid_node] at ha
      apply joinP_valid _ _ _ _ (ihl _ _ ha.2.2.1 h1) (ihr _ _ ha.2.2.2 h2)
      · intro y hy
        simp only [unionGo_elem _ _ _ _ ha.2.2.1 h1, h4] at hy
        grind
      · intro y hy
        simp only [unionGo_elem _ _ _ _ ha.2.2.2 h2, h5] at hy
        grind

/-! ## inter -/

theorem interGo_elem (x : Nat) (n : Nat) (a b : Tree) (ha : a.valid = true) (hb : b.valid = true) :
    (interGo n a b).elem x = true ↔ a.elem x = true ∧ b.elem x = true := by
  induction a generalizing n b with
  | leaf => simp [interGo]
  | node l1 k1 p1 r1 ihl ihr =>
    by_cases hb0 : b = .leaf
    · subst hb0; simp [interGo]
    · rw [interGo_node _ _ _ _ _ _ hb0]
      obtain ⟨h1, h2, h3, h4, h5⟩ := split_spec k1 _ hb
      simp only [valid_node] at ha
      simp only [h3]
      split <;>
      simp only [join, joinP_elem, join2_elem, ihl _ _ ha.2.2.1 h1, ihr _ _ ha.2.2.2 h2, h4, h5, elem_node] <;>
      grind

theorem interGo_valid (n : Nat) (a b : Tree) (ha : a.valid = true) (hb : b.valid = true) :
    (interGo n a b).valid = true := by
  induction a generalizing n b with
  | leaf => simp [interGo]
  | node l1 k1 p1 r1 ihl ihr =>
    by_cases hb0 : b = .leaf
    · subst hb0; simp [interGo]
    · rw [interGo_node _ _ _ _ _ _ hb0]
      obtain ⟨h1, h2, h3, h4, h5⟩ := split_spec k1 _ hb
      simp only [valid_node] at ha
      simp only [h3]
      split
      · apply joinP_valid _ _ _ _ (ihl _ _ ha.2.2.1 h1) (ihr _ _ ha.2.2.2 h2)
        · intro y hy
          simp only [interGo_elem _ _ _ _ ha.2.2.1 h1, h4] at hy
          grind
        · intro y hy
          simp only [interGo_elem _ _ _ _ ha.2.2.2 h2, h5] at hy
          grind
      · apply join2_valid _ _ (ihl _ _ ha.2.2.1 h1) (ihr _ _ ha.2.2.2 h2)
        intro y z hy hz
        simp only [interGo_elem _ _ _ _ ha.2.2.1 h1, interGo_elem _ _ _ _ ha.2.2.2 h2, h4, h5] at hy hz
        grind

/-! ## diff -/

theorem diffGo_elem (x : Nat) (n : Nat) (a b : Tree) (ha : a.valid = true) (hb : b.valid = true) :
    (diffGo n a b).elem x = true ↔ a.elem x = true ∧ b.elem x = false := by
  induction a generalizing n b with
  | leaf => simp [diffGo]
  | node l1 k1 p1 r1 ihl ihr =>
    by_cases hb0 : b = .leaf
    · subst hb0; simp [diffGo]
    · rw [diffGo_node _ _ _ _ _ _ hb0]
      obtain ⟨h1, h2, h3, h4, h5⟩ := split_spec k1 _ hb
      simp only [valid_node] at ha
      simp only [h3]
      split <;>
      simp only [join, joinP_elem, join2_elem, ihl _ _ ha.2.2.1 h1, ihr _ _ ha.2.2.2 h2, elem_node] <;>
      grind

theorem diffGo_valid (n : Nat) (a b : Tree) (ha : a.valid = true) (hb : b.valid = true) :
    (diffGo n a b).valid = true := by
  induction a generalizing n b with
  | leaf => simp [diffGo]
  | node l1 k1 p1 r1 ihl ihr =>
    by_cases hb0 : b = .leaf
    · subst hb0; simpa [diffGo] using ha
    · rw [diffGo_node _ _ _ _ _ _ hb0]
      obtain ⟨h1, h2, h3, h4, h5⟩ := split_spec k1 _ hb
      simp only [valid_node] at ha
      simp only [h3]
      split
      · apply join2_valid _ _ (ihl _ _ ha.2.2.1 h1) (ihr _ _ ha.2.2.2 h2)
        intro y z hy hz
        simp only [diffGo_elem _ _ _ _ ha.2.2.1 h1, diffGo_elem _ _ _ _ ha.2.2.2 h2] at hy hz
        grind
      · apply joinP_valid _ _ _ _ (ihl _ _ ha.2.2.1 h1) (ihr _ _ ha.2.2.2 h2)
        · intro y hy
          simp only [diffGo_elem _ _ _ _ ha.2.2.1 h1] at hy
          grind
        · intro y hy
          simp only [diffGo_elem _ _ _ _ ha.2.2.2 h2] at hy
          grind

/-! ## build -/

theorem buildGo_valid (n : Nat) (seed : UInt32) (bits d : Nat) (lo : UInt32) :
    (buildGo n seed bits d lo).valid = true := by
  induction d generalizing n lo with
  | zero => simp [buildGo]
  | succ e ih =>
    rw [buildGo]
    split
    · exact unionGo_valid _ _ _ (ih _ _) (ih _ _)
    · exact unionGo_valid _ _ _ (ih _ _) (by rw [spawn_get]; exact ih _ _)

/-! ## The laws, as restated in Check.lean -/

theorem union_valid : ∀ (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.union a b).valid = true :=
  fun a b ha hb => unionGo_valid _ a b ha hb

theorem union_elem : ∀ (x : Nat) (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.union a b).elem x = (a.elem x || b.elem x) := by
  intro x a b ha hb
  rw [Bool.eq_iff_iff, union, unionGo_elem x _ a b ha hb, Bool.or_eq_true]

theorem inter_valid : ∀ (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.inter a b).valid = true :=
  fun a b ha hb => interGo_valid _ a b ha hb

theorem inter_elem : ∀ (x : Nat) (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.inter a b).elem x = (a.elem x && b.elem x) := by
  intro x a b ha hb
  rw [Bool.eq_iff_iff, inter, interGo_elem x _ a b ha hb, Bool.and_eq_true]

theorem diff_valid : ∀ (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.diff a b).valid = true :=
  fun a b ha hb => diffGo_valid _ a b ha hb

theorem diff_elem : ∀ (x : Nat) (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.diff a b).elem x = (a.elem x && !b.elem x) := by
  intro x a b ha hb
  rw [Bool.eq_iff_iff, diff, diffGo_elem x _ a b ha hb]
  simp

theorem build_valid : ∀ (seed : UInt32) (bits d : Nat) (lo : UInt32),
    (OrderedSets.build seed bits d lo).valid = true :=
  fun seed bits d lo => buildGo_valid _ seed bits d lo

end OrderedSets
