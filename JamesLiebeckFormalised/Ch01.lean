import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Perm.Basic

-- The material of this chapter is nearly all in Mathlib, so we limit our
-- presentation to examples and illustrating names of relevant results

variable {G : Type*} [Group G]
variable (g h k : G)
variable (n : ℕ+)

-- A group consists of a set $G$ together with a rule for
-- combining any two elements $g$, $h$ of $G$ to form another
-- element of $G$, written $gh$; this rule must satisfy the
-- following axioms

-- (1) for all $g$, $h$, $k$ in $G$, $(gh)k = g(hk)$.
example : (g*h)*k = g*(h*k) := mul_assoc _ _ _

-- (2) there exists an element $e$ in $G$ such that for
-- all $g in $G$, $eg = ge = g$
example : ∃ e : G, (e*g = g ∧ g*e = g) :=
  ⟨ 1, ⟨one_mul g, mul_one g⟩ ⟩
  -- by use 1; exact ⟨one_mul g, mul_one g⟩

-- (3) for all g in G, there exists an element g⁻¹ in G
-- such that gg⁻¹ = g⁻¹g = e.
example : ∃ h : G, g * h = 1 ∧ h * g = 1 :=
  ⟨ g⁻¹, ⟨mul_inv_cancel g, inv_mul_cancel g⟩⟩
  -- by use g⁻¹; exact ⟨mul_inv_cancel g, inv_mul_cancel g⟩

/-
  1.1 Examples
  (1) The set of nth roots of unity in ℂ with the usual multiplication of
  complex numbers, is a group of order n.
-/

#check rootsOfUnity n ℂ
#check Complex.card_rootsOfUnity n
example : IsCyclic (rootsOfUnity n ℂ) := inferInstance

-- If a = e^(2πi/n) then Cₙ = {1, a, a^2, ..., a^(n-1) } and a^n = 1.
#check Complex.mem_rootsOfUnity n -- Mathlib built-in equivalence

-- (2) The set ℤ of all integers, under addition, is a group
example : AddGroup ℤ := Int.instAddGroup
#check Int.add_assoc  -- associativity
#check Int.zero_add   -- additive identity
#check Int.add_neg_eq_sub -- define subtraction
#check Int.sub_self   -- additive inverse
#check Int.add_comm   -- commutativity

-- (3) The 2n rotations and reflections [of a regular n-gon, n > 3]
-- form a group under the operation of composition.

/-
  Note: Whereas the book defines the dihedral group via the action on the n-gon, Mathlib
  defines it as the union of two sets of order n, with explicit multiplication rules given.

  Note 2: The book has functions acting on the right, so that fg means
  'first do f, then do g.' With apologies to Gordon and Martin, this is a
  20th-century group theory phenomenon and has no place here.
  Mathlib uses left actions throughout, so that fg means 'first do g, then do f.'
-/

section
open DihedralGroup
variable (i j : ZMod n)
example : Group (DihedralGroup n) := instGroup

#check r i -- DihedralGroup.r for rotations
#check sr i -- DihedralGroup.sr for reflections

example : (sr i) * (sr i)= 1 := by
  rw [sr_mul_sr, sub_self, r_zero]

#check instGroup.mul_assoc  -- associativity
#check instGroup.one_mul    -- identity
#check instGroup.inv_mul_cancel -- inverses

example : Fintype.card (DihedralGroup n) = 2 * n := DihedralGroup.card

end
/-
  (4) For n a positive integer, the set of all permutations of {1,2,...,n},
  under the product operation of composition, is a group. It is called the
  _symmetric group_ of degree n, and is written Sₙ.
-/

-- Mathlib defines Sₙ as the type of equivalences from a type to itself, i.e. Equiv.Perm (Fin n)

-- The order of Sₙ is n!.
example : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
  rw [Fintype.card_perm, Fintype.card_fin]
