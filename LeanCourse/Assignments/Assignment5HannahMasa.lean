import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 5 (mostly section 2) and 6 (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 12.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- A note on definitions -/

lemma my_lemma : 3 + 1 = 4 := rfl
def myThree : ℕ := 3

/-
Tactics like `simp` and `rw` will not unfold definitions unless instructed to.
Tactics like `exact` and `apply` will unfold definitions if needed.
Uncomment the following lines one-by-one to see the difference. -/

example : myThree + 1 = 4 := by
  -- rw [my_lemma] -- fails
  -- simp [my_lemma] -- fails to use `my_lemma`
  -- exact my_lemma -- works
  -- apply my_lemma -- works
  -- rw [myThree, my_lemma] -- works after instructing `rw` to unfold the definition
  simp [myThree] -- works after instructing `simp` to unfold the definition
                    -- (it doesn't need `my_lemma` to then prove the goal)


/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by {
  norm_cast at h
  exact h.symm
  }

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by {
  norm_cast at *
  apply lt_of_lt_of_le ((n + 1).lt_add_one.trans (n + 1 + 1).lt_add_one)
  simp [h]
  }

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by {
  calc
    (n : ℝ) + 1
    _ = (n : ℚ) + 1 := by norm_cast
    _ =  m ^ 2 - 2 * m + 1 := by
      rw [h]
      norm_cast
    _ = (↑m - 1) ^ 2 := by ring
  }

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by {
  norm_cast
  }

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by {
  norm_cast
  }

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by {
  rw [exp_le_exp]
  norm_cast
  }

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by {
  rw [Real.sqrt_pos]
  norm_cast
  }

/- Working with `Finset` is very similar to working with `Set`.
However, some notation, such as `f '' s` or `𝒫 s` doesn't exist for `Finset`. -/
example (s t : Finset ℕ) : (s ∪ t) ∩ t = (s ∩ t) ∪ t := by {
  simp [Finset.union_inter_cancel_right, Finset.inter_subset_right]
  }

example {α β : Type*} (f : α → β) (s : Finset α) (y : β) : y ∈ s.image f ↔ ∃ x ∈ s, f x = y := by {
  exact Finset.mem_image
  }

/- `Disjoint` can be used to state that two (fin)sets are disjoint.
Use `Finset.disjoint_left` (or `Set.disjoint_left`) to unfold its definition.
If you have `x ∈ t \ s` apply `simp` first to get a conjunction of two conditions.
-/
example {α : Type*} (s t : Finset α) : Disjoint s (t \ s) := by {
  simp [disjoint_iff]
  }


/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i in range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by {
  induction' n with n hn
  · simp [fibonacci]
  · simp only [sum_range_add, hn, Finset.range_one, mul_add, sum_singleton, mul_zero, add_zero,
    mul_one]
    rw [add_comm]
    rfl
  }

example (n : ℕ) : ∑ i in range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by {
  induction' n with n hn
  · simp [fibonacci]
  · simp only [sum_range_add, hn, Finset.range_one, sum_singleton, add_zero]
    rw [sub_eq_add_neg, add_assoc, add_comm (-1), ← add_assoc]
    congr
  }

example (n : ℕ) : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  induction' n with n hn
  · simp
  · rw [sum_range_add, mul_add, hn]
    simp only [Finset.range_one, sum_singleton, add_zero]
    ring
  }

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  induction' n with n hn
  · simp [fac]
  · calc
      2 ^ (n + 1) = 2 ^ n * 2 ^ 1 := rfl
      _ ≤ fac (n + 1) * 2 := by gcongr
      _ = 2 * fac (n + 1) := by rw [mul_comm]
      _ ≤ (n + 1 + 1) * fac (n + 1) := by
        gcongr
        simp
      _ = fac (n + 1 + 1) := rfl
  }

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  induction' n with n hn
  · simp [fac]
  · rw [prod_range_add, ← hn]
    simp [fac, mul_comm]
  }

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  induction' n with n hn
  · simp [fac]
  · simp [fac, mul_add, hn, prod_range_add]
    ring
  }





/- **Exercise**.
Define scalar multiplication of a real number and a `Point`. -/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

def Point.mul (b : Point) (a : ℝ) : Point where
  x := a * b.x
  y := a * b.y
  z := a * b.z


/- **Exercise**.Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/

structure PythagoreanTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  pow_two_add : a^2 + b^2 = c^2


/- Prove that triples of equivalent types are equivalent. -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β where
  toFun a := ⟨e a.x, e a.y, e a.z⟩
  invFun b := ⟨e.invFun b.x, e.invFun b.y, e.invFun b.z⟩
  left_inv := by simp [LeftInverse]
  right_inv := by simp [Function.RightInverse, LeftInverse]



/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

def Triple.add {α : Type*} [AbelianGroup' α] (a b : Triple α) : Triple α where
  x := AbelianGroup'.add a.x b.x
  y := AbelianGroup'.add a.y b.y
  z := AbelianGroup'.add a.z b.z

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) where
  add := Triple.add
  comm := by simp [Triple.add, AbelianGroup'.comm]
  assoc := by simp [Triple.add, AbelianGroup'.assoc]
  zero := ⟨AbelianGroup'.zero, AbelianGroup'.zero, AbelianGroup'.zero⟩
  add_zero := by simp [Triple.add, AbelianGroup'.add_zero]
  neg a := ⟨AbelianGroup'.neg a.x, AbelianGroup'.neg a.y, AbelianGroup'.neg a.z⟩
  add_neg := by simp [Triple.add, AbelianGroup'.add_neg]



/-! # Exercises to hand-in. -/

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

structure Bipointed where
  α : Type*
  x₀ : α
  x₁ : α
  not_eq : x₀ ≠ x₁

lemma Bipointed.ne_or_ne (A : Bipointed) : ∀ z, z ≠ A.x₀ ∨ z ≠ A.x₁ := by
  intro z
  by_cases h : z = A.x₀
  · right
    rw [h]
    exact not_eq A
  · left
    exact h

/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/

open Finset in
lemma helper (n : ℕ) : ∑ i ∈ range (n + 1), (i : ℚ) = (n + 1) * n / 2 := by
  induction' n with n hn
  · simp
  · simp [sum_range_add, hn]
    ring

open Finset in
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i in range (n + 1), (i : ℚ) ^ 3) = (∑ i in range (n + 1), (i : ℚ)) ^ 2 := by {
  induction' n with n hn
  · simp
  · calc
      ∑ i ∈ Finset.range (n + 1 + 1), (i : ℚ) ^ 3
      _ = ∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ 3 + (n + 1) ^ 3 := by simp [sum_range_add]
      _ = (∑ i ∈ range (n + 1), (i : ℚ)) ^ 2 + (n + 1) ^ 3 := by rw [hn]
      _ = (∑ i ∈ range (n + 1), (i : ℚ)) ^ 2 +
          2 * (∑ i ∈ range (n + 1), (i : ℚ)) * (n + 1) + (n + 1) ^ 2 := by
        rw [helper]
        ring
      _ = (∑ i ∈ Finset.range (n + 1 + 1), ↑i) ^ 2 := by
        simp [sum_range_add _ (n + 1), add_pow_two]
  }

/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma disjoint_unions {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have h := wf.wf.has_min -- this hypothesis allows you to use well-orderedness
  constructor
  · simp only [Pairwise, onFun, disjoint_iff, Set.inf_eq_inter, Set.bot_eq_empty]
    intro i j ne
    rw [hC i, hC j]
    rw [Set.eq_empty_iff_forall_not_mem]
    simp only [mem_inter_iff, mem_diff, mem_iUnion, exists_prop, not_exists, not_and, not_forall,
      Classical.not_imp, Decidable.not_not, and_imp]
    intro x xmemi hx xmemj
    rw [ne_iff_lt_or_gt] at ne
    rcases ne with ltj | lti
    · use i
    · exfalso
      exact hx j lti xmemj
  · ext x
    simp_rw [mem_iUnion]
    constructor
    · intro ⟨i, memi⟩
      simp only [hC i, mem_diff, mem_iUnion, exists_prop, not_exists, not_and] at memi
      use i
      exact memi.1
    · intro ⟨i, memi⟩
      let X := {j : ι | x ∈ A j}
      have : X.Nonempty := by
        simp_rw [nonempty_def, X]
        use i
        simp [memi]
      obtain ⟨j, jmems, hj⟩ := h X this
      use j
      simp only [hC j, mem_diff, mem_iUnion, exists_prop, not_exists, not_and]
      refine ⟨jmems , ?_⟩
      intro k kltj xmem
      exact hj k xmem kltj
  }



/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

lemma not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
  rw [Nat.prime_def_lt]
  simp
  constructor
  · intro h
    rw [← or_assoc]
    by_cases hn : 2 ≤ n
    · obtain ⟨m, mlt, mdvdn, hm⟩ := h hn
      right
      use m
      constructor
      · by_contra hm2
        push_neg at hm2
        rw [Nat.lt_succ_iff] at hm2
        have : m ≠ 0 := by
          apply ne_zero_of_dvd_ne_zero _ mdvdn
          linarith
        rw [le_one_iff_eq_zero_or_eq_one] at hm2
        tauto
      · obtain ⟨x, hx⟩ := mdvdn
        use x
        refine ⟨?_, hx⟩
        by_contra hx2
        push_neg at hx2
        rw [Nat.lt_succ_iff, le_one_iff_eq_zero_or_eq_one] at hx2
        rcases hx2 with hx2 | hx2
        · simp [hx2] at hx
          linarith
        · simp [hx2] at hx
          linarith
    · left
      push_neg at hn
      rw [Nat.lt_succ_iff] at hn
      exact le_one_iff_eq_zero_or_eq_one.mp hn
  · intro h twolen
    rcases h with h | h | ⟨a, twolea, x, xltn, hax⟩
    · linarith
    · linarith
    · use a
      refine ⟨?_, Dvd.intro x (id (Eq.symm hax)), by linarith⟩
      nth_rw 1 [hax, ← mul_one a]
      gcongr
      linarith
  }

lemma prime_of_prime_two_pow_sub_one (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by {
  by_contra h2n
  rw [not_prime_iff] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · norm_num at hn
  · norm_num at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [pow_mul]
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by
        apply Int.ModEq.sub_right
        apply Int.ModEq.pow
        exact Int.modEq_sub _ _
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by simp
  have h2 : 2 ^ 2 ≤ 2 ^ a := pow_le_pow_of_le_right zero_lt_two ha
  have h3 : 1 ≤ 2 ^ a := by
    apply le_trans ?_ h2
    norm_num
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    apply Nat.pow_lt_pow_of_lt (Nat.one_lt_two)
    nth_rw 1 [← mul_one a]
    gcongr
    exact hb
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by
    apply pow_le_pow_of_le_right Nat.zero_lt_two
    exact Nat.zero_le (a * b)
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1 := by norm_cast at h
  rw [Nat.prime_def_lt] at hn
  suffices ¬ ∀ m < 2 ^ (a * b) - 1, m ∣ 2 ^ (a * b) - 1 → m = 1 by exact this hn.2
  push_neg
  use 2 ^ a - 1
  }

/- Prove that for positive `a` and `b`, `a^2 + b` and `b^2 + a` cannot both be squares.
Prove it on paper first! -/
lemma not_isSquare_sq_add_or (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
  rw [Decidable.or_iff_not_imp_left, not_not]
  intro ⟨x, hx⟩
  intro ⟨y, hy⟩
  rw [← pow_two] at hx hy
  have h1 : x ^ 2 > a ^ 2 := by
    rw [← hx]
    exact Nat.lt_add_of_pos_right hb
  have h2 : x ≥ a + 1 := by
    by_contra h
    push_neg at h
    rw [Order.lt_add_one_iff] at h
    have : x ^ 2 ≤ a ^ 2 := pow_le_pow_of_le_left h 2
    linarith
  have h3 : y ^ 2 > b ^ 2 := by
    rw [← hy]
    exact Nat.lt_add_of_pos_right ha
  have h4 : y ≥ b + 1 := by
    by_contra h
    push_neg at h
    rw [Order.lt_add_one_iff] at h
    have : y ^ 2 ≤ b ^ 2 := pow_le_pow_of_le_left h 2
    linarith
  suffices x ^ 2 + y ^ 2 > x ^ 2 + y ^ 2 by linarith
  calc
    x ^ 2 + y ^ 2
    _ ≥ (a + 1) ^ 2 + (b + 1) ^ 2 := by gcongr
    _ = a ^ 2 + b + b ^ 2 + a + a + b + 2 := by
      ring
    _ = x ^ 2 + y ^ 2 + a + b + 2 := by
      rw [← hx, ← hy]
      ring
    _ > x ^ 2 + y ^ 2 := by linarith
  }


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosReal : Type := {x : ℝ // 0 < x}

example (x : ℝ) (h : x ≠ 0) : x⁻¹ * x = 1 := by exact inv_mul_cancel₀ h

def groupPosReal : Group PosReal where
  mul x y := ⟨x.1 * y.1, mul_pos  x.2 y.2⟩
  mul_assoc x y z := mul_assoc x y z
  one := ⟨1, Real.zero_lt_one⟩
  one_mul x := one_mul x
  mul_one x := mul_one x
  inv x := ⟨x.1⁻¹, inv_pos_of_pos x.2⟩
  inv_mul_cancel x := by
    simp only [HMul.hMul, OfNat.ofNat, One.one, Subtype.mk.injEq]
    exact inv_mul_cancel₀ (G₀ := ℝ) (x.2.ne.symm)




/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] card_powerset
#check Finset.induction

lemma fintype_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (powerset s) = 2 ^ Finset.card s := by
  induction s using Finset.induction with
    | empty => simp
    | @insert x s hxs ih =>
      have h1 : Disjoint s.powerset (Finset.image (insert x) s.powerset) := by
        simp only [disjoint_iff, Finset.inf_eq_inter, Finset.bot_eq_empty,
          Finset.eq_empty_iff_forall_not_mem, Finset.mem_inter, Finset.mem_powerset,
          Finset.mem_image, not_and, not_exists]
        intro t1 t1sub t2 t2sub heq
        apply hxs
        apply t1sub
        rw [← heq]
        exact mem_insert_self x t2
      have h2 : InjOn (insert x) (s.powerset : Set (Finset α)) := by
        intro t1 t1mem t2 t2mem eq
        simp only [coe_powerset, Set.mem_preimage, mem_powerset_iff, Finset.coe_subset]
          at t1mem t2mem
        have h1 : x ∉ t1 := fun a ↦ hxs (t1mem a)
        have h2 : x ∉ t2 := fun a ↦ hxs (t2mem a)
        ext y
        constructor
        · intro hy
          have hne : y ≠ x := by
            intro heq
            subst y
            exact h1 hy
          suffices y ∈ insert x t2 by
            simp [hne] at this
            exact this
          simp [← eq, hne, hy]
        · intro hy
          have hne : y ≠ x := by
            intro heq
            subst y
            exact h2 hy
          suffices y ∈ insert x t1 by
            simp [hne] at this
            exact this
          simp [eq, hne, hy]
      rw [Finset.powerset_insert, Finset.card_union_of_disjoint h1,
        Finset.card_image_of_injOn h2, ← two_mul, ih, Finset.card_insert_of_not_mem hxs,
        pow_add_one']
