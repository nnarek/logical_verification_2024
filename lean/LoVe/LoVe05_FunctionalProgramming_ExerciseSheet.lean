/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo


/- # LoVe Exercise 5: Functional Programming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Reverse of a List

We define an accumulator-based variant of `reverse`. The first argument, `as`,
serves as the accumulator. This definition is __tail-recursive__, meaning that
compilers and interpreters can easily optimize the recursion away, resulting in
more efficient code. -/

def reverseAccu {α : Type} : List α → List α → List α
  | as, []      => as
  | as, x :: xs => reverseAccu (x :: as) xs

/- 1.1. Our intention is that `reverseAccu [] xs` should be equal to
`reverse xs`. But if we start an induction, we quickly see that the induction
hypothesis is not strong enough. Start by proving the following generalization
(using the `induction` tactic or pattern matching): -/

theorem reverseAccu_Eq_reverse_append {α : Type} :
  ∀as xs : List α, reverseAccu as xs = reverse xs ++ as :=
  by
    intro as xs
    induction xs generalizing as with
    | nil => simp[reverseAccu,reverse]
    | cons x l => simp[reverseAccu,reverse,tail_ih]

/- 1.2. Derive the desired equation. -/

theorem reverseAccu_eq_reverse {α : Type} (xs : List α) :
  reverseAccu [] xs = reverse xs :=
  by simp [reverseAccu_Eq_reverse_append]


/- 1.3. Prove the following property.

Hint: A one-line inductionless proof is possible. -/

theorem reverseAccu_reverseAccu {α : Type} (xs : List α) :
  reverseAccu [] (reverseAccu [] xs) = xs :=
  by simp [reverseAccu_Eq_reverse_append,reverse_reverse]

/- 1.4. Prove the following theorem by structural induction, as a "paper"
proof. This is a good exercise to develop a deeper understanding of how
structural induction works (and is good practice for the final exam).

    theorem reverseAccu_Eq_reverse_append {α : Type} :
      ∀as xs : list α, reverseAccu as xs = reverse xs ++ as

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the induction hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `rfl` or `simp` need not be
justified if you think they are obvious (to humans), but you should say which
key theorems they depend on. You should be explicit whenever you use a function
definition. -/

-- enter your paper proof here


/- ## Question 2: Drop and Take

The `drop` function removes the first `n` elements from the front of a list. -/

def drop {α : Type} : ℕ → List α → List α
  | 0,     xs      => xs
  | _ + 1, []      => []
  | m + 1, _ :: xs => drop m xs

/- 2.1. Define the `take` function, which returns a list consisting of the first
`n` elements at the front of a list.

To avoid unpleasant surprises in the proofs, we recommend that you follow the
same recursion pattern as for `drop` above. -/

def take {α : Type} : ℕ → List α → List α
  | 0,     _    => []
  | n + 1, []   => []
  | n + 1, h::t => h :: take n t

#eval take 0 [3, 7, 11]   -- expected: []
#eval take 1 [3, 7, 11]   -- expected: [3]
#eval take 2 [3, 7, 11]   -- expected: [3, 7]
#eval take 3 [3, 7, 11]   -- expected: [3, 7, 11]
#eval take 4 [3, 7, 11]   -- expected: [3, 7, 11]

#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/- 2.2. Prove the following theorems, using `induction` or pattern matching.
Notice that they are registered as simplification rules thanks to the `@[simp]`
attribute. -/

@[simp] theorem drop_nil {α : Type} :
  ∀n : ℕ, drop n ([] : List α) = [] :=
  by
    intro n
    cases n with
    | zero => simp[drop]
    | succ m => simp[drop]

@[simp] theorem take_nil {α : Type} :
  ∀n : ℕ, take n ([] : List α) = [] :=
  by
    intro n
    cases n with
    | _ => simp[take]

/- 2.3. Follow the recursion pattern of `drop` and `take` to prove the
following theorems. In other words, for each theorem, there should be three
cases, and the third case will need to invoke the induction hypothesis.

Hint: Note that there are three variables in the `drop_drop` theorem (but only
two arguments to `drop`). For the third case, `← add_assoc` might be useful. -/

theorem drop_drop {α : Type} :
  ∀(m n : ℕ) (xs : List α), drop n (drop m xs) = drop (n + m) xs
  | 0,     n, xs      => by rfl
  | _ + 1, n, []       => by simp[drop]
  | m + 1, n, _::t       => by simp[drop,drop_drop]


theorem take_take {α : Type} :
  ∀(m : ℕ) (xs : List α), take m (take m xs) = take m xs
  | 0,     xs      => by simp[take]
  | _ + 1, []       => by simp
  | m + 1, _::t       => by simp[take]; apply take_take


theorem take_drop {α : Type} :
  ∀(n : ℕ) (xs : List α), take n xs ++ drop n xs = xs :=
  by
    intro n xs
    cases xs with
    | nil => simp
    | cons h t => cases n with
                  | zero => simp[take,drop]
                  | succ n => simp[take,drop,take_drop]


/- ## Question 3: A Type of Terms

3.1. Define an inductive type corresponding to the terms of the untyped
λ-calculus, as given by the following grammar:

    Term  ::=  `var` String        -- variable (e.g., `x`)
            |  `lam` String Term   -- λ-expression (e.g., `λx. t`)
            |  `app` Term Term     -- application (e.g., `t u`) -/

inductive Term : Type
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term

/- 3.2 (**optional**). Register a textual representation of the type `term` as
an instance of the `Repr` type class. Make sure to supply enough parentheses to
guarantee that the output is unambiguous. -/

def Term.repr : Term → String
  | var x => x
  | lam x t => "(λ" ++ x ++ ". " ++ "(" ++ (repr t) ++ "))"
  | app t1 t2 => "(" ++ (repr t1) ++ " " ++ (repr t2) ++ ")"

instance Term.Repr : Repr Term :=
  { reprPrec := fun t prec ↦ Term.repr t }

/- 3.3 (**optional**). Test your textual representation. The following command
should print something like `(λx. ((y x) x))`. -/

#eval (Term.lam "x" (Term.app (Term.app (Term.var "y") (Term.var "x"))
    (Term.var "x")))

end LoVe
