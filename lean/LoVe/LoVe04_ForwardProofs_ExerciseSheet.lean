/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
  a → a :=
  assume ha : a
  show a from
    ha

theorem K (a b : Prop) :
  a → b → b :=
  assume ha : a
  assume hb : b
  show b from
    hb

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
  assume fabc : a → b → c
  assume hb : b
  assume ha : a
  show c from
    fabc ha hb


theorem proj_fst (a : Prop) :
  a → a → a :=
  fix ha ha' : a
  show a from
    ha


/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
  a → a → a :=
  fix ha' ha : a
  show a from
    ha

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  assume fabc : a → b → c
  assume ha : a
  assume fac : a → c
  assume hb : b
  show c from
    fabc ha hb

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  assume fab : a → b
  assume nb : ¬ b
  assume ha : a
  show False from
    nb (fab ha)

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro
    ( assume pxqx : ∀x, p x ∧ q x
      show (∀x, p x) ∧ (∀x, q x) from
        And.intro
          ( assume y : α
            show p y from
              And.left (pxqx y) )
          ( assume y : α
            show q y from
              And.right (pxqx y) ) )
    ( assume pxqx : (∀x, p x) ∧ (∀x, q x)
      assume x : α
      show p x ∧ q x from
        And.intro
          ( show p x from
              And.left pxqx x )
          ( show q x from
              And.right pxqx x ) )

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume h : ∃x, ∀y, p x y
  assume y : α
  show ∃x, p x y from
    Exists.elim h ( assume x : α
                    assume h' : ∀ (y : α), p x y
                    show ∃ x, p x y from
                      Exists.intro x (h' y) )


/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/

theorem binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  calc
    (a+b) * (a+b) = a*(a+b) + b*(a+b) := by rw[add_mul]
    _ = a*a + a*b + b*a + b*b := by rw[mul_add,mul_add,<-add_assoc]
    _ = a*a + a*b + a*b + b*b := by rw[mul_comm b a]
    _ = a*a + 2*a*b + b*b := by rw[add_assoc (a*a),<-Nat.two_mul,mul_assoc]

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  let begin := (a + b) * (a + b)
  have : begin = a*(a+b) + b*(a+b) := by simp[begin,add_mul]
  have : begin = a*a + a*b + b*a + b*b := Eq.trans this (by rw[mul_add,mul_add,<-add_assoc])
  have : begin = a*a + a*b + a*b + b*b := Eq.trans this (by rw[mul_comm b a])
  have : begin = a*a + 2*a*b + b*b := Eq.trans this (by rw[add_assoc (a*a),<-Nat.two_mul,mul_assoc])
  this

/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
  False :=
  have : (∀ (x : Bool), x = true ∧ True) ↔ True
    := All.one_point_wrong true (fun _ ↦ True)
  have : True → (∀ (x : Bool), x = true ∧ True)
    := Iff.mpr this
  have : false = true
    := And.left (this True.intro false)
  show False from
    by contradiction


/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
  False :=
  have : (∃ x, x = true → False) → False
            := (Exists.one_point_wrong true (fun _ ↦ False)).mp
  show False from
    this (Exists.intro false ( assume contra : false = true
                                  by contradiction ) )



end LoVe
