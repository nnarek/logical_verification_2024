/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 4 (10 points): Forward Proofs

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1 (2 points). Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

theorem about_Impl_term :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  fun _ _ nab ha ↦ Or.elim nab
                        (fun na ↦ False.elim (na ha))
                        (fun hb ↦ hb)


/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  fix a b : Prop
  assume nab : ¬ a ∨ b
  assume ha : a
  show b from
    Or.elim nab
    ( assume na : ¬ a
      False.elim (na ha) )
    ( assume hb : b
      hb )



/- ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
  (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
    Iff.intro
      (
        assume f : (x : α) → p x ∨ q x
        assume x : α
        show q x ∨ p x from
          Or.elim (f x)
          ( assume px : p x
            Or.inr px )
          ( assume qx : q x
            Or.inl qx )
      )
      (
        assume f : (x : α) → q x ∨ p x
        assume x : α
        show p x ∨ q x from
          Or.elim (f x)
          ( assume qx : q x
            Or.inr qx )
          ( assume px : p x
            Or.inl px )
      )

/- 2.2 (3 points). We have proved or stated three of the six possible
implications between `ExcludedMiddle`, `Peirce`, and `DoubleNegation` in the
exercise of lecture 3. Prove the three missing implications using structured
proofs, exploiting the three theorems we already have. -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem Peirce_of_DN :
  DoubleNegation → Peirce :=
  assume dn : ∀a : Prop, (¬¬ a) → a
  fix a b : Prop
  assume faba : (a → b) → a
  show a from
    dn _ ( assume na : ¬ a
           have ha : a :=
              faba (assume ha' : a; False.elim (na ha'))
           na ha)

theorem EM_of_Peirce :
  Peirce → ExcludedMiddle :=
  assume pr : ∀a b : Prop, ((a → b) → a) → a
  assume A : Prop
  show A ∨ ¬A from
    pr _ (¬A) ( assume h : A ∨ ¬A → ¬A
                show A ∨ ¬A from
                  Or.inr ( assume a : A
                           show False from
                              h (Or.inl a) a) )

theorem dn_of_em :
  ExcludedMiddle → DoubleNegation :=
  assume em : ∀A : Prop, A ∨ ¬A
  assume B : Prop
  assume nBB : ¬¬B
  show B from
    Or.elim (em B)
      (assume b : B
        show B from
          b)
      ( assume nB : ¬B
        show B from
          False.elim (nBB nB) )

end BackwardProofs

end LoVe
