/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Exercise 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Even and Odd

The `Even` predicate is `True` for even numbers and `False` for odd numbers. -/

#check Even

/- We define `Odd` as the negation of `Even`: -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` or `induction` is useful to reason about hypotheses of the form
`Even …`. -/

@[simp] theorem Odd_1 :
  Odd 1 :=
  by
    rw [Odd]
    intro e1
    cases e1

/- 1.2. Prove that 3 and 5 are odd. -/

theorem Odd_3 : Odd 3 := by
  intro e3
  cases e3 with
  | add_two _ e1 => apply Odd_1 e1

theorem Odd_5 : Odd 5 := by
  intro e5
  cases e5 with
  | add_two _ e3 => apply Odd_3 e3


/- 1.3. Complete the following proof by structural induction. -/

theorem Even_two_times :
  ∀m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | m + 1 => Even.add_two (2*m) (Even_two_times m)


/- ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check Score

/- 2.1. Define an inductive predicate that returns `True` if the server is
ahead of the receiver and that returns `False` otherwise. -/

inductive ServAhead : Score → Prop
  -- enter the missing cases here

/- 2.2. Validate your predicate definition by proving the following theorems. -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
  ServAhead (Score.vs m n) :=
  sorry

theorem ServAhead_advServ :
  ServAhead Score.advServ :=
  sorry

theorem not_ServAhead_advRecv :
  ¬ ServAhead Score.advRecv :=
  sorry

theorem ServAhead_gameServ :
  ServAhead Score.gameServ :=
  sorry

theorem not_ServAhead_gameRecv :
  ¬ ServAhead Score.gameRecv :=
  sorry

/- 2.3. Compare the above theorem statements with your definition. What do you
observe? -/

-- enter your answer here


/- ## Question 3: Binary Trees

3.1. Prove the converse of `IsFull_mirror`. You may exploit already proved
theorems (e.g., `IsFull_mirror`, `mirror_mirror`). -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_nil {α : Type} (t : Tree α) : mirror t = Tree.nil ↔ t = Tree.nil := by
  cases t with
  | nil => rw[mirror]
  | node a l r => rw[mirror]
                  apply Iff.intro <;> intro _ <;> contradiction

theorem mirror_IsFull {α : Type} :
  ∀t : Tree α, IsFull (mirror t) → IsFull t := by
  intro t hfm
  generalize h : mirror t = mt at *
  --set mt :=  mirror t with h
  induction hfm generalizing t with
  | nil =>  cases t with
            | nil => exact IsFull.nil
            | node a r l => rw[mirror] at h
                            contradiction
  | node a l r hl hr hiff => cases t with
            | nil => exact IsFull.nil
            | node ta tr tl => rw[mirror] at *
                               cases h
                               apply IsFull.node
                               { apply hr_ih _ rfl }
                               { apply hl_ih _ rfl }
                               { simp[mirror_nil] at hiff
                                 apply Iff.symm hiff }

-- structured proof
theorem mirror_IsFull' {α : Type} :
  ∀t : Tree α, IsFull (mirror t) → IsFull t :=
  assume t : Tree α
  assume h : IsFull (mirror t)
  match t, h with
  | Tree.nil, IsFull.nil => IsFull.nil
  | Tree.node a r l, IsFull.node _ _ _ hl hr hiff => IsFull.node _ _ _
                                                        (mirror_IsFull' r hr)
                                                        (mirror_IsFull' l hl)
                                                        (show r = Tree.nil ↔ l = Tree.nil from
                                                          by simp[mirror_nil] at hiff
                                                             apply Iff.symm hiff)
-- lean proved other cases automatically by contradiction



/- 3.2. Define a `map` function on binary trees, similar to `List.map`. -/

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β
  | Tree.nil => Tree.nil
  | Tree.node a l r => Tree.node (f a) (Tree.map f l) (Tree.map f r)

/- 3.3. Prove the following theorem by case distinction. -/

theorem Tree.map_eq_empty_iff {α β : Type} (f : α → β) :
  ∀t : Tree α, Tree.map f t = Tree.nil ↔ t = Tree.nil
  | Tree.nil => by simp[map]
  | Tree.node a l r => by simp[map]

/- 3.4 (**optional**). Prove the following theorem by rule induction. -/

theorem map_mirror {α β : Type} (f : α → β) :
  ∀t : Tree α, IsFull t → IsFull (Tree.map f t) := by
  intro t h
  induction t with
  | nil => simp[Tree.map]; tauto
  | _ => cases' h
         simp[Tree.map]
         apply IsFull.node _ _ _ (a_ih hl) (a_ih_1 hr)
         simp[Tree.map_eq_empty_iff]
         assumption

end LoVe
