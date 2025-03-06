/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro h1
  rw[h1]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro h1
  rw[h1]
  intro h2
  rw[h2]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1
  intro h2
  rw[h1]
  exact h2
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro h1
  cases' h1 with hP hQ
  constructor 
  exact hQ --why after 'change' I can't use intro anymore
  exact hP
  intro h2
  cases' h2 with hP hQ
  constructor
  exact hQ
  exact hP
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  sorry
  done

example : P ↔ P ∧ True := by
  sorry
  done

example : False ↔ P ∧ False := by
  sorry
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry
  done

example : ¬(P ↔ ¬P) := by
  sorry
  done
