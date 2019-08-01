
open classical

-- example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
theorem de_morgan {p q : Prop} (h : ¬(p ∨ q)) : ¬p ∧ ¬q :=
sorry

-- BEGIN
theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)
-- END


theorem em' (p : Prop) : p ∨ ¬p :=
have hnnponp : ¬¬(p ∨ ¬p), from (
    assume hnponp : ¬(p ∨ ¬p),
    have hnpahnnp : ¬p ∧ ¬¬p, from de_morgan hnponp,
    have hnp : ¬p, from and.elim_left hnpahnnp,
    have hp : p, from dne (and.elim_right hnpahnnp),
    absurd hp hnp
),
show p ∨ ¬p, from dne hnnponp

theorem em'' (p: Prop) : p ∨ ¬p :=
suffices hdnem : ¬¬(p ∨ ¬p), from dne hdnem,
show ¬¬(p ∨ ¬p), from (
  assume hnem : ¬(p ∨ ¬p),
  have false : ¬p ∧ ¬¬p, from de_morgan hnem,
  absurd (and.elim_left false) (and.elim_right false)
)