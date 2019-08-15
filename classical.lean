
open classical

theorem de_morgan {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro
    (assume h : ¬(p ∨ q),
      and.intro
        (assume hp : p,
          have hpq : p ∨ q, from or.inl hp,
          absurd hpq h)
        (assume hq : q,
          have hpq : p ∨ q, from or.inr hq,
          absurd hpq h))
    (assume h : ¬p ∧ ¬q,
      have hnp : ¬p, from h.left,
      have hnq : ¬q, from h.right,
      assume hpq : p ∨ q,
      hpq.elim
        (assume hp : p,
          absurd hp hnp)
        (assume hq : q,
          absurd hq hnq))

-- BEGIN
theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)
-- END


theorem em' (p : Prop) : p ∨ ¬p :=
have hnnponp : ¬¬(p ∨ ¬p), from (
    assume hnponp : ¬(p ∨ ¬p),
    have hnpahnnp : ¬p ∧ ¬¬p, from de_morgan.elim_left hnponp,
    have hnp : ¬p, from and.elim_left hnpahnnp,
    have hp : p, from dne (and.elim_right hnpahnnp),
    absurd hp hnp
),
show p ∨ ¬p, from dne hnnponp

theorem em'' (p: Prop) : p ∨ ¬p :=
suffices hdnem : ¬¬(p ∨ ¬p), from dne hdnem,
show ¬¬(p ∨ ¬p), from (
  assume hnem : ¬(p ∨ ¬p),
  have false : ¬p ∧ ¬¬p, from de_morgan.elim_left hnem,
  absurd (and.elim_left false) (and.elim_right false)
)