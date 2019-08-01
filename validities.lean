open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  iff.intro
    (assume h : p ∧ q,
      show q ∧ p, from ⟨h.right, h.left⟩)
    (assume h : q ∧ p,
      show p ∧ q, from ⟨h.right, h.left⟩)

example : p ∨ q ↔ q ∨ p :=
  iff.intro
    (assume h : p ∨ q,
      show q ∨ p, from or.elim h
      (assume hp : p,
        show q ∨ p, from or.inr hp)
      (assume hq : q,
        show q ∨ p, from or.inl hq)
    )
    (assume h : q ∨ p,
      show p ∨ q, from or.elim h
      (assume hq : q,
        show p ∨ q, from or.inr hq)
      (assume hp : p,
        show p ∨ q, from or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (assume h : (p ∧ q) ∧ r,
      have hp : p, from h.left.left,
      have hq : q, from h.left.right,
      have hr : r, from h.right,
    show p ∧ (q ∧ r), from ⟨ hp, ⟨ hq, hr ⟩ ⟩)
    (assume h : p ∧ (q ∧ r),
      have hp : p, from h.left,
      have hq : q, from h.right.left,
      have hr : r, from h.right.right,
    show (p ∧ q) ∧ r, from ⟨ ⟨ hp, hq ⟩, hr ⟩)
   
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (assume h : (p ∨ q) ∨ r,
      show p ∨ (q ∨ r), from or.elim h
      (assume hl : p ∨ q,
        show p ∨ (q ∨ r), from or.elim hl
        (assume hp : p,
        show p ∨ (q ∨ r), from or.intro_left (q ∨ r) hp)
        (assume hq : q,
        show p ∨ (q ∨ r), from or.intro_right p (or.intro_left r hq)
        ))
      (assume hr : r,
        show p ∨ (q ∨ r), from or.intro_right p (or.intro_right q hr)))
    (assume h : p ∨ (q ∨ r),
      show (p ∨ q) ∨ r, from or.elim h
      (assume hr : p,
        show (p ∨ q) ∨ r, from or.intro_left r (or.intro_left q hr))
      (assume hl : q ∨ r,
        show (p ∨ q) ∨ r, from or.elim hl
        (assume hq : q,
          show (p ∨ q) ∨ r, from or.intro_left r (or.intro_right p hq))
        (assume hr : r,
          show (p ∨ q) ∨ r, from or.intro_right (p ∨ q) hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (assume h : p ∧ (q ∨ r),
      have hp : p, from and.elim_left h,
      have hqr : q ∨ r, from and.elim_right h,
      show (p ∧ q) ∨ (p ∧ r), from or.elim hqr
        (assume hq : q,
          show (p ∧ q) ∨ (p ∧ r), from or.intro_left (p ∧ r) (and.intro hp hq))
        (assume hr : r,
          show (p ∧ q) ∨ (p ∧ r), from or.intro_right (p ∧ q) (and.intro hp hr)))
    (assume h : (p ∧ q) ∨ (p ∧ r),
      or.elim h
      (assume hpq : p ∧ q,
        show p ∧ (q ∨ r), from ⟨ hpq.left, or.inl hpq.right ⟩ )
      (assume hpr : p ∧ r,
        show p ∧ (q ∨ r), from ⟨ hpr.left, or.inr hpr.right ⟩ ))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  iff.intro
    (assume h : p ∨ (q ∧ r),
      or.elim h
        (assume hp : p,
          show (p ∨ q) ∧ (p ∨ r), from ⟨ or.inl hp, or.inl hp ⟩)
        (assume qr : q ∧ r,
          show (p ∨ q) ∧ (p ∨ r), from ⟨ or.inr qr.left, or.inr qr.right ⟩))
    (assume h : (p ∨ q) ∧ (p ∨ r),
      have pq : p ∨ q, from h.left,
      have pr : p ∨ r, from h.right,
      show p ∨ (q ∧ r), from 
      pq.elim
        (assume hp : p,
          or.inl hp)
        (assume hq : q,
          pr.elim
            (assume hp : p,
              show p ∨ (q ∧ r), from or.inl hp)
            (assume hr : r,
              show p ∨ (q ∧ r), from or.inr ⟨ hq, hr ⟩)))

-- -- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  iff.intro
    (assume h : p → (q → r),
      assume hpq : p ∧ q,
      have hp : p, from hpq.left,
      have hq : q, from hpq.right,
      show r, from h hp hq)
    (assume h : p ∧ q → r,
      assume hp : p,
      assume hq : q,
      show r, from h ⟨ hp, hq ⟩)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  iff.intro
    (assume h : (p ∨ q) → r,
      and.intro
        (assume hp : p,
          have hpq : p ∨ q, from or.inl hp,
          show r, from h hpq)
        (assume hq : q,
          have hpq : p ∨ q, from or.inr hq,
          show r, from h hpq))
    (assume h : (p → r) ∧ (q → r),
      assume hpq : p ∨ q,
      hpq.elim
        (assume hp : p,
          show r, from h.left hp)
        (assume hq : q,
          show r, from h.right hq))
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
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
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  assume hnpnq : ¬p ∨ ¬q,
  hnpnq.elim
    (assume hnp : ¬p,
      assume hpq : p ∧ q,
      absurd hpq.left hnp)
    (assume hnq : ¬q,
      assume hpq : p ∧ q,
      absurd hpq.right hnq)
example : ¬(p ∧ ¬p) :=
  assume hpnp : p ∧ ¬p,
  absurd hpnp.left hpnp.right
example : p ∧ ¬q → ¬(p → q) :=
  assume hpnq : p ∧ ¬q,
  assume hpiq : p → q,
  have hp : p, from hpnq.left,
  have hnq : ¬q, from hpnq.right,
  absurd (hpiq hp) hnq
example : ¬p → (p → q) :=
  assume hnp : ¬p,
  assume hp : p,
  show q, from absurd hp hnp
example : (¬p ∨ q) → (p → q) :=
  assume hnpq : ¬p ∨ q,
  assume hp : p,
  hnpq.elim
    (assume hnp : ¬p,
      show q, from absurd hp hnp)
    (assume hq : q,
      show q, from hq)
example : p ∨ false ↔ p :=
  iff.intro
    (assume hpf : p ∨ false,
      hpf.elim
        (assume hp : p,
          hp)
        (assume hf : false,
          hf.elim))
    (assume hp : p,
      show p ∨ false, from or.inl hp)
example : p ∧ false ↔ false :=
  iff.intro
    (assume hpf : p ∧ false,
      show false, from hpf.right)
    (assume hf : false,
      show p ∧ false, from hf.elim)
example : ¬(p ↔ ¬p) :=
  sorry
example : (p → q) → (¬q → ¬p) :=
  assume hpiq : p → q,
  assume hnq : ¬q,
  assume hp : p,
  absurd (hpiq hp) hnq


-- -- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  assume hpirs : p → r ∨ s,
  by_cases
    (assume hp : p, 
      have hrs : r ∨ s, from hpirs hp,
      hrs.elim
        (assume hr : r,
          show (p → r) ∨ (p → s), from or.inl (assume hp : p, hr))
        (assume hs : s,
          show (p → r) ∨ (p → s), from or.inr (assume hp : p, hs)))
    (assume hnp : ¬p,
      or.inl (show p → r, from assume hp : p, absurd hp hnp))
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q :=
  assume hnpiq : ¬(p → q),
  by_cases
  (assume hp : p,
    sorry)
  (assume hnp : ¬p,
    sorry)

example : (p → q) → (¬p ∨ q) :=
  assume hpiq : p → q,
  by_cases
    (assume hp : p,
      show ¬p ∨ q, from or.inr (hpiq hp))
    (assume hnp : ¬p,
      show ¬p ∨ q, from or.inl hnp)
example : (¬q → ¬p) → (p → q) :=
  assume hnqinp : ¬q → ¬p,
  by_cases
    (assume hq : q,
      assume hp : p,
      hq)
    (assume hnq : ¬q,
      assume hp : p,
      have hnp : ¬p, from hnqinp hnq,
      absurd hp hnp)

example : p ∨ ¬p :=
  by_cases
    (assume hp : p, or.inl hp)
    (assume hnp : ¬p, or.inr hnp)
example : (((p → q) → p) → p) :=
  assume hpqp : (p → q) → p,
  by_cases
    (assume hp : p,
      show p, from hp)
    (assume hnp : ¬p,
      show p, from hpqp (assume hp : p, show q, from absurd hp hnp))

-- and also in classical logic
example : ¬(p ↔ ¬p) :=
  assume h : p ↔ ¬p,
  by_cases
    (assume hp : p,
      have hnp : ¬p, from h.elim_left hp,
      absurd hp hnp)
    (assume hnp : ¬p,
      have hp : p, from h.elim_right hnp,
      absurd hp hnp)