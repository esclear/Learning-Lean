namespace inner
  constant and   : Prop → Prop → Prop
  constant or    : Prop → Prop → Prop
  constant not   : Prop → Prop
  constant implies : Prop → Prop → Prop

  variables p q r : Prop
  -- #check and p q -- Prop
  -- #check or (and p q) r -- Prop
  -- #check implies (and p q) (and q p) -- Prop

  constant Proof : Prop → Type
  constant and_comm : Π p q : Prop,
    Proof (implies (and p q) (and q p))

  -- #check and_comm p q -- Proof (implies (and p q) (and q p))
  constant modus_ponens :
    Π p q : Prop, Proof (implies p q) → Proof p → Proof q
  constant implies_intro :
    Π p q : Prop, (Proof p → Proof q) → Proof (implies p q)

end inner

constants p q : Prop

-- theorem t1 : p → q → p := 
-- assume hp : p,
-- assume hq : q,
-- show p, from hp

theorem t1' (hp : p) (hq : q) : p := hp

axiom hp : p
-- theorem t2 : q → p := t1 hp

theorem t1 : ∀ (p q : Prop), p → q → p :=
λ (p q : Prop) (hp : p) (hq : q), hp

variables p q r s : Prop
-- variable h : r → s

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
assume h₃ : p,
show r, from h₁ (h₂ h₃)

#check p → q → p ∧ q
#check ¬p → p ↔ false
#check p ∨ q → q ∨ p

example (hp : p) (hq : q) : p ∧ q := and.intro hp hq

#check assume (hp : p) (hq : q), and.intro hp hq
example (h : p ∧ q) : p := and.elim_left h
example (h : p ∧ q) : q := and.elim_right h

example (h : p ∧ q) : q ∧ p := and.intro (and.right h) (and.left h)

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

example (hp : p) : p ∨ q := or.intro_left q hp
example (hq : q) : p ∨ q := or.intro_right p hq

example (h : p ∨ q) : q ∨ p :=
h.elim
(assume hp : p, or.inr hp)
(assume hq : q, or.inl hq)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  assume hp : p,
  show false, from hnq (hpq hp)

example (hp : p) (hnp : ¬p) : q := false.elim (hnp hp)
example (hp : p) (hnp : ¬p) : q := absurd hp hnp

example (hnp : ¬p) (hq : q) (hqp : q → p) : r := absurd (hqp hq) hnp

theorem and_swap : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume h : p ∧ q,
    show q ∧ p, from and.intro (and.right h) (and.left h))
  (assume h : q ∧ p,
    show p ∧ q, from and.intro (and.right h) (and.left h))

variable h : p ∧ q
example : q ∧ p := iff.mp (and_swap p q) h

theorem and_swap' : p ∧ q ↔ q ∧ p :=
  ⟨ λ h, ⟨h.right, h.left⟩, λ h, ⟨h.right, h.left⟩ ⟩
  
#check and_swap'