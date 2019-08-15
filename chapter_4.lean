open classical

variables (α : Type) (p q : α → Prop)
variable r : Prop

-- Exercise 1
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  iff.intro
    (assume h : ∀ x, p x ∧ q x,
      and.intro
        (assume x,
          (h x).left)
        (assume x,
          (h x).right))
    (assume h : (∀ x, p x) ∧ (∀ x, q x),
      assume x,
      show p x ∧ q x, from
      and.intro
        (h.left x)
        (h.right x))
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  assume hi : ∀ x, p x → q x,
  assume hp : ∀ x, p x,
  assume x,
  have hp : p x, from hp x,
  (hi x) hp
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  assume h : (∀ x, p x) ∨ (∀ x, q x),
  h.elim
    (assume hp : ∀ x, p x,
      assume x,
      or.inl (hp x))
    (assume hq : ∀ x, q x,
      assume x,
      or.inr (hq x))

-- Exercise 2
example : α → ((∀ x : α, r) ↔ r) :=
  assume hα,
  iff.intro
    (assume h : ∀ x : α, r,
      h hα)
    (assume hr : r,
      assume x : α,
      hr)
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  iff.intro
    (assume h : (∀ x, p x ∨ r),
      by_cases
        (assume hr : r,
          or.inr hr)
        (assume hnr : ¬r,
          have hfpx : ∀ x, p x, from (
            assume x,
            have ho : p x ∨ r, from h x,
            have hpx : p x, from
              ((h x).elim
                (assume hpx : p x,
                  hpx)
                (assume hr : r,
                  absurd hr hnr)),
            hpx),
          or.inl hfpx))
    (assume h : (∀ x, p x) ∨ r,
      h.elim
        (assume hf : ∀ x, p x,
          assume x,
          show p x ∨ r, from or.inl (hf x))
        (assume hr : r,
          assume x,
          show p x ∨ r, from or.inr hr))
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  iff.intro
    (assume h : ∀ x, r → p x,
      assume hr : r,
      assume x,
      (h x) hr)
    (assume h : r → ∀ x, p x,
      assume x,
      assume hr : r,
      (h hr) x)
-- Exercise 3
variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false := 
  have hab : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
  have hnsbb : ¬ shaves barber barber, from (
    assume hsbb : shaves barber barber,
    absurd hsbb (hab.elim_left hsbb)
  ),
  absurd (hab.elim_right hnsbb) hnsbb
-- Exercise 4
namespace hidden
  def divides (m n : ℕ) : Prop := ∃ k, m * k = n

  instance : has_dvd nat := ⟨divides⟩

  def even (n : ℕ) : Prop := 2 ∣ n

  section
    variables m n : ℕ

    def prime (n : ℕ) : Prop := ∀ r : ℕ, (r ∣ n) → (r = 1 ∨ r = n)

    def infinitely_many_primes : Prop := ∀ n : ℕ, ∃ q : ℕ, q > n ∧ prime q

    def Fermat_prime (n : ℕ) : Prop := prime n ∧ ∃ k : ℕ, n = 2 ^ (2 ^ k)

    def infinitely_many_Fermat_primes : Prop := ∀ n : ℕ, ∃ q : ℕ, q > n ∧ Fermat_prime q

    def goldbach_conjecture : Prop := ∀ k : ℕ, even k → ∃ (m n : ℕ), prime m ∧ prime n ∧ k = m + n

    def Goldbach's_weak_conjecture : Prop := ∀ k : ℕ, k > 5 ∧ ¬(even k) → ∃ (l m n : ℕ), prime l ∧ prime m ∧ prime n ∧ k = l + m + n

    def Fermat's_last_theorem : Prop := ¬ (∃ (a b c n : ℕ), a > 0 ∧ b > 0 ∧ c > 0 ∧ n > 2 ∧ a^n + b^n = c^n)
  end
end hidden
-- Exercise 5
-- see existential_quantifier.lean
-- Exercise 6
variables (real : Type) [ordered_ring real]
variables (log exp : real → real)

variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
  calc
    log(x * y) = log(exp (log x) * exp (log y)) : by rw [←eq.symm (exp_log_eq hx), ←eq.symm (exp_log_eq hy)]
           ... = log(exp (log x + log y))       : by rw [exp_add (log x) (log y)]
           ... = log x + log y                  : by rw [log_exp_eq]

-- Exercise 7
example (x : ℤ) : x * 0 = 0 :=
  calc
    x * 0 = x * (1 - 1)   : by rw sub_self
      ... = x * 1 - x * 1 : by rw mul_sub
      ... = x - x         : by rw mul_one   -- Could be skipped
      ... = 0             : by rw sub_self