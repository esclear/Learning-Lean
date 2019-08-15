open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

theorem dne {p : Prop} (hp : ¬¬p) : p :=
  by_contradiction (assume hnp : ¬p, absurd hnp hp)
--
example : (∃ x : α, r) → r :=
  assume h : (∃ x : α, r),
  exists.elim h
    (assume w,
      assume hr : r,
      hr)
  
example : r → (∃ x : α, r) :=
  assume hr : r,
  show ∃ x : α, r, from ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  iff.intro
    (assume h : (∃ x, p x ∧ r),
      match h with ⟨w, hpw, hr⟩ :=
        ⟨⟨w, hpw⟩, hr⟩
      end)
    (assume h : (∃ x, p x) ∧ r,
      match h with ⟨⟨w, hpw⟩, hr⟩ :=
        ⟨w, ⟨hpw, hr⟩⟩
      end)
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  iff.intro
    (assume h : (∃ x, p x ∨ q x),
      match h with ⟨w, hpqw⟩ :=
        hpqw.elim
          (assume hpw : p w,
            show (∃ x, p x) ∨ (∃ x, q x), from or.inl ⟨w, hpw⟩)
          (assume hqw : q w,
            show (∃ x, p x) ∨ (∃ x, q x), from or.inr ⟨w, hqw⟩)
      end)
    (assume h : (∃ x, p x) ∨ (∃ x, q x),
      h.elim
        (assume h : (∃ x, p x),
          match h with ⟨w, hpw⟩ := ⟨w, or.inl hpw⟩
          end)
        (assume h : (∃ x, q x),
          match h with ⟨w, hqw⟩ := ⟨w, or.inr hqw⟩
          end))
--
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  iff.intro
    (assume h : ∀ x, p x,
      assume hn : ∃ y, ¬ p y,
      match hn with ⟨w, hnpw⟩ :=
        have hpw : p w, from h w,
        absurd hpw hnpw
      end)
    (assume h : ¬ (∃ x, ¬ p x),
      assume x,
      have dnp : ¬¬ p x, from (
        assume hnpx : ¬ p x,
        have hen : ∃ x, ¬ p x, from ⟨x, hnpx⟩,
        absurd hen h
      ),
      dne dnp)
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  iff.intro
    (assume h : ∃ x, p x,
      show ¬(∀ x, ¬ p x), from (
        assume hfnp : ∀ x, ¬p x,
        match h with ⟨w, hpw⟩ :=
          have hnpw : ¬p w, from hfnp w,
          absurd hpw hnpw
        end
      ))
    (assume h : ¬(∀ x, ¬p x),
      by_contradiction
        (assume hnex : ¬(∃ x, p x),
          have ha : ∀ x, ¬p x, from (
            assume x,
              assume hp : p x,
              have hex: ∃ x, p x, from ⟨x, hp⟩,
              absurd hex hnex
          ),
          h ha))
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  iff.intro
    (assume h : ¬ ∃ x, p x,
      assume x,
      show ¬ p x, from (
        assume hp : p x,
        absurd (exists.intro x hp) h
      ))
    (assume h : ∀ x, ¬ p x,
      assume hex : ∃ x, p x,
      exists.elim hex (
        assume w,
        assume hp : p w,
        absurd hp (h w)
      ))
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  iff.intro
    (assume h : ¬ ∀ x, p x,
      by_contradiction
        (assume h' : ¬ ∃ x, ¬ p x,
          have hfp : ∀ x, p x, from (
            assume x,
            show p x, from by_contradiction (
              assume hnp : ¬ p x,
              absurd (exists.intro x hnp) h'
            )
          ),
          absurd hfp h))
    (assume ⟨w, (hnpw : ¬ p w)⟩,
      assume hfp : ∀ x, p x,
      absurd (hfp w) hnpw)
--
example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  iff.intro
    (assume h : ∀ x, p x → r,
      assume ⟨w, (hpw : p w)⟩,
        (h w) hpw)
    (assume h : (∃ x, p x) → r,
      assume x,
      assume hpx : p x,
      h ⟨x, hpx⟩)
example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  iff.intro
    (assume ⟨w, (hw : p w → r)⟩,
      assume h : ∀ x, p x,
      hw (h w))
    (assume h : (∀ x, p x) → r,
      show ∃ x, p x → r, from
        by_cases
          (assume hap : ∀ x, p x,
            ⟨a, (λ h', h hap)⟩)
          (assume hnap : ¬(∀ x, p x),
            by_contradiction
              (assume hnex : ¬ ∃ x, p x → r,
                have hap : ∀ x, p x,
                from
                  (assume x,
                    by_contradiction
                      (assume hnp : ¬ p x,
                        have hex : ∃ x, p x → r, from (
                          have hpair : p x → r, from (assume hpx : p x, absurd hpx hnp),
                          ⟨x, hpair⟩
                        ),
                        absurd hex hnex)),
                absurd hap hnap)
            )
      )
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  iff.intro
    (assume ⟨w, ripw⟩,
      assume hr : r,
      ⟨w, ripw hr⟩)
    (assume h : r → ∃ x, p x,
      by_cases
        (assume hr : r,
          match h hr with ⟨w, hpw⟩ :=
            have hi : r → p w, from (assume r, hpw),
            ⟨w, hi⟩
          end)
        (assume hnr : ¬r,
          have hpa : r → p a, from (
            assume hr : r,
            absurd hr hnr),
          ⟨a, hpa⟩))