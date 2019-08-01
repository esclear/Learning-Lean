def double (x : ℕ) : ℕ := x + x

def square (x : ℕ) := x * x

def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)

def quadruple (x : ℕ) : ℕ := do_twice double x

def octuple (x : ℕ) : ℕ := double (quadruple x)

def foo := let a := nat in λ x : a, x + 2

section useful
    variables (α β γ : Type)
    variables (g : β → γ) (f : α → β) (h : α → α)
    variable x : α
    def compose := g (f x)

    -- def do_twice := h (h x)
    def do_thrice := h (h (h x))
end useful

namespace hidden
    universe u
    
    constant list : Type u → Type u
    
    namespace list
        constant cons : Π {α : Type u}, α → list α → list α
        constant nil : Π {α : Type u}, list α
        constant append : Π {α : Type u}, list α → list α → list α
    end list
    
    constant vec : Type u → ℕ → Type u
    namespace vec
        constant empty  : Π  α : Type u, vec α 0
        constant cons   : Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
        constant append : Π (α : Type u) (n m : ℕ), vec α m → vec α n → vec α (n + m)
    end vec
end hidden

section
    open hidden.list

    variable α : Type
    variable a : α
    variables l1 l2 : hidden.list α
end

section
    universe u
    def ident {α : Type u} (x : α) := x
    variables α β : Type u
    variables (a : α) (b : β)
end

/- 2.10 Exercises -/
def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := λ f, λ g, f (f g)

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ (a : α) (b : β), f (a, b)
def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := λ (t : α × β), f t.fst t.snd

namespace exercise_2_10_3
    open hidden.vec
    universe u

    constant vec_add : Π {n : ℕ}, @hidden.vec ℕ n → @hidden.vec ℕ n → @hidden.vec ℕ n
    constant vec_reverse : Π {α : Type u}, Π {n : ℕ}, @hidden.vec α n → @hidden.vec α n

    variables (α : Type) (β : Type)
    variables (a : α) (b : β)
    
    #check empty ℕ
    #check cons ℕ 1 2 (cons ℕ 0 1 (empty ℕ))
    #check vec_add (cons ℕ 0 1 (empty ℕ)) (cons ℕ 0 2 (empty ℕ))
end exercise_2_10_3

namespace exercise_2_10_5
    universe u

    constant matrix : Type u -> ℕ → ℕ → Type u

    constant matrix_add : Π {α : Type u}, Π {m : ℕ}, Π {n : ℕ}, matrix α m n → matrix α m n → matrix α m n
    constant matrix_mult: Π {α : Type u} {m : ℕ} {n : ℕ} {o : ℕ}, matrix α m n → matrix α n o → matrix α m o

    #check matrix ℕ 1 5
    variable A : matrix ℕ 1 5
    variable B : matrix ℕ 5 3
    variable C : matrix ℕ 3 4
    variable D : matrix ℕ 5 3

    #check matrix_add B D
    -- #check matrix_add A D

    #check matrix_mult A B
    #check matrix_mult B C
    #check matrix_mult (matrix_mult A B) C
end exercise_2_10_5