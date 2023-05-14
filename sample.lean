constant m: nat -- m is a natural number
constant n: nat
constants b1 b2 : bool -- declare two constants at once

#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check tt

constant f: nat → nat
constant f': nat → nat
constant p : nat × nat
constant q : prod nat nat
constant g : nat → nat → nat
constant g' : nat → (nat → nat)
constant h : nat × nat → nat

constant F: (nat → nat) → nat

#check f
#check f n
#check g m n
#check g m
#check (m, n)
#check p.1
#check p.2
#check (m, n).1
#check (p.1, n)
#check F f

namespace Section2_2
#check nat
#check bool
#check nat → bool
#check nat × bool
#check nat × nat → nat

constants α β : Type
constant F: Type → Type
constant G: Type → Type → Type
#check α
#check F α
#check F nat
#check G α
#check G α β
#check G α nat

#check prod α β
#check prod nat nat

#check list α
#check list nat

#check Type
#check Type 0
#check Type 1
#check Type 2
#check Type 3
#check Type 4

#check Prop

#check list
#check prod

universe u
-- constant aa : Type u
-- constant aa : Type _
constant aa : Type*
#check aa
end Section2_2

namespace Section2_3

#check fun x : nat, x + 5
#check λ x : nat, x + 5

constants α β γ : Type
constants a1 a2 : α
constants b1 b2 : β

constant f : α → α
constant g : α → β
constant h : α → β → α
constant p : α → α → β

#check fun x : α, f x
#check λ x : α, f x
#check λ x : α, f (f x)
#check λ (x : α) (y : β), h (f x) y

#check λ b : β, λ x : α, x
#check λ (b : β) (x : α), x
#check λ (g : β → γ) (f : α → β) (x : α), g (f x)

#check λ (α β : Type*) (b : β) (x : α), x
#check λ (α β γ : Type*) (g : β → γ) (f : α → β) (x : α), g (f x)

namespace Reduce_Section
  constants α β γ : Type
  constant f : α → β
  constant g : β → γ
  constant h : α → α
  constants (a : α) (b : β)
  
  #check (λ x : α, x) a
  #reduce (λ x : α, x) a
  
  #check (λ x : α, g (f x)) a
  #reduce (λ x : α, g (f x)) a
end Reduce_Section
#eval 12345 * 54321
end Section2_3

namespace Section2_4
def foo: (ℕ → ℕ) → ℕ := λ f, f 0

#check foo
#print foo

def foo' := λ f : ℕ → ℕ, f 0

def double (x: ℕ) : ℕ := x + x
#print double
#check double 3
#reduce double 3

def square (x : ℕ) := x * x
#print square
#check square 3
#reduce square 3

def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)

#reduce do_twice double 2

def compose (α β γ : Type*) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ := sorry
def uncurry (α β γ : Type*) (f : α → β → γ) : α × β → γ := sorry
end Section2_4