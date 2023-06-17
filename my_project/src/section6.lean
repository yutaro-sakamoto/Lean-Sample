import data.nat.basic
import algebra.group.basic
import data.int.basic
import algebra.ring.basic
import algebra.order.monoid.lemmas

section
variables x y : ℕ

def double := x + x

#check double y
#check double (2 * x)

local attribute [simp] add_assoc add_comm add_left_comm

theorem t1 : double (x +y) = double x + double y :=
by simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y :=
by simp [double, add_mul]
end

section
variables (x y z : ℕ)
variables (h₁ : x = y) (h₂ : y = z)

include h₁ h₂
theorem foo : x = z :=
begin
  rw [h₁, h₂]
end
omit h₁ h₂

theorem bar : x = z :=
eq.trans h₁ h₂

theorem baz : x = x := rfl

#check @foo
#check @bar
#check @baz
end

namespace section6_2_1
section
variables (x y z : ℕ)
variables (h₁ : x = y) (h₂ : y = z)

section
variables {x y z}
include h₁ h₂
theorem foo : x = z :=
begin
  rw [h₁, h₂]
end
end

theorem bar : x = z :=
eq.trans h₁ h₂

variable {x}
theorem baz : x = x := rfl

#check @foo
#check @bar
#check @baz
end

section
parameters {α: Type*} (r : α → α → Prop)
parameter transr : ∀ {x y z}, r x y → r y z → r x z

variables {a b c d e : α}

theorem t1 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) : r a d :=
transr (transr h₁ h₂) h₃

theorem t2 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) (h₄ : r d e) :
  r a e :=
  transr h₁ (t1 h₂ h₃ h₄)

#check t1
#check t2
end

#check t1
#check t2
end section6_2_1

namespace Section6_3
  namespace foo
  def bar : ℕ := 1
  end foo
  open foo
  #check foo.bar

  def foo1.bar : ℕ := 1
  open foo

  #check foo1.bar

  #check add_sub_cancel
  #check nat.add_sub_cancel
  #check _root_.add_sub_cancel

  namespace foo2
  protected def bar : ℕ := 1
  end foo2
  open foo2
  #check foo2.bar

  open nat (renaming mul → times) (renaming add → plus)
    (hiding succ sub)
  export nat (succ add sub)
end Section6_3

namespace Section6_4
  variable {α : Type*}
  def is_prefix (l₁ : list α) (l₂ : list α) : Prop :=
  ∃ t, l₁ ++ t = l₂
  infix ` <<+: `:50 := is_prefix

  local attribute [simp]
  theorem list.is_prefix_refl (l : list α) : l <<+: l :=
  ⟨[], by simp⟩

  example : [1, 2, 3] <<+: [1, 2, 3] := by simp

  instance list_has_le : has_le (list α) := ⟨is_prefix⟩


  theorem list.is_prefix_refl2 (l : list α) : l ≤ l :=
  ⟨[], by simp⟩

  namespace sub
    def list_has_le : has_le (list α) := ⟨is_prefix⟩
    local attribute [instance] list_has_le

    theorem foo (l : list α) : l ≤ l := ⟨[], by simp⟩
  end sub

  @[simp, refl]
  theorem list.is_prefix_refl3 (l : list α) : l <<+: l :=
  ⟨[], by simp⟩

  example : [1, 2, 3] <<+: [1, 2, 3] := by reflexivity
end Section6_4

namespace Section6_5
  namespace hidden
    variables {α : Type*} (r : α → α → Prop)

    definition reflexive : Prop := ∀ (a : α), r a a
    definition symmetric : Prop := ∀ {a b : α}, r a b → r b a
    definition transitive : Prop :=
      ∀ {a b c : α}, r a b → r b c → r a c
    definition euclidean : Prop :=
      ∀ {a b c : α}, r a b → r a c → r b c
    
    variable {r}

    theorem th1 (reflr : reflexive r) (euclr : euclidean r) :
      symmetric r :=
    assume a b : α, assume : r a b,
    show r b a, from euclr this (reflr _)

    theorem th2 (symmr : symmetric r) (euclr : euclidean r) :
      transitive r :=
    assume (a b c : α), assume (rab : r a b) (rbc : r b c),
    euclr (symmr rab) (rbc)

    theorem th3 (reflr : reflexive r) (euclr : euclidean r) :
      transitive r :=
    @th2 _ _ (@th1 _ _ reflr @euclr) @euclr
  end hidden

  namespace hidden2
    variables {α : Type*} (r : α → α → Prop)

    definition reflexive : Prop := ∀ (a : α), r a a
    definition symmetric : Prop := ∀ ⦃a b : α⦄, r a b → r b a
    definition transitive : Prop :=
      ∀ ⦃a b c : α⦄, r a b → r b c → r a c
    definition euclidean : Prop :=
      ∀ ⦃a b c : α⦄, r a b → r a c → r b c
    
    variable {r}

    theorem th1 (reflr : reflexive r) (euclr : euclidean r) :
      symmetric r :=
    assume a b : α, assume : r a b,
    show r b a, from euclr this (reflr _)

    theorem th2 (symmr : symmetric r) (euclr : euclidean r) :
      transitive r :=
    assume (a b c : α), assume (rab : r a b) (rbc : r b c),
    euclr (symmr rab) (rbc)

    theorem th3 (reflr : reflexive r) (euclr : euclidean r) :
      transitive r :=
    th2 (th1 reflr euclr) euclr
  end hidden2
end Section6_5

namespace Section6_6
  local notation [parsing_only]`[` a  `**` b `]` := a * b + 1
  def mul_square (a b : ℕ) := a * a * b * b

  local infix (name := mul_square) `<*>`:50 := mul_square
  #reduce [2 ** 3]
  #reduce 2 <*> 3
  local infix `<<*>>`:50 := λ a b : ℕ, a * a * b * b

  namespace int
    def dvd (m n : ℤ) : Prop := ∃ k, n = m * k
    instance : has_dvd int := ⟨int.dvd⟩

    @[simp]
    theorem dvd_zero (n : ℤ) : n ∣ 0 :=
    ⟨0, by simp⟩

    theorem dvd_intro {m n : ℤ} (k : ℤ) (h : n = m * k) : m ∣ n :=
    ⟨k, h⟩
  end int

  open int
  section mod_m
    parameter (m : ℤ)
    variables (a b c : ℤ)

    definition mod_equiv := (m ∣ b - a)

    local infix ` ≡ `:50 := mod_equiv
    theorem mod_refl : a ≡ a :=
    show m ∣ a - a, by simp

    theorem mod_symm (h : a ≡ b) : b ≡ a :=
    by cases h with c hc; apply dvd_intro (-c); simp [eq.symm hc]

    local attribute [simp] add_assoc add_comm add_left_comm

    theorem mod_trans (h₁ : a ≡ b) (h₂ : b ≡ c) : a ≡ c :=
    begin
      cases h₁ with d hd, cases h₂ with e he,
      apply dvd_intro (d + e),
      simp [mul_add, eq.symm hd, eq.symm he],
    end
  end mod_m
  #check (mod_refl : ∀ (m a : ℤ), mod_equiv m a a)
  #check (mod_symm : ∀ (m a b : ℤ), mod_equiv m a b → mod_equiv m b a)
  #check (mod_trans: ∀ (m a b c : ℤ), mod_equiv m a b → mod_equiv m b c → mod_equiv m a c)
end Section6_6

namespace Section6_7
  variables m n : ℕ
  variables i j : ℤ

  #check i + m
  #check i + m + j
  #check i + m + n

  #check ↑m + i
  #check ↑(m + n) + i
  #check ↑m + ↑n + i
end Section6_7

namespace Section6_8
  #check eq
  #check @eq
  #check eq.symm
  #check @eq.symm

  #print eq.symm

  #check and
  #check and.intro
  #check @and.intro

  def foo {α : Type*} (x : α) : α := x

  #check foo
  #check @foo
  #reduce foo
  #reduce (foo nat.zero)
  #print foo

  #print notation
  #print notation + * -
  #print axioms
  #print options
  #print prefix nat
  #print prefix nat.le
  #print classes
  #print instances ring
  #print fields ring

  #print list.append
  #print definition list.append
  #print +
  #print nat
  #print inductive nat
  #print group
  #print inductive group
end Section6_8

namespace Section6_9
  set_option pp.implicit true
  set_option pp.universes true
  set_option pp.notation false
  set_option pp.numerals false

  #check 2 + 2 = 4
  #reduce (λ x, x + 2) = (λ x, x + 3)
  #check (λ x, x + 1) 1

  set_option pp.beta true
  #check (λ x, x + 1) 1
end Section6_9

namespace Section6_11
  open nat

  #check succ_ne_zero
  #check @mul_zero
  #check @mul_one
  #check @sub_add_eq_add_sub
  #check @le_iff_lt_or_eq

  #check @neg_neg
  #check pred_succ

  #check @nat.lt_of_succ_le
  #check @lt_of_not_ge
  #check @lt_of_le_of_ne
  #check @add_lt_add_of_lt_of_le

  #check @add_le_add_left
  #check @add_le_add_right

  #check mul_inv_self
  #check neg_add_self

  #check @prod.mk
  #check @prod.fst
  #check @prod.snd
  #check @prod.rec

  #check @and.intro
  #check @and.elim
  #check @and.left
  #check @and.right
  #check @or.inl
  #check @or.inr
  #check @or.elim
  #check @exists.intro
  #check @exists.elim
  #check @eq.refl
  #check @eq.subst
end Section6_11

namespace Section7_1
  inductive weekday : Type
  | sunday : weekday
  | monday : weekday
  | tuesday : weekday
  | wednesday : weekday
  | thursday : weekday
  | friday : weekday
  | saturday : weekday

  #check weekday.sunday
  #check weekday.wednesday
  open weekday
  #check friday

  def number_of_day(d: weekday) : ℕ :=
  weekday.rec_on d 1 2 3 4 5 6 7

  #reduce number_of_day weekday.sunday

  namespace weekday
  @[reducible]
  private def cases_on := @weekday.cases_on
  def number_of_day (d: weekday) : nat :=
  cases_on d 1 2 3 4 5 6 7
  end weekday

  #reduce weekday.number_of_day weekday.sunday
  open weekday (renaming cases_on → cases_on)
  #reduce number_of_day
  #check cases_on

  namespace weekday
    def next (d: weekday) : weekday :=
    weekday.cases_on d monday tuesday wednesday thursday friday saturday sunday

    def previous (d: weekday) : weekday :=
    weekday.cases_on d saturday sunday monday tuesday wednesday thursday friday

    #reduce next (next tuesday)
    #reduce next (previous tuesday)

    example : next (previous tuesday) = tuesday := rfl

    theorem next_previous (d: weekday) :
      next (previous d) = d :=
    weekday.cases_on d
      (show next (previous sunday) = sunday, from rfl)
      (show next (previous monday) = monday, from rfl)
      (show next (previous tuesday) = tuesday, from rfl)
      (show next (previous wednesday) = wednesday, from rfl)
      (show next (previous thursday) = thursday, from rfl)
      (show next (previous friday) = friday, from rfl)
      (show next (previous saturday) = saturday, from rfl)
    
    theorem next_previous2 (d : weekday) :
      next (previous d) = d :=
    weekday.cases_on d rfl rfl rfl rfl rfl rfl rfl

    theorem next_previous3 (d : weekday) :
      next (previous d) = d :=
    by apply weekday.cases_on d; refl

    theorem next_previous4 (d : weekday) :
      next (previous d) = d :=
    by apply weekday.rec_on d; refl
  end weekday

  def band (b1 b2 : bool) : bool :=
  bool.cases_on b1 ff b2
end Section7_1

namespace Section7_2
  universes u v

  inductive myprod (α : Type u) (β : Type v)
  | mk : α → β → myprod

  inductive mysum (α : Type u) (β : Type v)
  | inl : α → mysum
  | inr : β → mysum

  def fst {α : Type u} {β : Type v} (p : α × β) : α :=
  prod.rec_on p (λ a b, a)

  def snd {α : Type u} {β : Type v} (p : α × β) : β :=
  prod.rec_on p (λ a b, b)

  def prod_example (p : bool × ℕ) : ℕ :=
  prod.rec_on p (λ b n, cond b (2 * n) (2 * n + 1))

  #reduce prod_example (tt, 3)
  #reduce prod_example (ff, 3)

  def sum_example (s : ℕ ⊕ ℕ) : ℕ :=
  sum.cases_on s (λ n, 2 * n) (λ n, 2 * n + 1)

  #reduce sum_example (sum.inl 3)
  #reduce sum_example (sum.inr 3)

  inductive myprod2 (α : Type u) (β : Type v)
  | mk (fst : α) (snd : β) : myprod2

  inductive mysum2 (α : Type u) (β : Type v)
  | inl {} (a : α) : mysum2
  | inr {} (b : β) : mysum2

  structure myprod3 (α β : Type*) :=
  mk :: (fst : α) (snd : β)

  structure color := (red : nat) (green : nat) (blue : nat)
  def yellow := color.mk 255 255 0
  #reduce color.red yellow

  structure Semigroup :=
  (carrier : Type u)
  (mul : carrier → carrier → carrier)
  (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

  inductive option (α : Type*)
  | none {} : option
  | some    : α → option

  inductive inhabited (α : Type*)
  | mk : α → inhabited
end Section7_2

namespace Section7_3
inductive false : Prop

inductive true : Prop

inductive and (a b : Prop) : Prop
| intro : a → b → and

inductive or (a b : Prop) : Prop
| intro_left : a → or
| intro_right : b → or

inductive Exists {α : Type*} (q : α → Prop) : Prop
| intro : ∀ (a : α), q a → Exists

def exists.intro := @Exists.intro

inductive subtype {α : Type*} (p : α → Prop)
| mk : Π x : α, p x → subtype

universe u

structure subtype2 {α : Sort u} (p : α → Prop) :=
(val : α) (property : p val)

section
variables {α : Type u} (p : α → Prop)

#check subtype2 p
#check { x : α // p x }
end
end Section7_3

namespace Section7_4
  --inductive nat : Type
  --| zero : nat
  --| succ : nat → nat

  #check @nat.rec_on

  --namespace nat
  --  def add(m n : nat) : nat :=
  --    nat.rec_on n m (λ n add_m_n, succ add_m_n)
  --  #reduce add (succ zero) (succ (succ zero))
  --  instance : has_zero nat := has_zero.mk zero
  --  instance : has_add nat := has_add.mk add

  --  theorem add_zero (m : nat) : m + 0 = m := rfl
  --  theorem add_succ (m n : nat) : m + succ n = succ (m + n) := rfl

  --  -- theorem zero_add (n : nat) : 0 + n = n :=
  --  -- nat.rec_on n
  --  --   (show 0 + 0 = 0, from rfl)
  --  --   (assume n,
  --  --     assume ih : 0 + n = n,
  --  --     show 0 + succ n = succ n, from
  --  --       calc
  --  --         0 + succ n = succ (0 + n) : rfl
  --  --           ... = succ n : by rw ih)
  --end nat
  open nat
  theorem zero_add (n : ℕ) : 0 + n = n :=
    nat.rec_on n rfl (λ n ih, by rw [add_succ, ih])
  theorem zero_add' (n : ℕ) : 0 + n = n :=
    nat.rec_on n rfl (λ n ih, by simp only [add_succ, ih])
  
  theorem add_assoc (m n k : ℕ) : m + n + k = m + (n + k) :=
  nat.rec_on k
    (show m + n + 0 = m + (n + 0), from rfl)
    (assume k, assume ih : m + n + k = m + (n + k),
    show m + n + succ k = m + (n + succ k), from
      calc
        m + n + succ k = succ (m + n + k) : rfl
        ... = succ (m + (n + k)) : by rw ih
        ... = m + succ (n + k) : rfl
        ... = m + (n + succ k) : rfl)
  
  theorem add_assoc' (m n k : ℕ) : m + n + k = m + (n + k) :=
  nat.rec_on k rfl (λ k ih, by simp only [add_succ, ih])

  example (m n : nat) : m + n = n + m :=
  nat.rec_on n
    (show m + 0 = 0 + m, by rw [nat.zero_add, nat.add_zero])
    (assume n, assume ih : m + n = n + m,
    calc
      m + succ n = succ (m + n) : rfl
      ... = succ (n + m) : by rw ih
      ... = succ n + m : sorry)
  
  theorem succ_add (m n : nat) : succ m + n = succ (m + n) :=
  nat.rec_on n
  (show succ m + 0 = succ (m + 0), from rfl)
  (assume n,
    assume ih : succ m + n = succ (m + n),
    show succ m + succ n = succ (m + succ n), from
      calc
        succ m + succ n = succ (succ m + n) : rfl
          ... = succ (succ (m + n)) : by rw ih
          ... = succ (m + succ n) : rfl)

  theorem add_assoc1(m n k : ℕ) : m + n + k = m + (n + k) :=
  nat.rec_on k rfl (λ k ih, by simp only [add_succ, ih])

  theorem succ_add1 (m n : nat) : succ m + n = succ (m + n) :=
  nat.rec_on n rfl (λ n ih, by simp only [add_succ, ih])

  theorem add_comm (m n : nat) : m + n = n + m :=
  nat.rec_on n
    (by simp only [zero_add, add_zero])
    (λ n ih, by simp only [add_succ, ih, succ_add])
end Section7_4

namespace Section7_5
  inductive list (α : Type*)
  | nil {} : list
  | cons : α → list → list

  namespace list
    variable {α : Type*}

    notation (name := cons) h :: t := cons h t

    def append (s t : list α) : list α :=
    list.rec t (λ x l u, x :: u) s

    notation (name := append) s ++ t := append s t

    theorem nil_append (t : list α) : nil ++ t = t := rfl

    theorem cos_append (x : α) (s t : list α) :
    x :: s ++ t = x:: (s ++ t) := rfl
  end list

  namespace list
    notation (name := list) `[` l:(foldr `,` (h t, cons h t) nil)`]` := l

    section
      open nat
      #check [1, 2, 3, 4, 5]
      #check ([1, 2, 3, 4, 5] : list int)
    end
    variable α : Type*
    theorem append_nil (t : list α) : t ++ nil = t := sorry

    theorem append_assoc (r s t : list α) :
    r ++ s ++ t = r ++ (s ++ t) := sorry
  end list


  inductive binary_tree
  | leaf : binary_tree
  | node : binary_tree → binary_tree → binary_tree

  inductive cbtree
  | leaf : cbtree
  | sup : (ℕ → cbtree) → cbtree

  namespace cbtree
    def succ (t : cbtree) : cbtree :=
    sup (λ n, t)

    def omega : cbtree :=
    sup (λ n, nat.rec_on n leaf (λ n t, succ t))
  end cbtree
end Section7_5

namespace Section7_6
  variable p : ℕ → Prop
  open nat
  example (hz : p 0) (hs : ∀ n, p (succ n)) : ∀ n, p n :=
  begin
    intro n,
    cases n,
    { exact hz },
    apply hs
  end

  example (n : ℕ) (h : n ≠ 0) : succ (pred n) = n :=
  begin
    cases n with m,
    -- first goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
      { apply (absurd rfl h) },
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    reflexivity
  end

  def f (n : ℕ ): ℕ :=
  begin
    cases n, exact 3, exact 7
  end

  example : f 0 = 3 := rfl
  example : f 5 = 7 := rfl

  def tuple (α : Type*) (n : ℕ) :=
  { l : list α // list.length l = n }

  variables {α : Type*} {n : ℕ}

  def ff {n : ℕ} (t : tuple α n) : ℕ :=
  begin
    cases n, exact 3, exact 7
  end

  inductive foo : Type
  | bar1 : ℕ → ℕ → foo
  | bar2 : ℕ → ℕ → ℕ → foo

  def silly (x : foo) : ℕ :=
  begin
    cases x with a b c d e,
    exact b,
    exact e
  end

  open foo

  def silly2 (x : foo) : ℕ :=
  begin
    cases x,
      case bar1 : a b
        { exact b },
      case bar2 : c d e
        { exact e }
  end


  def silly3 (x : foo) : ℕ :=
  begin
    cases x,
      case bar2 : c d e
        { exact e },
      case bar1 : a b
        { exact b }
  end

end Section7_6