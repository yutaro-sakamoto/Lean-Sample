import data.nat.basic
import algebra.group.basic
import data.int.basic

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