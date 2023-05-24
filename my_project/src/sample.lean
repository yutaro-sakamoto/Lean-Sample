import data.int.basic
import data.nat.basic

namespace Section4_2
  variables x y z : ℤ

  example (x y z : ℕ) : x * (y + z) = x * y + x * z :=
    mul_add x y z
  example (x y z : ℕ) : (x + y) * z = x * z + y * z :=
    add_mul x y z
  example (x y z : ℕ) : x + y + z = x + (y + z) :=
    add_assoc x y z
  
  example (x y : ℕ) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y,
    from mul_add (x + y) x y,
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y),
    from (add_mul x y x) ▸ (add_mul x y y) ▸ h1,
  h2.trans (add_assoc (x * x + y * x) (x * y) (y * y)).symm
end Section4_2

namespace Section4_3
  variables (a b c d e: ℕ)
  variable h1 : a = b
  variable h2 : b = c + 1
  variable h3 : c = d
  variable h4 : e = 1 + d

  theorem T : a = e :=
  calc
    a   = b : h1
    ... = c + 1 : h2
    ... = d + 1 : congr_arg _ h3
    ... = 1 + d : add_comm d (1 : ℕ)
    ... = e     : eq.symm h4
  

  include h1 h2 h3 h4
  theorem T2 : a = e :=
  calc
    a     = b      : by rw h1
      ... = c + 1  : by rw h2
      ... = d + 1  : by rw h3
      ... = 1 + d  : by rw add_comm
      ... =  e     : by rw h4
  
  theorem T3 : a = e :=
  calc
    a     = d + 1 : by rw [h1, h2, h3]
      ... = 1 + d : by rw add_comm
      ... = e : by rw h4
  
  theorem T4 : a = e :=
  by rw [h1, h2, h3, add_comm, h4]

  theorem T5: a = e :=
  by rw [h1, h2, h3, h4, add_comm]

end Section4_3

namespace Section4_3_1
  theorem TT2 (a b c d : ℕ)
    (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a     = b     : h1
      ... < b + 1 : nat.lt_succ_self b
      ... ≤ c + 1 : nat.succ_le_succ h2
      ... < d     : h3
  
  example (x y : ℕ) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  : by rw mul_add
      ... = x * x + y * x + (x + y) * y            : by rw add_mul
      ... = x * x + y * x + (x * y + y * y)        : by rw add_mul
      ... = x * x + y * x + x * y + y * y          : by rw ←add_assoc

  example (x y : ℕ) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [mul_add, add_mul, add_mul, ←add_assoc]

  example (x y : ℕ) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [mul_add, add_mul, add_assoc, add_left_comm]
end Section4_3_1

namespace Section4_4
  open nat

  example : ∃ x : ℕ, x > 0 :=
  have h : 1 > 0, from zero_lt_succ 0,
  exists.intro 1 h

  example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
  exists.intro 0 h

  example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
    ∃ w, x < w ∧ w < z :=
    exists.intro y (and.intro hxy hyz)
  
  #check @exists.intro

  example : ∃ x : ℕ, x > 0 :=
  ⟨1, zero_lt_succ 0⟩

  example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

  example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
    ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

  variable g : ℕ → ℕ → ℕ
  variable hg : g 0 0 = 0

  theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
  theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
  theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
  theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

  set_option pp.implicit true
  #print gex1
  #print gex2
  #print gex3
  #print gex4

  variables (α : Type*) (p q : α → Prop)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  exists.elim h
    (assume w,
      assume hw : p w ∧ q w,
      show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩)
  
  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with ⟨w, hw⟩ :=
    ⟨w, hw.right, hw.left⟩
  end

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with ⟨(w : α), (hw : p w ∧ q w)⟩ :=
    ⟨w, hw.right, hw.left⟩
  end

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with ⟨w, hpw, hqw⟩ :=
    ⟨w, hqw, hpw⟩
  end

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h in ⟨w, hqw, hpw⟩

  example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  assume ⟨w, hpw, hqw⟩, ⟨w, hqw, hpw⟩

  def is_even (a : nat) := ∃ b, a = 2 * b

  theorem even_plus_even {a b : nat}
    (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  exists.elim h1 (assume w1, assume hw1 : a = 2 * w1,
  exists.elim h2 (assume w2, assume hw2 : b = 2 * w2,
    exists.intro (w1 + w2)
      (calc
        a + b = 2 * w1 + 2 * w2 : by rw [hw1, hw2]
          ... = 2 * (w1 + w2)   : by rw mul_add)))
  
  theorem even_plus_even2 {a b : nat}
    (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
    match h1, h2 with
      ⟨w1, hw1⟩, ⟨w2, hw2⟩ := ⟨w1 + w2, by rw [hw1, hw2, mul_add]⟩
    end
  
  example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  by_contradiction
    (assume h1 : ¬ ∃ x, p x,
      have h2 : ∀ x, ¬ p x, from
        assume x,
        assume h3 : p x,
        have h4 : ∃ x, p x, from ⟨x, h3⟩,
        show false, from h1 h4,
      show false, from h h2)
end Section4_4