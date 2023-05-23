import data.int.basic

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