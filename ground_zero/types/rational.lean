import ground_zero.types.integer data.bitvec

namespace ground_zero
namespace types

structure rational :=
(val : integer)
notation `ℚ` := rational

namespace rational

def zero : ℕ → ℕ
| 0 := 0
| _ := 1

-- https://en.wikipedia.org/wiki/Calkin%E2%80%93Wilf_tree#Stern%27s_diatomic_sequence
def fusc : ℕ → ℕ | n :=
if h : n > 2 then
  have two_gt_one : 2 > 1 :=
  nat.add_lt_add_left (nat.zero_lt_succ 0) 1,

  have n_gt_one : n > 1 := nat.lt_trans two_gt_one h,
  have n_gt_zero : n > 0 := nat.lt_trans (nat.zero_lt_succ 0) n_gt_one,

  have n / 2 < n :=
  nat.div_lt_self n_gt_zero two_gt_one,

  have n_plus_n : n + n = n * 2 :=
  begin simp [has_mul.mul, nat.mul] end,

  have n / 2 + 1 < n := begin
    apply (nat.div_lt_iff_lt_mul (n + 2) n (nat.zero_lt_succ 1)).mpr,
    rw [←n_plus_n], apply nat.add_lt_add_left, exact h
  end,

  if n % 2 = 0 then fusc (n / 2)
  else fusc (n / 2) + fusc (nat.succ $ n / 2)
else zero n

def numerator (x : rational) : integer :=
integer.signum x.val $ fusc (integer.abs x.val)

def denominator (x : rational) : ℕ :=
fusc (integer.abs x.val + 1)

def rat (x : rational) : integer × ℕ :=
⟨numerator x, denominator x⟩

instance : has_repr rational :=
⟨λ x, sformat! "{x.numerator} / {x.denominator}"⟩
instance : has_to_string rational := ⟨repr⟩

private def cont_frac_aux : nat → nat → list nat
| 0        y     := []
| (nat.succ x) y :=
have y % nat.succ x < nat.succ x := nat.mod_lt y (nat.succ_pos x),
(y / nat.succ x) :: cont_frac_aux (y % nat.succ x) (nat.succ x)

def cont_frac : ℕ × ℕ → list ℕ
| ⟨num, den⟩ := cont_frac_aux den num

private def cont_frac_odd_rev (n : ℕ × ℕ) : list ℕ :=
let frac := (cont_frac n).reverse in
if frac.length = 0 then []
else if frac.length % 2 = 0 then
match frac with
| [] := []
| (hd :: tl) := 1 :: (hd - 1) :: tl
end
else frac

private def generate_bool_list : bool → list ℕ → list bool
| _ [] := []
| x (hd :: tl) := list.repeat x hd ++ generate_bool_list (not x) tl

private def pos (num den : ℕ) : ℕ :=
bitvec.bits_to_nat (generate_bool_list tt $ cont_frac_odd_rev ⟨num, den⟩)

def intro (num : integer) (den : ℕ) : rational :=
⟨integer.signum num (pos (integer.abs num) den)⟩

def add (n m : rational) : rational :=
intro (n.numerator * m.denominator + m.numerator * n.denominator)
      (n.denominator * m.denominator)
instance : has_add rational := ⟨add⟩

def neg (n : rational) : rational :=
⟨-n.val⟩
instance : has_neg rational := ⟨neg⟩

def sub (n m : rational) : rational := n + (-m)
instance : has_sub rational := ⟨sub⟩

def mul (n m : rational) : rational :=
intro (n.numerator * m.numerator) (n.denominator * m.denominator)
instance : has_mul rational := ⟨mul⟩

def inv (n : rational) : rational :=
intro (integer.signum n.numerator n.denominator) (integer.abs n.numerator)
instance : has_inv rational := ⟨inv⟩

def div (n m : rational) : rational := n * m⁻¹
instance : has_div rational := ⟨div⟩

instance : has_zero rational := ⟨intro 0 1⟩
instance : has_one rational := ⟨intro 1 1⟩

def le (n m : rational) : Prop :=
n.numerator * m.denominator ≤ m.numerator * n.denominator
instance : has_le rational := ⟨le⟩

def lt (n m : rational) : Prop := n + 1 ≤ m
instance : has_lt rational := ⟨lt⟩

end rational

end types
end ground_zero