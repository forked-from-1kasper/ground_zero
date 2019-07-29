open lean.parser interactive tactic native
-- https://github.com/gebner/hott3/blob/master/src/hott/init/meta/support.lean

meta def expr.constants (e : expr) : list name :=
rb_map.keys $ e.fold (rb_map.mk name unit) (λ e _ buff, match e with
| expr.const name _ := buff.insert name unit.star
| _ := buff
end)

def test {α : Type} {a b : α} (p q : a = b) : p = q :=
begin symmetry, cases p, cases q, reflexivity end

namespace ground_zero.meta.hott_theory

meta def exec_cmd (cmd : string) : lean.parser unit :=
with_input command_like cmd >> pure ()

@[user_command] meta def hott (meta_info : decl_meta_info)
  (_ : parse $ tk "hott theory") : lean.parser unit :=
  exec_cmd "local infix ` = ` := ground_zero.types.eq"

end ground_zero.meta.hott_theory