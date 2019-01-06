open lean.parser interactive tactic

namespace ground_zero.meta.hott_theory
-- https://github.com/gebner/hott3/blob/master/src/hott/init/meta/support.lean

meta def exec_cmd (cmd : string) : lean.parser unit :=
with_input command_like cmd >> pure ()

@[user_command] meta def hott (meta_info : decl_meta_info)
  (_ : parse $ tk "hott theory") : lean.parser unit := do
  exec_cmd "local infix ` = ` := ground_zero.types.eq",
  pure ()

end ground_zero.meta.hott_theory