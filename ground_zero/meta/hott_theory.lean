open lean.parser interactive tactic native
-- https://github.com/gebner/hott3/blob/master/src/hott/init/meta/support.lean

meta def expr.constants (e : expr) : list name :=
rb_map.keys $ e.fold (rb_map.mk name unit) (λ e _ buff, match e with
| expr.const name _ := buff.insert name unit.star
| _ := buff
end)

meta def inst_args : expr → tactic expr | e := do
  t ← infer_type e >>= whnf,
  if t.is_pi then do
    x ← mk_local' t.binding_name t.binding_info t.binding_domain,
    inst_args (e.app x)
  else pure e

meta def has_large_elim (ind : name) : tactic bool := do
  type_former_is_prop ← mk_const ind >>= inst_args >>= is_prop,
  elim_is_prop ← mk_const (ind <.> "rec") >>= inst_args >>= is_proof,
  pure (type_former_is_prop ∧ ¬elim_is_prop)

meta def is_large_elim (n : name) : tactic bool := do
  env ← get_env,
  match env.recursor_of n with
  | some ind := has_large_elim ind
  | none := pure ff
  end

meta def has_attr (attr decl : name) : tactic bool :=
option.is_some <$> try_core (has_attribute attr decl)

meta def check_large_elim (chain : list name) (n : name) := do
  large_elim ← is_large_elim n,
  let chain' := string.intercalate " <- " (to_string <$> chain),
  when large_elim (tactic.fail $ sformat! "uses large eliminator: {chain'}")

meta def check_not_nothott (n : name) := do
  nothott ← has_attr `nothott n,
  when nothott (fail $ sformat! "“marked as [nothott]: {n}")

meta def check_decl (chain : list name) (n : name) := do
  is_safe ← has_attr `safe n,
  if is_safe then pure []
  else do
    check_large_elim chain n,
    check_not_nothott n,
    decl ← get_decl n,
    pure (decl.type.constants ++ decl.value.constants)

meta def check_hott' : list name → list name → rb_set name → tactic unit
| [] _ _ := pure ()
| (n :: todo) chain done :=
  if done.contains n then check_hott' todo chain done
  else let done' := done.insert n in do
    is_hott ← has_attr `hott n,
    if is_hott then check_hott' todo chain done'
    else do
      refd ← check_decl chain n,
      check_hott' refd (n :: chain) done',
      check_hott' todo chain done'

meta def check_hott (ns : list name) := check_hott' ns [] mk_rb_set

@[user_attribute] meta def hott : user_attribute :=
{ name         := `hott,
  descr        := "Marks a definition that can be safely used in HoTT",
  after_set    := some (λ n _ _, check_decl [n] n >>= check_hott),
  before_unset := some (λ _ _, skip) }

@[user_attribute] meta def safe : user_attribute :=
{ name         := `safe,
  descr        := "Unsafely marks a definition as safe for HoTT",
  before_unset := some (λ _ _, skip) }

@[user_attribute] meta def nothott : user_attribute :=
{ name         := `nothott,
  descr        := "Marks a defintion as unsafe for HoTT",
  before_unset := some (λ _ _, skip) }

abbreviation {u} Eq {α : Sort u} (a b : α) := a = b

namespace ground_zero.meta.hott_theory

meta def exec_cmd (cmd : string) : lean.parser unit :=
with_input command_like cmd >> pure ()

@[user_command] meta def hott (meta_info : decl_meta_info)
  (_ : parse $ tk "hott theory") : lean.parser unit :=
  exec_cmd "local infix ` ⇋ `:50 := Eq" >>
  exec_cmd "local infix ` = ` := ground_zero.types.Id"

end ground_zero.meta.hott_theory