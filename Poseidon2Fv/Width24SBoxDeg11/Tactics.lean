import Lean
import Mathlib
import LeanZKCircuit_Plonky3.Plonky3.Command.util

open Plonky3

def define_opaque_state
  (idx: ℕ) (expression : ℕ) (step: ℕ) (log: Bool := false)
: Lean.Elab.Command.CommandElabM Unit := do
  let def_string :=
    s!"def state{idx} {"{"}F ExtF C{"}"}" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]" ++
    s!"  (c : C F ExtF) (row: ℕ)" ++
    s!": Fin 24 → F :=" ++
    s!"  λ x => match x with" ++
    s!"    | 0 => e{expression} c row" ++
    s!"    | 1 => e{expression + step} c row" ++
    s!"    | 2 => e{expression + 2*step} c row" ++
    s!"    | 3 => e{expression + 3*step} c row" ++
    s!"    | 4 => e{expression + 4*step} c row" ++
    s!"    | 5 => e{expression + 5*step} c row" ++
    s!"    | 6 => e{expression + 6*step} c row" ++
    s!"    | 7 => e{expression + 7*step} c row" ++
    s!"    | 8 => e{expression + 8*step} c row" ++
    s!"    | 9 => e{expression + 9*step} c row" ++
    s!"    | 10 => e{expression + 10*step} c row" ++
    s!"    | 11 => e{expression + 11*step} c row" ++
    s!"    | 12 => e{expression + 12*step} c row" ++
    s!"    | 13 => e{expression + 13*step} c row" ++
    s!"    | 14 => e{expression + 14*step} c row" ++
    s!"    | 15 => e{expression + 15*step} c row" ++
    s!"    | 16 => e{expression + 16*step} c row" ++
    s!"    | 17 => e{expression + 17*step} c row" ++
    s!"    | 18 => e{expression + 18*step} c row" ++
    s!"    | 19 => e{expression + 19*step} c row" ++
    s!"    | 20 => e{expression + 20*step} c row" ++
    s!"    | 21 => e{expression + 21*step} c row" ++
    s!"    | 22 => e{expression + 22*step} c row" ++
    s!"    | 23 => e{expression + 23*step} c row" ++
    s!"    | _ => 0"
  runAsCommand def_string log

elab "#define_opaque_state" idx:num expression:num step:num : command => do
  define_opaque_state idx.getNat expression.getNat step.getNat

elab "#define_opaque_state?" idx:num expression:num step:num : command => do
  define_opaque_state idx.getNat expression.getNat step.getNat true


-- expression is the number after the end of the state
def define_internal_matrix_state
  (idx: ℕ) (expression : ℕ) (round : ℕ) (log: Bool := false)
: Lean.Elab.Command.CommandElabM Unit := do
  let part_sum_def_string :=
    s!"def part_sum_{round} {"{"}F ExtF C{"}"}" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]" ++
    s!"  (c : C F ExtF) (row: ℕ)" ++
    s!": F := e{expression - 52} c row"

  let full_sum_def_string :=
    s!"def full_sum_{round} {"{"}F ExtF C{"}"}" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]" ++
    s!"  (c : C F ExtF) (row: ℕ)" ++
    s!": F := e{expression - 51} c row"

  let state_def_string :=
    s!"def state{idx} {"{"}F ExtF C{"}"}" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]" ++
    s!"  (c : C F ExtF) (row: ℕ)" ++
    s!": Fin 24 → F :=" ++
    s!"  λ x => match x with" ++
    s!"    | 0 => e{expression - 50} c row" ++
    s!"    | 1 => e{expression - 49} c row" ++
    s!"    | 2 => e{expression - 47} c row" ++
    s!"    | 3 => e{expression - 45} c row" ++
    s!"    | 4 => e{expression - 42} c row" ++
    s!"    | 5 => e{expression - 39} c row" ++
    s!"    | 6 => e{expression - 37} c row" ++
    s!"    | 7 => e{expression - 34} c row" ++
    s!"    | 8 => e{expression - 31} c row" ++
    s!"    | 9 => e{expression - 29} c row" ++
    s!"    | 10 => e{expression - 27} c row" ++
    s!"    | 11 => e{expression - 25} c row" ++
    s!"    | 12 => e{expression - 23} c row" ++
    s!"    | 13 => e{expression - 21} c row" ++
    s!"    | 14 => e{expression - 19} c row" ++
    s!"    | 15 => e{expression - 17} c row" ++
    s!"    | 16 => e{expression - 15} c row" ++
    s!"    | 17 => e{expression - 13} c row" ++
    s!"    | 18 => e{expression - 11} c row" ++
    s!"    | 19 => e{expression - 9} c row" ++
    s!"    | 20 => e{expression - 7} c row" ++
    s!"    | 21 => e{expression - 5} c row" ++
    s!"    | 22 => e{expression - 3} c row" ++
    s!"    | 23 => e{expression - 1} c row" ++
    s!"    | _ => 0"

  runAsCommand part_sum_def_string log
  runAsCommand full_sum_def_string log
  runAsCommand state_def_string log

elab "#define_internal_matrix_state" idx:num expression:num round:num : command => do
  define_internal_matrix_state idx.getNat expression.getNat round.getNat

elab "#define_internal_matrix_state?" idx:num expression:num round:num : command => do
  define_internal_matrix_state idx.getNat expression.getNat round.getNat true

def define_constraint_group_string
  (start: ℕ) (count: ℕ)
: String :=
  if count = 0 then
    "  True"
  else
    s!"  constraint_{start} c row ∧" ++
    s!"{define_constraint_group_string (start+1) (count-1)}"

def define_constraint_group
  (name: String) (start: ℕ) (count: ℕ) (log: Bool := false)
: Lean.Elab.Command.CommandElabM Unit := do
  let def_string :=
    s!"def {name} {"{"}F ExtF C{"}"}" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]" ++
    s!"  (c : C F ExtF) (row: ℕ)" ++
    s!": Prop :=" ++
    s!"{define_constraint_group_string start count}"

  runAsCommand def_string log

elab "#define_constraint_group" name:str start:num count:num : command => do
  define_constraint_group name.getString start.getNat count.getNat

elab "#define_constraint_group?" name:str start:num count:num : command => do
  define_constraint_group name.getString start.getNat count.getNat true

def tag_simp_range
  (name: String) (start: ℕ) (count : ℕ) (step: ℕ) (tag: String) (log: Bool := false)
: Lean.Elab.Command.CommandElabM Unit := do
  if count ≠ 0 then
    runAsCommand s!"attribute [local {tag}] {name}{start}" log
    tag_simp_range name (start + step) (count - 1) step tag log

elab "#tag_simp_range" name:str start:num count:num step:num tag:str : command => do
  tag_simp_range name.getString start.getNat count.getNat step.getNat tag.getString

elab "#tag_simp_range?" name:str start:num count:num step:num tag:str : command => do
  tag_simp_range name.getString start.getNat count.getNat step.getNat tag.getString true

def prove_eval_sbox_r1_constraint
  (idx: ℕ) (constraint_idx: ℕ) (round: ℕ) (state: ℕ) (scope : String) (log: Bool := false)
: Lean.Elab.Command.CommandElabM Unit := do
  let lemma_string :=
    s!"lemma constraint_equiv_{constraint_idx}"++
    s!"  {"{"}C : Type → Type → Type{"}"} {"{"}F ExtF : Type{"}"}"++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]"++
    s!"  (c : C F ExtF) (row: ℕ)"++
    s!":"++
    s!"  constraint_{constraint_idx} c row ="++
    s!"  eval_sbox_11_2_r1"++
    s!"    (({scope}_full_rounds c row {round}).sbox_r1 {idx})"++
    s!"    (state{state} c row {idx})"++
    s!":= rfl"

  runAsCommand lemma_string log

def prove_eval_sbox_r2_constraint
  (idx: ℕ) (constraint_idx: ℕ) (round: ℕ) (scope : String) (log: Bool := false)
: Lean.Elab.Command.CommandElabM Unit := do
  let lemma_string :=
    s!"lemma constraint_equiv_{constraint_idx}"++
    s!"  {"{"}C : Type → Type → Type{"}"} {"{"}F ExtF : Type{"}"}"++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]"++
    s!"  (c : C F ExtF) (row: ℕ)"++
    s!":"++
    s!"  constraint_{constraint_idx} c row ="++
    s!"  eval_sbox_11_2_r2"++
    s!"    (({scope}_full_rounds c row {round}).sbox_r2 {idx})"++
    s!"    (({scope}_full_rounds c row {round}).sbox_r1 {idx})"++
    s!":= rfl"

  runAsCommand lemma_string log

def prove_eval_sbox_constraints
  (start_constraint: ℕ) (round: ℕ) (state: ℕ) (width: ℕ) (scope : String) (log: Bool := false)
: Lean.Elab.Command.CommandElabM Unit := do
  if width ≠ 0 then
    prove_eval_sbox_r1_constraint
      (width - 1)
      (start_constraint + width * 2 - 2)
      round
      state
      scope
      log
    prove_eval_sbox_r2_constraint
      (width - 1)
      (start_constraint + width * 2 - 1)
      round
      scope
      log
    prove_eval_sbox_constraints start_constraint round state (width - 1) scope log

elab "#prove_eval_sbox_constraints" start_constraint:num round:num state:num width:num scope:str : command => do
  prove_eval_sbox_constraints start_constraint.getNat round.getNat state.getNat width.getNat scope.getString

elab "#prove_eval_sbox_constraints?" start_constraint:num round:num state:num width:num scope:str : command => do
  prove_eval_sbox_constraints start_constraint.getNat round.getNat state.getNat width.getNat scope.getString true

def prove_full_round_post_constraint
  (idx: ℕ) (constraint_idx: ℕ) (round: ℕ) (state: ℕ) (log: Bool := false)
: Lean.Elab.Command.CommandElabM Unit := do
  let lemma_string :=
    s!"lemma constraint_equiv_{constraint_idx}\n" ++
    s!"  {"{"}C : Type → Type → Type{"}"} {"{"}F ExtF : Type{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  constraint_{constraint_idx} c row =\n" ++
    s!"  (state{state} c row {idx} -\n" ++
    s!"  (beginning_full_rounds c row {round}).post {idx} =\n" ++
    s!"  0)\n" ++
    s!":= rfl"

  runAsCommand lemma_string log

def prove_full_round_post_constraints
  (start_constraint: ℕ) (round: ℕ) (state: ℕ) (width: ℕ) (log: Bool := false)
: Lean.Elab.Command.CommandElabM Unit := do
  if width ≠ 0 then
    prove_full_round_post_constraint
      (width - 1)
      (start_constraint + width - 1)
      round
      state
      log
    prove_full_round_post_constraints start_constraint round state (width - 1) log

elab "#prove_full_round_post_constraints" start_constraint:num round:num state:num width:num : command => do
  prove_full_round_post_constraints start_constraint.getNat round.getNat state.getNat width.getNat

elab "#prove_full_round_post_constraints?" start_constraint:num round:num state:num width:num : command => do
  prove_full_round_post_constraints start_constraint.getNat round.getNat state.getNat width.getNat true

def prove_partial_round
  (round : ℕ) (log: Bool := false)
: Lean.Elab.Command.CommandElabM Unit := do
  let base_starting_state := 26
  let states_per_round := 6
  let state := base_starting_state + states_per_round*round

  let base_starting_expression := 2745
  let expressions_per_round := 82
  let starting_expression := base_starting_expression + expressions_per_round * round

  let base_starting_constraint := 288
  let sbox_registers := 2
  let constraints_per_round := sbox_registers + 1
  let starting_constraint := base_starting_constraint + constraints_per_round * round

  let width := 24
  let base_starting_column := base_starting_constraint + width + 1
  let column_expr_offset := 3
  let column_expr := column_expr_offset + base_starting_column + constraints_per_round * round

  let sbox_constraint_1 := "eval_sbox_11_2_r1"
  let sbox_member_1 := "sbox_r1"
  let sbox_constraint_2 := "eval_sbox_11_2_r2"
  let sbox_member_2 := "sbox_r2"

  let state1 :=
    s!"def state{state} {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  λ x => match x with\n" ++
    s!"    | 0 => e{starting_expression} c row\n" ++
    s!"    | x => state{state-1} c row x"

  let state1' :=
    s!"def state{state}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  add_partial_round_constant (state{state - 1} c row) {round}"

  let state1_equiv :=
    s!"lemma state{state}_equiv {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  state{state} c row = state{state}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{state} state{state}'\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  . simp [\n" ++
    s!"      add_partial_round_constant, partial_round_constants,\n" ++
    s!"      e{starting_expression}, state{state - 1}\n" ++
    s!"    ]\n" ++
    s!"  all_goals (\n" ++
    s!"    simp [\n" ++
    s!"      add_partial_round_constant\n" ++
    s!"    ]\n" ++
    s!"  )"

  runAsCommand state1 log
  runAsCommand state1' log
  runAsCommand state1_equiv log

  let state2 :=
    s!"def state{state + 1} {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  λ x => match x with\n" ++
    s!"    | 0 => e{starting_expression + 2} c row\n" ++
    s!"    | x => state{state} c row x"


  let state2' :=
    s!"def state{state + 1}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 24 → F\n" ++
    s!"  | 0 => (state{state} c row 0) ^ 3\n" ++
    s!"  | x => state{state} c row x"

  let state2_equiv :=
    s!"lemma state{state + 1}_equiv {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  state{state + 1} c row = state{state + 1}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{state + 1} state{state + 1}'\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  . simp [\n" ++
    s!"      e{starting_expression + 2}, e{starting_expression + 1}, state{state},\n" ++
    s!"      pow_three'\n" ++
    s!"    ]\n" ++
    s!"  all_goals rfl"

  runAsCommand state2 log
  runAsCommand state2' log
  runAsCommand state2_equiv log

  let constraint1_equiv :=
    s!"lemma constraint_equiv_{starting_constraint} {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  constraint_{starting_constraint} c row =\n" ++
    s!"  {sbox_constraint_1}\n" ++
    s!"    ((partial_rounds c row {round}).{sbox_member_1})\n" ++
    s!"    (state{state} c row 0)\n" ++
    s!":= rfl"

  runAsCommand constraint1_equiv log

  let state3 :=
    s!"def state{state + 2} {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  λ x => match x with\n" ++
    s!"    | 0 => e{starting_expression + 5} c row\n" ++
    s!"    | x => state{state} c row x"

  let state3' :=
    s!"def state{state + 2}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 24 → F\n" ++
    s!"  | 0 => (state{state} c row 0) ^ 9\n" ++
    s!"  | x => state{state} c row x"

  let state3_equiv :=
    s!"lemma state{state + 2}_equiv {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!"  (h : constraint_{starting_constraint} c row)\n" ++
    s!":\n" ++
    s!"  state{state + 2} c row = state{state + 2}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{state + 2} state{state + 2}'\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  . simp [\n" ++
    s!"      constraint_equiv_{starting_constraint} c row,\n" ++
    s!"      {sbox_constraint_1},\n" ++
    s!"      partial_rounds, state{state},\n" ++
    s!"      sub_eq_zero\n" ++
    s!"    ] at h\n" ++
    s!"    simp [\n" ++
    s!"      e{starting_expression+5}, e{starting_expression+4},\n" ++
    s!"      e{column_expr},\n" ++
    s!"      state{state},\n" ++
    s!"      h\n" ++
    s!"    ]\n" ++
    s!"    ring\n" ++
    s!"  all_goals rfl"

  runAsCommand state3 log
  runAsCommand state3' log
  runAsCommand state3_equiv log

  let constraint2_equiv :=
    s!"lemma constraint_equiv_{starting_constraint+1} {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  constraint_{starting_constraint+1} c row =\n" ++
    s!"  {sbox_constraint_2}\n" ++
    s!"    ((partial_rounds c row {round}).{sbox_member_2})\n" ++
    s!"    ((partial_rounds c row {round}).{sbox_member_1})\n" ++
    s!":= rfl"

  runAsCommand constraint2_equiv log

  let state4 :=
    s!"def state{state + 3} {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  λ x => match x with\n" ++
    s!"    | 0 => e{starting_expression + 7} c row\n" ++
    s!"    | x => state{state} c row x"

  let state4' :=
    s!"def state{state + 3}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 24 → F\n" ++
    s!"  | 0 => (state{state} c row 0) ^ 11\n" ++
    s!"  | x => state{state} c row x"

  let state4_equiv :=
    s!"lemma state{state + 3}_equiv {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!"  (h1 : constraint_{starting_constraint} c row)\n" ++
    s!"  (h2 : constraint_{starting_constraint+1} c row)\n" ++
    s!":\n" ++
    s!"  state{state + 3} c row = state{state + 3}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{state + 3} state{state + 3}'\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  . simp [\n" ++
    s!"      constraint_equiv_{starting_constraint} c row,\n" ++
    s!"      {sbox_constraint_1},\n" ++
    s!"      partial_rounds,\n" ++
    s!"      sub_eq_zero\n" ++
    s!"    ] at h1\n" ++
    s!"    simp [\n" ++
    s!"      constraint_equiv_{starting_constraint+1} c row,\n" ++
    s!"      {sbox_constraint_2},\n" ++
    s!"      partial_rounds,\n" ++
    s!"      sub_eq_zero\n" ++
    s!"    ] at h2\n" ++
    s!"    simp [\n" ++
    s!"      state{state},\n" ++
    s!"      e{starting_expression+7},\n"++
    s!"      e{starting_expression+1},\n" ++
    s!"      e{column_expr+1},\n" ++
    s!"      h1, h2\n" ++
    s!"    ]\n" ++
    s!"    ring\n" ++
    s!"  all_goals rfl"

  runAsCommand state4 log
  runAsCommand state4' log
  runAsCommand state4_equiv log

  let constraint3_equiv :=
    s!"lemma constraint_equiv_{starting_constraint+2} {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  constraint_{starting_constraint+2} c row =\n" ++
    s!"  (state{state + 3} c row 0 = (partial_rounds c row {round}).post_sbox)\n" ++
    s!":= by\n" ++
    s!"  simp [\n" ++
    s!"    constraint_{starting_constraint+2},\n" ++
    s!"    e{starting_expression+8},\n" ++
    s!"    sub_eq_zero,\n" ++
    s!"    state{state + 3},\n" ++
    s!"    partial_rounds,\n" ++
    s!"    e{column_expr+2}\n" ++
    s!"  ]"

  runAsCommand constraint3_equiv log

  let state5 :=
    s!"def state{state + 4} {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  λ x => match x with\n" ++
    s!"    | 0 => e{column_expr+2} c row\n" ++
    s!"    | x => state{state + 3} c row x"

  let state5' :=
    s!"def state{state + 4}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  state{state + 3} c row"

  let state5_equiv :=
    s!"lemma state{state + 4}_equiv {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!"  (h : constraint_{starting_constraint+2} c row)\n" ++
    s!":\n" ++
    s!"  state{state + 4} c row = state{state + 4}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{state + 4} state{state + 4}'\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  . simp [\n" ++
    s!"      constraint_equiv_{starting_constraint+2},\n" ++
    s!"      partial_rounds\n" ++
    s!"    ] at h\n" ++
    s!"    simp [e{column_expr+2}, h]\n" ++
    s!"  all_goals rfl"

  runAsCommand state5 log
  runAsCommand state5' log
  runAsCommand state5_equiv log

  let state6 :=
    s!"#define_internal_matrix_state {state + 5} {starting_expression+expressions_per_round} {round}"

  let state6' :=
    s!"def state{state + 5}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  generic_internal_linear_layer (state{state + 4} c row)"

  let state6_equiv :=
    s!"lemma state{state + 5}_equiv {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!"  (h_halve : ∀ x: F, x * 1006632961 = x / 2)\n" ++
    s!"  (h_div_pow_2 : ∀ x: F, x * 1509949441 = x / 2 ^ 2)\n" ++
    s!"  (h_div_pow_3 : ∀ x: F, x * 1761607681 = x / 2 ^ 3)\n" ++
    s!"  (h_div_pow_4 : ∀ x: F, x * 1887436801 = x / 2 ^ 4)\n" ++
    s!"  (h_div_pow_5 : ∀ x: F, x * 1950351361 = x / 2 ^ 5)\n" ++
    s!"  (h_div_pow_6 : ∀ x: F, x * 1981808641 = x / 2 ^ 6)\n" ++
    s!"  (h_div_pow_7 : ∀ x: F, x * 1997537281 = x / 2 ^ 7)\n" ++
    s!"  (h_div_pow_8 : ∀ x: F, x * 2005401601 = x / 2 ^ 8)\n" ++
    s!"  (h_div_pow_9 : ∀ x: F, x * 2009333761 = x / 2 ^ 9)\n" ++
    s!"  (h_div_pow_27 : ∀ x: F, x * 2013265906 = x / 2 ^ 27)\n" ++
    s!":\n" ++
    s!"  state{state + 5} c row = state{state + 5}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{state + 5} state{state + 5}'\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  all_goals (\n" ++
    s!"    simp [\n" ++
    s!"      generic_internal_linear_layer,\n" ++
    s!"      internal_layer_mat_mul,\n" ++
    s!"      state{state + 4},\n" ++
    s!"      state{state + 3},\n" ++
    s!"      state{state},\n" ++
    s!"      state{state - 1},\n" ++
    s!"      ←h_halve,\n" ++
    s!"      ←h_div_pow_2,\n" ++
    s!"      ←h_div_pow_3,\n" ++
    s!"      ←h_div_pow_4,\n" ++
    s!"      ←h_div_pow_5,\n" ++
    s!"      ←h_div_pow_6,\n" ++
    s!"      ←h_div_pow_7,\n" ++
    s!"      ←h_div_pow_8,\n" ++
    s!"      ←h_div_pow_9,\n" ++
    s!"      ←h_div_pow_27,\n" ++
    s!"    ]\n" ++
    s!"  )\n" ++
    s!"  all_goals rfl"

  runAsCommand state6 log
  runAsCommand state6' log
  runAsCommand state6_equiv log

  let round_lemma :=
    s!"lemma partial_round_{round} {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!"  (h1: constraint_{starting_constraint} c row)\n" ++
    s!"  (h2: constraint_{starting_constraint+1} c row)\n" ++
    s!"  (h3: constraint_{starting_constraint+2} c row)\n" ++
    s!"  (h_halve : ∀ x: F, x * 1006632961 = x / 2)\n" ++
    s!"  (h_div_pow_2 : ∀ x: F, x * 1509949441 = x / 2 ^ 2)\n" ++
    s!"  (h_div_pow_3 : ∀ x: F, x * 1761607681 = x / 2 ^ 3)\n" ++
    s!"  (h_div_pow_4 : ∀ x: F, x * 1887436801 = x / 2 ^ 4)\n" ++
    s!"  (h_div_pow_5 : ∀ x: F, x * 1950351361 = x / 2 ^ 5)\n" ++
    s!"  (h_div_pow_6 : ∀ x: F, x * 1981808641 = x / 2 ^ 6)\n" ++
    s!"  (h_div_pow_7 : ∀ x: F, x * 1997537281 = x / 2 ^ 7)\n" ++
    s!"  (h_div_pow_8 : ∀ x: F, x * 2005401601 = x / 2 ^ 8)\n" ++
    s!"  (h_div_pow_9 : ∀ x: F, x * 2009333761 = x / 2 ^ 9)\n" ++
    s!"  (h_div_pow_27 : ∀ x: F, x * 2013265906 = x / 2 ^ 27)\n" ++
    s!":\n" ++
    s!"  state{state + 5} c row =\n" ++
    s!"  partial_round (\n" ++
    s!"    state{state - 1} c row\n" ++
    s!"  ) {round}\n" ++
    s!":= by\n" ++
    s!"\n" ++
    s!"  rewrite [\n" ++
    s!"    state{state + 5}_equiv c row h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27\n" ++
    s!"  ]\n" ++
    s!"  unfold state{state + 5}' partial_round\n" ++
    s!"\n" ++
    s!"  rewrite [state{state + 4}_equiv c row h3]\n" ++
    s!"  unfold state{state + 4}'\n" ++
    s!"\n" ++
    s!"  rewrite [state{state + 3}_equiv c row h1 h2]\n" ++
    s!"  unfold state{state + 3}'\n" ++
    s!"\n" ++
    s!"  rewrite [state{state}_equiv c row]\n" ++
    s!"  unfold state{state}'\n" ++
    s!"  rfl"

  runAsCommand round_lemma log

elab "#prove_partial_round" round:num : command => do
  prove_partial_round round.getNat

elab "#prove_partial_round?" round:num : command => do
  prove_partial_round round.getNat true

def prove_full_round
  (round : ℕ) (state : ℕ) (expr_base: ℕ) (col_base: ℕ) (constraint_base: ℕ) (scope : String) (log: Bool := false)
: Lean.Elab.Command.CommandElabM Unit := do
  let state1' :=
    s!"def state{state}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  λ x => state{state-1} c row x + {scope}_full_round_constants {round} x"

  let state1_equiv :=
    s!"lemma state{state}_equiv {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!"  (h: {scope}_full_round_{round-1}_post_constraints c row)\n" ++
    s!":\n" ++
    s!"  state{state} c row = state{state}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{state} state{state}'\n" ++
    s!"  funext x\n" ++
    s!"  rewrite [state{state-1}_equiv c row h]\n" ++
    s!"  fin_cases x <;> rfl"

  define_opaque_state state (expr_base + 326*round) 8 log
  runAsCommand state1' log
  runAsCommand state1_equiv log

  let state2' :=
    s!"def state{state+1}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  λ x => state{state} c row x ^ 3"

  let state2_equiv :=
    s!"lemma state{state+1}_equiv {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  state{state+1} c row = state{state+1}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{state+1} state{state+1}' state{state}\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x <;> (\n" ++
    s!"    simp [pow_three']\n" ++
    s!"    congr\n" ++
    s!"  )"

  define_opaque_state (state+1) (expr_base + 2 + 326*round) 8 log
  runAsCommand state2' log
  runAsCommand state2_equiv log

  let state3' :=
    s!"def state{state+2}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  λ x => state{state+1} c row x"

  define_opaque_state (state+2) (col_base + 3 + 48*round) 1 log
  runAsCommand state3' log
  prove_eval_sbox_constraints (constraint_base + 72*round) round state 24 scope log
  -- if scope == "beginning" then

  let state4' :=
    s!"def state{state+3}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  λ x => state{state} c row x ^ 11\n" -- UP TO HERE and line 373 in diff between 788048a and 4b5b2cc

  let state4_equiv :=
    s!"lemma state{state+3}_equiv {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!"  (h: {scope}_full_round_{round}_sbox_constraints c row)\n" ++
    s!":\n" ++
    s!"  state{state+3} c row = state{state+3}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{state+3} state{state+3}' state{state}\n" ++
    s!"  funext x\n" ++
    s!"  have (x: F) : (x * x * x) * (x * x * x) * (x * x * x) * (x * x) = x^11 := by ring\n" ++
    s!"  simp [\n" ++
    s!"    {scope}_full_round_{round}_sbox_constraints,\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+1},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+2},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+3},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+4},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+5},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+6},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+7},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+8},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+9},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+10},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+11},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+12},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+13},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+14},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+15},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+16},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+17},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+18},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+19},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+20},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+21},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+22},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+23},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+24},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+25},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+26},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+27},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+28},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+29},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+30},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+31},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+32},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+33},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+34},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+35},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+36},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+37},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+38},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+39},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+40},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+41},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+42},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+43},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+44},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+45},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+46},\n" ++
    s!"    constraint_equiv_{constraint_base + 72*round+47},\n" ++
    s!"    eval_sbox_11_2_r1,\n" ++
    s!"    eval_sbox_11_2_r2,\n" ++
    s!"    {scope}_full_rounds,\n" ++
    s!"    state{state},\n" ++
    s!"    sub_eq_zero\n" ++
    s!"  ] at h\n" ++
    s!"  obtain ⟨\n" ++
    s!"     h0, h1, h2, h3, h4, h5, h6, h7, h8,\n" ++
    s!"     h9, h10, h11, h12, h13, h14, h15,\n" ++
    s!"     h16, h17, h18, h19, h20, h21, h22, h23,\n" ++
    s!"     h24, h25, h26, h27, h28, h29, h30, h31,\n" ++
    s!"     h32, h33, h34, h35, h36, h37, h38, h39,\n" ++
    s!"     h40, h41, h42, h43, h44, h45, h46, h47\n" ++
    s!"  ⟩ := h\n" ++
    s!"  fin_cases x <;> (\n" ++
    s!"    simp [\n" ++
    s!"      ←this,\n" ++
    s!"      ←h0, ←h1, ←h2, ←h3, ←h4, ←h5, ←h6, ←h7, ←h8, ←h9, ←h10, ←h11, ←h12, ←h13, ←h14, ←h15,\n" ++
    s!"      ←h16, ←h17, ←h18, ←h19, ←h20, ←h21, ←h22, ←h23, ←h24, ←h25, ←h26, ←h27, ←h28, ←h29, ←h30, ←h31,\n" ++
    s!"      ←h32, ←h33, ←h34, ←h35, ←h36, ←h37, ←h38, ←h39, ←h40, ←h41, ←h42, ←h43, ←h44, ←h45, ←h46, ←h47\n" ++
    s!"    ]\n" ++
    s!"    rfl\n" ++
    s!"  )"

  define_opaque_state (state+3) (expr_base + 7 + 326*round) 8 log
  runAsCommand state4' log
  define_constraint_group s!"{scope}_full_round_{round}_sbox_constraints" (constraint_base + 72*round) 48 log
  runAsCommand state4_equiv log

  let state5' :=
    s!"def state{state+4}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  mds_light_permutation (state{state+3} c row)"

  let state5_equiv :=
    s!"lemma state{state+4}_equiv {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  state{state+4} c row = state{state+4}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{state+4} state{state+4}' mds_light_permutation\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  all_goals (\n" ++
    s!"    simp [\n" ++
    s!"      state{state+3}, apply_m4_sums, apply_m4_loop, apply_m4\n" ++
    s!"    ]\n" ++
    s!"    congr\n" ++
    s!"  )"

  define_opaque_state (state+4) (expr_base + 278 + 326*round) 1 log
  runAsCommand state5' log
  runAsCommand state5_equiv log

  let state6' :=
    s!"def state{state+5}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Fin 24 → F :=\n" ++
    s!"  λ x => (Circuit.main c ({col_base + 48 + 72*round} + x.val) row 0)"

  let state6_equiv :=
    s!"lemma state{state+5}_equiv {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!"  (h: {scope}_full_round_{round}_post_constraints c row)\n" ++
    s!":\n" ++
    s!"  state{state+5} c row = state{state+5}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{state+5} state{state+5}'\n" ++
    s!"  funext x\n" ++
    s!"  simp [\n" ++
    s!"    {scope}_full_round_{round}_post_constraints,\n" ++
    s!"    constraint_{constraint_base+48+72*round},\n" ++
    s!"    constraint_{constraint_base+49+72*round},\n" ++
    s!"    constraint_{constraint_base+50+72*round},\n" ++
    s!"    constraint_{constraint_base+51+72*round},\n" ++
    s!"    constraint_{constraint_base+52+72*round},\n" ++
    s!"    constraint_{constraint_base+53+72*round},\n" ++
    s!"    constraint_{constraint_base+54+72*round},\n" ++
    s!"    constraint_{constraint_base+55+72*round},\n" ++
    s!"    constraint_{constraint_base+56+72*round},\n" ++
    s!"    constraint_{constraint_base+57+72*round},\n" ++
    s!"    constraint_{constraint_base+58+72*round},\n" ++
    s!"    constraint_{constraint_base+59+72*round},\n" ++
    s!"    constraint_{constraint_base+60+72*round},\n" ++
    s!"    constraint_{constraint_base+61+72*round},\n" ++
    s!"    constraint_{constraint_base+62+72*round},\n" ++
    s!"    constraint_{constraint_base+63+72*round},\n" ++
    s!"    constraint_{constraint_base+64+72*round},\n" ++
    s!"    constraint_{constraint_base+65+72*round},\n" ++
    s!"    constraint_{constraint_base+66+72*round},\n" ++
    s!"    constraint_{constraint_base+67+72*round},\n" ++
    s!"    constraint_{constraint_base+68+72*round},\n" ++
    s!"    constraint_{constraint_base+69+72*round},\n" ++
    s!"    constraint_{constraint_base+70+72*round},\n" ++
    s!"    constraint_{constraint_base+71+72*round},\n" ++
    s!"    e{expr_base + 302 + 0 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 1 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 2 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 3 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 4 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 5 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 6 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 7 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 8 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 9 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 10 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 11 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 12 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 13 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 14 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 15 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 16 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 17 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 18 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 19 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 20 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 21 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 22 + 326*round},\n" ++
    s!"    e{expr_base + 302 + 23 + 326*round},\n" ++
    s!"    sub_eq_zero\n" ++
    s!"  ] at h\n" ++
    s!"  simp [h]\n" ++
    s!"  fin_cases x <;> rfl\n"

  define_opaque_state (state+5) (expr_base + 278 + 326*round) 1 log
  runAsCommand state6' log
  define_constraint_group s!"{scope}_full_round_{round}_post_constraints" (constraint_base + 48 + 72*round) 24 log
  runAsCommand state6_equiv log

  let full_round_constraints :=
    s!"def {scope}_full_round_{round}_constraints {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Prop :=\n" ++
    s!"  {scope}_full_round_{round}_sbox_constraints c row ∧\n" ++
    s!"  {scope}_full_round_{round}_post_constraints c row"

  let full_round_lemma :=
    s!"lemma {scope}_full_round_{round} {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!"  (h0: {scope}_full_round_{round-1}_constraints c row)\n" ++
    s!"  (h1: {scope}_full_round_{round}_constraints c row)\n" ++
    s!":\n" ++
    s!"  ({scope}_full_rounds c row {round}).post =\n" ++
    s!"  {scope}_full_round (\n" ++
    s!"    ({scope}_full_rounds c row {round-1}).post\n" ++
    s!"  ) {round}\n" ++
    s!":= by\n" ++
    s!"  have ⟨h_sbox0, h_post0⟩ := h0\n" ++
    s!"  have ⟨h_sbox1, h_post1⟩ := h1\n" ++
    s!"\n" ++
    s!"  have := state{state-1}_equiv c row h_post0\n" ++
    s!"  unfold state{state-1}' at this\n" ++
    s!"  unfold {scope}_full_rounds\n" ++
    s!"  simp\n" ++
    s!"  rewrite [←this]; clear this\n" ++
    s!"\n" ++
    s!"  have := state{state}_equiv c row h_post0\n" ++
    s!"  unfold state{state}' at this\n" ++
    s!"  unfold {scope}_full_round add_{scope}_full_round_constants\n" ++
    s!"  rewrite [←this]; clear this\n" ++
    s!"\n" ++
    s!"  have := state{state+3}_equiv c row h_sbox1\n" ++
    s!"  unfold state{state+3}' at this\n" ++
    s!"  unfold apply_full_round_sbox\n" ++
    s!"  rewrite [←this]; clear this\n" ++
    s!"\n" ++
    s!"  have := state{state+4}_equiv c row\n" ++
    s!"  unfold state{state+4}' at this\n" ++
    s!"  rewrite [←this]; clear this\n" ++
    s!"\n" ++
    s!"  have := state{state+5}_equiv c row h_post1\n" ++
    s!"  unfold state{state+5}' at this\n" ++
    s!"  rewrite [←this]; clear this\n" ++
    s!"\n" ++
    s!"  rfl"

  runAsCommand full_round_constraints log
  runAsCommand full_round_lemma log
  -- else
  --   pure ()



elab "#prove_beginning_full_round" round:num : command => do
  prove_full_round round.getNat (round.getNat*6 + 2) 1441 25 0 "beginning"

elab "#prove_beginning_full_round?" round:num : command => do
  prove_full_round round.getNat (round.getNat*6 + 2) 1441 25 0 "beginning" true

elab "#prove_ending_full_round" round:num : command => do
  prove_full_round round.getNat (round.getNat*6 + 152) 4467 376 351 "ending"

elab "#prove_ending_full_round?" round:num : command => do
  prove_full_round round.getNat (round.getNat*6 + 152) 4467 376 351 "ending" true
