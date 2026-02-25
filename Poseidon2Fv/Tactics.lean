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
    s!": F := e{expression - 36} c row"

  let full_sum_def_string :=
    s!"def full_sum_{round} {"{"}F ExtF C{"}"}" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]" ++
    s!"  (c : C F ExtF) (row: ℕ)" ++
    s!": F := e{expression - 35} c row"

  let state_def_string :=
    s!"def state{idx} {"{"}F ExtF C{"}"}" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]" ++
    s!"  (c : C F ExtF) (row: ℕ)" ++
    s!": Fin 16 → F :=" ++
    s!"  λ x => match x with" ++
    s!"    | 0 => e{expression - 34} c row" ++
    s!"    | 1 => e{expression - 33} c row" ++
    s!"    | 2 => e{expression - 31} c row" ++
    s!"    | 3 => e{expression - 29} c row" ++
    s!"    | 4 => e{expression - 26} c row" ++
    s!"    | 5 => e{expression - 23} c row" ++
    s!"    | 6 => e{expression - 21} c row" ++
    s!"    | 7 => e{expression - 18} c row" ++
    s!"    | 8 => e{expression - 15} c row" ++
    s!"    | 9 => e{expression - 13} c row" ++
    s!"    | 10 => e{expression - 11} c row" ++
    s!"    | 11 => e{expression - 9} c row" ++
    s!"    | 12 => e{expression - 7} c row" ++
    s!"    | 13 => e{expression - 5} c row" ++
    s!"    | 14 => e{expression - 3} c row" ++
    s!"    | 15 => e{expression - 1} c row" ++
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
  let state1 :=
    s!"def state{26 + 5*round}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
    s!"  λ x => match x with\n" ++
    s!"    | 0 => e{1409 + 56*round} c row\n" ++
    s!"    | x => state{25 + 5*round} c row x"

  let state1' :=
    s!"def state{26 + 5*round}'\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
    s!"  add_partial_round_constant (state{25 + 5*round} c row) {round}"

  let state1_equiv :=
    s!"lemma state{26 + 5*round}_equiv\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  state{26 + 5*round} c row = state{26 + 5*round}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{26 + 5*round} state{26 + 5*round}'\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  . simp [\n" ++
    s!"      add_partial_round_constant, partial_round_constants,\n" ++
    s!"      e{1409 + 56*round}, state{25 + 5*round}\n" ++
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
    s!"def state{27 + 5*round}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
    s!"  λ x => match x with\n" ++
    s!"    | 0 => e{1411 + 56*round} c row\n" ++
    s!"    | x => state{26 + 5*round} c row x"


  let state2' :=
    s!"def state{27 + 5*round}'\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 16 → F\n" ++
    s!"  | 0 => (state{26 + 5*round} c row 0) ^ 3\n" ++
    s!"  | x => state{26 + 5*round} c row x"

  let state2_equiv :=
    s!"lemma state{27 + 5*round}_equiv\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  state{27 + 5*round} c row = state{27 + 5*round}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{27 + 5*round} state{27 + 5*round}'\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  . simp [\n" ++
    s!"      e{1411 + 56*round}, e{1410 + 56*round}, state{26 + 5*round},\n" ++
    s!"      pow_three'\n" ++
    s!"    ]\n" ++
    s!"  all_goals simp"

  runAsCommand state2 log
  runAsCommand state2' log
  runAsCommand state2_equiv log

  let constraint1_equiv :=
    s!"lemma constraint_equiv_{128 + 2*round}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  constraint_{128 + 2*round} c row =\n" ++
    s!"  eval_sbox_7_1\n" ++
    s!"    ((partial_rounds c row {round}).sbox)\n" ++
    s!"    (state{26 + 5*round} c row 0)\n" ++
    s!":= by\n" ++
    s!"  simp [\n" ++
    s!"    constraint_{128 + 2*round},\n" ++
    s!"    eval_sbox_7_1,\n" ++
    s!"    partial_rounds,\n" ++
    s!"    state{26 + 5*round},\n" ++
    s!"    sub_eq_zero,\n" ++
    s!"    e{1412 + 56*round},\n" ++
    s!"    e{148 + 2*round},\n" ++
    s!"    e{1411 + 56*round}, e{1410 + 56*round}\n" ++
    s!"  ]"

  runAsCommand constraint1_equiv log

  let state3 :=
    s!"def state{28 + 5*round}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
    s!"  λ x => match x with\n" ++
    s!"    | 0 => e{1414 + 56*round} c row\n" ++
    s!"    | x => state{26 + 5*round} c row x"

  let state3' :=
    s!"def state{28 + 5*round}'\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 16 → F\n" ++
    s!"  | 0 => (state{26 + 5*round} c row 0) ^ 7\n" ++
    s!"  | x => state{26 + 5*round} c row x"

  let state3_equiv :=
    s!"lemma state{28 + 5*round}_equiv\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!"  (h : constraint_{128 + 2*round} c row)\n" ++
    s!":\n" ++
    s!"  state{28 + 5*round} c row = state{28 + 5*round}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{28 + 5*round} state{28 + 5*round}'\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  . simp [\n" ++
    s!"      constraint_equiv_{128 + 2*round} c row,\n" ++
    s!"      eval_sbox_7_1,\n" ++
    s!"      partial_rounds, state{26 + 5*round},\n" ++
    s!"      sub_eq_zero\n" ++
    s!"    ] at h\n" ++
    s!"    simp [\n" ++
    s!"      e{1414 + 56*round}, state{26 + 5*round},\n" ++
    s!"      e{1413 + 56*round},\n" ++
    s!"      e{148 + 2*round},\n" ++
    s!"      h\n" ++
    s!"    ]\n" ++
    s!"    grind\n" ++
    s!"  all_goals simp"

  runAsCommand state3 log
  runAsCommand state3' log
  runAsCommand state3_equiv log

  let constraint2_equiv :=
    s!"lemma constraint_equiv_{129 + 2*round}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!":\n" ++
    s!"  constraint_{129 + 2*round} c row =\n" ++
    s!"  (state{28 + 5*round} c row 0 = (partial_rounds c row {round}).post_sbox)\n" ++
    s!":= by\n" ++
    s!"  simp [\n" ++
    s!"    constraint_{129 + 2*round},\n" ++
    s!"    e{1415 + 56*round},\n" ++
    s!"    sub_eq_zero,\n" ++
    s!"    state{28 + 5*round},\n" ++
    s!"    partial_rounds,\n" ++
    s!"    e{149 + 2*round}\n" ++
    s!"  ]"

  runAsCommand constraint2_equiv log

  let state4 :=
    s!"def state{29 + 5*round}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
    s!"  λ x => match x with\n" ++
    s!"    | 0 => e{149 + 2*round} c row\n" ++
    s!"    | x => state{28 + 5*round} c row x"

  let state4' :=
    s!"def state{29 + 5*round}'\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
    s!"  state{28 + 5*round} c row"

  let state4_equiv :=
    s!"lemma state{29 + 5*round}_equiv\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!"  (h : constraint_{129 + 2*round} c row)\n" ++
    s!":\n" ++
    s!"  state{29 + 5*round} c row = state{29 + 5*round}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{29 + 5*round} state{29 + 5*round}'\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  . simp [\n" ++
    s!"      constraint_equiv_{129 + 2*round},\n" ++
    s!"      partial_rounds\n" ++
    s!"    ] at h\n" ++
    s!"    simp [e{149 + 2*round}, h]\n" ++
    s!"  all_goals simp"

  runAsCommand state4 log
  runAsCommand state4' log
  runAsCommand state4_equiv log

  let state5 :=
    s!"#define_internal_matrix_state {30 + 5*round} {1465 + 56*round} {round}"

  let state5' :=
    s!"def state{30 + 5*round}'\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
    s!"  generic_internal_linear_layer (state{29 + 5*round} c row)"

  let state5_equiv :=
    s!"lemma state{30 + 5*round}_equiv\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row : ℕ)\n" ++
    s!"  (h_halve : ∀ x: F, x * 1006632961 = x / 2)\n" ++
    s!"  (h_div_pow_2 : ∀ x: F, x * 1509949441 = x / 2 ^ 2)\n" ++
    s!"  (h_div_pow_3 : ∀ x: F, x * 1761607681 = x / 2 ^ 3)\n" ++
    s!"  (h_div_pow_4 : ∀ x: F, x * 1887436801 = x / 2 ^ 4)\n" ++
    s!"  (h_div_pow_8 : ∀ x: F, x * 2005401601 = x / 2 ^ 8)\n" ++
    s!"  (h_div_pow_27 : ∀ x: F, x * 2013265906 = x / 2 ^ 27)\n" ++
    s!":\n" ++
    s!"  state{30 + 5*round} c row = state{30 + 5*round}' c row\n" ++
    s!":= by\n" ++
    s!"  unfold state{30 + 5*round} state{30 + 5*round}'\n" ++
    s!"  funext x\n" ++
    s!"  fin_cases x\n" ++
    s!"  all_goals (\n" ++
    s!"    simp [\n" ++
    s!"      generic_internal_linear_layer,\n" ++
    s!"      internal_layer_mat_mul,\n" ++
    s!"      state{29 + 5*round},\n" ++
    s!"      state{28 + 5*round},\n" ++
    s!"      state{26 + 5*round},\n" ++
    s!"      state{25 + 5*round},\n" ++
    s!"      ←h_halve,\n" ++
    s!"      ←h_div_pow_2,\n" ++
    s!"      ←h_div_pow_3,\n" ++
    s!"      ←h_div_pow_4,\n" ++
    s!"      ←h_div_pow_8,\n" ++
    s!"      ←h_div_pow_27,\n" ++
    s!"    ]\n" ++
    s!"  )\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr\n" ++
    s!"  . congr"

  runAsCommand state5 log
  runAsCommand state5' log
  runAsCommand state5_equiv log

  let round_lemma :=
    s!"lemma partial_round_{round}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!"  (h1: constraint_{128 + 2*round} c row)\n" ++
    s!"  (h2: constraint_{129 + 2*round} c row)\n" ++
    s!"  (h_halve : ∀ x: F, x * 1006632961 = x / 2)\n" ++
    s!"  (h_div_pow_2 : ∀ x: F, x * 1509949441 = x / 2 ^ 2)\n" ++
    s!"  (h_div_pow_3 : ∀ x: F, x * 1761607681 = x / 2 ^ 3)\n" ++
    s!"  (h_div_pow_4 : ∀ x: F, x * 1887436801 = x / 2 ^ 4)\n" ++
    s!"  (h_div_pow_8 : ∀ x: F, x * 2005401601 = x / 2 ^ 8)\n" ++
    s!"  (h_div_pow_27 : ∀ x: F, x * 2013265906 = x / 2 ^ 27)\n" ++
    s!":\n" ++
    s!"  state{30 + 5*round} c row =\n" ++
    s!"  partial_round (\n" ++
    s!"    state{25 + 5*round} c row\n" ++
    s!"  ) {round}\n" ++
    s!":= by\n" ++
    s!"\n" ++
    s!"  rewrite [\n" ++
    s!"    state{30 + 5*round}_equiv c row h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27\n" ++
    s!"  ]\n" ++
    s!"  unfold state{30 + 5*round}' partial_round\n" ++
    s!"\n" ++
    s!"  rewrite [state{29 + 5*round}_equiv c row h2]\n" ++
    s!"  unfold state{29 + 5*round}'\n" ++
    s!"\n" ++
    s!"  rewrite [state{28 + 5*round}_equiv c row h1]\n" ++
    s!"  unfold state{28 + 5*round}'\n" ++
    s!"\n" ++
    s!"  rewrite [state{26 + 5*round}_equiv c row]\n" ++
    s!"  unfold state{26 + 5*round}'\n" ++
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
    s!": Fin 16 → F :=\n" ++
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

  define_opaque_state state (expr_base + 184*round) 6 log
  runAsCommand state1' log
  runAsCommand state1_equiv log

  let state2' :=
    s!"def state{state+1}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
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

  define_opaque_state (state+1) (expr_base + 2 + 184*round) 6 log
  runAsCommand state2' log
  runAsCommand state2_equiv log

  let state3' :=
    s!"def state{state+2}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
    s!"  λ x => state{state+1} c row x"

  define_opaque_state (state+2) (col_base + 3 + 32*round) 1 log
  runAsCommand state3' log
  prove_eval_sbox_constraints (constraint_base + 32*round) round state 16 scope log

  let state4' :=
    s!"def state{state+3}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
    s!"  λ x => state{state} c row x ^ 7\n"

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
    s!"  have (x: F) : x * x * x * (x * x * x) * x = x^7 := by grind\n" ++
    s!"  simp [\n" ++
    s!"    {scope}_full_round_{round}_sbox_constraints,\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+1},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+2},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+3},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+4},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+5},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+6},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+7},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+8},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+9},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+10},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+11},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+12},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+13},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+14},\n" ++
    s!"    constraint_equiv_{constraint_base + 32*round+15},\n" ++
    s!"    eval_sbox_7_1,\n" ++
    s!"    {scope}_full_rounds,\n" ++
    s!"    state{state},\n" ++
    s!"    sub_eq_zero\n" ++
    s!"  ] at h\n" ++
    s!"  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h\n" ++
    s!"  fin_cases x <;> (\n" ++
    s!"    simp [\n" ++
    s!"      ←this,\n" ++
    s!"      ←h0, ←h1, ←h2, ←h3, ←h4, ←h5, ←h6, ←h7, ←h8, ←h9, ←h10, ←h11, ←h12, ←h13, ←h14, ←h15\n" ++
    s!"    ]\n" ++
    s!"    rfl\n" ++
    s!"  )"

  define_opaque_state (state+3) (expr_base + 5 + 184*round) 6 log
  runAsCommand state4' log
  define_constraint_group s!"{scope}_full_round_{round}_sbox_constraints" (constraint_base + 32*round) 16 log
  runAsCommand state4_equiv log

  let state5' :=
    s!"def state{state+4}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
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

  define_opaque_state (state+4) (expr_base + 152 + 184*round) 1 log
  runAsCommand state5' log
  runAsCommand state5_equiv log

  let state6' :=
    s!"def state{state+5}' {"{"}F ExtF C{"}"}\n" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]\n" ++
    s!"  (c : C F ExtF) (row: ℕ)\n" ++
    s!": Fin 16 → F :=\n" ++
    s!"  λ x => (Circuit.main c ({col_base + 16 + 32*round} + x.val) row 0)"

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
    s!"    constraint_{constraint_base+16+32*round},\n" ++
    s!"    constraint_{constraint_base+17+32*round},\n" ++
    s!"    constraint_{constraint_base+18+32*round},\n" ++
    s!"    constraint_{constraint_base+19+32*round},\n" ++
    s!"    constraint_{constraint_base+20+32*round},\n" ++
    s!"    constraint_{constraint_base+21+32*round},\n" ++
    s!"    constraint_{constraint_base+22+32*round},\n" ++
    s!"    constraint_{constraint_base+23+32*round},\n" ++
    s!"    constraint_{constraint_base+24+32*round},\n" ++
    s!"    constraint_{constraint_base+25+32*round},\n" ++
    s!"    constraint_{constraint_base+26+32*round},\n" ++
    s!"    constraint_{constraint_base+27+32*round},\n" ++
    s!"    constraint_{constraint_base+28+32*round},\n" ++
    s!"    constraint_{constraint_base+29+32*round},\n" ++
    s!"    constraint_{constraint_base+30+32*round},\n" ++
    s!"    constraint_{constraint_base+31+32*round},\n" ++
    s!"    e{expr_base + 168 + 184*round},\n" ++
    s!"    e{expr_base + 169 + 184*round},\n" ++
    s!"    e{expr_base + 170 + 184*round},\n" ++
    s!"    e{expr_base + 171 + 184*round},\n" ++
    s!"    e{expr_base + 172 + 184*round},\n" ++
    s!"    e{expr_base + 173 + 184*round},\n" ++
    s!"    e{expr_base + 174 + 184*round},\n" ++
    s!"    e{expr_base + 175 + 184*round},\n" ++
    s!"    e{expr_base + 176 + 184*round},\n" ++
    s!"    e{expr_base + 177 + 184*round},\n" ++
    s!"    e{expr_base + 178 + 184*round},\n" ++
    s!"    e{expr_base + 179 + 184*round},\n" ++
    s!"    e{expr_base + 180 + 184*round},\n" ++
    s!"    e{expr_base + 181 + 184*round},\n" ++
    s!"    e{expr_base + 182 + 184*round},\n" ++
    s!"    e{expr_base + 183 + 184*round},\n" ++
    s!"    sub_eq_zero\n" ++
    s!"  ] at h\n" ++
    s!"  simp [h]\n" ++
    s!"  fin_cases x <;> rfl\n"

  define_opaque_state (state+5) (expr_base + 152 + 184*round) 1 log
  runAsCommand state6' log
  define_constraint_group s!"{scope}_full_round_{round}_post_constraints" (constraint_base + 16 + 32*round) 16 log
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


elab "#prove_beginning_full_round" round:num : command => do
  prove_full_round round.getNat (round.getNat*6 + 2) 673 17 0 "beginning"

elab "#prove_beginning_full_round?" round:num : command => do
  prove_full_round round.getNat (round.getNat*6 + 2) 673 17 0 "beginning" true

elab "#prove_ending_full_round" round:num : command => do
  prove_full_round round.getNat (round.getNat*6 + 91) 2137 171 154 "ending"

elab "#prove_ending_full_round?" round:num : command => do
  prove_full_round round.getNat (round.getNat*6 + 91) 2137 171 154 "ending" true
