import Lean
import Mathlib
import LeanZKCircuit_Plonky3.Plonky3.Command.util

open Plonky3

def define_opaque_state
  (idx: ℕ) (expression : ℕ) (step: ℕ)
: Lean.Elab.Command.CommandElabM Unit := do
  let def_string :=
    s!"def state{idx} {"{"}F ExtF C{"}"}" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]" ++
    s!"  (c : C F ExtF) (row: ℕ)" ++
    s!": Fin 16 → F :=" ++
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
    s!"    | _ => 0"
  runAsCommand def_string

elab "#define_opaque_state" idx:num expression:num step:num : command => do
  define_opaque_state idx.getNat expression.getNat step.getNat


-- expression is the number after the end of the state
def define_internal_matrix_state
  (idx: ℕ) (expression : ℕ) (round : ℕ)
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

  runAsCommand part_sum_def_string
  runAsCommand full_sum_def_string
  runAsCommand state_def_string

elab "#define_internal_matrix_state" idx:num expression:num round:num : command => do
  define_internal_matrix_state idx.getNat expression.getNat round.getNat

def define_constraint_group_string
  (start: ℕ) (count: ℕ)
: String :=
  if count = 0 then
    "  True"
  else
    s!"  constraint_{start} c row ∧" ++
    s!"{define_constraint_group_string (start+1) (count-1)}"

def define_constraint_group
  (name: String) (start: ℕ) (count: ℕ)
: Lean.Elab.Command.CommandElabM Unit := do
  let def_string :=
    s!"def {name} {"{"}F ExtF C{"}"}" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]" ++
    s!"  (c : C F ExtF) (row: ℕ)" ++
    s!": Prop :=" ++
    s!"{define_constraint_group_string start count}"

  runAsCommand def_string

elab "#define_constraint_group" name:str start:num count:num : command => do
  define_constraint_group name.getString start.getNat count.getNat

def tag_simp_range
  (name: String) (start: ℕ) (count : ℕ) (step: ℕ) (tag: String)
: Lean.Elab.Command.CommandElabM Unit := do
  if count ≠ 0 then
    runAsCommand s!"attribute [local {tag}] {name}{start}"
    tag_simp_range name (start + step) (count - 1) step tag

elab "#tag_simp_range" name:str start:num count:num step:num tag:str : command => do
  tag_simp_range name.getString start.getNat count.getNat step.getNat tag.getString

def prove_eval_sbox_constraint
  (idx: ℕ) (constraint_idx: ℕ) (round: ℕ) (state: ℕ)
: Lean.Elab.Command.CommandElabM Unit := do
  let lemma_string :=
    s!"lemma constraint_equiv_{constraint_idx}"++
    s!"  {"{"}C : Type → Type → Type{"}"} {"{"}F ExtF : Type{"}"}"++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]"++
    s!"  (c : C F ExtF) (row: ℕ)"++
    s!":"++
    s!"  constraint_{constraint_idx} c row ="++
    s!"  eval_sbox_7_1"++
    s!"    ((beginning_full_rounds c row {round}).sbox {idx})"++
    s!"    (state{state} c row {idx})"++
    s!":= by simp [Poseidon2_expressions]"

  runAsCommand lemma_string true

def prove_eval_sbox_constraints
  (start_constraint: ℕ) (round: ℕ) (state: ℕ) (width: ℕ)
: Lean.Elab.Command.CommandElabM Unit := do
  if width ≠ 0 then
    prove_eval_sbox_constraint
      (width - 1)
      (start_constraint + width - 1)
      round
      state
    prove_eval_sbox_constraints start_constraint round state (width - 1)

elab "#prove_eval_sbox_constraints" start_constraint:num round:num state:num width:num : command => do
  prove_eval_sbox_constraints start_constraint.getNat round.getNat state.getNat width.getNat

def prove_full_round_post_constraint
  (idx: ℕ) (constraint_idx: ℕ) (round: ℕ) (state: ℕ)
: Lean.Elab.Command.CommandElabM Unit := do
  let lemma_string :=
    s!"lemma constraint_equiv_{constraint_idx}" ++
    s!"  {"{"}C : Type → Type → Type{"}"} {"{"}F ExtF : Type{"}"}" ++
    s!"  [Field F] [Field ExtF] [Circuit F ExtF C]" ++
    s!"  (c : C F ExtF) (row: ℕ)" ++
    s!":" ++
    s!"  constraint_{constraint_idx} c row =" ++
    s!"  (state{state} c row {idx} = (beginning_full_rounds c row {round}).post {idx})" ++
    s!":= by simp [Poseidon2_expressions]"

  runAsCommand lemma_string true

def prove_full_round_post_constraints
  (start_constraint: ℕ) (round: ℕ) (state: ℕ) (width: ℕ)
: Lean.Elab.Command.CommandElabM Unit := do
  if width ≠ 0 then
    prove_full_round_post_constraint
      (width - 1)
      (start_constraint + width - 1)
      round
      state
    prove_full_round_post_constraints start_constraint round state (width - 1)

elab "#prove_full_round_post_constraints" start_constraint:num round:num state:num width:num : command => do
  prove_full_round_post_constraints start_constraint.getNat round.getNat state.getNat width.getNat

def prove_partial_round
  (round : ℕ)
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

  runAsCommand state1
  runAsCommand state1'
  runAsCommand state1_equiv

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

  runAsCommand state2
  runAsCommand state2'
  runAsCommand state2_equiv

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

  runAsCommand constraint1_equiv

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

  runAsCommand state3
  runAsCommand state3'
  runAsCommand state3_equiv

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

  runAsCommand constraint2_equiv

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

  runAsCommand state4
  runAsCommand state4'
  runAsCommand state4_equiv

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

  runAsCommand state5
  runAsCommand state5'
  runAsCommand state5_equiv

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

  runAsCommand round_lemma

elab "#prove_partial_round" round:num : command => do
  prove_partial_round round.getNat
