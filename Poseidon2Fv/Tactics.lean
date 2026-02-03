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
