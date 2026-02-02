import LeanZKCircuit_Plonky3.Plonky3.Command.util
import Poseidon2Fv.Extraction.Full

open Plonky3 Poseidon2.extraction

namespace Poseidon2.Folding

def eval_sbox_7_1 [Field F] (x3 x : F) : Prop :=
  x3 - (x * x) * x = 0

def apply_full_round_sbox [Field F] (state: Fin 16 → F) : Fin 16 → F :=
  λ x => state x ^ 7

def apply_m4 [Field F] (state: Fin 16 → F) (idx: Fin 16) : Fin 4 → F :=
  λ x =>
  let x0 := state idx
  let x1 := state (idx + 1)
  let x2 := state (idx + 2)
  let x3 := state (idx + 3)
  let x01 := x0 + x1
  let x23 := x2 + x3
  let x0123 := x01 + x23
  let x01123 := x0123 + x1
  let x01233 := x0123 + x3
  match x with
    | 0 => x01123 + x01
    | 1 => x01123 + (state (idx + 2) + state (idx + 2))
    | 2 => x01233 + x23
    | 3 => x01233 + (state idx + state idx)
    | _ => 0

def apply_m4_loop [Field F] (state : Fin 16 → F) : Fin 16 → F
  | 0 => apply_m4 state 0 0
  | 1 => apply_m4 state 0 1
  | 2 => apply_m4 state 0 2
  | 3 => apply_m4 state 0 3
  | 4 => apply_m4 state 4 0
  | 5 => apply_m4 state 4 1
  | 6 => apply_m4 state 4 2
  | 7 => apply_m4 state 4 3
  | 8 => apply_m4 state 8 0
  | 9 => apply_m4 state 8 1
  | 10 => apply_m4 state 8 2
  | 11 => apply_m4 state 8 3
  | 12 => apply_m4 state 12 0
  | 13 => apply_m4 state 12 1
  | 14 => apply_m4 state 12 2
  | 15 => apply_m4 state 12 3
  | _ => 0

def apply_m4_sums [Field F] (state : Fin 16 → F) : Fin 4 → F
  | 0 => (apply_m4_loop state 0) + (apply_m4_loop state 4) + (apply_m4_loop state 8) + (apply_m4_loop state 12)
  | 1 => (apply_m4_loop state 1) + (apply_m4_loop state 5) + (apply_m4_loop state 9) + (apply_m4_loop state 13)
  | 2 => (apply_m4_loop state 2) + (apply_m4_loop state 6) + (apply_m4_loop state 10) + (apply_m4_loop state 14)
  | 3 => (apply_m4_loop state 3) + (apply_m4_loop state 7) + (apply_m4_loop state 11) + (apply_m4_loop state 15)

def mds_light_permutation [Field F] (state : Fin 16 → F) : Fin 16 → F
  | 0 => apply_m4_loop state 0 + apply_m4_sums state 0
  | 1 => apply_m4_loop state 1 + apply_m4_sums state 1
  | 2 => apply_m4_loop state 2 + apply_m4_sums state 2
  | 3 => apply_m4_loop state 3 + apply_m4_sums state 3
  | 4 => apply_m4_loop state 4 + apply_m4_sums state 0
  | 5 => apply_m4_loop state 5 + apply_m4_sums state 1
  | 6 => apply_m4_loop state 6 + apply_m4_sums state 2
  | 7 => apply_m4_loop state 7 + apply_m4_sums state 3
  | 8 => apply_m4_loop state 8 + apply_m4_sums state 0
  | 9 => apply_m4_loop state 9 + apply_m4_sums state 1
  | 10 =>apply_m4_loop state 10 + apply_m4_sums state 2
  | 11 =>apply_m4_loop state 11 + apply_m4_sums state 3
  | 12 =>apply_m4_loop state 12 + apply_m4_sums state 0
  | 13 =>apply_m4_loop state 13 + apply_m4_sums state 1
  | 14 =>apply_m4_loop state 14 + apply_m4_sums state 2
  | 15 =>apply_m4_loop state 15 + apply_m4_sums state 3
  | _ => 0

-- WIDTH → F
def round_constants [Field F] : Fin 4 → Fin 16 → F :=
  λ x y => match x, y with
    | 0, 0 => 0x69cbb6af
    | 0, 1 => 0x46ad93f9
    | 0, 2 => 0x60a00f4e
    | 0, 3 => 0x6b1297cd
    | 0, 4 => 0x23189afe
    | 0, 5 => 0x732e7bef
    | 0, 6 => 0x72c246de
    | 0, 7 => 0x2c941900
    | 0, 8 => 0x0557eede
    | 0, 9 => 0x1580496f
    | 0, 10 => 0x3a3ea77b
    | 0, 11 => 0x54f3f271
    | 0, 12 => 0x0f49b029
    | 0, 13 => 0x47872fe1
    | 0, 14 => 0x221e2e36
    | 0, 15 => 0x1ab7202e
    | 1, 0 => 0x487779a6
    | 1, 1 => 0x3851c9d8
    | 1, 2 => 0x38dc17c0
    | 1, 3 => 0x209f8849
    | 1, 4 => 0x268dcee8
    | 1, 5 => 0x350c48da
    | 1, 6 => 0x5b9ad32e
    | 1, 7 => 0x0523272b
    | 1, 8 => 0x3f89055b
    | 1, 9 => 0x01e894b2
    | 1, 10 => 0x13ddedde
    | 1, 11 => 0x1b2ef334
    | 1, 12 => 0x7507d8b4
    | 1, 13 => 0x6ceeb94e
    | 1, 14 => 0x52eb6ba2
    | 1, 15 => 0x50642905
    | 2, 0 => 0x05453f3f
    | 2, 1 => 0x06349efc
    | 2, 2 => 0x6922787c
    | 2, 3 => 0x04bfff9c
    | 2, 4 => 0x768c714a
    | 2, 5 => 0x3e9ff21a
    | 2, 6 => 0x15737c9c
    | 2, 7 => 0x2229c807
    | 2, 8 => 0x0d47f88c
    | 2, 9 => 0x097e0ecc
    | 2, 10 => 0x27eadba0
    | 2, 11 => 0x2d7d29e4
    | 2, 12 => 0x3502aaa0
    | 2, 13 => 0x0f475fd7
    | 2, 14 => 0x29fbda49
    | 2, 15 => 0x018afffd
    | 3, 0 => 0x0315b618
    | 3, 1 => 0x6d4497d1
    | 3, 2 => 0x1b171d9e
    | 3, 3 => 0x52861abd
    | 3, 4 => 0x2e5d0501
    | 3, 5 => 0x3ec8646c
    | 3, 6 => 0x6e5f250a
    | 3, 7 => 0x148ae8e6
    | 3, 8 => 0x17f5fa4a
    | 3, 9 => 0x3e66d284
    | 3, 10 => 0x0051aa3b
    | 3, 11 => 0x483f7913
    | 3, 12 => 0x2cfe5f15
    | 3, 13 => 0x023427ca
    | 3, 14 => 0x2cc78315
    | 3, 15 => 0x1e36ea47
    | _, _ => 0

def add_round_constants [Field F] (state: Fin 16 → F) (round : Fin 4) : Fin 16 → F :=
  λ x => state x + round_constants round x

def define_opaque_state
  (idx: ℕ) (expression : ℕ) (step: ℕ)
: Lean.Elab.Command.CommandElabM Unit := do
  let def_string :=
    s!"def state{idx}" ++
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

def tag_simp_range
  (name: String) (start: ℕ) (count : ℕ) (step: ℕ)
: Lean.Elab.Command.CommandElabM Unit := do
  if count ≠ 0 then
    runAsCommand s!"attribute [local Poseidon2_expressions] {name}{start}"
    tag_simp_range name (start + step) (count - 1) step

elab "#tag_simp_range" name:str start:num count:num step:num : command => do
  tag_simp_range name.getString start.getNat count.getNat step.getNat

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

structure FullRound (F: Type) where
  sbox : Fin 16 → F -- WIDTH sboxes, each of which is 1 register
  post : Fin 16 → F

def inputs
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (1 + x.val) row 0)

-- HALF FULL ROUNDS →
def beginning_full_rounds
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 4 → FullRound F :=
  λ round => {
    sbox := λ x => (Circuit.main c (17 + 32*round.val + x.val) row 0)
    post := λ x => (Circuit.main c (33 + 32*round.val + x.val) row 0)
  }

-- Start state
#define_opaque_state 0 4 1

def state0'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  inputs c row

lemma state0_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  state0 c row = state0' c row
:= by
  unfold state0 state0' inputs
  funext x
  fin_cases x <;> rfl

-- After first external linear layer
#define_opaque_state 1 657 1

def state1'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  mds_light_permutation (state0 c row)

section external_linear_layer_zero
  #tag_simp_range "e" 601 72 1

  lemma state1_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state1 c row = state1' c row
  := by
    unfold state1 state1' mds_light_permutation
    funext x
    fin_cases x
    all_goals (
      simp [
        Poseidon2_expressions,
        state0, apply_m4_sums, apply_m4_loop, apply_m4
      ]
    )
end external_linear_layer_zero

#define_opaque_state 2 673 6

-- After adding round constants
def state2'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state1 c row x + round_constants 0 x

lemma state2_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  state2 c row = state2' c row
:= by
  unfold state2 state2'
  funext x
  fin_cases x <;> rfl

#define_opaque_state 3 675 6

-- sbox internal state
def state3'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state2 c row x ^ 3

section sbox_zero_internal

  #tag_simp_range "e" 674 16 6
  #tag_simp_range "e" 675 16 6

  lemma state3_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state3 c row = state3' c row
  := by
    unfold state3 state3' state2
    funext x
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        pow_three'
      ]
    )

end sbox_zero_internal

-- saved sbox internal state
#define_opaque_state 4 20 1

def state4'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state3 c row x

section sbox_state_zero
  #tag_simp_range "constraint_" 0 16 1
  #tag_simp_range "e" 20 16 1
  #tag_simp_range "e" 673 94 1
  attribute [local simp]
    eval_sbox_7_1
    round_constants
    beginning_full_rounds
    state1
    state2

  #prove_eval_sbox_constraints 0 0 2 16
end sbox_state_zero


-- sbox result
#define_opaque_state 5 678 6

def state5'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state2 c row x ^ 7

section sbox_zero_external

  #tag_simp_range "constraint_equiv_" 0 16 1
  #tag_simp_range "e" 20 16 1
  #tag_simp_range "e" 677 16 6
  #tag_simp_range "e" 678 16 6

  lemma state5_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h0: constraint_0 c row)
    (h1: constraint_1 c row)
    (h2: constraint_2 c row)
    (h3: constraint_3 c row)
    (h4: constraint_4 c row)
    (h5: constraint_5 c row)
    (h6: constraint_6 c row)
    (h7: constraint_7 c row)
    (h8: constraint_8 c row)
    (h9: constraint_9 c row)
    (h10: constraint_10 c row)
    (h11: constraint_11 c row)
    (h12: constraint_12 c row)
    (h13: constraint_13 c row)
    (h14: constraint_14 c row)
    (h15: constraint_15 c row)
  :
    state5 c row = state5' c row
  := by
    unfold state5 state5' state2
    funext x
    have (x: F) : x * x * x * (x * x * x) * x = x^7 := by grind
    simp [
      Poseidon2_expressions,
      eval_sbox_7_1,
      beginning_full_rounds,
      state2,
      sub_eq_zero
    ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        this
      ]
    )

end sbox_zero_external

-- After external linear layer
#define_opaque_state 6 825 1

def state6'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  mds_light_permutation (state5 c row)

section external_linear_layer_one
  #tag_simp_range "e" 769 72 1

  lemma state6_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state6 c row = state6' c row
  := by
    unfold state6 state6' mds_light_permutation
    funext x
    fin_cases x
    all_goals (
      simp [
        Poseidon2_expressions,
        state5, apply_m4_sums, apply_m4_loop, apply_m4
      ]
    )
end external_linear_layer_one

-- Round 0 post
#define_opaque_state 7 825 1

def state7'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (33 + x.val) row 0)

section full_round_0_post

  #tag_simp_range "constraint_" 16 16 1
  #tag_simp_range "e" 36 16 1
  #tag_simp_range "e" 841 16 1
  attribute [local simp]
    eval_sbox_7_1
    beginning_full_rounds
    state7
    sub_eq_zero

  #prove_full_round_post_constraints 16 0 7 16

  lemma state7_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h16: constraint_16 c row)
    (h17: constraint_17 c row)
    (h18: constraint_18 c row)
    (h19: constraint_19 c row)
    (h20: constraint_20 c row)
    (h21: constraint_21 c row)
    (h22: constraint_22 c row)
    (h23: constraint_23 c row)
    (h24: constraint_24 c row)
    (h25: constraint_25 c row)
    (h26: constraint_26 c row)
    (h27: constraint_27 c row)
    (h28: constraint_28 c row)
    (h29: constraint_29 c row)
    (h30: constraint_30 c row)
    (h31: constraint_31 c row)
  :
    state7 c row = state7' c row
  := by
    unfold state7 state7'
    funext x
    simp [
      Poseidon2_expressions,
      sub_eq_zero
    ] at h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31
      ]
    )
end full_round_0_post

lemma full_round_0
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h0: constraint_0 c row)
  (h1: constraint_1 c row)
  (h2: constraint_2 c row)
  (h3: constraint_3 c row)
  (h4: constraint_4 c row)
  (h5: constraint_5 c row)
  (h6: constraint_6 c row)
  (h7: constraint_7 c row)
  (h8: constraint_8 c row)
  (h9: constraint_9 c row)
  (h10: constraint_10 c row)
  (h11: constraint_11 c row)
  (h12: constraint_12 c row)
  (h13: constraint_13 c row)
  (h14: constraint_14 c row)
  (h15: constraint_15 c row)
  (h16: constraint_16 c row)
  (h17: constraint_17 c row)
  (h18: constraint_18 c row)
  (h19: constraint_19 c row)
  (h20: constraint_20 c row)
  (h21: constraint_21 c row)
  (h22: constraint_22 c row)
  (h23: constraint_23 c row)
  (h24: constraint_24 c row)
  (h25: constraint_25 c row)
  (h26: constraint_26 c row)
  (h27: constraint_27 c row)
  (h28: constraint_28 c row)
  (h29: constraint_29 c row)
  (h30: constraint_30 c row)
  (h31: constraint_31 c row)
:
  (beginning_full_rounds c row 0).post =
  mds_light_permutation (
    apply_full_round_sbox (
      add_round_constants (
        mds_light_permutation (
          inputs c row
        )
      ) 0
    )
  )
:= by
  have := state0_equiv c row
  unfold state0' at this
  rewrite [←this]; clear this

  have := state1_equiv c row
  unfold state1' at this
  rewrite [←this]; clear this

  have := state2_equiv c row
  unfold state2' at this
  unfold add_round_constants
  rewrite [←this]; clear this

  have := state5_equiv c row
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  unfold state5' at this
  unfold apply_full_round_sbox
  rewrite [←this]; clear this

  have := state6_equiv c row
  unfold state6' at this
  rewrite [←this]; clear this

  have := state7_equiv c row
    h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  unfold state7' at this
  unfold beginning_full_rounds
  simp
  rewrite [←this]; clear this

  rfl


-- After adding round constants
def state6
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state5 c row x + round_constants 1 x

-- After sbox
def state7
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state6 c row x ^ 7

-- After external linear layer
#define_opaque_state 8 1009

-- Round 1 post
def state9
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (65 + x.val) row 0)

-- After adding round constants
def state10
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state9 c row x + round_constants 2 x

-- After sbox
def state11
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state10 c row x ^ 7

-- After external linear layer
#define_opaque_state 12 1193

-- Round 1 post
def state13
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (97 + x.val) row 0)

-- After adding round constants
def state14
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state13 c row x + round_constants 3 x

-- After sbox
def state15
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state14 c row x ^ 7

-- After external linear layer
#define_opaque_state 16 1377


-- section Full_round_1_sbox

--   #tag_simp_range "constraint_" 32 16 1
--   #tag_simp_range "e" 36 16 1
--   #tag_simp_range "e" 52 16 1
--   #tag_simp_range "e" 857 16 6
--   #tag_simp_range "e" 858 16 6
--   #tag_simp_range "e" 859 16 6
--   #tag_simp_range "e" 860 16 6
--   attribute [local simp]
--     eval_sbox_7_1
--     round_constants
--     beginning_full_rounds
--     state5
--     state6

--   #prove_eval_sbox_constraints 32 1 6 16
-- end Full_round_1_sbox

-- section Full_round_2_sbox

--   #tag_simp_range "constraint_" 64 16 1
--   #tag_simp_range "e" 68 16 1
--   #tag_simp_range "e" 84 16 1
--   #tag_simp_range "e" 1041 16 6
--   #tag_simp_range "e" 1042 16 6
--   #tag_simp_range "e" 1043 16 6
--   #tag_simp_range "e" 1044 16 6
--   attribute [local simp]
--     eval_sbox_7_1
--     round_constants
--     beginning_full_rounds
--     state9
--     state10

--   #prove_eval_sbox_constraints 64 2 10 16
-- end Full_round_2_sbox

-- section Full_round_3_sbox

--   #tag_simp_range "constraint_" 96 16 1
--   #tag_simp_range "e" 100 16 1
--   #tag_simp_range "e" 116 16 1
--   #tag_simp_range "e" 1225 16 6
--   #tag_simp_range "e" 1226 16 6
--   #tag_simp_range "e" 1227 16 6
--   #tag_simp_range "e" 1228 16 6
--   attribute [local simp]
--     eval_sbox_7_1
--     round_constants
--     beginning_full_rounds
--     state13
--     state14

--   #prove_eval_sbox_constraints 96 3 14 16
-- end Full_round_3_sbox


-- section Full_round_1_post

--   #tag_simp_range "constraint_" 48 16 1
--   #tag_simp_range "e" 68 16 1
--   #tag_simp_range "e" 1025 16 1
--   attribute [local simp]
--     eval_sbox_7_1
--     beginning_full_rounds
--     state8
--     sub_eq_zero

--   #prove_full_round_post_constraints 48 1 8 16
-- end Full_round_1_post

-- section Full_round_2_post

--   #tag_simp_range "constraint_" 80 16 1
--   #tag_simp_range "e" 100 16 1
--   #tag_simp_range "e" 1209 16 1
--   attribute [local simp]
--     eval_sbox_7_1
--     beginning_full_rounds
--     state12
--     sub_eq_zero

--   #prove_full_round_post_constraints 80 2 12 16
-- end Full_round_2_post

-- section Full_round_3_post

--   #tag_simp_range "constraint_" 112 16 1
--   #tag_simp_range "e" 132 16 1
--   #tag_simp_range "e" 1393 16 1
--   attribute [local simp]
--     eval_sbox_7_1
--     beginning_full_rounds
--     state16
--     sub_eq_zero

--   #prove_full_round_post_constraints 112 3 16 16
-- end Full_round_3_post

end Poseidon2.Folding
