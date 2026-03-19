import Poseidon2Fv.Width16SBoxDeg7.BeginningFullRounds

open Plonky3
open Poseidon2W16S7.Extraction
open Poseidon2W16S7.Folding
open Poseidon2W16S7.Tactics

def state26
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 16 → F :=
  λ x => match x with
    | 0 => e1409 c row
    | x => state25 c row x

def state26'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 16 → F :=
  add_partial_round_constant (state25 c row) 0

lemma state26_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h : beginning_full_round_3_post_constraints c row)
:
  state26 c row = state26' c row
:= by
  unfold state26 state26'
  funext x
  fin_cases x
  . rewrite [state25_equiv c row h]
    simp [
      add_partial_round_constant, partial_round_constants,
      e1409, state25', e132
    ]
  all_goals {
    simp [
      add_partial_round_constant
    ]
  }

def state27
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 16 → F :=
  λ x => match x with
    | 0 => e1411 c row
    | x => state26 c row x

def state27'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 16 → F
  | 0 => (state26 c row 0) ^ 3
  | x => state26 c row x

lemma state27_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  state27 c row = state27' c row
:= by
  unfold state27 state27'
  funext x
  fin_cases x
  . simp [
      e1411, e1410, state26,
      pow_three'
    ]
  all_goals simp

lemma constraint_equiv_128
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  constraint_128 c row =
  eval_sbox_7_1
    ((partial_rounds c row 0).sbox)
    (state26 c row 0)
:= by
  simp [
    constraint_128,
    eval_sbox_7_1,
    partial_rounds,
    state26,
    sub_eq_zero,
    e1412,
    e148,
    e1411, e1410
  ]

def state28
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 16 → F :=
  λ x => match x with
    | 0 => e1414 c row
    | x => state26 c row x

def state28'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 16 → F
  | 0 => (state26 c row 0) ^ 7
  | x => state26 c row x

lemma state28_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h : constraint_128 c row)
:
  state28 c row = state28' c row
:= by
  unfold state28 state28'
  funext x
  fin_cases x
  . simp [
      constraint_equiv_128 c row,
      eval_sbox_7_1,
      partial_rounds, state26,
      sub_eq_zero
    ] at h
    simp [
      e1414, state26,
      e1413,
      e148,
      h
    ]
    grind
  all_goals simp

lemma constraint_equiv_129
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  constraint_129 c row =
  (state28 c row 0 = (partial_rounds c row 0).post_sbox)
:= by
  simp [
    constraint_129,
    e1415,
    sub_eq_zero,
    state28,
    partial_rounds,
    e149
  ]

def state29
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 16 → F :=
  λ x => match x with
    | 0 => e149 c row
    | x => state28 c row x

def state29'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 16 → F :=
  state28 c row

lemma state29_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h : constraint_129 c row)
:
  state29 c row = state29' c row
:= by
  unfold state29 state29'
  funext x
  fin_cases x
  . simp [
      constraint_equiv_129,
      partial_rounds
    ] at h
    simp [e149, h]
  all_goals simp

#define_internal_matrix_state 30 1465 0

def state30'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 16 → F :=
  generic_internal_linear_layer (state29 c row)

lemma state30_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
  (h: beginning_full_round_3_post_constraints c row)
  (h_halve : ∀ x: F, x * 1006632961 = x / 2)
  (h_div_pow_2 : ∀ x: F, x * 1509949441 = x / 2 ^ 2)
  (h_div_pow_3 : ∀ x: F, x * 1761607681 = x / 2 ^ 3)
  (h_div_pow_4 : ∀ x: F, x * 1887436801 = x / 2 ^ 4)
  (h_div_pow_8 : ∀ x: F, x * 2005401601 = x / 2 ^ 8)
  (h_div_pow_27 : ∀ x: F, x * 2013265906 = x / 2 ^ 27)
:
  state30 c row = state30' c row
:= by
  unfold state30 state30'
  funext x
  fin_cases x
  all_goals (
    simp [
      generic_internal_linear_layer,
      internal_layer_mat_mul,
      state29,
      state28,
      state26,
      state25_equiv c row h,
      state25',
      ←h_halve,
      ←h_div_pow_2,
      ←h_div_pow_3,
      ←h_div_pow_4,
      ←h_div_pow_8,
      ←h_div_pow_27,
    ]
  )
  . congr
  . congr
  . congr
  . congr
  . congr
  . congr
  . congr
  . congr
  . congr
  . congr
  . congr
  . congr
  . congr
  . congr
  . congr
  . congr

lemma partial_round_0
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h128: constraint_128 c row)
  (h129: constraint_129 c row)
  (h_round_3: beginning_full_round_3_constraints c row)
  (h_halve : ∀ x: F, x * 1006632961 = x / 2)
  (h_div_pow_2 : ∀ x: F, x * 1509949441 = x / 2 ^ 2)
  (h_div_pow_3 : ∀ x: F, x * 1761607681 = x / 2 ^ 3)
  (h_div_pow_4 : ∀ x: F, x * 1887436801 = x / 2 ^ 4)
  (h_div_pow_8 : ∀ x: F, x * 2005401601 = x / 2 ^ 8)
  (h_div_pow_27 : ∀ x: F, x * 2013265906 = x / 2 ^ 27)
:
  state30 c row =
  partial_round (
    (beginning_full_rounds c row 3).post
  ) 0
:= by

  have ⟨h_sbox3, h_post3⟩ := h_round_3
  rewrite [
    state30_equiv c row h_post3 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27
  ]
  unfold state30' partial_round

  rewrite [state29_equiv c row h129]
  unfold state29'

  rewrite [state28_equiv c row h128]
  unfold state28'

  rewrite [state26_equiv c row h_post3]
  unfold state26'

  rewrite [state25_equiv c row h_post3]
  rfl

#prove_partial_round 1
#prove_partial_round 2
#prove_partial_round 3
#prove_partial_round 4
#prove_partial_round 5
#prove_partial_round 6
#prove_partial_round 7
#prove_partial_round 8
#prove_partial_round 9
#prove_partial_round 10
#prove_partial_round 11
#prove_partial_round 12
