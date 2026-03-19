import Poseidon2Fv.Width24SBoxDeg11.BeginningFullRounds

open Plonky3
open Poseidon2W24S11.BeginningFullRounds
open Poseidon2W24S11.Extraction
open Poseidon2W24S11.Folding
open Poseidon2W24S11.Tactics

namespace Poseidon2W24S11.PartialRounds

def state26
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 24 → F :=
  λ x => match x with
    | 0 => e2745 c row
    | x => state25 c row x

def state26'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 24 → F :=
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
      e2745, state25', e292
    ]
  all_goals {
    simp [
      add_partial_round_constant
    ]
  }

def state27
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 24 → F :=
  λ x => match x with
    | 0 => e2747 c row
    | x => state26 c row x

def state27'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 24 → F
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
      e2747, e2746, state26,
      pow_three'
    ]
  all_goals rfl

lemma constraint_equiv_288
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  constraint_288 c row =
  eval_sbox_11_2_r1
    ((partial_rounds c row 0).sbox_r1)
    (state26 c row 0)
:= rfl

def state28
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 24 → F :=
  λ x => match x with
    | 0 => e2750 c row
    | x => state26 c row x

def state28'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 24 → F
  | 0 => (state26 c row 0) ^ 9
  | x => state26 c row x

lemma state28_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h : constraint_288 c row)
:
  state28 c row = state28' c row
:= by
  unfold state28 state28'
  funext x
  fin_cases x
  . simp [
      constraint_equiv_288 c row,
      eval_sbox_11_2_r1,
      partial_rounds, state26,
      sub_eq_zero
    ] at h
    simp [
      e2750, e2749,
      e316,
      state26,
      h
    ]
    ring
  all_goals rfl

lemma constraint_equiv_289
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  constraint_289 c row =
  eval_sbox_11_2_r2
    ((partial_rounds c row 0).sbox_r2)
    ((partial_rounds c row 0).sbox_r1)
:= rfl

def state29
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 24 → F :=
  λ x => match x with
    | 0 => e2752 c row
    | x => state26 c row x

def state29'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 24 → F
  | 0 => (state26 c row 0) ^ 11
  | x => state26 c row x

lemma state29_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h1 : constraint_288 c row)
  (h2 : constraint_289 c row)
:
  state29 c row = state29' c row
:= by
  unfold state29 state29'
  funext x
  fin_cases x
  . simp [
      constraint_equiv_288 c row,
      eval_sbox_11_2_r1,
      partial_rounds,
      sub_eq_zero
    ] at h1
    simp [
      constraint_equiv_289 c row,
      eval_sbox_11_2_r2,
      partial_rounds,
      sub_eq_zero
    ] at h2
    simp [
      state26,
      e2752,
      e2746,
      e317,
      h1, h2
    ]
    ring
  all_goals rfl

lemma constraint_equiv_290
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  constraint_290 c row =
  (state29 c row 0 = (partial_rounds c row 0).post_sbox)
:= by
  simp [
    constraint_290,
    e2753,
    sub_eq_zero,
    state29,
    partial_rounds,
    e318
  ]

def state30
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 24 → F :=
  λ x => match x with
    | 0 => e318 c row
    | x => state29 c row x

def state30'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 24 → F :=
  state29 c row

lemma state30_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h : constraint_290 c row)
:
  state30 c row = state30' c row
:= by
  unfold state30 state30'
  funext x
  fin_cases x
  . simp [
      constraint_equiv_290,
      partial_rounds
    ] at h
    simp [e318, h]
  all_goals rfl

#define_internal_matrix_state 31 2827 0

def state31'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
: Fin 24 → F :=
  generic_internal_linear_layer (state30 c row)

lemma state31_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row : ℕ)
  (h: beginning_full_round_3_post_constraints c row)
  (h_halve : ∀ x: F, x * 1006632961 = x / 2)
  (h_div_pow_2 : ∀ x: F, x * 1509949441 = x / 2 ^ 2)
  (h_div_pow_3 : ∀ x: F, x * 1761607681 = x / 2 ^ 3)
  (h_div_pow_4 : ∀ x: F, x * 1887436801 = x / 2 ^ 4)
  (h_div_pow_5 : ∀ x: F, x * 1950351361 = x / 2 ^ 5)
  (h_div_pow_6 : ∀ x: F, x * 1981808641 = x / 2 ^ 6)
  (h_div_pow_7 : ∀ x: F, x * 1997537281 = x / 2 ^ 7)
  (h_div_pow_8 : ∀ x: F, x * 2005401601 = x / 2 ^ 8)
  (h_div_pow_9 : ∀ x: F, x * 2009333761 = x / 2 ^ 9)
  (h_div_pow_27 : ∀ x: F, x * 2013265906 = x / 2 ^ 27)
:
  state31 c row = state31' c row
:= by
  unfold state31 state31'
  funext x
  fin_cases x
  all_goals simp [
    generic_internal_linear_layer,
    state30, state29, state26, state25_equiv c row h, state25',
    internal_layer_mat_mul,
    ←h_halve,
    ←h_div_pow_2,
    ←h_div_pow_3,
    ←h_div_pow_4,
    ←h_div_pow_5,
    ←h_div_pow_6,
    ←h_div_pow_7,
    ←h_div_pow_8,
    ←h_div_pow_9,
    ←h_div_pow_27,
  ]
  all_goals rfl

lemma partial_round_0
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h288: constraint_288 c row)
  (h289: constraint_289 c row)
  (h290: constraint_290 c row)
  (h_round_3: beginning_full_round_3_constraints c row)
  (h_halve : ∀ x: F, x * 1006632961 = x / 2)
  (h_div_pow_2 : ∀ x: F, x * 1509949441 = x / 2 ^ 2)
  (h_div_pow_3 : ∀ x: F, x * 1761607681 = x / 2 ^ 3)
  (h_div_pow_4 : ∀ x: F, x * 1887436801 = x / 2 ^ 4)
  (h_div_pow_5 : ∀ x: F, x * 1950351361 = x / 2 ^ 5)
  (h_div_pow_6 : ∀ x: F, x * 1981808641 = x / 2 ^ 6)
  (h_div_pow_7 : ∀ x: F, x * 1997537281 = x / 2 ^ 7)
  (h_div_pow_8 : ∀ x: F, x * 2005401601 = x / 2 ^ 8)
  (h_div_pow_9 : ∀ x: F, x * 2009333761 = x / 2 ^ 9)
  (h_div_pow_27 : ∀ x: F, x * 2013265906 = x / 2 ^ 27)
:
  state31 c row =
  partial_round (
    (beginning_full_rounds c row 3).post
  ) 0
:= by

  have ⟨h_sbox3, h_post3⟩ := h_round_3
  rewrite [
    state31_equiv c row h_post3 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27
  ]
  unfold state31' partial_round

  rewrite [state30_equiv c row h290]
  unfold state30'

  rewrite [state29_equiv c row h288 h289]
  unfold state29'

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
#prove_partial_round 13
#prove_partial_round 14
#prove_partial_round 15
#prove_partial_round 16
#prove_partial_round 17
#prove_partial_round 18
#prove_partial_round 19
#prove_partial_round 20

end Poseidon2W24S11.PartialRounds
