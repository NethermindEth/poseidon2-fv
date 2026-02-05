
import Poseidon2Fv.Folding
import Poseidon2Fv.FullRound1

open Plonky3
open Poseidon2.Extraction
open Poseidon2.Folding

-- After adding round constants
#define_opaque_state 14 1041 6

def state14'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state13 c row x + beginning_full_round_constants 2 x

lemma state14_equiv
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h: full_round_1_post_constraints c row)
:
  state14 c row = state14' c row
:= by
  unfold state14 state14'
  funext x
  rewrite [state13_equiv c row h]
  fin_cases x <;> rfl

-- sbox internal state
#define_opaque_state 15 1043 6

def state15'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state14 c row x ^ 3

section sbox_two_internal

  #tag_simp_range "e" 1042 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1043 16 6 "Poseidon2_expressions"

  lemma state15_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state15 c row = state15' c row
  := by
    unfold state15 state15' state14
    funext x
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        pow_three'
      ]
    )

end sbox_two_internal

-- saved sbox internal state
#define_opaque_state 16 84 1

def state16'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state16 c row x

section sbox_state_two
  #tag_simp_range "constraint_" 64 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 84 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 1042 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1043 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1044 16 6 "Poseidon2_expressions"
  attribute [local simp]
    eval_sbox_7_1
    beginning_full_round_constants
    beginning_full_rounds
    state14

  #prove_eval_sbox_constraints 64 2 14 16
end sbox_state_two

-- sbox result
#define_opaque_state 17 1046 6

def state17'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state14 c row x ^ 7

#define_constraint_group "full_round_2_sbox_constraints" 64 16

section sbox_two_external

  #tag_simp_range "constraint_equiv_" 64 16 1 "Poseidon2_constraints"
  #tag_simp_range "e" 84 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 1045 16 6 "Poseidon2_expressions"
  #tag_simp_range "e" 1046 16 6 "Poseidon2_expressions"

  lemma state17_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: full_round_2_sbox_constraints c row)
  :
    state17 c row = state17' c row
  := by
    unfold state17 state17' state14
    funext x
    have (x: F) : x * x * x * (x * x * x) * x = x^7 := by grind
    simp [
      full_round_2_sbox_constraints,
      Poseidon2_constraints,
      eval_sbox_7_1,
      beginning_full_rounds,
      state14,
      sub_eq_zero
    ] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        this
      ]
    )

end sbox_two_external

-- After external linear layer
#define_opaque_state 18 1193 1

def state18'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  mds_light_permutation (state17 c row)

section external_linear_layer_two

  lemma state18_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :
    state18 c row = state18' c row
  := by
    unfold state18 state18' mds_light_permutation
    funext x
    fin_cases x
    all_goals (
      simp [
        Poseidon2_expressions,
        state17, apply_m4_sums, apply_m4_loop, apply_m4
      ]
      congr
    )
end external_linear_layer_two

-- Round 2 post
#define_opaque_state 19 1193 1

def state19'
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (97 + x.val) row 0)

#define_constraint_group "full_round_2_post_constraints" 80 16

section full_round_2_post

  #tag_simp_range "constraint_" 80 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 100 16 1 "Poseidon2_expressions"
  #tag_simp_range "e" 1209 16 1 "Poseidon2_expressions"
  attribute [local simp]
    eval_sbox_7_1
    beginning_full_rounds
    state19
    sub_eq_zero

  #prove_full_round_post_constraints 80 2 19 16

  lemma state19_equiv
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
    (h: full_round_2_post_constraints c row)
  :
    state19 c row = state19' c row
  := by
    unfold state19 state19'
    funext x
    simp [
      full_round_2_post_constraints,
      Poseidon2_expressions,
      sub_eq_zero
    ] at h
    obtain ⟨h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := h
    fin_cases x <;> (
      simp [
        Poseidon2_expressions,
        h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31
      ]
    )
end full_round_2_post

def full_round_2_constraints
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Prop :=
  full_round_2_sbox_constraints c row ∧
  full_round_2_post_constraints c row

lemma full_round_2
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h1: full_round_1_constraints c row)
  (h2: full_round_2_constraints c row)
:
  (beginning_full_rounds c row 2).post =
  beginning_full_round (
    (beginning_full_rounds c row 1).post
  ) 2
:= by
  have ⟨h_sbox1, h_post1⟩ := h1
  have ⟨h_sbox2, h_post2⟩ := h2

  have := state13_equiv c row h_post1
  unfold state13' at this
  unfold beginning_full_rounds
  simp
  rewrite [←this]; clear this

  have := state14_equiv c row h_post1
  unfold state14' at this
  unfold beginning_full_round add_beginning_full_round_constants
  rewrite [←this]; clear this

  have := state17_equiv c row h_sbox2
  unfold state17' at this
  unfold apply_full_round_sbox
  rewrite [←this]; clear this

  have := state18_equiv c row
  unfold state18' at this
  rewrite [←this]; clear this

  have := state19_equiv c row h_post2
  unfold state19' at this
  rewrite [←this]; clear this

  rfl
