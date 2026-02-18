import Poseidon2Fv.PartialRounds

open Plonky3
open Poseidon2.Extraction
open Poseidon2.Folding

#define_opaque_state 91 2137 6

def state91' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state90 c row x + ending_full_round_constants 0 x

lemma state91_equiv {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  state91 c row = state91' c row
:= by
  unfold state91 state91'
  funext x
  fin_cases x
  all_goals congr

#define_opaque_state 92 2139 6

def state92' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state91 c row x ^ 3

lemma state92_equiv {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  state92 c row = state92' c row
:= by
  unfold state92 state92' state91
  funext x
  fin_cases x <;> (
    simp [pow_three']
    congr
  )

#define_opaque_state 93 174 1
def state93' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state92 c row x

#prove_eval_sbox_constraints 154 0 91 16 "ending"


#define_opaque_state 94 2142 6

def state94' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => state91 c row x ^ 7

#define_constraint_group "ending_full_round_0_sbox_constraints" 154 16

lemma state94_equiv {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h: ending_full_round_0_sbox_constraints c row)
:
  state94 c row = state94' c row
:= by
  unfold state94 state94' state91
  funext x
  have (x: F) : x * x * x * (x * x * x) * x = x^7 := by grind
  simp [
    ending_full_round_0_sbox_constraints,
    constraint_equiv_154,
    constraint_equiv_155,
    constraint_equiv_156,
    constraint_equiv_157,
    constraint_equiv_158,
    constraint_equiv_159,
    constraint_equiv_160,
    constraint_equiv_161,
    constraint_equiv_162,
    constraint_equiv_163,
    constraint_equiv_164,
    constraint_equiv_165,
    constraint_equiv_166,
    constraint_equiv_167,
    constraint_equiv_168,
    constraint_equiv_169,
    eval_sbox_7_1,
    ending_full_rounds,
    state91,
    sub_eq_zero
  ] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  fin_cases x <;> (
    simp [
      ←this,
      ←h0, ←h1, ←h2, ←h3, ←h4, ←h5, ←h6, ←h7, ←h8, ←h9, ←h10, ←h11, ←h12, ←h13, ←h14, ←h15
    ]
    rfl
  )

#define_opaque_state 95 2289 1

def state95' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  mds_light_permutation (state94 c row)

lemma state95_equiv {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  state95 c row = state95' c row
:= by
  unfold state95 state95' mds_light_permutation
  funext x
  fin_cases x
  all_goals (
    simp
    congr
  )

#define_opaque_state 96 2289 1
def state96' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 16 → F :=
  λ x => (Circuit.main c (187 + x.val) row 0)

#define_constraint_group "ending_full_round_0_post_constraints" 170 16
lemma state96_equiv {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h: ending_full_round_0_post_constraints c row)
:
  state96 c row = state96' c row
:= by
  unfold state96 state96'
  funext x
  simp [
    ending_full_round_0_post_constraints,
    constraint_170,
    constraint_171,
    constraint_172,
    constraint_173,
    constraint_174,
    constraint_175,
    constraint_176,
    constraint_177,
    constraint_178,
    constraint_179,
    constraint_180,
    constraint_181,
    constraint_182,
    constraint_183,
    constraint_184,
    constraint_185,
    e2305,
    e2306,
    e2307,
    e2308,
    e2309,
    e2310,
    e2311,
    e2312,
    e2313,
    e2314,
    e2315,
    e2316,
    e2317,
    e2318,
    e2319,
    e2320,
    sub_eq_zero
  ] at h
  simp [h]
  fin_cases x <;> rfl

def ending_full_round_0_constraints {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Prop :=
  ending_full_round_0_sbox_constraints c row ∧
  ending_full_round_0_post_constraints c row

lemma ending_full_round_0 {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h0: ending_full_round_0_constraints c row)
:
  (ending_full_rounds c row 0).post =
  ending_full_round (
    state90 c row
  ) 0
:= by
  simp [ending_full_round, ending_full_rounds]
  have :=state96_equiv c row h0.2
  unfold state96' at this
  rewrite [←this]; clear this

  have := state95_equiv c row
  unfold state95 at this
  unfold state96
  rewrite [this]; clear this

  unfold state95'
  rewrite [state94_equiv c row h0.1]

  unfold state94' apply_full_round_sbox
  rewrite [state91_equiv c row]

  unfold state91' add_ending_full_round_constants
  rfl

#prove_ending_full_round 1
#prove_ending_full_round 2
#prove_ending_full_round 3

-- This will need to be updated due to the change in the number of partial rounds
lemma poseidon_permutation
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h_halve : ∀ x: F, x * 1006632961 = x / 2)
  (h_div_pow_2 : ∀ x: F, x * 1509949441 = x / 2 ^ 2)
  (h_div_pow_3 : ∀ x: F, x * 1761607681 = x / 2 ^ 3)
  (h_div_pow_4 : ∀ x: F, x * 1887436801 = x / 2 ^ 4)
  (h_div_pow_8 : ∀ x: F, x * 2005401601 = x / 2 ^ 8)
  (h_div_pow_27 : ∀ x: F, x * 2013265906 = x / 2 ^ 27)
  (h_beginning_0: beginning_full_round_0_constraints c row)
  (h_beginning_1: beginning_full_round_1_constraints c row)
  (h_beginning_2: beginning_full_round_2_constraints c row)
  (h_beginning_3: beginning_full_round_3_constraints c row)
  (h_128: constraint_128 c row)
  (h_129: constraint_129 c row)
  (h_130: constraint_130 c row)
  (h_131: constraint_131 c row)
  (h_132: constraint_132 c row)
  (h_133: constraint_133 c row)
  (h_134: constraint_134 c row)
  (h_135: constraint_135 c row)
  (h_136: constraint_136 c row)
  (h_137: constraint_137 c row)
  (h_138: constraint_138 c row)
  (h_139: constraint_139 c row)
  (h_140: constraint_140 c row)
  (h_141: constraint_141 c row)
  (h_142: constraint_142 c row)
  (h_143: constraint_143 c row)
  (h_144: constraint_144 c row)
  (h_145: constraint_145 c row)
  (h_146: constraint_146 c row)
  (h_147: constraint_147 c row)
  (h_148: constraint_148 c row)
  (h_149: constraint_149 c row)
  (h_150: constraint_150 c row)
  (h_151: constraint_151 c row)
  (h_152: constraint_152 c row)
  (h_153: constraint_153 c row)
  (h_ending_0: ending_full_round_0_constraints c row)
  (h_ending_1: ending_full_round_1_constraints c row)
  (h_ending_2: ending_full_round_2_constraints c row)
  (h_ending_3: ending_full_round_3_constraints c row)
:
  (ending_full_rounds c row 3).post =
  permutation (inputs c row)
:= by
  unfold permutation
  rw [
    ←beginning_full_round_0 c row h_beginning_0,
    ←beginning_full_round_1 c row h_beginning_0 h_beginning_1,
    ←beginning_full_round_2 c row h_beginning_1 h_beginning_2,
    ←beginning_full_round_3 c row h_beginning_2 h_beginning_3,
    ←partial_round_0 c row h_128 h_129 h_beginning_3 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_1 c row h_130 h_131 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_2 c row h_132 h_133 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_3 c row h_134 h_135 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_4 c row h_136 h_137 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_5 c row h_138 h_139 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_6 c row h_140 h_141 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_7 c row h_142 h_143 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_8 c row h_144 h_145 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_9 c row h_146 h_147 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_10 c row h_148 h_149 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_11 c row h_150 h_151 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←partial_round_12 c row h_152 h_153 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_8 h_div_pow_27,
    ←ending_full_round_0 c row h_ending_0,
    ←ending_full_round_1 c row h_ending_0 h_ending_1,
    ←ending_full_round_2 c row h_ending_1 h_ending_2,
    ←ending_full_round_3 c row h_ending_2 h_ending_3,
  ]
