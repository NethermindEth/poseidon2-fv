import Poseidon2Fv.PartialRounds

open Plonky3
open Poseidon2.Extraction
open Poseidon2.Folding

#define_opaque_state 152 4467 8

def state152' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 24 → F :=
  λ x => state151 c row x + ending_full_round_constants 0 x

lemma state152_equiv {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  state152 c row = state152' c row
:= by
  unfold state152 state152'
  funext x
  fin_cases x
  all_goals rfl

#define_opaque_state 153 4469 8

def state153' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 24 → F :=
  λ x => state152 c row x ^ 3

lemma state153_equiv {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  state153 c row = state153' c row
:= by
  unfold state153 state153' state152
  funext x
  fin_cases x <;> (
    simp [pow_three']
    rfl
  )

#define_opaque_state 154 377 1
def state154' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 24 → F :=
  λ x => state153 c row x

#prove_eval_sbox_constraints 351 0 152 24 "ending"


#define_opaque_state 155 4474 8

def state155' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 24 → F :=
  λ x => state152 c row x ^ 11

#define_constraint_group "ending_full_round_0_sbox_constraints" 351 48

lemma state155_equiv {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h: ending_full_round_0_sbox_constraints c row)
:
  state155 c row = state155' c row
:= by
  unfold state155 state155' state152
  funext x
  have (x: F) : (x * x * x) * (x * x * x) * (x * x * x) * (x * x) = x^11 := by ring
  simp [
    ending_full_round_0_sbox_constraints,
    constraint_equiv_351,
    constraint_equiv_352,
    constraint_equiv_353,
    constraint_equiv_354,
    constraint_equiv_355,
    constraint_equiv_356,
    constraint_equiv_357,
    constraint_equiv_358,
    constraint_equiv_359,
    constraint_equiv_360,
    constraint_equiv_361,
    constraint_equiv_362,
    constraint_equiv_363,
    constraint_equiv_364,
    constraint_equiv_365,
    constraint_equiv_366,
    constraint_equiv_367,
    constraint_equiv_368,
    constraint_equiv_369,
    constraint_equiv_370,
    constraint_equiv_371,
    constraint_equiv_372,
    constraint_equiv_373,
    constraint_equiv_374,
    constraint_equiv_375,
    constraint_equiv_376,
    constraint_equiv_377,
    constraint_equiv_378,
    constraint_equiv_379,
    constraint_equiv_380,
    constraint_equiv_381,
    constraint_equiv_382,
    constraint_equiv_383,
    constraint_equiv_384,
    constraint_equiv_385,
    constraint_equiv_386,
    constraint_equiv_387,
    constraint_equiv_388,
    constraint_equiv_389,
    constraint_equiv_390,
    constraint_equiv_391,
    constraint_equiv_392,
    constraint_equiv_393,
    constraint_equiv_394,
    constraint_equiv_395,
    constraint_equiv_396,
    constraint_equiv_397,
    constraint_equiv_398,
    eval_sbox_11_2_r1,
    eval_sbox_11_2_r2,
    ending_full_rounds,
    state152,
    sub_eq_zero
  ] at h
  obtain ⟨
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31,
    h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47
  ⟩ := h
  fin_cases x <;> (
    simp [
      ←this,
      ←h0, ←h1, ←h2, ←h3, ←h4, ←h5, ←h6, ←h7, ←h8, ←h9, ←h10, ←h11, ←h12, ←h13, ←h14, ←h15,
      ←h16, ←h17, ←h18, ←h19, ←h20, ←h21, ←h22, ←h23, ←h24, ←h25, ←h26, ←h27, ←h28, ←h29, ←h30, ←h31,
      ←h32, ←h33, ←h34, ←h35, ←h36, ←h37, ←h38, ←h39, ←h40, ←h41, ←h42, ←h43, ←h44, ←h45, ←h46, ←h47
    ]
    rfl
  )

#define_opaque_state 156 4745 1

def state156' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 24 → F :=
  mds_light_permutation (state155 c row)

lemma state156_equiv {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
:
  state156 c row = state156' c row
:= by
  unfold state156 state156' mds_light_permutation
  funext x
  fin_cases x
  all_goals (
    simp
    rfl
  )

#define_opaque_state 157 4745 1
def state157' {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
: Fin 24 → F :=
  λ x => (Circuit.main c (1+24+4*3*24+21*3 + 48 + x.val) row 0)

#define_constraint_group "ending_full_round_0_post_constraints" 399 24
lemma state157_equiv {F ExtF C}
  [Field F] [Field ExtF] [Circuit F ExtF C]
  (c : C F ExtF) (row: ℕ)
  (h: ending_full_round_0_post_constraints c row)
:
  state157 c row = state157' c row
:= by
  unfold state157 state157'
  funext x
  simp [
    ending_full_round_0_post_constraints,
    constraint_399,
    constraint_400,
    constraint_401,
    constraint_402,
    constraint_403,
    constraint_404,
    constraint_405,
    constraint_406,
    constraint_407,
    constraint_408,
    constraint_409,
    constraint_410,
    constraint_411,
    constraint_412,
    constraint_413,
    constraint_414,
    constraint_415,
    constraint_416,
    constraint_417,
    constraint_418,
    constraint_419,
    constraint_420,
    constraint_421,
    constraint_422,
    e4769,
    e4770,
    e4771,
    e4772,
    e4773,
    e4774,
    e4775,
    e4776,
    e4777,
    e4778,
    e4779,
    e4780,
    e4781,
    e4782,
    e4783,
    e4784,
    e4785,
    e4786,
    e4787,
    e4788,
    e4789,
    e4790,
    e4791,
    e4792,
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
    state151 c row
  ) 0
:= by
  simp [ending_full_round, ending_full_rounds]
  have :=state157_equiv c row h0.2
  unfold state157' at this
  rewrite [←this]; clear this

  have := state156_equiv c row
  unfold state156 at this
  unfold state157
  rewrite [this]; clear this

  unfold state156'
  rewrite [state155_equiv c row h0.1]

  unfold state155' apply_full_round_sbox
  rewrite [state152_equiv c row]

  unfold state152' add_ending_full_round_constants
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
  (h_div_pow_5 : ∀ x: F, x * 1950351361 = x / 2 ^ 5)
  (h_div_pow_6 : ∀ x: F, x * 1981808641 = x / 2 ^ 6)
  (h_div_pow_7 : ∀ x: F, x * 1997537281 = x / 2 ^ 7)
  (h_div_pow_8 : ∀ x: F, x * 2005401601 = x / 2 ^ 8)
  (h_div_pow_9 : ∀ x: F, x * 2009333761 = x / 2 ^ 9)
  (h_div_pow_27 : ∀ x: F, x * 2013265906 = x / 2 ^ 27)
  (h_beginning_0: beginning_full_round_0_constraints c row)
  (h_beginning_1: beginning_full_round_1_constraints c row)
  (h_beginning_2: beginning_full_round_2_constraints c row)
  (h_beginning_3: beginning_full_round_3_constraints c row)
  (h_288: constraint_288 c row)
  (h_289: constraint_289 c row)
  (h_290: constraint_290 c row)
  (h_291: constraint_291 c row)
  (h_292: constraint_292 c row)
  (h_293: constraint_293 c row)
  (h_294: constraint_294 c row)
  (h_295: constraint_295 c row)
  (h_296: constraint_296 c row)
  (h_297: constraint_297 c row)
  (h_298: constraint_298 c row)
  (h_299: constraint_299 c row)
  (h_300: constraint_300 c row)
  (h_301: constraint_301 c row)
  (h_302: constraint_302 c row)
  (h_303: constraint_303 c row)
  (h_304: constraint_304 c row)
  (h_305: constraint_305 c row)
  (h_306: constraint_306 c row)
  (h_307: constraint_307 c row)
  (h_308: constraint_308 c row)
  (h_309: constraint_309 c row)
  (h_310: constraint_310 c row)
  (h_311: constraint_311 c row)
  (h_312: constraint_312 c row)
  (h_313: constraint_313 c row)
  (h_314: constraint_314 c row)
  (h_315: constraint_315 c row)
  (h_316: constraint_316 c row)
  (h_317: constraint_317 c row)
  (h_318: constraint_318 c row)
  (h_319: constraint_319 c row)
  (h_320: constraint_320 c row)
  (h_321: constraint_321 c row)
  (h_322: constraint_322 c row)
  (h_323: constraint_323 c row)
  (h_324: constraint_324 c row)
  (h_325: constraint_325 c row)
  (h_326: constraint_326 c row)
  (h_327: constraint_327 c row)
  (h_328: constraint_328 c row)
  (h_329: constraint_329 c row)
  (h_330: constraint_330 c row)
  (h_331: constraint_331 c row)
  (h_332: constraint_332 c row)
  (h_333: constraint_333 c row)
  (h_334: constraint_334 c row)
  (h_335: constraint_335 c row)
  (h_336: constraint_336 c row)
  (h_337: constraint_337 c row)
  (h_338: constraint_338 c row)
  (h_339: constraint_339 c row)
  (h_340: constraint_340 c row)
  (h_341: constraint_341 c row)
  (h_342: constraint_342 c row)
  (h_343: constraint_343 c row)
  (h_344: constraint_344 c row)
  (h_345: constraint_345 c row)
  (h_346: constraint_346 c row)
  (h_347: constraint_347 c row)
  (h_348: constraint_348 c row)
  (h_349: constraint_349 c row)
  (h_350: constraint_350 c row)
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
    ←partial_round_0 c row (by assumption) (by assumption) (by assumption) h_beginning_3 h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_1  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_2  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_3  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_4  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_5  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_6  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_7  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_8  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_9  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_10  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_11  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_12  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_13  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_14  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_15  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_16  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_17  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_18  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_19  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←partial_round_20  c row (by assumption) (by assumption) (by assumption) h_halve h_div_pow_2 h_div_pow_3 h_div_pow_4 h_div_pow_5 h_div_pow_6 h_div_pow_7 h_div_pow_8 h_div_pow_9 h_div_pow_27,
    ←ending_full_round_0 c row h_ending_0,
    ←ending_full_round_1 c row h_ending_0 h_ending_1,
    ←ending_full_round_2 c row h_ending_1 h_ending_2,
    ←ending_full_round_3 c row h_ending_2 h_ending_3,
  ]
