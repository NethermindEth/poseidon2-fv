import Mathlib

def BabyBear_Prime := 2013265921

lemma babybear_prime' : (2013265921).Prime := by norm_num
lemma babybear_prime : BabyBear_Prime.Prime := babybear_prime'

instance : Fact (2013265921).Prime := {
  out := babybear_prime'
}

instance : Fact BabyBear_Prime.Prime := {
  out := babybear_prime
}

lemma babybear_halve' (x: ZMod 2013265921) :
  x * 1006632961 = x / 2
:= by grind

lemma babybear_halve (x: ZMod BabyBear_Prime) :
  x * 1006632961 = x / 2
:= by convert babybear_halve' x

lemma babybear_div_pow_2' (x: ZMod 2013265921) :
  x * 1509949441 = x / 2 ^ 2
:= by grind

lemma babybear_div_pow_2 (x: ZMod BabyBear_Prime) :
  x * 1509949441 = x / 2 ^ 2
:= by convert babybear_div_pow_2' x

lemma babybear_div_pow_3' (x: ZMod 2013265921) :
  x * 1761607681 = x / 2 ^ 3
:= by grind

lemma babybear_div_pow_3 (x: ZMod BabyBear_Prime) :
  x * 1761607681 = x / 2 ^ 3
:= by convert babybear_div_pow_3' x

lemma babybear_div_pow_4' (x: ZMod 2013265921) :
  x * 1887436801 = x / 2 ^ 4
:= by grind

lemma babybear_div_pow_4 (x: ZMod BabyBear_Prime) :
  x * 1887436801 = x / 2 ^ 4
:= by convert babybear_div_pow_4' x

lemma babybear_div_pow_5' (x: ZMod 2013265921) :
  x * 1950351361 = x / 2 ^ 5
:= by grind

lemma babybear_div_pow_5 (x: ZMod BabyBear_Prime) :
  x * 1950351361 = x / 2 ^ 5
:= by convert babybear_div_pow_5' x

lemma babybear_div_pow_6' (x: ZMod 2013265921) :
  x * 1981808641 = x / 2 ^ 6
:= by grind

lemma babybear_div_pow_6 (x: ZMod BabyBear_Prime) :
  x * 1981808641 = x / 2 ^ 6
:= by convert babybear_div_pow_6' x

lemma babybear_div_pow_7' (x: ZMod 2013265921) :
  x * 1997537281 = x / 2 ^ 7
:= by grind

lemma babybear_div_pow_7 (x: ZMod BabyBear_Prime) :
  x * 1997537281 = x / 2 ^ 7
:= by convert babybear_div_pow_7' x

lemma babybear_div_pow_8' (x: ZMod 2013265921) :
  x * 2005401601 = x / 2 ^ 8
:= by grind

lemma babybear_div_pow_8 (x: ZMod BabyBear_Prime) :
  x * 2005401601 = x / 2 ^ 8
:= by convert babybear_div_pow_8' x

lemma babybear_div_pow_9' (x: ZMod 2013265921) :
  x * 2009333761 = x / 2 ^ 9
:= by grind

lemma babybear_div_pow_9 (x: ZMod BabyBear_Prime) :
  x * 2009333761 = x / 2 ^ 9
:= by convert babybear_div_pow_9' x

lemma babybear_div_pow_27' (x: ZMod 2013265921) :
  x * 2013265906 = x / 2 ^ 27
:= by grind

lemma babybear_div_pow_27 (x: ZMod BabyBear_Prime) :
  x * 2013265906 = x / 2 ^ 27
:= by convert babybear_div_pow_27' x
