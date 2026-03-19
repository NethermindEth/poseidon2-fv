import Mathlib

def BabyBear_Prime := 2013265921

lemma babybear_halve' [Fact (2013265921).Prime] (x: ZMod 2013265921) :
  x * 1006632961 = x / 2
:= by grind

lemma babybear_halve [Fact BabyBear_Prime.Prime] (x: ZMod BabyBear_Prime) :
  x * 1006632961 = x / 2
:= by convert babybear_halve' x

lemma babybear_div_pow_2' [Fact (2013265921).Prime] (x: ZMod 2013265921) :
  x * 1509949441 = x / 2 ^ 2
:= by grind

lemma babybear_div_pow_2 [Fact BabyBear_Prime.Prime] (x: ZMod BabyBear_Prime) :
  x * 1509949441 = x / 2 ^ 2
:= by convert babybear_div_pow_2' x

lemma babybear_div_pow_3' [Fact (2013265921).Prime] (x: ZMod 2013265921) :
  x * 1761607681 = x / 2 ^ 3
:= by grind

lemma babybear_div_pow_3 [Fact BabyBear_Prime.Prime] (x: ZMod BabyBear_Prime) :
  x * 1761607681 = x / 2 ^ 3
:= by convert babybear_div_pow_3' x

lemma babybear_div_pow_4' [Fact (2013265921).Prime] (x: ZMod 2013265921) :
  x * 1887436801 = x / 2 ^ 4
:= by grind

lemma babybear_div_pow_4 [Fact BabyBear_Prime.Prime] (x: ZMod BabyBear_Prime) :
  x * 1887436801 = x / 2 ^ 4
:= by convert babybear_div_pow_4' x

lemma babybear_div_pow_8' [Fact (2013265921).Prime] (x: ZMod 2013265921) :
  x * 2005401601 = x / 2 ^ 8
:= by grind

lemma babybear_div_pow_8 [Fact BabyBear_Prime.Prime] (x: ZMod BabyBear_Prime) :
  x * 2005401601 = x / 2 ^ 8
:= by convert babybear_div_pow_8' x

lemma babybear_div_pow_27' [Fact (2013265921).Prime] (x: ZMod 2013265921) :
  x * 2013265906 = x / 2 ^ 27
:= by grind

lemma babybear_div_pow_27 [Fact BabyBear_Prime.Prime] (x: ZMod BabyBear_Prime) :
  x * 2013265906 = x / 2 ^ 27
:= by convert babybear_div_pow_27' x

-- instance [Fact BabyBear_Prime.Prime]: Field (ZMod BabyBear_Prime) := ZMod.instField BabyBear_Prime
