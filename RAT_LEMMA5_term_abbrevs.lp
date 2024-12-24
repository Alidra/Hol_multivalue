require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El real) (x1: El real) ≔ (∧ (real_lt (real_of_num (NUMERAL _0)) x0) (real_lt (real_of_num (NUMERAL _0)) x1));
symbol term0 (x0: El real) (x1: El real) (x2: El real) (x3: El real) ≔ (⇒ (∧ (real_lt (real_of_num (NUMERAL _0)) x3) (real_lt (real_of_num (NUMERAL _0)) x1)) (= (= (real_div x0 x3) (real_div x2 x1)) (= (real_mul x0 x1) (real_mul x2 x3))));
