require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 ≔ (real_of_num (NUMERAL _0));
symbol term1 ≔ (real_abs (real_of_num (NUMERAL _0)));
symbol term0 ≔ (⇒ (⇒ (¬ (= (real_abs (real_of_num (NUMERAL _0))) (real_of_num (NUMERAL _0)))) F) (= (real_abs (real_of_num (NUMERAL _0))) (real_of_num (NUMERAL _0))));
