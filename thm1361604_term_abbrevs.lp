require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 ≔ (real_of_num (NUMERAL _0));
symbol term0 (x0: El bool) ≔ (⇒ (¬ x0) F);
symbol term1 ≔ (real_neg (real_of_num (NUMERAL _0)));
symbol term3 ≔ (⇒ (¬ (= (real_neg (real_of_num (NUMERAL _0))) (real_of_num (NUMERAL _0)))) F);
