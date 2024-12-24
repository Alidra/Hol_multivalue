require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El num) ≔ ((λ y0 : El num, ((@̦‚ hreal hreal) (hreal_of_num y0) (hreal_of_num (NUMERAL _0)))) x0);
symbol term2 (x0: El num) ≔ ((@̦‚ hreal hreal) (hreal_of_num x0) (hreal_of_num (NUMERAL _0)));
symbol term0 ≔ (λ y0 : El num, ((@̦‚ hreal hreal) (hreal_of_num y0) (hreal_of_num (NUMERAL _0))));
symbol term3 ≔ (∀ (λ y0 : El num, (= (treal_of_num y0) ((@̦‚ hreal hreal) (hreal_of_num y0) (hreal_of_num (NUMERAL _0))))));
symbol term4 (x0: El num) ≔ ((λ y0 : El num, (= (treal_of_num y0) ((@̦‚ hreal hreal) (hreal_of_num y0) (hreal_of_num (NUMERAL _0))))) x0);
