require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 ≔ (λ y0 : El num, (= (real_of_num y0) (real_of_int (int_of_num y0))));
symbol term0 (x0: El num) ≔ (real_of_int (int_of_num x0));
symbol term4 ≔ (∀ (λ y0 : El num, (= (real_of_num y0) (real_of_int (int_of_num y0)))));
symbol term3 ≔ (∀ (λ y0 : El num, (= (real_of_int (int_of_num y0)) (real_of_num y0))));
symbol term1 ≔ (λ y0 : El num, (= (real_of_int (int_of_num y0)) (real_of_num y0)));
