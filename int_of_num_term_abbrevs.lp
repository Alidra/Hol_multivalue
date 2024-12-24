require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El num) ≔ (int_of_real (real_of_num x0));
symbol term0 ≔ (λ y0 : El num, (int_of_real (real_of_num y0)));
symbol term3 ≔ (∀ (λ y0 : El num, (= (int_of_num y0) (int_of_real (real_of_num y0)))));
symbol term1 (x0: El num) ≔ ((λ y0 : El num, (int_of_real (real_of_num y0))) x0);
symbol term4 (x0: El num) ≔ ((λ y0 : El num, (= (int_of_num y0) (int_of_real (real_of_num y0)))) x0);
