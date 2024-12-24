require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) ≔ (∃ (λ y0 : El num, (∨ (= x0 (real_of_num y0)) (= x0 (real_neg (real_of_num y0))))));
