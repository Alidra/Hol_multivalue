require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= (int_max (int_of_num y0) (int_of_num y1)) (int_of_num (MAX y0 y1)))))));
