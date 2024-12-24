require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (λ y0 : El num, (mk_nadd (λ y1 : El num, (* y0 y1))));
symbol term1 (x0: El num) ≔ ((λ y0 : El num, (mk_nadd (λ y1 : El num, (* y0 y1)))) x0);
symbol term4 (x0: El num) ≔ ((λ y0 : El num, (= (nadd_of_num y0) (mk_nadd (λ y1 : El num, (* y0 y1))))) x0);
symbol term2 (x0: El num) ≔ (mk_nadd (λ y0 : El num, (* x0 y0)));
symbol term3 ≔ (∀ (λ y0 : El num, (= (nadd_of_num y0) (mk_nadd (λ y1 : El num, (* y0 y1))))));
