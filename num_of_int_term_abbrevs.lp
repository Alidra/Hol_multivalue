require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term4 (x0: El int) ≔ ((λ y0 : El int, (= (num_of_int y0) ((@ε num) (λ y1 : El num, (= (int_of_num y1) y0))))) x0);
symbol term0 ≔ (λ y0 : El int, ((@ε num) (λ y1 : El num, (= (int_of_num y1) y0))));
symbol term2 (x0: El int) ≔ ((@ε num) (λ y0 : El num, (= (int_of_num y0) x0)));
symbol term1 (x0: El int) ≔ ((λ y0 : El int, ((@ε num) (λ y1 : El num, (= (int_of_num y1) y0)))) x0);
symbol term3 ≔ (∀ (λ y0 : El int, (= (num_of_int y0) ((@ε num) (λ y1 : El num, (= (int_of_num y1) y0))))));
