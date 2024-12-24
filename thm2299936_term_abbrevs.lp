require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) ≔ ((λ y0 : El int, (∀ (λ y1 : El int, (= (real_lt (real_of_int y0) (real_of_int y1)) (int_lt y0 y1))))) x0);
symbol term1 (x0: El int) ≔ (∀ (λ y0 : El int, (= (real_lt (real_of_int x0) (real_of_int y0)) (int_lt x0 y0))));
symbol term2 (x0: El int) (x1: El int) ≔ ((λ y0 : El int, (= (real_lt (real_of_int x0) (real_of_int y0)) (int_lt x0 y0))) x1);
