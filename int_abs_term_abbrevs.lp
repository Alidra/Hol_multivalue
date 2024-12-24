require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El int) ≔ ((λ y0 : El int, (int_of_real (real_abs (real_of_int y0)))) x0);
symbol term3 ≔ (∀ (λ y0 : El int, (= (int_abs y0) (int_of_real (real_abs (real_of_int y0))))));
symbol term2 (x0: El int) ≔ (int_of_real (real_abs (real_of_int x0)));
symbol term0 ≔ (λ y0 : El int, (int_of_real (real_abs (real_of_int y0))));
symbol term4 (x0: El int) ≔ ((λ y0 : El int, (= (int_abs y0) (int_of_real (real_abs (real_of_int y0))))) x0);
