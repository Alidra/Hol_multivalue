require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 (x0: El int) (x1: El int) (x2: El int) ≔ ((@== int) (rem x0 (int_mul x1 x2)) x0 (int_mod (int_mul x1 x2)));
symbol term2 (x0: El int) (x1: El int) (x2: El int) ≔ ((λ y0 : El int, ((@== int) (rem x0 y0) x0 (int_mod y0))) (int_mul x1 x2));
symbol term0 (x0: El int) ≔ ((λ y0 : El int, (∀ (λ y1 : El int, ((@== int) (rem y0 y1) y0 (int_mod y1))))) x0);
symbol term1 (x0: El int) ≔ (∀ (λ y0 : El int, ((@== int) (rem x0 y0) x0 (int_mod y0))));
