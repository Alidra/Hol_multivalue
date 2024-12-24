require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El a0) ≔ ((λ y0 : El a0, (∀ (λ y1 : El a0, (= ((@GEQ a0) y0 y1) (= y0 y1))))) x0);
symbol term2 a0 (x0: El a0) (x1: El a0) ≔ ((λ y0 : El a0, (= ((@GEQ a0) x0 y0) (= x0 y0))) x1);
symbol term1 a0 (x0: El a0) ≔ (∀ (λ y0 : El a0, (= ((@GEQ a0) x0 y0) (= x0 y0))));
