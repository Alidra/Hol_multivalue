require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 a0 ≔ (∀ (λ y0 : El num, (= ((@INJN a0) y0) (λ y1 : El num, (λ y2 : El a0, (= y1 y0))))));
symbol term4 a0 (x0: El num) ≔ ((λ y0 : El num, (= ((@INJN a0) y0) (λ y1 : El num, (λ y2 : El a0, (= y1 y0))))) x0);
symbol term1 a0 (x0: El num) ≔ ((λ y0 : El num, (λ y1 : El num, (λ y2 : El a0, (= y1 y0)))) x0);
symbol term2 a0 (x0: El num) ≔ (λ y0 : El num, (λ y1 : El a0, (= y0 x0)));
symbol term0 a0 ≔ (λ y0 : El num, (λ y1 : El num, (λ y2 : El a0, (= y1 y0))));
