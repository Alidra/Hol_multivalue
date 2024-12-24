require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) ≔ ((λ y0 : El int, (∀ (λ y1 : El int, (= (int_sub y0 y1) (int_add y0 (int_neg y1)))))) x0);
symbol term2 (x0: El int) (x1: El int) ≔ ((λ y0 : El int, (= (int_sub x0 y0) (int_add x0 (int_neg y0)))) x1);
symbol term1 (x0: El int) ≔ (∀ (λ y0 : El int, (= (int_sub x0 y0) (int_add x0 (int_neg y0)))));
