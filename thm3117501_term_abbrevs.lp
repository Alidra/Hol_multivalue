require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) ≔ ((λ y0 : El num, (∀ (λ y1 : El num, (∀ (λ y2 : El num, (= ((@== num) y0 y1 (num_mod y2)) ((@== int) (int_of_num y0) (int_of_num y1) (int_mod (int_of_num y2))))))))) x0);
symbol term4 (x0: El num) (x1: El num) (x2: El num) ≔ ((λ y0 : El num, (= ((@== num) x0 x1 (num_mod y0)) ((@== int) (int_of_num x0) (int_of_num x1) (int_mod (int_of_num y0))))) x2);
symbol term2 (x0: El num) (x1: El num) ≔ ((λ y0 : El num, (∀ (λ y1 : El num, (= ((@== num) x0 y0 (num_mod y1)) ((@== int) (int_of_num x0) (int_of_num y0) (int_mod (int_of_num y1))))))) x1);
symbol term3 (x0: El num) (x1: El num) ≔ (∀ (λ y0 : El num, (= ((@== num) x0 x1 (num_mod y0)) ((@== int) (int_of_num x0) (int_of_num x1) (int_mod (int_of_num y0))))));
symbol term1 (x0: El num) ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (= ((@== num) x0 y0 (num_mod y1)) ((@== int) (int_of_num x0) (int_of_num y0) (int_mod (int_of_num y1))))))));
