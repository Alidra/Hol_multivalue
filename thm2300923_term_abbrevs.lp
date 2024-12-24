require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) (x1: El real) (x2: El real) ≔ (∧ (= (real_add (real_add x1 x0) x2) (real_add x1 (real_add x0 x2))) (= (real_add x1 (real_add x0 x2)) (real_add x0 (real_add x1 x2))));
