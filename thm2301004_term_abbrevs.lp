require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) (x1: El int) (x2: El int) ≔ (∧ (= (int_add (int_add x1 x0) x2) (int_add x1 (int_add x0 x2))) (= (int_add x1 (int_add x0 x2)) (int_add x0 (int_add x1 x2))));
