require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2318541 (x : El int) : Prf ((λ x' : El int, (= (real_of_int (int_neg x')) (real_neg (real_of_int x')))) x);
