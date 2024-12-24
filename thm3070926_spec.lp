require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3070926 (x : El int) : Prf (= ((λ x' : El int, (= (int_abs (int_abs x')) (int_abs x'))) x) (= (int_abs (int_abs x)) (int_abs x)));
