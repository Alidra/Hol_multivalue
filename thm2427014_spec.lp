require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2427014 (a : El int) (b : El int) (c : El int) (d : El int) : Prf ((λ d' : El int, (= (∧ (¬ (= a b)) (¬ (= c d'))) (¬ (= (int_add (int_mul a c) (int_mul b d')) (int_add (int_mul a d') (int_mul b c)))))) d);
