require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2528721 (m : El int) (n : El int) (p : El int) : Prf ((λ p' : El int, (= (= (rem m p') (rem n p')) ((@== int) m n (int_mod p')))) p);
