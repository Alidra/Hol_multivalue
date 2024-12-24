require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2528731 (n : El int) (m : El int) (p : El int) : Prf (= ((@== int) (rem m (int_mul n p)) m (int_mod p)) (= (rem (rem m (int_mul n p)) p) (rem m p)));
