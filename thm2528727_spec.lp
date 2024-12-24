require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2528727 (p : El int) (m : El int) (n : El int) : Prf (= ((@== int) (rem m (int_mul n p)) m (int_mod n)) (= (rem (rem m (int_mul n p)) n) (rem m n)));
