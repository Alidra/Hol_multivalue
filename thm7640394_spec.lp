require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7640394 [M N] : Prf (∧ ((@FINITE (finite_sum M N)) (@UNIV (finite_sum M N))) (= ((@CARD (finite_sum M N)) (@UNIV (finite_sum M N))) (+ ((@dimindex M) (@UNIV M)) ((@dimindex N) (@UNIV N)))));
