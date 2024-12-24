require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7640437 [M N] : Prf (= ((@COND num) ((@FINITE (finite_sum M N)) (@UNIV (finite_sum M N))) ((@CARD (finite_sum M N)) (@UNIV (finite_sum M N))) (NUMERAL (BIT1 _0))) (+ ((@dimindex M) (@UNIV M)) ((@dimindex N) (@UNIV N))));
