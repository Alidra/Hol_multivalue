require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7917679 [M N] : Prf (= ((@dimindex (finite_diff M N)) (@UNIV (finite_diff M N))) ((@COND num) (< ((@dimindex N) (@UNIV N)) ((@dimindex M) (@UNIV M))) (- ((@dimindex M) (@UNIV M)) ((@dimindex N) (@UNIV N))) (NUMERAL (BIT1 _0))));
