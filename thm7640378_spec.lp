require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7640378 [M N] : Prf ((@HAS_SIZE (finite_sum M N)) ((@IMAGE num (finite_sum M N)) (@mk_finite_sum M N) (… (NUMERAL (BIT1 _0)) (+ ((@dimindex M) (@UNIV M)) ((@dimindex N) (@UNIV N))))) (+ ((@dimindex M) (@UNIV M)) ((@dimindex N) (@UNIV N))));
