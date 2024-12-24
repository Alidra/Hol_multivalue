require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7640379 [M N] : Prf ((@HAS_SIZE (finite_sum M N)) (@UNIV (finite_sum M N)) (+ ((@dimindex M) (@UNIV M)) ((@dimindex N) (@UNIV N))));
