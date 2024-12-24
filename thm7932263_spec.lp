require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7932263 [A] : Prf (= (= (@UNIV (tybit0 A)) ((@IMAGE (finite_sum A A) (tybit0 A)) (@mktybit0 A) (@UNIV (finite_sum A A)))) ((@HAS_SIZE (tybit0 A)) (@UNIV (tybit0 A)) (* (NUMERAL (BIT0 (BIT1 _0))) ((@dimindex A) (@UNIV A)))));
