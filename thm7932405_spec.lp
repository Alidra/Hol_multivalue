require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7932405 [A] (h1 : Prf (= (@UNIV (tybit1 A)) ((@IMAGE (finite_sum (finite_sum A A) 1) (tybit1 A)) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) 1))))) : Prf (= ((@HAS_SIZE (tybit1 A)) ((@IMAGE (finite_sum (finite_sum A A) 1) (tybit1 A)) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) 1))) (+ (* (NUMERAL (BIT0 (BIT1 _0))) ((@dimindex A) (@UNIV A))) (NUMERAL (BIT1 _0)))) ((@HAS_SIZE (tybit1 A)) (@UNIV (tybit1 A)) (+ (* (NUMERAL (BIT0 (BIT1 _0))) ((@dimindex A) (@UNIV A))) (NUMERAL (BIT1 _0)))));
