require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8026123 [A M N] : Prf (= ((@PCROSS A M N) (@UNIV (cart A M)) (@UNIV (cart A N))) (@UNIV (cart A (finite_sum M N))));
