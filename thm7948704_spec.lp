require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7948704 [A] (n : El num) : Prf (∧ (= (= ((@dimindex A) (@UNIV A)) n) (= ((@dimindex (tybit0 A)) (@UNIV (tybit0 A))) (BIT0 n))) (∧ (= (= ((@dimindex A) (@UNIV A)) n) (= ((@dimindex (tybit1 A)) (@UNIV (tybit1 A))) (BIT1 n))) (= ((@dimindex 1) (@UNIV 1)) (BIT1 _0))));
