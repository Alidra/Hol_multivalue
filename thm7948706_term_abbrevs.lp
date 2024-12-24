require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El num) ≔ (∧ (= (= ((@dimindex a0) (@UNIV a0)) x0) (= ((@dimindex (tybit1 a0)) (@UNIV (tybit1 a0))) (BIT1 x0))) (= ((@dimindex 1) (@UNIV 1)) (BIT1 _0)));
