require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 ≔ (∧ ((@FINITE (tybit0 a0)) (@UNIV (tybit0 a0))) ((@FINITE (tybit1 a0)) (@UNIV (tybit1 a0))));
symbol term3 a0 ≔ (∧ ((@FINITE 1) (@UNIV 1)) (∧ ((@FINITE (tybit0 a0)) (@UNIV (tybit0 a0))) ((@FINITE (tybit1 a0)) (@UNIV (tybit1 a0)))));
symbol term1 a0 ≔ (∧ ((@FINITE (tybit0 a0)) (@UNIV (tybit0 a0))));
symbol term0 ≔ (∧ ((@FINITE 1) (@UNIV 1)));
