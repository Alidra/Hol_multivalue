require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 ≔ (∨ ((@INFINITE a0) (@UNIV a0)) ((@INFINITE a0) (@UNIV a0)));
symbol term0 a0 a1 ≔ (∨ ((@INFINITE a0) (@UNIV a0)) ((@INFINITE a1) (@UNIV a1)));
symbol term2 a0 ≔ ((@= bool) ((@INFINITE (prod a0 a0)) (@UNIV (prod a0 a0))));
symbol term3 a0 ≔ ((@= bool) ((@INFINITE a0) (@UNIV a0)));
