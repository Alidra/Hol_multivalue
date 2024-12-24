require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 ≔ (∧ ((@FINITE a0) (@UNIV a0)) ((@FINITE a0) (@UNIV a0)));
symbol term0 a0 a1 ≔ (∧ ((@FINITE a0) (@UNIV a0)) ((@FINITE a1) (@UNIV a1)));
symbol term3 a0 ≔ ((@= bool) ((@FINITE a0) (@UNIV a0)));
symbol term2 a0 ≔ ((@= bool) ((@FINITE (prod a0 a0)) (@UNIV (prod a0 a0))));
