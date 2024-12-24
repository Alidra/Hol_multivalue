require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7_spec;
opaque symbol lem7640397 [M N] : Prf (= ((@FINITE (finite_sum M N)) (@UNIV (finite_sum M N))) (= ((@FINITE (finite_sum M N)) (@UNIV (finite_sum M N))) T)) ≔ (@lem7 ((@FINITE (finite_sum M N)) (@UNIV (finite_sum M N))));
