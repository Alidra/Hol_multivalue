require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7921508 [A B] : Prf (= (@UNIV (finite_prod A B)) ((@IMAGE num (finite_prod A B)) (@mk_finite_prod A B) (… (NUMERAL (BIT1 _0)) (* ((@dimindex A) (@UNIV A)) ((@dimindex B) (@UNIV B))))));
