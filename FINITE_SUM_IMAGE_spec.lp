require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7637130 [A B] : Prf (= (@UNIV (finite_sum A B)) ((@IMAGE num (finite_sum A B)) (@mk_finite_sum A B) (… (NUMERAL (BIT1 _0)) (+ ((@dimindex A) (@UNIV A)) ((@dimindex B) (@UNIV B))))));
