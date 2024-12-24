require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7689528 [A B] : Prf (= (@UNIV (finite_diff A B)) ((@IMAGE num (finite_diff A B)) (@mk_finite_diff A B) (… (NUMERAL (BIT1 _0)) ((@COND num) (< ((@dimindex B) (@UNIV B)) ((@dimindex A) (@UNIV A))) (- ((@dimindex A) (@UNIV A)) ((@dimindex B) (@UNIV B))) (NUMERAL (BIT1 _0))))));
