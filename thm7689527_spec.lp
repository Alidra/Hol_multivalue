require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7689527 [A B] : Prf (∀ (λ x : El (finite_diff A B), (∃ (λ x' : El num, (∧ (= x ((@mk_finite_diff A B) x')) ((@IN num) x' (… (NUMERAL (BIT1 _0)) ((@COND num) (< ((@dimindex B) (@UNIV B)) ((@dimindex A) (@UNIV A))) (- ((@dimindex A) (@UNIV A)) ((@dimindex B) (@UNIV B))) (NUMERAL (BIT1 _0))))))))));
