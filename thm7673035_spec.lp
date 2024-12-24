require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7673035 [A B] : Prf (∧ (∀ (λ a : El (finite_diff A B), (= ((@mk_finite_diff A B) ((@dest_finite_diff A B) a)) a))) (∀ (λ r : El num, (= ((@IN num) r (… (NUMERAL (BIT1 _0)) ((@COND num) (< ((@dimindex B) (@UNIV B)) ((@dimindex A) (@UNIV A))) (- ((@dimindex A) (@UNIV A)) ((@dimindex B) (@UNIV B))) (NUMERAL (BIT1 _0))))) (= ((@dest_finite_diff A B) ((@mk_finite_diff A B) r)) r)))));
