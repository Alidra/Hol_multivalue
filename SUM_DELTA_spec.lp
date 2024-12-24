require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7123775 [A] (b : El real) : Prf (∀ (λ s : El (fun A bool), (∀ (λ a : El A, (= ((@sum A) s (λ x : El A, ((@COND real) (= x a) b (real_of_num (NUMERAL _0))))) ((@COND real) ((@IN A) a s) b (real_of_num (NUMERAL _0))))))));
