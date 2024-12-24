require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7132374 [_133404] : Prf (∀ (λ f : El (fun _133404 real), (∀ (λ s : El (fun _133404 bool), (⇒ ((@FINITE _133404) s) (= ((@sum _133404) s (λ x : El _133404, ((@COND real) ((@IN _133404) x s) (f x) (real_of_num (NUMERAL _0))))) ((@sum _133404) s f)))))));
