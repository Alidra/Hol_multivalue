require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7169057 [_134498] : Prf (∀ (λ f : El (fun _134498 num), (∀ (λ s : El (fun _134498 bool), (⇒ ((@FINITE _134498) s) (= (real_of_num ((@nsum _134498) s f)) ((@sum _134498) s (λ x : El _134498, (real_of_num (f x))))))))));
