require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8026003 [M N] : Prf (∀ (λ s : El (fun (cart real M) bool), (∀ (λ s' : El (fun (cart real M) bool), (∀ (λ t : El (fun (cart real N) bool), (∀ (λ t' : El (fun (cart real N) bool), (= (= ((@PCROSS real M N) s t) ((@PCROSS real M N) s' t')) (∨ (∧ (∨ (= s (@EMPTY (cart real M))) (= t (@EMPTY (cart real N)))) (∨ (= s' (@EMPTY (cart real M))) (= t' (@EMPTY (cart real N))))) (∧ (= s s') (= t t'))))))))))));
