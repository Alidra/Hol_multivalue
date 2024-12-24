require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8036724 [M N] : Prf (∀ (λ s : El (fun (cart real M) bool), (∀ (λ t : El (fun (cart real N) bool), (= ((@IMAGE (cart real (finite_sum M N)) (cart real N)) (@sndcart real M N) ((@PCROSS real M N) s t)) ((@COND (fun (cart real N) bool)) (= s (@EMPTY (cart real M))) (@EMPTY (cart real N)) t))))));
