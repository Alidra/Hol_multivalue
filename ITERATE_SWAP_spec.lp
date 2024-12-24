require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6113745 [A B C] : Prf (∀ (λ op : El (fun C (fun C C)), (⇒ ((@monoidal C) op) (∀ (λ f : El (fun A (fun B C)), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@FINITE A) s) ((@FINITE B) t)) (= ((@iterate C A) op s (λ i : El A, ((@iterate C B) op t (f i)))) ((@iterate C B) op t (λ j : El B, ((@iterate C A) op s (λ i : El A, (f i j))))))))))))))));
