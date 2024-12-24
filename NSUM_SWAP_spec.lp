require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6961567 [A B] : Prf (∀ (λ f : El (fun A (fun B num)), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@FINITE A) s) ((@FINITE B) t)) (= ((@nsum A) s (λ i : El A, ((@nsum B) t (f i)))) ((@nsum B) t (λ j : El B, ((@nsum A) s (λ i : El A, (f i j)))))))))))));
