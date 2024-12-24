require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7124408 [A B] : Prf (∀ (λ f : El (fun A (fun B real)), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@FINITE A) s) ((@FINITE B) t)) (= ((@sum A) s (λ i : El A, ((@sum B) t (f i)))) ((@sum B) t (λ j : El B, ((@sum A) s (λ i : El A, (f i j)))))))))))));
