require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5042707 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ u : El (fun A bool), (∀ (λ v : El (fun B bool), (= (∀ (λ t : El (fun B bool), (⇒ ((@SUBSET B) t v) (∃ (λ s : El (fun A bool), (∧ ((@SUBSET A) s u) (= ((@IMAGE A B) f s) t))))))) (∀ (λ y : El B, (⇒ ((@IN B) y v) (∃ (λ x : El A, (∧ ((@IN A) x u) (= (f x) y))))))))))))));
