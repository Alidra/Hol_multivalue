require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3269122 [A] : Prf (∧ (∀ (λ s : El (fun A bool), (∀ (λ a : El A, (= ((@DISJOINT A) s ((@INSERT A) a (@EMPTY A))) (¬ ((@IN A) a s))))))) (∀ (λ s : El (fun A bool), (∀ (λ a : El A, (= ((@DISJOINT A) ((@INSERT A) a (@EMPTY A)) s) (¬ ((@IN A) a s))))))));
