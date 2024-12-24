require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3231915 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@PSUBSET A) s t) (∧ ((@SUBSET A) s t) (∃ (λ a : El A, (∧ ((@IN A) a t) (¬ ((@IN A) a s)))))))))));
