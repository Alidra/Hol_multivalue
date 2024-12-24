require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5163728 : Prf (∀ (λ s : El (fun real bool), (∀ (λ t : El (fun real bool), (⇒ (∧ (¬ (= s (@EMPTY real))) (∧ ((@SUBSET real) s t) (∃ (λ b : El real, (∀ (λ x : El real, (⇒ ((@IN real) x t) (real_le x b)))))))) (real_le (sup s) (sup t)))))));
