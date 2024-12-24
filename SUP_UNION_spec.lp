require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5197251 : Prf (∀ (λ s : El (fun real bool), (∀ (λ t : El (fun real bool), (⇒ (∧ (¬ (= s (@EMPTY real))) (∧ (¬ (= t (@EMPTY real))) (∧ (∃ (λ b : El real, (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x b)))))) (∃ (λ c : El real, (∀ (λ x : El real, (⇒ ((@IN real) x t) (real_le x c))))))))) (= (sup ((@UNION real) s t)) (real_max (sup s) (sup t))))))));
