require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5136700 : Prf (∀ (λ s : El (fun real bool), (⇒ (∧ (¬ (= s (@EMPTY real))) (∃ (λ b : El real, (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x b))))))) (∧ (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x (sup s))))) (∀ (λ b : El real, (⇒ (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x b)))) (real_le (sup s) b))))))));
