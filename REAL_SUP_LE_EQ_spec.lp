require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5188259 : Prf (∀ (λ s : El (fun real bool), (∀ (λ y : El real, (⇒ (∧ (¬ (= s (@EMPTY real))) (∃ (λ b : El real, (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x b))))))) (= (real_le (sup s) y) (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x y))))))))));
