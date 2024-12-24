require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5200089 : Prf (∀ (λ s : El (fun real bool), (∀ (λ c : El real, (⇒ (∧ (¬ (= s (@EMPTY real))) (∧ (∃ (λ b : El real, (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x b)))))) (real_lt c (sup s)))) (∃ (λ x : El real, (∧ ((@IN real) x s) (real_lt c x)))))))));
