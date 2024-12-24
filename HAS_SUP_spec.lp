require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5319392 : Prf (∀ (λ s : El (fun real bool), (∀ (λ l : El real, (= (has_sup s l) (∧ (¬ (= s (@EMPTY real))) (∧ (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x l)))) (∀ (λ c : El real, (⇒ (real_lt c l) (∃ (λ x : El real, (∧ ((@IN real) x s) (real_lt c x))))))))))))));
