require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5315196 : Prf (∀ (λ s : El (fun real bool), (∀ (λ l : El real, (= (has_inf s l) (∧ (¬ (= s (@EMPTY real))) (∧ (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le l x)))) (∀ (λ c : El real, (⇒ (real_lt l c) (∃ (λ x : El real, (∧ ((@IN real) x s) (real_lt x c))))))))))))));
