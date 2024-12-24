require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5311014 : Prf (∀ (λ s : El (fun real bool), (∀ (λ l : El real, (∀ (λ c : El real, (⇒ (∧ (has_sup s l) (real_lt c l)) (∃ (λ x : El real, (∧ ((@IN real) x s) (real_lt c x)))))))))));
