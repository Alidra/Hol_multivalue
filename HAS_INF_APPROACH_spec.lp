require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5308185 : Prf (∀ (λ s : El (fun real bool), (∀ (λ l : El real, (∀ (λ c : El real, (⇒ (∧ (has_inf s l) (real_lt l c)) (∃ (λ x : El real, (∧ ((@IN real) x s) (real_lt x c)))))))))));
