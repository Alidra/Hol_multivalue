require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5293342 : Prf (∀ (λ s : El (fun real bool), (∀ (λ b : El real, (∀ (λ x : El real, (⇒ (∧ (has_sup s b) ((@IN real) x s)) (real_le x b))))))));
