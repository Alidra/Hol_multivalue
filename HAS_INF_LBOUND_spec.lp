require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5292278 : Prf (∀ (λ s : El (fun real bool), (∀ (λ b : El real, (∀ (λ x : El real, (⇒ (∧ (has_inf s b) ((@IN real) x s)) (real_le b x))))))));
