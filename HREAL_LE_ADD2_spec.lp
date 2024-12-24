require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1322168 : Prf (∀ (λ a : El hreal, (∀ (λ b : El hreal, (∀ (λ c : El hreal, (∀ (λ d : El hreal, (⇒ (∧ (hreal_le a b) (hreal_le c d)) (hreal_le (hreal_add a c) (hreal_add b d)))))))))));
