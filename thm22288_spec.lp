require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem22288 : Prf (∀ (λ a : El bool, (∀ (λ b : El bool, (∀ (λ c : El bool, (⇒ (∨ a b) (⇒ (∨ (¬ a) c) (∨ b c)))))))));
