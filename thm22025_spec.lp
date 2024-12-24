require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem22025 : Prf (∀ (λ a : El bool, (∀ (λ c : El bool, (⇒ a (⇒ (∨ (¬ a) c) c))))));
