require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem22403 : Prf (∀ (λ a : El bool, (∀ (λ b : El bool, (= (⇒ (¬ a) b) (∨ a b))))));
