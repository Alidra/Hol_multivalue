require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem54 : Prf (= ∨ (λ p : El bool, (λ q : El bool, (∀ (λ r : El bool, (⇒ (⇒ p r) (⇒ (⇒ q r) r)))))));
