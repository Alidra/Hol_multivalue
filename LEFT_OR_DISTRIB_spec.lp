require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1001 : Prf (∀ (λ p : El bool, (∀ (λ q : El bool, (∀ (λ r : El bool, (= (∧ p (∨ q r)) (∨ (∧ p q) (∧ p r)))))))));
