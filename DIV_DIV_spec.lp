require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem220350 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (DIV (DIV m n) p) (DIV m (* n p)))))))));
