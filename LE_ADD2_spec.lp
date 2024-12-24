require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem101399 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (∀ (λ q : El num, (⇒ (∧ (<= m p) (<= n q)) (<= (+ m n) (+ p q)))))))))));
