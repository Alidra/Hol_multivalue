require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5476933 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (∀ (λ q : El num, (= ((@SUBSET num) (… m n) (… p q)) (∨ (< n m) (∧ (<= p m) (<= n q))))))))))));
