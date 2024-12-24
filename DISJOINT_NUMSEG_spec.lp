require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5451441 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (∀ (λ q : El num, (= ((@DISJOINT num) (… m n) (… p q)) (∨ (< n p) (∨ (< q m) (∨ (< n m) (< q p)))))))))))));
