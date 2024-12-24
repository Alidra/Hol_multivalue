require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem13262 [A] : Prf (∀ (λ p : El bool, (∀ (λ x : El A, (∀ (λ y : El A, (= ((@COND A) (¬ p) x y) ((@COND A) p y x))))))));
