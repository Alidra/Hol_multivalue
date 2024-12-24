require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem45472 [A B] : Prf (∀ (λ p : El (prod A B), (= ((@FST A B) p) ((@ε A) (λ x : El A, (∃ (λ y : El B, (= p ((@̦‚ A B) x y)))))))));
