require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem45478 [A B] : Prf (∀ (λ p : El (prod A B), (= ((@SND A B) p) ((@ε B) (λ y : El B, (∃ (λ x : El A, (= p ((@̦‚ A B) x y)))))))));
