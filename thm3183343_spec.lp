require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3183343 [_83064] (x : El _83064) : Prf (= (∀ (λ x' : El bool, (∀ (λ x'' : El _83064, (= ((@SETSPEC _83064) x x' x'') (∧ x' (= x x''))))))) (= ((@SETSPEC _83064) x) (λ p : El bool, (λ t : El _83064, (∧ p (= x t))))));
