require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1346200 : Prf (∀ (λ m : El real, (∀ (λ n : El real, (= (real_min m n) ((@COND real) (real_le m n) m n))))));
