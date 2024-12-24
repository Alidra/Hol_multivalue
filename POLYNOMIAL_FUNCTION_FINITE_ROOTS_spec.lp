require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7588957 : Prf (∀ (λ p : El (fun real real), (∀ (λ a : El real, (⇒ (polynomial_function p) (= ((@FINITE real) ((@GSPEC real) (λ GEN_PVAR_351 : El real, (∃ (λ x : El real, ((@SETSPEC real) GEN_PVAR_351 (= (p x) a) x)))))) (¬ (∀ (λ x : El real, (= (p x) a))))))))));
