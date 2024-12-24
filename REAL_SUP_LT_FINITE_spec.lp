require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5154372 : Prf (∀ (λ s : El (fun real bool), (∀ (λ a : El real, (⇒ (∧ ((@FINITE real) s) (¬ (= s (@EMPTY real)))) (= (real_lt (sup s) a) (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_lt x a))))))))));
