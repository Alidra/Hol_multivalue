require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5231643 : Prf (∀ (λ s : El (fun real bool), (∀ (λ a : El real, (⇒ (∧ ((@FINITE real) s) (¬ (= s (@EMPTY real)))) (= (real_lt (inf s) a) (∃ (λ x : El real, (∧ ((@IN real) x s) (real_lt x a))))))))));
