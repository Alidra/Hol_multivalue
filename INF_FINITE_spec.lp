require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5222545 : Prf (∀ (λ s : El (fun real bool), (⇒ (∧ ((@FINITE real) s) (¬ (= s (@EMPTY real)))) (∧ ((@IN real) (inf s) s) (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le (inf s) x))))))));
