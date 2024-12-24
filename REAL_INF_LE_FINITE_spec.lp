require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5227045 : Prf (∀ (λ s : El (fun real bool), (∀ (λ a : El real, (⇒ (∧ ((@FINITE real) s) (¬ (= s (@EMPTY real)))) (= (real_le (inf s) a) (∃ (λ x : El real, (∧ ((@IN real) x s) (real_le x a))))))))));
