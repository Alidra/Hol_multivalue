require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5266204 : Prf (∀ (λ s : El (fun real bool), (⇒ (∧ (¬ (= s (@EMPTY real))) (∃ (λ B : El real, (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le (real_abs x) B))))))) (= (= (sup s) (inf s)) (∃ (λ a : El real, (= s ((@INSERT real) a (@EMPTY real)))))))));
