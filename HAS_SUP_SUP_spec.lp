require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5297166 : Prf (∀ (λ s : El (fun real bool), (∀ (λ l : El real, (= (has_sup s l) (∧ (¬ (= s (@EMPTY real))) (∧ (∃ (λ b : El real, (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x b)))))) (= (sup s) l))))))));
