require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5160982 (s : El (fun real bool)) : Prf (∀ (λ b : El real, (⇒ (∧ (¬ (= s (@EMPTY real))) (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le x b))))) (real_le (sup s) b))));
