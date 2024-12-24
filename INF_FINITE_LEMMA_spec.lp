require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5217581 : Prf (∀ (λ s : El (fun real bool), (⇒ (∧ ((@FINITE real) s) (¬ (= s (@EMPTY real)))) (∃ (λ b : El real, (∧ ((@IN real) b s) (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le b x))))))))));
