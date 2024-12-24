require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5241000 : Prf (∀ (λ s : El (fun real bool), (∀ (λ t : El (fun real bool), (⇒ (∧ (¬ (= t (@EMPTY real))) (∧ ((@SUBSET real) t s) (∃ (λ b : El real, (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le b x)))))))) (real_le (inf s) (inf t)))))));
