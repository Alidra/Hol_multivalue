require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5282345 : Prf (∀ (λ s : El (fun real bool), (∀ (λ t : El (fun real bool), (⇒ (∧ (¬ (= s (@EMPTY real))) (∧ (¬ (= t (@EMPTY real))) (∧ (∃ (λ b : El real, (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le b x)))))) (∃ (λ c : El real, (∀ (λ x : El real, (⇒ ((@IN real) x t) (real_le c x))))))))) (= (inf ((@UNION real) s t)) (real_min (inf s) (inf t))))))));
