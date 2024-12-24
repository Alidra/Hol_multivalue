require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5295254 : Prf (∀ (λ s : El (fun real bool), (∀ (λ l : El real, (= (has_inf s l) (∧ (¬ (= s (@EMPTY real))) (∧ (∃ (λ b : El real, (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le b x)))))) (= (inf s) l))))))));
