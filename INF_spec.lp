require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5214027 : Prf (∀ (λ s : El (fun real bool), (⇒ (∧ (¬ (= s (@EMPTY real))) (∃ (λ b : El real, (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le b x))))))) (∧ (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le (inf s) x)))) (∀ (λ b : El real, (⇒ (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le b x)))) (real_le b (inf s)))))))));
