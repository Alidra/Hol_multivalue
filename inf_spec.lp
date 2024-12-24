require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5204233 : Prf (∀ (λ s : El (fun real bool), (= (inf s) ((@ε real) (λ a : El real, (∧ (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le a x)))) (∀ (λ b : El real, (⇒ (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le b x)))) (real_le b a))))))))));
