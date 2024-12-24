require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1351370 : Prf (∀ (λ P : El (fun real bool), (⇒ (∧ (∃ (λ x : El real, (P x))) (∃ (λ M : El real, (∀ (λ x : El real, (⇒ (P x) (real_le x M))))))) (∃ (λ M : El real, (∧ (∀ (λ x : El real, (⇒ (P x) (real_le x M)))) (∀ (λ M' : El real, (⇒ (∀ (λ x : El real, (⇒ (P x) (real_le x M')))) (real_le M M'))))))))));
