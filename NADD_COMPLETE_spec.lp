require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1299407 : Prf (∀ (λ P : El (fun nadd bool), (⇒ (∧ (∃ (λ x : El nadd, (P x))) (∃ (λ M : El nadd, (∀ (λ x : El nadd, (⇒ (P x) (nadd_le x M))))))) (∃ (λ M : El nadd, (∧ (∀ (λ x : El nadd, (⇒ (P x) (nadd_le x M)))) (∀ (λ M' : El nadd, (⇒ (∀ (λ x : El nadd, (⇒ (P x) (nadd_le x M')))) (nadd_le M M'))))))))));
