require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1318736 : Prf (∀ (λ P : El (fun hreal bool), (⇒ (∧ (∃ (λ x : El hreal, (P x))) (∃ (λ M : El hreal, (∀ (λ x : El hreal, (⇒ (P x) (hreal_le x M))))))) (∃ (λ M : El hreal, (∧ (∀ (λ x : El hreal, (⇒ (P x) (hreal_le x M)))) (∀ (λ M' : El hreal, (⇒ (∀ (λ x : El hreal, (⇒ (P x) (hreal_le x M')))) (hreal_le M M'))))))))));
