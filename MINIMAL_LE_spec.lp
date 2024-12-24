require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem278395 : Prf (∀ (λ P : El (fun num bool), (∀ (λ n : El num, (⇒ (∃ (λ r : El num, (P r))) (= (<= (minimal P) n) (∃ (λ i : El num, (∧ (<= i n) (P i))))))))));
