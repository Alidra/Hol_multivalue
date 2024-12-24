require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem276690 : Prf (∀ (λ P : El (fun num bool), (∀ (λ n : El num, (⇒ (∃ (λ r : El num, (P r))) (= (<= n (minimal P)) (∀ (λ i : El num, (⇒ (P i) (<= n i))))))))));
