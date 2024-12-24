require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1318748 : Prf (∧ (∀ (λ P : El (fun hreal bool), (= (∀ (λ x : El nadd, (P (mk_hreal (nadd_eq x))))) (∀ (λ x : El hreal, (P x)))))) (∧ (∀ (λ P : El (fun hreal bool), (= (∃ (λ x : El nadd, (P (mk_hreal (nadd_eq x))))) (∃ (λ x : El hreal, (P x)))))) (∀ (λ x : El hreal, (= (mk_hreal (nadd_eq ((@ε nadd) (dest_hreal x)))) x)))));
