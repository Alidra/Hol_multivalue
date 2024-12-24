require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1318759 (P : El (fun hreal bool)) : Prf ((λ P' : El (fun hreal bool), (= (∀ (λ x : El nadd, (P' (mk_hreal (nadd_eq x))))) (∀ (λ x : El hreal, (P' x))))) P);
