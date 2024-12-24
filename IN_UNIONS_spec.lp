require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3205091 [A] : Prf (∀ (λ s : El (fun (fun A bool) bool), (∀ (λ x : El A, (= ((@IN A) x ((@UNIONS A) s)) (∃ (λ t : El (fun A bool), (∧ ((@IN (fun A bool)) t s) ((@IN A) x t)))))))));
