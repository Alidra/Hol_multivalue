require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4605902 [A] : Prf (∀ (λ s : El (fun (fun A bool) bool), (= ((@FINITE A) ((@UNIONS A) s)) (∧ ((@FINITE (fun A bool)) s) (∀ (λ t : El (fun A bool), (⇒ ((@IN (fun A bool)) t s) ((@FINITE A) t))))))));
