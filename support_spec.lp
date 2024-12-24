require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5716761 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (∀ (λ op : El (fun B (fun B B)), (= ((@support A B) op f s) ((@GSPEC A) (λ GEN_PVAR_237 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_237 (∧ ((@IN A) x s) (¬ (= (f x) ((@neutral B) op)))) x))))))))))));
