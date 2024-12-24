require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5773307 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@FINITE A) ((@support A B) op f s)) ((@SUBSET A) ((@support A B) op f t) ((@support A B) op f s))) (= (op ((@iterate B A) op ((@DIFF A) s t) f) ((@iterate B A) op t f)) ((@iterate B A) op s f))))))))))));
