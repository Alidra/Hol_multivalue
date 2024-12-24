require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5753234 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∧ (∀ (λ f : El (fun A B), (= ((@iterate B A) op (@EMPTY A) f) ((@neutral B) op)))) (∀ (λ f : El (fun A B), (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) ((@support A B) op f s)) (= ((@iterate B A) op ((@INSERT A) x s) f) ((@COND B) ((@IN A) x s) ((@iterate B A) op s f) (op (f x) ((@iterate B A) op s f)))))))))))))));
