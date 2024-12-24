require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6184258 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) ((@support A B) op f s)) ((@FINITE A) ((@support A B) op g s))) (= ((@iterate B A) op s (λ x : El A, (op (f x) (g x)))) (op ((@iterate B A) op s f) ((@iterate B A) op s g)))))))))))));
