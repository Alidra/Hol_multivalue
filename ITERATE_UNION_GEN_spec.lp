require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5764561 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@FINITE A) ((@support A B) op f s)) (∧ ((@FINITE A) ((@support A B) op f t)) ((@DISJOINT A) ((@support A B) op f s) ((@support A B) op f t)))) (= ((@iterate B A) op ((@UNION A) s t) f) (op ((@iterate B A) op s f) ((@iterate B A) op t f)))))))))))));
