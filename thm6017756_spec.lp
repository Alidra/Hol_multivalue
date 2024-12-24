require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6017756 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ ((@SUBSET A) ((@support A B) op f (@UNIV A)) s) (= ((@iterate B A) op s f) ((@iterate B A) op (@UNIV A) f))))))))));
