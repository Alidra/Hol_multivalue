require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2427819 [A] : Prf (∀ (λ rel : El (fun A (fun A bool)), (∀ (λ x : El A, (∀ (λ y : El A, (= ((@== A) x y rel) (rel x y))))))));
